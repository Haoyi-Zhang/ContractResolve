"""Version-aware proof-survival circuits for checked resolution schemas.

A survival certificate names exact source axioms and exact binary-resolution
schemas.  The checker validates every axiom body and every schema, unrolls the
schemas for a bounded number of layers, and obtains a monotone circuit over
source-clause retention bits.  A true root yields a concrete resolution proof
that is checked again by the ordinary certificate checker.

This is a small reference implementation.  It is not a production SAT solver or
proof format, and a false root means only that this certificate cannot derive the
root from retained source clauses.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

from certificates import (
    MAX_CLAUSE,
    MAX_NODES,
    MAX_VARIABLE,
    Rejected,
    _clause,
    _keys,
    _name,
    formula,
    verify,
)

Clause = tuple[int, ...]
Schema = tuple[Clause, Clause, int, Clause]

MAX_SCHEMAS = 200_000
MAX_GATES = 2_000_000


def _schema(obj: Any) -> Schema:
    _keys(obj, {"left", "right", "pivot", "clause"})
    left = _clause(obj["left"])
    right = _clause(obj["right"])
    out = _clause(obj["clause"])
    pivot = obj["pivot"]
    if type(pivot) is not int or not 0 < pivot <= MAX_VARIABLE:
        raise Rejected("invalid positive pivot")
    a, b = set(left), set(right)
    if pivot not in a or -pivot not in b:
        raise Rejected("schema pivot absent or wrong orientation")
    expected = (a - {pivot}) | (b - {-pivot})
    if expected != set(out):
        raise Rejected("schema is not the exact binary resolvent")
    return left, right, pivot, out


@dataclass(frozen=True)
class Gate:
    kind: str
    parents: tuple[int, ...]
    payload: Any


@dataclass(frozen=True)
class Evaluation:
    values: tuple[bool, ...]
    target: tuple[tuple[str, Clause], ...]
    owner_token: object
    changed_leaves: int = 0
    recomputed_gates: int = 0


@dataclass(frozen=True)
class VerifiedSurvival:
    source: tuple[tuple[str, Clause], ...]
    mode: str
    clauses: tuple[Clause, ...]
    schemas: tuple[Schema, ...]
    max_depth: int
    root_clause: Clause
    gates: tuple[Gate, ...]
    root_gate: int
    reverse: tuple[tuple[int, ...], ...]
    leaf_by_source: tuple[tuple[str, int], ...]
    clause_gate: tuple[tuple[int, ...], ...]
    schema_gates_by_layer: tuple[tuple[int, ...], ...]
    owner_token: object

    def _target_map(self, target: Mapping[str, Any]) -> dict[str, Clause]:
        return formula(target)

    def _validate_evaluation(self, evaluation: Evaluation) -> None:
        """Reject malformed or cross-circuit in-process evaluation state."""
        if not isinstance(evaluation, Evaluation):
            raise Rejected("expected an Evaluation produced by this circuit")
        if evaluation.owner_token is not self.owner_token:
            raise Rejected("evaluation belongs to a different survival circuit")
        if len(evaluation.values) != len(self.gates):
            raise Rejected("evaluation gate vector has the wrong length")
        if any(type(value) is not bool for value in evaluation.values):
            raise Rejected("evaluation gate vector must contain Booleans")
        try:
            current = dict(evaluation.target)
        except (TypeError, ValueError) as exc:
            raise Rejected("evaluation target snapshot is malformed") from exc
        if len(current) != len(evaluation.target):
            raise Rejected("evaluation target snapshot has duplicate identifiers")
        checked = tuple(sorted(formula(current).items()))
        if checked != evaluation.target:
            raise Rejected("evaluation target snapshot is not canonical")

    def evaluate(self, target: Mapping[str, Any]) -> Evaluation:
        current = self._target_map(target)
        values: list[bool] = []
        for gate in self.gates:
            if gate.kind == "leaf":
                sid, body = gate.payload
                values.append(sid in current and current[sid] == body)
            elif gate.kind == "and":
                values.append(all(values[p] for p in gate.parents))
            elif gate.kind == "or":
                values.append(any(values[p] for p in gate.parents))
            else:  # pragma: no cover - construction invariant
                raise AssertionError("unknown gate kind")
        return Evaluation(tuple(values), tuple(sorted(current.items())), self.owner_token)

    def update(self, previous: Evaluation, target: Mapping[str, Any]) -> Evaluation:
        """Re-evaluate exactly the transitive fanout of changed source leaves."""
        self._validate_evaluation(previous)
        current = self._target_map(target)
        values = list(previous.values)
        changed: list[int] = []
        for sid, gate_index in self.leaf_by_source:
            body = self.gates[gate_index].payload[1]
            new_value = sid in current and current[sid] == body
            if new_value != values[gate_index]:
                values[gate_index] = new_value
                changed.append(gate_index)
        affected: set[int] = set()
        stack = changed[:]
        while stack:
            g = stack.pop()
            for child in self.reverse[g]:
                if child not in affected:
                    affected.add(child)
                    stack.append(child)
        recomputed = 0
        for index in sorted(affected):
            gate = self.gates[index]
            old = values[index]
            if gate.kind == "and":
                values[index] = all(values[p] for p in gate.parents)
            elif gate.kind == "or":
                values[index] = any(values[p] for p in gate.parents)
            else:  # leaf descendants are never leaves
                continue
            recomputed += 1
            # Descendants were conservatively marked before recomputation.  This
            # keeps the procedure simple and makes the reported cone an upper
            # bound on gates whose value had to be reconsidered.
            _ = old
        return Evaluation(tuple(values), tuple(sorted(current.items())), self.owner_token,
                          changed_leaves=len(changed),
                          recomputed_gates=recomputed)

    def survives(self, evaluation: Evaluation) -> bool:
        self._validate_evaluation(evaluation)
        return evaluation.values[self.root_gate]

    def reconstruct(self, evaluation: Evaluation) -> dict[str, Any]:
        """Return one surviving ordinary resolution proof and check it again."""
        if not self.survives(evaluation):
            raise Rejected("survival root is false")
        current = dict(evaluation.target)
        nodes: list[dict[str, Any]] = []
        memo: dict[int, str] = {}

        def build(gate_index: int) -> str:
            if gate_index in memo:
                return memo[gate_index]
            gate = self.gates[gate_index]
            if not evaluation.values[gate_index]:
                raise AssertionError("false gate selected for witness")
            if gate.kind == "or":
                chosen = next(p for p in gate.parents if evaluation.values[p])
                ident = build(chosen)
                memo[gate_index] = ident
                return ident
            if gate.kind == "leaf":
                sid, body = gate.payload
                ident = f"n{len(nodes)}"
                nodes.append({"id": ident, "kind": "axiom", "source": sid,
                              "clause": list(body)})
                memo[gate_index] = ident
                return ident
            if gate.kind == "and":
                left_gate, right_gate = gate.parents
                left_id, right_id = build(left_gate), build(right_gate)
                left, right, pivot, out = gate.payload
                ident = f"n{len(nodes)}"
                nodes.append({"id": ident, "kind": "resolve", "left": left_id,
                              "right": right_id, "pivot": pivot,
                              "clause": list(out)})
                memo[gate_index] = ident
                return ident
            raise AssertionError("unknown gate kind")

        root = build(self.root_gate)
        packet = {"nodes": nodes, "root": root}
        checked = verify(current, packet)
        if checked.conclusion != self.root_clause:
            raise AssertionError("reconstructed conclusion mismatch")
        return packet

    def blocking_cut(self, evaluation: Evaluation) -> tuple[str, ...]:
        """Return a deterministic sufficient leaf cut when the root is false.

        The cut is not claimed minimum.  Keeping every listed leaf inactive is
        sufficient to keep the root false, regardless of other leaf changes.
        """
        if self.survives(evaluation):
            raise Rejected("survival root is true")
        memo: dict[int, frozenset[str]] = {}

        def cut(gate_index: int) -> frozenset[str]:
            if gate_index in memo:
                return memo[gate_index]
            gate = self.gates[gate_index]
            if evaluation.values[gate_index]:
                raise AssertionError("blocking cut requested for true gate")
            if gate.kind == "leaf":
                result = frozenset([gate.payload[0]])
            elif gate.kind == "or":
                result = frozenset().union(*(cut(p) for p in gate.parents))
            elif gate.kind == "and":
                choices = [cut(p) for p in gate.parents if not evaluation.values[p]]
                result = min(choices, key=lambda s: (len(s), tuple(sorted(s))))
            else:  # pragma: no cover
                raise AssertionError("unknown gate kind")
            memo[gate_index] = result
            return result

        return tuple(sorted(cut(self.root_gate)))

    def stats(self) -> dict[str, int | str | bool]:
        leaves = sum(g.kind == "leaf" for g in self.gates)
        ands = sum(g.kind == "and" for g in self.gates)
        ors = sum(g.kind == "or" for g in self.gates)
        edges = sum(len(g.parents) for g in self.gates)
        return {
            "mode": self.mode,
            "clauses": len(self.clauses),
            "schemas": len(self.schemas),
            "max_depth": self.max_depth,
            "gates": len(self.gates),
            "edges": edges,
            "leaf_gates": leaves,
            "and_gates": ands,
            "or_gates": ors,
            "closed": self.mode == "closed",
        }


def compile_survival(source: Mapping[str, Any], certificate: Any) -> VerifiedSurvival:
    """Validate a survival certificate and compile its layered monotone circuit."""
    base = formula(source)
    _keys(certificate, {"mode", "axioms", "clauses", "schemas", "root", "max_depth"})
    mode = certificate["mode"]
    if mode not in {"trace", "closed"}:
        raise Rejected("mode must be trace or closed")
    root = _clause(certificate["root"])
    depth = certificate["max_depth"]
    if type(depth) is not int or not 0 <= depth <= MAX_NODES:
        raise Rejected("invalid max_depth")

    raw_clauses = certificate["clauses"]
    if not isinstance(raw_clauses, list) or not 1 <= len(raw_clauses) <= MAX_NODES:
        raise Rejected("clauses must be a bounded nonempty list")
    clauses = tuple(_clause(c) for c in raw_clauses)
    if len(set(clauses)) != len(clauses):
        raise Rejected("duplicate clause in survival certificate")
    clause_set = set(clauses)
    if root not in clause_set:
        raise Rejected("root clause absent from clause universe")

    raw_axioms = certificate["axioms"]
    if not isinstance(raw_axioms, list) or len(raw_axioms) > MAX_NODES:
        raise Rejected("axioms must be a bounded list")
    axioms: list[tuple[str, Clause]] = []
    for item in raw_axioms:
        _keys(item, {"source", "clause"})
        sid = _name(item["source"])
        body = _clause(item["clause"])
        if sid not in base or base[sid] != body:
            raise Rejected("survival axiom identity/body mismatch")
        if body not in clause_set:
            raise Rejected("axiom body absent from clause universe")
        axioms.append((sid, body))
    if len(set(axioms)) != len(axioms):
        raise Rejected("duplicate survival axiom")

    raw_schemas = certificate["schemas"]
    if not isinstance(raw_schemas, list) or len(raw_schemas) > MAX_SCHEMAS:
        raise Rejected("schemas must be a bounded list")
    schemas = tuple(_schema(s) for s in raw_schemas)
    if len(set(schemas)) != len(schemas):
        raise Rejected("duplicate resolution schema")
    if any(a not in clause_set or b not in clause_set or c not in clause_set
           for a, b, _, c in schemas):
        raise Rejected("schema clause absent from clause universe")

    gate_count = (len(axioms) + (depth + 1) * len(clauses)
                  + depth * len(schemas))
    if gate_count > MAX_GATES:
        raise Rejected(
            f"compiled survival circuit would require {gate_count} gates; "
            f"bound is {MAX_GATES}"
        )

    if mode == "closed":
        if set(axioms) != set(base.items()):
            raise Rejected("closed certificate must expose every exact source axiom")
        if depth < len(clauses):
            raise Rejected("closed certificate depth is too small for fixed-point completeness")
        schema_set = set(schemas)
        for left in clauses:
            ls = set(left)
            for right in clauses:
                rs = set(right)
                for pivot in sorted(abs(x) for x in ls if x > 0 and -x in rs):
                    out = tuple(sorted((ls - {pivot}) | (rs - {-pivot})))
                    if any(-x in out for x in out):
                        continue
                    if out not in clause_set:
                        raise Rejected("closed clause universe omits a non-tautological resolvent")
                    if (left, right, pivot, out) not in schema_set:
                        raise Rejected("closed certificate omits a resolution schema")

    clause_index = {c: i for i, c in enumerate(clauses)}
    gates: list[Gate] = []
    reverse: list[list[int]] = []

    def add(kind: str, parents: tuple[int, ...], payload: Any) -> int:
        if len(gates) >= MAX_GATES:
            raise Rejected("compiled survival circuit exceeds gate bound")
        index = len(gates)
        gates.append(Gate(kind, parents, payload))
        reverse.append([])
        for parent in parents:
            reverse[parent].append(index)
        return index

    leaf_by_source: list[tuple[str, int]] = []
    leaves_for_clause: list[list[int]] = [[] for _ in clauses]
    for sid, body in sorted(axioms):
        gi = add("leaf", (), (sid, body))
        leaf_by_source.append((sid, gi))
        leaves_for_clause[clause_index[body]].append(gi)

    clause_gate: list[list[int]] = [[] for _ in range(depth + 1)]
    layer0: list[int] = []
    for ci, c in enumerate(clauses):
        layer0.append(add("or", tuple(leaves_for_clause[ci]), (c, 0)))
    clause_gate[0] = layer0

    by_result: list[list[int]] = [[] for _ in clauses]
    for si, (_, _, _, out) in enumerate(schemas):
        by_result[clause_index[out]].append(si)

    schema_gates_by_layer: list[tuple[int, ...]] = [tuple()]
    for layer in range(1, depth + 1):
        schema_gate_indices: list[int] = []
        for schema in schemas:
            left, right, _, _ = schema
            gi = add("and", (clause_gate[layer - 1][clause_index[left]],
                             clause_gate[layer - 1][clause_index[right]]), schema)
            schema_gate_indices.append(gi)
        schema_gates_by_layer.append(tuple(schema_gate_indices))
        current: list[int] = []
        for ci, c in enumerate(clauses):
            parents = [clause_gate[layer - 1][ci]]
            parents.extend(schema_gate_indices[si] for si in by_result[ci])
            current.append(add("or", tuple(parents), (c, layer)))
        clause_gate[layer] = current

    return VerifiedSurvival(
        source=tuple(sorted(base.items())),
        mode=mode,
        clauses=clauses,
        schemas=schemas,
        max_depth=depth,
        root_clause=root,
        gates=tuple(gates),
        root_gate=clause_gate[depth][clause_index[root]],
        reverse=tuple(tuple(x) for x in reverse),
        leaf_by_source=tuple(leaf_by_source),
        clause_gate=tuple(tuple(x) for x in clause_gate),
        schema_gates_by_layer=tuple(schema_gates_by_layer),
        owner_token=object(),
    )
