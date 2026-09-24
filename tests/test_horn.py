"""Tests for exact version-bound Horn certificates."""
from __future__ import annotations

import sys
import unittest
from dataclasses import replace
from pathlib import Path

SRC = Path(__file__).resolve().parents[1] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from certificates import Rejected, verify
from horn import compile_horn
from horn_oracle import retained_horn_unsat


class HornTests(unittest.TestCase):
    def test_acyclic_chain_reconstructs_and_rechecks(self):
        source = {"start": [1], "r12": [-1, 2], "r23": [-2, 3], "bad": [-3]}
        circuit = compile_horn(source)
        self.assertEqual(circuit.strategy, "acyclic")
        evaluation = circuit.evaluate(source)
        self.assertTrue(circuit.survives(evaluation))
        self.assertEqual(verify(source, circuit.reconstruct(evaluation)).conclusion, ())
        self.assertTrue(circuit.stats()["bound_matches"])

    def test_duplicate_rule_repairs_selected_proof(self):
        source = {"start": [1], "r12a": [-1, 2], "r12b": [-1, 2], "bad": [-2]}
        circuit = compile_horn(source)
        target = {k: v for k, v in source.items() if k != "r12a"}
        evaluation = circuit.evaluate(target)
        self.assertTrue(circuit.survives(evaluation))
        checked = verify(target, circuit.reconstruct(evaluation))
        self.assertNotIn("r12a", {sid for sid, _ in checked.support})

    def test_same_identifier_replacement_deactivates_clause(self):
        source = {"start": [1], "bad": [-1]}
        circuit = compile_horn(source)
        target = {"start": [2], "bad": [-1]}
        evaluation = circuit.evaluate(target)
        self.assertFalse(circuit.survives(evaluation))
        self.assertIn("start", circuit.blocking_cut(evaluation))

    def test_new_equal_body_under_new_identifier_is_not_exact_retention(self):
        source = {"start": [1], "bad": [-1]}
        circuit = compile_horn(source)
        target = {"renamed": [1], "bad": [-1]}
        self.assertFalse(circuit.survives(circuit.evaluate(target)))

    def test_cyclic_source_uses_layered_fixed_point(self):
        source = {"fact": [1], "r12": [-1, 2], "r21": [-2, 1], "bad": [-2]}
        circuit = compile_horn(source)
        self.assertEqual(circuit.strategy, "layered")
        evaluation = circuit.evaluate(source)
        self.assertTrue(circuit.survives(evaluation))
        verify(source, circuit.reconstruct(evaluation))
        with self.assertRaises(Rejected):
            compile_horn(source, strategy="acyclic")

    def test_conjunctive_rule(self):
        source = {"a": [1], "b": [2], "join": [-2, -1, 3], "bad": [-3]}
        circuit = compile_horn(source)
        evaluation = circuit.evaluate(source)
        self.assertTrue(circuit.survives(evaluation))
        self.assertEqual(verify(source, circuit.reconstruct(evaluation)).conclusion, ())

    def test_non_horn_clause_rejected(self):
        with self.assertRaises(Rejected):
            compile_horn({"not_horn": [1, 2]})

    def test_exact_for_every_deletion_subset(self):
        source = {
            "a": [1], "b": [2], "join": [-2, -1, 3],
            "alt": [-1, 3], "bad": [-3],
        }
        circuit = compile_horn(source)
        keys = sorted(source)
        for mask in range(1 << len(keys)):
            target = {sid: source[sid] for i, sid in enumerate(keys) if mask >> i & 1}
            expected = retained_horn_unsat(source, target)
            full = circuit.evaluate(target)
            self.assertEqual(circuit.survives(full), expected)
            if expected:
                verify(target, circuit.reconstruct(full))

    def test_incremental_updates_match_full_evaluation(self):
        source = {"a": [1], "b": [2], "r": [-2, -1, 3], "bad": [-3], "decoy": [-4, 5]}
        circuit = compile_horn(source)
        keys = sorted(source)
        previous = circuit.evaluate(source)
        for mask in range(1 << len(keys)):
            target = {sid: source[sid] for i, sid in enumerate(keys) if mask >> i & 1}
            updated = circuit.update(previous, target)
            full = circuit.evaluate(target)
            self.assertEqual(updated.values, full.values)
            previous = updated

    def test_blocking_cut_is_sufficient(self):
        source = {"a": [1], "b": [2], "join": [-2, -1, 3], "bad": [-3]}
        circuit = compile_horn(source)
        target = {"a": [1], "join": [-2, -1, 3], "bad": [-3]}
        evaluation = circuit.evaluate(target)
        self.assertFalse(circuit.survives(evaluation))
        cut = set(circuit.blocking_cut(evaluation))
        keys = sorted(source)
        for mask in range(1 << len(keys)):
            candidate = {sid: source[sid] for i, sid in enumerate(keys)
                         if mask >> i & 1 and sid not in cut}
            self.assertFalse(circuit.survives(circuit.evaluate(candidate)))

    def test_cross_circuit_evaluation_rejected(self):
        source = {"a": [1], "bad": [-1]}
        first, second = compile_horn(source), compile_horn(source)
        with self.assertRaises(Rejected):
            second.survives(first.evaluate(source))

    def test_malformed_evaluation_rejected(self):
        source = {"a": [1], "bad": [-1]}
        circuit = compile_horn(source)
        evaluation = circuit.evaluate(source)
        with self.assertRaises(Rejected):
            circuit.survives(replace(evaluation, values=evaluation.values[:-1]))
        with self.assertRaises(Rejected):
            circuit.survives(replace(evaluation, values=(1,) + evaluation.values[1:]))

    def test_size_formulas_acyclic_and_layered(self):
        acyclic = compile_horn({"a": [1], "b": [2], "r": [-2, -1, 3], "bad": [-3]})
        cyclic = compile_horn({"a": [1], "r12": [-1, 2], "r21": [-2, 1], "bad": [-2]})
        for circuit in (acyclic, cyclic):
            stats = circuit.stats()
            self.assertTrue(stats["bound_matches"])
            self.assertEqual(stats["gates"], stats["exact_gate_bound"])
            self.assertEqual(stats["edges"], stats["exact_edge_bound"])

    def test_empty_constraint(self):
        source = {"empty": []}
        circuit = compile_horn(source)
        evaluation = circuit.evaluate(source)
        self.assertTrue(circuit.survives(evaluation))
        self.assertEqual(len(circuit.reconstruct(evaluation)["nodes"]), 1)

    def test_no_constraint_has_empty_sufficient_cut(self):
        source = {"fact": [1], "rule": [-1, 2]}
        circuit = compile_horn(source)
        evaluation = circuit.evaluate(source)
        self.assertFalse(circuit.survives(evaluation))
        self.assertEqual(circuit.blocking_cut(evaluation), ())


if __name__ == "__main__":
    unittest.main()
