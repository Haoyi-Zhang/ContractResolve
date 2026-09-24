"""Regression tests for the independent row-level result audit."""
from __future__ import annotations

import json
import shutil
import sys
import tempfile
from pathlib import Path
import unittest

SRC = Path(__file__).resolve().parents[1] / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from result_audit import AuditError, audit


class ResultAuditTests(unittest.TestCase):
    @property
    def result_root(self) -> Path:
        return Path(__file__).resolve().parents[1] / "results"

    def test_bundled_results_pass_independent_aggregation(self):
        report = audit(self.result_root)
        self.assertTrue(report["success"])
        self.assertGreaterEqual(len(report["checks"]), 12)
        self.assertEqual(report["key_claims"]["two_variable_closed_misses"], 0)
        self.assertEqual(report["key_claims"]["two_variable_all_source_deletion_pairs"], 19683)
        self.assertEqual(report["key_claims"]["two_variable_all_source_deletion_mismatches"], 0)
        self.assertEqual(report["key_claims"]["three_variable_closed_misses"], 0)
        self.assertEqual(report["key_claims"]["horn_complete_pairs"], 9921)
        self.assertEqual(report["key_claims"]["horn_scale_max_clauses"], 16420)

    def test_audit_rejects_missing_all_subset_pair(self):
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "results"
            shutil.copytree(self.result_root, copied)
            path = copied / "all-subsets" / "all-subsets.csv"
            lines = path.read_text(encoding="utf-8").splitlines()
            path.write_text("\n".join(lines[:-1]) + "\n", encoding="utf-8")
            with self.assertRaises(AuditError):
                audit(copied)

    def test_audit_rejects_corrupted_circuit_count(self):
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "results"
            shutil.copytree(self.result_root, copied)
            path = copied / "survival" / "circuit-stats.json"
            rows = json.loads(path.read_text(encoding="utf-8"))
            rows[0]["closed"]["gates"] += 1
            path.write_text(json.dumps(rows, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(AuditError):
                audit(copied)


    def test_audit_rejects_missing_horn_pair(self):
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "results"
            shutil.copytree(self.result_root, copied)
            path = copied / "horn" / "horn-exhaustive.csv"
            lines = path.read_text(encoding="utf-8").splitlines()
            path.write_text("\n".join(lines[:-1]) + "\n", encoding="utf-8")
            with self.assertRaises(AuditError):
                audit(copied)

    def test_audit_rejects_corrupted_horn_gate_count(self):
        with tempfile.TemporaryDirectory() as directory:
            copied = Path(directory) / "results"
            shutil.copytree(self.result_root, copied)
            path = copied / "horn" / "horn-summary.json"
            summary = json.loads(path.read_text(encoding="utf-8"))
            summary["scalable_contract_graphs"]["instances"][0]["gates"] += 1
            path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
            with self.assertRaises(AuditError):
                audit(copied)


if __name__ == "__main__":
    unittest.main(verbosity=2)
