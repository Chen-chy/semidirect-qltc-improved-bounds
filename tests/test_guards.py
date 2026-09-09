"""Regression tests for validation scope and failure handling."""
import os
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]


class VerificationGuardTests(unittest.TestCase):
    def test_optimized_verifier_is_rejected(self):
        proc = subprocess.run([sys.executable, "-O", "scripts/verify.py"], cwd=ROOT,
                              capture_output=True, text=True, timeout=20)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("Refusing optimized Python", proc.stderr)

    def test_baseline_output_path_is_rejected(self):
        proc = subprocess.run([sys.executable, "scripts/verify.py", "--output",
                               "verification/baseline"], cwd=ROOT, capture_output=True,
                              text=True, timeout=20)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("Output must be inside", proc.stderr)

    def test_optimized_standalone_chain_check_is_rejected(self):
        proc = subprocess.run([sys.executable, "-O", "experiments/check_t4_chains.py"],
                              cwd=ROOT, capture_output=True, text=True, timeout=20)
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("Refusing optimized Python", proc.stderr)


if __name__ == "__main__":
    unittest.main()
