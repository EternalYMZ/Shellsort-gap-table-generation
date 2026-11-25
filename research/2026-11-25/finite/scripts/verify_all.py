#!/usr/bin/env python3
"""Reproduce the exact certificates in an isolated temporary directory.

Python standard library only.  This checks finite arithmetic and the specified
eight-key exhaustive counterexample; the analytic lemmas are in the chapters.
Existing delivered certificates are never overwritten.
"""
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile


def main():
    source = Path(__file__).resolve().parent
    jobs = [
        ("entropy_baseline.py", ["--output", "entropy_baseline_certificate.json"]),
        ("two_temperature_certificate.py", ["--output", "two_temperature_certificate.json"]),
        ("kappa_two_temperature_certificate.py", ["--output", "kappa_two_temperature_certificate.json"]),
        ("capacity_certificate.py", []),
        ("verify_structure_extension.py", ["--enumerate", "--output", "structure_certificate.json"]),
    ]
    with tempfile.TemporaryDirectory(prefix="shellsort_eight_pass_") as directory:
        target = Path(directory)
        for name, _ in jobs:
            shutil.copy2(source / name, target / name)
        for name, arguments in jobs:
            result = subprocess.run([sys.executable, str(target / name), *arguments],
                                    cwd=target, capture_output=True, text=True)
            if result.returncode:
                print(result.stdout)
                print(result.stderr, file=sys.stderr)
                raise SystemExit(result.returncode)
            print("PASS", name)
        def read(name):
            return json.loads((target / name).read_text(encoding="utf-8"))
        baseline = read("entropy_baseline_certificate.json")
        same_row = read("two_temperature_certificate.json")
        kappa = read("kappa_two_temperature_certificate.json")
        regional = read("capacity_region_entropy_certificate.json")
        transport = read("structure_certificate.json")
        assert baseline["passed"] and same_row["passed"] and kappa["passed"]
        assert regional["passed"]
        bounds = {r["at_most_passes"]: r["total_comparison_lower_bound"]
                  for r in kappa["pass_results"]}
        assert bounds == {7: 50054104988, 8: 40912368737}
        assert regional["claim_total_strictly_greater_than"] == 50490000000
        assert transport["gcd_transport"]["suffix_max_gap_3_lower_bound"] == 63393814526
        assert transport["counterexample"]["probability"] == "29/56"
        print(json.dumps({"passed": True, "n": 10**9,
                          "uniform_comparison_lower_bounds": bounds,
                          "eight_pass_region_strict_bound": 50490000000,
                          "gcd_prefix_suffix_gap_at_most_3_bound": 63393814526,
                          "arbitrary_prefix_record_counterexample": "29/56",
                          "scope": "Exact finite certificates, not Lean formalization."},
                         ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
