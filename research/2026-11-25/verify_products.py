"""Rebuild every product-table bound and relaxation witness, without sorting a billion keys."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def run(folder, script, *args):
    subprocess.run([sys.executable, str(folder / script), *args], cwd=folder,
                   env={**os.environ, "PYTHONUTF8": "1"}, check=True,
                   stdout=subprocess.DEVNULL)
    print("PASS", script, flush=True)

def check_products(folder):
    run(folder, "gap_batch.py", "--output", "source")
    run(folder, "source/evaluate_gap_lower_bounds.py", "source/gap_tables.jsonl",
        "--output", "source/gap_lower_bounds.jsonl", "--summary", "source/gap_lower_bound_summary.json",
        "--coefficient-certificate", "source/gibbs_coefficient_certificate.json")
    run(folder, "evaluate_semigroup_bounds.py")
    run(folder, "certify_selected_temperatures.py")
    run(folder, "family_capacity_barrier.py")
    run(folder, "verify_producer.py", "--old-results", "source/gap_lower_bounds.jsonl",
        "--new-results", "data/semigroup_gap_lower_bounds.jsonl")
    run(folder, "verify_family_barrier.py")
    run(folder, "eight_pass/coordinate_relaxation_kappa_certificate.py")
    data = folder / "data"
    with (data / "combined_gap_lower_bounds.jsonl").open(encoding="utf-8") as file:
        rows = [json.loads(line) for line in file]
    excluded = [r for r in rows if r["certified_comparison_lower_bound"] > 50_000_000_000]
    remaining = {(r["a"], r["b"]) for r in rows if r["certified_comparison_lower_bound"] <= 50_000_000_000}
    assert len(rows) == 16471 and len({tuple(r["gaps"]) for r in rows}) == 16462
    assert len(excluded) == 6694 and len(remaining) == 9777
    assert sum(r["semigroup_original_grid_gain"] > 0 for r in rows) == 1765
    assert all(r["previous_certified_comparison_lower_bound"] > 50_000_000_000 for r in excluded)
    barrier = json.loads((data / "family_capacity_barrier.json").read_text(encoding="utf-8"))
    witnesses = barrier["witnesses"]
    assert len(witnesses) == len(remaining) and {(w["a"], w["b"]) for w in witnesses} == remaining
    for w in witnesses:
        assert int(w["expected_cost_upper_scaled"]) < 49_900_000_000 * int(barrier["scale"])
        assert int(w["record_entropy_lower_scaled"]) > int(barrier["log_factorial_upper_scaled"])
    print(f"{len(excluded)} parameter pairs excluded; {len(witnesses)} relaxation witnesses", flush=True)

if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="p09-products-") as tmp:
        copy = Path(tmp) / "products"
        shutil.copytree(ROOT / "products", copy)
        check_products(copy)
