"""Check five frozen P09 releases without extracting or executing their code.

Pass the restored Project-S_Latest_Complete_20261125 directory as the argument.
This replays finite coverage, cost aggregation, rounding and witness identities.
The probability kernels and entropy inequalities are inputs to this check.
"""
import argparse
import hashlib
import json
import zipfile
from contextlib import ExitStack
from fractions import Fraction as F
from math import gcd
from pathlib import Path


N = 1_000_000_000
GAPS = (62_500_000, 16_000_001, 4_000_003, 1_000_003, 250_007, 62_501, 15_629, 1)
HASHES = (
    "5aeb98cdde45b1b3b8a32846b320c4970dd649cc6e6719814b4274aea6ff42a6",
    "c5a70cedf73ebe398540ace6d334df5f218f18431088b5883d40f491896e8cf1",
    "2ff73034035c7b70aac01cf76756431624d6f9c339a52b7fcd078de5c02168ea",
    "cd0388baf6360fdd34cc6f421b90c965ef059b1e479726750a435d8f80ac08be",
    "e0a5e204ebeba31127c5832a00352d65c50b96ab72a04e4818d32e05f34192be",
)


def read(archive, name):
    directory = archive.namelist()[0].split("/", 1)[0]
    with archive.open(f"{directory}/{name}.json") as stream:
        return json.load(stream)


def check_sources():
    h, g2, g3, g4 = GAPS[:4]
    # Two positions can share an original h-chain only when their difference
    # after tracing the two g3 chains agrees modulo g2 with k*h, |k|<=15.
    residues = {k * h % g2 for k in range(-15, 16)}
    assert all(delta * g3 % g2 not in residues for delta in range(1, 250))
    shared = {}
    for d in range(1, N // g4 + 1):
        starts = N - d * g4
        differences = [d * g4 + a * g3 for a in range(-498, 499)]
        possible = [e for e in differences if abs(e) < N and e % g2 in residues]
        if not possible:
            continue
        assert len(possible) == 1
        e, = possible
        low, high = max(0, -e), min(N, N - e)
        if high - low >= g3:
            shared[d] = starts
        else:
            # Count legal starts in each residue of this one partial interval.
            periods, tail = divmod(starts, g3)
            shared[d] = sum(periods + (s % g3 < tail) for s in range(low, high))
    assert len(shared) == 104 and sum(shared.values()) == 87_599_939_100
    all_pairs = sum(N - d * g4 for d in range(1, N // g4 + 1))
    assert all_pairs - sum(shared.values()) == 411_898_562_400
    return shared


def check_cost(doc, prior, shared):
    gap = GAPS[3]
    assert doc["n"] == N and tuple(doc["gaps_prefix"]) == GAPS[:4]
    assert set(doc["possible_shared_distances"]) == shared.keys()
    lo_moves = hi_moves = lo_records = hi_records = lo_cost = hi_cost = F(0)
    cursor = sites = types = 0
    by_distance = {d: [F(0), F(0)] for d in shared}
    for phase in doc["phases"]:
        stop = phase["upper_residue_exclusive"]
        w = stop - cursor
        assert cursor == phase["lower_residue"] and w == phase["multiplicity"] > 0
        size = phase["chain_length"]
        assert size == (N - 1 - cursor) // gap + 1 == (N - stop) // gap + 1
        assert len(phase["rows"]) == size - 1
        for j, row in enumerate(phase["rows"], 1):
            a, b = F(row["mean_lower"]), F(row["mean_upper"])
            beta = F(row["record_probability_upper"])
            alpha = max(0, a - j + 1)
            assert row["depth"] == j and 0 <= a <= b <= j and 0 <= alpha <= beta <= 1
            lo_moves += w * a
            hi_moves += w * b
            lo_records += w * alpha
            hi_records += w * beta
            lo_cost += w * max(a + 1 - beta, 1 + F(j - 1, j) * a)
            hi_cost += w * min(j, b + 1 - alpha)
        assert {r["distance"] for r in phase["shared_distance_bounds"]} == shared.keys()
        for row in phase["shared_distance_bounds"]:
            d = row["distance"]
            assert row["pair_count_per_residue"] == size - d
            by_distance[d][0] += w * F(row["probability_lower_sum"])
            by_distance[d][1] += w * F(row["probability_upper_sum"])
        sites += w * size
        types += size - 1
        cursor = stop
    assert (cursor, sites, types) == (gap, N, 3995)
    assert (lo_moves, hi_moves) == tuple(F(doc[k]) for k in ("marginal_moves_lower", "marginal_moves_upper"))
    assert (lo_cost, hi_cost) == tuple(F(doc[k]) for k in ("marginal_comparison_lower", "marginal_comparison_upper"))
    credit = max(0, F(doc["distance44_retained_family_lower"]) - by_distance[44][0])
    slope = lo_cost + F(43, 44) * credit
    lo_moves += credit
    joint = {r["distance"]: r for r in prior["distance_rows"]}
    assert 44 not in joint and len(joint) == 14
    assert {r["distance"] for r in doc["joint_distance_replacements"]} == joint.keys()
    for d, row in joint.items():
        low, high = by_distance[d]
        gain = max(0, F(row["joint_lower"]) - low)
        lo_moves += gain
        hi_moves -= max(0, high - F(row["joint_upper"]))
        slope += F(d - 1, d) * gain
    low = max(slope, lo_moves + N - gap - hi_records, F(prior["comparison_lower"]))
    high = min(hi_cost, hi_moves + N - gap - lo_records, F(prior["comparison_upper"]))
    assert (low, high) == (F(doc["comparison_lower"]), F(doc["comparison_upper"]))
    assert doc["comparison_lower_floor"] < low <= high < doc["comparison_upper_ceiling"]
    return doc["comparison_lower_floor"], doc["comparison_upper_ceiling"]


def replay(archives):
    a, b, c, d, e = archives
    baseline = read(a, "source/eight_pass_20261124/certificates/kappa_two_temperature_certificate")
    for row, target in zip(baseline["pass_results"], (50_054_104_988, 40_912_368_737), strict=True):
        assert target < N * F(row["uniform_per_key_bound"]["lower"]) < target + 1
    previous = read(a, "source/eight_pass_20261124/certificates/capacity_region_entropy_certificate")
    region = read(a, "exact_second_block")["extended_first_two_gap_region"]
    h = GAPS[0]
    assert (previous["pass_count"], previous["first_gap"], previous["second_gap_min"], previous["second_gap_max"]) == (8, h, 7, 2_604_166)
    assert F(previous["proved_lower_bound_per_key"]) * N > 50_490_000_000
    assert (region["first_gap"], region["new_second_gap_min"], region["new_second_gap_max"]) == (h, 2_604_167, 2_850_000)
    exceptional = [(g, g // gcd(h, g)) for g in range(2_604_167, 2_850_001) if g // gcd(h, g) < 16]
    assert exceptional == [(2_734_375, 7), (2_750_000, 11), (2_812_500, 9)]
    assert 50_002_479_509 < F(region["bound_per_key"]) * N < 50_002_479_510
    family = read(a, "data/first_gap_family_certificate")
    assert family["combined_covered_integer_gaps"] == h - 7
    cursor = 2_850_001
    floors = []
    for cell in family["certificate_cells"]:
        end = cell["second_gap_max"]
        assert cell["second_gap_min"] == cursor <= end
        assert {r["second_gap"] for r in cell["endpoints"]} == {cursor, end}
        for row in cell["endpoints"]:
            numerator = (F(family["input_entropy_lower"]) - F(family["first_entropy_upper"])
                         - F(row["second_entropy_tangent_upper"]) - F(family["tail_log_partition_upper"]))
            lmin, lmax = map(F, family["log_inverse_temperature_interval"])
            suffix = numerator / (lmax if numerator >= 0 else lmin)
            value = F(family["first_cost"]) + F(row["second_shift_mean"]) + F(row["second_failed_lower"]) + suffix
            assert value == F(row["total_lower"])
            floors.append(value)
        cursor = end + 1
    assert cursor == h and len(family["certificate_cells"]) == 1759 and len(floors) == 3437
    assert min(floors) == F(family["weakest_certified_endpoint"]["total_lower"])
    assert 41_101_012_178 < min(floors) < 41_101_012_179
    shared = check_sources()
    old = read(c, "data/fourth_full_cost")
    prev = read(d, "data/shared_cost_grid2048")
    covered = omitted = 0
    for row in prev["distance_rows"]:
        distance = row["distance"]
        raw = read(d, row["source_file"].removesuffix(".json"))
        scale = 2 ** raw["fixed_point_bits"]
        count = N - distance * GAPS[3]
        assert row["covered_pairs"] + row["omitted_pairs"] == count == shared[distance]
        assert F(row["joint_lower"]) == F(raw["selected_lower_scaled"], scale)
        assert F(row["joint_upper"]) == F(raw["selected_upper_scaled"], scale) + row["omitted_pairs"]
        covered += row["covered_pairs"]
        omitted += row["omitted_pairs"]
    assert (covered, omitted) == (13_671_197_442, 20_801_634)
    total = read(a, "data/combined_third_pass_certificate")["best_witness"]["total_comparison_lower"]
    third = read(a, "joint_rank_grid256_full")
    assert 4_548_852_759 < F(third["comparisons_lower_exact"]) <= F(third["comparisons_upper_exact"]) < 5_036_388_572
    bounds = [F(total), F(read(b, "data/third_profile_variational_certificate")["best_comparison_lower"]),
              F(read(c, "data/fourth_full_variational")["best_comparison_lower"]),
              F(read(d, "data/combined_variational")["comparison_lower"])]
    fourth = [(old["comparison_lower_floor"], old["comparison_upper_ceiling"]),
              (prev["comparison_lower_floor"], prev["comparison_upper_ceiling"])]
    for document, (low, high) in zip((old, prev), fourth):
        assert low < F(document["comparison_lower"]) <= F(document["comparison_upper"]) < high
    for grid in (4096, 8192):
        cost = read(e, f"data/refined_full_cost_grid{grid}")
        fourth.append(check_cost(cost, prev, shared))
        tilt = read(e, f"data/reopt_scale_variational_grid{grid}")
        gain = F(tilt["information_gain_from_old_full_fourth"])
        lo_log, hi_log = map(F, tilt["old_L_interval"])
        assert gain > 0 and 0 < lo_log < hi_log and tuple(tilt["gaps"]) == GAPS
        bound = bounds[2] + gain / hi_log
        assert bound == F(tilt["best_comparison_lower"])
        bounds.append(bound)
    integers = (41573992787, 41628458196, 41630465084, 41637062522, 41640442357, 41641698503)
    assert all(k < x < k + 1 for x, k in zip(bounds, integers, strict=True))
    assert fourth == [(3913419537, 7776534589), (5074893131, 5352596032),
                      (5115314824, 5307960825), (5135574733, 5287379676)]
    print("Fixed first gap 62500000: > 50002479509 through second gap 2850000; > 41101012178 for all second gaps")
    print("6 strict fixed-table lower endpoints:", *integers)
    print("4 fourth-pass open intervals:", fourth)
    print("999 distances, 104 shared, 3995 depth rows per refined grid; all checks passed")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O so all exact checks are enabled.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("restored_root", type=Path)
    root = parser.parse_args().restored_root / "03_P09"
    with ExitStack() as stack:
        archives = []
        for i, digest in enumerate(HASHES, 1):
            path, = root.glob(f"{i:02d}_*/*.zip")
            with path.open("rb") as stream:
                assert hashlib.file_digest(stream, "sha256").hexdigest() == digest, path
            archives.append(stack.enter_context(zipfile.ZipFile(path)))
        replay(archives)
