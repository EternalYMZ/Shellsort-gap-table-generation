"""Strengthened artificial-law certificate, including existing kappa bounds.

Run this file beside coordinate_relaxation_certificate.py.  All arithmetic
used for decisions is exact.  No actual Shellsort execution is simulated.
"""

from fractions import Fraction as F
from functools import lru_cache
from math import comb, gcd
from pathlib import Path
import json

import coordinate_relaxation_certificate as core


N = core.N
GAPS = (62500000, 16000001, 4000003, 1000003, 250007, 62501, 15629, 1)
CAP = core.CAP
T = core.TEMPERATURE


def harmonic(length):
    return sum((F(1, j) for j in range(1, length + 1)), F(0))


def kappa(length):
    """Direct defining hypergeometric finite sum; no conjectured formula."""
    total = F(0)
    for a in range(1, length):
        for b in range(a + 1, length + 1):
            rank = a + b - 1
            numerator = sum(
                comb(length, c) * comb(length, rank - c)
                for c in range(max(0, rank - length), a)
            )
            total += F(numerator, comb(2 * length, rank))
    return F(1, 4) + total / length


@lru_cache(None)
def local_shift_mean(depth):
    costs = [min(m + 1, depth) for m in range(min(CAP, depth) + 1)]
    weights = [T**cost for cost in costs]
    partition = sum(weights, F(0))
    mean = sum((m * weight for m, weight in enumerate(weights)), F(0)) / partition
    record_probability = weights[-1] / partition if depth <= CAP else F(0)
    # The Gibbs weights are nonincreasing in m; the final probability is
    # no greater than the uniform probability.  This also checks it exactly.
    assert record_probability <= F(1, depth + 1)
    return mean


def second_shift_mean(gap):
    mean = F(0)
    finite_count = 0
    for depth in range(1, CAP + 1):
        count = core.coordinate_multiplicity(gap, depth)
        finite_count += count
        mean += count * local_shift_mean(depth)
    tail_count = N - gap - finite_count
    assert tail_count >= 0
    mean += tail_count * local_shift_mean(CAP + 1)
    return mean


def run():
    assert GAPS[0] == core.GAPS[0]
    holes = [core.semigroup_hole_certificate(gap, GAPS[:i])
             for i, gap in enumerate(GAPS) if i]
    first_mean, first_entropy = core.first_pass_exact()
    mean = first_mean
    entropy_lo, entropy_hi = first_entropy
    suffix_entropy_lo = F(0)
    suffix_entropy_hi = F(0)
    rows = []
    second_comparisons = None
    for i, gap in enumerate(GAPS[1:], 1):
        pass_mean, pass_entropy, tail_count = core.suffix_pass(gap)
        mean += pass_mean
        entropy_lo += pass_entropy[0]
        entropy_hi += pass_entropy[1]
        suffix_entropy_lo += pass_entropy[0]
        suffix_entropy_hi += pass_entropy[1]
        if i == 1:
            second_comparisons = pass_mean
        rows.append({
            "gap": gap,
            "mean_per_key": str(pass_mean / N),
            "entropy_per_key_interval": [str(x / N) for x in pass_entropy],
            "tail_coordinates": tail_count,
        })

    n_log = core.log_interval(F(N))
    log_n_factorial_lower = N * n_log[0] - N
    log_n_factorial_upper = (N + 1) * n_log[1] - N + 1
    assert mean < 50 * N
    assert entropy_lo > log_n_factorial_upper
    assert F(45497636, 10**6) < mean / N < F(45497637, 10**6)
    assert F(20506551, 10**6) < entropy_lo / N
    assert entropy_hi / N < F(20506552, 10**6)
    assert (entropy_lo - log_n_factorial_upper) / N > F(78328, 100000)

    h, g = GAPS[:2]
    length = N // h
    coefficient = kappa(length)
    assert coefficient == F(268435456, 300540195)
    ratio = F(h, g)
    shift_lower_per_key = (ratio - 1) * coefficient - (coefficient - F(1, 4)) / (4 * ratio)
    q, r = divmod(N, g)
    same_source_period = h // gcd(h, g)
    assert same_source_period > CAP
    failure_lower = (N - (g - r) * harmonic(min(q, same_source_period))
                     - r * harmonic(min(q + 1, same_source_period)))
    shift_mean = second_shift_mean(g)
    failure_mean = second_comparisons - shift_mean
    assert shift_mean / N > shift_lower_per_key
    assert failure_mean >= failure_lower >= F(N - g, 2)

    # Exact-entropy adjustment: mix the entire suffix law with all-zero
    # shifts, leaving the true first-pass law independent and unchanged.
    # H(mixture) <= log 2 + lambda*H(suffix).  Therefore any mixture attaining
    # total entropy log(n!) must have lambda > 3/4, by this exact inequality.
    log_two_upper = core.log_interval(F(2))[1]
    assert first_entropy[1] + F(3, 4) * suffix_entropy_hi + log_two_upper < log_n_factorial_lower
    assert F(3, 4) * shift_mean / N > shift_lower_per_key
    assert mean - first_mean >= sum(N - gap for gap in GAPS[1:])
    # All-zero shifts have one failed comparison at every insertion, so
    # mixing increases the failure mean relative to the original suffix law.
    assert failure_mean <= N - g

    result = {
        "claim": "limitation of specified record-support/entropy/second-pass-lower-bound relaxation",
        "not_claimed": [
            "a real Shellsort execution law or an actual cost upper bound",
            "infeasibility of proving a universal eight-pass bound by other methods",
            "compliance with exact second-pass block means or all existing P09 results",
            "a uniform law on n! realizable execution logs",
        ],
        "n": N,
        "gaps": list(GAPS),
        "cap": CAP,
        "temperature": str(T),
        "first_pass_exact": True,
        "all_coordinate_support_constraints": True,
        "all_elementary_two_record_shift_constraints": True,
        "second_pass_record_probability_bound": "P(new minimum at depth j) <= 1/(j+1); zero for j>=h/gcd(h,g)",
        "semigroup_hole_certificates": holes,
        "suffix_passes": rows,
        "expected_comparisons_per_key": str(mean / N),
        "expected_comparisons_readable_per_key": ["45.497636", "45.497637"],
        "entropy_per_key_interval": [str(entropy_lo / N), str(entropy_hi / N)],
        "entropy_readable_per_key": ["20.506551", "20.506552"],
        "log_n_factorial_upper_per_key": str(log_n_factorial_upper / N),
        "entropy_margin_per_key_lower": str((entropy_lo - log_n_factorial_upper) / N),
        "kappa_16": str(coefficient),
        "second_pass_ratio": str(ratio),
        "second_pass_shift_mean_per_key": str(shift_mean / N),
        "second_pass_kappa_shift_lower_per_key": str(shift_lower_per_key),
        "second_pass_failure_mean_per_key": str(failure_mean / N),
        "second_pass_harmonic_failure_lower_per_key": str(failure_lower / N),
        "exact_entropy_adjustment": {
            "construction": "independent true first pass; suffix lambda*P+(1-lambda)*delta_allzero",
            "exists_by_continuity": True,
            "lambda_strict_lower": "3/4",
            "cost_does_not_increase": True,
            "kappa_shift_bound_preserved": True,
            "harmonic_failure_bound_preserved": True,
            "all_pointwise_support_and_two_record_constraints_preserved": True,
        },
        "passed": True,
    }
    output = Path(__file__).with_name("coordinate_relaxation_kappa_certificate.json")
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({
        "passed": True,
        "mean_per_key_display": float(mean / N),
        "entropy_per_key_display": float(entropy_lo / N),
        "entropy_margin_per_key_display": float((entropy_lo - log_n_factorial_upper) / N),
        "second_shift_mean_per_key_display": float(shift_mean / N),
        "second_kappa_lower_per_key_display": float(shift_lower_per_key),
        "second_failure_mean_per_key_display": float(failure_mean / N),
        "second_harmonic_lower_per_key_display": float(failure_lower / N),
        "certificate": str(output),
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    run()
