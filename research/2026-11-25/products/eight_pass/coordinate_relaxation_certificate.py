"""Exact certificate for a limitation of a Shellsort record relaxation.

This constructs an artificial record law.  It is NOT a Shellsort execution
law and makes no upper-bound claim about any real gap table.  The law obeys
every coordinatewise prefix-semigroup support constraint, the true first-
pass record law, and the elementary two-record displacement inequalities.
Its entropy exceeds log(n!), while its expected comparisons are below 50n.

Only Python's standard library is used.  Every decision is made with exact
integers/Fractions and outward rational logarithm intervals.  Floats printed
to the terminal are explanatory only.
"""

from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import json


N = 10**9
GAPS = (62500000, 5000003, 400003, 32003, 2503, 197, 101, 1)
CAP = 64
TEMPERATURE = F(5, 6)
LOG_SCALE = 10**45


@lru_cache(None)
def unit_log_interval(x, terms=48):
    """Exact atanh-series enclosure of log(x), for 1 <= x <= 2."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    z2 = z * z
    power = z
    partial = F(0)
    for k in range(terms):
        partial += 2 * power / (2 * k + 1)
        power *= z2
    # After terms terms, power=z^(2*terms+1).  Replace all remaining
    # denominators by the first remaining denominator to bound the tail.
    tail_upper = 2 * power / ((2 * terms + 1) * (1 - z2))
    return partial, partial + tail_upper


@lru_cache(None)
def log_interval(x):
    """Outward-rounded exact rational bounds for the natural logarithm."""
    x = F(x)
    assert x > 0
    if x < 1:
        lo, hi = log_interval(1 / x)
        return -hi, -lo
    exponent = 0
    while x >= 2:
        x /= 2
        exponent += 1
    lo, hi = unit_log_interval(x)
    lo2, hi2 = unit_log_interval(F(2))
    lo += exponent * lo2
    hi += exponent * hi2
    lo_int = (lo.numerator * LOG_SCALE) // lo.denominator
    hi_int = -((-hi.numerator * LOG_SCALE) // hi.denominator)
    return F(lo_int, LOG_SCALE), F(hi_int, LOG_SCALE)


def semigroup_hole_certificate(gap, prefix, cap=CAP):
    """Enumerate every prefix-semigroup sum <= cap*gap, without a huge DP.

    All generators are positive, so a generator larger than the target
    cannot occur.  At each step we add every allowed multiplicity of the
    next generator.  This is a complete enumeration, not a heuristic.
    """
    target = cap * gap
    active = tuple(h for h in prefix if h <= target)
    reachable = {0}
    for h in active:
        reachable = {
            v + copies * h
            for v in reachable
            for copies in range((target - v) // h + 1)
        }
    members = [k for k in range(1, cap + 1) if k * gap in reachable]
    assert members == []
    return {
        "gap": gap,
        "target": target,
        "active_prefix_generators": list(active),
        "all_reachable_sums_through_target": sorted(reachable),
        "members_among_first_64_multiples": members,
    }


@lru_cache(None)
def local_law(depth):
    """A bounded Gibbs law with the exact ordinary-comparison charge.

    For depths > CAP the local law is constant, so CAP+1 represents the
    entire infinite tail.  For depth <= CAP, the record-minimum case has
    charge depth, not depth+1, and is explicitly included.
    """
    assert 1 <= depth <= CAP + 1
    maximum = min(CAP, depth)
    costs = tuple(min(m + 1, depth) for m in range(maximum + 1))
    weights = tuple(TEMPERATURE**c for c in costs)
    partition = sum(weights, F(0))
    mean = sum((c * w for c, w in zip(costs, weights)), F(0)) / partition
    log_z = log_interval(partition)
    log_t = log_interval(TEMPERATURE)
    entropy = (log_z[0] - log_t[1] * mean,
               log_z[1] - log_t[0] * mean)
    return mean, entropy


def coordinate_multiplicity(gap, depth, n=N):
    """Number of gap-chain positions with this depth, for indices 0..n-1."""
    return max(0, min(gap, n - depth * gap))


def first_pass_exact():
    gap = GAPS[0]
    assert N % gap == 0
    length = N // gap
    harmonic = sum((F(1, k) for k in range(1, length + 1)), F(0))
    per_chain = F(length * (length - 1), 4) + length - harmonic
    mean = gap * per_chain
    log_factorial = log_interval(F(factorial(length)))
    entropy = tuple(gap * x for x in log_factorial)
    return mean, entropy


def suffix_pass(gap):
    mean = F(0)
    entropy_lo = F(0)
    entropy_hi = F(0)
    finite_count = 0
    for depth in range(1, CAP + 1):
        multiplicity = coordinate_multiplicity(gap, depth)
        finite_count += multiplicity
        local_mean, (local_lo, local_hi) = local_law(depth)
        mean += multiplicity * local_mean
        entropy_lo += multiplicity * local_lo
        entropy_hi += multiplicity * local_hi
    tail_count = N - gap - finite_count
    assert tail_count >= 0
    tail_mean, (tail_lo, tail_hi) = local_law(CAP + 1)
    mean += tail_count * tail_mean
    entropy_lo += tail_count * tail_lo
    entropy_hi += tail_count * tail_hi
    return mean, (entropy_lo, entropy_hi), tail_count


def interval_strings(interval):
    return [str(value) for value in interval]


def run():
    holes = [semigroup_hole_certificate(gap, GAPS[:index])
             for index, gap in enumerate(GAPS) if index]
    mean, entropy = first_pass_exact()
    entropy_lo, entropy_hi = entropy
    first_mean, first_entropy = mean, entropy
    passes = [{
        "gap": GAPS[0],
        "law": "true uniform-input first-pass insertion-rank law",
        "mean_per_key": str(mean / N),
        "entropy_per_key_interval": interval_strings((x / N for x in entropy)),
    }]
    for gap in GAPS[1:]:
        pass_mean, pass_entropy, tail_count = suffix_pass(gap)
        mean += pass_mean
        entropy_lo += pass_entropy[0]
        entropy_hi += pass_entropy[1]
        passes.append({
            "gap": gap,
            "law": "independent coordinate Gibbs laws, cap 64, t=5/6",
            "mean_per_key": str(pass_mean / N),
            "entropy_per_key_interval": interval_strings(x / N for x in pass_entropy),
            "tail_coordinate_count": tail_count,
        })

    log_n = log_interval(F(N))
    # Sum_{k=1}^{n-1} log k <= integral_1^n log x dx.
    log_factorial_upper = (N + 1) * log_n[1] - N + 1
    assert mean < 50 * N
    assert entropy_lo > log_factorial_upper
    assert F(46271002, 10**6) < mean / N < F(46271003, 10**6)
    assert F(20754971, 10**6) < entropy_lo / N
    assert entropy_hi / N < F(20754972, 10**6)
    assert log_factorial_upper / N < F(19723266, 10**6)
    assert (entropy_lo - log_factorial_upper) / N > F(10317, 10000)

    result = {
        "claim": "limitation of coordinate-support entropy relaxation only",
        "not_claimed": "an actual Shellsort execution law or a cost upper bound",
        "n": N,
        "gaps": list(GAPS),
        "cap": CAP,
        "temperature": str(TEMPERATURE),
        "first_pass_exact": True,
        "all_coordinate_support_constraints": True,
        "all_elementary_two_record_shift_constraints": True,
        "semigroup_hole_certificates": holes,
        "passes": passes,
        "expected_comparisons": str(mean),
        "expected_comparisons_per_key": str(mean / N),
        "expected_comparisons_per_key_readable_interval": ["46.271002", "46.271003"],
        "entropy_per_key_interval": interval_strings((entropy_lo / N, entropy_hi / N)),
        "entropy_per_key_readable_interval": ["20.754971", "20.754972"],
        "log_n_factorial_upper_per_key": str(log_factorial_upper / N),
        "log_n_factorial_readable_upper_per_key": "19.723266",
        "entropy_margin_per_key_lower": str((entropy_lo - log_factorial_upper) / N),
        "entropy_margin_per_key_readable_lower": "1.0317",
        "first_pass_expected_comparisons_per_key": str(first_mean / N),
        "first_pass_entropy_per_key_interval": interval_strings(x / N for x in first_entropy),
        "passed": True,
    }
    output = Path(__file__).with_name("coordinate_relaxation_certificate.json")
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({
        "passed": True,
        "mean_per_key_display": float(mean / N),
        "entropy_per_key_display": float(entropy_lo / N),
        "log_n_factorial_upper_per_key_display": float(log_factorial_upper / N),
        "entropy_margin_per_key_display": float((entropy_lo - log_factorial_upper) / N),
        "certificate": str(output),
    }, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    run()
