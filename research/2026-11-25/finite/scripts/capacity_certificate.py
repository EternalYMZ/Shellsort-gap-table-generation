"""Exact finite arithmetic for the two-pass regional Shellsort bound.

Python standard library only.  The coefficient kappa is computed from its
defining finite hypergeometric sum; no asymptotic or conjectured closed form
is used.  All decisions are made with Fraction, never a rounded decimal.
"""
from fractions import Fraction as F
from math import comb, factorial
from functools import lru_cache
from pathlib import Path
import json


def harmonic(m):
    return sum((F(1, j) for j in range(1, m + 1)), F(0))


def kappa(m):
    """1/4 + (1/m) sum_{1<=a<b<=m} P(X_(a)>Y_(b))."""
    row = [comb(m, j) for j in range(m + 1)]
    total = F(0)
    # t=a+b-1. Interchange the finite a and hypergeometric-c sums.
    for t in range(2, 2 * m - 1):
        amin, amax = max(1, t + 1 - m), min(m, t // 2)
        numerator = 0
        for c in range(max(0, t - m), min(m, amax - 1) + 1):
            multiplicity = max(0, amax - max(amin, c + 1) + 1)
            numerator += multiplicity * row[c] * row[t - c]
        total += F(numerator, comb(2 * m, t))
    return F(1, 4) + total / m


def first_mean(m):
    return F(m - 1, 4) + 1 - harmonic(m) / m


def regional_lower(m, ratio, passes):
    k = kappa(m)
    R = F(ratio)
    # The last passes-2 passes really are executed.  Each uses >= n-g
    # comparisons, and pass 2 has >= (n-g)/2 failed comparisons in mean.
    return (first_mean(m) + (R - 1) * k - (k - F(1, 4)) / (4 * R)
            + (F(passes) - F(3, 2)) * (1 - 1 / (m * R)))


def _log_unit_interval(x, terms=48):
    """For 1<=x<=2, exact enclosure using the positive atanh series."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    z2 = z * z
    power = z
    total = F(0)
    for j in range(terms):
        total += 2 * power / (2 * j + 1)
        power *= z2
    remainder = 2 * power / ((2 * terms + 1) * (1 - z2))
    return total, total + remainder


@lru_cache(None)
def log_interval(x):
    """Outward-rounded rational bounds, derived entirely by exact arithmetic."""
    x = F(x)
    assert x > 0
    if x < 1:
        lo, hi = log_interval(1 / x)
        return -hi, -lo
    k = 0
    while x >= 2:
        x /= 2
        k += 1
    lo, hi = _log_unit_interval(x)
    lo2, hi2 = _log_unit_interval(F(2))
    lo, hi = lo + k * lo2, hi + k * hi2
    scale = 10**45
    # Fractions are now outward-rounded to short decimal-rational endpoints.
    lower = (lo.numerator * scale) // lo.denominator
    upper = -((-hi.numerator * scale) // hi.denominator)
    return F(lower, scale), F(upper, scale)


def stronger_region_certificate():
    n, m, passes, R0 = 10**9, 16, 8, 24
    k = kappa(m)
    e0 = (R0 - 1) * k - (k - F(1, 4)) / (4 * R0)
    f0 = (1 - F(1, m * R0)) / 2
    assert e0 > 3
    logn = log_interval(F(n))
    logfac = log_interval(F(factorial(m)))
    loge = log_interval(e0)
    logep = log_interval(e0 + 1)
    log4 = log_interval(F(4))
    denominator = log_interval(F(4, 3))
    gamma_upper = (e0 + 1) * logep[1] - e0 * loge[0]
    gamma_lower = (e0 + 1) * logep[0] - e0 * loge[1]
    numerator_lower = (logn[0] - 1 - logfac[1] / m
                       - gamma_upper - (passes - 2) * log4[1])
    numerator_upper = (logn[1] - 1 - logfac[0] / m
                       - gamma_lower - (passes - 2) * log4[0])
    assert numerator_lower > 0
    base = first_mean(m) + e0 + f0 + passes - 2
    lower = base + numerator_lower / denominator[1]
    upper = base + numerator_upper / denominator[0]
    # Readable outer interval, not the number used in the check.
    assert F(50491696, 10**6) < lower < upper < F(50491697, 10**6)
    target = F(5049, 100)  # 50.49 per key, never rounded upwards.
    assert lower > target
    intervals = {"log_n": logn, "log_16_factorial": logfac,
                 "log_e0": loge, "log_e0_plus_one": logep,
                 "log_4": log4, "log_4_over_3": denominator}
    return {
        "n": n, "first_gap": n // m, "pass_count": passes,
        "second_gap_min": passes - 1,
        "second_gap_max": (n // m) // R0,
        "ratio_lower": R0,
        "temperature": "3/4",
        "second_shift_lower_per_key": str(e0),
        "monotonicity_threshold": 3,
        "failed_comparison_lower_per_key": str(f0),
        "log_intervals": {key: [str(v) for v in pair]
                          for key, pair in intervals.items()},
        "proved_lower_bound_per_key": str(lower),
        "readable_lower_bound_interval": ["50.491696", "50.491697"],
        "target_per_key": str(target),
        "claim_total_strictly_greater_than": int(n * target),
        "passed": True,
        "scope": "Every legal strictly decreasing exactly-eight-pass table "
                 "with h1=62500000, 7<=h2<=2604166, and final gap 1.",
    }


def run():
    n, m, passes, R0 = 10**9, 16, 8, 45
    h = n // m
    bound = regional_lower(m, R0, passes)
    target_per_key = F(251629, 5000)  # 50.3258, exact
    assert n % m == 0
    assert kappa(16) == F(268435456, 300540195)
    assert bound == F(174413632831749931, 3465685269446400)
    assert bound > target_per_key
    result = {
        "n": n,
        "first_gap": h,
        "second_gap_min": passes - 1,
        "second_gap_max": h // R0,
        "pass_count": passes,
        "ratio_lower": R0,
        "kappa_16": str(kappa(m)),
        "lower_bound_per_key": str(bound),
        "target_per_key": str(target_per_key),
        "positive_margin_per_key": str(bound - target_per_key),
        "claim_total_strictly_greater_than": int(n * target_per_key),
        "passed": True,
        "scope": "Every legal strictly decreasing exactly-eight-pass table "
                 "with h1=62500000, 7<=h2<=1388888, and final gap 1.",
    }
    base = Path(__file__).resolve().parent
    (base / "capacity_region_certificate.json").write_text(
        json.dumps(result, indent=2) + "\n")
    table = {str(j): str(kappa(j)) for j in range(1, 202)}
    (base / "kappa_1_to_201.json").write_text(json.dumps(table, indent=2) + "\n")
    stronger = stronger_region_certificate()
    (base / "capacity_region_entropy_certificate.json").write_text(
        json.dumps(stronger, indent=2) + "\n")
    print(json.dumps(result, indent=2))
    print("Wrote 201 exact kappa values computed from finite probability sums.")
    print("Stronger region: h2 <=", stronger["second_gap_max"],
          "certifies EC >", stronger["claim_total_strictly_greater_than"])


if __name__ == "__main__":
    run()
