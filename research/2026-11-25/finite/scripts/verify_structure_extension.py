#!/usr/bin/env python3
"""Exact arithmetic for the structural extensions; no simulation claims.

The mathematical arguments are in structure_extension.md.  This script checks
the explicitly stated rational constants and optionally enumerates the eight-
key counterexample to extending a second-pass record bound to arbitrary
prefixes.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from math import comb, factorial, isqrt
from pathlib import Path


def continuous_first_pass_constant(length: int) -> Fraction:
    """Sum_j integral_{j/L}^{(j+1)/L} E|U_{j+1:L}-x| dx."""
    out = Fraction()
    for j in range(length):
        a, b = Fraction(j, length), Fraction(j + 1, length)
        value = Fraction(j + 1, length + 1) * (b - a) - (b * b - a * a) / 2
        for r in range(j + 1, length + 1):
            for v in range(length - r + 1):
                k = r + v
                coefficient = comb(length, r) * comb(length - r, v) * (-1) ** v
                value += (
                    2
                    * coefficient
                    * (b ** (k + 2) - a ** (k + 2))
                    / ((k + 1) * (k + 2))
                )
        out += value
    return out


def first_pass_mean_per_key(length: int) -> Fraction:
    harmonic = sum((Fraction(1, j) for j in range(1, length + 1)), Fraction())
    return Fraction(length - 1, 4) + 1 - harmonic / length


def ceil_fraction(value: Fraction) -> int:
    return -(-value.numerator // value.denominator)


def count_record_counterexample() -> dict[str, object]:
    # Complete enumeration, not a Monte Carlo estimate.  At the next gap-1
    # insertion of position 1, a new minimum is exactly state[1] < state[0].
    count = 0
    for perm in itertools.permutations(range(8)):
        state = list(perm)
        for gap in (5, 3):
            for residue in range(gap):
                state[residue::gap] = sorted(state[residue::gap])
        count += state[1] < state[0]
    probability = Fraction(count, factorial(8))
    assert count == 20880
    assert probability == Fraction(29, 56)
    assert probability > Fraction(1, 2)
    return {"n": 8, "prefix": [5, 3], "next_gap": 1,
            "depth": 1, "count": count, "total": factorial(8),
            "probability": str(probability)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--enumerate", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    n = 10**9

    # sqrt(n^3 / 27648) = n sqrt(n) / (96 sqrt(3)).
    lower = isqrt(n**3 // 27648)
    slack = n**3 - 27648 * lower * lower
    next_slack = 27648 * (lower + 1) ** 2 - n**3
    assert lower == 190_181_443_578
    assert slack >= 0 and next_slack > 0
    assert lower % 3 == 0
    assert lower // 3 == 63_393_814_526 > 50_000_000_000

    c16 = continuous_first_pass_constant(16)
    assert c16 == Fraction(8_507_735_836_635_473, 108_086_391_056_891_904)
    a16 = first_pass_mean_per_key(16)
    assert a16 == Fraction(52_338_161, 11_531_520)
    footrule_bound = c16 * n * n - Fraction(33, 2) * n
    max_suffix_gap_bound = footrule_bound / (2 * (50 - a16) * n)
    assert ceil_fraction(max_suffix_gap_bound) == 865_708

    result: dict[str, object] = {
        "n": n,
        "gcd_transport": {
            "integer_lower_bound": lower,
            "square_certificate_slack": slack,
            "next_integer_square_excess": next_slack,
            "suffix_max_gap_3_lower_bound": lower // 3,
        },
        "first_pass_length_16": {
            "c16": str(c16),
            "a16": str(a16),
            "footrule_lower_bound": str(footrule_bound),
            "max_suffix_gap_necessary_bound": str(max_suffix_gap_bound),
            "max_suffix_gap_necessary_integer": ceil_fraction(max_suffix_gap_bound),
        },
    }
    if args.enumerate:
        result["counterexample"] = count_record_counterexample()
    text = json.dumps(result, ensure_ascii=False, indent=2)
    print(text)
    if args.output:
        args.output.write_text(text + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
