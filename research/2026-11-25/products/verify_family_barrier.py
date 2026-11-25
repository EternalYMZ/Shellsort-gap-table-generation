#!/usr/bin/env python3
"""Reproduce the completed independent finite audit of the family barrier.

This preserves exactly the previously executed inline checks: 56 complete
product tables and their first-pass statistics, 44 finite-law coefficients,
and the integer arithmetic of all 9,777 archived witnesses.  It does not
enumerate sorting inputs, increase the sample domain, or assert that the
artificial record laws are realizable by actual Shellsort executions.

The complete-prefix semigroups and 50-decimal outward rational logarithms
come from the independent verification module, not the barrier producer.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import json
from math import gcd
from pathlib import Path

import family_capacity_barrier as producer
import verify_semigroup_constraints as independent
import verify_producer as producer_review


ROOT = Path(__file__).resolve().parent
SIZES = (2, 7, 40, 64, 65, 66, 100, 257)
BASE_PAIRS = ((2, 3), (5, 34), (11, 12), (57, 98),
              (64, 65), (67, 71), (182, 183))
OLD_INDICES = (1, 2, 16, 63, 64)
GEOMETRIC_INDICES = (0, 1, 2, 16, 63, 64)


def review_support_and_first_pass():
    support_checks = first_checks = 0
    for n in SIZES:
        rows = [producer_review.make_row(n, a, b) for a, b in BASE_PAIRS
                if gcd(a, b) == 1]
        prepared = producer.prepare_first(n, rows)
        for row in rows:
            expected = {'old': Counter(), 'geometric': Counter()}
            specs = independent.stage_specs(n, tuple(row['gaps']))
            for _, _, depths in specs[1:]:
                for j, multiplicity, q in depths:
                    if q == 0 and j <= 64:
                        expected['old'][j] += multiplicity
                    else:
                        cap = min(64, j - q) if q else 64
                        assert cap < j
                        expected['geometric'][cap] += multiplicity
            actual = producer.support_weights(row, n)
            for kind in expected:
                assert +Counter(actual[kind]) == +expected[kind], (row, kind)
            support_checks += 1

            first = producer.first_statistics(row, n, prepared)
            g = row['gaps'][0]
            mean, entropy_lower = F(0), F(0)
            for chain in range(g):
                length = (n - 1 - chain) // g + 1
                for j in range(1, length):
                    mean += sum(F(1 + min(m, j - 1), j + 1)
                                for m in range(j + 1))
                    entropy_lower += independent.log_interval(F(j + 1))[0]
            assert mean == F(first['mean_exact'])
            assert F(first['entropy_lower_scaled'], producer.SCALE) <= entropy_lower
            first_checks += 1
    return support_checks, first_checks


def review_finite_probability_coefficients(report):
    temperatures = sorted({F(report['coefficients'][0]['t']),
                           F(report['coefficients'][-1]['t']),
                           F(13, 100), F(12, 25)})
    checks = 0
    for t in temperatures:
        coeff = producer.temperature_coefficients(t)
        log_t = independent.log_interval(t)
        for kind, indices in (('old', OLD_INDICES),
                              ('geometric', GEOMETRIC_INDICES)):
            for index in indices:
                costs = ([1 + min(m, index - 1) for m in range(index + 1)]
                         if kind == 'old' else list(range(1, index + 2)))
                partition = sum(t ** c for c in costs)
                mean = sum(c * t ** c for c in costs) / partition
                entropy_lower = (independent.log_interval(partition)[0]
                                 - mean * log_t[1])
                coefficient = coeff[kind][index]
                assert F(coefficient['mean_upper_scaled'], producer.SCALE) >= mean
                assert F(coefficient['entropy_lower_scaled'], producer.SCALE) <= entropy_lower, (t, kind, index)
                checks += 1
    return checks, temperatures


def review_witness_arithmetic(report):
    lookup = {c['t']: c for c in report['coefficients']}
    for witness in report['witnesses']:
        coeff = lookup[witness['t']]
        cost = witness['first']['mean_upper_scaled']
        entropy = witness['first']['entropy_lower_scaled']
        for kind in ('old', 'geometric'):
            for index, weight in witness['suffix_support_counts'][kind].items():
                assert isinstance(weight, int) and weight >= 0
                cost += weight * coeff[kind][index]['mean_upper_scaled']
                entropy += weight * coeff[kind][index]['entropy_lower_scaled']
        assert cost == witness['expected_cost_upper_scaled']
        assert entropy == witness['record_entropy_lower_scaled']
        assert cost < 50 * report['n'] * producer.SCALE
        assert entropy > report['log_factorial_upper_scaled']
    return len(report['witnesses'])


def make_result(support_checks, first_checks, coefficient_checks,
                witness_checks, temperatures, execution):
    return {
        'status': 'PASS',
        'execution': execution,
        'source': 'data/family_capacity_barrier.json',
        'counts': {
            'independent_support_histograms': support_checks,
            'first_digit_mean_entropy_checks': first_checks,
            'direct_finite_probability_coefficient_checks': coefficient_checks,
            'witness_integer_sum_and_margin_checks': witness_checks,
        },
        'domain': {
            'n_values': list(SIZES),
            'base_pairs': [list(pair) for pair in BASE_PAIRS],
            'cap': 64,
            'temperatures': [str(t) for t in temperatures],
            'old_indices': list(OLD_INDICES),
            'geometric_indices': list(GEOMETRIC_INDICES),
        },
        'methods': {
            'support': 'Direct complete-prefix semigroup reachability and insertion-depth multiplicities.',
            'first_pass': 'Direct uniform insertion-digit cost averages and sum of log(j+1).',
            'coefficients': 'Direct finite probability normalizers, exact rational means, and independent outward 50-decimal rational log enclosures.',
            'witnesses': 'Recompute every archived integer weighted sum and its strict cost and entropy inequalities.',
        },
        'scope': 'Independent finite checks and mathematical review; not a Lean build or a large-array sorting experiment.',
        'mathematical_review': {
            'blocking_errors_found': False,
            'first_pass_law': 'Independent uniform insertion digits give the stated exact first-pass comparison mean and entropy.',
            'entropy_rounding': 'H=-log(1-t)+log(1+correction)+(mean-1)*log(1/t); the producer rounds the mean upward and entropy downward.',
            'quantifier': 'The artificial law is feasible for the relaxation using coordinatewise supports, total Shannon entropy and cost, with the first-pass law fixed. The obstruction covers common or coordinatewise temperature arguments within that relaxation.',
            'exact_entropy': 'Mix each suffix marginal continuously toward m=0. Cost does not increase; continuity suffices to attain exactly log(n!), without requiring entropy monotonicity along the path.',
            'exclusion': 'No claim of realizable Shellsort records, actual sorting upper bounds, or obstruction to additional joint-state, trajectory or probability constraints.',
        },
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=ROOT / 'data/family_barrier_verification.json')
    args = parser.parse_args()
    report = json.loads((ROOT / 'data/family_capacity_barrier.json').read_text())
    support_checks, first_checks = review_support_and_first_pass()
    coefficient_checks, temperatures = review_finite_probability_coefficients(report)
    witness_checks = review_witness_arithmetic(report)
    result = make_result(support_checks, first_checks, coefficient_checks,
                         witness_checks, temperatures, 'standalone_script')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'counts': result['counts']},
                     ensure_ascii=False))


if __name__ == '__main__':
    main()
