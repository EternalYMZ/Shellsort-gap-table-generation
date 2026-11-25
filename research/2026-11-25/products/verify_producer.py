#!/usr/bin/env python3
"""Independent end-to-end checks of the semigroup certificate producer.

Uses complete product tables at n=2..40, 2<=a<=8, a<b<=11.  Complete
prefix semigroups and finite insertion capacities are constructed directly.
They are compared against producer interval weights, rounded log upper
bounds, and returned certificates.  Only two targeted true-mean enumerations
are repeated (5,760 inputs total); the earlier 173,870 pairs are not rerun.

The independent rational logarithm and ordinary insertion runner live in
verify_semigroup_constraints.py.  No producer source or old dataset is edited.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from itertools import permutations
from math import factorial, gcd
from pathlib import Path
import argparse
import json
import sys

import verify_semigroup_constraints as independent


ROOT = Path(__file__).resolve().parent


def load_producer(path):
    sys.path.insert(0, str(path.resolve().parent))
    spec = spec_from_file_location('semigroup_producer_under_review', path)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    # Memoizing this unchanged pure builder avoids rebuilding the identical
    # 20 temperature certificates for each small n. No value is modified.
    module.legacy.temperature_data = lru_cache(None)(module.legacy.temperature_data)
    return module


def direct_product_gaps(n, a, b):
    pa, pb = [1], [1]
    while pa[-1] * a < n:
        pa.append(pa[-1] * a)
    while pb[-1] * b < n:
        pb.append(pb[-1] * b)
    return sorted({x * y for x in pa for y in pb if x * y < n}, reverse=True)


def make_row(n, a, b):
    gaps = direct_product_gaps(n, a, b)
    return {'n': n, 'a': a, 'b': b, 'gcd': gcd(a, b),
            'coprime': gcd(a, b) == 1, 'passes': len(gaps), 'gaps': gaps}


def audit_log_one_plus(producer):
    eps = F(1, 10 ** 18)
    tiny = F(1, 10 ** 12)
    quarter = F(1, 4)
    values = {F(0), F(-999999, 1000000), F(-3, 4), F(-1, 2),
              F(1, 2), F(3, 4), F(99, 100)}
    for pivot in (-tiny, tiny, -quarter, quarter):
        values.update((pivot - eps, pivot, pivot + eps))
    values.update((F(1, 10 ** 30), F(-1, 10 ** 30)))
    branches = Counter()
    for y in sorted(values):
        upper = F(producer.log_one_plus_upper(y), producer.SCALE)
        lo, hi = independent.log_interval(1 + y)
        assert lo <= hi <= upper, (y, lo, hi, upper)
        branch = 'tiny_linear' if abs(y) <= tiny else ('signed_atanh' if abs(y) <= quarter else 'legacy_log')
        branches[branch] += 1
    return {'cases': len(values), 'branches': dict(branches),
            'passed': True, 'method': 'compare against independent outward 50-decimal rational enclosures'}


def direct_weight_data(row):
    n, a, b = row['n'], row['a'], row['b']
    full, suffix = Counter(), Counter()
    specs = independent.stage_specs(n, tuple(row['gaps']))
    two_generator = independent.semigroup_reachability((a, b), n - 1)
    holes, running = {}, 0
    for j in range(1, n):
        running += not two_generator[j]
        holes[j] = running
    membership_checks = 0
    for index, (g, _, rows) in enumerate(specs):
        for depth, multiplicity, actual_q in rows:
            q_two = depth - holes[depth]
            assert q_two <= actual_q
            if row['coprime']:
                assert q_two == actual_q
            membership_checks += 1
            full[depth] += multiplicity
            if index:
                suffix[depth] += multiplicity
    return specs, holes, full, suffix, membership_checks


def check_weights(row, producer, cutoff, data):
    _, holes, full, suffix, _ = data
    weights = producer.make_weights(row, row['n'], cutoff)
    assert weights['scan'] == sum(full.values())
    assert weights['suffix_scan'] == sum(suffix.values())
    assert weights['early'] == [(j, full[j], suffix[j]) for j in range(1, row['a'])]
    expected_full, expected_suffix = Counter(), Counter()
    for j in range(row['a'], row['n']):
        if holes[j] <= cutoff:
            expected_full[holes[j]] += full[j]
            expected_suffix[holes[j]] += suffix[j]
    actual_full, actual_suffix = Counter(), Counter()
    for count, w, v in weights['caps']:
        assert isinstance(w, int) and isinstance(v, int) and 0 <= v <= w
        actual_full[count] += w
        actual_suffix[count] += v
    assert actual_full == +expected_full
    assert actual_suffix == +expected_suffix
    return weights


def exact_log_partitions(specs, temperature):
    t = F(temperature)
    full_lo = full_hi = suffix_lo = suffix_hi = F(0)
    for index, (_, _, rows) in enumerate(specs):
        for depth, multiplicity, q in rows:
            z = independent.local_capacity(depth, q, t)
            lo, hi = independent.log_interval(z)
            full_lo += multiplicity * lo
            full_hi += multiplicity * hi
            if index:
                suffix_lo += multiplicity * lo
                suffix_hi += multiplicity * hi
    return (full_lo, full_hi), (suffix_lo, suffix_hi)


def upper_quotient(numerator_upper, denominator_interval):
    lo, hi = denominator_interval
    assert lo > 0
    return numerator_upper / (lo if numerator_upper >= 0 else hi)


def independent_ideal_upper_bounds(row, temperature, partitions):
    n, h = row['n'], row['gaps'][0]
    q, r = divmod(n, h)
    entropy_lo, entropy_hi = independent.log_interval(F(factorial(n)))
    first_cost, _ = independent.first_cost_and_state_entropy(n, h, entropy_lo)
    state_entropy_hi = entropy_hi - (h - r) * independent.log_interval(F(factorial(q)))[0] - r * independent.log_interval(F(factorial(q + 1)))[0]
    full, suffix = partitions
    denominator = independent.log_interval(1 / F(temperature))
    return (upper_quotient(entropy_hi - full[0], denominator),
            first_cost + upper_quotient(state_entropy_hi - suffix[0], denominator))


def targeted_exact_means():
    result, counts = {}, Counter()
    for n, word in ((6, (4, 2, 1)), (7, (3, 1))):
        specs = independent.stage_specs(n, word)
        total = sum(independent.execute_checked(x, specs, counts) for x in permutations(range(n)))
        result[(n, word)] = F(total, factorial(n))
    assert result[(6, (4, 2, 1))] == F(407, 30)
    assert result[(7, (3, 1))] == F(508, 35)
    # Values already independently exhausted in the previous exact search;
    # these are reused test data, not new enumerations.
    result.update({(5, (4, 1)): F(463, 60),
                   (6, (4, 1)): F(319, 30),
                   (7, (5, 1)): F(2903, 210)})
    return result


def verify_small_producer(producer, max_n):
    tds = tuple(producer.legacy.TEMPERATURES)
    assert tuple(F(t) for t in tds) == independent.TEMPERATURES
    extra_tds = ('0.375', '0.625')
    coefficients = {td: producer.restriction_coefficients(td, max_a=8, cutoff=512)
                    for td in tds + extra_tds}
    clipped = {(td, cutoff): producer.restriction_coefficients(td, max_a=8, cutoff=cutoff)
               for td in ('0.15', '0.50', '0.80', '0.95') for cutoff in (0, 1, 3)}
    counters = Counter()
    true_means = targeted_exact_means()
    for n in range(2, max_n + 1):
        rows = [make_row(n, a, b) for a in range(2, 9) for b in range(a + 1, 12)]
        prepared = producer.prepared_from_source(n, rows)
        for row in rows:
            data = direct_weight_data(row)
            specs = data[0]
            counters['full_prefix_membership_checks'] += data[-1]
            weights = check_weights(row, producer, 512, data)
            counters['interval_weight_checks'] += 1
            per_t = {}
            for td, coefficient in coefficients.items():
                partitions = exact_log_partitions(specs, td)
                full_upper, suffix_upper = producer.restricted_log_partitions(weights, coefficient)
                assert partitions[0][1] <= F(full_upper, producer.SCALE), (row, td, 'full')
                assert partitions[1][1] <= F(suffix_upper, producer.SCALE), (row, td, 'suffix')
                counters['producer_log_partition_upper_checks'] += 2
                result = producer.evaluate_temperature(row, n, prepared, weights, coefficient)
                upper_full, upper_first = independent_ideal_upper_bounds(row, td, partitions)
                assert result['new_full'] <= upper_full
                assert result['new_first'] <= upper_first
                assert result['new'] >= result['old']
                counters['producer_bound_direction_checks'] += 3
                true_mean = true_means.get((n, tuple(row['gaps'])))
                if row['gaps'] == [1] and n <= 7:
                    true_mean = independent.first_cost_and_state_entropy(n, 1, F(0))[0]
                if true_mean is not None:
                    assert result['new'] <= true_mean
                    counters['producer_bound_true_mean_checks'] += 1
                per_t[td] = result
            old_row = producer.legacy.evaluate(row, n, prepared)
            combined = producer.evaluate_row(
                row, old_row, n, prepared,
                [coefficients[t] for t in tds],
                refinements=[coefficients[t] for t in extra_tds])
            base = old_row['certified_comparison_lower_bound']
            same = max(base, *(per_t[t]['new'] for t in tds))
            refined = max(same, *(per_t[t]['new'] for t in extra_tds))
            old_refined = max(base, *(per_t[t]['old'] for t in extra_tds))
            assert combined['previous_certified_comparison_lower_bound'] == base
            assert combined['semigroup_original_grid_lower_bound'] == same
            assert combined['temperature_refinement_without_semigroup_lower_bound'] == old_refined
            assert combined['certified_comparison_lower_bound'] == refined >= same >= base
            assert refined >= old_refined
            counters['producer_retained_max_and_grid_separation_checks'] += 1
            if n in (17, 40):
                for cutoff in (0, 1, 3):
                    truncated_weights = check_weights(row, producer, cutoff, data)
                    counters['interval_weight_checks'] += 1
                    for td in ('0.15', '0.50', '0.80', '0.95'):
                        raw_full, raw_suffix = producer.restricted_log_partitions(truncated_weights, clipped[(td, cutoff)])
                        partitions = exact_log_partitions(specs, td)
                        assert partitions[0][1] <= F(raw_full, producer.SCALE)
                        assert partitions[1][1] <= F(raw_suffix, producer.SCALE)
                        limited = producer.evaluate_temperature(row, n, prepared, truncated_weights, clipped[(td, cutoff)])
                        assert per_t[td]['new'] >= limited['new'] >= limited['old']
                        counters['omitted_negative_tail_direction_checks'] += 3
            counters['product_rows'] += 1
        if n in (2, 7, 17, 25, 40) or n == max_n:
            print(json.dumps({'producer_checked_through_n': n,
                              'product_rows': counters['product_rows']}, ensure_ascii=False), flush=True)
    return {'counts': dict(counters),
            'parameter_domain': f'2<=n<={max_n}, 2<=a<=8, a<b<=11',
            'old_temperature_points': len(tds), 'separately_checked_refinement_points': list(extra_tds),
            'tail_cutoffs_checked': [0, 1, 3, 512],
            'targeted_exact_mean_input_table_pairs_repeated': factorial(6) + factorial(7),
            'full_prefix_membership': 'equality checked for coprime bases; guaranteed subset checked for noncoprime bases',
            'scope': 'end-to-end producer comparisons against directly constructed full-prefix finite capacities and selected exact means'}


def verify_full_batch(old_path, new_path):
    def read(path):
        rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
        keyed = {(r['n'], r['a'], r['b']): r for r in rows}
        assert len(keyed) == len(rows)
        return keyed
    old, new = read(old_path), read(new_path)
    assert set(old) == set(new)
    improved = exclusions = 0
    for key, r in new.items():
        prior = old[key]
        assert r['gaps'] == prior['gaps']
        base = prior['certified_comparison_lower_bound']
        fixed = r['semigroup_original_grid_lower_bound']
        final = r['certified_comparison_lower_bound']
        assert r['previous_certified_comparison_lower_bound'] == base
        assert final >= fixed >= base
        assert final >= r['temperature_refinement_without_semigroup_lower_bound'] >= base
        assert r['semigroup_original_grid_gain'] == fixed - base
        assert r['strictly_above_50_billion'] == (final > 50_000_000_000)
        improved += fixed > base
        exclusions += base <= 50_000_000_000 < fixed
    return {'rows': len(new), 'all_old_bounds_retained': True,
            'same_grid_integer_improvements': improved,
            'same_grid_new_exclusions_at_50_billion': exclusions,
            'scope': 'data identity, retained maximum, separated gain fields, and budget flags; no large-array sorting'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--producer', type=Path, default=ROOT / 'evaluate_semigroup_bounds.py')
    parser.add_argument('--max-n', type=int, default=40)
    parser.add_argument('--old-results', type=Path)
    parser.add_argument('--new-results', type=Path)
    parser.add_argument('--output', type=Path, default=ROOT / 'data/producer_verification_results.json')
    args = parser.parse_args()
    if not 7 <= args.max_n <= 40:
        parser.error('Focused producer domain requires 7<=max-n<=40')
    if bool(args.old_results) != bool(args.new_results):
        parser.error('Supply both --old-results and --new-results')
    producer = load_producer(args.producer)
    report = {'status': 'independent finite producer audit; not a Lean build',
              'log_one_plus_audit': audit_log_one_plus(producer),
              'producer_finite_audit': verify_small_producer(producer, args.max_n)}
    if args.new_results:
        report['full_batch_audit'] = verify_full_batch(args.old_results, args.new_results)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, ensure_ascii=False, indent=2), flush=True)


if __name__ == '__main__':
    main()
