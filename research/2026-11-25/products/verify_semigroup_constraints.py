#!/usr/bin/env python3
"""Independent finite verification of prefix-semigroup insertion supports.

This checker implements its own ordinary insertion runner and bounded
additive-semigroup reachability.  For a fixed prefix, every positive distance
in its additive semigroup is ordered: each original gap order is preserved
by later complete gap passes, and positive-distance paths give transitivity.
At depth j of a current g-chain, q_j previous keys at distances in that
semigroup are therefore smaller than the inserted key.  There are at most
j-q_j greater predecessors.  If q_j>0 the insertion cannot reach the head.

The exact local capacity is consequently
  sum(k=0..j) t**(1+min(k,j-1))                 if q_j=0;
  sum(k=0..j-q_j) t**(k+1)                     if q_j>0.
The checker compares these capacities at identical rational temperatures,
verifies the resulting full-record and exact-first-pass entropy lower bounds
against exhaustive uniform means, and verifies that taking maxima over an
enlarged temperature grid cannot weaken the bound.  It does not equate a
lower-bound ranking with a performance ranking.

Optional JSONL comparison checks retained old certificates and, for small
instances already enumerated, true means.  For large instances that comparison
checks preservation only; it is not a proof of the new producer's arithmetic.
No existing dataset or implementation is modified.
"""

from __future__ import annotations

from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from itertools import permutations
from math import factorial
from pathlib import Path
import argparse
import json


TEMPERATURES = tuple(F(x) for x in (
    '0.02', '0.05', '0.10', '0.15', '0.20', '0.25', '0.30',
    '0.35', '0.40', '0.45', '0.50', '0.55', '0.60', '0.65',
    '0.70', '0.75', '0.80', '0.85', '0.90', '0.95'))
REFINED_TEMPERATURES = tuple(sorted(set(TEMPERATURES) | {F(3, 8), F(5, 8)}))
LOG_SCALE = 10 ** 50


def floor_fraction(x):
    return x.numerator // x.denominator


def ceil_fraction(x):
    return -((-x.numerator) // x.denominator)


def _unit_log_interval(x):
    """A 64-term rational atanh enclosure; no binary floating point."""
    assert 1 <= x <= 2
    z = (x - 1) / (x + 1)
    power = z
    partial = F(0)
    for j in range(64):
        partial += 2 * power / (2 * j + 1)
        power *= z * z
    remainder = 2 * power / (129 * (1 - z * z))
    return partial, partial + remainder


LN2 = _unit_log_interval(F(2))


@lru_cache(None)
def log_interval(value):
    """Independent outward rational log enclosure rounded to 50 decimals."""
    x = F(value)
    if x <= 0:
        raise ValueError('Logarithm requires a positive argument')
    k = 0
    while x < 1:
        x *= 2
        k -= 1
    while x >= 2:
        x /= 2
        k += 1
    lo, hi = _unit_log_interval(x)
    if k >= 0:
        lo, hi = lo + k * LN2[0], hi + k * LN2[1]
    else:
        lo, hi = lo + k * LN2[1], hi + k * LN2[0]
    return F(floor_fraction(lo * LOG_SCALE), LOG_SCALE), F(ceil_fraction(hi * LOG_SCALE), LOG_SCALE)


def lower_quotient(numerator_lower, denominator_interval):
    lo, hi = denominator_interval
    assert 0 < lo <= hi
    return numerator_lower / (hi if numerator_lower >= 0 else lo)


def semigroup_reachability(prefix, limit):
    reached = [False] * (limit + 1)
    reached[0] = True
    for distance in range(1, limit + 1):
        reached[distance] = any(h <= distance and reached[distance - h] for h in prefix)
    return tuple(reached)


def legal_words(n):
    for mask in range(1 << (n - 2)):
        yield tuple(h for h in range(n - 1, 1, -1) if mask & (1 << (h - 2))) + (1,)


@lru_cache(None)
def stage_specs(n, word):
    specs = []
    prefix = ()
    for g in word:
        reachable = semigroup_reachability(prefix, n - 1)
        counts = []
        q = 0
        for depth in range(1, (n - 1) // g + 1):
            q += reachable[depth * g]
            counts.append((depth, min(g, n - depth * g), q))
        specs.append((g, reachable, tuple(counts)))
        prefix += (g,)
    return tuple(specs)


def execute_checked(x, specs, counts):
    a = list(x)
    total = 0
    for g, reachable, depth_rows in specs:
        before = tuple(a)
        for distance in range(1, len(a)):
            if reachable[distance]:
                assert all(before[i] < before[i + distance] for i in range(len(a) - distance))
                counts['known_ordered_distance_checks'] += 1
        q_by_depth = {j: q for j, _, q in depth_rows}
        for i in range(g, len(a)):
            depth = i // g
            guaranteed_smaller = q_by_depth[depth]
            key = a[i]
            position = i
            moves = comparisons = 0
            while position >= g:
                comparisons += 1
                if a[position - g] < key:
                    break
                a[position] = a[position - g]
                position -= g
                moves += 1
            a[position] = key
            record = position < g
            assert moves <= depth - guaranteed_smaller
            assert comparisons == 1 + min(moves, depth - 1)
            if guaranteed_smaller:
                assert not record
                assert comparisons == moves + 1
                counts['positive_support_nonrecord_checks'] += 1
            counts['actual_insertion_support_checks'] += 1
            total += comparisons
        counts['actual_gap_passes'] += 1
    assert tuple(a) == tuple(range(len(a)))
    return total


@lru_cache(None)
def local_capacity(depth, guaranteed_smaller, temperature):
    t = F(temperature)
    assert 0 < t < 1 and 0 <= guaranteed_smaller <= depth
    if guaranteed_smaller:
        return sum((t ** (moves + 1) for moves in range(depth - guaranteed_smaller + 1)), F(0))
    return sum((t ** (1 + min(moves, depth - 1)) for moves in range(depth + 1)), F(0))


def first_cost_and_state_entropy(n, h, input_entropy_lower):
    q, r = divmod(n, h)
    def chain_cost(length):
        return F(length * (length - 1), 4) + length - sum((F(1, j) for j in range(1, length + 1)), F(0))
    cost = (h - r) * chain_cost(q) + r * chain_cost(q + 1)
    entropy = input_entropy_lower - (h - r) * log_interval(F(factorial(q)))[1] - r * log_interval(F(factorial(q + 1)))[1]
    return cost, entropy


def table_bounds(n, word, exact_mean, counts):
    entropy = log_interval(F(factorial(n)))[0]
    first_cost, state_entropy = first_cost_and_state_entropy(n, word[0], entropy)
    specs = stage_specs(n, word)
    old_by_t, new_by_t = {}, {}
    for t in REFINED_TEMPERATURES:
        old_logs, new_logs = [], []
        for _, _, rows in specs:
            old_sum = new_sum = F(0)
            for depth, multiplicity, q in rows:
                old_z = local_capacity(depth, 0, t)
                new_z = local_capacity(depth, q, t)
                assert new_z <= old_z
                old_log = log_interval(old_z)[1]
                new_log = log_interval(new_z)[1]
                assert new_log <= old_log
                old_sum += multiplicity * old_log
                new_sum += multiplicity * new_log
                counts['local_capacity_direction_checks'] += 1
                counts['strict_local_capacity_reductions'] += new_z < old_z
            old_logs.append(old_sum)
            new_logs.append(new_sum)
        denominator = log_interval(1 / t)
        old_full = lower_quotient(entropy - sum(old_logs), denominator)
        new_full = lower_quotient(entropy - sum(new_logs), denominator)
        old_first = first_cost + lower_quotient(state_entropy - sum(old_logs[1:]), denominator)
        new_first = first_cost + lower_quotient(state_entropy - sum(new_logs[1:]), denominator)
        assert old_full <= new_full <= exact_mean, (n, word, t, new_full, exact_mean)
        assert old_first <= new_first <= exact_mean, (n, word, t, new_first, exact_mean)
        counts['same_temperature_bound_and_true_mean_checks'] += 2
        old_by_t[t] = max(old_full, old_first)
        new_by_t[t] = max(new_full, new_first)
    scan = sum(n - h for h in word)
    old_grid = max(F(scan), *(old_by_t[t] for t in TEMPERATURES))
    new_grid = max(F(scan), *(new_by_t[t] for t in TEMPERATURES))
    refined = max(F(scan), *new_by_t.values())
    assert old_grid <= new_grid <= refined <= exact_mean
    counts['temperature_grid_maximum_checks'] += 1
    old_floor, new_floor, refined_floor = map(floor_fraction, (old_grid, new_grid, refined))
    counts['tables_with_stronger_unrounded_same_grid_bound'] += new_grid > old_grid
    counts['tables_with_stronger_integer_same_grid_bound'] += new_floor > old_floor
    return {'n': n, 'gaps': word, 'true_uniform_mean': str(exact_mean),
            'old_same_grid_floor': old_floor, 'semigroup_same_grid_floor': new_floor,
            'semigroup_refined_grid_floor': refined_floor}


def finite_verification(max_n=7):
    counts = Counter()
    summaries = []
    exact_means = {}
    examples = []
    for n in range(2, max_n + 1):
        inputs = list(permutations(range(n)))
        counts['distinct_input_permutations_by_size'] += len(inputs)
        start_counts = counts.copy()
        for word in legal_words(n):
            specs = stage_specs(n, word)
            total = 0
            for x in inputs:
                total += execute_checked(x, specs, counts)
                counts['permutation_table_pairs'] += 1
            mean = F(total, factorial(n))
            exact_means[(n, word)] = mean
            row = table_bounds(n, word, mean, counts)
            counts['complete_tables'] += 1
            if row['semigroup_same_grid_floor'] > row['old_same_grid_floor'] and len(examples) < 12:
                examples.append(row)
        summaries.append({'n': n, 'tables': 1 << (n - 2), 'inputs': factorial(n),
                          'support_checks': counts['actual_insertion_support_checks'] - start_counts['actual_insertion_support_checks'],
                          'nonrecord_checks': counts['positive_support_nonrecord_checks'] - start_counts['positive_support_nonrecord_checks']})
        print(json.dumps({'verified_n': n, 'tables': 1 << (n - 2),
                          'permutations': factorial(n)}, ensure_ascii=False), flush=True)
    return {'counts': dict(counts), 'per_size': summaries, 'integer_improvement_examples': examples}, exact_means


def import_module(path):
    spec = spec_from_file_location('legacy_gap_bounds_for_audit', path)
    if spec is None or spec.loader is None:
        raise ValueError(f'Cannot load module: {path}')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def audit_legacy_numeric_helpers(path):
    """Check selected legacy enclosures against independent rational bounds."""
    legacy = import_module(path)
    assert tuple(F(t) for t in legacy.TEMPERATURES) == TEMPERATURES
    inputs = set(TEMPERATURES) | {1 - t for t in TEMPERATURES}
    inputs |= {F(1), F(2), F(1, 2), F(1, 10 ** 12), F(10 ** 9), F(2 * 10 ** 9 + 1, 2)}
    for x in inputs:
        legacy_lo, legacy_hi = legacy.log_bounds(x)
        own_lo, own_hi = log_interval(x)
        assert F(legacy_lo, legacy.SCALE) <= own_lo <= own_hi <= F(legacy_hi, legacy.SCALE)
    divisions = 0
    for t in TEMPERATURES:
        lo, hi = legacy.log_bounds(1 / t)
        c = {'L_lower': lo, 'L_upper': hi}
        for numerator in (-10 ** 30, -1, 0, 1, 10 ** 30):
            result = legacy.divide_lower(numerator, c)
            assert result <= F(numerator, lo) and result <= F(numerator, hi)
            assert result == floor_fraction(F(numerator, hi if numerator >= 0 else lo))
            divisions += 1
    return {'selected_log_enclosures': len(inputs), 'signed_division_checks': divisions,
            'temperature_grid_exact_match': True,
            'scope': 'selected numerical primitives; not a rerun of the billion-key batch'}


def compare_result_rows(old_path, new_path, new_bound_field, exact_means, allow_subset=False):
    def read(path):
        result = {}
        for line in Path(path).read_text(encoding='utf-8').splitlines():
            if not line.strip():
                continue
            row = json.loads(line)
            key = (row['n'], row.get('a'), row.get('b'), tuple(row['gaps']))
            assert key not in result, ('duplicate key', key)
            result[key] = row
        return result
    old, new = read(old_path), read(new_path)
    assert set(new) <= set(old)
    if not allow_subset:
        assert set(new) == set(old)
    improved = small_mean_checks = newly_excluded = 0
    for key, row in new.items():
        old_bound = old[key]['certified_comparison_lower_bound']
        new_bound = row[new_bound_field]
        assert type(old_bound) is int and type(new_bound) is int
        assert new_bound >= old_bound, (key, old_bound, new_bound)
        improved += new_bound > old_bound
        newly_excluded += old_bound <= 50_000_000_000 < new_bound
        finite_key = (key[0], key[3])
        if finite_key in exact_means:
            assert new_bound <= exact_means[finite_key]
            small_mean_checks += 1
    return {'old_rows': len(old), 'new_rows': len(new), 'old_bound_preserved': True,
            'strict_improvements': improved, 'new_exclusions_at_50_billion': newly_excluded,
            'true_mean_checks_for_enumerated_sizes': small_mean_checks,
            'scope': 'large-instance checks establish retained old bounds only, not the validity of each new bound'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n', type=int, default=7)
    parser.add_argument('--legacy-module', type=Path)
    parser.add_argument('--old-results', type=Path)
    parser.add_argument('--new-results', type=Path)
    parser.add_argument('--new-bound-field', default='certified_comparison_lower_bound')
    parser.add_argument('--allow-subset', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not 2 <= args.max_n <= 7:
        parser.error('This focused verifier supports 2 <= max-n <= 7')
    if bool(args.old_results) != bool(args.new_results):
        parser.error('--old-results and --new-results must be supplied together')
    finite, exact_means = finite_verification(args.max_n)
    report = {'status': 'finite exhaustive checks of the stated semigroup support; no Lean build',
              'fixed_temperature_grid': [str(t) for t in TEMPERATURES],
              'refinement_check_only': ['3/8', '5/8'],
              'finite_checks': finite}
    if args.legacy_module:
        report['legacy_numeric_audit'] = audit_legacy_numeric_helpers(args.legacy_module)
    if args.new_results:
        report['result_comparison'] = compare_result_rows(args.old_results, args.new_results,
                                                        args.new_bound_field, exact_means, args.allow_subset)
    rendered = json.dumps(report, ensure_ascii=False, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, flush=True)


if __name__ == '__main__':
    main()
