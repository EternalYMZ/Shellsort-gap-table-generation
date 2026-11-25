#!/usr/bin/env python3
"""Certified prefix-semigroup comparison bounds for complete product tables.

The producer uses rational logarithm enclosures followed by integer arithmetic.
No input permutations of length n are generated.  All old certificates are
retained.  The original temperature grid and optional refinements are reported
separately.  For coprime bases the two-generator support is the exact support
implied by the entire prefix additive semigroup; for noncoprime bases it is a
safe subset of those known ordered distances.
"""
from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path
from math import gcd
import argparse
import hashlib
import importlib.util
import json
import time

ROOT = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location('legacy_bounds', ROOT / 'source/evaluate_gap_lower_bounds.py')
legacy = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(legacy)
from semigroup_prototype import intervals, aggregate_weights

SCALE = legacy.SCALE
HOLE_CUTOFF = 512


def read_jsonl(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def product_gaps(a, b, n):
    values = set()
    x = 1
    while x < n:
        y = x
        while y < n:
            values.add(y)
            y *= b
        x *= a
    return sorted(values, reverse=True)


def log_one_plus_upper(y):
    """An exact upper enclosure, with <2/SCALE error in the tiny branch."""
    assert y > -1
    if abs(y) <= F(1, 10**12):
        return legacy.ceil_q(y * SCALE)
    if abs(y) <= F(1, 4):
        # Work around 1 directly.  Scaling a number just BELOW 1 into
        # [1,2] unnecessarily creates large near-ln(2) rational series.
        v = y/(2+y)
        v2, power, total, j = v*v, v, F(0), 0
        while True:
            total += power/(2*j+1)
            power *= v2
            remainder = 2*abs(power)/((2*j+3)*(1-v2))
            if remainder*SCALE < 1:
                break
            j += 1
        upper = 2*total + (remainder if v >= 0 else 0)
        return legacy.ceil_q(upper*SCALE)
    return legacy.log_bounds(1 + y)[1]


def fast_temperature_data(td):
    """The same certified finite-tail formula with direct log1p arithmetic."""
    t = F(td)
    gamma = 1-2*t
    K = 512 if t >= F('0.95') else (256 if t >= F('0.90') else 128)
    lt, lc = legacy.log_bounds(t), legacy.log_bounds(1-t)
    corrections, prefix, power = [0], [0], F(1)
    for j in range(1, K+1):
        upper = log_one_plus_upper(gamma*power)
        corrections.append(upper)
        prefix.append(prefix[-1]+upper)
        power *= t
    return {'t':td, 'cutoff':K, 'L_lower':-lt[1], 'L_upper':-lt[0],
            'alpha_upper':lt[1]-lc[0], 'correction_upper':corrections,
            'prefix_correction_upper':prefix,
            'tail_sum_upper':legacy.ceil_q(max(F(0),gamma)*power/(1-t)*SCALE),
            'tail_last_upper':legacy.ceil_q(max(F(0),gamma)*power*SCALE)}


_ORIGINAL_COEFFICIENTS = {c['t']:c for c in json.loads(
    (ROOT/'source/gibbs_coefficient_certificate.json').read_text())['temperature_coefficients']}


def restriction_coefficients(td, max_a=183, cutoff=HOLE_CUTOFF):
    t = F(td)
    assert 0 < t < 1
    old = _ORIGINAL_COEFFICIENTS.get(td)
    if old is None:
        old = fast_temperature_data(td)
    corrections = [0]
    power = F(1)
    gamma = 1 - 2*t
    for j in range(1, max_a):
        corrections.append(log_one_plus_upper(gamma*power))
        power *= t
    # Index w is the number of positive integers absent from <a,b> through j.
    log_caps = []
    power = t
    for w in range(cutoff + 1):
        if power*SCALE < 1:
            log_caps.extend([0]*(cutoff+1-len(log_caps)))
            break
        log_caps.append(min(0, log_one_plus_upper(-power)))
        power *= t
    return {'t': td, 'old': old, 'unrestricted_correction_upper': corrections,
            'restricted_correction_upper_by_holes': log_caps,
            'hole_cutoff': cutoff, 'scale': str(SCALE)}


def prepared_from_source(n, rows):
    max_m = max(n // r['gaps'][0] for r in rows)
    if n != 10**9:
        return legacy.prepare(n, max_m)
    source = json.loads((ROOT / 'source/gibbs_coefficient_certificate.json').read_text())
    assert source['n'] == n and int(source['scale']) == SCALE
    logs = [(0, 0)] + [legacy.log_bounds(F(i)) for i in range(1, max_m+2)]
    lfub, harmonics = [0], [F(0)]
    for i in range(1, max_m+2):
        lfub.append(lfub[-1] + logs[i][1])
        harmonics.append(harmonics[-1] + F(1, i))
    return (int(source['entropy_log_factorial_lower_scaled']), lfub, harmonics,
            logs, source['temperature_coefficients'])


def make_weights(row, n, cutoff=HOLE_CUTOFF):
    a, b, gaps = row['a'], row['b'], row['gaps']
    assert 2 <= a < b
    assert gaps == product_gaps(a, b, n), 'The prefix equality requires a complete product table.'
    agg = aggregate_weights(gaps, n)
    early = [(j, agg.full(j, j), agg.suffix(j, j)) for j in range(1, a)]
    caps = []
    for lower, upper, holes in intervals(a, b, cutoff):
        full, suffix = agg.full(lower, upper), agg.suffix(lower, upper)
        if full:
            caps.append((holes, full, suffix))
    return {'scan': sum(n-h for h in gaps), 'suffix_scan': sum(n-h for h in gaps[1:]),
            'early': early, 'caps': caps, 'cutoff': cutoff}


def restricted_log_partitions(weights, coeff):
    old = coeff['old']
    full = weights['scan'] * old['alpha_upper']
    suffix = weights['suffix_scan'] * old['alpha_upper']
    early = coeff['unrestricted_correction_upper']
    caps = coeff['restricted_correction_upper_by_holes']
    for j, w, v in weights['early']:
        full += w * early[j]
        suffix += v * early[j]
    for holes, w, v in weights['caps']:
        upper = caps[holes]
        if upper:
            full += w * upper
            suffix += v * upper
    # For omitted intervals holes>cutoff, the correction log(1-t^(holes+1))
    # is negative.  Replacing it by zero is an upper, never a lower, bound.
    return full, suffix


def first_statistics(row, n, prepared):
    entropy, lfub, harmonics, logs, _ = prepared
    h = row['gaps'][0]
    m, r = divmod(n, h)
    cost = h*(F(m*(m-1), 4) + m-harmonics[m]) + r*(F(m, 2)+1-F(1, m+1))
    loss_upper = h*lfub[m] + r*logs[m+1][1]
    return legacy.floor_q(cost), entropy-loss_upper


def evaluate_temperature(row, n, prepared, weights, coeff):
    entropy = prepared[0]
    first_floor, state_entropy = first_statistics(row, n, prepared)
    old = coeff['old']
    old_first = legacy.log_partition_upper(n, row['gaps'][0], old)
    old_suffix = sum(legacy.log_partition_upper(n, h, old) for h in row['gaps'][1:])
    new_full, new_suffix = restricted_log_partitions(weights, coeff)
    # Both alternatives are independently valid upper bounds.  This minimum
    # also protects against a deliberately conservative finite hole cutoff.
    new_full = min(new_full, old_first+old_suffix)
    new_suffix = min(new_suffix, old_suffix)
    old_full_bound = legacy.divide_lower(entropy-old_first-old_suffix, old)
    old_first_bound = first_floor + legacy.divide_lower(state_entropy-old_suffix, old)
    full_bound = legacy.divide_lower(entropy-new_full, old)
    first_bound = first_floor + legacy.divide_lower(state_entropy-new_suffix, old)
    assert full_bound >= old_full_bound and first_bound >= old_first_bound
    return {'old': max(old_full_bound, old_first_bound), 'new': max(full_bound, first_bound),
            'new_full': full_bound, 'new_first': first_bound, 't': coeff['t']}


def evaluate_row(row, old_row, n, prepared, coefficients, cutoff=HOLE_CUTOFF, refinements=()):
    assert row['gaps'] == old_row['gaps']
    weights = make_weights(row, n, cutoff)
    base = old_row['certified_comparison_lower_bound']
    best_old, best_new, best = base, base, base
    old_t = new_t = best_t = None
    best_kind = 'retained_old_certificate'
    same_grid_values = []
    for coeff in coefficients:
        ev = evaluate_temperature(row, n, prepared, weights, coeff)
        same_grid_values.append(ev)
        if ev['old'] > best_old:
            best_old, old_t = ev['old'], ev['t']
        if ev['new'] > best_new:
            best_new, new_t = ev['new'], ev['t']
    assert best_old == base, 'The original 20-temperature calculation must reproduce the old maximum.'
    best, best_t = best_new, new_t
    if best > base:
        best_kind = 'semigroup_original_grid'
    refined_old = base
    for coeff in refinements:
        ev = evaluate_temperature(row, n, prepared, weights, coeff)
        refined_old = max(refined_old, ev['old'])
        if ev['new'] > best:
            best, best_t, best_kind = ev['new'], ev['t'], 'semigroup_refined_temperature'
    out = dict(old_row)
    out.update({'previous_certified_comparison_lower_bound': base,
                'semigroup_original_grid_lower_bound': best_new,
                'semigroup_original_grid_best_t': new_t,
                'semigroup_original_grid_gain': best_new-base,
                'temperature_refinement_without_semigroup_lower_bound': refined_old,
                'certified_comparison_lower_bound': best,
                'certified_per_key': best/n,
                'new_best_t': best_t, 'new_best_certificate_kind': best_kind,
                'strictly_above_50_billion': best > 50_000_000_000,
                'strictly_above_53_billion': best > 53_000_000_000,
                'at_least_200_billion': best >= 200_000_000_000,
                'semigroup_support_exact_for_full_prefix': gcd(row['a'], row['b']) == 1,
                'hole_cutoff': cutoff})
    return out


def summarize(rows, elapsed, n=10**9):
    def group(xs):
        before = sum(r['previous_certified_comparison_lower_bound'] > 50_000_000_000 for r in xs)
        fixed = sum(r['semigroup_original_grid_lower_bound'] > 50_000_000_000 for r in xs)
        after = sum(r['certified_comparison_lower_bound'] > 50_000_000_000 for r in xs)
        gains = [r['semigroup_original_grid_gain'] for r in xs]
        return {'tables': len(xs), 'old_excluded_above_50_billion': before,
                'semigroup_same_grid_excluded_above_50_billion': fixed,
                'final_excluded_above_50_billion': after,
                'new_exclusions_by_support_same_grid': fixed-before,
                'new_exclusions_after_refinement': after-fixed,
                'improved_integer_bounds_by_support_same_grid': sum(x > 0 for x in gains),
                'maximum_same_grid_integer_gain': max(gains, default=0),
                'remaining_not_excluded': len(xs)-after}
    selected = {(11,12), (29,33), (8,179), (182,183)}
    keys = ('a','b','passes','previous_certified_comparison_lower_bound',
            'semigroup_original_grid_lower_bound','semigroup_original_grid_gain',
            'temperature_refinement_without_semigroup_lower_bound',
            'certified_comparison_lower_bound','new_best_t')
    short = lambda r: {k:r[k] for k in keys}
    return {'n': n, 'total': group(rows),
            'coprime': group([r for r in rows if r['coprime']]),
            'noncoprime': group([r for r in rows if not r['coprime']]),
            'specified_examples': [short(r) for r in rows if (r['a'],r['b']) in selected],
            'largest_same_grid_gains': [short(r) for r in sorted(rows,key=lambda r:r['semigroup_original_grid_gain'],reverse=True)[:20]],
            'newly_excluded_tables': [short(r) for r in rows if r['previous_certified_comparison_lower_bound'] <= 50_000_000_000 < r['certified_comparison_lower_bound']],
            'original_temperature_grid': legacy.TEMPERATURES,
            'scale': str(SCALE), 'hole_cutoff': HOLE_CUTOFF,
            'arithmetic': 'Exact rational log enclosures; integer interval weights and outward rounding. Floating point is not used to certify bounds.',
            'interpretation': 'Lower bounds only. Remaining tables are not certified fast tables. Same-grid support and refined-temperature improvements are separate.',
            'elapsed_seconds': elapsed}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=ROOT/'source/gap_tables.jsonl')
    parser.add_argument('--old-results', type=Path, default=ROOT/'source/gap_lower_bounds.jsonl')
    parser.add_argument('--output', type=Path, default=ROOT/'data/semigroup_gap_lower_bounds.jsonl')
    parser.add_argument('--summary', type=Path, default=ROOT/'data/semigroup_summary.json')
    parser.add_argument('--coefficients', type=Path, default=ROOT/'data/semigroup_coefficients.json')
    parser.add_argument('--n', type=int, default=10**9)
    parser.add_argument('--limit', type=int)
    args = parser.parse_args()
    start = time.monotonic()
    rows = read_jsonl(args.input)
    if args.limit:
        rows = rows[:args.limit]
    old = {(r['a'],r['b']):r for r in read_jsonl(args.old_results)}
    prepared = prepared_from_source(args.n, rows)
    coefficients = [restriction_coefficients(t) for t in legacy.TEMPERATURES]
    args.coefficients.parent.mkdir(parents=True, exist_ok=True)
    args.coefficients.write_text(json.dumps({'scale':str(SCALE),'coefficients':coefficients},indent=2)+'\n')
    print(f'Prepared {len(coefficients)} rational temperature certificates.',flush=True)
    results = []
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('w') as f:
        for i,row in enumerate(rows,1):
            out = evaluate_row(row,old[(row['a'],row['b'])],args.n,prepared,coefficients)
            results.append(out)
            f.write(json.dumps(out,ensure_ascii=False)+'\n')
            if i%2000 == 0:
                print(f'Certified {i} product tables.',flush=True)
    summary = summarize(results,time.monotonic()-start,args.n)
    args.summary.write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in ('total','coprime','specified_examples','elapsed_seconds')},ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
