#!/usr/bin/env python3
"""Exact P09 gap-table search with an integer residual-information bound.

The suffix is a fixed ordinary comparison-based Shellsort program. It receives
the current array, n, and its fixed gap list; it does not inspect the prefix's
comparison transcript or other input-dependent historical metadata. Distinct
current rank permutations must reach distinct leaves of its comparison tree:
at one leaf the induced permutation of the current entries is fixed, and it
cannot map two different rank permutations to the same sorted array. Hence
the leaf depths form a binary prefix code on the distinct current states.

If state x occurs with integer multiplicity m_x, the total suffix comparison
cost is at least the minimum weighted path length of a binary prefix code
with these weights. Huffman's merging algorithm computes that lower bound
using integers only. The combined bound is the MAXIMUM of this quantity and
the existing sum_x m_x L(x,u), never their sum. All pruning uses strict >,
so every tied optimal gap table is retained.

Place the already delivered p09_certificates.py next to this file for a
self-contained package. In the research workspace only, the default loader
also recognizes its unchanged sibling-round location.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from heapq import heapify, heappop, heappush
from importlib.util import module_from_spec, spec_from_file_location
from itertools import permutations
from math import factorial
from pathlib import Path
import hashlib
import json
import time


def load_baseline(path):
    spec = spec_from_file_location('p09_certificates_baseline', path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'Cannot load baseline: {path}')
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def huffman_cost(weights):
    """Minimum weighted binary-code length, including the singleton case."""
    heap = list(weights)
    if not heap or any(not isinstance(weight, int) or weight <= 0 for weight in heap):
        raise ValueError('A nonempty sequence of positive integer masses is required')
    heapify(heap)
    total = 0
    while len(heap) > 1:
        merged = heappop(heap) + heappop(heap)
        total += merged
        heappush(heap, merged)
    return total


def exact_information_search(n, baseline):
    """All n! inputs and all tied optima, with safe integer pruning."""
    if n < 2:
        raise ValueError('n must be at least 2')
    start = time.perf_counter()
    mass = factorial(n)
    root = Counter({x: 1 for x in permutations(range(n))})
    dp = baseline.build_joint_dp(n)
    best_total, winners = None, []
    stats = Counter()
    diagnostics = []

    @lru_cache(maxsize=400000)
    def transition(x, h):
        return baseline.gap_pass(x, h)

    @lru_cache(maxsize=400000)
    def lower_state(x, u):
        return baseline.suffix_floor(x, u, dp)

    def propagate(dist, h):
        out = Counter()
        total = 0
        for x, weight in dist.items():
            y, c, _, _ = transition(x, h)
            out[y] += weight
            total += weight * c
            stats['weighted_state_evaluations'] += 1
        assert sum(out.values()) == mass
        return out, total

    def visit(dist, u, prefix, prefix_total):
        nonlocal best_total, winners
        stats['visited_prefixes'] += 1
        information = None
        if best_total is not None:
            joint = sum(weight * lower_state(x, u) for x, weight in dist.items())
            information = huffman_cost(dist.values())
            stats['information_bound_calls'] += 1
            stats['information_weights_processed'] += len(dist)
            stats['huffman_merges'] += len(dist) - 1
            stats['information_stronger_than_joint'] += information > joint
            remaining = max(joint, information)
            if prefix_total + remaining > best_total:
                stats['pruned_prefixes'] += 1
                stats['pruned_complete_tables'] += 2 ** (u - 1)
                if prefix_total + joint <= best_total:
                    stats['prunes_requiring_information'] += 1
                    stats['complete_tables_pruned_by_information_only'] += 2 ** (u - 1)
                    diagnostics.append({
                        'prefix': prefix,
                        'remaining_max_gap': u,
                        'state_count': len(dist),
                        'prefix_cost_sum': prefix_total,
                        'joint_suffix_floor_sum': joint,
                        'information_suffix_floor_sum': information,
                        'incumbent_total': best_total,
                    })
                return
        _, tail_total = propagate(dist, 1)
        if information is not None:
            assert information <= tail_total
        total = prefix_total + tail_total
        word = prefix + (1,)
        stats['scored_complete_tables'] += 1
        if best_total is None or total < best_total:
            best_total, winners = total, [word]
        elif total == best_total:
            winners.append(word)
        for h in range(2, u + 1):
            child, step_total = propagate(dist, h)
            visit(child, h - 1, prefix + (h,), prefix_total + step_total)

    visit(root, n - 1, (), 0)
    assert stats['scored_complete_tables'] + stats['pruned_complete_tables'] == 2 ** (n - 2)
    result = {
        'n': n,
        'mode': 'joint_information',
        'input_count': mass,
        'legal_table_count': 2 ** (n - 2),
        'optimum_total_comparisons': best_total,
        'optimum_mean': str(Fraction(best_total, mass)),
        'optimum_mean_decimal': best_total / mass,
        'all_winners': sorted(winners),
        'statistics': dict(stats),
        'information_only_prunes': diagnostics,
        'seconds': time.perf_counter() - start,
    }
    transition.cache_clear()
    lower_state.cache_clear()
    return result


def default_baseline():
    here = Path(__file__).resolve().parent
    choices = [here / 'p09_certificates.py',
               here.parent / 'p09_round_20261125' / 'p09_certificates.py']
    for candidate in choices:
        if candidate.is_file():
            return candidate
    return choices[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--min-n', type=int, default=2)
    parser.add_argument('--max-n', type=int, default=8)
    parser.add_argument('--baseline', type=Path, default=default_baseline())
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).resolve().with_name('information_search_results.json'))
    args = parser.parse_args()
    if not (2 <= args.min_n <= args.max_n <= 9):
        parser.error('supported exact sizes: 2 <= min-n <= max-n <= 9')
    if not args.baseline.is_file():
        parser.error('Place p09_certificates.py next to this file or pass --baseline')
    baseline = load_baseline(args.baseline)
    results = {
        'model': 'uniform distinct-rank permutations; fixed strictly decreasing gaps ending at 1; ordinary key comparisons',
        'suffix_assumption': 'No reading of prefix comparison transcripts or other input-dependent historical metadata',
        'bound': 'max(sum_x m_x L(x,u), HuffmanCost(m_x))',
        'pruning_rule': 'strictly greater than incumbent integer total; all tied optima retained',
        'baseline_sha256': hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
        'timing_status': 'single sequential runs; implementation diagnostics, not a speed benchmark',
        'status': 'exact finite experiments; no Lean compilation',
        'requested_range': [args.min_n, args.max_n],
        'searches': [],
    }
    for n in range(args.min_n, args.max_n + 1):
        rows = [baseline.exact_search(n, mode) for mode in ('none', 'joint')]
        rows.append(exact_information_search(n, baseline))
        assert len({row['optimum_total_comparisons'] for row in rows}) == 1
        assert all(row['all_winners'] == rows[0]['all_winners'] for row in rows)
        results['searches'].extend(rows)
        results['verified_through_n'] = n
        results['complete'] = n == args.max_n
        args.output.write_text(json.dumps(results, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
        print(json.dumps({
            'n': n, 'mean': rows[0]['optimum_mean'], 'winners': rows[0]['all_winners'],
            'scored_tables': {row['mode']: row['statistics']['scored_complete_tables'] for row in rows},
            'state_evaluations': {row['mode']: row['statistics']['weighted_state_evaluations'] for row in rows},
            'information_only_prunes': rows[-1]['statistics'].get('prunes_requiring_information', 0),
            'seconds': {row['mode']: row['seconds'] for row in rows},
        }, ensure_ascii=False), flush=True)
    print(str(args.output.resolve()), flush=True)


if __name__ == '__main__':
    main()
