#!/usr/bin/env python3
"""Exact finite checks for Project S P09, 2026-11-25.

All ranking, costs, lower bounds, and branch decisions use integers.
The joint suffix relaxation is a lower bound, not an exact state model.
No claim of a polynomial-time optimal gap-table generator is made.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from math import factorial, isqrt
from pathlib import Path
import json
import time


def inversion_count(x):
    return sum(x[i] > x[j] for i in range(len(x)) for j in range(i + 1, len(x)))


def diagonal_min(x):
    return min(i + rank for i, rank in enumerate(x))


def gap_pass(x, h):
    """Ordinary, unsentinelled linear insertion; key comparisons only."""
    a = list(x)
    comparisons = moves = records = 0
    for i in range(h, len(a)):
        value, j = a[i], i
        while j >= h:
            comparisons += 1
            if a[j - h] < value:
                break
            a[j] = a[j - h]
            j -= h
            moves += 1
        a[j] = value
        records += j < h
    assert comparisons == moves + len(x) - h - records
    return tuple(a), comparisons, moves, records


def run_word(x, word):
    comparisons = moves = 0
    for h in word:
        x, c, m, _ = gap_pass(x, h)
        comparisons += c
        moves += m
    return x, comparisons, moves


def move_capacity(n, h):
    q, s = divmod(n, h)
    return h * q * (q - 1) // 2 + s * q


def record_budget(h, records):
    a, b = divmod(records, h)
    return h * a * (a + 1) // 2 + (a + 1) * b


def record_cap(n, h, moves):
    lo, hi = 0, n - h
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if record_budget(h, mid) <= moves:
            lo = mid
        else:
            hi = mid - 1
    return lo


def pass_floor(n, h, moves):
    return moves + n - h - record_cap(n, h, moves)


def build_joint_dp(n):
    """D[u][b][I]: certified cost for any legal suffix with max gap <=u.

    b is an upper bound on min_i(i+rank_i); this is sufficient, not exact.
    """
    imax = n * (n - 1) // 2
    dp = [None] * n
    dp[1] = [
        [i + n - 1 - min(b, (isqrt(1 + 8 * i) - 1) // 2)
         for i in range(imax + 1)]
        for b in range(n)
    ]
    for u in range(2, n):
        cap = move_capacity(n, u)
        fees = [pass_floor(n, u, m) for m in range(cap + 1)]
        prev = dp[u - 1]
        rows = []
        for b in range(n):
            nextrow = prev[min(b, u - 1)]
            row = []
            for i in range(imax + 1):
                best = prev[b][i]
                for m in range(min(i, cap) + 1):
                    residual = max(0, i - (2 * u - 1) * m)
                    best = min(best, fees[m] + nextrow[residual])
                row.append(best)
            rows.append(row)
        dp[u] = rows
    for u in range(1, n):
        for b in range(n):
            assert all(a <= c for a, c in zip(dp[u][b], dp[u][b][1:]))
            if b:
                assert all(a >= c for a, c in zip(dp[u][b - 1], dp[u][b]))
    return dp


def movement_floor(x, u):
    i = inversion_count(x)
    inverse_floor = (i + 2 * u - 2) // (2 * u - 1)
    distance_sum = sum((abs(rank - j) + u - 1) // u for j, rank in enumerate(x))
    transport_floor = (distance_sum + 1) // 2
    return max(inverse_floor, transport_floor)


def suffix_floor(x, u, dp):
    i, b = inversion_count(x), diagonal_min(x)
    return max(dp[u][b][i], movement_floor(x, u) + len(x) - 1 - b)


def check_invariants(max_n=7):
    counts = Counter()
    equality = Counter()
    min_distribution = []
    for n in range(2, max_n + 1):
        dp = build_joint_dp(n)

        @lru_cache(None)
        def optimum_for_state(x, u):
            best = gap_pass(x, 1)[1]
            for h in range(2, u + 1):
                y, c, _, _ = gap_pass(x, h)
                best = min(best, c + optimum_for_state(y, h - 1))
            return best

        hist = Counter()
        terminal_envelope = {}
        for x in permutations(range(n)):
            counts['permutations'] += 1
            inv, b = inversion_count(x), diagonal_min(x)
            hist[b] += 1
            final = gap_pass(x, 1)
            terminal_envelope[inv] = min(terminal_envelope.get(inv, 10**20), final[1])
            assert final[3] <= b
            for h in range(1, n):
                y, c, m, r = gap_pass(x, h)
                delta = inv - inversion_count(y)
                assert m <= delta <= (2 * h - 1) * m
                assert record_budget(h, r) <= m
                assert c >= pass_floor(n, h, m) >= max(m, n - h)
                assert diagonal_min(y) <= min(b, h - 1)
                counts['gap_pass_checks'] += 1
                actual = optimum_for_state(x, h)
                lower = suffix_floor(x, h, dp)
                assert lower <= actual, (n, x, h, lower, actual)
                counts['suffix_optimum_checks'] += 1
                equality[n] += lower == actual
            for left in range(n):
                for right in range(left + 1, n):
                    if x[left] > x[right]:
                        y = list(x)
                        y[left], y[right] = y[right], y[left]
                        assert diagonal_min(y) <= b
                        counts['inversion_swap_checks'] += 1
        for t in range(1, n):
            count = sum(v for b, v in hist.items() if b >= t)
            predicted = (n - t) ** t * factorial(n - t)
            assert count == predicted
            counts['diagonal_tail_checks'] += 1
        for inv, actual in terminal_envelope.items():
            assert actual == pass_floor(n, 1, inv)
            counts['terminal_envelope_checks'] += 1
        expected_b = Fraction(sum(b * v for b, v in hist.items()), factorial(n))
        min_distribution.append({'n': n, 'mean_b': str(expected_b), 'counts': dict(hist)})
    return {'counts': dict(counts), 'exact_bound_cases_by_n': dict(equality),
            'diagonal_distributions': min_distribution}


def exact_search(n, mode):
    """Uniform means over all n! inputs; outputs every tied optimal table.

    mode='none' enumerates every legal table.
    mode='scan' uses actual prefix cost plus mandatory final scan.
    mode='joint' uses the proved (I,b) relaxation and transport bound.
    """
    assert mode in ('none', 'scan', 'joint')
    start = time.perf_counter()
    mass = factorial(n)
    root = Counter({x: 1 for x in permutations(range(n))})
    dp = build_joint_dp(n) if mode == 'joint' else None
    best_total, winners = None, []
    stats = Counter()

    @lru_cache(maxsize=400000)
    def transition(x, h):
        return gap_pass(x, h)

    @lru_cache(maxsize=400000)
    def lower_state(x, u):
        return suffix_floor(x, u, dp)

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
        if best_total is not None and mode != 'none':
            if mode == 'scan':
                remaining = mass * (n - 1)
            else:
                remaining = sum(weight * lower_state(x, u) for x, weight in dist.items())
            # Strict inequality preserves all tied winners.
            if prefix_total + remaining > best_total:
                stats['pruned_prefixes'] += 1
                stats['pruned_complete_tables'] += 2 ** (u - 1)
                return
        _, tail_total = propagate(dist, 1)
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
    answer = {'n': n, 'mode': mode, 'input_count': mass, 'legal_table_count': 2 ** (n - 2),
              'optimum_total_comparisons': best_total, 'optimum_mean': str(Fraction(best_total, mass)),
              'optimum_mean_decimal': best_total / mass, 'all_winners': sorted(winners),
              'statistics': dict(stats), 'seconds': time.perf_counter() - start}
    transition.cache_clear()
    lower_state.cache_clear()
    return answer


def check_moment_algebra(max_order=40):
    """Exact checks of the new invariant; not checks of the upstream drift."""
    previous = None
    for q in range(2, max_order + 1):
        bq = Fraction(4, 3) ** q * 2 ** (65 * q * (q + 1) + 130)
        kq = 2 ** (130 * q)
        if q == 2:
            root = Fraction(4, 3) * kq
            assert bq == root * root
            assert bq / 4 + kq * root == bq
        else:
            assert bq == Fraction(4, 3) * kq * previous
            assert bq / 4 + kq * previous == bq
        old = 4 ** q * 2 ** (130 * q * q)
        assert bq < old
        previous = bq
    return {'orders_verified': max_order - 1, 'upstream_drift_tested': False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-max-n', type=int, default=7)
    parser.add_argument('--search-max-n', type=int, default=8)
    parser.add_argument('--output', default='verification_results.json')
    args = parser.parse_args()
    if not (2 <= args.check_max_n <= 8 and 2 <= args.search_max_n <= 9):
        parser.error('supported finite checks: 2..8; exhaustive uniform search: 2..9')
    result = {'model': 'uniform distinct-rank permutations; strictly decreasing gaps ending at 1; ordinary key comparisons',
              'status': 'analytic proofs plus finite verification; no Lean compilation',
              'moment_algebra': check_moment_algebra()}
    result['invariants'] = check_invariants(args.check_max_n)
    print(json.dumps({'invariants': result['invariants']['counts']}, ensure_ascii=False), flush=True)
    result['searches'] = []
    for n in range(2, args.search_max_n + 1):
        rows = [exact_search(n, mode) for mode in ('none', 'scan', 'joint')]
        assert len({row['optimum_total_comparisons'] for row in rows}) == 1
        assert all(row['all_winners'] == rows[0]['all_winners'] for row in rows)
        result['searches'].extend(rows)
        print(json.dumps({'n': n, 'mean': rows[0]['optimum_mean'],
                          'winners': rows[0]['all_winners'],
                          'scored_tables': {row['mode']: row['statistics']['scored_complete_tables'] for row in rows}},
                         ensure_ascii=False), flush=True)
    path = Path(args.output)
    path.write_text(json.dumps(result, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(str(path.resolve()), flush=True)


if __name__ == '__main__':
    main()
