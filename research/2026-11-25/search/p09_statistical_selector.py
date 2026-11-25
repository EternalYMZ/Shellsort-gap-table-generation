#!/usr/bin/env python3
"""P09: exact parameter planning and a capped-score candidate selector.

The probabilistic guarantee requires the assumptions in research_notes.md.
Parameters here use normalized moments E[Y**q] <= 2**(65*(q-1)*(q-2)).
The CLI generates parameters and finite mechanical checks; it does NOT run
the astronomically large sample counts prescribed by asymptotic bounds.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import count, product
from pathlib import Path
import argparse
import json


def ceil_log2(x: Fraction) -> int:
    if x <= 0:
        raise ValueError('positive rational required')
    k = x.numerator.bit_length() - x.denominator.bit_length()
    if k >= 0:
        if (x.denominator << k) < x.numerator:
            k += 1
    elif x.denominator < (x.numerator << (-k)):
        k += 1
    return k


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


@dataclass(frozen=True)
class SelectorPlan:
    moment_order: int
    cap: int
    samples_per_candidate: int
    max_candidates: int


def plan_for_delta(delta: Fraction):
    """Exact rational validation, conservative integer powers/log bounds.

    E[Y**q] <= 2**(65*(q-1)*(q-2)), q>=2; this includes E[Y**2]<=1.
    Returns the smallest power-of-two cap found over all integer q>=2.
    The search terminates once the order-dependent lower bound exceeds it.
    """
    delta = Fraction(delta)
    if not 0 < delta < 1:
        raise ValueError('0 < delta < 1 required')
    log_bound = ceil_log2(Fraction(16) / delta)
    best = None
    examined = []
    for q in count(2):
        r = q - 1
        if best is not None and 65 * (r - 1) > best[0]:
            break
        # Smallest k with delta * 2**(k*r) >= 16 * B_q.
        k = max(2, ceil_div(65 * r * (r - 1) + log_bound, r))
        examined.append((q, k))
        if best is None or (k, q) < best:
            best = (k, q)
    k, q = best
    cap = 1 << k
    # ln(16/delta) <= ceil(log2(16/delta)); no floating point needed.
    samples = 8 * cap * log_bound
    rejection_bound, attempts = Fraction(1), 0
    while rejection_bound > delta / 2:
        rejection_bound *= Fraction(9, 16)
        attempts += 1
    moment = 1 << (65 * (q - 1) * (q - 2))
    assert Fraction(moment, cap ** (q - 1)) <= delta / 16
    assert rejection_bound <= delta / 2
    plan = SelectorPlan(q, cap, samples, attempts)
    return plan, {'delta': str(delta), 'cap_log2': k, 'moment_order': q,
                  'samples_per_candidate': str(samples), 'max_candidates': attempts,
                  'worst_queries': str(attempts * samples),
                  'worst_score_sum': str(attempts * (3 * samples + cap)),
                  'orders_examined': examined,
                  'guarantee': 'Pr[no acceptance or accepted true mean > 5] < delta, under the stated model'}


def select_candidate(new_candidate, capped_score, plan: SelectorPlan):
    """Return first accepted opaque candidate, or None on budget exhaustion.

    new_candidate() must produce independent candidates from one fixed law.
    For the theorem, plan must come from plan_for_delta or satisfy the same
    parameter inequalities; this function also allows smaller toy test plans.
    capped_score(h, cap) must return a fresh independent draw of min(Y_h,cap).
    Its running cost must be separately justified; score_sum is not blindly
    treated as runtime. This routine accepts probabilistically, not by an
    exact deterministic certificate of the candidate's true mean.
    """
    if plan.cap <= 0 or plan.samples_per_candidate <= 0 or plan.max_candidates <= 0:
        raise ValueError('positive plan entries required')
    queries = attempts = 0
    score_sum = Fraction(0)
    threshold = 3 * plan.samples_per_candidate
    for _ in range(plan.max_candidates):
        candidate = new_candidate()
        attempts += 1
        subtotal = Fraction(0)
        for _ in range(plan.samples_per_candidate):
            score = Fraction(capped_score(candidate, plan.cap))
            if not 0 <= score <= plan.cap:
                raise ValueError('oracle returned a score outside [0,cap]')
            queries += 1
            subtotal += score
            score_sum += score
            # The threshold uses the FULL planned sample count, not the
            # number of samples seen so far. Nonnegativity makes this safe.
            if subtotal > threshold:
                break
        else:
            return candidate, {'accepted': True, 'queries': queries,
                               'attempts': attempts, 'score_sum': str(score_sum)}
    assert queries <= plan.max_candidates * plan.samples_per_candidate
    assert score_sum <= plan.max_candidates * (threshold + plan.cap)
    return None, {'accepted': False, 'queries': queries,
                  'attempts': attempts, 'score_sum': str(score_sum)}


def finite_checks():
    cases = pairs = rational_cases = 0
    for denominator in range(1, 25):
        for numerator in range(1, 50):
            x = Fraction(numerator, denominator)
            k = ceil_log2(x)
            power = Fraction(1 << k) if k >= 0 else Fraction(1, 1 << (-k))
            assert power >= x > power / 2
            rational_cases += 1
    for cap in (1, 2, 4, 8):
        for m in range(1, 6):
            threshold = 3 * m
            for scores in product(range(cap + 1), repeat=m):
                subtotal = 0
                stopped = False
                for score in scores:
                    subtotal += score
                    if subtotal > threshold:
                        stopped = True
                        break
                assert (not stopped) == (sum(scores) <= threshold)
                assert subtotal <= threshold + cap
                cases += 1
    streams = list(product(range(5), repeat=3))
    toy = SelectorPlan(2, 4, 3, 2)
    for first in streams:
        for second in streams:
            samples = [iter(first), iter(second)]
            ids = iter((0, 1))
            winner, stats = select_candidate(lambda: next(ids),
                                             lambda h, cap: next(samples[h]), toy)
            expected = next((i for i, s in enumerate((first, second)) if sum(s) <= 9), None)
            assert winner == expected
            assert stats['queries'] <= 6
            assert Fraction(stats['score_sum']) <= 26
            pairs += 1
    plans = []
    for confidence_bits in (4, 20, 100, 1000, 10000):
        delta = Fraction(1, 1 << confidence_bits)
        plan, report = plan_for_delta(delta)
        brute = min((max(2, ceil_div(65*(q-1)*(q-2)+confidence_bits+4, q-1)), q)
                    for q in range(2, 100))
        assert (report['cap_log2'], plan.moment_order) == brute
        # Store compact parameters, not huge decimal numerator/denominator strings.
        plans.append({'confidence_bits': confidence_bits,
                      'moment_order': plan.moment_order,
                      'cap_log2': report['cap_log2'],
                      'max_candidates': plan.max_candidates,
                      'worst_queries_log2_ceiling': (plan.max_candidates*plan.samples_per_candidate-1).bit_length()})
    for q in range(2, 101):
        bq = Fraction(4,3)**q * (1 << (65*q*(q+1)+130))
        scale = Fraction(4,3) * (1 << 260)
        assert bq / scale**q == (1 << (65*(q-1)*(q-2)))
    return {'ceil_log2_rational_cases': rational_cases,
            'early_rejection_streams': cases,
            'first_accept_stream_pairs': pairs,
            'normalization_orders_checked': 99,
            'parameter_examples': plans,
            'scope': 'finite arithmetic and decision-equivalence checks; no empirical proof of probability guarantees; no huge selector run'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--verify', action='store_true')
    parser.add_argument('--confidence-bits', type=int, default=20)
    parser.add_argument('--output', default='selector_verification_results.json')
    args = parser.parse_args()
    if args.verify:
        result = finite_checks()
        Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps(result, indent=2))
    else:
        if not 1 <= args.confidence_bits <= 10000:
            parser.error('confidence bits must be in 1..10000')
        plan, report = plan_for_delta(Fraction(1, 1 << args.confidence_bits))
        print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
