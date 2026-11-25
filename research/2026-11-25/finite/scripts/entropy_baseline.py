#!/usr/bin/env python3
"""Exact-rational certificates for the first-pass / suffix entropy relaxation.

The exploratory t choices are rationalized near numerical maximizers.
All reported integer lower bounds and barrier inequalities are certified
with rational logarithm enclosures, not floating-point comparisons.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from pathlib import Path
import argparse
import json

N = 10**9
GRID = 10**45
TERMS = 32

def add(x, y):
    return x[0] + y[0], x[1] + y[1]

def neg(x):
    return -x[1], -x[0]

def sub(x, y):
    return add(x, neg(y))

def scale(x, a):
    a = F(a)
    v = [a*x[0], a*x[1]]
    return min(v), max(v)

def divide(x, y):
    assert y[0] > 0
    v = [a/b for a in x for b in y]
    return min(v), max(v)

def const(x):
    x = F(x)
    return x, x

def grid_enclosure(x):
    """Keep denominators manageable; rounding is exact and outward."""
    lo = (x[0].numerator*GRID)//x[0].denominator
    hi = -((-x[1].numerator*GRID)//x[1].denominator)
    return F(lo, GRID), F(hi, GRID)

def unit_log(x):
    assert 1 <= x <= 2
    v = (x-1)/(x+1)
    v2 = v*v
    power = v
    total = F(0)
    for j in range(TERMS):
        total += power/(2*j+1)
        power *= v2
    lo = 2*total
    error = 2*power/((2*TERMS+1)*(1-v2))
    return grid_enclosure((lo, lo+error))

LN2 = unit_log(F(2))

@lru_cache(None)
def log_interval(x):
    x = F(x)
    assert x > 0
    k = 0
    while x > 2:
        x /= 2
        k += 1
    while x < 1:
        x *= 2
        k -= 1
    return grid_enclosure(add(unit_log(x), scale(LN2,k)))

def decimal_endpoint(x, rounding):
    with localcontext() as ctx:
        ctx.prec = 65
        ctx.rounding = rounding
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def display(x):
    return {'lower':decimal_endpoint(x[0],ROUND_FLOOR),
            'upper':decimal_endpoint(x[1],ROUND_CEILING)}

PARAMETERS = [
    (3,'0.996912471162576169901',3890),
    (4,'0.983302817119471821455',970),
    (5,'0.954488469800381056532',450),
    (6,'0.912278761631825846716',285),
    (7,'0.861829707674505021083',210),
    (8,'0.807360223728423898574',175),
    (9,'0.753708555890462242035',155),
    (10,'0.702006571958902461044',145),
    (11,'0.653632702927725151992',135),
    (12,'0.607297935758757294376',130),
]

def run():
    max_l = max(x[2] for x in PARAMETERS)
    harmonic = F(0)
    log_fact = const(0)
    aa = [F(0)]
    bb = [const(0)]
    for ell in range(1,max_l+1):
        harmonic += F(1,ell)
        log_fact = add(log_fact,log_interval(F(ell)))
        aa.append(F(ell-1,4)+1-harmonic/ell)
        bb.append(scale(log_fact,F(1,ell)))
    log_n = log_interval(F(N))
    old_A = sub(log_n,const(1))
    # Concavity of log: sum log(k) >= integral_{1/2}^{n+1/2} log(x) dx.
    log_factorial_lower = add(
        sub(scale(log_interval(F(2*N+1,2)),F(2*N+1,2)),const(N)),
        scale(LN2,F(1,2)))
    new_A = scale(log_factorial_lower,F(1,N))
    results = []
    for p,td,L in PARAMETERS:
        r = p-1
        t = F(td)
        den = neg(log_interval(t))
        rlog = scale(log_interval(1-t),r)
        intervals = []
        old_intervals = []
        for ell in range(1,L+1):
            constant = const(aa[ell]+r)
            intervals.append(add(constant,divide(add(sub(new_A,bb[ell]),rlog),den)))
            old_intervals.append(add(constant,divide(add(sub(old_A,bb[ell]),rlog),den)))
        min_iv = min(x[0] for x in intervals),min(x[1] for x in intervals)
        min_old = min(x[0] for x in old_intervals),min(x[1] for x in old_intervals)
        target = (N*min_iv[0]).numerator//(N*min_iv[0]).denominator
        checks = {
            'all_short_chain_lower_endpoints_exceed_target':all(x[0]>F(target,N) for x in intervals),
            'long_chain_first_pass_alone_exceeds_target':aa[L]>F(target,N),
            'positive_denominator':den[0]>0,
        }
        min_index = min(range(L),key=lambda i:intervals[i][0])
        results.append({
            'at_most_passes':p,'t_exact':td,'cutoff':L,
            'lower_bound_total_comparisons':target,
            'minimizing_chain_length_at_this_t':min_index+1,
            'fixed_t_relaxation_per_key':display(min_iv),
            'original_n_log_n_minus_n_relaxation_per_key':display(min_old),
            'long_chain_a_L':display(const(aa[L])),
            'checks':checks,'passed':all(checks.values())})

    # Eight-pass artificial suffix-record law for the finite-alphabet barrier.
    t = F(101,125)  # .808
    M = 100
    u = t**M
    mean_m = t/(1-t)-M*u/(1-u)
    entropy_one = sub(add(neg(log_interval(1-t)),log_interval(1-u)),
                      scale(log_interval(t),mean_m))
    K = 7*N-M*28
    V = 7*N-28
    fake_total_cost = N*aa[16]+(V-K)+K*(1+mean_m)
    # Elementary upper bound log(n!) <= integral_1^n log x dx + log n.
    log_fact_upper = add(sub(scale(log_n,N),const(N-1)),log_n)
    entropy_required_upper = sub(log_fact_upper,scale(bb[16],N))
    margin = sub(scale(entropy_one,K),entropy_required_upper)
    barrier = {
        'gap_table':[62500000,7,6,5,4,3,2,1],
        'artificial_record_law':{'random_coordinates':K,'total_suffix_coordinates':V,
                                 't':'101/125','support_m':'0,...,99',
                                 'all_coordinates_with_j_less_than_100':'m=0'},
        'mean_total_cost':display(const(fake_total_cost)),
        'entropy_margin_above_required_upper_bound':display(margin),
        'entropy_per_random_digit':display(entropy_one),
        'checks':{'cost_below_41_billion':fake_total_cost<41_000_000_000,
                  'entropy_above_actual_required':margin[0]>0},
        'scope':'Artificial law on allowed insertion digits, not asserted realizable by Shellsort. It certifies a barrier for the entropy-and-digit-range relaxation only.'}
    barrier['passed']=all(barrier['checks'].values())

    # A cap for max_t min_l f_l(t): min_l f_l <= f_16. The derivative of
    # f_16 has one zero, since D'(t)=-7 log(1/t)/(1-t)^2<0.
    derivative_checks = {}
    for name,td in [('lo','0.807360223'),('hi','0.807360225')]:
        t=F(td);s=neg(log_interval(t))
        numerator=add(sub(new_A,bb[16]),scale(log_interval(1-t),7))
        D=sub(numerator,scale(s,7*t/(1-t)))
        derivative_checks[name]=D
    hi=F('0.807360225')
    cap=aa[16]+F(7)/(1-hi)
    scalar_cap={'t_lower':'0.807360223','t_upper':'0.807360225',
                'D_lower_t':display(derivative_checks['lo']),
                'D_upper_t':display(derivative_checks['hi']),
                'upper_cap_per_key':display(const(cap)),
                'checks':{'D_at_lower_positive':derivative_checks['lo'][0]>0,
                          'D_at_upper_negative':derivative_checks['hi'][1]<0,
                          'cap_below_40_876_per_key':cap<F('40.876')}}
    scalar_cap['passed']=all(scalar_cap['checks'].values())
    return {'n':N,'logarithm_series_terms':TERMS,'rounding_grid_denominator':str(GRID),
            'numeric_lower_bounds_are_exactly_certified':True,
            'optimization_claim':'Rational t witnesses near numerical envelope maximizers; no global optimizer claim is needed for the lower bounds.',
            'pass_results':results,'eight_pass_scalar_cap':scalar_cap,
            'eight_pass_finite_alphabet_barrier':barrier,
            'passed':all(x['passed'] for x in results) and barrier['passed'] and scalar_cap['passed']}

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=run()
    content=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if args.output:args.output.write_text(content,encoding='utf-8')
    print(content,end='')
    raise SystemExit(0 if result['passed'] else 1)
