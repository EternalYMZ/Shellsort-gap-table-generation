#!/usr/bin/env python3
"""Exact rational certificate for the two-temperature eight-pass lower bound.

Input lemma: after h-pass, n=m*h+r, A=(m+1)*r*r+m*(h-r)*(h-r),
the next g-pass has expected cost >=A/(4*g)+n/4-g/2.
All arithmetic uses Fractions, elementary log series and integer square roots.
"""
from fractions import Fraction as F
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from functools import lru_cache
from math import isqrt
from pathlib import Path
import argparse
import json
N=10**9
GRID=10**45
TERMS=32
CUTOFF=200

def rounded(x):
    lo=x[0].numerator*GRID//x[0].denominator
    hi=-((-x[1].numerator*GRID)//x[1].denominator)
    return F(lo,GRID),F(hi,GRID)
def const(x):
    x=F(x);return x,x
def add(x,y):return rounded((x[0]+y[0],x[1]+y[1]))
def neg(x):return -x[1],-x[0]
def sub(x,y):return add(x,neg(y))
def mul(x,y):
    z=[a*b for a in x for b in y];return rounded((min(z),max(z)))
def scale(x,a):return mul(x,const(a))
def divide(x,y):
    assert y[0]>0
    z=[a/b for a in x for b in y];return rounded((min(z),max(z)))
def square(x):
    lo=0 if x[0]<=0<=x[1] else min(x[0]*x[0],x[1]*x[1])
    return rounded((lo,max(x[0]*x[0],x[1]*x[1])))
def sqrt_interval(x):
    assert x[0]>=0
    q=GRID
    k=isqrt(x[0].numerator*q*q//x[0].denominator)
    j=isqrt(x[1].numerator*q*q//x[1].denominator)
    if j*j*x[1].denominator<x[1].numerator*q*q:j+=1
    return F(k,q),F(j,q)
def unit_log(x):
    assert 1<=x<=2
    v=(x-1)/(x+1);v2=v*v;power=v;total=F(0)
    for j in range(TERMS):
        total+=power/(2*j+1);power*=v2
    lo=2*total
    return rounded((lo,lo+2*power/((2*TERMS+1)*(1-v2))))
LN2=unit_log(F(2))
@lru_cache(None)
def log_interval(x):
    x=F(x);assert x>0;k=0
    while x>2:x/=2;k+=1
    while x<1:x*=2;k-=1
    return add(unit_log(x),scale(LN2,k))
def display(x):
    def endpoint(y,mode):
        with localcontext() as ctx:
            ctx.prec=65;ctx.rounding=mode
            return str(Decimal(y.numerator)/Decimal(y.denominator))
    return {'lower':endpoint(x[0],ROUND_FLOOR),'upper':endpoint(x[1],ROUND_CEILING)}
def imin(xs):return min(x[0] for x in xs),min(x[1] for x in xs)
def imax(x,y):return max(x[0],y[0]),max(x[1],y[1])
def arrays():
    aa=[F(0)];bb=[const(0)];harm=F(0);lf=const(0)
    for ell in range(1,CUTOFF+2):
        harm+=F(1,ell);lf=add(lf,log_interval(F(ell)))
        aa.append(F(ell-1,4)+1-harm/ell);bb.append(scale(lf,F(1,ell)))
    lf_lower=add(sub(scale(log_interval(F(2*N+1,2)),F(2*N+1,2)),const(N)),scale(LN2,F(1,2)))
    return aa,bb,scale(lf_lower,F(1,N))
def verify(td,ud,retain_mixture):
    aa,bb,entropy=arrays();t=F(td);u=F(ud)
    L=neg(log_interval(t));U=neg(log_interval(u));w=sub(const(1),divide(U,L))
    at=sub(log_interval(t),log_interval(1-t));au=sub(log_interval(u),log_interval(1-u))
    B=sub(divide(au,L),scale(w,F(1,2)))
    K=mul(w,B)
    correction=add(neg(divide(sub(au,at),L)),scale(w,F(1,4)))
    assert F(1,2)<t<u<1 and w[0]>0 and B[0]>0
    fs=[None]
    for ell in range(1,CUTOFF+2):
        fs.append(add(const(aa[ell]+7),divide(add(sub(entropy,bb[ell]),scale(log_interval(1-t),7)),L)))
    rows=[]
    for m in range(1,CUTOFF+1):
        d0=F(1,2*m+1)
        simple=add(add(imin([fs[m],fs[m+1]]),correction),sqrt_interval(scale(K,d0)))
        chosen=simple;mode='minimum_of_adjacent_lengths';mixed=None
        if retain_mixture:
            a=m*(m+1)*(2*m+1)
            slope=scale(sub(fs[m],fs[m+1]),m*(m+1))
            f0=scale(add(scale(fs[m],m),scale(fs[m+1],m+1)),d0)
            rad=sub(K,scale(square(slope),F(1,a)))
            if rad[0]>0:
                mixed=add(add(f0,correction),sqrt_interval(scale(rad,d0)))
                chosen=imax(simple,mixed)
                if mixed[0]>simple[0]:mode='retained_chain_length_mixture'
        row={'m':m,'bound_per_key':display(chosen),'method':mode}
        if mixed:row['mixture_bound_per_key']=display(mixed)
        rows.append((chosen,row))
    min_iv=imin([x[0] for x in rows]);raw=N*min_iv[0];target=raw.numerator//raw.denominator
    checks={'ordered_temperatures':F(1,2)<t<u<1,'positive_w':w[0]>0,'positive_B':B[0]>0,
      'all_m_1_through_200_above_integer_target':all(x[0][0]>F(target,N) for x in rows),
      'm_at_least_201_first_pass_alone_above_target':aa[CUTOFF+1]>F(target,N),
      'one_pass_table_above_target':F(N*(N-1),4)>target}
    return {'t_exact':td,'u_exact':ud,'retain_chain_length_mixture':retain_mixture,
      'total_comparison_lower_bound':target,'improvement_over_certified_one_temperature_bound':target-40875955994,
      'gap_to_50_billion':50000000000-target,'uniform_per_key_bound':display(min_iv),
      'smallest_rows':sorted([r for _,r in rows],key=lambda r:Decimal(r['bound_per_key']['lower']))[:5],
      'w':display(w),'B':display(B),'K':display(K),'correction':display(correction),
      'long_chain_first_pass_per_key':display(const(aa[CUTOFF+1])),
      'checks':checks,'passed':all(checks.values())}
def run():
    simple=verify('0.8074055','0.80776465',False)
    mixed=verify('0.8071469627378816','0.8075234450681327',True)
    return {'n':N,'at_most_passes':8,'logarithm_series_terms':TERMS,
      'outward_rounding_denominator':str(GRID),
      'sqrt_method':'Integer square-root floor/ceiling on exact rational endpoints.',
      'model':'Uniform random distinct keys; fixed legal ordinary insertion Shellsort gap table ending in 1.',
      'scope':'Exact scalar certificate; no Lean formalization or global numerical optimality claim.',
      'simple_certificate':simple,'retained_mixture_certificate':mixed,
      'passed':simple['passed'] and mixed['passed']}
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=run();content=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if args.output:args.output.write_text(content,encoding='utf-8')
    print(content,end='');raise SystemExit(0 if result['passed'] else 1)
