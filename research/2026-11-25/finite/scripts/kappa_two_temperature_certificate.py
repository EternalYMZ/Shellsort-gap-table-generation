#!/usr/bin/env python3
"""Exact certificates: cross-row second-pass structure + two temperatures.

Requires sibling two_temperature_certificate.py (interval arithmetic only).
All kappa coefficients are recomputed from their defining finite sums.
No floating point or conjectural kappa closed form is used.
"""
from fractions import Fraction as F
from math import comb
from pathlib import Path
from functools import lru_cache
from decimal import Decimal
import argparse
import json
import two_temperature_certificate as I

@lru_cache(None)
def kappa(m):
    row=[comb(m,j) for j in range(m+1)];total=F(0)
    for t in range(2,2*m-1):
        amin,amax=max(1,t+1-m),min(m,t//2)
        numerator=0
        for c in range(max(0,t-m),min(m,amax-1)+1):
            count=max(0,amax-max(amin,c+1)+1)
            numerator+=count*row[c]*row[t-c]
        total+=F(numerator,comb(2*m,t))
    return F(1,4)+total/m

def verify(p,td,ud):
    aa,bb,entropy=I.arrays();t=F(td);u=F(ud);N=I.N
    L=I.neg(I.log_interval(t));U=I.neg(I.log_interval(u))
    w=I.sub(I.const(1),I.divide(U,L))
    at=I.sub(I.log_interval(t),I.log_interval(1-t));au=I.sub(I.log_interval(u),I.log_interval(1-u))
    diff=I.divide(I.sub(au,at),L);al_u_over_L=I.divide(au,L)
    B=I.sub(al_u_over_L,I.scale(w,F(1,2)));K=I.mul(w,B)
    correction=I.add(I.neg(diff),I.scale(w,F(1,4)))
    assert F(1,2)<t<u<1 and w[0]>0 and B[0]>0
    fs=[None]
    for ell in range(1,I.CUTOFF+2):
        fs.append(I.add(I.const(aa[ell]+p-1),I.divide(I.add(I.sub(entropy,bb[ell]),I.scale(I.log_interval(1-t),p-1)),L)))
    rows=[];positive_kappa_roots=0
    for m in range(1,I.CUTOFF+1):
        d0=F(1,2*m+1)
        simple=I.add(I.add(I.imin([fs[m],fs[m+1]]),correction),I.sqrt_interval(I.scale(K,d0)))
        chosen=simple;mode='same_row_minimum'
        a=m*(m+1)*(2*m+1)
        slope=I.scale(I.sub(fs[m],fs[m+1]),m*(m+1))
        f0=I.scale(I.add(I.scale(fs[m],m),I.scale(fs[m+1],m+1)),d0)
        rad=I.sub(K,I.scale(I.square(slope),F(1,a)))
        if rad[0]>0:
            mixed=I.add(I.add(f0,correction),I.sqrt_interval(I.scale(rad,d0)))
            chosen=I.imax(chosen,mixed)
            if mixed[0]>simple[0]:mode='same_row_mixture'
        a1=(m+1)*kappa(m+1);a0=m*kappa(m)
        ak=a1*m*m+a0*(m+1)*(m+1)
        bk=a1*m+a0*(m+1)
        dk=a1*a0/ak
        penalty=((m+1)*(kappa(m+1)-F(1,4))+m*(kappa(m)-F(1,4)))/4
        Q=I.sub(al_u_over_L,I.scale(w,penalty+F(1,2)))
        q=I.add(I.sub(I.sub(I.scale(fs[m+1],m+1),I.scale(fs[m],m)),diff),I.scale(w,F(1,2)-a1+a0))
        s=I.sub(slope,I.scale(w,a0*(m+1)-a1*m))
        radk=I.sub(I.scale(I.mul(w,Q),4),I.scale(I.square(s),1/ak))
        new=None
        if Q[0]>0 and radk[0]>0:
            new=I.add(I.add(q,I.scale(s,bk/ak)),I.sqrt_interval(I.scale(radk,dk)))
            if new[0]>chosen[0]:mode='cross_row_kappa_mixture'
            chosen=I.imax(chosen,new);positive_kappa_roots+=1
        row={'m':m,'bound_per_key':I.display(chosen),'method':mode}
        if new:row['cross_row_bound_per_key']=I.display(new)
        rows.append((chosen,row))
    min_iv=I.imin([r[0] for r in rows]);value=N*min_iv[0];target=value.numerator//value.denominator
    old={7:50017343203,8:40875955994}[p]
    checks={
      'ordered_temperatures':F(1,2)<t<u<1,'positive_w':w[0]>0,'positive_same_row_B':B[0]>0,
      'kappa_16_matches_independent_exact_value':kappa(16)==F(268435456,300540195),
      'all_m_1_through_200_above_integer_target':all(z[0][0]>F(target,N) for z in rows),
      'm_at_least_201_first_pass_alone_above_target':aa[I.CUTOFF+1]>F(target,N),
      'one_pass_table_above_target':F(N*(N-1),4)>target,
    }
    return {'at_most_passes':p,'t_exact':td,'u_exact':ud,
      'total_comparison_lower_bound':target,'uniform_per_key_bound':I.display(min_iv),
      'improvement_over_one_temperature_bound':target-old,
      'signed_margin_above_50_billion':target-50000000000,
      'smallest_rows':sorted([r for _,r in rows],key=lambda r:Decimal(r['bound_per_key']['lower']))[:5],
      'rows_where_cross_row_Cauchy_radical_is_certifiably_positive':positive_kappa_roots,
      'w':I.display(w),'first_pass_long_chain_bound_per_key':I.display(I.const(aa[I.CUTOFF+1])),
      'checks':checks,'passed':all(checks.values())}

def run():
    results=[verify(7,'0.8615169789675514','0.862089636727044'),
             verify(8,'0.806886602104151','0.8078956997072975')]
    return {'n':I.N,'arithmetic':'Fraction intervals; 32-term rigorous logarithm series; outward rational sqrt.',
      'kappa_source':'Recomputed from the defining finite order-statistic hypergeometric sums.',
      'scope':'Analytic two-pass structure theorem plus exact scalar certificate. No Lean verification or global optimizer claim.',
      'pass_results':results,'passed':all(x['passed'] for x in results)}
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
    args=parser.parse_args();result=run();content=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    if args.output:args.output.write_text(content,encoding='utf-8')
    print(content,end='');raise SystemExit(0 if result['passed'] else 1)
