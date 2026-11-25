#!/usr/bin/env python3
"""Fast certified lower bounds for JSONL records containing {a,b,gaps}.

No sorting of length-n arrays is performed. A rational-log precomputation
is followed solely by integer arithmetic for each submitted gap table.
The fixed-temperature grid gives rigorous witnesses, not globally optimized
bounds. Every integer comparison bound is rounded down.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
from math import gcd
import argparse,json,time

SCALE=10**24
TEMPERATURES=['0.02','0.05','0.10','0.15','0.20','0.25','0.30','0.35','0.40','0.45','0.50','0.55','0.60','0.65','0.70','0.75','0.80','0.85','0.90','0.95']
GCD_FINAL_PASS_BOUND_N1E9=190_181_443_578
assert 10**27-27648*GCD_FINAL_PASS_BOUND_N1E9**2>0
assert 27648*(GCD_FINAL_PASS_BOUND_N1E9+1)**2-10**27>0

def floor_q(x):return x.numerator//x.denominator
def ceil_q(x):return -((-x.numerator)//x.denominator)
def unit_log_bounds(x):
    assert 1<=x<=2
    v=(x-1)/(x+1);v2=v*v;power=v;total=F(0);j=0
    while True:
        total+=power/(2*j+1)
        power*=v2
        remainder=2*power/((2*j+3)*(1-v2))
        if remainder*SCALE<1:break
        j+=1
    return floor_q(2*total*SCALE),ceil_q((2*total+remainder)*SCALE)
LN2=unit_log_bounds(F(2))
@lru_cache(None)
def log_bounds(x):
    x=F(x);assert x>0;k=0
    while x<1:x*=2;k-=1
    while x>2:x/=2;k+=1
    lo,hi=unit_log_bounds(x)
    if k>=0:return lo+k*LN2[0],hi+k*LN2[1]
    return lo+k*LN2[1],hi+k*LN2[0]

def temperature_data(td):
    t=F(td);gamma=1-2*t
    K=512 if t>=F('0.95') else (256 if t>=F('0.90') else 128)
    lt=log_bounds(t);lc=log_bounds(1-t)
    alpha_upper=lt[1]-lc[0]
    correction=[0];prefix=[0];power=F(1)
    for j in range(1,K+1):
        ub=log_bounds(1+gamma*power)[1]
        correction.append(ub);prefix.append(prefix[-1]+ub);power*=t
    tail_sum_upper=ceil_q(max(F(0),gamma)*power/(1-t)*SCALE)
    tail_last_upper=ceil_q(max(F(0),gamma)*power*SCALE)
    return {'t':td,'cutoff':K,'L_lower':-lt[1],'L_upper':-lt[0],
            'alpha_upper':alpha_upper,'correction_upper':correction,
            'prefix_correction_upper':prefix,
            'tail_sum_upper':tail_sum_upper,'tail_last_upper':tail_last_upper}

def log_partition_upper(n,h,c):
    q,r=divmod(n,h);K=c['cutoff']
    base=(n-h)*c['alpha_upper']
    if q<=K:
        return base+h*c['prefix_correction_upper'][q-1]+r*c['correction_upper'][q]
    return (base+h*c['prefix_correction_upper'][K]+h*c['tail_sum_upper']+r*c['tail_last_upper'])

def divide_lower(numerator,c):
    return numerator//(c['L_upper'] if numerator>=0 else c['L_lower'])

def prepare(n,max_m):
    logs=[(0,0)]+[log_bounds(F(i)) for i in range(1,max_m+2)]
    lfub=[0];H=[F(0)]
    for i in range(1,max_m+2):
        lfub.append(lfub[-1]+logs[i][1]);H.append(H[-1]+F(1,i))
    # Concavity: log(n!) >= integral from 1/2 to n+1/2 of log(x).
    l=log_bounds(F(2*n+1,2))[0]
    entropy_lower=((2*n+1)*l+LN2[0])//2-n*SCALE
    temperatures=[temperature_data(t) for t in TEMPERATURES]
    return entropy_lower,lfub,H,logs,temperatures

def evaluate(row,n,prepared):
    hlist=row['gaps']
    assert hlist and all(isinstance(h,int) and 1<=h<n for h in hlist)
    assert hlist[-1]==1 and all(hlist[i]>hlist[i+1] for i in range(len(hlist)-1))
    entropy,lfub,H,logs,temps=prepared
    first=hlist[0];m,r=divmod(n,first)
    cchain=F(m*(m-1),4)+m-H[m]
    delta=F(m,2)+1-F(1,m+1)
    first_cost=first*cchain+r*delta
    first_floor=floor_q(first_cost)
    first_entropy_loss_upper=first*lfub[m]+r*logs[m+1][1]
    state_entropy_lower=entropy-first_entropy_loss_upper
    scan=sum(n-h for h in hlist)
    full_best=-10**100;first_best=-10**100;full_t=None;first_t=None
    for c in temps:
        first_logz=log_partition_upper(n,first,c)
        total_logz=first_logz+sum(log_partition_upper(n,h,c) for h in hlist[1:])
        full=divide_lower(entropy-total_logz,c)
        after_first=first_floor+divide_lower(state_entropy_lower-(total_logz-first_logz),c)
        if full>full_best:full_best=full;full_t=c['t']
        if after_first>first_best:first_best=after_first;first_t=c['t']
    best=max(scan,first_floor,full_best,first_best)
    out=dict(row)
    out.update({'scan_lower_bound':scan,'first_pass_mean_floor':first_floor,
                'finite_partition_gibbs_lower_bound':full_best,'finite_partition_best_t':full_t,
                'first_pass_finite_partition_lower_bound':first_best,'first_pass_best_t':first_t,
                'certified_comparison_lower_bound':best,'certified_per_key':best/n,
                'strictly_above_50_billion':best>50_000_000_000,
                'strictly_above_53_billion':best>53_000_000_000})
    return apply_gcd_transport(out,n)

def apply_gcd_transport(row,n):
    """Use the separately proved common-residue final-pass transport lemma.

    It supplies E C_last >= 190181443578 for n=1e9 when every
    nonfinal gap shares a divisor d>1. Add only the OTHER scans.
    """
    out=dict(row);d=0
    for h in out['gaps'][:-1]:d=gcd(d,h)
    out['gcd_of_nonfinal_gaps']=d
    transport=None;old_transport=None;first_replacement=0
    if n==10**9 and d>1:
        old_transport=out['scan_lower_bound']-(n-1)+GCD_FINAL_PASS_BOUND_N1E9
        first_replacement=max(0,out['first_pass_mean_floor']-(n-out['gaps'][0]))
        transport=old_transport+first_replacement
    out['gcd_transport_with_scans_lower_bound']=old_transport
    out['gcd_first_pass_replacement_gain']=first_replacement
    out['gcd_transport_total_lower_bound']=transport
    best=max(out['scan_lower_bound'],out['first_pass_mean_floor'],
             out['finite_partition_gibbs_lower_bound'],
             out['first_pass_finite_partition_lower_bound'],transport or 0)
    out['certified_comparison_lower_bound']=best
    out['certified_per_key']=best/n
    out['strictly_above_50_billion']=best>50_000_000_000
    out['strictly_above_53_billion']=best>53_000_000_000
    out['at_least_200_billion']=best>=200_000_000_000
    return out

def summarize(rows,n):
    def subset(xs):
        if not xs:return {'tables':0}
        byscan=sum(r['scan_lower_bound']>50_000_000_000 for r in xs)
        byall=sum(r['certified_comparison_lower_bound']>50_000_000_000 for r in xs)
        bygibbs=sum(max(r['scan_lower_bound'],r['first_pass_mean_floor'],r['finite_partition_gibbs_lower_bound'],r['first_pass_finite_partition_lower_bound'])>50_000_000_000 for r in xs)
        return {'tables':len(xs),'excluded_above_50_billion_by_scanning':byscan,
                'excluded_above_50_billion_by_scanning_and_gibbs':bygibbs,
                'tables_with_gcd_transport_bound':sum(r.get('gcd_transport_total_lower_bound') is not None for r in xs),
                'excluded_above_50_billion_by_all_certificates':byall,
                'additional_exclusions_beyond_scanning':byall-byscan,
                'not_excluded_at_50_billion':len(xs)-byall,
                'excluded_above_53_billion':sum(r['strictly_above_53_billion'] for r in xs),
                'certified_at_least_200_billion':sum(r['certified_comparison_lower_bound']>=200_000_000_000 for r in xs),
                'minimum_certified_bound':min(r['certified_comparison_lower_bound'] for r in xs),
                'maximum_certified_bound':max(r['certified_comparison_lower_bound'] for r in xs)}
    requested={(11,12),(29,33),(8,179)}
    selected=[r for r in rows if (r['a'],r['b']) in requested]
    groups={}
    for r in rows:
        p=len(r['gaps']);groups.setdefault(p,[]).append(r)
    bypasses={str(p):subset(xs) for p,xs in sorted(groups.items())}
    rank=sorted(rows,key=lambda r:(r['certified_comparison_lower_bound'],r['a'],r['b']))[:30]
    def short(r):return {k:r[k] for k in ('a','b','coprime','passes','scan_lower_bound','first_pass_mean_floor','finite_partition_gibbs_lower_bound','first_pass_finite_partition_lower_bound','gcd_transport_total_lower_bound','certified_comparison_lower_bound','certified_per_key','first_pass_best_t') if k in r}
    return {'n':n,'total':subset(rows),'coprime':subset([r for r in rows if r.get('coprime')]),
            'noncoprime':subset([r for r in rows if not r.get('coprime')]),
            'specified_examples':[short(r) for r in selected],
            'smallest_certified_lower_bounds':[short(r) for r in rank],
            'by_pass_count':bypasses,
            'interpretation':'Lower bounds only. A smaller certified bound is not evidence that a table actually sorts faster. All comparisons against budgets are strict integer comparisons.',
            'temperature_grid':TEMPERATURES,'log_scale':str(SCALE),
            'certificate_method':'Exact Fraction log bounds, then integer upper bounds on finite cost partition functions; plus the separately proved common-residue final-pass transport lemma at n=1e9. No sampled permutations and no sorting experiment.',
            'gcd_transport_lemma_input':{'n':10**9,'condition':'gcd of every nonfinal gap >1','last_pass_comparison_lower_bound':GCD_FINAL_PASS_BOUND_N1E9,'combination':'Add scan_lower_bound-(n-1), then replace the first-pass scan by max(first-pass scan, floor exact first-pass mean). Each cost component is counted once.','constant_square_checks_passed':True}}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True);p.add_argument('--summary',type=Path,required=True);p.add_argument('--coefficient-certificate',type=Path);p.add_argument('--n',type=int,default=10**9)
    a=p.parse_args();start=time.monotonic();rows=[json.loads(s) for s in a.input.read_text().splitlines() if s.strip()]
    assert all(r.get('n',a.n)==a.n for r in rows)
    max_m=max(a.n//r['gaps'][0] for r in rows)
    prepared=prepare(a.n,max_m)
    print(f'Prepared exact coefficients; {len(rows)} tables; max first-chain floor {max_m}.',flush=True)
    results=[]
    with a.output.open('w') as f:
        for i,row in enumerate(rows,1):
            out=evaluate(row,a.n,prepared);results.append(out);f.write(json.dumps(out,ensure_ascii=False)+'\n')
            if i%4000==0:print(f'Evaluated {i} tables.',flush=True)
    summary=summarize(results,a.n);summary['elapsed_seconds']=time.monotonic()-start
    a.summary.write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    if a.coefficient_certificate:
        a.coefficient_certificate.write_text(json.dumps({'n':a.n,'scale':str(SCALE),'entropy_log_factorial_lower_scaled':str(prepared[0]),'temperature_coefficients':prepared[4]},indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in ('total','coprime','specified_examples','elapsed_seconds')},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
