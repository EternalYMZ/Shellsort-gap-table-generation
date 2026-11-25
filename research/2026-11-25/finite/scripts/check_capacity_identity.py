from itertools import permutations
from fractions import Fraction as F
from math import factorial,gcd
from pathlib import Path
import json
from capacity_explore import second_inversions

def one_sort(a,h):
    b=list(a)
    for r in range(h):b[r::h]=sorted(b[r::h])
    return b

def check(n,h,g):
    total=[0]*n;records=[0]*n;failures=0
    for x in permutations(range(n)):
        a=one_sort(x,h)
        for i in range(g,n):
            j=i//g;m=sum(a[u]>a[i] for u in range(i%g,i,g))
            total[i]+=m
            records[i]+=int(m==j)
            failures+=int(m<j)
    den=factorial(n)
    bs,expected=second_inversions(n,h,g,exact=True)
    for block,val in zip(bs,expected):
        assert F(sum(total[block[0]:block[1]]),den)==val,(n,h,g,block,val)
    T=h//gcd(h,g)
    for i in range(g,n):
        j=i//g
        assert records[i]==0 if j>=T else F(records[i],den)<=F(1,j+1),(n,h,g,i)
    lower=n-sum(sum((F(1,j) for j in range(1,min(len(range(r,n,g)),T)+1)),F(0)) for r in range(g))
    assert F(failures,den)>=lower
    return {'n':n,'h':h,'g':g,'permutations':den,'exact_expected_inversions':str(F(sum(total),den)),
            'exact_expected_failed_comparisons':str(F(failures,den)),'record_bound':str(lower),'passed':True}

if __name__=='__main__':
    results=[check(n,h,g) for n in range(3,8) for h in range(2,n) for g in range(1,h)]
    results += [check(8,h,g) for h,g in [(5,3),(4,1),(3,2)]]
    data={'scope':'All n=3,...,7 and h>g plus three n=8 cases, all input permutations',
          'checks':['Exact blockwise mean second-pass shifts','Second-pass record-minimum bound, with h-sort as sole prefix'],
          'passed':all(r['passed'] for r in results),'cases':results}
    Path(__file__).with_name('capacity_identity_checks.json').write_text(json.dumps(data,indent=2)+'\n')
    print({'cases':len(results),'permutation_schedule_pairs':sum(r['permutations'] for r in results),'passed':data['passed']})
