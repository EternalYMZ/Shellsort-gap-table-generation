from functools import lru_cache
from math import log,lgamma,gcd,floor
from fractions import Fraction
import numpy as np
from scipy.stats import hypergeom
from scipy.optimize import minimize_scalar

def blocks(n,h):
    q,r=divmod(n,h)
    out=[]
    for k in range(q+1):
        if r:out.append((k*h,k*h+r,q+1,k,r))
        if k<q and h-r:out.append((k*h+r,(k+1)*h,q,k,h-r))
    return out

def cyclic_parts(a,s,g):
    a%=g
    return [(a,a+s)] if a+s<=g else [(a,g),(0,a+s-g)]

def residue_pairs(a,b,c,d,g):
    qa,ra=divmod(b-a,g);qb,rb=divmod(d-c,g)
    inter=sum(max(0,min(y,v)-max(x,u)) for x,y in cyclic_parts(a,ra,g) for u,v in cyclic_parts(c,rb,g))
    return g*qa*qb+qa*rb+qb*ra+inter

def same_block_pairs(length,g):
    q,r=divmod(length,g)
    return g*q*(q-1)//2+r*q

@lru_cache(None)
def prob_float(L,K):
    a=np.arange(1,L+1)[:,None];b=np.arange(1,K+1)[None,:]
    return hypergeom.cdf(a-1,L+K,L,a+b-1)

@lru_cache(None)
def prob_exact(L,K,a,b):
    from math import comb
    z=a+b-1
    return Fraction(sum(comb(L,c)*comb(K,z-c) for c in range(max(0,z-K),min(a-1,L,z)+1)),comb(L+K,z))

def second_inversions(n,h,g,exact=False):
    bs=blocks(n,h);amount=[]
    for j,(a,b,L,k,r) in enumerate(bs):
        val=Fraction(same_block_pairs(b-a,g),2) if exact else .5*same_block_pairs(b-a,g)
        for c,d,K,l,s in bs[:j]:
            count=residue_pairs(c,d,a,b,g)
            if K==L and ((k-l)*h)%g==0:count-=r
            if count:
                prob=prob_exact(K,L,l+1,k+1) if exact else prob_float(K,L)[l,k]
                val+=count*prob
        amount.append(val)
    return bs,amount

def entropy_geom(mu):
    return (mu+1)*log(mu+1)-mu*log(mu) if mu>0 else 0.

def harmonic(n):
    if n<1000:return sum(1/i for i in range(1,n+1))
    from scipy.special import digamma
    return float(digamma(n+1)+np.euler_gamma)

def entropy_tail(H,r):
    if H<=r*log(2):return max(0.,H/log(2))
    def f(t):return r+(H+r*log(1-t))/log(1/t)
    res=minimize_scalar(lambda t:-f(t),bounds=(.50000001,.99999),method='bounded')
    return f(res.x)

def bound(n,h,g,p=8):
    bs,parts=second_inversions(n,h,g)
    a=b=E=H2=0.
    for (u,v,L,k,r),I in zip(bs,parts):
        w=(v-u)/n
        a+=w*((L-1)/4+1-harmonic(L)/L)
        b+=w*lgamma(L+1)/L
        E+=I/n
        H2+=w*entropy_geom(I/(v-u))
    q,r=divmod(n,g)
    T=h//gcd(h,g)
    fail=1-((g-r)*harmonic(min(q,T))+r*harmonic(min(q+1,T)))/n
    s=p-2
    Hremain=log(n)-1-b-H2
    raw=a+E+fail+entropy_tail(Hremain,s)
    Vmin=(s*n-(s-1)*g+s*(s-1)//2-1)/n
    return max(raw,a+E+fail+Vmin),dict(first=a,secondI=E,fail=fail,H1=b,H2=H2,Hremaining=Hremain,raw=raw)

if __name__=='__main__':
    n=10**9
    best=(1e100,None)
    for L in range(2,80):
        h=n//L
        for ratio in np.geomspace(1.00001,100,101):
            g=max(7,min(h-1,int(h/ratio)))
            val,detail=bound(n,h,g)
            if val<best[0]:best=(val,(h,g,L,ratio,detail))
    print('best sampled',best)
    for h,g in [(n//16,7),(n//16,n//16-1),(n//16,n//32),(n//16,n//64),(n//16,n//128),(n//24,n//48)]:
        print(h,g,bound(n,h,g))
