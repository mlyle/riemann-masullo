"""Enclose both exact signed square-cutoff first-prime prefixes by sieving all integers."""
import argparse
from math import isqrt
import flint
from flint import acb, arb, ctx


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision",type=int,default=128)
    parser.add_argument("--K",type=int,default=512)
    args=parser.parse_args()
    assert args.precision>=64 and args.K>=20
    ctx.prec=args.precision
    root=arb(2).sqrt()
    nmax=args.K**2
    primes=bytearray([1])*(nmax+1)
    primes[:2]=bytes(2)
    for p in range(2,isqrt(nmax)+1):
        if primes[p]:
            primes[p*p:nmax+1:p]=bytes((nmax-p*p)//p+1)
    pcount=sum(primes)
    weighted=arb(0)
    discrete_mean=arb(0)
    discrete_prefix=arb(0)
    integral_prefix=arb(0)
    maxd,maxc=arb(-100),arb(-100)
    k=1
    for n in range(1,nmax+1):
        t=arb(n).log()
        weight=2-t.cos()-(root*t).cos()
        if primes[n]:
            weighted+=t*weight
        discrete_mean+=weight
        if n==k*k:
            density=2*(n-1)-sum(((n*acb(0,v*t).exp()-1)/acb(1,v)).real for v in (arb(1),root))
            discrete_prefix+=weighted-discrete_mean
            integral_prefix+=weighted-density
            if k>=20:
                maxd=maxd.max((discrete_prefix/(k*k)).upper())
                maxc=maxc.max((integral_prefix/(k*k)).upper())
            k+=1
    assert k==args.K+1
    print("python-flint",flint.__version__,"precision",ctx.prec,"last K",args.K,
          "sieved through",nmax,"prime count",pcount)
    print("upper bound for maximum A_integral(K)/K^2, 20<=K<=last",maxc)
    print("upper bound for maximum A_discrete(K)/K^2, 20<=K<=last",maxd)
    assert maxc < 0 and maxd < 0


if __name__=="__main__":
    main()
