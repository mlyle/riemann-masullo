"""Verify the rational principal-character finite fourth-power deficit bounds."""
import argparse
from math import factorial
from flint import acb_series, arb, ctx
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args=parser.parse_args()
    assert args.precision>=96
    ctx.prec=args.precision
    path=Path(__file__).with_name("spectral-interpolation-mod4-deficit.py")
    spec=spec_from_file_location("modfour",path)
    mod=module_from_spec(spec)
    spec.loader.exec_module(mod)
    h=arb(3_000_000_000_000)
    a=h-arb(1)/2
    z0=acb_series([0,1],prec=2).zeta()
    zm=acb_series([-1,1],prec=2).zeta()
    residue0=-(z0[1]/z0[0]).real
    residuem=(zm[1]/zm[0]).real
    assert abs(residue0)<2 and abs(residuem)<2
    mass=2+arb.const_euler()-(4*arb.pi()).log()
    k=((h/(2*arb.pi()*arb(1).exp())).log()+2)/(arb.pi()*h)
    k+=(2*h.log()+arb(1)/2)/h**2
    limit=1000
    primes=[2]+mod.primes_through(limit**2)
    powers=[]
    for p in primes:
        v=p*p
        logp=arb(p).log()
        while v<=limit**4:
            powers.append((v,logp)); v*=p
    powers.sort(key=lambda x:x[0])
    a0=a1=arb(0)
    index=0
    upper=arb(0)
    small_max=arb(0)
    for j in range(1,limit+1):
        x=j**4
        while index<len(powers) and powers[index][0]<=x:
            v,c=powers[index]
            a0+=c; a1+=v*c; index+=1
        if j<=10:
            y=arb(x)**2/2-sum((x-p)*arb(p).log() for p in primes if p<=x)
        else:
            y=x*a0-a1-residue0*x-residuem+1+mass*j**6+(arb(j*j)+1/arb(j*j))*k*j**6/2
        if y>0: upper+=y
        else: assert y<=0
        if upper.upper()/j**7>small_max: small_max=upper.upper()/j**7
    print("bits, zero mass, high tail, arch constants", args.precision,mass,k,residue0,residuem)
    print("small max and endpoint",small_max,upper/limit**7)
    assert small_max<1 and upper/limit**7<arb("0.12")
    # The pointwise comparison with high frequencies added absolutely covers
    # J=1001,...,2100, and in fact much higher, without any new prime sieve.
    x0=arb(limit)**4
    proper=arb("1.01624")*(arb(2)/3+x0**(-arb(1)/6)+x0.log()/arb(2).log()/x0**(arb(1)/4))
    assert (proper+mass+3/arb(limit)**2+(arb(2100)**2+1)*k/2)*(arb(1)/7+1/arb(limit)) + arb("0.12")<1
    scale=arb(2100)
    base=arb("0.12")*(limit/scale)**7 +(mass+k+proper+3/arb(limit)**2)*(arb(1)/7+1/scale)
    def energy(power,order):
        maxterm=(arb(order)/(power*arb(1).exp()))**(2*order) if order else arb(1)
        return arb(factorial(2*order))/(2*power+1)**(2*order+1)+2*maxterm/scale
    def norm(power,order):
        v,d=energy(power,order),energy(power,order+1)
        return (v+4*(v*d).sqrt()).sqrt()
    f=norm(8,0)+2*norm(6,1)
    def bound(j):
        j=arb(j)
        v=(a.log()+1)/a+(a.log()/a**2)*j*(1+j.log())
        return base+j*j.sqrt()*(k*arb("0.39")*v).sqrt()*f
    print("large-J baseline, energy",base,f)
    for j in (1000000,10000000,50000000,75000000,80000000):
        print(j,bound(j))
    assert bound(75_000_000)<1


if __name__=="__main__":
    main()
