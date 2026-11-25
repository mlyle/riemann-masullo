"""Ramaré density plus the actual clipped fourth-power phases in fixed abscissa bands."""
from argparse import ArgumentParser
from math import factorial
from flint import arb, ctx


def check(name, H, baseline, indices, verbose=True):
    h, j0 = arb(H), arb(2100)
    m = 4 if name=="mod4" else 1
    kh = ((m*h/(2*arb.pi()*arb(1).exp())).log()+2)/(arb.pi()*h)
    kh += (2*h.log()+arb(1)/2)/h**2
    ha = h-arb(1)/2
    def energy(p,k):
        m=(arb(k)/(p*arb(1).exp()))**(2*k) if k else arb(1)
        return arb(factorial(2*k))/(2*p+1)**(2*k+1)+2*m/j0
    def norm(p,k):
        e,d=energy(p,k),energy(p,k+1)
        return (e+4*(e*d).sqrt()).sqrt()
    def weighted_count(a,d,b):
        r=(b*h).log()
        assert 2-a-d/r>0
        return h**(a-2)*r**d/(2-a-d/r)
    def upper_tail(l):
        if l<arb("0.52"): return kh/4
        r=1-l
        if m==1:
            a=8*r/3
            c=arb("9.8")*arb(3)**a*weighted_count(a,5-2*l,1)+103*weighted_count(0,2,1)
        else:
            a=3*r
            c=10*arb(56*10**5)**r*weighted_count(a,5-2*l,100)+1600*weighted_count(0,2,100)
        return c.min(kh/4)
    if verbose: print(name,"abscissa mesh 0.5, 0.625, then steps of 0.001 through 1")
    # Layer-cake in beta before imposing the common mask. Every mesh comparison
    # is increasing in the sample cutoff. The initial constant uses absolute sums.
    cuts=[500]+list(range(625,1001))
    specs=[]
    for q,r in zip(cuts,cuts[1:]):
        l,u=arb(q)/1000,arb(r)/1000
        tail=upper_tail(l)
        specs.append((l,u,tail,norm(4+4*l,0)))
    for end in indices:
        j=arb(end)
        v=(ha.log()+1)/ha+j*(1+j.log())*ha.log()/ha**2
        amount=direct_total=arb(baseline)+2*upper_tail(arb(1)/2)*(arb(1)/7+1/j0)
        for l,u,tail,nrm in specs:
            ms=2*(tail*arb("0.39")*v).sqrt()*nrm*(
                j**(4*u-arb(5)/2)-j**(4*l-arb(5)/2))
            direct=2*tail*(1/(5+4*l)+1/j0)*(j**(4*u-2)-j**(4*l-2))
            amount+=ms.min(direct)
            direct_total+=direct
        if verbose: print(end,amount,"absolute-only",direct_total)
    return amount, direct_total


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument("--precision",type=int,default=128)
    opts=p.parse_args()
    assert opts.precision>=96
    ctx.prec=opts.precision
    print("bits",ctx.prec)
    m, raw_m = check("mod4",25_000_000,"0.127630",[100000,150000])
    assert m < arb("0.891") and raw_m > 15
    z, raw_z = check("zeta",3_000_000_000_000,"0.111658",[10_000_000_000,20_000_000_000])
    assert z < arb("0.912") and raw_z >14


if __name__=="__main__":
    main()
