"""Explicit high-zero mean-square bound for the clipped modulo-four fourth-power Riesz deficit."""
import argparse
from math import factorial
from flint import arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 96
    ctx.prec = args.precision
    h = arb(25_000_000)
    a = h-arb(1)/2
    scale = arb(2100)
    mass = arb("0.155568")
    k = ((2*h/(arb.pi()*arb(1).exp())).log()+2)/(arb.pi()*h)
    k += (2*h.log()+arb(1)/2)/h**2
    x0 = arb(1000)**4
    proper = arb("1.01624")*(arb(2)/3+x0**(-arb(1)/6)+x0.log()/arb(2).log()/x0**(arb(1)/4))
    base = arb("0.173")*(1000/scale)**7 + (
        mass + k + proper + arb(2)/1_000_000)*(arb(1)/7 + 1/scale)
    def energy(power, order):
        sup = ((arb(order)/(power*arb(1).exp()))**(2*order) if order else arb(1))
        return arb(factorial(2*order))/(2*power+1)**(2*order+1) + 2*sup/scale
    def norm(power, order):
        e, d = energy(power, order), energy(power, order+1)
        return (e+4*(e*d).sqrt()).sqrt()
    f = norm(8,0) + 2*norm(6,1)
    def bound(j):
        j = arb(j)
        v = (a.log()+1)/a + (a.log()/a**2)*j*(1+j.log())
        return base+j*j.sqrt()*(k*arb("0.39")*v).sqrt()*f
    print("bits, known-Dirichlet-zero-height, proper-power coefficient, cumulative baseline",
          args.precision,h,proper,base)
    print("square-mean coefficient factor", f)
    for j in (5000, 7000, 10000, 20000, 40000, 44000):
        print(j, bound(j))
    assert bound(5000)<arb("0.173") and bound(10000)<arb("0.23")
    assert bound(44000)<1 and bound(10000)<arb("0.221")


if __name__ == "__main__":
    main()
