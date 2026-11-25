"""Outward-rounded ledger for the unrestricted mod-5 quartic prime deficit."""
from argparse import ArgumentParser
from flint import acb_series, arb, ctx, dirichlet_char

def certify(bits):
    ctx.prec = bits
    chi=dirichlet_char(5,2)
    assert chi(2).imag == 1
    def dlog(s):
        z=acb_series([s,1],prec=2).dirichlet_l(chi)
        return (z[1]/z[0]).real
    L=(arb(5)/arb.pi()).log()-arb.const_euler()
    mass=L+2*dlog(1)
    a0=L-arb(2).log()+dlog(1)
    a1=L-arb(2).log()+1+dlog(2)
    assert 0<mass<arb("0.204") and abs(a0)<1 and abs(a1)<1
    # Bound every log-weighted proper prime power, with y^(4/3) handling k>=3.
    assert arb(2)/3*arb(4).log()<1
    assert arb(4).log()*(1+12/(arb(1).exp()*arb(2).log()))<11
    N, J, H = arb(256), arb(2_500_000), arb(20_000_000)
    v0=1/N**2
    # E[(Y-1)^4] <= 4 v^2 via the second derivative of exp(6v)-4exp(3v)+6exp(v)-3.
    assert 108*v0*(6*v0).exp()+6*v0.exp()<8
    assert v0.exp()<arb("1.0001")
    # Bounds for E|Y-1| |log Y| and E (Y-1)^2 |log Y| by Cauchy-Schwarz.
    assert (arb("1.0001")*(1+v0/4)).sqrt()<arb("1.01")
    assert 2*(1+v0/4).sqrt()<3
    def P(a):
        return 1/(a+1)+1/N
    a=arb(4)/3
    low=(1+mass)*(3*v0/8).exp()*P(arb(6))
    proper=11*(2*v0/9).exp()*N**(-arb(2)/3)*P(4*a)
    affine=4*P(arb(4))/N**2+8/N**6
    high=2*mass*(v0-H**2/(2*J**2)).exp()*J**2*P(arb(8))
    # Length d in one positive residue class costs at most d^2/10+d in tent weight.
    curvature=(4*J.log()*arb("1.0001")+3/N)/10*P(arb(8))
    curvature+=arb("1.01")*(4*J.log()+1/N)*P(arb(4))/N**3
    bound=low+proper+affine+high+curvature
    print("precision",bits,"character modulus 5 with chi(2)=i")
    print("B, Re a0, Re a1",mass,a0,a1)
    print("low and squares, remaining powers, affine, high, positive prime kinks")
    print(low,proper,affine,high,curvature)
    print("uniform normalized upper, J=256..2500000",bound)
    assert bound<arb("0.902417")

if __name__=="__main__":
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--bits",type=int,default=128)
    bits=ap.parse_args().bits
    assert bits>=96
    certify(bits)
