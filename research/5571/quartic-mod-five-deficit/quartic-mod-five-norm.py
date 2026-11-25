"""Enclose the sum of complex Riesz norms, allowing a different phase at every sample."""
from argparse import ArgumentParser
from fractions import Fraction
from math import isqrt
from pathlib import Path
from flint import acb_series, arb, ctx, dirichlet_char

def direct(audit_initial):
    root=Path(__file__).resolve().parent
    data=[tuple(map(int,r.split())) for r in (root/'complex-grid-256.txt').read_text().splitlines()]
    real=[tuple(map(int,r.split())) for r in (root/'grid-256.txt').read_text().splitlines()]
    assert len(data)==len(real)==256
    total=0
    peak=Fraction(0)
    for expected,row in enumerate(data,1):
        j,l,h,li,hi=row
        assert j==expected and l<=h and li<=hi and (j,l,h)==real[j-1]
        squared=max(l*l,h*h)+max(li*li,hi*hi)
        top=isqrt(squared)
        total+=top+(top*top<squared)
        peak=max(peak,Fraction(total,(1<<30)*j**7))
    print("direct all-prefix upper through 256",peak)
    assert peak < Fraction(103,1000)

    if audit_initial:
        from decimal import Decimal, localcontext
        n=audit_initial**4
        flags=bytearray([1])*(n+1)
        flags[:2]=bytes(2)
        for p in range(2,isqrt(n)+1):
            if flags[p]:
                flags[p*p::p]=bytes((n-p*p)//p+1)
        with localcontext() as dc:
            dc.prec=45
            sums=[Decimal(0),Decimal(0)]
            weighted=[Decimal(0),Decimal(0)]
            p=2
            for j,l,h,li,hi in data[:audit_initial]:
                x=j**4
                while p<=x:
                    r=p%5
                    if flags[p] and r:
                        k=int(r in (2,3))
                        w=dc.ln(Decimal(p))*(1 if r in (1,2) else -1)
                        sums[k]+=w
                        weighted[k]+=p*w
                    p+=1
                for k,left,right in ((0,l,h),(1,li,hi)):
                    projected=x*sums[k]-weighted[k]
                    if left or right or projected:
                        assert Decimal(left)/(1<<30)<projected-Decimal('1e-24')
                        assert projected+Decimal('1e-24')<Decimal(right)/(1<<30)
        print("independent complex samples through",audit_initial)

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--bits",type=int,default=128)
    ap.add_argument("--audit-initial",type=int,default=0)
    opt=ap.parse_args()
    assert 0 <= opt.audit_initial <= 32
    assert opt.bits>=96
    ctx.prec=opt.bits
    direct(opt.audit_initial)
    chi=dirichlet_char(5,2)
    def ld(s):
        z=acb_series([s,1],prec=2).dirichlet_l(chi)
        return (z[1]/z[0]).conjugate()
    L=(arb(5)/arb.pi()).log()-arb.const_euler()
    B=L+2*ld(1).real
    assert 0<B<arb("0.204")
    assert abs(L-arb(2).log()+ld(1))<1 and abs(L-arb(2).log()+1+ld(2))<1
    assert (arb(2)/3)*arb(4).log()<1 and arb(4).log()*(1+12/(arb(1).exp()*arb(2).log()))<11
    H=arb(20_000_000)
    for start,end,width,bt in [(256,100000,"0.6",False),(100000,8000000,"3.45",True)]:
        N,J,c=arb(start),arb(end),arb(width)
        v0=(c/N)**2
        def P(a):
            return 1/(arb(a)+1)+1/N
        assert 108*v0*(6*v0).exp()+6*v0.exp()<8 and v0.exp()<arb("1.0001")
        assert (arb("1.0001")*(1+v0/4)).sqrt()<arb("1.01") and 2*(1+v0/4).sqrt()<3
        base=(1+B)*(3*v0/8).exp()*P(6)+11*(2*v0/9).exp()*N**(-arb(2)/3)*P(arb(16)/3)
        base+=4*P(4)/N**2+8/N**6
        high=2*B*(v0-(c*H/J)**2/2).exp()*J**2*P(8)
        if bt:
            m=arb(5000)
            assert 256 <= m <= N
            base+=(m/N)**7
            alpha=arb(2)/3
            lx0=4*m.log()
            assert ((alpha*lx0).exp()-1) > 5*arb(1).exp()
            assert (8*alpha-6)*(4*N.log())+4<0
            assert (v0+v0**2/4).sqrt()<arb("0.001")
            first=(4*N.log()+arb("0.001"))/2*P(8*alpha)*N**(8*alpha-6)
            second=(arb("1.0001")+3*v0.sqrt()/lx0)*c*c*P(8)/(4*(alpha-arb(5).log()/lx0))
            kink=arb(2).sqrt()*(first+second)
        else:
            kink=arb(2).sqrt()*((4*J.log()*arb("1.0001")+3*c/N)*c*c*P(8)/10+
                                 arb("1.01")*(4*J.log()+c/N)*c*P(4)/N**3)
        print("bits, range, width, base, high zeros, curvature, total")
        print(opt.bits,start,end,width,base,high,kink,base+high+kink)
        assert base+high+kink<(arb("0.930294") if bt else arb("0.490482"))

if __name__=='__main__':
    main()
