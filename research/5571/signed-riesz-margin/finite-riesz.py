"""Certify unconditional finite-range Riesz sign margins with verified low zeta zeros."""
import argparse
import flint
from flint import acb, acb_series, arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    a, root, H = arb(1)/2, arb(2).sqrt(), arb(3)*10**12
    Z = 2 + arb.const_euler() - (4*arb.pi()).log()
    assert acb.zeta_zero(1).imag > 14
    print("python-flint", flint.__version__, "precision", ctx.prec, "H", H)
    for alpha in [arb(1),a]:
        drift = 2*alpha/(a+alpha)
        low = 4*alpha*Z/(1-root/14)**2
        swing = sum((alpha/(abs(acb(1,2*t))*abs(acb(a+alpha,t))) for t in [arb(1),root]),arb(0))
        # Finite kernel residues at z=0 and z=-alpha, and the missing density integral [0,1].
        low_endpoint = arb(4)
        for t, abs_c in [(arb(0),arb(2)),(arb(1),arb(1)),(root,arb(1))]:
            for x in [arb(0),-alpha]:
                zj=acb_series([acb(x,-t),1]).zeta()
                low_endpoint += abs_c*abs(zj[1]/zj[0])
        D=2*(1+root)+8*alpha
        for lo,hi,goal in [(10**10,10**18,"0.02"),(10**14,10**16,"0.55")]:
            Ymin=arb(lo).sqrt()
            Ymax=arb(hi).sqrt()
            assert Ymin > arb(4).exp() and Ymax <= arb("1.101e26")
            high=16*alpha*Ymax*(H.log()+1)/(H*(1-root/H)**2)
            square_count = D * (598/Ymin+Ymin.log()**2/(4*arb.pi()*Ymin.sqrt()))
            # Missing interval [0,1] in the square integral, and all trivial-zero residues.
            constants=(low_endpoint + 4 + 4*alpha/(arb(lo)**2-1))/Ymin
            gap=drift-low-swing-high-square_count-constants
            print("alpha",alpha,"X from",lo,"to",hi)
            print("low",low,"swing",swing,"upper-zero tail",high,
                  "square PNT remainder",square_count,"endpoint cost",constants)
            print("uniform strict negativity margin",gap)
            assert gap>arb(goal)


if __name__=="__main__":
    main()
