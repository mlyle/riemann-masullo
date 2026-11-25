"""Arithmetic smoothing of the triangular prime sum with a mean-one lognormal factor."""
import argparse
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from flint import arb, ctx


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--precision",type=int,default=128)
    opt=ap.parse_args()
    assert opt.precision>=96
    ctx.prec=opt.precision
    path=Path(__file__).with_name("spectral-interpolation-rational-deficit-density.py")
    spec=spec_from_file_location("density",path)
    density=module_from_spec(spec)
    spec.loader.exec_module(density)
    for char,h,b,ends in [("mod4",25_000_000,"0.155568",[16_000_000]),
                          ("zeta",3_000_000_000_000,"0.046192",[1_750_000_000_000])]:
        j0=arb(150_000 if char=="mod4" else 20_000_000_000)
        small=arb(10_000 if char=="mod4" else 10_000_000)
        x0=small**4
        q=4 if char=="mod4" else 1
        phi=2 if char=="mod4" else 1
        pole=0 if char=="mod4" else 1
        kh=((arb(4 if char=="mod4" else 1)*h/(2*arb.pi()*arb(1).exp())).log()+2)/(arb.pi()*h)
        kh+=(2*arb(h).log()+arb(1)/2)/arb(h)**2
        print("bits, character",opt.precision,char)
        for end in ends:
            j=arb(end)
            high,raw=density.check(char,h,0,[end],False)
            best=arb(1000000)
            best_raw=arb(1000000)
            for ci in range(50,371):
                c=arb(ci)/100
                v0=(c/j0)**2
                # A uniform upper on E(Y-1)^2 and the mixed third moment.
                assert v0<arb("0.00001") and (v0+v0**2/4).sqrt()<arb("0.001")
                assert v0.exp()<arb("1.00001") and (6*v0).exp()<arb("1.0001")
                assert 108*v0*(6*v0).exp()+6*v0.exp()<8
                moments=(arb("1.00001")+3*v0.sqrt()/x0.log())
                # Earlier small prefix, lower arch terms, composite powers, and central zeros.
                initial=(small/j0)**7
                base=initial+(arb("0.729")+arb(b))*(3*v0/8).exp()*(arb(1)/7+1/j0)
                base+=kh*v0.exp()*(arb(1)/7+1/j0)
                base+=arb(4_000_004)*(arb(1)/5+1/j0)/j0**2+8/j0**6
                alpha=arb(2)/3
                # The low-truncation curvature and known main-term correction.
                curvature=(arb(4)*j0.log()+arb("0.001"))*(1/(8*alpha+1)+1/j0)*j0**(8*alpha-6)/2
                bt=1/(phi*(alpha-arb(q).log()/x0.log()))
                curvature+=(bt*moments-arb(pole)/2)*c*c*(arb(1)/9+1/j0)
                damp=(v0-c*c*h*h/(2*j*j)).exp()
                upper=base+curvature+high*damp
                naive=base+curvature+raw*damp
                if upper<best:
                    best=upper; bc=ci
                if naive<best_raw:
                    best_raw=naive;br=ci
            print(end,best,"100*c",bc,"absolute-only",best_raw,"100*c",br)
            assert best < 1 and best_raw > 1


if __name__=="__main__":
    main()
