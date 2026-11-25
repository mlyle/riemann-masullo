"""Certified upper count for the union of nonnegative physical square prefixes."""
import argparse
import flint
from flint import acb, acb_series, arb, ctx


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--precision", type=int, default=128)
    precision = args.parse_args().precision
    assert precision >= 96
    ctx.prec = precision
    H = arb(3)*10**12
    left = 3*10**13
    J = arb(left)
    two, root = arb(2), arb(2).sqrt()
    D, alpha, half = 1+root, arb(1)/2, arb(1)/2
    pi, ell = arb.pi(), (4*H).log()
    # Hasanalizade--Shen--Wong Cor. 1.2. For all T>=H the ratios
    # log(log(4T))/log(4T) and 1/log(4T) decrease.
    R = arb("0.1038") + arb("0.2573")*ell.log()/ell + arb("9.3675")/ell
    assert R < arb("0.46")
    # Endpoints of a zero subinterval of length one lie between H-2 and 4T.
    # One may enlarge it by 1/10 on each side when counting boundary zeros.
    unit = arb("1.2")/(2*pi) + 2*R
    assert unit < arb("1.25")
    total = 2/pi + 2*R/H
    assert total < arb("0.7")
    # Sum the two unit bins at each integer distance. The tail from m=2
    # has ratio at most exp(-5).
    gaussian_bins = 2*(1+(-arb(1)).exp()+(-arb(4)).exp()/(1-(-arb(5)).exp()))
    assert arb("1.25")*gaussian_bins < arb("3.5")
    ratio = 1/(two*root)
    shell_sum = 1/(1-ratio) + two.log()/ell*ratio/(1-ratio)**2
    gram = 2*(two.log()**2).exp()*pi.sqrt()*arb(1).exp()*arb("3.5")*arb("0.7")
    rms_constant = 4*alpha*gram.sqrt()*shell_sum/(1-root/H)**2
    rms = rms_constant * J*ell/H**arb("1.5")
    # Competing deterministic terms on the full band, with actual critical
    # ordinates below H bounded by the reciprocal-square Hadamard mass.
    Z = 2+arb.const_euler()-(4*pi).log()
    assert acb.zeta_zero(1).imag > 14
    low = 4*alpha*Z/(1-root/14)**2
    low_endpoint = arb(4)
    for t, abs_c in ((arb(0),arb(2)),(arb(1),arb(1)),(root,arb(1))):
        for x in (arb(0),-alpha):
            z = acb_series([acb(x,-t),1]).zeta()
            low_endpoint += abs_c*abs(z[1]/z[0])
    xlo, xhi = J**2, (2*J)**2
    assert 2*J < arb("1.101e26") and xhi < arb("2.165e30")
    # Johnston Cor. 3.3 for the square-prime replacement and Table 2 line a=1
    # for the genuine prime endpoint and its unit-k transfer.
    square_err=(2*D+8*alpha)*(598/J+J.log()**2/(4*pi*J.sqrt()))
    residues=(low_endpoint+4+4*alpha/(xlo**2-1))/J
    Eerr=((4+2*D)*xhi.log()**2/J + 2*D/xlo)
    mesherr=( (8+4*D)/8+D*xhi.log() )/J
    # Cover every real u in [J,2J] by exact integer balls.
    nboxes, step=4000,left//4000
    assert step*nboxes==left and step%2==0
    phase_upper=arb(-2)
    for j in range(nboxes):
        u=arb(left+j*step+step//2, step//2)
        y=2*u.log()
        phase=-sum(( (acb(0,t)*acb(0,t*y).exp()/(acb(1,t)*acb(1,2*t))).real
                    for t in (arb(1),root)),arb(0))
        phase_upper=max(phase_upper,phase.upper())
    threshold=-phase_upper-low-square_err-residues-2*Eerr-mesherr
    assert threshold > arb("0.215")
    frac=(rms/threshold)**2
    assert frac<arb("0.00025")
    # Counting includes all earlier positive prefixes, even if every one is positive.
    assert (1+frac)*J < (arb(58)*10**12)**(arb(49)/50)
    print("python-flint",flint.__version__,"precision",ctx.prec,"H",H,"J",J,"boxes",nboxes)
    print("zero count remainder ratio",R,"unit bin coefficient",unit,"two-sign shell count coefficient",total)
    print("discrete sign transfer via continuous RMS; dyadic norm constant",rms_constant,"absolute RMS",rms)
    print("phase upper",phase_upper,"critical zero cost",low,"square PNT cost",square_err)
    print("Riesz endpoint and missing square integral",residues,"endpoint E relative cost",Eerr,"other unit transfer cost",mesherr)
    print("strict threshold",threshold,"nonnegative union fraction at most",frac)
    print("prefix exponent 49/50 at every terminal from 58000000000000 through 60000000000000")


if __name__=="__main__":
    main()
