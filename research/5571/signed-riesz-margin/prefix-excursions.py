"""Certify low shifted zeros avoid the Fejer frequencies and enclose the two Riesz excursions."""
import argparse
import flint
from flint import acb, arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    degree = 128
    root, half = arb(2).sqrt(), arb(1)/2
    max_height = degree*(1+root)+root
    multiples = [m*root for m in range(-degree-1, degree+2)]
    gap = arb(1)
    k = 1
    while True:
        gamma = acb.zeta_zero(k).imag
        if gamma > max_height:
            break
        assert gamma < max_height
        for v in multiples:
            u = gamma-v
            candidate = round(float(u.mid()))
            distance = abs(u-candidate)
            # Strictly nearest integer is verified, so this accounts for every integer.
            assert distance < half
            gap = min(gap, distance.lower())
        k += 1
    assert gap > arb("1e-8")
    print("python-flint", flint.__version__, "precision", ctx.prec, "degree", degree)
    print("height bound", max_height, "number of positive zeros through the bound", k-1)
    print("first excluded ordinate", gamma, "certified distance from resonances", gap)
    for alpha in [arb(1), half]:
        drift = 2*alpha/(half+alpha)
        amplitude = sum((alpha/(abs(acb(1,2*t))*abs(acb(half+alpha,t)))
                         for t in (arb(1),root)), arb(0))
        offset = degree*amplitude/(degree+1)
        print("alpha", alpha, "liminf at most", -drift-offset, "limsup at least", -drift+offset)


if __name__ == "__main__":
    main()
