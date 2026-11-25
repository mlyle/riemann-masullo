"""Enclose the signed prime-square and absolute zeta-zero constants for two Riesz means."""
import argparse
import flint
from flint import acb, arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    a = arb(1) / 2
    root = arb(2).sqrt()
    first = acb.zeta_zero(1)
    assert first.real == a and first.imag > 14
    hadamard = 2 + arb.const_euler() - (4 * arb.pi()).log()
    factor = 4 * hadamard / (1 - root/14)**2
    print("python-flint", flint.__version__, "precision", ctx.prec)
    print("lowest zeta ordinate", first.imag)
    print("Hadamard reciprocal-square mass under RH", hadamard)
    for alpha, margin in ((arb(1), "0.69"), (a, "0.63")):
        drift = 2*alpha/(a+alpha)
        rotating = sum((alpha / (abs(acb(1, 2*t)) * abs(acb(a+alpha, t)))
                        for t in [arb(1), root]), arb(0))
        spectrum = alpha * factor
        D = drift - rotating - spectrum
        print("alpha", alpha, "drift", drift, "rotating", rotating, "zeros", spectrum)
        print("strict upper margin", D, "absolute upper envelope", drift + rotating + spectrum)
        assert D > arb(margin)


if __name__ == "__main__":
    main()
