"""Certify the isolated first zeta pole for the exact two-cosine prime-power count."""
import argparse
import flint
from flint import acb, arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    rho = acb.zeta_zero(1)
    assert rho.real == arb(1) / 2 and 14 < rho.imag < 15
    print("python-flint", flint.__version__, "precision", ctx.prec)
    print("first zeta zero", rho)
    for shift in [arb(1), arb(-1), arb(2).sqrt(), -arb(2).sqrt()]:
        absolute = abs(acb(rho.real, rho.imag - shift).zeta())
        assert absolute > 0
        print("shift", shift, "absolute zeta", absolute)
    amplitude = 2 / abs(rho)
    assert amplitude > arb("0.1414")
    print("symmetric excursion constant at least", amplitude)


if __name__ == "__main__":
    main()
