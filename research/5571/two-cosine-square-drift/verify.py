"""Enclose zeta at half-line ordinates in the finite two-frequency difference grid."""
import argparse

from flint import acb, arb, ctx
import flint


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--size", type=int, default=64)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.size >= 2 and args.precision >= 64
    ctx.prec = args.precision
    half = arb(1) / 2
    root = arb(2).sqrt()
    n = args.size

    # The difference of two grid frequencies has coordinates in [1-n,n-1]^2.
    # The five shifts are contained in the larger square [-n,n]^2.
    # Conjugation reduces the signed square to a half-square and its center.
    lower = arb(10)
    count = 0
    for k in range(n + 1):
        start = 0 if k == 0 else -n
        for ell in range(start, n + 1):
            ordinate = k + ell * root
            value = abs(acb(half, ordinate).zeta())
            assert value.is_finite() and value > 0, (k, ell, value)
            lower = lower.min(value.lower())
            count += 1

    assert count == ((2 * n + 1) ** 2 + 1) // 2
    bound = 2 + 2 * (arb.pi() / (n + 1)).cos() * (1 / (2 * arb(5).sqrt()) + arb(1) / 6)
    print("python-flint", flint.__version__, "precision", ctx.prec, "grid", n)
    print("half-square certified points", count)
    print("minimum certified |zeta| lower bound", lower)
    print("endpoint drift constant", bound)


if __name__ == "__main__":
    main()
