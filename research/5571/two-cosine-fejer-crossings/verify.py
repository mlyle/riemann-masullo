"""Rigorous Fejer values for the two-cosine first-prime Mellin residues."""
import argparse
import flint
from flint import acb, arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    a, root, T = arb(1)/2, arb(2).sqrt(), arb(200)
    shifts = [(arb(0), arb(2)), (arb(1), -a), (-arb(1), -a),
              (root, -a), (-root, -a)]
    poles = []
    n = 1
    last = arb(0)
    while True:
        z = acb.zeta_zero(n)
        assert z.real == a and z.imag > last
        gamma = z.imag
        last = gamma
        if gamma > T + root:
            break
        assert gamma < T + root
        for g in (gamma, -gamma):
            for t, c in shifts:
                v = g + t
                if abs(v) < T:
                    poles.append((v, -c / acb(a, v)))
                else:
                    assert abs(v) > T
        n += 1
    for t, c in shifts:
        poles.append((t, -c / (2 * acb(a, t))))
    print("python-flint", flint.__version__, "precision", ctx.prec, "T", T)
    print("included indexed zeros", n-1, "first excluded zero", n, last)
    print("in-band pole contributions counted with multiplicity", len(poles))
    for numerator, sign, threshold in ((3005769, 1, "0.199"), (1423955, -1, "4.648")):
        y = arb(numerator)/1000
        result = sum((R * (1 - abs(v)/T) * acb(0, v*y).exp()
                      for v, R in poles), acb(0))
        assert result.imag.contains(0)
        assert sign * result.real > arb(threshold)
        print("y", numerator, "/ 1000", "Fejer polynomial", result.real)


if __name__ == "__main__":
    main()
