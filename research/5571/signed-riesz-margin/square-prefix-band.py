"""Uniform interval proof for the physical square-prefix statistic on a million integer cutoffs."""
import argparse
from math import isqrt
import flint
from flint import arb, ctx


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    args = parser.parse_args()
    assert args.precision >= 64
    ctx.prec = args.precision
    start, end, step = 10_000_000, 11_000_000, 1_000
    assert (end - start) % step == 0 and step % 2 == 0
    assert 10**14 <= start**2 <= end**2 <= 10**16
    D = 1 + arb(2).sqrt()
    # For real y below 599, theta(y) <= 2y follows from these integer upper sums.
    prime_log_bound = 0
    for n in range(1, 600):
        if n >= 2 and all(n % d for d in range(2, isqrt(n)+1)):
            prime_log_bound += n.bit_length()
        assert prime_log_bound <= 2*n
    norm_upper = arb(-10)
    for lo in range(start, end, step):
        # A ball with exact integer midpoint and radius covers every real point of the cell.
        K = arb(lo + step//2, step//2)
        u = 2*K.log()
        mean = 2 - sum((((t*u).cos()+t*(t*u).sin())/(1+t*t)
                        for t in (arb(1), arb(2).sqrt())), arb(0))
        norm_upper = max(norm_upper, mean.upper())
    # The E bound follows by partial summation and Johnston's finite theta estimate.
    logarithm = 2*arb(end).log()
    error = ((4+2*D)*end*logarithm**2/(8*arb.pi()) + 598*D)/start**2
    saw = (8+4*D)/(8*start)
    discrete = D*logarithm/start
    # finite-riesz.py certifies B_(1/2)(K^2)/K^2 < -0.5651 on the enclosing range.
    integral_margin = arb("0.5651") - norm_upper/2 - error - saw
    discrete_margin = integral_margin - discrete
    print("python-flint", flint.__version__, "precision", ctx.prec)
    print("inclusive integer endpoints", start, end, "enclosing cells", (end-start)//step)
    print("uniform normalized density upper bound", norm_upper)
    print("normalized first-prime error bound", error)
    print("continuous saw contribution", saw, "discrete extra cost", discrete)
    print("integral-mean strict negativity margin", integral_margin)
    print("discrete-mean strict negativity margin", discrete_margin)
    assert integral_margin > arb("0.0843") and discrete_margin > arb("0.0843")


if __name__ == "__main__":
    main()
