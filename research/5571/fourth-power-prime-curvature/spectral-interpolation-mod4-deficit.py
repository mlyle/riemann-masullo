"""Enclose the modulo-four first-prime fourth-power deficit using a verified zero height."""
import argparse
from math import isqrt
from flint import acb_series, arb, ctx, dirichlet_char


def primes_through(n):
    allowed = bytearray(b"\1") * (n + 1)
    allowed[0:2] = b"\0\0"
    for p in range(2, isqrt(n) + 1):
        if allowed[p]:
            size = (n - p * p) // p + 1
            allowed[p * p :: p] = b"\0" * size
    return [p for p in range(3, n + 1, 2) if allowed[p]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=128)
    parser.add_argument("--max-j", type=int, default=2100)
    args = parser.parse_args()
    assert args.precision >= 96 and args.max_j >= 4
    ctx.prec = args.precision
    chi = dirichlet_char(4, 3)
    beta = acb_series([1, 1], prec=2).dirichlet_l(chi)
    mass = (4 / arb.pi()).log() - arb.const_euler() + 2 * (beta[1] / beta[0]).real
    assert 0 < mass < arb("0.157")
    pending = [(arb(0), arb(6), 0)]
    verified_boxes = 0
    while pending:
        l, r, k = pending.pop()
        enclosure = chi.hardy_z(l.union(r))
        if enclosure.real > 0:
            verified_boxes += 1
            continue
        assert k < 30
        m = (l + r) / 2
        pending.extend([(l, m, k+1), (m, r, k+1)])
    edge = arb(61)/10
    assert chi.hardy_z(edge).real < 0
    mode = 1/((edge**2+arb(1)/4).sqrt() * (edge**2+arb(9)/4).sqrt() *
              (49+16*edge**2).sqrt())
    assert mode > arb("0.00102464")
    print("coefficient from a zero in (6,6.1)", mode)
    # The two symmetric off-line zeros share a height. Their mean growth
    # is bounded by (sqrt(x)+1/sqrt(x))/2 on the normalized Riesz scale.
    H = arb(25_000_000)
    tail = ((2*H/(arb.pi()*arb(1).exp())).log() + 2) / (arb.pi()*H)
    tail += (2*H.log() + arb(1)/2) / H**2
    # Residues of the kernel at zero and minus one.
    beta2 = acb_series([2, 1], prec=2).dirichlet_l(chi)
    a0 = (4/arb.pi()).log() - arb.const_euler() - arb(2).log() + (beta[1]/beta[0]).real
    a1 = (4/arb.pi()).log() - arb.const_euler() - arb(2).log() + 1 + (beta2[1]/beta2[0]).real
    print("bits, max-j, Hardy boxes", args.precision, args.max_j, verified_boxes)
    print("zero mass, tail, A(0), finite part A(-1)", mass, tail, a0, a1)
    cutoff = args.max_j**4
    powers = []
    for p in primes_through(args.max_j**2):
        v, sign, logp = p*p, (1 if p % 4 == 1 else -1), arb(p).log()
        coeff = logp
        while v <= cutoff:
            powers.append((v, coeff))
            v *= p
            coeff *= sign
    powers.sort(key=lambda pair: pair[0])
    first_primes = [(p, (1 if p % 4 == 1 else -1)*arb(p).log())
                    for p in primes_through(20**4)]
    a = b = arb(0)
    i = 0
    lower = upper = arb(0)
    worst_margin, worst_j, cum_worst, upper_j = arb(10), None, arb(0), None
    for j in range(1, args.max_j+1):
        x = j**4
        while i < len(powers) and powers[i][0] <= x:
            v, c = powers[i]
            a, b = a+c, b+v*c
            i += 1
        composite = x*a-b
        if j <= 20:
            exact = sum((x-p)*c for p,c in first_primes if p<=x)
            lo = hi = -arb(exact)
        else:
            # The residual -sum_{m>=1} x^{-2m}/((2m+1)2m) has magnitude <1.
            arch = a0*x + 1 + arb(x).log() - a1
            spread = mass + ((j*j)+arb(1)/(j*j))*tail/2
            lo = composite - arch - spread*j**6 - 1
            hi = composite - arch + spread*j**6 + 1
        if j >= 2:
            assert lo > 0, (j, lo/j**6, hi/j**6)
            margin = lo.lower()/j**6
            if margin < worst_margin:
                worst_margin, worst_j = margin, j
            lower += lo
            upper += hi
        cup = upper.upper()/j**7
        if cup > cum_worst:
            cum_worst, upper_j = cup, j
    print("worst individual certified -S/j^6 lower and index", worst_margin, worst_j)
    print("largest D(J)/J^7 upper and index", cum_worst, upper_j)
    assert worst_margin > arb("0.0174") and cum_worst < arb("0.173")
    print("endpoint deficit/J^7 lower, upper", lower/args.max_j**7, upper/args.max_j**7)
    print("GRH cumulative asymptotic margin", arb(2)/21 - mass/25, arb(2)/21 + mass/25)


if __name__ == "__main__":
    main()
