"""An independently centered prime-free positive test at height 32*pi."""

from argparse import ArgumentParser
from fractions import Fraction as Q
from math import comb, factorial
import flint
from flint import arb, acb, ctx, fmpq

parser = ArgumentParser()
parser.add_argument(
    "--panels", type=int, default=512, help="range cells per basic 1/32 interval"
)
parser.add_argument("--precision", type=int, default=100)
args = parser.parse_args()
ctx.prec = args.precision
assert ctx.prec >= 90 and args.panels > 0


def b(x):
    x = Q(x)
    return arb(fmpq(x.numerator, x.denominator))


def iv(l, r):
    return b(l).union(b(r))


def polyval(c, z):
    out = arb(0)
    for a in reversed(c):
        out = out * z + a
    return out


def hardy(t):
    t = b(t)
    theta = acb(arb(1) / 4, t / 2).lgamma().imag - t * arb.pi().log() / 2
    return ((acb(0, theta)).exp() * acb(arb(1) / 2, t).zeta()).real


def sign(x):
    if x > 0:
        return 1
    assert x < 0
    return -1


# Find sign changes on a dyadic grid, then bisect. Only the certified IVT brackets matter.
Ts = 32 * arb.pi()
lo, hi = 64, 138
cuts = [Q(i, 4) for i in range(4 * lo, 4 * hi + 1)]
sg = [sign(hardy(t)) for t in cuts]
brackets = []
for j in range(len(cuts) - 1):
    if sg[j] == sg[j + 1]:
        continue
    l, r = cuts[j], cuts[j + 1]
    for _ in range(17):
        m = (l + r) / 2
        if sign(hardy(m)) == sg[j]:
            l = m
        else:
            r = m
    assert sign(hardy(l)) * sign(hardy(r)) < 0
    brackets.append((l, r))
assert all(brackets[j][1] < brackets[j + 1][0] for j in range(len(brackets) - 1))
gammas = [iv(l, r) for l, r in brackets]
inside = [(l, r) for l, r in brackets if b(l) > Ts - 1 and b(r) < Ts + 1]
outside = [(l, r) for l, r in brackets if b(l) > Ts + 1 or b(r) < Ts - 1]
assert len(inside) + len(outside) == len(brackets)
print(
    "Certified sign changes",
    len(brackets),
    "in initial unit-radius target",
    inside,
    flush=True,
)

h = Q(1, 8)
d = Q(1, 32)
eps = Q(1, 2**60)
A = Q(2, 3)
a0 = 3 * h + d
assert b(A).exp() < 2


# B_T(x)=cos(Tx)*(2K(x)+K(x-d)+K(x+d)) because Td=pi.
def piece(x):
    coeff = [Q(0)] * 6
    for delta, weight in [(0, 2), (d, 1), (-d, 1)]:
        for i in range(7):
            a = x + delta + (3 - i) * h
            if a < 0:
                continue
            for k in range(6):
                coeff[k] += (
                    weight
                    * (-1) ** i
                    * comb(6, i)
                    * comb(5, k)
                    * a ** (5 - k)
                    / factorial(5)
                    / h**6
                )
    return [b(v) for v in coeff]


P = args.panels
step = d / P
pieces = [piece(j * d) for j in range(13)]
c = pieces[0][0]
# Generic smooth-envelope derivative bounds; multiply by cos(Tx) by the product rule.
M = b(32 * (16**2 + 16 + Q(1, 4))) + 2 * Ts * b(32 * (16 + Q(1, 2))) + Ts**2 * 32
arch = arb(0)
sample = [arb(0) for _ in gammas]
for j, coeff in enumerate(pieces):
    origin = b(j * d)
    for m in range(P):
        l = j * d + m * step
        r = iv(l, l + step)
        H = polyval(coeff, r - origin) * (r * Ts).cos() / (r / 2).cosh()
        weight = b(2 * step) * H
        for i, gamma in enumerate(gammas):
            sample[i] += weight * (r * gamma).cos()
        if l == 0:
            err = M * b((1 + 2 * step) * step * step / 4)
            arch += arb(0, err)
        else:
            arch += b(2 * step) * (-r / 2).exp() * (c - H) / (-(-2 * r).expm1())
q = (-b(a0) / 2).exp()
psi = (arb(1) / 4).digamma() - arb.pi().log()
V0 = c * psi + arch + 2 * c * (q.atanh() + q.atan())
# Perturbation due to smoothing K0, then multiplying by the cosine.
D0 = 2 * eps * 32 * 16
D1 = 2 * eps * 32 * (16**2 + Q(16, 2))
D2 = b(2 * eps * 32 * (16**3 + 16**2 + Q(16, 4))) + 2 * Ts * b(D1) + Ts**2 * b(D0)
q = (-b(A) / 2).exp()
Verr = (
    abs(psi) * b(D0)
    + D2 * b((1 + 2 * A) * A * A / 4)
    + 2 * b(D0) * (q.atanh() + q.atan())
)
V = V0 + arb(0, Verr)
Gerr = b(2 * A * D0)
pair_sum = 2 * (sum(sample) + arb(0, len(sample) * Gerr))
U = V - pair_sum
# For |t-T|<=1 the near boundary lobe alone suffices; the mirror lobe is nonnegative.
near = (1 - b(Q(1, 6 * 16**2))) ** 6 * (1 - b(eps**2 / 2)) ** 2
floor = (1 + (arb.pi() / Ts).cos()) * near - 4 * (1 - 1 / (b(A) / 2).cosh())
print("flint", flint.__version__, "precision", ctx.prec, "panels", P)
print("V", V.lower(), V.upper())
print("sampled pairs", pair_sum.lower(), pair_sum.upper())
print("U", U.lower(), U.upper())
print("uniform single mass", floor, "pair margin lower bound", (2 * floor - U).lower())

assert len(brackets) == 32 and len(inside) == 1
assert U < arb("0.876")
assert floor > arb("1.779") and 2 * floor - U > arb("2.682")
for distance in [15, 16]:
    d0 = b(distance)
    # sinc(u)=integral_0^1 cos(us)ds is decreasing on 0<=u<=pi.
    near = (d0 / 16).sinc() ** 6 * (1 - b((distance * eps) ** 2 / 2)) ** 2
    wall = (1 + (d0 / 32).cos()) * near - 4 * (1 - 1 / (b(A) / 2).cosh())
    inside = [
        iv(l, r) for l, r in brackets if b(l) > Ts - distance and b(r) < Ts + distance
    ]
    outside = [
        (l, r) for l, r in brackets if b(l) > Ts + distance or b(r) < Ts - distance
    ]
    assert len(inside) + len(outside) == len(brackets)
    print(
        "radius",
        distance,
        "samples inside",
        len(inside),
        "one-zero floor",
        wall.lower(),
        "pair margin",
        (2 * wall - U).lower(),
    )
    expected, minimum_margin = {15: (13, Q(228, 1000)), 16: (15, Q(326, 10000))}[
        distance
    ]
    assert len(inside) == expected and (2 * wall - U) > b(minimum_margin)
print("Uniform analytic floor, all T>=16 and radius one")
uniform = (2 - b(Q(22, 7) ** 2 / 512)) * (1 - b(Q(1, 6 * 16**2))) ** 6 * (
    1 - b(eps**2 / 2)
) ** 2 - b(Q(2, 9))
assert uniform > b(Q(7, 4))
print(uniform)
print(
    "Disjoint IVT brackets for the positive ordinate; exact endpoints in units of 2^-19:"
)
for l, r in brackets:
    assert (l * 2**19).denominator == (r * 2**19).denominator == 1
    print(int(l * 2**19), int(r * 2**19))
