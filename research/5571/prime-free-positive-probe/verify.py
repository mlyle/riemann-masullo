"""Certified interval pilot; see the accompanying proof for the smoothing perturbation."""

from argparse import ArgumentParser
from fractions import Fraction as Q
from math import comb, factorial
import flint
from flint import arb, acb, ctx, fmpq

parser = ArgumentParser()
parser.add_argument(
    "--panels", type=int, default=4096, help="range-integration cells per spline piece"
)
parser.add_argument("--precision", type=int, default=100, help="Arb precision in bits")
args = parser.parse_args()
assert args.panels > 0 and args.precision >= 96
ctx.prec = args.precision


def ball(q):
    q = Q(q)
    return arb(fmpq(q.numerator, q.denominator))


def interval(a, b):
    return ball(a).union(ball(b))


def polynomial(coeffs, x):
    v = arb(0)
    for c in reversed(coeffs):
        v = v * x + c
    return v


h = Q(1, 8)
shift = Q(1, 4)
A = Q(2, 3)  # room for smoothing; exp(A)<2
eps = Q(1, 2**60)
assert ball(A).exp() < 2


# Express B0(j*h+z) as a degree-five polynomial in local coordinate z.
def spline_piece(j):
    c = [Q(0)] * 6
    for delta, weight in [(0, 2), (shift, -1), (-shift, -1)]:
        for i in range(7):
            a = j * h + delta + (3 - i) * h
            if a < 0:
                continue
            for k in range(6):
                c[k] += (
                    weight
                    * (-1) ** i
                    * comb(6, i)
                    * comb(5, k)
                    * a ** (5 - k)
                    / factorial(5)
                    / h**6
                )
    return [ball(v) for v in c]


pieces = [spline_piece(j) for j in range(5)]
c = pieces[0][0]


def H0(j, x):
    return polynomial(pieces[j], x - ball(j * h)) / (x / 2).cosh()


def hardy_Z(t):
    t = ball(t)
    theta = acb(arb(1) / 4, t / 2).lgamma().imag - t * arb.pi().log() / 2
    return ((acb(0, theta)).exp() * acb(arb(1) / 2, t).zeta()).real


lo, hi = Q(14134724, 10**6), Q(14134726, 10**6)
zlo, zhi = hardy_Z(lo), hardy_Z(hi)
assert zlo * zhi < 0
gamma = interval(lo, hi)

# Signed full zero mass for the C^4 prototype via the finite archimedean formula, and the
# bilateral transform at the certified sign change. The spline is zero beyond r=5/8.
P = args.panels
step = h / P
a0 = 5 * h
arch = arb(0)
spect = arb(0)
for j in range(5):
    for m in range(P):
        left = j * h + m * step
        r = interval(left, left + step)
        H = H0(j, r)
        spect += ball(2 * step) * H * (r * gamma).cos()
        if left == 0:
            # sup |H0''| <= 32 (16^2+16+1/4);
            # integral |g| on [0,step] <= M*(1+2*step)*step^2/4.
            M = 32 * (16**2 + 16 + Q(1, 4))
            E = M * (1 + 2 * step) * step**2 / 4
            arch += interval(-E, E)
        else:
            arch += ball(2 * step) * (-r / 2).exp() * (c - H) / (-(-2 * r).expm1())
q = (-ball(a0) / 2).exp()
V0 = (
    c * ((arb(1) / 4).digamma() - arb.pi().log())
    + arch
    + 2 * c * (q.atanh() + q.atan())
)

# Actual smooth H minus prototype H0. Convolution by the two mollifiers moves by <=2eps.
D0 = 2 * eps * 32 * 16
D2 = 2 * eps * 32 * (16**3 + 16**2 + Q(16, 4))
q = (-ball(A) / 2).exp()
psi = (arb(1) / 4).digamma() - arb.pi().log()
Verr = (
    abs(psi) * ball(D0)
    + ball(D2 * (1 + 2 * A) * A * A / 4)
    + 2 * ball(D0) * (q.atanh() + q.atan())
)
F_err = ball(2 * A * D0)
V = V0 + arb(0, Verr)
F = spect + arb(0, F_err)
U = V - 2 * F
print("FLINT", flint.__version__, "precision", ctx.prec, "per spline piece panels", P)
print("Hardy Z at signed bracket endpoints", zlo, zhi)
print("V prototype", V0, "smooth error", Verr, "actual full V", V)
print("F at the line zero", F, "remaining mass", U)
# Boundary mass on a candidate window. For |a|<=1/2 compare cosh(a*x)/cosh(x/2)
# to 1. The smoothed second difference has L1 norm <=4.
delta = 4 * (1 - 1 / (ball(A) / 2).cosh())


def min_mass(L, R):
    lower = arb(10)
    n = (R - L) * 32
    for i in range(n):
        t = interval(Q(L) + Q(i, 32), Q(L) + Q(i + 1, 32))
        eta = 1 - (t * ball(eps)) ** 2 / 2
        u = 2 * (1 - (t / 4).cos()) * (t / 16).sinc() ** 6 * eta**2 - delta
        lower = lower.min(u.lower())
    return lower


assert U < ball(Q(21, 50))
assert Verr < ball(Q(71, 10**15))
print("V endpoints", V.lower(), V.upper())
print("F endpoints", F.lower(), F.upper())
print("U endpoints", U.lower(), U.upper())
for L, R, minimum, margin in [
    (4, 19, Q(1119, 5000), Q(69, 2500)),
    (5, 18, Q(539, 1250), Q(553, 1250)),
]:
    floor = min_mass(L, R)
    assert floor > ball(minimum)
    assert 2 * floor - U > ball(margin)
    print(
        f"window [{L},{R}]; each zero has mass > {minimum}; conjugate-pair margin > {margin}"
    )
