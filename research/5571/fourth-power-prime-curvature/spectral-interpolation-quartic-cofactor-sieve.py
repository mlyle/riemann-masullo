"""Exact dyadic exponents, sharp cofactor inclusion, and formal logarithmic weight tests."""
from collections import Counter
from fractions import Fraction as Q
from math import gcd, isqrt, lcm


def primes(n):
    return [p for p in range(2, n + 1) if all(p % a for a in range(2, isqrt(p) + 1))]


def logvector(n):
    out = Counter()
    for p in primes(n):
        while n % p == 0:
            out[p] += 1
            n //= p
    return out


def mobius(n):
    v = logvector(n)
    return 0 if any(k > 1 for k in v.values()) else (-1) ** len(v)


def outer(a, b):
    out = Counter()
    for i, v in a.items():
        for j, w in b.items():
            out[tuple(sorted((i, j)))] += v * w
    return out


def add_scaled(a, b, c):
    for i, v in b.items():
        a[i] += c * v


def cleaned(a):
    return {k: v for k, v in a.items() if v}


exponents = (Q(1, 2) + Q(791, 1000) * Q(7, 6), Q(791, 1000) * Q(11, 6),
             Q(791, 1000) * Q(5, 2) - Q(1, 2), Q(791, 1000) * Q(13, 7))
assert exponents == (Q(8537, 6000), Q(8701, 6000), Q(591, 400), Q(10283, 7000))
assert max(exponents) < Q(37, 25) and Q(21, 100) - Q(209, 1000) > (1 - Q(209, 1000)) / 1000
R, K = 16, 4
lam = {}
for d in range(1, R + 1):
    v = Counter()
    if d <= K:
        add_scaled(v, logvector(K), mobius(d))
    else:
        add_scaled(v, logvector(R), mobius(d))
        add_scaled(v, logvector(d), -mobius(d))
    lam[d] = v
# Pair index and divisor-square profile must agree as polynomials in the individual log primes.
row = {}
for d, a in lam.items():
    for e, b in lam.items():
        key = lcm(d, e)
        add_scaled(row.setdefault(key, Counter()), outer(a, b), 1)
unit = ((1, 0), (0, 1), (-1, 0), (0, -1))
phase = {1: 0, 2: 1, 3: 3, 4: 2}
Xmax = 210
pseq = primes(Xmax)
weights = {}
for m in range(1, Xmax + 1):
    z = Counter()
    for d, a in lam.items():
        if m % d == 0:
            add_scaled(z, a, 1)
    weights[m] = outer(z, z)
    if 1 < m <= K:
        assert not cleaned(weights[m])
for x in range(1, Xmax + 1):
    for p in pseq:
        if p > x:
            break
        actual, pair = (Counter(), Counter()), (Counter(), Counter())
        for m in range(1, x // p + 1):
            if m * p % 5 == 0:
                continue
            coords = unit[phase[m * p % 5]]
            # Test an arbitrary common nonconstant cofactor weight, without evaluating logs.
            physical_weight = (x - m * p) * (m + 3 if m <= 17 else 1)
            for side, coord in zip(actual, coords):
                add_scaled(side, weights[m], physical_weight * coord)
        for h, a in row.items():
            for k in range(1, x // (h * p) + 1):
                m = h * k
                if m * p % 5 == 0:
                    continue
                coords = unit[phase[m * p % 5]]
                physical_weight = (x - m * p) * (m + 3 if m <= 17 else 1)
                for side, coord in zip(pair, coords):
                    add_scaled(side, a, physical_weight * coord)
        assert list(map(cleaned, actual)) == list(map(cleaned, pair))
P = 2 * 3 * 5 * 7
for m in range(1, 2001):
    direct = int(gcd(m, P) == 1)
    exact = sum(mobius(d) for d in range(1, P + 1) if P % d == 0 and m % d == 0)
    assert direct == exact
print('dyadic exponents', *(str(r) for r in exponents))
print('flat lambda-square: all quartic prime-log coefficients as quadratic divisor-log polynomials, X=1..210, R=16, K=4: PASS')
print('literal coprime cutoff P=210, every cofactor 1..2000: PASS')
