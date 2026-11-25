"""Check the finite conductor-five inverse coefficientwise, without evaluating logarithms."""
from math import isqrt


def is_prime(k):
    return k >= 2 and all(k % d for d in range(2, isqrt(k) + 1))


def mobius(k):
    factors = [p for p in range(2, k + 1) if is_prime(p) and k % p == 0]
    return 0 if any(k % (p * p) == 0 for p in factors) else (-1) ** len(factors)


# The quartic character exponent modulo 4. The nonunit residue is skipped.
phase = {1: 0, 2: 1, 3: 3, 4: 2}
units = ((1, 0), (0, 1), (-1, 0), (0, -1))
limit = 320
primes = [p for p in range(2, limit + 1) if is_prime(p)]
mu = [0] + [mobius(k) for k in range(1, limit + 1)]
checks = 0
for x in range(limit + 1):
    for p in primes:
        if p > x:
            break
        re = im = 0
        for n in range(1, x // p + 1):
            if n % 5 == 0 or mu[n] == 0:
                continue
            for m in range(1, x // (n * p) + 1):
                residue = m * p % 5
                if residue == 0:
                    continue
                a, b = units[(phase[n % 5] + phase[residue]) % 4]
                weight = mu[n] * (x - n * m * p)
                re += a * weight
                im += b * weight
        a, b = units[phase[p % 5]] if p % 5 else (0, 0)
        assert (re, im) == (a * (x - p), b * (x - p))
        checks += 1
print(f'conductor 5, chi(2)=i: {checks} exact log-prime coefficients, every integer cutoff 0..{limit}: PASS')
