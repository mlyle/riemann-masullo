"""Check the cumulative physical deficits against rational thresholds and audit initial rows."""
from fractions import Fraction
from pathlib import Path
import argparse

def verify(rows):
    assert len(rows) == 256
    scale = 1 << 30
    low = high = 0
    ratios = []
    signs = []
    for j, (idx, l, h) in enumerate(rows, 1):
        assert idx == j and l <= h
        low += max(0, -h)
        high += max(0, -l)
        ratios.append((Fraction(low, scale*j**7), Fraction(high, scale*j**7)))
        assert 250000*high < 1577*scale*j**7
        signs.append(1 if l > 0 else -1 if h < 0 else 0)
    assert signs.count(-1) == 128 and signs.count(1) == 127 and signs[0] == 0
    assert max(y for j, (_, y) in enumerate(ratios, 1) if j != 117) < ratios[116][0]
    print("D(J) < 0.006308 J^7 for 1 <= J <= 256; maximum ratio at J=117")
    print("S(j^4) positive for 127 indices, negative for 128, zero at j=1")
    print("peak ratio enclosure", *ratios[116])
    print("final ratio enclosure", *ratios[-1])

def audit_initial(rows, jmax):
    # A different sieve and an independent correctly rounded logarithm.
    from decimal import Decimal, localcontext
    from math import isqrt
    cutoff = jmax**4
    sieve = bytearray([1]) * (1 + cutoff)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(cutoff)+1):
        if sieve[p]:
            start = p*p
            sieve[start::p] = bytes((cutoff-start)//p+1)
    with localcontext() as ctx:
        ctx.prec = 45
        lo = plo = Decimal(0)
        at = 2
        for j, l, h in rows[:jmax]:
            x = j**4
            while at <= x:
                sign = {1:1,4:-1}.get(at%5,0)
                if sieve[at] and sign:
                    w = sign * ctx.ln(Decimal(at))
                    lo += w
                    plo += at*w
                at += 1
            val = x*lo-plo
            # 45 digits, fewer than 2e6 terms of individual size < 2e7.
            # Even 1e-24 at the final Riesz sum is a conservative error for jmax<=32.
            if j >= 2:
                assert Decimal(l)/(1<<30) < val - Decimal("1e-24")
                assert val + Decimal("1e-24") < Decimal(h)/(1<<30)
            else:
                assert val == l == h == 0
    print(f"independent prime sieve and decimal logarithms through j={jmax}")

if __name__ == '__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("rows",type=Path)
    ap.add_argument("--audit-initial",type=int,default=0)
    args=ap.parse_args()
    rows=[tuple(map(int,l.split())) for l in args.rows.read_text().splitlines()]
    verify(rows)
    if args.audit_initial:
        assert 2 <= args.audit_initial <= 32
        audit_initial(rows,args.audit_initial)
