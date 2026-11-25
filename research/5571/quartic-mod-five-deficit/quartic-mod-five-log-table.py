"""Write certified dyadic enclosures for 2^30 log(1+i/4096), including log 2."""
from fractions import Fraction
from sys import stdout
N, scale = 4096, 1 << 30
for i in range(N + 1):
    z = Fraction(i, 2*N+i)
    z2 = z*z
    partial, power = Fraction(0), z
    for k in range(13):
        partial += power / (2*k+1)
        power *= z2
    floor = (2*scale*partial).__floor__()
    ceil = (2*scale*(partial+power/(27*(1-z2)))).__ceil__()
    assert 0 <= ceil-floor <= 2
    print(floor, ceil, file=stdout)
