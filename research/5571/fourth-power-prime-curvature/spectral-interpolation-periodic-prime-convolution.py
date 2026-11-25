"""Exact exponent checks for the truncated periodic-prime convolution."""
from fractions import Fraction as F

lo, hi = F(74, 100), F(79, 100)
phase = 1/lo - 1 + F(1,7)
assert phase==F(128,259) and F(1,2)-phase==F(3,518)
assert 1/hi-1==F(21,79)
exponents=(F(1,2)+hi*F(7,6), hi*F(11,6), hi*F(5,2)-F(1,2), hi*F(13,7))
assert exponents==(F(853,600),F(869,600),F(59,40),F(1027,700))
assert all(k<2*lo for k in exponents)
assert 2-3*(1-hi)==F(137,100)<2*lo==F(37,25)<F(3,2)
print("uniform Fourier gap",F(1,2)-phase,"dyadic powers",*exponents,
      "smooth remainder",2-3*(1-hi),"including small primes",2*lo)
