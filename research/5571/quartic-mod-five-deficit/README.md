# A finite fourth-power deficit estimate for the primitive quartic character modulo five

For the primitive character $\chi$ of modulus five with $\chi(2)=i$, let
$$S(x)=\sum_p\Re\chi(p)(x-p)_+\log p,\qquad D(J)=\sum_{j=1}^J[-S(j^4)]_+.$$
Then $D(J)<J^7$ for every $1\le J\le 2{,}500{,}000$. The explicit upper constant is $0.006308$ for $1\le J\le256$ and $0.902417$ for $256\le J\le2{,}500{,}000$. The conjugate character has the same real coefficients. This is a classical finite estimate with certified numerical constants. Controlling the signed deficit on an unbounded sequence is open. The target is Theorem 12.5.1.1, pp. 519–520. [Issue](https://github.com/mccorvie/riemann-masullo/issues/5571)

## Actual prime samples through index 256

The two residues $p\equiv1,4\pmod5$ have real coefficients $+1,-1$. The other three residues have real coefficient zero. An odd segmented sieve through $256^4=4{,}294{,}967{,}296$ gives 203,280,221 primes including 2. Signed integer bounds on the sums of $\log p$ and $p\log p$ in each prefix give a lower and upper bound at every sample. For a fixed choice of lower (or upper) coefficients, subtract its own weighted sum from $j^4$ times its unweighted sum. This is valid because $j^4-p\ge0$ on that prefix. Use the opposite logarithm endpoint for a negative coefficient. Of the 256 samples, 127 are positive, 128 are negative and $S(1)=0$. The maximum of $D(J)/J^7$ is attained at $J=117$ and lies between 0.00630707 and 0.00630799. There are 39 consecutive negative samples from 217 through 255.

Use the scale $s=2^{30}$, $K=4096$. For $p=2^e(1+i/K)(1+u)$ with $i$ the integer mantissa bin and $0\le u\le1/K$, use $u-u^2/2\le\log(1+u)\le u$. The table for $\log(1+i/K)$ encloses the first 13 terms of $2\operatorname{arctanh}(i/(2K+i))$ with the geometric upper bound for the remaining tail, using rational arithmetic. The same table includes $\log2$. Integer arithmetic then gives both logarithm endpoints, including the error from rounding $su$ down. A second sieve and 45-digit decimal logarithms independently check every row through $j=32$. The exact certificates use the integer bounds.

## The unrestricted smoothed estimate

For an odd primitive character write $A=-L'/L$, $a_0=A(0)$ and $a_1=\operatorname{fp}_{s=-1}A(s)$. Let $B=2\Re\Lambda'/\Lambda(1)$ for the completed function. The functional equation and the order-one product give
$$B=2\sum_\rho\Re(1/(1-\rho))=\log(5/\pi)-\gamma_E+2\Re L'(1)/L(1).$$
Indeed the difference of the logarithmic derivatives at one and zero cancels the Hadamard constant. Reflection $\rho\mapsto1-\bar\rho$ makes the two real-part sums equal. Taylor evaluation of this one Dirichlet function gives $0<B<0.204$, $|\Re a_0|<1$, $|\Re a_1|<1$. The odd gamma factor gives $\Re a_0=\log(5/\pi)-\gamma_E-\log2+\Re L'(1)/L(1)$, with the corresponding last term $1+\Re L'(2)/L(2)$ for $\Re a_1$. [Completed-product identity and zero sums](https://www.math.uwaterloo.ca/~mrubinst/publications/Chebyshev.pdf)

Platt's Theorem 7.1 verifies the critical line for this character through $H=20{,}000{,}000$, in both directions. The absolute coefficient mass $\sum|\rho(1+\rho)|^{-1}$ below $H$ is at most $B$ since $|\rho|^{-2}=2\Re(1/(1-\rho))$ on that line. Above $H$ use $|\rho(1+\rho)|^{-1}\le\gamma^{-2}$. Summing over the reflection with the same ordinate gives $\sum_{|\gamma|>H}(1+\gamma^2)^{-1}\le B$, since $2(1-\beta)/((1-\beta)^2+\gamma^2)\ge 2(1-\beta)/(1+\gamma^2)$. Thus the high coefficient mass is at most $2B$. These bounds use no symmetry between positive and negative ordinates of this nonreal character. [Platt, Theorem 7.1](https://arxiv.org/pdf/1305.3087#page=14)

For $y>1$ the triangular Perron kernel $y^{1+s}/[s(s+1)]$ applied to $A(s)$ gives the complete prime-power sum as the negative of the zero series plus
$$a_0 y+1+\log y-a_1-\sum_{m\ge1}\frac{y^{-2m}}{2m(2m+1)}.$$
The double pole at $-1$ gives $1+\log y-a_1$, and the last sum has modulus less than one. The real part supplies the physical coefficient. The absolute unsigned proper-power weight is at most $y^{3/2}+11y^{4/3}$: integrate $2u\vartheta(u)$ for the squares, use $y\vartheta(y^{1/3})$ for cubes, then $y\log_2(y)\vartheta(y^{1/4})$ for all higher exponents. The elementary Chebyshev bound $\vartheta(u)\le(\log4)u$ suffices, since $\log y\le(12/e)y^{1/12}$. For $0<y<1$ there are no primes and the modulus of the zero series is at most $3By$. These bounds give, for every $y>0$,
$$S(y)\ge-\Re\sum_\rho\frac{y^{1+\rho}}{\rho(1+\rho)}-y^{3/2}-11y^{4/3}-4y-8.$$
The expression at one follows by continuity. [Integrated explicit formula and contour](https://github.com/willzh0/riemann-masullo/blob/719213f260386a753004ab3b23596c8caa0f42c5/research/5571/fourth-power-deficit-boundary/subsequence.md) · [Odd-character residue calculation and the mean-one smoothing method](https://github.com/mlyle/riemann-masullo/tree/2e6ed753a03d0f98a94d9f7052754f77d0dc47a6/research/5571/fourth-power-prime-curvature)

For each prefix fix $v=J^{-2}$ and $Y=\exp(\sqrt v Z-v/2)$ with $Z$ standard normal. Its mean is one. The zero series is absolutely integrable by the two mass bounds and $\mathbb E Y^2=e^v$. Substitution of $y=xY$ multiplies each zero coefficient by $\exp(v\rho(1+\rho)/2)$. Put $N=256$, $J_* = 2{,}500{,}000$, $v_0=N^{-2}$. The modulus of this multiplier is at most $e^{3v_0/8}$ on the verified critical line, and at most $e^{v_0-H^2/(2J_*^2)}$ at all higher zeros, at any abscissa in the strip.

To return to the physical prime sum, subtract the tangent to $(y-p)_+$ at $x=j^4$, which is never prime. Its nonnegative remainder $h_p$ only occurs for primes between $x$ and $xY$. The tangent has its prescribed value in expectation. For a one-sided deficit, only $p\equiv1\pmod5$ can raise $\sum \Re\chi(p)h_p\log p$. If $d=|xY-x|$, there are at most $1+t/5$ integers of that residue in any interval of length $t$. Integration in $t$ bounds this entire curvature cost by $(d+d^2/10)(\log x+|\log Y|)$ before expectation. In particular, the prime sum can have either sign at any sample. The lower bound for $S(x)$ is uniform in that sign.

For $N\le J\le J_*$ let $P(a)=1/(a+1)+1/N$, so $\sum_{j\le J}j^a\le P(a)J^{a+1}$ for $a\ge0$. Cauchy–Schwarz and the Gaussian moments give $\mathbb E(Y-1)^2\le1.0001v$, $\mathbb E|Y-1|\le1.01\sqrt v$, $\mathbb E|Y-1||\log Y|\le1.01v$, and $\mathbb E(Y-1)^2|\log Y|\le3v^{3/2}$. For the last bound use $\mathbb E(Y-1)^4=e^{6v}-4e^{3v}+6e^v-3\le4v^2$ on this range. The script bounds its second derivative by $108v e^{6v}+6e^v<8$. The resulting nonnegative upper bounds for the sum of the clipped samples, divided by $J^7$, are

| Contribution | Upper bound |
| --- | --- |
| Low zeros and squares | $(1+B)e^{3v_0/8}P(6)$ |
| Remaining proper powers | $11e^{2v_0/9}N^{-2/3}P(16/3)$ |
| Affine remainder | $4P(4)/N^2+8/N^6$ |
| High zeros of this character | $2B e^{v_0-H^2/(2J_*^2)}J_*^2P(8)$ |
| Positive prime curvature | $(4.0004\log J_*+3/N)P(8)/10+1.01(4\log J_*+1/N)P(4)/N^3$ |

Their sum is less than $0.902417$. The executable repeats the outward-rounded intervals at 128 and 192 bits. This argument uses the verified height, and the exponential damping in the high-zero term weakens as the index grows beyond the stated interval.

## Reproduction

Use Python 3 and a C++17 compiler for the direct prime certificate. The analytic ledger also needs python-flint 0.9.0.

```sh
python3 quartic-mod-five-log-table.py > logs.txt
g++ -std=c++17 -Wall -Wextra -O3 quartic-mod-five-samples.cpp -o samples
./samples 256 < logs.txt > grid-256.txt
python3 quartic-mod-five-check.py grid-256.txt --audit-initial 32
python3 quartic-mod-five-smoothed.py --bits 128
python3 quartic-mod-five-smoothed.py --bits 192
```
