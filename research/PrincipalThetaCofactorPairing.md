# Cancellation among actual rational theta coefficients

For Theorem 12.5.1.1, pp. 519–520, take the principal character of the rational field and the smooth real detector and monotone weight from the earlier low-ratio calculation. Three signed estimates below use the actual coefficient sequence. The first gives an explicit set of compensating terms. The second extends the selection to the entire limiting mass of the critical low-ratio band. The third deletes a family of original columns from the full middle-window sum in physical norm. The signed contribution of the remaining high-ratio terms is open. [Gap issue](https://github.com/mccorvie/riemann-masullo/issues/5571) · [Low-ratio calculation and covariance estimates](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7146011837)

## Coefficients and physical normalization

Write $L=\log X$, $W=L/\log L$, $R=\sqrt W$, $S=W/2$, $Z=\log(S/(2R))$ and $V=R^2Z^2$. Define
$$e(n)=\sum_{d\mid n}\mu(d)w(\log d)-\mathbf 1_{n=1},\qquad e_M(j)=\sum_{d\mid j}\mu(d)w(\log M+\log d)-\mathbf 1_{j=1}.$$
The normalized weight is one up to $L-S$ and zero above $L-R$. Its derivatives are bounded uniformly as in the earlier calculation. The detector $h$ is real, smooth and supported in $[r_0,1]$ for a fixed $r_0>0$. All integrals here are over $I=(Xe^{-S},Xe^{-R/2})$ with measure $dy/y^2$. The full middle-window error vector is $F_X(y)=\sum_n e(n)h(n/y)$. The squared norm is a sum over ordered pairs. For distinct $n,m$, the low-ratio band consists of the pairs with $\max(n,m)/\gcd(n,m)\le V$. Its signed subtotal tends to $P_h>0$ for the nonzero test in the earlier calculation.

Suppose $Mj\le X$, $(M,j)=1$, and every prime factor of $M>1$ exceeds $e^S$. Every proper divisor of $M$ times any divisor of $j$ lies on the unit plateau, so expansion of the coprime divisor product gives $e(Mj)=\mu(M)e_M(j)$. If a prime $q>e^S$ has $q^2\mid Mj$, every squarefree divisor of $Mj$ is at most $X/q$. Its coefficient then vanishes. The argument also works on individual detector columns because $h(Mj/y)=0$ when $Mj>X$.

## A fixed selection covering two fifths of the low band

Partition $[X^{4/5},X^{49/50}]$ into complete multiplicative cells $(T,(1+\eta)T]$ with $\eta=\exp(-\kappa\sqrt L)$, for a sufficiently small fixed $\kappa>0$. In each cell pair every prime $B$ with a distinct semiprime $C=st$, choosing the smaller prime in $[T^{13/51},T^{49/100}]$. The prime number theorem with its classical remainder applies uniformly to the quotient intervals. The ratio of the available semiprime count to the prime count tends to
$$\int_{13/51}^{49/100}\frac{du}{u(1-u)}=\log(1862/663)>1.$$
The matching can use the natural ordering in each cell. Both $\sum_B1/B$ and $\sum_B1/C$ tend to $\log(49/40)$. Every factor of $C$ exceeds $X^{52/255}>X^{1/5}$ and is below $X^{4/5}$. Consequently two selected decompositions $C\ell$ of the same cofactor agree, since the two largest prime factors recover $C$. A selected giant prime $B$ cannot divide such a cofactor. [Prime number theorem with remainder, Maynard, Lemma 4.3](https://arxiv.org/pdf/1507.05080#page=9)

For distinct primes $p,p'\le V$ take the four pairs indexed by a common $\ell$, with first entry $pB\ell$ or $pC\ell$ and second entry $p'B\ell$ or $p'C\ell$. The two equal-multiplier pairs lie in the low band. Each mixed pair has gcd $\ell$ and both reduced entries exceed $V$. Its reduced entries recover the two small primes, the matched giant prime and semiprime, and their orientation.

Set $r=B\ell/y$. In the Hilbert space with measure $\sum_\ell\ell^{-1}dr$ write $G_p(u)(\ell,r)=\mathbf 1_{B\ell/r\in I}e_{uB}(p\ell)h(upr)$. The sum of the four terms is exactly
$$B^{-1}\langle G_p(C/B)-G_p(1),G_{p'}(C/B)-G_{p'}(1)\rangle.$$
The cutoff in this expression is independent of $u$. The derivative in $u$ has squared norm $O_h((1+L)^4/p)$ on the interpolation interval. Indeed $\tau(p\ell)\le2\tau(\ell)$, the detector or its derivative has support of length $O_h(1/p)$ in $r$, and $\sum_{\ell\le2X}\tau(\ell)^2/\ell\ll(1+L)^4$ follows by comparison with the fourfold divisor function. Cauchy–Schwarz gives a total absolute error after grouping of $O_h(\eta^2(1+L)^4V\sum_B1/B)=o(1)$.

The within-$M$ prime-pair contribution, for $M=B,C$, is $(P_h+o(1))/M$ uniformly. To see the uniformity in the earlier low-band calculation, replace $L$ by $L_M=L-\log M$ and keep $R,S,Z$ fixed. The support of the translated slope remains above $\log V$. In $x=L_M-t$ its shape is unchanged. With $f_R(x)=Z[-w'(L-x)]$ the main harmonic variance at the running upper endpoint is exactly
$$ Z^{-2}\int_R^S (1+x-R/2-\log p+\log r)|f_R'(x)|^2\,dx.$$
The clipped covariance error is $O(1/(R^3 Z^2))$ uniformly. The prime-shift Taylor errors depend only on $R,S,Z,p$. Thus the normalized main term and limiting prime-pair kernel are independent of $M$. Summing the two signs shows that the selected low subtotal tends to $2\log(49/40)P_h$ and its selected higher counterpart to the negative of that quantity. [Covariance theorem, Chen An, Theorem 1.3](https://arxiv.org/abs/2206.10104)

## Selecting higher ratios to balance the entire critical low band

Define a positive measure on the common cofactors by
$$\nu_X(A)=\sum_{k\in A}\int_I\Big|\sum_{p\le V\ {\rm prime}} e(pk)h(pk/y)\Big|^2\frac{dy}{y^2}.$$
Removing the equal primes changes any subtotal by $o(1)$ uniformly in $A$. The positive diagonal is $O_h((1+\log V)^2/V)$ by the single-prime estimate in the earlier calculation. Nonprime reduced directions have total absolute cost $o(1)$. Hence $\nu_X(\mathbb N)\to P_h$. Normalize to a probability measure $\mu_X$.

For fixed $a>0$ and integer $D$, squarefree $d\le\sqrt X$ supported on at most $D$ primes above $X^a$ satisfy
$$\mu_X\{k:d\mid k\}=(1+o(1))/d$$
uniformly. Put $k=dj$. On coprime cofactors the exact factorization above applies on the detector support. If a prime of $d$ divides $j$, the original row is zero. In the translated unrestricted row the total squared-norm cost of these excluded $j$ is $O_h(V(1+L)^4\sum_{q\mid d}1/q)=o(1)$ before the $1/d$ change of variables. This follows by summing the square roots of individual $p$-row bounds, using $\tau(qb)\le2\tau(b)$. The translated unrestricted variance is $P_h+o(1)$ uniformly, since $L/2\le L_d\le L$. Repeated factors from this prime range have zero mass in the original measure.

Fix a number of ranges $m$ and a Bonferroni truncation order $K$. Choose $\delta_1<1/[2(K+5)]$ and $\delta_i=10^{1-i}\delta_1$. Let $G_i$ be the primes between $X^{.19\delta_i}$ and $X^{.99\delta_i}$. These sets are disjoint. Run the previous matching at scale $X^{\delta_i}$ inside each range, choosing a common $\eta=\exp(-\kappa\sqrt{\delta_m L})$. All factors of the matched numbers lie in that range. The sum of the reciprocals of all matched primes and semiprimes there tends to $w_0=2\log(49/40)$. The sum of prime reciprocals in $G_i$ tends to $\lambda=\log(.99/.19)$.

Let $E_i$ be the event that the entire $G_i$-part of $k$ equals one of the matched numbers. For a single range or two distinct ranges, let $n=1$ or $2$ respectively. Prescribe one matched number from each range, with product $M$. Exclude other prime factors in their union by finite inclusion–exclusion. Every divisor tested through the first $K+1$ additional primes is at most $\sqrt X$ and uses at most $K+5$ primes. The uniform divisor estimate applies with fixed $a<.19\delta_m$. The limiting inclusion–exclusion coefficients are $w_0^n(n\lambda)^j/j!$. Indeed the sum of squared reciprocals of the extra primes is $o(1)$, and deleting factors of $M$ changes their reciprocal mass by $o(1)$. All sums of reciprocal weights under consideration are bounded for fixed $K,m$. Bonferroni therefore makes the single and double event probabilities arbitrarily close to $c=w_0e^{-\lambda}>0$ and $c^2$ respectively by choosing $K$ large.

If both approximations have error at most $\tau$, the second moment of $N=\sum_i\mathbf1_{E_i}$ gives
$$\mu_X(N=0)\le\frac{1-c}{mc}+\frac{(1+2c)\tau}{c^2}.$$
First choose $m,\tau$ for the desired error, then $K$, then the ranges, and finally $X$. For each cofactor with a successful range take the first such range. Exchanging its matched prime and semiprime preserves admissibility of the remaining cofactor and all earlier ranges. Thus the same cofactor restriction applies on both sides of the four-term pairing. Reduced indices recover the orientation and the matched range uniquely. The derivative bound continues to apply after restriction. The total grouped error is $O_h(\eta^2(1+L)^4V\sum_{i,B}1/B)=o(1)$ for each fixed family.

Taking a sequence of desired errors tending to zero and sufficiently large successive thresholds $X$ gives a selection of distinct higher-ratio terms whose signed subtotal tends to $-P_h$. The omitted part of the signed low band tends to zero. No bound on the unselected higher-ratio terms follows from this selection.

## Deleting a positive proportion of integer columns in the physical norm

There is a separate deletion estimate for the full middle-window vector. Use primes $B$ in $[X^{.94},X^{.99}]$. In dyadic intervals at height $T$ take cells of length $H=T^{.45}$. Pair a prime $B$ to a semiprime $C=st$ in the same cell, with $T^{.08}\le s\le T^{.30}$. The supply of semiprimes per prime tends in mean square over the cell locations to the ratio $\log((.30/.70)/(.08/.92))>1$, in the sense that both counts divided by the common prime main term approach their respective constants.

In detail, the Selberg integral bound on p. 225 of Zaccagnini gives $o((H/\log T)^2)$ mean-square error for prime counts over a translate of a cell. For each prime $s$ in the specified sector apply the same estimate at length $H/s$ and scale $T/s$. The quotient lengths exceed $(T/s)^{1/5}$ by a fixed power of $T$, uniformly since $.45-.30>.2(1-.30)$. Changing variables back, the root-mean-square error is $o(H/[s\log(T/s)])$ uniformly. Sum these bounds by the triangle inequality in $L^2$. Partial summation over $s$ yields the stated ratio. For the endpoint interval $[x,x+H]$ with $x\asymp T$, replacing $\log(x/s)$ by $\log(T/s)$ costs relative $O(1/\log T)$. A common grid shift exists whose summed squared errors for the prime and semiprime counts are at most their average over shifts. On this grid all but a vanishing fraction of cells have a surplus of semiprimes. The prime count in the remaining cells is $o(T/\log T)$ by Cauchy–Schwarz. One can cover the full exponent range with complete dyadic intervals, since deleting the two endpoint dyads costs $O(1/\log X)$ in harmonic mass. Cell boundary strips cost $O(H/T)$ per dyad even using the trivial integer bound. All errors are uniform for $T\ge X^{.94}/2$. [Zaccagnini, *Primes in almost all short intervals*, Theorem, p. 225](https://matwbn.icm.edu.pl/ksiazki/aa/aa84/aa8432.pdf)

Match all primes in the surplus cells injectively. Their reciprocal mass tends to $\log(.99/.94)$ by Mertens' theorem, and the matched semiprimes have the same limiting mass. Both prime factors of $C$ exceed $X^{.06}$ by a fixed power and are below $X^{.94}$ by a fixed power. A column index $n=Mj\le X$ for a selected $M=B,C$ can therefore be decoded uniquely. The two largest prime factors identify $C$ in its case, and none of them is a candidate giant prime. The selected indices $\mathcal S_X$ have
$$ |\mathcal S_X|/X\longrightarrow 2\log(.99/.94). $$
Indeed summing $\lfloor X/M\rfloor$ introduces at most $O(X^{.99})$ error.

For a fixed match, sum over $j$ through $\lfloor X/\min(B,C)\rfloor$. Whenever the associated index exceeds $X$ its detector is already zero. On the remaining indices the exact signs are opposite. Differentiate $e_{uB}(j)h(uBj/y)$ in $u$ between $1$ and $C/B$. The coefficient and its derivative are $O(\tau(j))$. The change of variables $r=Bj/y$ shows the vector derivative in $L^2(I,dy/y^2)$ has norm $O_h(\tau(j)/\sqrt{Bj})$. Summing the paired differences in the Hilbert norm itself, using $\sum_{j\le z}\tau(j)/\sqrt j\ll\sqrt z\log(2z)$, gives
$$
 \Big\|\sum_{n\in\mathcal S_X}e(n)h(n/y)\Big\|_2
 \ll_h \sqrt X\log X\sum_B\frac{T^{-.55}}{B}
 \ll_h X^{-.017}\log X=o(1).
$$
This controls the change caused by deleting every selected column simultaneously, independently of the unselected columns. The proportion counts integer indices. It gives no percentage of the whole squared error. The remaining vector still needs an estimate.
