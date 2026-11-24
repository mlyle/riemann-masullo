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

## Reducing the full vector to a sparse remainder

A short-interval Möbius estimate allows more columns to be removed. For the same middle window and principal rational character, one can choose original columns $J_X$ such that
$$
\left\|F_X-\sum_{n\in J_X} e(n)h(n/y)\right\|_2=O_h(X^{-.03}),\qquad
\sum_{n\in J_X}\|e(n)h(n/y)\|_2^2\ll_{A,h}(\log X)^{-A}
$$
for every fixed $A>0$. The harmonic mass of the nonzero, active indices in $J_X$ obeys the same logarithmic estimate.

Put $Y=e^S$ and write $n=Mj$ uniquely, assigning all prime powers with prime exceeding $Y$ to $M$. The remaining $j$ is $Y$-smooth. The exact coefficient formula above applies for squarefree $M>1$, and a repeated prime in $M$ makes the physical column zero. For $M=1$ use $e_1=e$. In particular, $|e(n)|\le2\tau(j)$ on the active indices.

For fixed $b>0$ and fixed nonnegative integer $k$ we have
$$ \sum_{j>X^b,\,P^+(j)\le Y}\frac{\tau(j)^k}{j}\ll_{b,k,A}L^{-A}. $$
For the Rankin bound take $q=\log L$ and $\sigma=(\log q)/(2\log Y)$. The factor $X^{-b\sigma}$ is $\exp(-bq\log q)$. On prime powers, $\tau(n)^k\le d_{2^k}(n)$ by counting a tuple of valuations as its nested subsets at each possible level. The logarithm of the corresponding Euler product is $O_k(q)$. Indeed $\sum_{p\le Y}1/p=O(q)$ and $\sum_{p\le Y}(p^\sigma-1)/p\ll\sigma\sqrt q\sum_{p\le Y}(\log p)/p\ll\sqrt q\log q$.

Define $\mu_Y(M)$ to equal $\mu(M)$ when all prime factors exceed $Y$, and zero otherwise. Its exact Dirichlet convolution is $\mu_Y=\mathbf1_{P^+\le Y}*\mu$, as seen on prime powers. For a dyad $T\asymp X^u$ with $.9\le u\le1$, set $H=T^{.41}$. Then
$$ \int_T^{2T}\left|\sum_{x<M\le x+H}\mu_Y(M)\right|dx\ll_A THL^{-A}. $$
In the convolution truncate the smooth factor at $d\le T^{.06}$. For each such $d$, the integration variable changes to $x/d$ and the interval length $H/d$ exceeds $(T/d)^{1/3+\epsilon}$ for a fixed $\epsilon>0$. Apply Theorem 1.1(i) of Matomäki–Radziwiłł–Shao–Tao–Teräväinen to the constant nilsequence. On the exceptional locations use the trivial interval count. Sum the resulting integrals in $d$, losing at most a logarithm. The larger smooth factors have integrated total at most $3TH\sum_{d>T^{.06},\,P^+(d)\le Y}1/d$, covered by the Rankin estimate. [Short-interval Möbius theorem, p. 3](https://arxiv.org/pdf/2411.05770#page=3)

Choose a shift of a grid of length $H$ minimizing its total absolute sign imbalance. Averaging over shifts bounds the number of unmatched rough squarefree multipliers by $O_A(TL^{-A})$ on each dyad, including the cost of its two boundary cells. Match the opposite signs within each cell. For each match $B,C$ take all smooth $j$ at once. The previous detector bound and divisor sum estimate show that one match costs $O_h((H/T)\sqrt X(1+L)/T)$ in norm. There are at most $2T$ matches, and summing geometrically from $T=X^{.9}$ gives $O_h((1+L)X^{-.031})$. This estimate bounds the sum of the norms of the matched differences.

The unpaired large multipliers have total reciprocal mass $O_A(L^{-A})$, with a further logarithm for summing dyads absorbed by increasing $A$. Sum $\tau(j)^2/j\ll(1+L)^4$ in the sense of its cumulative sum over $j\le X$, to get the same bound for the diagonal. For $M<X^{.9}$ on the active window, $Mj\ge r_0Xe^{-S}> X^{.99}$ for sufficiently large $X$. Thus $j>X^{.09}$ and the smooth-tail estimate applies before summing $1/M$. This proves the reduction. A graph of residual pairings with maximum degree $O(L^C)$ consequently has total absolute contribution $o(1)$ for any fixed $C$, by $2|\langle v,w\rangle|\le\|v\|^2+\|w\|^2$. Higher-degree correlations in the remainder are still uncontrolled.

## A sparse family of genuine columns can have divergent energy

The two sparsity estimates just obtained cannot by themselves control all the remaining off-diagonal pairs, even when every coefficient is taken from the original Möbius error. For the actual detector take $1/2<u<r_0$ and put $Y_*=Xe^{-R/2}$, the top of the middle window. Select $K=\lfloor Y_*^{3/4}\rfloor$ distinct primes in $[uY_*,uY_*+Y_*/\log Y_*]$. Such a selection exists for every sufficiently large $X$ by the classical prime number theorem with remainder. For these primes $p>Xe^{-R}$ and $e(p)=w(0)-w(\log p)=1$. The entire support of $h(p/y)$ lies inside the middle window. With $H(z)=\int_0^\infty h(r)h(zr)dr$,
$$ \langle h(p/y),h(p'/y)\rangle = p^{-1}H(p'/p)=(1+o(1))\|h\|_2^2/(uY_*) $$
uniformly for the selected pairs, by continuity at one. Their total harmonic mass and positive diagonal are $O(Y_*^{-1/4})$. Yet the squared norm of their sum is asymptotic to $Y_*^{1/2}\|h\|_2^2/u$. Every distinct pair has reduced height comparable to $Y_*$.

This family can be retained in a remainder that still satisfies both compression estimates. Keep any previously matched partners of these primes alongside them, undoing only their matches. A partner is within $O(Y_*^{.41})$ and has modulus asymptotic to $uY_*$. Its only potentially active smooth cofactor is $j=1$, since $u>1/2$. Its coefficient there has absolute value one. Retaining both sides adds $O(K/Y_*)$ harmonic and diagonal mass. The bound on the sum of the norms of *all* matched differences still bounds the removed part. The prime-only subtotal shows why a hereditary absolute estimate on these pairs fails. The signed norm of the complete remainder, including the opposite signs of the partners, remains open.
