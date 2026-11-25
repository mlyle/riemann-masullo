# The long Möbius tail of the bare conductor-five prime deficit

Let χ be either quartic character modulo five. Put S(x)=Σₚχ(p)log p (x−p)₊ and B(x)=Σₘχ(m)m S(x/m), with both functions zero for x≤2. The complete-convolution estimate of the [periodic prime calculation](spectral-interpolation-periodic-prime-convolution.md) gives |B(x)|≪x^(3/2) exp(−cΦ(log x)) for some c>0, where Φ(t)=t^(3/5)(log t)^(−1/5) for large t. The square-prime drift vanishes because χ² is nonprincipal.

## The omitted dilations can grow with the cutoff

By completely multiplicative character values and Σ_{d|m}μ(d)=1_{m=1}, finite summation gives

\[
 S(X)=\sum_{1\le n\le X/2}\mu(n)\chi(n)nB(X/n).
\]

For any 0<λ<2c write M(X)=exp(λΦ(log X)) for large X. Uniformly for 1≤n≤M(X), Φ(log(X/n))≥(1−o(1))Φ(log X), since log M=o(log X). Consequently for each 0<c′<c−λ/2,

\[
 \left|\sum_{n\le M(X)}\mu(n)\chi(n)nB(X/n)\right|
 \ll X^{3/2}\exp[-c'\Phi(\log X)].
\]

This uses only Σ_{n≤M}n^(−1/2)≤2√M. Define U(X)=−Re Σ_{M(X)<n≤X/2}μ(n)χ(n)nB(X/n). The physical unsmoothed deficit satisfies

\[
 \sum_{j\le J}(-\Re S(j^4))_+
 =\sum_{j\le J}U(j^4)_++O\big(J^7 e^{-c''\Phi(\log J)}\big)
\]

for some c″>0. This follows from the pointwise 1-Lipschitz property of the positive part, and splitting the sum at √J. The finitely many small X allow any positive cutoff convention. Every surviving B-value is at a cutoff below X exp(−λΦ(log X)). The remaining signed tail is an explicit sum with the true Möbius-character coefficients. An upper estimate on its positive part at the required scale remains open.

The inverse includes a simple fixed arithmetic row: for X/3<n≤X/2, B(X/n)=χ(2)log 2·(X/n−2), so this entire portion is χ(2)log 2 times Σ_{X/3<n≤X/2} μ(n)χ(n)(X−2n). If χ(2)=i, its real part probes the imaginary part of this Möbius-character sum with a minus sign. Other rows may cancel it.

## Exact price of independent pointwise error bars

For a finite inverse row n≤M, with X>2M, allow an independent complex error |e_n|≤(X/n)^(3/2) on each distinct B(X/n). The operator norm from these disks to the absolute value of the real signed output is exactly

\[
 X^{3/2}\sum_{n\le M}\mu(n)^2\mathbf1_{5\nmid n} n^{-1/2}.
\]

Choose eₙ with the phase conjugate to that of μ(n)χ(n) to attain the upper triangle bound. Simultaneously changing those phases by −1 attains the same magnitude on the negative part. For a prescribed finite X the finitely many distinct values are compatible with a smooth error envelope: interpolate their normalized values by bumps with disjoint supports.

The density of squarefree integers coprime to 5 is 5/π². Indeed insert μ(n)²=Σ_{d²|n}μ(d), discard 5|d, and use #{m≤t:5∤m}=(4/5)t+O(1). Summing over d≤√M produces

\[
 \sum_{n\le M}\mu(n)^2\mathbf1_{5\nmid n}
 =\tfrac45 M\prod_{p\ne 5}(1-p^{-2})+O(\sqrt M)
 =\tfrac5{\pi^2}M+O(\sqrt M).
\]

Partial summation gives the normalized row norm (10/π²)√M+O(log(2M)). With independent pointwise budgets (X/n)^(3/2)exp(−cΦ(log(X/n))), its size on M=X^η with fixed 0<η<1 is X^(3/2+η/2−o(1)). In particular the available stretched-log saving alone cannot protect the anchored exponent under an absolute polynomial-length inversion. For polynomial budgets (X/n)^(3/2−δ) with fixed δ≥0 the exact exponent is 3/2+η/2−δ(1−η); the endpoint first becomes compatible when δ≥η/[2(1−η)]. These operator statements concern independent errors. The actual values B(X/n) are jointly arithmetic and a signed estimate could exploit that dependence.

The native [PR 7668](https://github.com/mccorvie/riemann-masullo/pull/7668) proves the preceding complete-convolution bound at square-root scale for all nonprincipal characters. The stretched-log gain, smooth shortening and inverse-tail consequences here use classical estimates.
