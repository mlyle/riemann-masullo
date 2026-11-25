# The size of the actual rational fourth-power deficit

For the trivial character over the rationals put
\[
S(x)=\sum_{p\le x}(x-p)\log p-x^2/2,\quad
A(j)=\max(0,-S(j^4)),\quad D(J)=\sum_{1\le j\le J} A(j).
\]
Let \(\Theta=\sup_\rho\Re\rho\) over the nontrivial zeta zeros. The following classical deductions concern the unmodified, unsmoothed sum of nonnegative deficits.
\[
\lim_{J\to\infty}\frac{\log(1+D(J))}{\log J}=4\Theta+5.
\]
Thus an upper bound at exponent seven **along any one unbounded sequence**, even \(D(J_k)\le J_k^{7+o(1)}\), suffices for rational RH. The existing all-field Lean result uses a bound at every sufficiently large index. The lower bound on every large rational prefix below uses Ingham's zeta zero-density theorem. Extension to a general Hecke character would need its own density input. An upper bound along such a sequence for rational primes remains open. [All-field Lean theorem](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7153546171)

## The critical-line case

The identity \(S(x)=\int_0^x(\vartheta(t)-t)\,dt\) fixes the endpoint convention. The prime number theorem and the prime-power decomposition give \(\psi(t)-\vartheta(t)\sim\sqrt t\). Indeed the square term is \(\vartheta(\sqrt t)\); exponents at least three contribute \(O(t^{1/3}\log t)\) by the Chebyshev bound. The normalized integral of the discarded prime powers therefore tends to \(2/3\). This conclusion about prime powers is unconditional.

The integrated von Mangoldt explicit formula, on writing \(\beta=\Re\rho,\gamma=\Im\rho\), gives for \(x\ge2\)
\[
\frac{S(x)}{x^{3/2}}=-\frac23-\sum_\rho\frac{x^{\rho-1/2}}{\rho(\rho+1)}+o(1).
\]
The error is uniform as \(x\to\infty\), including on failure of RH: it consists of the prime-power asymptotic and the elementary terms of the exact formula. Multiplicities are counted throughout. The series of absolute coefficients is at most \(\sum_\rho 1/\gamma^2<0.04621\). In particular on RH every sufficiently late sample is strictly negative. Johnston's Theorem 1.2 even gives \(S(x)<-2\) for every real \(x>2\) on RH. [Johnston, Theorem 1.2 and Lemma 2.6](https://arxiv.org/pdf/2201.06184) · [Brent, Platt and Trudgian, Corollary 1](https://arxiv.org/pdf/2009.13791)

On RH, summing the expansion at \(x=j^4\) yields
\[
\frac{D(J)}{J^7}=\frac{2}{21}+
 \sum_\rho\frac{J^{4i\gamma}}{\rho(\rho+1)(7+4i\gamma)}+o(1).
\]
For each fixed ordinate use the Riemann sum of \(t^{6+4i\gamma}\) on \([0,1]\); truncating the absolutely convergent coefficient series makes the error uniform in \(J\). Since every \(|\gamma|>14\), the displayed oscillation has modulus less than \(0.00083\). The logarithmic average of \(D(J)/J^7\) tends to \(2/21\): harmonic averaging kills each nonzero frequency, and the absolute coefficient bound permits termwise passage. In particular, a method treating the rational deficits as negligible compared with \(J^7\) would fail even on RH.

## An exterior zero forces excess in every large prefix

Write \(F(y)=e^{-3y/2}S(e^y)\). Suppose \(1/2<\sigma<\beta_0\le\Theta\), with a zero \(\rho_0=\beta_0+i\gamma_0\). Ingham's estimate \(N(\sigma,T)\ll_\sigma T^{3(1-\sigma)/(2-\sigma)}\log^5 T\) implies \(\sum_{\beta>\sigma,\ \gamma>0}1/\gamma<\infty\). Use the unshifted instance of the independent worker's compact positive test. For each distinct \(z=\rho-1/2=b+i\gamma\) with \(\beta>\sigma,\gamma>0\), place masses in the ratio \(e^{b\pi/\gamma}:1\) at \(0,\pi/\gamma\). The distribution of the sum of independent such variables has bounded support and transform zero at every selected pair. Convolve with a compact smooth nonnegative density to obtain \(K\) supported in an interval \(I\). A further convolution with a wide uniform density gives a bounded compactly supported probability density \(P\) which is a positive constant throughout \(I\) and has the same required zeros. [Ingham, 1940](https://doi.org/10.1093/qmath/os-11.1.201) · [Compact test and primitive calculation](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md)

Use the transform convention \(\widehat K(z)=\int K(v)e^{zv}\,dv\). If its zero at \(z_0=\rho_0-1/2\) has order \(m\), then \(\widehat K(z)/(z-z_0)^m\) is the transform of a bounded complex kernel \(L\) supported in \(I\). One division follows by integrating \(e^{z_0s}K(s)\) from \(v\) to the right endpoint and multiplying by \(e^{-z_0v}\); its moment zero gives vanishing left of \(I\). Iterate. Consequently \(|L|\ll P\), its transform is nonzero at \(z_0\), and it still vanishes at all other selected points. Integration of the displayed expansion for \(F\) against \(P\) gives \(O(e^{(\sigma-1/2)y})\). Against \(L\) it gives a nonzero multiple of \(e^{z_0y}\) plus that same order of error. The unshifted coefficient of \(z_0\) is its multiplicity times \(-1/(\rho_0(\rho_0+1))\), so it cannot cancel. The compact supports and absolute convergence justify integration and the error uniformly at every large real \(y\). Hence \(\int P(v)|F(y+v)|\,dv\gg e^{(\beta_0-1/2)y}\), and subtracting the signed integral gives the same lower bound for \(\int P(v)\max(-F(y+v),0)\,dv\).

Put \(X=e^y\). On the support of this integral \(x=Xe^v\asymp X\). In each cell \([j^4,(j+1)^4]\), the lower interpolation bound gives
\[
\max(-S(x),0)\le A(j)+A(j+1)+O(X^{3/2}\log X).
\]
The length of this cell in \(v\) is \(4\log(1+1/j)\ll X^{-1/4}\). Thus the negative integral is at most \(O(\log X)+O(X^{-7/4}D(\lceil cX^{1/4}\rceil))\), with fixed \(c\) covering the supports and endpoint neighbors. For each large integer \(J\) choose \(X=((J-1)/c)^4\). The exponential gain \(X^{\beta_0-1/2}\) absorbs the logarithm and forces \(D(J)\gg_{\rho_0}J^{4\beta_0+5}\) for **all sufficiently large \(J\)**. The explicit formula also gives \(|S(x)|\ll x^{1+\Theta}\), whence \(D(J)\ll J^{4\Theta+5}\). Let \(\beta_0\) approach \(\Theta\). This proves the asserted limit irrespective of whether the supremum is attained. [Endpoint interpolation](https://github.com/mccorvie/riemann-masullo/pull/7603)

Combining the cases gives an unconditional arithmetic lower floor \(\liminf D(J)/J^7\ge 2/21-0.00083\) and \(\limsup D(J)/J^7\ge 2/21\). These inequalities are in the opposite direction to the missing upper bound, and they quantify the amount of prime-square bias any successful upper bound must accommodate. The subsequence criterion and the explicit oscillation above are paper proofs.
