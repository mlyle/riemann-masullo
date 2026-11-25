# Fixed-ratio windows and actual signed prime counts from Ingham density

Let \(A,A_d\) be the [two rational first-prime square prefixes](../square-prefix-sign-density/README.md). Write \(N_\pm(X;L)\) for the number of integers \(X\le k\le e^L X\) where **both** prefixes have the indicated strict sign. Here \(L>0\) is the logarithmic width in the integer **square index**.

* Unconditionally there is a fixed \(L>0\) for which \(\log(1+N_-(X;L))/\log X\to1\) as \(X\to\infty\).
* If RH fails there is a fixed \(L>0\) such that this limit equals one for each sign. No assumption on existence of a rightmost zero is needed.
* If RH fails and the supremum \(\Theta=\sup_\rho\Re\rho\) is **unattained**, the conclusion for both signs holds for **every prescribed** \(L>0\). Thus in every fixed interval \([X,(1+\varepsilon)X]\), however small its fixed relative length, the count of each sign is \(X^{1+o(1)}\).
* In the remaining exterior case where \(\Theta\) is attained, the [almost periodic top-line calculation](../square-prefix-sign-density/README.md#what-density-zero-along-a-subsequence-excludes) gives a positive lower ordinary density of each sign in cumulative prefixes. No positive lower ordinary density in arbitrary short prescribed windows is asserted.

Consequently a lower cumulative positive density of zero together with even one unbounded sequence of any fixed-ratio windows on which the positive count is \(O(X^{1-\delta})\) for some \(\delta>0\) would imply RH. The two sequences may differ. Either arithmetic compensator can be used for those hypotheses. Their proof for the actual primes remains open.

## Sparse exterior terms and a compact positive measure

Use the [physical Riesz expansion](../square-prefix-signed-gaussian/README.md#proof)
\[
 F(u)=D(u)+\sum_{b,\omega}C_{b,\omega}e^{(b+i\omega)u}+o(1),\qquad
 F(u)=A(\lfloor e^{u/2}\rfloor)/\lfloor e^{u/2}\rfloor^2.
\]
The trigonometric polynomial \(D\) is bounded, \(\sum|C_{b,\omega}|<\infty\), \(b=\beta-1/2\), and \(\omega=\gamma+t\) for a nontrivial zero \(\beta+i\gamma\) and \(t\in\{0,\pm1,\pm\sqrt2\}\). Grouping coincident shifted points accounts for multiplicities. Every zero-bearing abscissa has a surviving coefficient by the four-shift argument in the linked derivation. The two compensators' normalized step functions differ by \(o(1)\).

Suppose \(\Theta>1/2\) and fix \(1/2<\sigma<\Theta\). Ingham's density theorem bounds the zero count with \(\beta>\sigma\) and \(0<\gamma\le T\) by \(O_\sigma(T^{d_\sigma}\log^5 T)\), where \(d_\sigma=3(1-\sigma)/(2-\sigma)<1\). Summing by dyadic heights gives \(\sum_{\beta>\sigma}1/|\gamma|<\infty\), by conjugation and local finiteness. The finitely many fixed shifts preserve this convergence; all shifted ordinates are nonzero since the first zeta zero has height greater than 14. Therefore for the surviving pairs above \(\sigma\) the **total length**
\[
 S_\sigma=\sum_{b>\sigma-1/2,\,\omega>0:C_{b,\omega}\ne0}\frac{\pi}{\omega}
\]
is finite. Each positive imaginary pair is taken once, with the real weights below annihilating its conjugate automatically. Multiplicities can only enlarge the zeta upper bound. [A. E. Ingham, *On the estimation of \(N(\sigma,T)\)*, Q. J. Math. 11 (1940), 201–202](https://doi.org/10.1093/qmath/os-11.1.201) · [Modern explicit formulation, Theorem 1.1 and introduction](https://arxiv.org/abs/2507.15184).

For each such \(z=b+i\omega\), put \(d=\pi/\omega\). Independently choose the random variable \(V_z\) taking \(0,d\) with probabilities \(e^{bd}/(1+e^{bd}),1/(1+e^{bd})\). Its bilateral transform vanishes at \(z\) and \(\bar z\). The sum of all choices converges absolutely for every outcome and has probability law \(\mu\) supported on \([0,S_\sigma]\). Its transform is entire, has mass one at zero, and vanishes at each required point, by independence of any one summand from the complementary sum. This construction uses the true arithmetic zero-density theorem, in contrast to an assumption that the whole zeta divisor is sparse.

Fix \(\tau>0\), and convolve \(\mu\) with a smooth probability bump supported on \([-\tau,\tau]\) to get \(K\). Write \(I=[-\tau,S_\sigma+\tau]\), of length \(\ell=S_\sigma+2\tau>0\), so \(K\) is smooth, nonnegative and supported on \(I\). Let \(P=K*U\), where \(U\) is the uniform probability density on \([-2\ell,2\ell]\). Then \(P\) is bounded and supported on \(I+[-2\ell,2\ell]\) of length \(5\ell\). For every \(v\in I\), \(P(v)=1/(4\ell)\): the translated uniform covers the entire support of \(K\). Its transform keeps all the zeros of \(\widehat K\).

## Isolate a single actual exterior term

For any surviving \(z_0=b+i\omega\) with \(b>\sigma-1/2\), divide \(\widehat K\) by \((z-z_0)^m\), where \(m\) is its entire zero order. The inverse kernel \(L_{z_0}\) is bounded and supported on the **same** \(I\). This follows by repeated integration of \(e^{z_0s}K(s)\) from \(v\) to \(+\infty\) with the factor \(e^{-z_0v}\), as in the [two-sided primitive calculation](../square-prefix-theta-annihilator/README.md#isolating-one-exterior-zero-and-forcing-both-signs-in-the-same-window). The exact transform zero makes the primitive vanish to the left of \(I\) also. Thus \(|L_{z_0}|\le C(z_0)P\); the support and \(P\) are independent of the active pair being isolated.

The residual spectral contribution from every lower abscissa is \(O_\sigma(e^{(\sigma-1/2)y})\) after integration against \(P\) or \(L_{z_0}\); the implied constant may include the chosen kernel. This is uniform at all sufficiently large \(y\). Indeed all kernels have bounded support, \(|b|<1/2\), and all Riesz coefficients are absolutely summable. Consequently
\[
 \left|\int P(v)F(y+v)\,dv\right|\ll e^{(\sigma-1/2)y},\qquad
 \int L_{z_0}(v)F(y+v)\,dv
   =c(z_0)e^{z_0y}+O_{z_0}(e^{(\sigma-1/2)y}),
\]
where \(c(z_0)=C_{b,\omega}\widehat K^{(m)}(z_0)/m!\ne0\). Neither integral uses any knowledge of the signs of prime error measurements. The first suppresses the entire high divisor and the second retains exactly the chosen member of a conjugate pair.

It follows that \(\int P|F(y+\cdot)|\gg_{z_0}e^{by}\) at **every** sufficiently large center. Subtract the smaller signed integral to get the same lower order for each one-sided mass. Since \(P\) is fixed while \(b\) can approach \(b_*=\Theta-1/2\), and \(|F(u)|\ll1+e^{b_*u}\) for \(u\ge0\), both one-sided \(P\)-masses have logarithmic rate exactly \(b_*\) per unit \(y\). This compact test has a bounded support length, unlike the all-divisor theta test, which gives a signed limit of \(-1\) without requiring an exterior zero.

To count, each integer floor cell in the fixed support window has \(P\)-mass \(O_\sigma(e^{-y/2})\) and \(|F|\ll_\sigma e^{b_*y}\). Contributions with \(|F|\le1\) cost at most one. Thus the number with \(F>1\), and separately the number with \(F<-1\), is at least \(\exp((1/2-o(1))y)\). The other compensator has the same strict sign on these cells for large \(y\). Shift \(y\) so that the full interval of square indices lies inside \([X,e^L X]\), taking \(L>5\ell/2\); the strict slack absorbs floor effects. The trivial upper count is \(O_L(X)\), which proves the claimed limits.

If \(\Theta\) is unattained then \(S_\sigma\downarrow0\) as \(\sigma\uparrow\Theta\), by dominated convergence starting at any fixed \(\sigma_0\in(1/2,\Theta)\). Each term from a fixed zero eventually drops out. Given any prescribed \(L>0\), take \(\sigma\) sufficiently close to \(\Theta\), followed by a sufficiently small \(\tau>0\), so \(5(S_\sigma+2\tau)/2<L\). When \(\Theta\) is attained simply keep one \(\sigma\) and the resulting \(L\). Unconditional joint negative counts follow by this exterior argument or by eventual strict negativity on RH. If cumulative positive density has liminf zero, the attained exterior case is impossible by almost periodicity; if also the stated localized power saving holds, the unattained exterior case is impossible by the arbitrary-width assertion.

These arithmetic implications are classical derivations. The fixed-width compact test depends on a zero abscissa threshold and is used here to prove a consequence of any failure of RH. The separate [positive theta-pair theorem in Lean](https://github.com/mccorvie/riemann-masullo/pull/7612) applies to an explicit fixed signed-mean test without this spectral input.

## What arbitrarily long runs of one sign can distinguish

For either physical prefix, define \(D_\pm\) as the supremum of the fixed logarithmic lengths \(L>0\) for which there are arbitrarily large \(X\) such that **every** integer in \([X,e^L X]\) has that strict sign. Use zero if the set is empty. The same classification holds for simultaneous signs of the two compensators.

| Arithmetic zero configuration | \(D_+\) | \(D_-\) |
| --- | --- | --- |
| RH | \(0\) | \(+\infty\) |
| An attained exterior supremum | finite and strictly positive | finite and strictly positive |
| An unattained exterior supremum | \(0\) | \(0\) |

Indeed, on an attained exterior line the uniformly almost periodic top-line spectrum has relatively densely recurring intervals above and below fixed thresholds after normalization. For all sufficiently late such intervals the whole integer block, for both compensators, has the selected strict sign. This gives the strict lower bounds. A sufficiently large fixed-ratio window has both signs everywhere by the preceding theorem, giving the finite upper bounds. The unattained case follows by applying the same theorem to every fixed positive \(L\). The critical case follows from the eventual strict sign margin.

Thus a locally perfect sign count, with zero positive indices on arbitrarily large windows of some fixed relative width, could itself occur with an attained exterior supremum. A power saving on such windows by itself excludes an unattained supremum but does not exclude that attained case.
