# The upper Riesz sample bound and the rightmost real zero

Fix a normalized unitary Hecke character \(\chi\) of a fixed number field \(F\). Normalize away a pure norm twist, so the only possible pole of its ordinary finite L-function in positive real part is the simple pole at 1 for the trivial character. Write \(\delta_\chi\) for that character's indicator, and set
\[
 B_\chi(X)=\Re\sum_{N\mathfrak a\le X}(X-N\mathfrak a)\Lambda_\chi(\mathfrak a)-\delta_\chi X^2/2.
\]
Suppose \(B_\chi(X_j)\le C_\varepsilon X_j^{3/2+\varepsilon}\) for each \(\varepsilon>0\) and all sufficiently large indices of a sequence tending to infinity whose successive gaps are \(O(X_j^{1-\alpha})\) for some fixed \(\alpha>0\). If an exterior zero exists, its supremal real part \(\Theta_\chi\) must be the real part of an **actual real zero** at \(s=\Theta_\chi\) of this very L-function. Thus, whenever the real interval \((1/2,1)\) is certified free of zeros, these upper bounds alone imply GRH for this individual character. These are implications from an arithmetic upper bound on every sufficiently large sample.

## Why the upper sign singles out the real axis

Write \(M(z)=\int_1^\infty B_\chi(X)X^{-z-1}dX\). For \(\Re z>2\), its analytic expression is
\[
 \frac{L_\chi^*(z-1)+L_{\bar\chi}^*(z-1)}{2z(z-1)}
     -\frac{\delta_\chi}{2(z-2)},\qquad L_\chi^*=-L_\chi'/L_\chi.
\]
This follows by integrating each Riesz kernel and using absolute convergence. The residue of the trivial-character pole at 2 cancels. For any zero \(\rho\) with \(\Re\rho>1/2\), its translated pole at \(1+\rho\) has residue \(-[m_\chi(\rho)+m_{\bar\chi}(\rho)]/[2\rho(1+\rho)]\). In particular no two characters cancel one another's zero residue, and at a real zero the residue is negative.

Let \(\Theta>1/2\) be the supremum for this character. Conjugation gives the same supremum for \(\bar\chi\). Use the fixed-character classical estimate \(\psi_\chi(X)-\delta_\chi X=O_\eta(X^{\Theta+\eta})\) for every \(\eta>0\). It follows from the fixed-conductor truncated explicit formula and the \(O_F(T\log T)\) zero count, first at half-integers to stay clear of jumps, and then throughout the unit intervals since ideal norms are integers; at \(\Theta=1\) the elementary Chebyshev estimate suffices. This gives \(B_\chi'(X)=O_\eta(X^{\Theta+\eta})\) away from the integer norm discontinuities of the derivative. The continuous piecewise linear prime sum minus the smooth centering term is locally absolutely continuous. Choose \(\eta>0\) small relative to \(\alpha\) and \(\Theta-1/2\). Integration across each sample gap extends the assumed upper bound to \(B_\chi(X)\le C X^\kappa\) eventually with \(\kappa=\max(3/2+\eta,1+\Theta+\eta-\alpha)<1+\Theta\).

The nonnegative tail \(C X^\kappa-B_\chi(X)\) has Mellin abscissa exactly \(1+\Theta\). The absolute upper bound \(B_\chi(X)=O_\eta(X^{1+\Theta+\eta})\) for every \(\eta>0\) gives one inequality. For the reverse, poles with real parts approaching \(1+\Theta\) survive the subtraction of the one real majorant pole at \(\kappa\); absolute convergence farther left would analytically remove one such pole. Landau now requires an actual singularity at the **real** abscissa. Meromorphicity and \(\kappa<1+\Theta\) force a zero of \(L_\chi\) or \(L_{\bar\chi}\) at \(\Theta\). A zero of one on the real axis is a zero of the other. In particular the supremum cannot equal 1, by the classical nonvanishing line. For a lower sample bound one applies the same argument to \(C X^\kappa+B_\chi(X)\); the negative residue there is incompatible with a nonnegative Mellin transform on approach from the right, so even the real-zero alternative is eliminated. Under fixed-character GRH the quadratic smoothing and the absolutely convergent sum of reciprocal-square ordinates give \(B_\chi(X)=O(X^{3/2})\) by the Riesz explicit formula. The pointwise upper sample estimate is still open in general.

## Finite-conductor scope and a direct example

For every primitive Dirichlet character of conductor \(3\le q\le400000\), Platt's Theorem 7.1 rigorously verifies its zeros through a positive ordinate. In particular there is no real zero with \(1/2<\beta<1\). The same conclusion holds for the principal primitive character of conductor 1, since the alternating eta series is positive at every positive real argument. It passes to every imprimitive Dirichlet character induced from these conductors: every removed finite Euler factor \(1-\chi(p)p^{-s}\) with \(|\chi(p)|=1\) is nonzero on \(\Re s>0\). Consequently the upper-sample bound suffices for each of these individual characters, at arbitrary height and at any fixed polynomial grid. Platt's verification concerns the prior zero input; the signed sample estimate itself remains an arithmetic hypothesis. [Platt, Theorem 7.1](https://arxiv.org/pdf/1305.3087).

All six characters modulo 7 also admit a direct proof of this real-axis condition. Take 3 as generator, write \(\chi(3)=\exp(2\pi i j/6)\), and put \(f(x)=x^{-s}\) for real \(s>0\). For a nonprincipal character its Dirichlet series in the natural order converges and agrees with its continuation there, by bounded periodic partial sums and partial summation locally uniformly on \(\Re s>0\). Reorganize it into consecutive length-seven blocks. For \(j=1\), the imaginary part of each block, divided by \(\sqrt3/2\), is
\[
 f(7k+2)+f(7k+3)-f(7k+4)-f(7k+5)>0
\]
by strict decrease. For \(j=2\) it is
\[
 -f(7k+2)+f(7k+3)+f(7k+4)-f(7k+5)<0
\]
because the successive differences \(f(v)-f(v+1)\) strictly decrease with \(v\) by strict convexity. Conjugation handles \(j=4,5\). For \(j=3\), the running sums of the coefficients in each block are \(1,2,1,2,1,0,0\), so partial summation and the strict decrease give positivity. For \(j=0\), the factor \(1-7^{-s}\) is positive and the ordinary zeta function is nonzero throughout \((1/2,1)\).
