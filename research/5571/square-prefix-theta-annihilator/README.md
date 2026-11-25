# Actual signed prime prefixes in every polylogarithmic-ratio window

Let \(A,A_d,F\) be the two [rational first-prime square prefixes and their normalized step functions](../square-prefix-signed-gaussian/README.md). There is \(C>1\) such that, for every sufficiently large \(X\), some integer
\[
 X/[C(\log X)^{5/4}]\le k\le C X(\log X)^{5/4}
\]
has both \(A(k)/k^2\) and \(A_d(k)/k^2<-1/2\). In fact \(-1/2\) can be replaced by any fixed number greater than \(-1\).

If \(\beta>1/2\) is the real part of an actual nontrivial zeta zero, there are constants \(C_\beta,c_\beta>0\) such that the same window, with \(C=C_\beta\), contains two integer cutoffs \(k_+,k_-\). For both physical compensators simultaneously,
\[
 A(k_+)/k_+^2>c_\beta X^{2\beta-1},\qquad
 A(k_-)/k_-^2<-c_\beta X^{2\beta-1}.
\]
These conclusions hold at every sufficiently large center, including when the supremum of the real parts is unattained. The argument uses the theta transform of the ordinary rational zeta function; finite-height zero verification is unnecessary. Its purpose is a localized arithmetic sign consequence. A bound on the *frequency* of positive prefixes on an unbounded sequence remains open.

## The two shifted theta factors have a positive inverse transform

Use the bilateral transform \(\widehat f(z)=\int_{\mathbb R}f(v)e^{zv}dv\), and \(Q(z)=\xi(1/2+z)\). Riemann's theta formula gives \(Q=\widehat\Phi\), where \(\Phi\) is even and, for \(u\ge0\),
\[
 \Phi(u)=\sum_{n\ge1}(4\pi^2n^4e^{9u/2}-6\pi n^2e^{5u/2})
                e^{-\pi n^2e^{2u}} .
\]
The formula on the whole complex plane follows by analytic continuation from its Fourier form and the double-exponential decay of the even kernel. [D. Romik, equations (1.8), (1.11)](https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi.pdf).

Set \(r(u)=\exp(9|u|/2-\pi e^{2|u|})\). Uniformly in \(u\),
\[
 (4\pi^2/2)\,r(u)\le\Phi(u)\le (4\pi^2)(1.01)\,r(u).
\]
The first summand alone gives the lower bound, since \(1-3/(2\pi e^{2|u|})>1/2\). For the upper bound use \(\sum_{n\ge2}n^4 e^{-\pi(n^2-1)}<0.01\): the first term is \(16e^{-3\pi}<0.002\), and successive ratios are at most \((3/2)^4e^{-5\pi}<0.001\).

For \(t=1,\sqrt2\) the inverse transform of \(Q(z+it)Q(z-it)\) is
\[
 P_t(v)=\int_{\mathbb R}\Phi(v/2+h)\Phi(v/2-h)\cos(2th)\,dh.
\]
This follows by the convolution formula, since the imaginary integrand is odd in \(h\). In particular \(P_t\le\Phi*\Phi\). We claim \(P_t\ge \kappa(\Phi*\Phi)\) pointwise with an absolute \(\kappa>0\). The even function \(\log r\) has second derivative at most \(-4\pi\) away from zero and a downward derivative jump there, since \(9/2-2\pi<0\). Thus \(\log r(u)+2\pi u^2\) is concave on the real line. For \(a=v/2\) put \(f_a(h)=r(a+h)r(a-h)\). The even function \(\log f_a(h)+4\pi h^2\) is concave; its derivative is nonpositive almost everywhere on \(h>0\). Consequently \(-h f'_a(h)\ge 8\pi h^2 f_a(h)\) almost everywhere. Integration by parts gives \(\int h^2 f_a/\int f_a\le1/(8\pi)\) with vanishing boundary terms. Piecewise smoothness and continuity handle both possible corners without extra terms.

For the probability density proportional to \(\Phi(a+h)\Phi(a-h)\), the preceding comparison bounds \(\mathbb E h^2\le(2.02)^2/(8\pi)<0.171\). Now \(\cos(2th)\ge1-2t^2h^2\) gives \(P_t(v)\ge(1-4\cdot0.171)(\Phi*\Phi)(v)\). This proves the claimed uniform positivity.

## One fixed annihilating probability with two-sided physical tails

Let \(U_t\) be uniform probability density on \([-\pi/t,\pi/t]\). Normalize to mass one the convolution
\[
 K=\text{const}\cdot\Phi*P_1*P_{\sqrt2}*U_1*U_{\sqrt2}.
\]
It is a strictly positive even continuous density. The entire transform contains the five factors \(Q(z),Q(z+i),Q(z-i),Q(z+i\sqrt2),Q(z-i\sqrt2)\). In particular it vanishes at each shifted zero \(z=\rho-1/2+it'\), \(t'=0,\pm1,\pm\sqrt2\), and the two uniform factors give zeros at the four nonconstant prime-square drift frequencies. No restriction on the zeros' real parts is needed. The normalization exists by the physical positivity just proved.

There are \(c,C,M,m>0\) and \(a=2/5\) such that for all real \(v\)
\[
 m e^{-C e^{a|v|}}\le K(v)\le M e^{-c e^{a|v|}}.
\]
By the bounds on \(P_t\), it suffices to consider five copies of \(\Phi\) and two bounded uniform shifts. For the pointwise upper bound at \(v\), one of the five variables on the convolution hyperplane must have absolute value at least \((|v|-B)/5\), where \(B=\pi+\pi/\sqrt2\). Bound that density by its tail supremum and integrate the four other densities in \(L^1\) and the bounded shifts against their probability measures. Summing over the five choices gives the bound, since \(\Phi(s)\ll\exp(-c_0e^{2|s|})\). For the lower bound, for every bounded sum of box shifts \(d\), restrict four variables to fixed-width intervals centered at \((v-d)/5\); the fifth is within a bounded distance of the same center. The lower bound on \(\Phi\), with these five bounded offsets, gives the claimed lower inequality. The positive constants absorb any bounded values of \(v\).

By the [absolutely convergent grouped Riesz spectrum and physical rounding comparison](../square-prefix-signed-gaussian/README.md#proof), for \(u\ge0\)
\[
 F(u)=D(u)+\sum_{b,\omega}C_{b,\omega}e^{(b+i\omega)u}+r_0(u),\quad r_0(u)\to0.
\]
Here \(D=-1\) plus just the four box-annihilated frequencies, \(|b|<1/2\), and \(\sum |C_{b,\omega}|<\infty\). Every zero-bearing abscissa supports a nonzero grouped coefficient by the [four-shift multiplicity argument](../square-prefix-sign-blocks/README.md#exact-absolutely-summable-spectrum). Extend \(F=0\) on the negative line. Termwise integration against \(K(v)\) at \(u=y+v\) is justified by its finite exponential moments. The bounded remainder on \(u\ge0\) contributes \(o(1)\) by dominated convergence; on \(u<0\) the spectral extension is \(O(e^{|u|/2})\) and contributes \(o(1)\) by the double-exponential tail. Therefore
\[
 \int K(v)F(y+v)\,dv=-1+o(1)\qquad(y\to+\infty).
\]
These are positive weights on the actual discrete square cutoffs, obtained by integrating the translated kernel over their floor cells. Since \(|F(y+v)|\ll e^{y/2} e^{|v|/2}\), the absolute cost of discarding \(|v|>D_y=(5/2)\log y+C_0\) is \(O(e^{-y})\) for a sufficiently large fixed \(C_0\). Indeed the tail integral is \(\ll e^{y/2-c' e^{2D_y/5}}\). The retained kernel mass tends to one. This forces the asserted negative value for any fixed threshold above \(-1\) (use a slightly stricter threshold for the other compensator, whose pointwise difference is \(o(1)\)). Put \(y=2\log X\); taking integer parts changes the multiplicative window constant only.

## Isolating one exterior zero and forcing both signs in the same window

Fix an active grouped \(z_0=b+i\omega\), \(b=\beta-1/2>0\), and let \(l\ge1\) be the order of the zero of \(\widehat K\) there. This order is finite since \(\widehat K(0)=1\). There is a complex kernel \(L\) with transform \(\widehat L(z)=\widehat K(z)/(z-z_0)^l\) and a pointwise bound \(|L(v)|\ll\exp(-c_1e^{2|v|/5})\). To divide a transform by \(z-z_0\), when \(\widehat f(z_0)=0\), use
\[
 g(v)=e^{-z_0 v}\int_v^\infty e^{z_0s}f(s)\,ds
     =-e^{-z_0v}\int_{-\infty}^v e^{z_0s}f(s)\,ds .
\]
Either tail representation, on its corresponding half-line, preserves a double-exponential bound with index \(2/5\), allowing the positive constant in the exponent to decrease. This follows for example by absorbing \(\exp(|z_0|(|v|+|s|))\) and one tail integration into half the original exponent for all sufficiently large \(|v|\). The identity \(g'=-z_0g-f\) and integration by parts give \((z-z_0)\widehat g=\widehat f\). Repeat \(l\) times. The transform of \(L\) still vanishes at every other active pair and every nonconstant drift frequency. Hence
\[
 \int L(v)F(y+v)dv=C_{b,\omega}\frac{\widehat K^{(l)}(z_0)}{l!}e^{z_0y}
                     -\widehat L(0)+o(1).
\]
Its leading coefficient is nonzero. This isolates a single chosen member of a conjugate pair; the signed measurement is complex.

The lower bound on \(K\) shows that for sufficiently large fixed \(s>0\) and \(C'>0\),
\[
 P(v)=C'[K(v-s)+K(v+s)+K(v)]\ge|L(v)|\quad(v\in\mathbb R).
\]
For large positive \(v\), \(K(v-s)\ge m\exp(-Ce^{-2s/5}e^{2v/5})\); choose \(s\) to make the constant smaller than \(c_1\), and use \(K(v+s)\) on the negative side. Positivity and continuity handle the intervening compact set. Translated \(K\)'s keep every required transform zero. Thus \(\int PF(y+\cdot)=-\widehat P(0)+o(1)\). At each \(y\) choose a unit \(\eta_y\) making the leading term of \(\eta_y\int LF(y+\cdot)\) positive real. The two nonnegative weights \(P\pm\Re(\eta_y L)\) have uniformly bounded total mass and uniform double-exponential tails of index \(2/5\). Their integrals against \(F(y+\cdot)\) exceed \(c_2e^{by}\) and are below \(-c_2 e^{by}\), respectively, for all sufficiently large \(y\). The same truncation leaves \(O(e^{-y})\) absolute error with a constant allowed to depend on \(z_0\). Nonnegativity now forces opposite values of sizes \(\gg e^{by}\) in the retained window. Transfer to the other compensator by its \(o(1)\) difference, proving the second assertion.

A consequence for successive indices of either strict sign off RH is that from every large \(X\) one can find the desired sign by \(C'X(\log X)^{5/2}\), by moving the center from \(X\) to a constant times \(X(\log X)^{5/4}\). The same conclusion for the negative sign holds unconditionally. All results on this page are classical paper proofs.
