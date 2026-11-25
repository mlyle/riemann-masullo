# Exact finite positive mixtures for the ordinary rational prime atoms

This is a **classical construction** for the trivial rational character at one fixed width \(0<b\le 1/2\). The profile vanishes at log norm zero. Both ordinary polar moments vanish. Every single rational prime-power evaluation vanishes, and the real transform on both edges dominates a fixed strictly positive function on every |t| ≥ 14. The construction allows the base kernel to be chosen for this width, and the finite frequency list and weights to change with the observation scale. It does not prove a sign or vanishing of the project's width jump. In the constructed sequence the surviving signed archimedean term has a strictly positive limit. No statement below has been checked in Lean.

Use \(\widehat f(t)=\int e^{itx}f(x)dx\). In the rational Weil–Barner formula an even test \(H\) has prime term \(-2\sum_{p,m}(\log p)p^{-m/2}H(m\log p)\), and true polar moments \(LH(\pm1/2)\). The lowest absolute ordinate of a nontrivial zeta zero exceeds 14. These are the arithmetic inputs. [Büthe, §2](https://arxiv.org/pdf/1308.6704) · [Brent–Platt–Trudgian, opening paragraph](https://arxiv.org/pdf/2009.13791)

## A direct prime-free comparison and its surviving sign

Choose a nonzero smooth real \(f\) supported in an interval of length \(s<\log2\). Put \(k=f*\check f\), \(w=|\widehat f|^2\), and \(C=\|f'\|_2^2/\|f\|_2^2\). Then
\[
 B=-k''-Ck,\quad B(0)=0,\quad\widehat B(t)=(t^2-C)w(t),\quad H=B/\cosh(bx).
\]
Its prime evaluations all vanish by support. For even real \(B\), both edge real parts are precisely \(\widehat B(t)\). Unlike a globally strip-positive test, a norm-one-vanishing test can have negative boundary values at some ordinates; indeed Fourier inversion gives \(\int\widehat B=0\).

Use one even nonnegative \(f_e\) and one odd \(f_o\) positive on the interior of its positive half-support, both with \(2<C_i<196\). An explicit choice starts with the first even cosine and second odd sine Dirichlet modes on \([-1/4,1/4]\), extended by zero, and convolves each with an even positive smooth probability mollifier of radius \(1/1024\). The support length is \(257/512<\log2\). For an input mode with wave number \(q\le4\pi\), translation gives \(\|f-f_{\rm raw}\|_2\le q\|f_{\rm raw}\|_2/1024\) and \(\|f'\|_2\le q\|f_{\rm raw}\|_2\), hence \(\sqrt C\le4\pi/(1-4\pi/1024)<14\). The Dirichlet Poincaré inequality gives \(C\ge\pi^2/s^2>2\). The odd convolution is positive for \(x\ge1/1024\) inside its positive support by the sign of the unmollified sine; nearer zero the uncut sine convolves to a positive multiple of itself.

The actual polar value is \(-\int k(x)S(x)dx\) where \(R(x)=\cosh(x/2)/\cosh(bx)\) and \(S=R''+CR\). For \(0<b<1/2\), \(S>0\) and \(S'(x)>0\) on \(0<x<s\). Indeed, with \(c=1/2\) and \(D=c^2-b^2\),
\[
 R''=D R-2b\tanh(bx) R',\quad
 0<R'/R=c\tanh(cx)-b\tanh(bx)\le c,\quad
 R'/R\ge Dx\operatorname{sech}^2(cx).
\]
For the last inequality differentiate \(z\tanh(zx)\) with respect to \(z^2\) and use \(\tanh u\ge u\operatorname{sech}^2u\). Differentiating the first identity gives \(R'''\ge-2b^2[1+\cosh^2(cx)]R'\ge-3R'/2\) on this interval. Also \(R''\ge-2bcR\). Thus the even polar value is negative, because \(k_e\ge0\). For the odd input,
\[
 \int k_o S=2\iint_{x,y>0} f_o(x)f_o(y)[S(x-y)-S(x+y)]dxdy<0.
\]
Its polar value is strictly positive. A convex combination cancels the poles. At \(b=1/2\) the direct odd polar value is zero because \(\int k_o=0\). These direct edge weights can have zeros where \(\widehat f\) vanishes; the regularization in the next section supplies a strict common floor.

The real archimedean term of each direct test is strictly positive. Put \(q(t)=\Re\psi(1/4+it/2)-\log\pi\), \(s_b(t)=(2b)^{-1}\operatorname{sech}(\pi t/(2b))\) and \(Q_b=q*s_b\). The digamma series shows \(q\) is even and strictly increasing for \(t>0\). Its derivative convolved with \(s_b\) is positive for \(t>0\), since the latter is even and strictly decreasing there and \(Q_b'(t)=\int_0^\infty q'(y)[s_b(t-y)-s_b(t+y)]dy\). Fourier transformation of \(\operatorname{sech}(bx)\) and \(\int(t^2-C)w(t)dt=0\) now give
\[
 \mathrm{Arch}(H)=\frac1{2\pi}\int (t^2-C)w(t)[Q_b(t)-Q_b(\sqrt C)]dt>0.
\]
Strictness follows on an open set since \(\widehat f\) is entire and nonzero as a function. [Digamma series (5.7.6)](https://dlmf.nist.gov/5.7#E6) · [Rational real gamma term](https://arxiv.org/pdf/1308.6704)

## A fixed lower envelope before choosing the observation scales

For each of the two inputs define \(E(t)=\int_{t-2}^{t+2}(|\widehat f(u)|^2+|\widehat f'(u)|^2)du\). It is even, strictly positive and Schwartz. Its inverse Fourier transform is smooth and supported in \([-s,s]\): convolution by the indicator in frequency multiplies the sum of the autocorrelations of \(f\) and \(xf\) by the inverse transform of the indicator. One-dimensional Sobolev embedding on these length-four intervals gives \(\sup_{|u-t|\le1}w(u)\le C_S E(t)\), with an absolute constant. For instance choose a point where \(|\widehat f|^2\) is at most its interval mean, use the fundamental theorem along an interval of length at most four, and then Cauchy–Schwarz.

Fix \(A=1\), and for sufficiently small \(\delta>0\) set
\[
 \widehat K_i(t)=(A+t^2)[w_i(t)+\delta E_i(t)],\qquad
 \nu_i(t)=\frac{w_i(t)}{2\pi k_i(0)}.
\]
Thus \(K_i\) is smooth real even of support in \([-s,s]\), \(\widehat K_i>0\), \(K_i(0)>0\), and \(\nu_i\) is an even probability density whose characteristic function is \(k_i(x)/k_i(0)\). The limiting numerator \(K_i-K_i(0)k_i/k_i(0)\) differs from \(-k_i''-C_i k_i\) by \(O(\delta)\) in each smooth seminorm with support fixed. For \(|t|\ge14\), its transform dominates \(d_i\widehat K_i(t)\) for some \(d_i>0\). Indeed the coefficient of \(w_i\) is \(t^2-C_i-O(\delta)\), whereas the regularizer appears with its full coefficient. At \(b<1/2\), both strict pole signs and both strict archimedean signs persist for small \(\delta\). At \(b=1/2\), the regularized odd polar value is \(\widehat K_o(0)=\delta A E_o(0)>0\) because \(w_o(0)=0\); the even one stays strictly negative. The comparison is made separately for each fixed width.

Choose \(0<\lambda<1\) so that the convex combination of the two limiting polar values is zero. This fixes **one baseline** \(K=\lambda K_e+(1-\lambda)K_o\). Define \(r_*=\lambda K_e(0)/K(0)\), and \(\nu_r=r\nu_e+(1-r)\nu_o\) with characteristic function \(\phi_r\). The limiting numerator is \(K-K(0)\phi_r\). At \(r=r_*\) this is the polar-zero convex combination already constructed. Varying \(r\) has a nonzero polar slope, since \(\int R k_e/k_e(0)>0\) while \(\int R k_o/k_o(0)\le0\) by the same odd-kernel difference, with equality at \(b=1/2\). Select nearby **fixed** endpoints \(r_-<r_*<r_+\) inside \((0,1)\) so their limiting pole values straddle zero. Both profiles have positive archimedean values bounded below by a fixed constant, and \(\widehat K-2\pi K(0)\nu_{r_\pm}\ge d\widehat K\) for \(|t|\ge14\), with common \(d>0\). For the latter assertion \(2\pi K(0)|\nu_e-\nu_o|\le C\widehat K/(A+t^2)\), since both coefficients in the baseline are positive. These endpoints, baseline and constants all precede the choice of \(n\).

## The literal long-support probes: uniform edges and complete prime cancellation

Use the given positive-mixture family
\[
 H_{\omega,L}(x)=\frac{K(x)+G(x/L)\cos(\omega x)}{\cosh(bx)},\qquad
 \omega=T+h_n,\quad L=L_n\to\infty.
\]
The baseline \(K(Mx)\) convention is recovered at any fixed prescribed \(M>0\) by rescaling the initial free kernel to \(K_{\rm initial}(v)=K(v/M)\). This is an existence statement allowing that initial choice, not a theorem about every previously fixed baseline. Assume \(G\) is smooth real even, supported in \([-A_G,A_G]\), \(G(0)=-K(0)\), and \(\widehat G\ge0\) outside \([-R,R]\). Such \(G\) exists, e.g. a positive scaling of \(-k_e''-D k_e\) with \(D>C_e\). Frequencies are free real parameters; one may choose \(T=\omega-h_n\). If a nonnegative carrier is desired, evenness of the cosine identifies opposite effective frequencies; a convention disallowing \(|\omega|<h_n\) would be an additional restriction.

**Continuous mixture.** For either endpoint law \(\nu\), its averaged numerator is exactly \(K(x)+G(x/L)\phi(x)\), supported in \([-s,s]\) for every \(L\). Thus every rational prime-power atom vanishes. It converges in every fixed compact smooth seminorm to \(K-K(0)\phi\). Both edge real parts are the ordinary Fourier transform of the numerator. On bounded \(14\le|t|\le Y\) convergence gives a relative lower bound \((d/2)\widehat K(t)\), since \(\widehat K\) has positive minimum there.

Uniformity at unbounded ordinates is essential. For a symmetric bounded truncation \(\nu_U=\nu\mathbf1_{[-U,U]}/\nu([-U,U])\) of mass retained at least \(1/2\), the potentially negative part of its edge correction is at most
\[
 \int L\widehat G_-(L(t-\omega))\nu_U(\omega)d\omega
 \le 2\|\widehat G_-\|_1\sup_{|u-t|\le R/L}\nu(u)
 \le C(E_e(t)+E_o(t))
\]
when \(L\ge R\). Meanwhile \(\widehat K(t)\ge c\delta(A+t^2)(E_e(t)+E_o(t))\). Choose \(Y\) large, once and for both endpoint laws. For \(|t|\ge Y\) the truncated edge is at least \(\widehat K(t)/2\), independently of \(U\). On \([14,Y]\) truncation changes the untruncated edge by at most \(2L\|\widehat G\|_\infty\nu(|\omega|>U)\). First choose \(L\) large enough for the compact convergence, both strict polar signs and the strictly positive arch bound, then \(U\) large enough at that \(L\). On the fixed compact interval this preserves a fixed fraction of the lower bound. The same estimates hold at negative ordinates.

**Correct all active prime atoms exactly.** For this fixed \(L\), list once the distinct numbers \(x_j=m\log p\le A_G L\), \(1\le j\le D_L\). Put \(v(\omega)=(\cos(\omega x_j))_j\), a bounded real vector, and observe \(\int v\nu=0\). There are a finite \(B_L\) and radius \(r_L>0\) such that the convex hull of \(v([-B_L,B_L])\) contains the closed ball \(\overline B(0,r_L)\). Indeed every nonzero linear combination has mean zero against a law positive on every open interval, and is not identically zero by independence of the cosines at distinct positive frequencies. It takes both signs. Compactness of the unit sphere, followed by the finite-dimensional separation theorem, supplies a common finite frequency interval and radius. When \(D_L=0\) omit the correction.

Choose \(B_L,r_L\) **before** fixing the final truncation \(U\). For \(e=\int v\nu_U\) one has \(\|e\|_2\le 2\sqrt{D_L}\,\nu(|\omega|>U)\). Choose a probability \(\sigma\) on \([-B_L,B_L]\) with vector mean \(-r_L e/\|e\|\), symmetrize it, and give it weight \(\tau=\|e\|/(r_L+\|e\|)\) in the truncation (take zero when \(e=0\)). The corrected compact law has vector mean exactly zero. Its edge on \(|t|>B_L+R/L\) retains the previous fraction of the baseline because the correction packet there is nonnegative. On \(14\le|t|\le B_L+R/L\) its possible downward effect is bounded by \(2\tau L\|\widehat G\|_\infty\); choose \(U\ge B_L\) so this is smaller than a fixed fraction of the previous bound times the minimum of \(\widehat K\) on the interval. The finite-frequency correction and truncated tails also preserve both strict scalar signs. For fixed \(L\) the polar functional per vertex is bounded by a constant depending on \(L,b\), and the arch functional is \(O_{L,b}(1+\omega^2)\): at the origin use evenness, the common value zero, and the sup-norm bound for the second derivative; the remaining integral is over a fixed compact interval. The original law is Schwartz and the correction support is fixed before choosing \(U\). Thus losses in these two quantities can be made arbitrarily small, e.g. \(1/L\), by further increasing \(U\).

**Finite positive quadrature without a zero list.** The corrected compact law has a lower bound \(d_0\widehat K(t)\) on every \(|t|\ge14\), with common \(d_0>0\). On the finite interval \(I=[14,U+R/L]\) take a deterministic mesh containing the endpoints. Every convex mixture, discrete or continuous, has an edge transform with derivative bounded by \(D=\|\widehat K'\|_\infty+L^2\|\widehat G'\|_\infty\). Let \(m_I=\min_I\widehat K>0\). Use mesh size at most \(d_0m_I/[2(D+d_0\|\widehat K'\|_\infty+1)]\). If the interval is empty, omit its mesh. By Carathéodory applied to the compact finite-dimensional image of \([-U,U]\), obtain a finite positive atomic probability integrating exactly all \(D_L\) prime coordinates, the two real scalar functionals (polar and arch), and the edge value at every mesh point. All are continuous in \(\omega\) at the fixed \(L\). For \(t\in I\) compare to the closest mesh value, using the derivative bounds for both the final edge and the baseline. This gives a lower bound \((d_0/2)\widehat K(t)\). At \(t>U+R/L\) all packets are nonnegative, and evenness gives the negative-ordinate result. No actual zeta ordinates are used for this discretization. [Classical positive quadrature, Bayer–Teichmann, Corollary 2](https://arxiv.org/abs/math/0502473)

Perform this construction for both fixed endpoints. Their finite mixtures have opposite actual polar moments. Combine them by the exact convex weight that makes the moment zero; evenness cancels both. This final finite probe still has \(H(0)=0\), all prime evaluations zero, and a common \(c\widehat K(\gamma)>0\) on every actual ordinate, with \(c\) independent of all sufficiently large \(n\). Only the final mixture needs this positivity. Choosing all approximation errors tending to zero shows its archimedean term tends to the strictly positive convex combination determined by the limiting poles. The finite mixtures are generally supported up to \(A_GL\); they vanish **at the prime atoms**. In contrast the direct tests vanish on the entire complement of a fixed short support. There is no explicit upper bound for the frequency cutoff or number of vertices here. The hull proof yields existence; it does not provide an economical search, and no bounds uniform over characters have been proved. The signed difference with the Hilbert traces at the edge widths remains to be evaluated.

## The exact cost of bounding the frequency window

A fixed bounded carrier range cannot realize this particular atom-by-atom cancellation at growing \(L\). If \(\Phi(z)=\sum a_j\cos(\omega_j z)\), \(a_j\ge0\), \(\sum a_j=1\), and \(|\omega_j|\le U\), then \(\Phi(0)=1\), \(|\Phi(z)|\le e^{U|\Im z|}\). If \(\Phi(\log p)=0\) for every \(p\le e^X\), Jensen's formula on the disk of radius \(2X\), by continuity in case of boundary zeros, gives
\[
 2\pi_{\rm primes}(e^X)\log2\le 4UX/\pi.
\]
The ordinary PNT implies \(U\ge(\pi\log2/2+o(1))e^X/X^2\). Since \(G(0)\ne0\), one may take \(X=aL\) for some fixed \(a>0\) whenever exact prime-atom vanishing is demanded. The constructive moment argument permits arbitrarily large frequencies; the lower bound explains why that permission matters. Killing only a signed aggregate need not force these transform zeros. This lower bound and the positive arch computation distinguish exact finite-prime cancellation from an all-width exterior-zero argument.
