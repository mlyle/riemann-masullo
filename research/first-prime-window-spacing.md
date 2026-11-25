# Bounded first-prime errors in every sufficiently late power interval

25 November 2026. For the rational principal character in Theorem 12.5.1.1, pp. 519–520, set
\[
 w(t)=2-\cos t-\cos(\sqrt2t),\qquad
 E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log t)\,dt.
\]
For every fixed \(\varepsilon>0\) and all sufficiently large real \(X\), there are integers \(m<n\) in \([X,X^{1+\varepsilon}]\) with
\[
 E(m)>0.19\sqrt m,\qquad E(n)<-4.64\sqrt n.
\]
The interval therefore contains an integer \(N\) with \(-4<E(N)\le0\). Both statements also hold with the discrete mean \(\sum_{j\le N}w(\log j)\), with its own cutoffs. The continuous mean has a real-cutoff zero there. In particular, the increasing sequence of all bounded-error integers for either convention satisfies \(\log N_{j+1}/\log N_j\to1\). The threshold in \(X\) may depend on \(\varepsilon\). This is a classical argument. Its finite numerical input has independently replayed rigorous Arb enclosures. [Earlier crossing theorem, Mellin normalization, verifier and receipts](https://github.com/mlyle/riemann-masullo/tree/8653a3a595b5f123342c26c8e863cf1e16922f10/research/5571/two-cosine-fejer-crossings).

## Mellin data

Put \(a=1/2\) and \(g(u)=e^{-au}E(e^u)\) for \(u\ge0\), extended by zero for \(u<0\). We have \(|g(u)|\ll (1+u)e^{u/2}\) for \(u\ge0\) by bounding the first-prime sum by the sum over all integers. The Laplace transform of \(g\) is \(M(a+z)\) on \(\Re z>1/2\), where
\[
 M(s)=\frac1s\sum_{t\in\{0,\pm1,\pm\sqrt2\}}c_t
 \left(P(s-it)-\frac1{s-1-it}\right),\qquad
 P(s)=\sum_p\log(p)p^{-s},
\]
with \(c_0=2\) and the four other coefficients \(-1/2\). With \(L=-\zeta'/\zeta\), the identity
\[
 P(s)=L(s)-L(2s)+\sum_{k\ge2}P(2ks)-\sum_{k\ge3}P(ks)
\]
continues \(M\) meromorphically to \(\Re s>1/3\). The two tails converge normally there and the density poles cancel. Every pole in the rectangles below is simple, with contributions at coincident ordinates combined. In \(|\Im z|\le T=200\), between \(\Re z=-1/9\) and \(1\), all poles are on \(\Re z=0\). For \(L(s-it)\) this uses the verified zeros at heights up to \(T+\sqrt2\). For \(L(2s-2it)\), the corresponding height is \(2(T+\sqrt2)\), and its real part is greater than \(2/3\), so only its pole at one can contribute. No pole is at the band endpoints. These finite-height facts follow from the verified zeta zero list and the certified ordinate comparisons. [Platt and Trudgian, verification through height \(3\cdot10^{12}\)](https://arxiv.org/abs/2004.09765) · [Finite signed residue computation](https://github.com/mlyle/riemann-masullo/blob/8653a3a595b5f123342c26c8e863cf1e16922f10/research/5571/two-cosine-fejer-crossings/spectral-interpolation-two-cosine-crossings-fejer.py).

Write \(\Phi(v)=(1-|v|/T)_+\), and \(K(u)=(1-\cos(Tu))/(\pi T u^2)\), extended continuously at zero. This is the nonnegative inverse Fourier transform of \(\Phi\) with mass one. For the actual residues \(R_{i\gamma}=\operatorname{Res}_{z=i\gamma}M(a+z)\), the real trigonometric polynomial
\[
 Q(y)=\sum_{|\gamma|<T}R_{i\gamma}\Phi(\gamma)e^{i\gamma y}
\]
has certified values greater than \(0.19927\) and less than \(-4.64898\). These evaluations use 797 contributions, including the square-prime terms.

## A positive localized average

It suffices to take \(0<\varepsilon\le1\). Set \(\eta=\varepsilon/20\), and take \(\lambda\in[\eta^2/8,\eta^2/4]\), with its exact choice specified below. For \(y>0\), define
\[
 B(y)=\int_0^\infty g(u)K(y-u)\exp[-(y-u)^2/(2\lambda y)]\,du.
\]
The kernel is positive and has mass tending to one on \(|u-y|\le\eta y\) by dominated convergence. The contribution outside this interval is \(o(1)\), even with the absolute value of \(g\). Indeed, writing \(u=y(1+v)\) gives the exponential bound \(\exp(y[(1+v)/2-v^2/(2\lambda)])\) times a polynomial. For \(v\ge\eta\) the exponent in brackets starts below \(-1\) and has derivative at most \(-1\). On \(-1\le v\le-\eta\) it stays below \(-1\).

The bilateral Laplace multiplier of the Gaussian times \(K\) is entire and equals
\[
 H_y(z)=\sqrt{\frac{\lambda y}{2\pi}}\int_{-T}^T
 \Phi(v)\exp\left(\tfrac12\lambda y(z-iv)^2\right)\,dv .
\]
Fourier inversion on the initial line \(\Re z=1\) gives
\[
 B(y)=\frac1{2\pi i}\int_{1-i\infty}^{1+i\infty} M(a+z)e^{zy}H_y(z)\,dz .
\]
Fubini follows from \(e^{-u}g(u)\in L^1\) and Gaussian decay of the multiplier on that line. Equivalently, invert the Fourier transform of \(e^{-v}K(v)e^{-v^2/(2\lambda y)}\) and then integrate against \(e^{-u}g(u)\).

Choose a fixed pole-free height \(A>T\) so large that \((\eta^2/8)(A-T)^2/2>3\). Choose a pole-free vertical edge \(-1/9<\ell<-1/12\) for the rectangle \(\ell\le\Re z\le1, |\Im z|\le A\). The original line tails tend to zero since \(M(a+1+it)\) is bounded and the Gaussian has exponent at most \(y[1+\lambda/2-\lambda(|t|-T)^2/2]\). The horizontal edges have the same upper bound with \(|t|=A\), up to a fixed constant and a factor \(O(\sqrt y)\). On the left edge the exponent is at most \(y(\ell+\lambda\ell^2/2)<0\). The meromorphic function is bounded on each compact pole-free edge. Consequently,
\[
 B(y)=\sum_{z_j} R_j e^{z_jy}H_y(z_j)+o(1)
\]
over the finite set of actual poles inside the rectangle, with \(R_j\ne0\). This move needs no assumption on the positions of high zeta zeros. The poles of \(L(2s-2it)\) are included in the same finite accounting.

## Possible poles outside the finite certificate

For \(z=i\gamma\) in the original band, \(H_y(i\gamma)\to\Phi(\gamma)\) by the Gaussian approximate identity. For an upper pole \(z=\alpha+i\gamma\), \(\gamma>T\), there is a nonzero constant \(C_z\) with
\[
 e^{zy}H_y(z)=C_z y^{-3/2}\exp\left(y\left[z+\tfrac12\lambda(z-iT)^2\right]\right)(1+o(1)).
\]
To see this, put \(v=T-h/y\). On \(0\le h\le Ty\) the triangular weight equals \(h/(Ty)\). After factoring the displayed exponential, the remaining scaled integral tends to
\[
 C_z=\frac{\sqrt{\lambda/(2\pi)}}{T}\int_0^\infty h e^{i\lambda(z-iT)h}\,dh
 =\frac{\sqrt{\lambda/(2\pi)}}{T[-i\lambda(z-iT)]^2}.
\]
The part corresponding to \(v<0\) tends to zero under the same scaling, since \(y\Phi(T-h/y)\le h/T\) on \(0\le h\le2Ty\) and the absolute integrand is dominated by a constant times \(h e^{-\lambda(\gamma-T)h}\). The lower poles give the conjugates.

The effective real exponent for an exterior upper pole is
\[
 q_z(\lambda)=\alpha+\tfrac12\lambda[\alpha^2-(\gamma-T)^2].
\]
Distinct upper poles give different affine functions of \(\lambda\): differing real parts give different intercepts, and for equal real parts their positive distances \(\gamma-T\) differ. Pick \(\lambda\) in the original interval outside the finite set of pairwise ties. If every exterior exponent is nonpositive, their sum tends to zero and \(B(y)=Q(y)+o(1)\). The positive and negative values of \(Q\) recur with bounded gaps in \(y\), since the translation flow of a finite list of frequencies has compact closure and every neighborhood of one attained phase has relatively dense return times.

If some exponent is positive, one upper pole and its conjugate have the largest exponent \(q\). Their leading term gives
\[
 B(y)=e^{qy} y^{-3/2}\bigl(2\Re(R_z C_z e^{i\omega y})+o(1)\bigr),
 \qquad \omega=\gamma+\lambda\alpha(\gamma-T)>0 .
\]
Here \(\alpha>\ell>-1/9\) and \(\lambda<1\). The coefficient is nonzero. On relatively dense sets of times the sinusoid is strictly positive or strictly negative by a fixed margin. Thus in both cases every sufficiently late log-time interval of a fixed large length contains times with \(B(y)>0.195\) and times with \(B(y)<-4.645\). All constants may depend on the chosen \(\varepsilon\).

## From averages to cutoffs

Let \(Y=\log X\). Choose a positive time within a bounded distance of \((1+\varepsilon/4)Y\), and a negative time within a bounded distance of \((1+3\varepsilon/4)Y\). Their physical log windows of radius \(\eta y\) are disjoint, in that order, and strictly inside \([Y,(1+\varepsilon)Y]\) for large \(Y\). Positivity, the localized mass limit one and the absolute tail bound give an earlier value of \(g\) greater than \(0.19\) and a later one less than \(-4.64\), with room to spare. Returning to integer cutoffs changes the integral-centered error by at most four and the square-root normalization by a relative \(o(1)\). At integers the two mean conventions differ by \(O(\log N)\), since the derivative of \(w(\log x)\) is \(O(1/x)\). Both effects preserve the two strict bounds using the margins above.

For each mean the discrete arithmetic mass increases and the mean grows by at most four per step. The first nonpositive integer after the positive witness therefore has \(-4<E(N)\le0\). For the integral mean the error is continuous between primes and has only upward jumps, so passage to a later negative value attains zero on the real axis. Taking \(X=N_j+1\) gives \(N_{j+1}\le(N_j+1)^{1+\varepsilon}\) eventually for each fixed \(\varepsilon\), yielding the logarithmic spacing limit. The witness can be chosen away from the two ends of the power interval, so its full radius-\(\lfloor\sqrt N\rfloor\) good window from the Brun–Titchmarsh argument lies inside the power interval as well. Power-interval spacing still allows very long gaps relative to \(\sqrt X\). The all-cutoff estimate for zero exclusion remains open.
