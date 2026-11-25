# A prime-free explicit-formula test centered at a chosen height

At \(T=32\pi\), one compact smooth test and 32 disjoint Hardy-Z sign-change brackets prove that **exactly 15** ordinary zeta zeros, all simple and critical, have positive ordinate in \([32\pi-16,32\pi+16]\). Exactly 13 lie in the radius-15 subinterval and exactly one in the radius-one subinterval. The coarse certificate gives a strict margin greater than 0.0326 against any additional conjugate pair in the widest interval. As in the [original low-height pilot](../prime-free-positive-probe/README.md), this is a different verification within a classically known height range. No prior full zero count or indexed zero routine is an input.

[Interval verifier](verify.py) · [100-bit computation and exact sign brackets](receipt-100.txt) · [136-bit refined computation](receipt-136.txt)

## Construction at arbitrary heights

Take \(J=8\mathbf1_{[-1/16,1/16]}\), \(K_0=J^{*6}\), \(\epsilon=2^{-60}\), and \(K=K_0*\eta*\eta\) for the even normalized compact bump of radius \(\epsilon\) in the original pilot. Given real \(T\ge16\), put \(d=\pi/T\) and \(L(x)=\cos(Tx)K(x)\). Define
\[
 B_T(x)=2L(x)-L(x+d)-L(x-d),\qquad H_T(x)=B_T(x)/\cosh(x/2).
\]
Its support radius is at most \(3/8+2\epsilon+\pi/16<2/3<\log2\). Put \(F_T(w)=\int H_T(x)e^{wx}dx\). The real part on either boundary of the strip is
\[
 (1-\cos(dt))[\widehat K(t-T)+\widehat K(t+T)],\qquad
 \widehat K(s)=\operatorname{sinc}(s/16)^6\widehat\eta(s)^2.
\]
The boundary function is nonnegative and nonzero, and the two polar values vanish at \(t=0\). Uniform decay at large ordinates and the strong minimum principle imply strict positivity in the open strip. Thus the zeta explicit formula gives the total mass from the archimedean term alone.

In the entire closed strip, the single-zero real mass differs from its boundary value by at most \(4(1-\operatorname{sech}(1/3))\), by \(\|B_T\|_1\le4\) and evenness. For \(|t-T|\le1\), drop the nonnegative mirror lobe. Then \(1-\cos(dt)\ge2-(22/7)^2/512\), \(\operatorname{sinc}((t-T)/16)\ge1-1/(6\cdot16^2)\), and \(\widehat\eta(t-T)\ge1-\epsilon^2/2\). The error is at most \(2/9\) since \(1-\operatorname{sech}(x)\le x^2/2\). The resulting rational lower bound exceeds **\(7/4\) for all \(T\ge16\)**.

## Finite certificate

When \(T=32\pi\), the shift \(d=1/32\) exactly, and \(Td=\pi\) gives
\[
 H_T(x)=\cos(Tx) A_T(x),\qquad A_T(x)=\frac{2K(x)+K(x+d)+K(x-d)}{\cosh(x/2)}\ge0.
\]
The verifier constructs this envelope first with \(K_0\). Its polynomial numerator is computed from the positive-part cardinal spline formula on the thirteen intervals of length \(1/32\) between 0 and \(13/32\). As in the original pilot, range integration encloses the archimedean term and all the listed central masses over complete cells. The archimedean formula is
\[
 c[\psi(1/4)-\log\pi]+\int_0^A2e^{-x/2}\frac{c-H_T(x)}{1-e^{-2x}}dx+
 2c[\operatorname{artanh}(e^{-A/2})+\arctan(e^{-A/2})]
\]
with \(c=H_T(0)\); take \(A=13/32\) for the spline prototype and \(A=2/3\) for the true smoothed test. This is the standard rational specialization of the [Weil–Barner formula, Büthe §2](https://arxiv.org/pdf/1308.6704).

For the smoothing error of the envelope take
\[
 D_0=2\epsilon\cdot32\cdot16,\quad D_1=2\epsilon\cdot32(16^2+16/2),\quad
 D_2=2\epsilon\cdot32(16^3+16^2+16/4).
\]
The same box-derivative argument as in the first pilot bounds the zeroth through second derivatives of the envelope perturbation by these constants. Multiplication by the cosine gives the true-profile second derivative error bound \(D_2+2TD_1+T^2D_0\) and leaves the sup-norm bound \(D_0\). These bounds control the archimedean perturbation, including the removable origin singularity, and each central mass perturbation. The source treats these errors as unsigned intervals.

A mesh of step \(1/4\) in \([64,138]\) produces 32 provable Hardy-Z sign changes; bisection and direct evaluation certify disjoint rational brackets of width \(2^{-19}\). The receipts list both exact endpoints in units of \(2^{-19}\). Distinctness alone certifies 32 central zeros. An even test gives equal masses for each conjugate pair. Subtracting one copy of every listed pair leaves a residual smaller than 0.876 at 100 bits with 512 intervals per spline piece, and smaller than 0.440 at 136 bits with 1,024 intervals per piece.

For \(|t-T|\le D\) and \(D=1,15,16\), the boundary formula minus the global strip error gives the single-zero floor
\[
 (1+\cos(D/32))\operatorname{sinc}(D/16)^6[1-(\epsilon D)^2/2]^2
 -4[1-\operatorname{sech}(1/3)].
\]
Here sinc is decreasing on \([0,1]\) by its integral representation. The floors exceed 1.779, 0.55215 and 0.45417 respectively. The corresponding coarse conjugate-pair margins exceed 2.682, 0.228 and 0.0326. Therefore any additional zero, including a repeated listed zero in the slab, would exceed the residual. The closed-interval counts follow from the certified brackets. Both runs use python-flint 0.9.0. Run the verifier with its defaults and then with `--panels 1024 --precision 136`. This is an interval-arithmetic certificate with an analytic proof.

## Sample cost at unbounded target heights

Fix \(K\) and use the same family for all \(T\to\infty\). Let \(m=\int K(x)\operatorname{sech}(x/2)dx\). The archimedean total satisfies
\[
 V_T=4K(0)\log(T/(2\pi))+O_K(T^{-2}\log T).
\]
Indeed, \(A_T\) has uniformly bounded smooth compact-support seminorms and \(A_T(0)=4K(0)+O_K(T^{-2})\). In the Fourier version of the explicit formula,
\[
 V_T=\frac1{2\pi}\int_{\mathbb R}\widehat A_T(v)q(T+v)\,dv,\qquad
 q(s)=\Re\psi(1/4+is/2)-\log\pi.
\]
Both poles and all finite primes vanish. Stirling’s expansion gives \(q(s)=\log(|s|/(2\pi))+O(|s|^{-2})\) at infinity. For \(|v|<T/2\), \(q(T+v)=\log(T/(2\pi))+v/T+O((1+v^2)/T^2)\). Evenness cancels the linear term; uniform Schwartz decay handles the complementary tail since \(q\ll\log(2+|s|)\). Fourier inversion gives the displayed coefficient. [Digamma asymptotic, DLMF (5.11.2)](https://dlmf.nist.gov/5.11#E2)

Each sampled positive-height central conjugate pair contributes
\[
 2F_T(i\gamma)=\widehat A_T(\gamma-T)+\widehat A_T(\gamma+T)
 \le 4m+O_K(T^{-2})
\]
uniformly in \(\gamma>0\). The first term is at most \(\int A_T=4m+O_K(T^{-2})\) by nonnegativity, and the mirror term is \(O_{K,N}(T^{-N})\) for every fixed \(N\). Each hypothetical off-line symmetry quartet costs at most 16, since \(\cosh(ax)/\cosh(x/2)\le1\) and the nonnegative numerator of \(A_T\) has mass four. Therefore a residual-versus-one-orbit certificate from \(n_T\) sampled positive-height line multiplicities at growing targets necessarily has
\[
 \liminf\frac{n_T}{\log T}\ge K(0)/m.
\]
The liminf is over the targets where such certificates succeed. Here \(m\le1\), \(K_0(0)=22/5\) by its exact polynomial, and \(|K(0)-K_0(0)|\le256\epsilon\), so eventually at least \(4.39\log T\) sample multiplicities are necessary. A fixed finite sample instead contributes \(O_{K,N}(T^{-N})\) for every \(N\). These estimates account for an increasing archimedean mass even while the single-zero sensitivity stays above \(7/4\). They establish a limitation of the raw positive-sum subtraction method, with no implication about previously unverified zero heights.
