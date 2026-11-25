# One prime-free rational trace probe certifying a complete low-height slab

There is exactly one nontrivial zero of the ordinary Riemann zeta function with positive imaginary part in \([4,19]\). It is simple, on the critical line, and has ordinate in \((14.134724,14.134726)\). This bounded pilot recovers this known result from **one prime-free compact smooth profile, one Hardy-Z sign change, and the signed archimedean value**. The argument uses no input about the completeness of any published zero list and no global assumption about zeros. It verifies the arithmetic use of the positive trace criterion in a range previously covered by [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765).

[Self-contained interval verifier](verify.py) · [100-bit certificate](receipt-100.txt) · [144-bit, doubled-mesh certificate](receipt-144.txt)

## The test and its analytic proof

Let \(h=1/8\), \(d=1/4\), \(\epsilon=2^{-60}\), and \(J=h^{-1}\mathbf 1_{[-h/2,h/2]}\). Define \(\eta\) to be the mass-one even bump proportional to \(\exp[-1/(1-(x/\epsilon)^2)]\) on \(|x|<\epsilon\), extended by zero. Put
\[
 K_0=J^{*6},\quad K=K_0*\eta*\eta,\quad
 B(x)=2K(x)-K(x-d)-K(x+d),\quad H(x)=B(x)/\cosh(x/2).
\]
This construction first picks the support, then kills the polar moments. Its support radius is at most \(5/8+2\epsilon< A=2/3<\log2\), so its prime-power sum is exactly empty. Its bilateral Laplace transform is \(F(w)=\int H(x)e^{wx}dx\). On either boundary \(\Re w=\pm1/2\),
\[
 \Re F(\pm1/2+it)=2(1-\cos(t/4))\operatorname{sinc}(t/16)^6\widehat\eta(t)^2\ge0.
\]
At \(t=0\) both actual complex polar values are zero by evenness. The real part is strictly positive in the open strip. In detail, \(H\) is compact smooth, so its transform tends to zero uniformly at large positive and negative ordinates on the closed strip by integration by parts. The minimum principle on finite rectangles and then the strong minimum principle give positivity because the boundary function is nonnegative and not identically zero. This also makes every omitted zeta zero contribute positive mass.

For \(|a|\le1/2\), evenness and \(\|B\|_1\le4\) give the uniform lower bound
\[
 \Re F(a+it)\ge
 2(1-\cos(t/4))\operatorname{sinc}(t/16)^6\widehat\eta(t)^2
 -4(1-\operatorname{sech}(A/2)).
\]
In the tested ranges \(\widehat\eta(t)\ge 1-(\epsilon t)^2/2>0\) by \(\cos z\ge1-z^2/2\). Outward-rounded interval evaluations over every height cell of width \(1/32\) prove a common one-zero floor \(1119/5000=0.2238\) on \([4,19]\), and \(539/1250=0.4312\) on \([5,18]\). Neither bound samples a discrete set of candidate zero heights.

## Signed local mass and one certified central zero

For \(c=H(0),\ q=e^{-A/2}\), the rational explicit formula with both poles and all finite places vanishing is
\[
 V=c(\psi(1/4)-\log\pi)+\int_0^A 2e^{-r/2}\frac{c-H(r)}{1-e^{-2r}}dr
       +2c(\operatorname{artanh}q+\arctan q).
\]
This is the real sum of \(F(\rho-1/2)\) over all nontrivial zeta zeros with multiplicities. The signs and the factor of two follow directly from [Büthe, §2, rational Euler factor and real gamma factor](https://arxiv.org/pdf/1308.6704). Büthe’s Theorem 3.2 is the earlier positive-test completeness method. Its particular test is a different family.

For evaluation, use \(B_0=2K_0-K_0(\cdot-d)-K_0(\cdot+d)\) and \(H_0=B_0/\cosh(\cdot/2)\). The cardinal spline is computed in exact rationals on the five positive intervals of length \(h\), using
\[
 K_0(x)=\frac{1}{5!h^6}\sum_{j=0}^6(-1)^j {6\choose j}(x+(3-j)h)_+^5.
\]
Writing \(E=H-H_0\), the verifier uses
\[
 \|E\|_\infty\le D_0=2\epsilon\cdot32\cdot16,\qquad
 \|E''\|_\infty\le D_2=2\epsilon\cdot32(16^3+16^2+16/4).
\]
Indeed one derivative of the normalized box has distributional total variation \(2/h=16\); placing each derivative on a separate factor gives \(\|K_0^{(j)}\|_\infty\le8\cdot16^j\) for \(j\le3\). Translation by at most \(2\epsilon\) bounds the mollification error by the corresponding derivative norm times \(2\epsilon\). The second difference has operator norm at most four and the zeroth through second derivative norms of \(\operatorname{sech}(x/2)\) are at most \(1,1/2,1/4\). Thus the central transform error is at most \(2AD_0\), and the archimedean mass error is at most
\[
 |\psi(1/4)-\log\pi|D_0+
 \tfrac14D_2(1+2A)A^2+2D_0(\operatorname{artanh}q+\arctan q)
 <7.1\cdot10^{-14}.
\]
Here \(|E(0)-E(r)|\le D_2r^2/2\) by evenness and \(2e^{-r/2}/(1-e^{-2r})\le(1+2A)/r\). The prototype is integrated by range enclosures on each cell, with the removable singularity in the first cell bounded by the same estimate using \(\|H_0''\|_\infty\le32(16^2+16+1/4)\). The prototype archimedean tail starts at \(5/8\) exactly. These integrals are bounded on every full cell, including between the evaluation centers.

The verifier uses the functional equation to write the real Hardy function as \(Z(t)=e^{i\theta(t)}\zeta(1/2+it)\), with \(\theta(t)=\Im\log\Gamma(1/4+it/2)-\frac12t\log\pi\). At the two **exact rational** bracket endpoints, Arb encloses the first value strictly below zero and the second strictly above zero. This certifies one central zero \(\gamma_*\) in the interval without using a zero counting or indexing function. The central integral \(F(i\gamma_*)=2\int_0^{5/8}H_0(r)\cos(r\gamma_*)dr+O(2AD_0)\) is enclosed over the whole bracket. [FLINT interval complex arithmetic](https://python-flint.readthedocs.io/en/latest/acb.html)

At 100 bits and 4,096 integration intervals per polynomial piece, \(3.84838<V<3.86011\), \(1.72202<F(i\gamma_*)<1.72389\), and \(V-2F(i\gamma_*)<0.41605<21/50\). The independently rerun 144-bit check with 8,192 intervals per piece gives \(V-2F(i\gamma_*)<0.41219\). The second run is the same mathematical algorithm with higher precision and finer enclosures.

Every extra positive-height zero in \([4,19]\) and its conjugate would cost more than \(2(1119/5000)\), including any extra copy of the certified line zero. This exceeds the admissible residual by more than **\(69/2500=0.0276\)**. In \([5,18]\) the guaranteed margin is **\(553/1250=0.4424\)**. The entire positive-height slab is therefore complete, including simplicity. The source is a classical proof with certified Arb arithmetic, not a Lean proof. To reproduce both receipts use Python with python-flint 0.9.0 and run the verifier at its defaults, then with `--panels 8192 --precision 144`.
