# Eventual negativity of an actual signed first-prime square prefix

Let \(w(t)=2-\cos t-\cos(\sqrt2t)\), let \(E(x)=\sum_{p\le x}\log p\,w(\log p)-\int_1^x w(\log t)dt\), and put \(A(K)=\sum_{k=1}^K E(k^2)\). The following three statements are equivalent classically.

1. All nontrivial ordinary zeta zeros have real part \(1/2\).
2. \(\int_1^X E(t)dt\le0\) for every sufficiently large real \(X\).
3. \(A(K)\le0\) for every sufficiently large integer \(K\).

Statement 3 is equivalent with the discrete mean \(\sum_{n\le k^2}w(\log n)\) in place of the integral as well. In the forward direction the eventual bounds strengthen to \(\int_1^X E(t)dt<-0.69 X^{3/2}\) and \(A(K)<-0.63 K^2\). No rate assumption appears in the converses.

**Unconditionally**, \(\int_1^X E(t)dt<-0.0315X^{3/2}\) for every real \(10^{10}\le X\le10^{18}\), and even \(<-0.5944X^{3/2}\) on \(10^{14}\le X\le10^{16}\). A separate prime sieve gives \(A(K)/K^2<-1.1590\) for every integer \(20\le K\le512\) with the integral mean, and \(<-1.1679\) there with the discrete mean. Eventual negativity remains open.

## Exact weighted Riesz formula

Write \(a=1/2\), \(S=\{0,\pm1,\pm\sqrt2\}\), \(c_0=2,\ c_{t\ne0}=-1/2\), \(L=-\zeta'/\zeta\), and \(B_\alpha(X)=\alpha\int_1^X E(u)u^{\alpha-1}du\) with \(\alpha\in\{1,1/2\}\). The kernel attached to a jump at \(y\le X\) is \(X^\alpha-y^\alpha\). For a single frequency let
\[
 P_{\alpha,t}(X)=\sum_{n\le X}\Lambda(n)n^{it}(X^\alpha-n^\alpha).
\]
On \(\Re z=2\), Mellin inversion of \((1-u^\alpha)_+\) gives the absolutely convergent integral with integrand \(\alpha L(z-it)X^{z+\alpha}/[z(z+\alpha)]\) and factor \(1/(2\pi i)\). The kernel vanishes at \(u=1\), so there is no endpoint convention for a jump at \(X\). Moving the contour left gives the exact formula for \(X>1\)
\[
\begin{split}
 P_{\alpha,t}(X)={}&\frac{\alpha X^{1+it+\alpha}}{(1+it)(1+it+\alpha)}
 -\alpha\sum_\rho\frac{X^{\rho+it+\alpha}}{(\rho+it)(\rho+it+\alpha)}\\
 &+X^\alpha L(-it)-L(-\alpha-it)
 -\alpha\sum_{j\ge1}\frac{X^{-2j+it+\alpha}}
 {(-2j+it)(-2j+it+\alpha)} .
\end{split}
\]
Zeros are counted with multiplicity. The pole at \(z=1+it\) has positive residue in \(L(z-it)\), all its zero residues are negative, and both kernel poles have the written signs. Each of \(\zeta(-it)\), \(\zeta(-\alpha-it)\) is nonzero, by the functional equation and the one-line zero-free theorem (including \(\zeta(0)=-1/2\)). For justification of the shift, take horizontal truncation heights going to infinity a distance \(\gg1/\log T\) from the finite union of translates of zeta-zero heights. Such heights exist using \(N(T+1)-N(T)=O(\log T)\). On any fixed horizontal strip between the two vertical lines, the standard local partial-fraction bound for \(\zeta'/\zeta\) then gives \(O_R(\log^2 T)\), so division by the quadratic denominator kills the horizontal integrals. Send the left vertical line through \(\Re z=-2j-1/2\). The functional equation and absolute convergence on the reflected right line bound \(L(z-it)\) there by \(O(\log(2+|\Re z|+|\Im z|))\), uniformly in \(j\); the distance from the trivial zeros controls the sine/cotangent term. The last vertical integral vanishes since \(X>1\). All displayed zero sums converge absolutely for fixed \(X\) by ordinary zero counting. [Hadamard's product and the one-line theorem](https://www.numdam.org/item/BSMF_1896__24__199_1/) · [Classical local logarithmic-derivative bounds as in Bellotti, Lemma 2.2](https://arxiv.org/html/2508.02041).

The first displayed term is \(\int_0^X y^{it}(X^\alpha-y^\alpha)dy\). Replacing \(0\) by \(1\) when subtracting the physical mean changes the weighted result by at most \(4X^\alpha\). The sum with \(k\ge2\) must be subtracted from the result for \(\Lambda\): it is the positive weighted contribution of all composite prime powers and kernel \(X^\alpha-p^{k\alpha}\). Its unconditional first-order Riesz expansion, divided by \(X^{a+\alpha}\), is
\[
 D_\alpha-\alpha\Re\sum_{t\in\{1,\sqrt2\}}
                 \frac{X^{it}}{(1+2it)(a+\alpha+it)}+o(1),
 \qquad D_\alpha=\frac{2\alpha}{a+\alpha}.
\]
Indeed the full unsmoothed composite sum divided by \(\sqrt x\) is \(2-\Re\sum_{t=1,\sqrt2}x^{it}/(1+2it)+o(1)\), by the prime number theorem at the two fixed frequencies and the elementary \(k\ge3\) bound. Integrating its \(o(\sqrt x)\) remainder against \(\alpha x^{\alpha-1}\) gives \(o(X^{a+\alpha})\). [Native full composite-prime asymptotic](https://github.com/mlyle/riemann-masullo/compare/951a318969dfccd6fbbac6687124ff330b626d13...50c33a73a02c4eca003b1d82b2abbaba752a0429).

## All-height sign margin when the zeros are critical

The Hadamard expansion of \(\xi\) gives the absolutely convergent identity \(\sum_\rho [\rho(1-\rho)]^{-1}=2+\gamma_E-\log(4\pi)=Z\). Indeed the left side is \((\xi'/\xi)(1)-(\xi'/\xi)(0)=2(\xi'/\xi)(1)\). Taking the logarithmic derivative of \(s((s-1)\zeta(s))\pi^{-s/2}\Gamma(s/2)/2\) at 1 gives \(1+\gamma_E/2-\log(4\pi)/2\). If the zeros are critical this is the identity \(\sum_\rho|\rho|^{-2}=Z\). The lowest indexed zero has imaginary part greater than 14. Thus, for every \(t\in S\),
\[
 |\rho+\alpha+it|\ge|\rho+it|\ge(1-\sqrt2/14)|\rho|.
\]
Since \(\sum_{t\in S}|c_t|=4\), the normalized entire true-zero contribution is at most \(4\alpha Z/(1-\sqrt2/14)^2\). The total rotating prime-square amplitude is
\[
 V_\alpha=\alpha\sum_{t=1,\sqrt2}
    \frac{1}{|1+2it|\,|a+\alpha+it|}.
\]
The kernel poles and trivial-zero sum contribute \(o(X^{a+\alpha})\). Therefore \(\limsup B_\alpha(X)/X^{a+\alpha}\le-D_\alpha+V_\alpha+4\alpha Z/(1-\sqrt2/14)^2\). At \(\alpha=1\) the positive excess \(D_\alpha-V_\alpha-4\alpha Z/(1-\sqrt2/14)^2\) exceeds \(0.69495217356\), and at \(\alpha=1/2\) it exceeds \(0.63135043517\). This proves both eventual strict bounds with the advertised slightly smaller margins once the square-prefix identity below is used. [128-bit constants](conditional-margin-128.txt) · [192-bit constants](conditional-margin-192.txt) · [Verifier](conditional-margin.py).

## Exact square prefix and the sign-only converse

Write \(dA(t)=\sum_p\log(p)w(\log p)\delta_p-w(\log t)dt\) and \(q(t)=\lceil\sqrt t\rceil-\sqrt t-1/2\). Interchanging the \(k\)-sum with this measure gives, **exactly** when \(X=K^2\),
\[
 A(K)-B_{1/2}(X)=\tfrac12 E(X)-\int_{1}^{X}q(t)\,dA(t).
\]
Indeed the discrete and integrated kernels on \(t\le K^2\) are respectively \(K-\lceil\sqrt t\rceil+1\) and \(K-\sqrt t\). The ordinary PNT gives \(E(X)=o(X)\) by partial summation. The centered square-root rounding factor has \(\int_1^Xq\,dA=o(X)\) by Zhai's prime discrepancy theorem; the continuous part is \(O(\sqrt X)\) via a bounded primitive of the sawtooth. Thus \(A(K)=B_{1/2}(K^2)+o(K^2)\) unconditionally. Replacing every integral mean \(E(k^2)\) by the discrete mean changes the prefix by \(O(K\log(2K))=o(K^2)\). [Prime rounding proof and source](https://github.com/mlyle/riemann-masullo/tree/4d9dea99a39d3b2476f777c4bae0c6c659d9bf8c/research/5571/sparse-prime-cutoffs).

Initially for \(\Re z>1+\alpha\), Fubini gives \(\int_1^\infty B_\alpha(X)X^{-z-1}dX=\alpha M(z-\alpha)/z\), where \(M(s)=\int_1^\infty E(x)x^{-s-1}dx\). The meromorphic \(M(s)\) is regular for all real \(s>1/2\): the five shifted zeta poles cancel the five mean-density poles, and the first zero ordinate exceeds 14. This real-axis property is unconditional. If \(B_1\le0\) eventually, Landau's positive-transform theorem on the tail \(-B_1\) gives absolute convergence and analytic continuation on \(\Re z>3/2\). Hence \(M\) is holomorphic for \(\Re s>1/2\).

If instead \(A(K)\le0\) eventually, the exact prefix comparison gives \(B_{1/2}(K^2)\le o(K^2)\), for either choice of compensator. For \(K^2\le X<(K+1)^2\), the additional integral is \(o(X)\) uniformly because \(E(t)=o(t)\), \(t^{-1/2}\asymp X^{-1/2}\), and the interval has length \(O(\sqrt X)\). Thus \(X-B_{1/2}(X)\) is eventually nonnegative. Its tail Mellin transform is \(1/(z-1)-M(z-1/2)/(2z)\) up to an entire function; it is regular on the real interval \(z>1\). Landau gives absolute convergence on \(\Re z>1\), so \(M\) is again holomorphic on \(\Re s>1/2\). In either case \(sM(s)\) differs by a holomorphic function from the two-cosine combination of pole-corrected logarithmic zeta derivatives there. Its residues imply four-neighbor harmonicity of the nonnegative zero multiplicities under shifts by \(1,\sqrt2\). Local finiteness, density and propagation from a zero multiplicity rule out all positive multiplicities in this half-plane. The functional equation reflects the remaining half of the critical strip. [Native Landau result](https://github.com/mccorvie/riemann-masullo/pull/7555) · [Rational zero detector](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521).

## Unconditional finite-height interval

Take \(H=3\cdot10^{12}\). All zeros through that height are critical. The low sum of \(|\rho|^{-2}\) is at most \(Z\) even without global RH: every summand \(1/[\rho(1-\rho)]\) has positive real part because \(\Re(\rho(1-\rho))=\beta(1-\beta)+\gamma^2>0\), and the low summands are positive real. For \(u\ge H\), the explicit counting estimate of Hasanalizade, Shen and Wong gives \(N(u)\le u\log u\) for the positive ordinates. Integrating by parts gives \(\sum_{|\gamma|>H}\gamma^{-2}\le4(\log H+1)/H\). For these zeros both shifted denominators have modulus at least \((1-\sqrt2/H)|\gamma|\) and \(\beta\le1\). After normalization the high-zero contribution is therefore at most
\[
 \frac{16\alpha\sqrt X(\log H+1)}{H(1-\sqrt2/H)^2}.
\]
[Platt and Trudgian's verified height](https://arxiv.org/abs/2004.09765) · [Explicit zero count](https://arxiv.org/abs/2107.06506).

For an **upper** bound on \(B_\alpha\), it suffices to subtract the actual prime squares, since the higher composite terms are nonnegative. Set \(Y=\sqrt X\) and \(f(y)=w(2\log y)(1-(y/Y)^{2\alpha})\). Its endpoint values at 1 and \(Y\) are zero. For \(1\le y\le Y\), \(|f'(y)|\le D'/y\), \(D'=2(1+\sqrt2)+8\alpha\). Chebyshev bounds give \(|\theta(y)-y|\le y\) below 599. Above 599, Johnston's theorem supplies \(\sqrt y\log^2y/(8\pi)\) through \(1.101\cdot10^{26}\), which exceeds all \(Y\) used here. Partial summation gives the following full bound on replacing the normalized square sum by its integral from 0 to \(Y\):
\[
 D'\left(598/Y+\frac{\log^2Y}{4\pi\sqrt Y}\right)+4/Y.
\]
Here the last term pays for \([0,1]\). The integral from 0 can be evaluated exactly by elementary complex powers: it is \(D_\alpha-\alpha\Re\sum_{t=1,\sqrt2} X^{it}/[(1+2it)(a+\alpha+it)]\), after normalization. Both error terms above decrease for \(Y>e^4\). [Johnston, Theorem 3.2 and Corollary 3.3](https://arxiv.org/pdf/2109.02249).

Finally the normalized Riesz endpoints plus omitted \([0,1]\) density integrate to at most
\[
 \frac{4+\sum_{t\in S}|c_t|(|L(-it)|+|L(-\alpha-it)|)
                  +4\alpha/(X^2-1)}{\sqrt X}.
\]
The last term bounds the convergent trivial-zero series using \(2j(2j-\alpha)\ge1\). The verifier encloses each finite zeta derivative divided by zeta, all elementary constants and the monotone worst-case endpoints. The resulting unconditional uniform negative margins are as follows.

| Range of real \(X\) | \(-B_1(X)/X^{3/2}\) exceeds | \(-B_{1/2}(X)/X\) exceeds |
|---|---:|---:|
| \(10^{10}\le X\le10^{18}\) | 0.0315 | 0.2046 |
| \(10^{14}\le X\le10^{16}\) | 0.5944 | 0.5651 |

These entries concern the continuous Riesz means. A separate sieve and exact elementary formula for the mean at square cutoffs certify the finite signed prefixes in the opening paragraph, without estimating their rounding discrepancy. The sieve uses all 23,000 primes through \(512^2=262144\); the unconditional finite statements do not require a zeta assumption outside the published verification height. [Finite-range verifier](finite-riesz.py) · [128-bit receipt](finite-riesz-128.txt) · [192-bit receipt](finite-riesz-192.txt) · [Square-prefix verifier](finite-square-prefix.py) · [128-bit sieve receipt](finite-square-prefix-128.txt) · [192-bit sieve receipt](finite-square-prefix-192.txt).

The analytic derivations on this page are classical. Arb verifies the displayed numerical enclosures; they are separate from the existing native Lean detector and crossing lemmas. The open step is proving either sign criterion at every sufficiently large cutoff.



Replay each verifier with `uv run --no-project --with python-flint==0.9.0 python SCRIPT.py --precision 192`, replacing SCRIPT with `conditional-margin`, `finite-riesz` or `finite-square-prefix`.

## Locating an exterior zero from a finite discrepancy

For \(X>1\), add the exactly computable nonnegative composite prime powers to \(B_\alpha(X)\). Divide by \(X^{1/2+\alpha}\), subtract the terms other than the nontrivial-zero sum of the exact formula (the integral over \([0,1]\), the two kernel residues and the trivial-zero series), and subtract the full signed contribution from ordinary zeta zeros with \(|\gamma|\le H=3\cdot10^{12}\). Write \(R\) for the absolute value of the result. It is exactly the absolute value of the high-zero tail. A certified lower bound on \(R\) suffices below. The low zeros can alternatively be handled at once by subtracting their absolute upper bound \(4\alpha Z/(1-\sqrt2/14)^2\) from the absolute value prior to the low-zero subtraction.

Set \(T_\alpha(u)=16\alpha(\log u+1)/(u(1-\sqrt2/u)^2)\). For any \(G>H\) and \(0\le\delta<1/2\), the strict inequality
\[
 R>X^\delta T_\alpha(H)+\sqrt X\,T_\alpha(G)
\]
forces an ordinary zeta zero with \(H<|\gamma|\le G\) and \(\beta>1/2+\delta\). Indeed, in the absence of such a zero the normalized powers on the intermediate band all have modulus at most \(X^\delta\). The global bound \(\beta\le1\) pays for the part beyond \(G\). The same inverse-square count and shifted denominator bounds used above give the two displayed terms. If there is no upper cutoff, \(R>X^\delta T_\alpha(H)\) suffices to force an ordinate above \(H\). No discrepancy meeting either strict test has been certified here.

## A million consecutive large square-prefix cutoffs

For every integer \(10^7\le K\le 11\cdot10^6\), both versions of the actual signed square-prefix sum satisfy \(A(K)<-0.0843K^2\) unconditionally. This uses the actual prime counts through \(K^2\) by partial summation with an explicit uniform error.

Write \(X=K^2\), \(I(X)=\int_1^Xw(\log t)dt\), and \(D=1+\sqrt2\). In the exact identity for \(A(K)-B_{1/2}(X)\), \(-q\le1/2\) bounds the atomic term from above by \((E(X)+I(X))/2\), since all its prime weights are nonnegative. On writing \(u=\sqrt t\), the continuous sawtooth is \(1/2-\{u\}\) almost everywhere, with a primitive zero at each integer and bounded by \(1/8\). The derivative of \(2u\,w(2\log u)\) has absolute value at most \(8+4D\). Hence
\[
 A(K)\le B_{1/2}(X)+E(X)+I(X)/2+(8+4D)(K-1)/8.
\]
For the discrete compensator there is an extra cost of at most \(KD\log X\), by bounding the integral of the absolute density derivative over all unit cells at each cutoff. Johnston's finite theta bound and partial summation give
\[
 |E(X)|\le 598D+(4+2D)\sqrt X\log^2 X/(8\pi).
\]
For the integral below 599 the verifier checks \(0\le\theta(t)\le2t\) by integer trial division; the weight vanishes at 1. For the main density, positivity allows the integration to start at 0, giving \(I(X)/X\le 2-\Re\sum_{t=1,\sqrt2}X^{it}/(1+it)\). Over the 1,000 covering intervals of length 1,000 in \(K\), this last expression is at most 0.961450. Combining the three error bounds with \(B_{1/2}(X)/X<-0.5651\) on the enclosing interval gives margins greater than 0.084334 (integral compensator) and 0.084326 (discrete compensator). [Johnston, Theorem 3.2 and Corollary 3.3](https://arxiv.org/pdf/2109.02249) · [Verifier](square-prefix-band.py) · [128-bit receipt](square-prefix-band-128.txt) · [192-bit receipt](square-prefix-band-192.txt).

## Unconditional recurring excursions of the square prefix

For both compensators, the physical signed square prefix satisfies
\[
 \liminf_{K\to\infty} A(K)/K^2<-1.25236,\qquad
 \limsup_{K\to\infty} A(K)/K^2>-0.74764.
\]
The continuous integral \(B_1(X)/X^{3/2}\) has liminf below \(-1.73991\) and limsup above \(-0.92676\). Both statements concern recurring cutoffs and require no eventual-sign assumption.

First consider any \(\alpha\in\{1/2,1\}\). If \(B_\alpha(X)/X^{\alpha+1/2}\) is bounded on either side eventually, choose a constant \(C\) such that \(C X^{\alpha+1/2}\pm B_\alpha(X)\ge0\) on a tail, with the sign chosen for that side. Its Mellin transform is regular on the real ray \(s>\alpha+1/2\) by the same exact identity as in the sign converse. Landau and the rational zero detector imply RH. Thus if RH fails, this normalized mean has infinite positive limsup and infinite negative liminf. The unconditional square-prefix discrepancy and within-cell estimates above carry this conclusion to both versions of \(A(K)/K^2\). More explicitly, setting \(K=\lfloor\sqrt X\rfloor\) changes \(B_{1/2}(X)\) by \(o(X)\) and \(K^2/X\to 1\).

In the remaining case all zeros are critical. Put \(y=\log X\). The preceding exact formula, divided by \(X^{\alpha+1/2}\), becomes the sum of a constant \(-D_\alpha\), the two rotating terms
\[
 \Re\sum_{t=1,\sqrt2} d_t e^{ity},\qquad
 d_t=\frac{\alpha}{(1+2it)(1/2+\alpha+it)},
\]
an absolutely and uniformly convergent trigonometric series supported on the frequencies \(\gamma+t\) for \(t\in S\), and a remainder tending to zero. The signs in the two displayed rotating terms come from subtracting the prime squares.

Define \(F_m(u)=|\sum_{j=0}^m e^{iju}|^2/(m+1)\). For any two phases, \(P(y)=F_m(y-\phi_1)F_m(\sqrt2 y-\phi_2)\ge0\) has mean one, by irrationality of \(\sqrt2\). The coefficients at each of the two first harmonics have modulus \(m/(m+1)\). If the finite frequency set \(\{j+k\sqrt2: |j|,|k|\le m\}\) misses the shifted zero frequencies, then all true-zero terms have zero mean against \(P\). Absolute uniform convergence permits taking the mean termwise. Choose the phases to make both square terms contribute with the same requested sign so the weighted mean is exactly \(-D_\alpha\pm m V_\alpha/(m+1)\). Positivity and unit mean put each weighted mean between the ordinary liminf and limsup. The \(o(1)\) remainder is harmless because \(P\) is bounded for fixed \(m\). The unconditional square-cell comparison then yields the asserted prefix bounds.

An analytic choice \(m=5\) already gives the same inequalities with \(5V_\alpha/6\), since \(5(1+\sqrt2)+\sqrt2<14\). For \(m=128\), possible collisions require a positive zeta ordinate below 310.434 to have the form \(j+k\sqrt2\) with arbitrary integer \(j\) and \(|k|\le129\). Conjugation handles negative ordinates. The verifier encloses all 144 positive ordinates to that height by index, including the following ordinate above 311 as the completeness check. It proves that in every test the distance to the nearest integer exceeds \(0.00002006\). The resulting two-sided constants include the printed margins. [FLINT's indexed zero enclosure](https://flintlib.org/doc/acb_dirichlet/zeta-zeros.html) · [Verifier](prefix-excursions.py) · [128-bit receipt](prefix-excursions-128.txt) · [192-bit receipt](prefix-excursions-192.txt).

## Why the finite square-prefix majorant changes sign at arbitrarily large cutoffs

For the actual \(E,I,B_{1/2}\) used above and integer \(K\), put \(X=K^2\), \(D=1+\sqrt2\), and
\[
 U(K)=B_{1/2}(X)+E(X)+\frac12 I(X)+\frac{8+4D}{8}(K-1).
\]
The million-cutoff proof uses the exact upper bound \(A(K)\le U(K)\), with an extra \(KD\log X\) permitted for the discrete compensator. This particular majorant changes sign unconditionally. More precisely,
\[
 \limsup_K U(K)/K^2\ge c,\qquad
 \liminf_K U(K)/K^2\le-c,\qquad
 c=\frac{128}{129}\Bigl(\frac{1}{\sqrt{10}}+\sqrt{\frac{2}{27}}\Bigr)>0.58383.
\]
The extra term for the discrete compensator vanishes after normalization. Thus increasing the precision of the endpoint measurements in this particular majorant cannot make it certify eventual negativity.

Indeed \(E(X)=o(X)\) by the prime number theorem and \(I(X)=O(X)\). If RH fails, the signed Landau argument above and the square-cell comparison give infinite positive limsup and infinite negative liminf for \(B_{1/2}(K^2)/K^2\). If all zeros are critical, put \(y=\log X\). Half the density divided by \(X\) is
\[
 1-\tfrac12\Re\sum_{t=1,\sqrt2}\frac{e^{ity}}{1+it}+O(1/X).
\]
Its constant cancels the \(-1\) from the integrated prime squares. Its coefficients combine with the two rotating square terms of \(B_{1/2}(X)/X\) to give
\[
 \frac{1}{2(1+2it)(1+it)}-\frac{1}{2(1+it)}
     =\frac{-it}{(1+2it)(1+it)}.
\]
The remaining nontrivial-zero series has precisely the same absolutely summable coefficients and frequencies as before. The positive product of Fejér kernels of degree 128 therefore extracts either sign of \(c\), using the same certified finite separation. The normalized expression on real \(X\) is a uniformly almost periodic function of \(\log X\) plus \(o(1)\). Indeed the shifted-zero series is uniformly absolutely convergent, and both extra principal terms are individual frequencies. Consecutive values of \(\log K^2\) have gaps tending to zero. Uniform continuity therefore transfers both limiting bounds to these actual square cutoffs. The simpler degree-five version requires only the first zero above 14 and gives the factor \(5/6\) in place of \(128/129\).

This is a limitation of the use of the absolute bound on the prime sawtooth inside the finite certificate. The arithmetic rounding term itself is \(o(K^2)\) by prime discrepancy, as proved in the square-prefix comparison above. This calculation leaves the eventual sign of the signed Riesz mean open. [Frequency verifier](prefix-excursions.py) · [192-bit frequency receipt](prefix-excursions-192.txt).
