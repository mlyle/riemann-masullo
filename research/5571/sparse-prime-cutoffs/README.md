# A rational zeta zero-exclusion criterion using only perfect-cube prime cutoffs

Put \(w(t)=2-\cos t-\cos(\sqrt2\,t)\) and \(E(X)=\sum_{p\le X}\log(p)w(\log p)-\int_1^X w(\log t)dt\). If for every \(r>1/2\) one has \(|E(k^3)|\ll_r (k^3)^r\) at every positive integer \(k\), then the Riemann zeta function has no zeros in \(\Re s>1/2\). The discrete compensator \(\sum_{n\le k^3}w(\log n)\) yields the same criterion. The hypothesis is an estimate on a deterministic sequence containing only \(\lfloor X^{1/3}\rfloor\) integer cutoffs up to \(X\). The upper estimate at these cubes remains open.

More generally fix \(1/2\le\sigma<1\), \(\alpha=2(1-\sigma)/3\), and \(b=1/\alpha\). Assume \(|E(\lfloor k^b\rfloor)|\ll_r(\lfloor k^b\rfloor)^r\) for every fixed \(\sigma<r<1\) and every positive integer \(k\). Then \(\zeta\) has no zero in \(\Re s>\sigma\). The proof uses a classical power saving for an exponential sum over genuine primes, together with the two-cosine cutoff transform. No assumption about the zeta zero distribution enters the proof.

## Rounding error from a prime exponential sum

For \(0<\alpha<2/3\) let \(\delta=\min((1-\alpha)/3,\alpha/2,1/6)\). Wenguang Zhai, Proposition 3.4, p. 236, bounds
\[
 \sum_{Y<n\le2Y}\Lambda(n)e(hn^\alpha)\ll_\alpha
          Y^{1-\delta}\log^{9/2}(2Y),\qquad 1\le h\le Y^\delta ,
\]
where \(e(v)=e^{2\pi iv}\). The proposition uses \(m\sim M\); take \(M=Y\) in the dyadic notation specified before the proposition. The weighted prime sum obtained by retaining the degree-one terms still satisfies this bound, since all higher powers have total von Mangoldt mass \(O(\sqrt Y\log^2(2Y))\). See also Zhai's explicit invocation of this proposition for the one-monomial case in the proof of Theorem 1 following Proposition 3.4. [Zhai, *On the simultaneous distribution of the fractional parts of different powers of primes*, Proposition 3.4, p. 236](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1274-27.pdf).

For the positive measure \(\mu_Y=\sum_{Y<p\le2Y}\log(p)\delta_{\{p^\alpha\}}\) on the unit circle, the one-dimensional Erdős–Turán inequality, applied with \(H=\lfloor Y^\delta\rfloor\), bounds its discrepancy in intervals by
\[
 O\!\left(\frac{\mu_Y([0,1))}{H+1}+
         \sum_{1\le h\le H}\frac{|\widehat\mu_Y(h)|}{h}\right)
 =O_\alpha(Y^{1-\delta}\log^{11/2}(2Y)).
\]
The usual finite-sequence version gives the positive weighted version by first repeating points with rational masses, rescaling, and approximating the finitely many positive weights. The shell mass is \(O(Y)\) by Chebyshev's bound. Integrate the discrepancy for \([0,v)\) over \(0<v<1\) to bound the centered sawtooth sum with \(\frac12-\{p^\alpha\}\). The mass of the single point \(0\) is bounded by the same discrepancy, by shrinking an interval to zero. Thus \(q(t)=\lceil t^\alpha\rceil-t^\alpha-1/2\), with its exact value at integers \(t^\alpha\), satisfies
\[
 \sum_{p\le X}\log(p)q(p)\ll_\alpha X^{1-\delta}\log^{11/2}(2X)
\]
after summing the dyadic shells. Partial summation against the bounded \(w(\log t)\), whose derivative is bounded by \((1+\sqrt2)/t\), preserves this bound. Directly \(\int_1^X q(t)w(\log t)dt=O_\alpha(X^{1-\alpha})\), by the periodic bounded-primitive calculation with \(u=t^\alpha\). [Uniform Fourier discrepancy inequality, Zhai, Lemma 1, p. 231](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1274-27.pdf).

## Arithmetic Mellin continuation and disappearance of right-half-plane poles

Let \(M(s)=\int_1^\infty E(x)x^{-s-1}dx\), \(D_b(x)=E(\lfloor x^\alpha\rfloor^b)\), and \(M_b(s)=\int_1^\infty D_b(x)x^{-s-1}dx\) initially for \(\Re s>1\). The arithmetic and mean-density masses at \(t\) enter \(D_b\) at \(B(t)=\lceil t^\alpha\rceil^b\). The Taylor formula \(B(t)^{-s}=t^{-s}(1-bs(q(t)+1/2)t^{-\alpha}+O_K(t^{-2\alpha}))\), locally uniform on compact sets of \(s\), therefore gives the meromorphic identity
\[
 M_b(s)=M(s)-\frac b2(s+\alpha)M(s+\alpha)+J_b(s),
 \qquad J_b\text{ holomorphic for }\Re s>\max(1-\alpha-\delta,1-2\alpha).
\]
Indeed the Taylor remainder is absolutely integrable against the prime and continuous variation for \(\Re s>1-2\alpha\); the centered sawtooth term is holomorphic on \(\Re s>1-\alpha-\delta\) by the preceding partial-summation bounds. The \(1/2\) term is exactly the translated original Mellin transform. The factor \(1/s\) is harmless on this domain for the exponents used. [Details of the transform and the square case](rounding-transform.md).

For \(\alpha=2(1-\sigma)/3\) one has \(0<\alpha\le1/3\), so \(\delta=\alpha/2\) and \(1-\alpha-\delta=\sigma\). Replacing a real \(k^b\) by its integer part changes the integral-mean error by at most four; switching the compensator at an integer changes the error by \(O(\log(2k^b))\). Under either version of the hypothesis \(M_b\) is therefore holomorphic throughout \(\Re s>\sigma\), by absolute convergence of its defining integral (use any exponent strictly between \(\sigma\) and \(\Re s\)). The original \(M\) already has meromorphic continuation to \(\Re s>1/3\). A pole of \(M\) at any \(s_0\) in \(\Re s>\sigma\) would force a pole at \(s_0+\alpha\) by the displayed identity. Iterating eventually reaches the absolutely convergent domain \(\Re s>1\). Thus \(M\) is holomorphic on \(\Re s>\sigma\).

In this half-plane \(P(s) = \sum_p\log(p)p^{-s}\), continued meromorphically, differs from \(L(s)=-\zeta'(s)/\zeta(s)\) by a holomorphic function, since every omitted higher Euler power converges normally for \(\Re s>1/2\). With \(S=\{0,\pm1,\pm\sqrt2\}\), \(c_0=2,\ c_{t\ne0}=-1/2\), the function \(sM(s)\) is the finite sum \(\sum_{t\in S}c_t(P(s-it)-1/(s-1-it))\). Its holomorphy thus implies that the corresponding combination of the pole-corrected logarithmic derivatives is holomorphic. At any real part \(\beta>\sigma\) the ordinary zeta zero multiplicity \(m(u)\ge0\) at \(\beta+iu\), taking zero at regular points, consequently satisfies
\[
 4m(u)=m(u+1)+m(u-1)+m(u+\sqrt2)+m(u-\sqrt2).
\]
If a point has \(m>0\), choose a nearby point in its dense additive orbit by \(1,\sqrt2\) where \(m=0\); local finiteness supplies an entire zero-free interval at that real part. The equation and nonnegativity at the zero-multiplicity point then force all its translates in the orbit to have zero multiplicity, a contradiction. This completes the proof. The pole of zeta at 1 was explicitly removed. [Formal completed-divisor argument](https://github.com/mccorvie/riemann-masullo/pull/7541) · [Ordinary rational zero-exclusion join](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521).

## What the same estimate proves without assuming the sparse growth bound

For every \(2\le b<3\), take \(\alpha=1/b\) and the same one-dimensional discrepancy. Here \(\delta=1/6\) and \(\alpha+\delta>1/2\); the holomorphy of \(J_b\) extends *through* the critical line. In the low Fejér band \(|\Im s|\le200\), finite verification excludes poles of \(M(s+\alpha)\) on and in a sufficiently small neighborhood of the critical line. Thus the first-prime error at these integer cutoffs, normalized by \(k^{b/2}\), retains the unconditional limsup at least \(0.1992738068088042\) and liminf at most \(-4.6489811143273203\). The small-strip Gaussian localization proof transfers as in the square case. For \(b=3\) the discrepancy only gives holomorphy of \(J_b\) on the open right half-plane; the zero-exclusion criterion still applies there but this argument does not give the numerical boundary excursions at the cubes.

The discrepancy and meromorphic deductions above are classical paper proofs. The separate direct sampling result for perfect squares and both rational zeta specializations have native Lean certificates; the present improvement from squares to cubes uses Zhai's published prime exponential-sum bound and has not been formalized.



The [square sampling certificate](square-interpolation.md) includes its Lean source and axiom check. The [rounding calculation](rounding-transform.md) gives the independent two-dimensional discrepancy bound before the stronger one-dimensional estimate in this note.
