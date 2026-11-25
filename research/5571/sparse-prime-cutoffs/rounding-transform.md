# The Fejér excursions survive restriction to perfect-square prime cutoffs

For the two-cosine first-prime error \(E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log t)dt\), where \(w(v)=2-\cos v-\cos(\sqrt2v)\), one has unconditionally
\[
 \limsup_{k\to\infty}E(k^2)/k\ge 0.1992738068088042,\qquad
 \liminf_{k\to\infty}E(k^2)/k\le-4.6489811143273203.
\]
The discrete compensator has the same two estimates. This restriction to square arguments uses a genuine distribution theorem for the fractional parts of square roots of primes. The bounded-step comparison alone has an additive error of order \(\sqrt{x}\) at this spacing and does not transfer the signs by these constants.

## Power saving for the arithmetic rounding factor

For \(t\ge1\) put \(B(t)=\lceil\sqrt t\rceil^2\), \(v(t)=\lceil\sqrt t\rceil-\sqrt t\), and \(q(t)=v(t)-1/2\). Outside the squares \(q(t)=1/2-\{\sqrt t\}\). No square is a rational prime. Take \(\alpha_1=1/2,\alpha_2=3/8\) in Wenguang Zhai's Theorem 1, pp. 232–233. The box discrepancy for the two fractional parts \(\{p^{\alpha_i}\}\) has exponent
\[
 \delta=\min(1-\alpha_1,\alpha_1-\alpha_2,\alpha_2/3,20/177)=20/177 .
\]
The bound is uniform in boxes: the Fourier discrepancy inequality of Lemma 1, p. 231, bounds all boxes by the same exponential sums. The endpoints zero in a box can be reached by decreasing positive lower endpoints, since the set of primes under a fixed cutoff is finite and neither fractional part vanishes. Choosing the second interval to be the entire unit interval, and integrating the first-coordinate discrepancy \(\#\{p\le x:\{\sqrt p\}<y\}-y\pi(x)\) over \(0<y<1\), gives
\[
 \sum_{p\le x}q(p)\ll x^{1-\delta}\log^{15} (2x).
\]
Here 15 is a convenient integer overshoot of the printed logarithmic exponent. Partial summation with \(\log t\,w(\log t)\), whose derivative is \(O((1+\log t)/t)\), yields
\[
 \sum_{p\le x}\log(p)w(\log p)q(p)\ll x^{1-\delta}\log^{16}(2x).
\]
For the continuous density, \(\int_1^x q(t)dt=O(\sqrt{x})\): substitute \(t=u^2\), take a bounded primitive of the mean-zero periodic function \(1/2-\{u\}\), and integrate by parts against \(2u\). A second partial summation with \(w(\log t)\) retains the \(O(\sqrt x)\) bound. [Wenguang Zhai, *On the simultaneous distribution of the fractional parts of different powers of primes*, Theorem 1, equation (5), and Example 1](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1274-27.pdf).

## Continued Mellin transform and its exact rounding term

Write \(dA(t)=\sum_p\log(p)w(\log p)\delta_p-w(\log t)dt\), \(M(s)=\int_1^\infty E(x)x^{-s-1}dx\), and \(D(x)=E(\lfloor\sqrt x\rfloor^2)\). Every arithmetic or mean-density mass originally at \(t\) begins contributing to \(D\) at \(B(t)\). Fubini therefore gives \(M_D(s)=s^{-1}\int B(t)^{-s}dA(t)\) for \(\Re s>1\). For \(s\) in any compact subset of this initial domain, and then of \(\Re s>0\), Taylor expansion in \(v(t)/\sqrt{t}\) gives
\[
 B(t)^{-s}=t^{-s}\bigl(1-2s\,v(t)/\sqrt t+O_K(t^{-1})\bigr).
\]
The Taylor remainder integrated against \(|dA|\) converges absolutely and locally uniformly when \(\Re s>0\). The \(q\)-part of the linear term defines a normally convergent partial-summation integral when \(\Re(s+1/2)>1-\delta\) by the two discrepancy bounds above. Its constant \(1/2\) part is \(-\int t^{-(s+1/2)}dA(t)=-(s+1/2)M(s+1/2)\). Thus
\[
 M_D(s)=M(s)-(s+1/2)M(s+1/2)+J(s),\qquad
 J\text{ holomorphic on }\Re s>1/2-20/177.
\]
The original meromorphic continuation of \(M\) holds on \(\Re s>1/3\). On \(\Re(s+1/2)=1\) the shifted \(M\) is regular, since zeta is nonzero on the one-line away from its pole and the five shifted density poles cancel exactly. Consequently \(M_D\) has the same residues as \(M\) on the entire critical line, in particular all 797 contributions in the finite band \([-200,200]\). Both are regular on the real ray \(s>1/2\), so the one-sided Landau–Fejér theorem and previously certified sample values apply verbatim to \(D\). For \(k^2\le x<(k+1)^2\), \(D(x)/\sqrt x=(k/\sqrt x)E(k^2)/k\), where the prefactor tends uniformly to one. This proves the announced estimates. The discrete compensator changes \(E(k^2)\) by \(O(\log k)\) only. [Original arithmetic transform, one-sided Fejér proof and verified values](https://github.com/mlyle/riemann-masullo/tree/8653a3a595b5f123342c26c8e863cf1e16922f10/research/5571/two-cosine-fejer-crossings).

## Localized consequence and the outstanding square estimate

The Gaussian-localized argument by the project lead transfers to \(D\). A fixed left contour with \(5/12\le\Re s<1/2\) lies in the continuation domain above. The extra transform \(M(s+1/2)\) has no poles in the finite rectangle near the small Fejér band, by the verified low zero list. All of its possible poles in this larger strip lie to the left of \(\Re s=1/2\), by zeta's zero-free Euler half-plane and one-line. The generic endpoint analysis therefore applies unchanged to the complete meromorphic \(M_D\), including any nonreal poles farther up the original prime transform. Its initial absolute convergence on \(\Re s=3/2\) and the trivial physical bound \(|D(e^u)|e^{-u/2}=O((1+u)e^{u/2})\) give both required tails. It follows that for each \(\varepsilon>0\) and all sufficiently large \(X\), there are perfect squares of both excursion signs in \([X,X^{1+\varepsilon}]\); one may take any fixed slightly weakened amplitudes below the certified positive and negative magnitudes. Selecting Gaussians in inner subintervals absorbs rounding \(x\mapsto\lfloor\sqrt x\rfloor^2=x+O(\sqrt x)\).

This is a classical deduction. The [separate Lean certificate](square-interpolation.md) proves that uniform power control on *all* square samples implies the required all-integer bound, with both physical compensators. The sign oscillations and window localization do not control that upper envelope.

## Excursions on polynomial grids with spacing larger than the square-root scale

For every fixed \(2\le b<5/2\) the same two numerical excursion bounds hold for \(E(\lfloor k^b\rfloor)/k^{b/2}\), for both compensators. The localization in every sufficiently large \([X,X^{1+\varepsilon}]\) extends to these grids as well. For \(b=12/5\), successive cutoffs have spacing asymptotic to \((12/5)X^{7/12}\), larger than the normalization \(\sqrt X\).

Indeed set \(\alpha=1/b,\ \alpha_2=3\alpha/4\), \(v(t)=\lceil t^\alpha\rceil-t^\alpha\) and \(B(t)=\lceil t^\alpha\rceil^b\). Zhai's uniform box estimate gives exponent \(\delta=\min(\alpha/4,20/177)\) for \(\{p^\alpha\}\). This includes possible atoms with zero fractional part: the count excluded from the entire open unit square is \(O(X^{1-\delta}\log^{15}(2X))\) by decreasing the lower box endpoints to zero and subtracting from the total. Thus it also covers the difference between \(v(p)-1/2\) and \(1/2-\{p^\alpha\}\) at integer values of \(p^\alpha\). The former centered rounding factor has the same weighted \(O(X^{1-\delta}\log^{16}(2X))\) partial-sum bound. Under \(u=t^\alpha\), the continuous density becomes \(bu^{b-1}du\); the bounded primitive of the centered periodic sawtooth yields \(O(X^{1-\alpha})\) for its integral and its two-cosine weighted integral. The Taylor remainder for \(B(t)^{-s}\) now costs \(O_K(t^{-\Re s-2\alpha})\). Hence, for \(D_b(x)=E(\lfloor x^\alpha\rfloor^b)\),
\[
 M_{D_b}(s)=M(s)-\tfrac b2(s+\alpha)M(s+\alpha)+J_b(s),\qquad
 J_b\text{ holomorphic for }\Re s>\max(1-\alpha-\delta,1-2\alpha).
\]
Since \(\alpha>2/5\), \(\alpha+\delta>1/2\), so a neighborhood of the critical edge is available. When \(b=12/5\), \(\alpha=5/12,\delta=5/48\), giving the explicit continuation threshold \(23/48\). For \(b>2\) the shifted \(M(s+\alpha)\) can have additional high poles on or to the right of the critical line. In the band \(|\Im s|\le200\), the finite verification through the slightly enlarged height and the normal prime-power tails exclude any poles of that term in a sufficiently small closed strip about \(1/2\). On the positive real axis it is regular. Therefore the finite Fejér calculation is unaffected. The localized Gaussian contour now uses a left shift lying strictly between \(\max(1-\alpha-\delta,1-2\alpha,1/3)\) and \(1/2\), chosen to avoid the finitely many poles on the horizontal truncation. Additional poles outside the Fejér band are precisely of the kind treated by the generic leading-exponent argument. Finally replacing the real cutoff \(k^b\) by \(\lfloor k^b\rfloor\) changes the integral-mean error by at most four. The discrete-compensator correction at that integer is \(O(\log k)\).
