# Signed Gaussian averages of the two actual rational square prefixes at every large center

Let \(A(k)\) be the rational first-prime square prefix with weight \(w(t)=2-\cos t-\cos(\sqrt2t)\) and the integral compensator, and \(A_d(k)\) the integer-compensated version. Both are [defined here](../square-prefix-sign-density/README.md). In either case write \(F(u)=A(\lfloor e^{u/2}\rfloor)/\lfloor e^{u/2}\rfloor^2\) for \(u\ge0\) and \(F(u)=0\) for \(u<0\). Let \(U_y\) be Gaussian with mean \(y\) and variance \(\lambda y\). Fix \(H=3\cdot10^{12}\). For example \(\lambda=10^{-24}\) satisfies the assumptions below.

## A signed average with an unconditional limit

For every fixed \(0<\lambda<1\) with \(\lambda((H-\sqrt2)^2-1/4)>1\),
\[
 \lim_{y\to\infty}\mathbb E F(U_y)=-1 .
\]
The limit holds over all real \(y\to\infty\). The exact weights on the physical sequence \(A(k)/k^2\) are the positive Gaussian probabilities of the intervals \([2\log k,2\log(k+1))\). Their sum tends to one. When \(\lambda=10^{-24}\) this conclusion, and the exponential-rate conclusion below, hold after restricting \(U_y\) to \([(1-2\cdot10^{-12})y,(1+2\cdot10^{-12})y]\). Thus the signed sum in every sufficiently large such window is negative, independently of the location of any exterior zeros.

More generally fix real \(t\) such that \(H-\sqrt2-|t|>0\) and \(\lambda((H-\sqrt2-|t|)^2-1/4)>1\). Then \(\mathbb E[e^{-itU_y}F(U_y)]\) converges to the coefficient of frequency \(t\) in the explicit prime-square trigonometric polynomial and the critical zero series combined. This includes frequencies without a coefficient, with limit zero. The shift \(t\) belongs in the integrand inside each integer cell. For \(t=0\) only the prime-square constant remains.

## What opposite signs contribute to this cancellation

Put \(b_*=\sup_\rho\Re\rho-1/2\), and \(g_\lambda(b)=b+\lambda b^2/2\). Under the same unconditional variance hypothesis, with \(F_+=\max(F,0)\) and \(F_-=\max(-F,0)\),
\[
 \lim_{y\to\infty}\frac{\log(1+\mathbb E F_+(U_y))}{y}
 =\lim_{y\to\infty}\frac{\log(1+\mathbb E F_-(U_y))}{y}=g_\lambda(b_*).
\]
If there is an exterior zero then both means grow exponentially at every large center, their ratio tends to one, and their difference tends to \(-1\). On RH the positive mass tends to zero and the negative mass tends to one. In particular, a subexponential bound for the positive physical mass along even one sequence \(y\to\infty\) implies RH. This criterion concerns the positive part of the actual normalized arithmetic values. Counting positive indices discards their magnitudes.

## Proof

The [actual absolutely convergent Riesz formula and square-prefix comparison](../square-prefix-sign-blocks/README.md#exact-absolutely-summable-spectrum) give
\[
  F(u)=D(u)+\sum_{b,\omega} C_{b,\omega}e^{(b+i\omega)u}+o(1)\quad(u\to+\infty).
\]
Here \(D(u)=-1+\Re\sum_{t=1,\sqrt2}e^{itu}/[2(1+2it)(1+it)]\), the \(C\)'s are grouped by the pair \((b,\omega)\) and absolutely summable, \(|b|<1/2\), \(\omega=\gamma+t'\) for \(t'\in\{0,\pm1,\pm\sqrt2\}\), and bounded frequency sets contain finitely many pairs. At every abscissa supporting a zeta zero at least one grouped coefficient survives the five shifts. The comparison also holds between consecutive integers: \(B((k+v)^2)-B(k^2)=\int_k^{k+v}E(s^2)\,ds=o(k^2)\) uniformly in \(0\le v\le1\) by the prime number theorem. Moreover \(B(k^2)=o(k^3)\), so changing its normalizing denominator to \((k+v)^2\) costs \(o(1)\). The integer-compensator difference is \(O(k\log(2k))\). [Four-shift divisor propagation](https://github.com/mccorvie/riemann-masullo/pull/7541) · [Zhai, Proposition 3.4, for signed prime rounding](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1274-27.pdf).

Extend \(D+\sum C e^{(b+i\omega)u}\) to all real \(u\). Its absolute size on \(u<0\) is \(O(e^{-u/2})\). Its expectation on that tail is \(o(1)\), since \(\mathbb E[e^{-U_y/2}]=\exp((-1/2+\lambda/8)y)\). The bounded \(o(1)\) remainder on the positive half-line has expectation \(o(1)\), also after multiplication by a unit phase. Termwise integration follows from \(\sum|C|<\infty\) and finite Gaussian moments. A term modulated by \(e^{-itu}\) has exact Gaussian expectation
\[
 C_{b,\omega}\exp\left(y\left[z+\lambda z^2/2\right]\right),\qquad
 z=b+i(\omega-t).
\]
The real growth exponent is \(q_{b,\omega}(t)=g_\lambda(b)-\lambda(\omega-t)^2/2\). For low critical terms \(q=-\lambda(\omega-t)^2/2\); they decay except at \(\omega=t\). Every term from an off-line zero has \(|\omega|>H-\sqrt2\) by the verified zero theorem, so in the stipulated low-frequency band its exponent is bounded above by \(1/2+\lambda/8-\lambda(H-\sqrt2-|t|)^2/2<0\). The finitely many terms from \(D\) have the same elementary modulation rule at \(b=0\). This proves the signed limits. [Platt and Trudgian, Theorem 1](https://arxiv.org/abs/2004.09765).

The bound \(|F(u)|\ll 1+e^{b_*u}\) for \(u\ge0\) gives the upper exponential rates. If \(b_*>0\), fix \(0<\theta<b_*\) and take \(C_{b,\omega}\ne0\) with \(b>\theta\). For every \(t\) near \(\omega\) its tilted exponent exceeds \(g_\lambda(\theta)>0\). Choose such \(t\) avoiding the countable set of ties between distinct pairs. For unequal \(\omega\)'s the exponent difference is affine with nonzero slope in \(t\); for equal \(\omega\) and unequal \(b\), it never vanishes because \(g_\lambda\) is strictly increasing on \([-1/2,1/2]\). Hence precisely one active pair has the maximal exponent \(q>g_\lambda(\theta)\). It exists, with a strictly positive gap, by local finiteness and \(q_{b,\omega}(t)\to-\infty\) uniformly for \(|\omega|\to\infty\). The \(D\) terms have nonpositive exponents. Absolute summability gives a strict asymptotic for the modulus of the tilted expectation, \(|\mathbb E[e^{-itU_y}F(U_y)]|\sim |C_{\max}|e^{qy}\). This is a lower bound for \(\mathbb E|F(U_y)|\). Since \(\mathbb E F(U_y)\to-1\), each one-sided mass is \(\frac12(\mathbb E|F(U_y)|+O(1))\). Take \(\theta\uparrow b_*\). When \(b_*=0\), boundedness gives rate zero, the [strict RH sign margin](../signed-riesz-margin/README.md#all-height-sign-margin-when-the-zeros-are-critical) makes \(F\) eventually negative, and Gaussian mass on the remaining bounded region tends to zero.

Finally \(e^{|u|/2}\le e^{y/2}e^{|u-y|/2}\). Completing the square on either tail outside \(|u-y|\le dy\), for \(d>\lambda/2\), bounds the absolute error in every above mean by
\[
 O\!\left(\exp\left\{\left[1/2+\lambda/8-\frac{(d-\lambda/2)^2}{2\lambda}\right]y\right\}\right).
\]
At \(d=2\cdot10^{-12}\), \(\lambda=10^{-24}\), the bracket is less than \(-1\). Both the value \(-1\) and the both-sign exponents therefore use only the indicated physical window. Dividing by its probability gives the same conclusions. The mean \(-1\) measures signed cancellations. The exponential growth of both parts in the exterior-zero case demonstrates why it cannot by itself give a bound for the count of positive prefixes.

These are unconditional classical implications from the cited inputs. A cofinal saving in the positive count or the positive mass remains open.
