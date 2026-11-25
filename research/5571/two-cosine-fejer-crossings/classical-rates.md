# Global and finite-range bounds for the two-cosine first-prime statistic

For \(w(t)=2-\cos t-\cos(\sqrt2t)\), write \(E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log t)\,dt\) and \(e(x)=\theta(x)-x\). Stieltjes integration by parts gives, exactly for \(x\ge1\),
\[
 E(x)=w(\log x)e(x)-\int_1^x w'(\log t)e(t)\,dt/t.
\]
The lower endpoint cancels because \(w(0)=0\). The prime mass at an integer upper cutoff is included. This fixes the signs of both terms.

## Classical Korobov–Vinogradov bound for every large cutoff

Bellotti's 2025 Corollary 1.6 bounds \(|\theta(x)-x|/x\ll \exp[-d L^{3/5}(\log L)^{-1/5}]\), \(L=\log x\), \(A_0=1/48.0718\), \(d=(5^6A_0^3/(4\cdot3^4))^{1/5}=0.21257920212094204\ldots\). The implied constant absorbs a fixed \(\exp(55 A_0)\). For \(\Phi(L)=d L^{3/5}(\log L)^{-1/5}\), \(\Phi'(L)\to0\). For \(L_0\) sufficiently large and \(L\ge u\ge L_0\), \(\Phi(L)-\Phi(u)\le (L-u)/2\). Consequently
\[
 \int_{L_0}^{L}e^{u-\Phi(u)}du\le
 e^{L-\Phi(L)}\int_0^\infty e^{-v/2}dv .
\]
As \(|w|\le4\) and \(|w'|\le1+\sqrt2\), partial summation gives \(|E(x)|\ll x\exp[-d L^{3/5}(\log L)^{-1/5}]\) with the *same* positive \(d\). The discrete mean differs by \(O(\log x)\) at integer arguments and obeys this rate too. The effective exponent in this upper bound is \(1-d/[(\log x)^{2/5}(\log\log x)^{1/5}]\), which tends to 1. Thus this classical zero-free-region input supplies no fixed power exponent below one on all large cutoffs. This is a paper derivation from Bellotti's theorem. [Bellotti, Theorem 1.5 and Corollary 1.6](https://arxiv.org/html/2508.02041).

## Square-root error on the verified finite range

Johnston's Theorem 3.2, estimate (3.4), and Corollary 3.3 give \(|e(t)|\le \sqrt t\log^2t/(8\pi)\) on \(599\le t\le1.101\cdot10^{26}\) using the verified zeros up to \(3\cdot10^{12}\). For \(1\le t\le599\) the elementary Chebyshev estimate \(0\le\theta(t)\le t\log 4\le 2t\) implies \(|e(t)|\le t\). With \(\lambda=1/2\), define
\[
 D=\sum_{\omega\in\{1,\sqrt2\}}\omega
 \sqrt{\frac1\lambda\left(\frac1{2\lambda}+
               \frac1{2\sqrt{\lambda^2+4\omega^2}}\right)}.
\]
Over the full verified range,
\[
 |E(x)|\le
 \frac{w(\log x)+D}{8\pi}\sqrt x\log^2x+
 598(1+\sqrt2)
 \le 0.308105\,\sqrt x\log^2 x+598(1+\sqrt2).
\]
Indeed the part of the integral up to 599 costs at most \(598(1+\sqrt2)\). In the other part replace \(\log^2 t\) by \(\log^2 x\) and change variables \(t=xe^{-v}\). The integral factor is bounded by \(\sqrt x\int_0^\infty e^{-v/2}|w'(\log x-v)|dv\). For each frequency, Cauchy–Schwarz with measure \(e^{-\lambda v}dv\) and the identity for \(\sin^2\) give
\[
 \int_0^\infty e^{-\lambda v}|\sin(\alpha-\omega v)|dv
 \le \sqrt{\frac1\lambda\left(\frac1{2\lambda}+
    \frac1{2|\lambda+2i\omega|}\right)} .
\]
Summing with coefficients \(1,\sqrt2\) gives \(D=3.74350815668733263\ldots\) and \((4+D)/(8\pi)=0.30810440000229994\ldots\). For the discrete compensator the displayed upper bound increases by at most \((1+\sqrt2)\log N\) for an integer \(N\): on every \([n,n+1]\) the derivative of \(w(\log t)\) is bounded in modulus by \((1+\sqrt2)/t\), and summing its integral over the partition proves this bound directly. [Johnston, Theorem 3.2 and Corollary 3.3](https://arxiv.org/pdf/2109.02249) · [Platt and Trudgian's finite verification](https://arxiv.org/abs/2004.09765).

These pointwise upper bounds complement the [finite Fejér calculation and arbitrarily late bounded errors](README.md).
