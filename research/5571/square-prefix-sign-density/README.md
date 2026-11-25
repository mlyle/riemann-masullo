# Density of square-prefix signs and estimates between consecutive squares

Let \(w(v)=2-\cos v-\cos(\sqrt2v)\), \(E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log t)\,dt\), and \(A(k)=\sum_{j=1}^k E(j^2)\). The discrete version \(A_d\) replaces the integral by \(\sum_{m\le x}w(\log m)\); \(w(0)=0\). Either prefix can be used independently in the count \(P_c(T)=\#\{1\le j\le T:A(\lfloor j^c\rfloor)>0\}\), with fixed real \(c\ge1\).

## What density zero along a subsequence excludes

Suppose \(\Theta=\sup_\rho\Re\rho>1/2\) is attained by a nontrivial zeta zero. There exists \(\delta_c>0\) such that, for all sufficiently large real \(T\),
\[
\delta_c T\le P_c(T)\le(1-\delta_c)T .
\]
There are blocks of each strict sign with comparable cardinality for both compensators at once. Consequently \(\liminf_{T\to\infty}P_c(T)/T=0\) excludes every attained exterior supremum. The case where real parts tend to an exterior supremum strictly from below remains open under this weaker count hypothesis. The [previous long-block result](../square-prefix-sign-blocks/README.md) handles that case when the hypothesis has a power saving.

Indeed let \(b_*=\Theta-1/2\). In the [absolutely summable grouped Riesz spectrum](../square-prefix-sign-blocks/README.md#exact-absolutely-summable-spectrum) at \(y=2\log k\), divide by \(e^{b_*y}\). All terms of lower abscissa have absolute sum tending to zero by dominated convergence, even if those abscissae approach \(\Theta\). The bounded prime-square drift and the \(o(1)\) physical rounding error also tend to zero after division. Thus
\[
 k^{-1-2\Theta}A(k)=G(2\log k)+o(1),\qquad
 G(v)=\sum_{\omega} C_{b_*,\omega} e^{i\omega v},
\]
and likewise for \(A_d\). The shift multiplicity argument linked above gives a nonzero coefficient at that abscissa, every frequency has modulus greater than 12, and conjugate terms pair. The uniformly absolutely convergent series \(G\) is real, uniformly continuous and almost periodic. Its mean is zero by termwise averaging. The mean of \(G^2\) is \(\sum_\omega|C_{b_*,\omega}|^2>0\), again by absolute convergence. A function of one sign would satisfy \(G^2\le \|G\|_\infty |G|\) and have zero mean square. Thus \(G\) takes both signs with a fixed nonzero margin. Some fixed positive-width interval above this margin and one below its negative recur with bounded gaps in \(v\), by simultaneous approximate periods of a sufficiently accurate trigonometric polynomial approximation. As \(j\to\infty\), \(2\log\lfloor j^c\rfloor=2c\log j+o(1)\). For every large \(T\), there are intervals of each strict sign of fixed positive length in \([2c\log T-L,2c\log T]\), with a common constant \(L\). Each pulls back to at least \(\delta_c T\) integer indices. This also proves the assertion for both prefixes together.

## Arithmetic mean values at adjacent square cutoffs

With the centered second difference \(\Delta^2 A(k)=A(k+1)-2A(k)+A(k-1)\), one has unconditionally, for each fixed \(\eta,\varepsilon>0\),
\[
  \#\{Y\le k\le2Y: |\Delta^2 A(k)|\ge \eta k\}
     \ll_{\eta,\varepsilon}Y^{1/2+\varepsilon}.
\]
The same estimate holds for \(A_d\). Bazzanella's Theorem 1, with the exceptional set for fixed relative tolerance defined in §2, bounds the exceptional consecutive-square intervals contained in \([1,N]\) by \(O_{\delta,\varepsilon}(N^{1/4+\varepsilon})\). Set \(N=(2Y+1)^2\) and halve the exponent tolerance. Outside that set \(|\psi((k+1)^2)-\psi(k^2)-(2k+1)|<\delta(2k+1)\). [D. Bazzanella, *Primes between consecutive squares*, Arch. Math. 75 (2000), 29–34](https://iris.polito.it/retrieve/handle/11583/1397858/e384c42d-e02c-d4b2-e053-9f05fe0a1d67/Primes-between-squares.pdf).

For \(k\ge2\), at exponent two there is at most one square prime power in the shell. For each exponent \(h\ge3\), \((k+1)^{2/h}-k^{2/h}<1\), so there is again at most one possible base. Summing at most \(O(\log k)\) exponents with weight \(O(\log k)\) gives a uniform \(O(\log^2 k)\) cost in replacing \(\psi\) by \(\theta\). Throughout the shell the weight differs from \(w(2\log k)\) by at most \(2(1+\sqrt2)/k\). Summing that error against either \(\theta\) or Lebesgue measure costs \(O(\log k)\) using the integer count in the shell. Hence \(|\Delta^2 A(k)|\le 4\delta(2k+1)+O(\log^2 k)\) outside the stated exceptional set. Integrating the derivative bound \((1+\sqrt2)/t\) on each unit cell shows the two compensators' increments differ by \(O(1/k)\). Choosing \(\delta\) sufficiently small proves both estimates.

## Why even a stronger shell moment cannot settle these sign counts by itself

Fix \(1/2<\beta<3/4\) and a nonzero real \(\gamma\). The model \(a(k)=k^{1+2\beta}\cos(2\gamma\log k)\) has
\[
 |\Delta^2 a(k)|\ll_{\beta,\gamma}k^{2\beta-1},\qquad
 \sum_{Y\le k\le2Y}|\Delta^2 a(k)|^2\ll_{\beta,\gamma}Y^{4\beta-1}=o(Y^2).
\]
Twice integrating the continuous second derivative over the two neighboring unit cells bounds the centered difference. Both signs of \(a(k)\) have positive lower density by log-periodicity. A smooth initial cutoff makes \(a(k)\) zero through any prescribed finite bound while preserving these assertions. This sequence has the growth and log frequency of an exterior zero in the physical prefix. It is a counterexample to an inference using only exceptional shell counts or absolute per-shell second moments, even with a Poisson-scale \(O_\varepsilon(Y^{2+\varepsilon})\) total moment. It supplies no example of a prime counting function with those zeros. Correlations in the actual signed shells remain available to an arithmetic argument.

The bounded positive-count certificate over 30 trillion consecutive cutoffs is [recorded separately](../square-prefix-mean-square-count/README.md). The above statements are classical derivations.
