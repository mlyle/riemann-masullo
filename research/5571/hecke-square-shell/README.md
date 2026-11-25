# The prime-square correction in the signed translated formula

For Theorem 12.5.1.1 on pp. 519–520, fix a number field, a norm section, a unitary character ψ trivial on the section, and a continuous profile H with support in [u,v], 0<u≤v. Let P be the residue-degree-one sum with character ψ⁻¹, L the signed local expression, V the norm-one volume and h the bilateral Laplace transform of H. In the notation of willzh0's #7569 put

$$D(y)=P(y)-{\bf1}_{\psi=1}e^{y/2}h(1/2)+L(y)/V.$$

## Lean calculation for all normalized unitary characters

The signed term which can survive at bounded size is

$$S_2(y)=\sum_p \frac{\Lambda_{\psi^{-1}}(p^2)}p H(2\log p-y).$$

Here the coefficient includes the second powers of degree-one prime ideals and first powers of degree-two prime ideals, with their local Euler values. In particular a degree-two first power carries $2\log p$.

For composite rational norms the von Mangoldt majorant is $[F:\mathbb Q]\Lambda(n)$. Removing prime squares leaves total mass at most $K x^{1/3}$ up to $x$, by the Costa Pereira inequality for the Chebyshev functions. The denominator contributes at most $e^{-(y+u)/2}$ on this shell and the upper cutoff is $e^{y+v}$. With the factor $[F:\mathbb Q]\|H\|_\infty$ this gives $K e^{v/3-u/2}e^{-y/6}$ for the residual. The negative polar term and all archimedean places decay as $e^{-y/2}$. Hence

$$|D(y)+S_2(y)|\le C_{F,\psi,H,u,v}e^{-y/6}\qquad(y\ge0).$$

The arithmetic module was checked at 44fd355a232d8d233d0c7fa26aa4586fedb7b7a9. The attached joint theorem was checked with the exact published head 70f438aace22ec5ee7bcfe6002447424aa7f1058 of #7569 and this arithmetic module. The author’s signs, inverse character, volume, arbitrary representatives and quantification over all translates are preserved. [Arithmetic module](https://github.com/mlyle/riemann-masullo/blob/44fd355a232d8d233d0c7fa26aa4586fedb7b7a9/RiemannMasullo/Ch01_Introduction/HeckePrimeSquareShell.lean) · [Local comparison](https://github.com/mccorvie/riemann-masullo/pull/7569) · [Joint proof](Combination.lean) · [Build receipt](receipt.txt)

## Classical limit for finite-order characters

Assume in addition that ψ has finite order. Regard ψ⁻¹ as a finite-order Galois character using class field theory with the Euler-factor Frobenius convention. Write $W=\operatorname{Ind}_{G_F}^{G_{\mathbb Q}}\psi^{-1}$, and let G be a finite quotient through which W factors and which contains the splitting data for F. Define the Frobenius–Schur indicator of W by

$$\nu(W)=|G|^{-1}\sum_{g\in G}\operatorname{tr} W(g^2).$$

Artin induction of the Euler product gives $\Lambda_{\psi^{-1}}(p^2)=(\log p)\operatorname{tr} W(g_p^2)$ at each unramified p. Indeed, expand the logarithmic derivative of $\det(1-W(g_p)p^{-s})^{-1}$ at the second power. Equivalently a Frobenius cycle of length one contributes its Euler value squared and a cycle of length two contributes twice its Euler value. A finite set of exceptional primes eventually leaves the translated square window. [Emerton, *Reciprocity and L-functions*, formulas (39)–(41)](https://math.uchicago.edu/~emerton/pdffiles/reciprocity.pdf)

Put $X=e^{y/2}$. For each conjugacy class C, Chebotarev and partial summation give $\sum_{p\le z,\,g_p\in C}\log p=(|C|/|G|)z+o(z)$. On the fixed compact interval $[e^{u/2},e^{v/2}]$, this implies convergence of the measures $X^{-1}\sum_{g_p\in C}(\log p)\delta_{p/X}$ against continuous tests to $(|C|/|G|)dt$. One can first check subintervals by subtracting the endpoint sums and then use uniform step approximations. Testing with $H(2\log t)/t$ and summing the classes gives

$$\lim_{y\to\infty} S_2(y)=\tfrac12\nu(W)\int_{\mathbb R}H(x)\,dx,\qquad \lim_{y\to\infty}D(y)=-\tfrac12\nu(W)\int_{\mathbb R}H(x)\,dx.$$

The factor $1/2$ is the Jacobian for $x=2\log t$. This finite-order limit uses the classical Chebotarev theorem outside Lean. The quantitative bound in the preceding section is Lean-checked. [Lagarias and Odlyzko, *Effective Versions of the Chebotarev Density Theorem*, introduction and Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko-dyslexic.pdf)

For the trivial character over the rationals, ν=1. Any nonnegative unit-integral bump supported in [2,4] gives $D(y)\to-1/2$, ruling out an uncorrected $o(1)$ for general positive-window profiles. For the specific Gevrey detector in #7571, its central moment gives $\int H=0$ and hence $D(y)\to0$ for every finite-order character over every number field. The centered degree-one prime sum can still grow. The signed subexponential estimate asked for in #5571 remains open. [Rational prime-square comparison](https://github.com/mccorvie/riemann-masullo/pull/7445) · [Smoothed rational PNT](https://github.com/mccorvie/riemann-masullo/pull/7527) · [Gevrey detector](https://github.com/mccorvie/riemann-masullo/pull/7571)
