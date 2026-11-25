# Exact cancellation from the Fourier barycenter of the baseline

The following argument strengthens the finite-dimensional convex step for the rational admissible edge probes. It gives the real principal value, actual Sonin correction, higher prime powers, any finite list of full prime places and both polar moments in one construction. It also covers arbitrary finite collections of interior spectral rows. The width $0<b<1/2$ and the finite list of functionals are fixed throughout. [Earlier construction and sources for the local terms](zero-sonin-and-local-probes.md)

Write the even radial profile as $H(x)=P(x)/\cosh(bx)$. Let $\mu_1,\dots,\mu_m$ be real even measures on the punctured real line, allowed either sign, with

$$
 \int \min(1,x^2)\,d|\mu_j|(x)<\infty .
$$

This means a signed Radon measure on $\mathbb R\setminus\{0\}$ with the displayed integrability of its variation. We test it only on functions integrable for that variation. The desired coordinates are $\int P\,d\mu_j$. Such pairings exist for even smooth compact $P$ with $P(0)=0$, since $P(x)=O(x^2)$ near zero.

Choose once any nonnegative compact smooth even $K$ with $K(0)>0$ and strictly positive Fourier transform on the whole real line. The nonnegative bump autocorrelation times a Gaussian supplies one. The probability measure

$$
 d\pi(t)=\widehat K(t)\,dt/(2\pi K(0))
$$

has full support. Its cosine characteristic function is $K(x)/K(0)$, by Fourier inversion and evenness. For a chosen measure set $D_\mu(T)=\int(1-\cos(Tx))\,d\mu(x)$. This is a continuous even real function, bounded by $O_\mu(1+T^2)$. The vector $D(T)=(D_{\mu_j}(T))_j$ has finite expectation under $\pi$.

## A common convex combination

Use the same filtered kernel $G$ with $G(0)=-K(0)$ and positive Fourier transform beyond $R$. For fixed carrier $T>0$ set $u_n=1/(n+1)$, $L_n=2(R+1)/u_n$ and

$$
 P_{n,T}(x)=K(x)+G(x/L_n)\cos((T+u_n)x).
$$

These even numerators vanish at zero. For fixed $T$, the true moment vector tends to

$$
 B(T)
 =\left(\int[K(x)-K(0)\cos(Tx)]\,d\mu_j(x)\right)_j
 = K(0)\left[D(T)-\int D(s)\,d\pi(s)\right].
$$

The first equality uses dominated convergence. The ratios $L_n^{-1}$ and the modulation frequencies are bounded, giving a uniform second derivative bound near zero and a uniform bound elsewhere. The second equality follows by Fourier inversion. Absolute Fubini follows from $|1-\cos(tx)|\le C(1+t^2)\min(1,x^2)$.

Set $V=\operatorname{span}\{B(T):T>0\}$. Then $0$ belongs to the relative interior in $V$ of the convex hull of finitely many $B(T_i)$ with $T_i>0$. Every nonzero linear functional on $V$ evaluates to a continuous even scalar function on this curve having mean zero under the full-support measure $\pi$. Since it takes a nonzero value, it takes both positive and negative values. A compactness argument on the unit dual sphere gives finitely many positive frequencies whose support function is uniformly positive in all directions. If $V=0$, choose an arbitrary positive frequency.

The finite-index vectors lie in exactly the same $V$. In fact, if a linear functional annihilates the limiting curve, its measure combination $\mu$ has $D_\mu$ constant, hence identically zero by $D_\mu(0)=0$. For any real even smooth compact $P$ with $P(0)=0$,

$$
 \int P\,d\mu=-(2\pi)^{-1}\int\widehat P(t)D_\mu(t)\,dt .
$$

This follows by subtracting the Fourier inversion formula at zero and applying the same Fubini estimate. All moment vectors of the original and polar-adjusted numerators therefore lie in $V$. Convergence of the finite set of vertices preserves a smaller relative-interior ball. For each sufficiently large $n$ some convex combination of the finitely many numerators annihilates every coordinate exactly. Since the carriers $T_i$ are fixed and finite, the punctured-divisor argument for these profiles gives the fixed floor $\widehat K(t)>0$ at all ordinates of every locally finite divisor, eventually for each divisor. [Fourier filter and the edge formula](sonin-edge-probe-correction.md)

## Adding the two polar moment conditions

Before taking the convex combination, replace each vertex numerator by $P_{n,T_i}-c_{n,i}(K(\,\cdot-A_n)+K(\,\cdot+A_n))$. Choose $A_n$ beyond the support of $K$. The coefficient is the unique scalar killing the integral against $\cosh(x/2)/\cosh(bx)$. The denominator in the coefficient grows at least as a positive constant times $\exp((1/2-b)A_n)$. Each translated kernel has all its measure coordinates uniformly bounded once its support is outside $[-1,1]$, since the measures have finite variation there. For the fixed finite list of vertices at each $n$, one may choose $A_n$ sufficiently large so that their coefficients are at most $1/4$ in absolute value and the perturbation of each moment vector is at most $1/n$. The finite convex hull still contains the origin for sufficiently large $n$. Each vertex now has both even polar moments zero, and its Fourier response loses at most $2|c_{n,i}|\widehat K(t)\le\widehat K(t)/2$ at any frequency. The final common floor is therefore $\widehat K(t)/2$. The choices require no concentration parameter or asymptotically large carrier. [Polar correction and its normalization](zero-sonin-and-local-probes.md)

## Scope for the normalized arithmetic terms

* The actual real orbital coordinate is $\mu(dx)=J(x)\,dx/\cosh(bx)$, where $J(x)=1/(2|x|)+O(1)$ at the origin and decays exponentially at infinity. It satisfies the hypothesis even though its total variation near zero is infinite.
* The genuine Connes–Consani Sonin remainder has bounded continuous even density $e(x)/\cosh(bx)$ and finite total variation. Killing it together with the real orbital term also kills their actual Sonin trace. Their prolate eigenvalues enter only in verifying that this is the claimed functional. [Theorem 4.7](https://arxiv.org/pdf/2006.13771)
* Any finite list of full rational prime places and the aggregate of every prime power of exponent at least two give finite measures away from zero. The degree-one aggregate over all primes fails the variation requirement at infinity for $0<b<1/2$. [Prime-power calculation](zero-sonin-and-local-probes.md)
* For a complex site with real displacement $a$ and ordinate $t$, the even real part of its Mellin evaluation has density $\cosh(ax)\cos(tx)/\cosh(bx)$ in numerator coordinates. Any finitely many prescribed strictly interior rows $|a|<b$ therefore also qualify, with their multiplicities if desired. At $|a|=b$ this density becomes $\cos(tx)$ and loses finite variation at infinity. For a tested ordinate on the edge, the fixed positive floor directly prevents making the corresponding row vanish.

The independent signed local cancellation is exact for each resulting test. The proof supplies neither an infinite interior spectral-tail bound nor control of the first powers of all primes. All test families, except when explicitly selecting interior spectral rows as additional constraints, can be fixed independently of all divisors and number fields.
