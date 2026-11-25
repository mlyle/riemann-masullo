# Admissible probes with zero Sonin correction and prescribed local cancellations

Fix a rational width $0<b<1/2$. There is a sequence of real even compact smooth radial profiles $H_n$ with all the following properties.

* They vanish at zero and have zero polar Mellin moments at both $\pm1/2$.
* The real principal value and the actual Connes–Consani Sonin correction each vanish exactly. In particular the actual Sonin trace vanishes.
* They annihilate the total rational finite-place contribution of all powers $p^k$ with $k\ge2$, and the full orbital contribution of each member of any prescribed finite list of primes.
* There is a fixed function $q(t)>0$ such that for every locally finite divisor in the complex plane, all sufficiently late profiles have real Laplace response at least $q(t)$ at $\pm b+it$ for **all** its critical-strip ordinates. The same radial numerators divided by $\cosh(vx)$ provide this edge floor at every width $v$. The asserted local cancellations occur at $v=b$.

The choices use only the known kernels and the selected width and finite prime list. The remaining signed degree-one prime aggregate is outside the estimate used here. All the constructions in this note are written proofs. [Adelic realization and Lean proof of the original probe floor](../RiemannMasullo/Ch12_TraceGeometric/Sec5_AdmissibleEdgeProbes.lean) · [Exact Sonin source and signs](sonin-edge-probe-correction.md)

## A single correction

The preceding calculation gives two sequences $H_n^+,H_n^-$ of probes sharing a strictly positive eventual floor and satisfying $E(H_n^+)>0>E(H_n^-)$ for sufficiently large $n$. For each such $n$ set

$$
 \lambda_n=\frac{-E(H_n^-)}{E(H_n^+)-E(H_n^-)},\qquad
 H_n=\lambda_n H_n^++(1-\lambda_n)H_n^- .
$$

Then $0<\lambda_n<1$, $E(H_n)=0$, and every common edge floor survives. The finite-dimensional argument below adds the other constraints simultaneously.

## Measures small near the identity

For an even numerator $P$ write the radial test as $H(x)=P(x)/\cosh(bx)$. Let $\mu_1,\dots,\mu_m$ be any finite collection of real even signed measures of finite total variation for which $|\mu_j|([-r,r])=o(r)$ as $r\downarrow0$. The corresponding desired functionals of $H$ are $\int P\,d\mu_j$. These hypotheses hold for the Sonin correction with $d\mu=e(x)\,dx/\cosh(bx)$ since $e$ is continuous, bounded, even and $e(0)=0$. They also hold for measures supported away from zero that have finite weighted total variation.

Write $F(T)=(\int\cos(Tx)\,d\mu_j)_j$ and let $V$ be its real span. For every nonzero linear functional on $V$, the scalar function $\ell(F(T))$ takes both signs. Indeed, extend $\ell$ to $\mathbb R^m$ and put $\nu=\sum_j\ell_j\mu_j$. Then $\widehat\nu(T)=\ell(F(T))$ since $\nu$ is even. Gaussian-regularized Fourier inversion at zero tends to zero under $|\nu|([-r,r])=o(r)$. Explicitly the approximate identity is $g_\eta(x)=(4\pi\eta)^{-1/2}e^{-x^2/(4\eta)}$. On $|x|\le r_0$, integration by parts in radius against $|\nu|([-r,r])\le \epsilon r$ bounds its integral by a universal constant times $\epsilon$. Outside this neighborhood the integral tends to zero by finite variation. If $\widehat\nu$ had one sign, monotone convergence for $e^{-\eta T^2}|\widehat\nu(T)|$ would force $\widehat\nu=0$, contradicting that $\ell$ is nonzero on $V$. The frequencies of the two signs can be chosen positive by evenness and continuity.

Therefore there are finitely many positive $T_i$ for which $0$ lies in the relative interior of $\operatorname{conv}\{F(T_i)\}$. To see this directly, for each unit functional on $V$ choose a frequency on its positive side. The same strict inequality holds in a neighborhood of that functional. Compactness of the unit sphere gives a finite choice of frequencies with uniformly positive support function in every direction. The case $V=0$ requires no such constraints. Fourier uniqueness for finite measures also shows that any linear relation vanishing on every $F(T)$ annihilates the integrals of every compact profile. Thus all moment vectors below lie in this same $V$.

Use a nonnegative even kernel $K$ of compact support with $K(0)>0$ and strictly positive Fourier transform, as supplied by the nonnegative bump autocorrelation multiplied by the Gaussian in the project. Put $K_M(x)=K(Mx)$. The finite list of probes with carriers $T_i$ from the preceding note has moment-vector limits

$$
 d_M-K(0)F(T_i),\qquad d_M=\left(\int K(Mx)\,d\mu_j(x)\right)_j .
$$

Each measure has zero atom at zero, so $d_M\to0$. For large fixed $M$, their convex hull still contains a ball around zero in $V$. By dominated convergence the actual moment-vector vertices at index $n$ approach these limits. A fixed smaller ball stays in their convex hull for all sufficiently large $n$. Convex weights then annihilate all these moment coordinates exactly.

## The genuine real principal value

The real orbital density $J(x)=e^{-|x|/2}/(1-e^{-2|x|})$ is singular at zero. Set $j_b(x)=J(x)/\cosh(bx)$. For the same $K_M$ and fixed carrier $T$, the limiting real orbital value is

$$
 h_M(T)=\int (K(Mx)-K(0)\cos(Tx))j_b(x)\,dx .
$$

For fixed $M$ the passage $n\to\infty$ is justified separately on $|x|\le1$ and its complement. The even compact numerators vanish at zero and have uniformly bounded second derivatives there, since $T+1/(n+1)$ is bounded and $L_n^{-1}$ is bounded. This gives an $O(x^2)$ majorant near zero. On the complement boundedness and the exponential decay of $j_b$ suffice.

Two elementary limits supply the extra coordinate. As $M\to\infty$ with $T$ fixed,

$$
 h_M(T)=-K(0)\log M+O_{K,T,b}(1).
$$

Indeed $j_b(x)=1/(2|x|)+O(1)$ near zero. For a fixed support radius $D>0$ of $K$, split the singular integral at $D/M$. On $|x|\le D/M$, the bounded integral of $|K(u)-K(0)|/|u|$ controls the difference by scaling. On $D/M<|x|\le1$, the constant part of $\cos(Tx)$ yields the displayed logarithm and the remainder is integrable.

Conversely, for fixed $M$ one has $h_M(T)=K(0)\log T+O_{K,M,b}(1)$ as $T\to\infty$. Subtract $h_M(0)$ and split the remaining integral of $(1-\cos(Tx))j_b(x)$ at $|x|=1$. The bounded part of the density is uniformly integrable there, while $\int_0^1(1-\cos(Tx))dx/x=\log T+O(1)$ for $T\ge1$ by integration by parts on $[1,T]$. These logarithms have coefficient one in the rational real Haar normalization.

Increase $M$ until all of the finitely many original vertices have last coordinate $h_M(T_i)<-1$ and their projections contain a ball of radius $r>0$ around zero in $V$. Write $C$ for a finite bound on the absolute values of these last coordinates. For an additional arbitrarily high carrier $T$ its vector of measure coordinates is bounded uniformly in $T$ by finiteness of the measures. Choose a small fixed convex weight $\lambda>0$ such that for every projected target in a sufficiently small ball about zero one can offset the high vertex's projected displacement with weight $1-\lambda$ in the original ball. Now choose $T$ large enough that $\lambda h_M(T)-(1-\lambda)C>1$. At every such target the old vertices attain a last coordinate below $-1$, and a mixture including this high vertex attains one above $1$. By convexity the enlarged hull contains a neighborhood of zero in $V\times\mathbb R$. This interior margin will also absorb the next perturbation.

## Killing both polar moments

Let $P_{i,n}$ be each of these finitely many numerators at index $n$. For $A$ larger than the support radius of $K_M$ put

$$
 U_A(x)=K_M(x-A)+K_M(x+A),\qquad
 p(P)=\int P(x)\frac{\cosh(x/2)}{\cosh(bx)}\,dx .
$$

Since $K_M$ is nonnegative and nonzero, $p(U_A)\gg_{K,M,b}e^{(1/2-b)A}$. Evenness makes both polar moments of $P/\cosh(bx)$ equal to $p(P)$ up to the positive adelic class-volume factor. Replace each numerator by $P_{i,n}-c_{i,n}U_A$ with $c_{i,n}=p(P_{i,n})/p(U_A)$. For each fixed $n$ choose $A$ sufficiently large that $|c_{i,n}|\le1/4$ for every vertex and that all changes in the finite vector of measure and real orbital coordinates tend to zero as $n\to\infty$. This is possible because the translated kernels have uniformly bounded measure moments and their real orbital integrals tend to zero at infinity. Their supports avoid the origin.

The correction to the edge cosine transform is $-2c_{i,n}\widehat K_M(t)\cos(At)$. It costs at most half the original fixed floor $\widehat K_M(t)$ at each formerly detected ordinate. Polar cancellation is exact for each vertex. The preceding interior margin survives, so for every sufficiently large $n$ choose convex weights making the perturbed measure and real orbital vector zero. The result retains the fixed floor $q(t)=\widehat K_M(t)/2$ at all sufficiently late indices for each divisor. The finitely many earlier indices can be filled by repeating one of the resulting profiles. [Laplace response and divisor gap](sonin-edge-probe-correction.md)

## Rational finite-place range

For the trivial rational character the nonunit part of the $p$-orbital distribution on a norm-one-vanishing test is $\log p\sum_{k\ge1}p^{-k/2}(H(k\log p)+H(-k\log p))$. The unit term vanishes. After passing to the numerator coordinates its masses acquire the factor $1/\cosh(bk\log p)$. Each fixed prime then gives a finite measure supported outside $(-\log2,\log2)$. Over **all** primes the terms with $k\ge2$ also give one finite measure, since

$$
 \sum_p\sum_{k\ge2}(\log p)p^{-k(1/2+b)}
 \le \frac{1}{1-2^{-(1/2+b)}}\sum_{m\ge2}\frac{\log m}{m^{1+2b}}<\infty.
$$

Those measures and the Sonin correction can therefore all be included above. The degree-one measure at all primes has infinite weighted total mass when $0<b<1/2$, already by the prime number theorem. The construction leaves this infinite aggregate and the actual global signed width comparison unresolved. [Normalized local terms](../transcription/chapters/chapter-12.md)
