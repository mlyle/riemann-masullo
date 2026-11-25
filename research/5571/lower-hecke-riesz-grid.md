# A lower bound on sparse degree-one prime sums for all Hecke characters

Fix a number field $F$, a norm section and a unitary idele class character $\chi$ trivial on the section. Write $\delta=1$ for the trivial character and $0$ otherwise. For a rational prime $p$, put
$$
a_\chi(p)=(\log p)\sum_{\substack{\mathfrak p\mid p,\ f(\mathfrak p/p)=1\\
\chi\text{ unramified at }\mathfrak p}}\chi_{\mathfrak p}(\varpi_{\mathfrak p}),
\qquad P_\chi(N)=\sum_{p\le N}(N-p)\Re a_\chi(p).
$$
The convention for the local value is the Euler-factor convention. Taking the inverse character gives the same real sum. Ramification of the rational prime in the field does not remove its unramified degree-one local character values. [The degree-one coefficient](https://github.com/mccorvie/riemann-masullo/pull/7569)

Choose any increasing unbounded integer grid $N_j$ with $N_{j+1}-N_j=O(N_j^{1-\alpha})$ for some fixed $\alpha>0$. Then the nontrivial zeros of $L(s,\chi)$ all have real part $1/2$ if and only if, at every sufficiently late grid point,
$$
 P_\chi(N_j)\ \ge\ \frac{\delta N_j^2}{2}-N_j^{3/2}\log(2N_j).
$$
The coefficient of the slack is one. The starting index can depend on the field, character and grid. In particular the single predetermined grid $N_j=j^{100}$ works simultaneously as a choice of grid for every character. Alternatively one can require $P_\chi(N_j)\ge\delta N_j^2/2-O_\varepsilon(N_j^{3/2+\varepsilon})$ for every $\varepsilon>0$. No one-sided arithmetic estimate of this strength for all characters is known here.

## The arithmetic transform

Let $R_\chi(x)=\sum_{N I\le x}(x-N I)\Lambda_\chi(I)$, including all nonzero integral ideals, and $B_\chi(x)=\Re R_\chi(x)-\delta x^2/2$. The sum is finite and piecewise affine before centering. Its forward difference at an integer $n$ is exactly the unsmoothed Hecke von Mangoldt sum $\psi_\chi(n)$. For $\Re s>1$,
$$
 G(s)=\int_1^\infty B_\chi(x)x^{-s-2}\,dx
 =-\frac{(L'/L)(s,\chi)+(L'/L)(s,\overline\chi)}{2s(s+1)}
   -\frac{\delta}{2(s-1)}.
$$
The real arithmetic part averages the two analytic logarithmic derivatives. It is important to conjugate the argument as well when obtaining the second derivative from the first. The scalar computation is $\int_q^\infty (x-q)x^{-s-2}dx=q^{-s}/(s(s+1))$. Absolute convergence justifies exchange with the ideal sum. The principal pole at one cancels. Normalization excludes a nontrivial pure norm character with a shifted pole.

The formalization checks both Mellin identities, the exact forward difference, affine interpolation, grouping by rational norm and the uniform estimate
$$|\Re R_\chi(x)-P_\chi(x)|\le C[F:\mathbb Q]x\sqrt{x}.$$
The last estimate follows because every remaining rational norm is a composite prime power and $0\le(x-n)_+\le x$. [Lean source](https://github.com/mlyle/riemann-masullo/blob/d4d9b67345d5757fd7ddcbeccabb264558c83617/RiemannMasullo/Ch13_ZerosHecke/HeckeRieszMellin.lean) · [Prime-power majorant](https://github.com/mccorvie/riemann-masullo/pull/7436)

## Why the lower sign excludes real zeros, too

Suppose $1/2<r<1$ and $B_\chi(x)\ge-K x^{1+r}$ at all real $x\ge1$, enlarging $K$ on any bounded initial segment. The Mellin transform of the nonnegative function $B_\chi(x)+Kx^{1+r}$ equals $G(s)+K/(s-r)$ on its initial half-plane. If its abscissa of convergence $c$ were greater than $r$, Landau's theorem would force a singularity at the real point $c$. In this region every remaining possible real singularity of $G$ is a simple pole of residue
$$-\frac{m_\chi(c)+m_{\overline\chi}(c)}{2c(c+1)}<0.$$
A transform of a nonnegative function is nonnegative at real points immediately to the right of its abscissa. A simple pole with that residue tends to minus infinity there. Thus $c\le r$ and the integral furnishes a holomorphic representative throughout $\Re s>r$. At a complex zero $\rho$ the analogous numerator is a sum of nonnegative multiplicities with a common nonzero factor. Coincident reflected residues cannot cancel. Hence $L(s,\chi)$ has no zero with real part greater than $r$. This handles a possible real exceptional zero without assuming a zero-free real interval. [Landau for positive measures](https://github.com/mccorvie/riemann-masullo/pull/7555)

## From isolated samples to the full half-plane

Let $\Theta$ be the supremum of the real parts of the nontrivial zeros. For fixed field and character the classical estimate
$$
\psi_\chi(x)-\delta x=O_{F,\chi,\varepsilon}(x^{\Theta+\varepsilon})
$$
holds for every $\varepsilon>0$. When $\Theta=1$ the elementary coefficient bound suffices. When $\Theta<1$, apply truncated Perron first at a half-integer and move the integral to a vertical line strictly between $\Theta$ and $\Theta+\varepsilon$. The logarithmic derivative there and on the intervening horizontal segments at large height is $O_\varepsilon(\log^2(2+|t|))$ by the local Hadamard expansion and the unit-height zero count. Take truncation height of order $x^2$. The bound $|a_\chi(n)|\le[F:\mathbb Q]\Lambda(n)$ and the half-integer separation bound the Perron error by $O_F(x\log^2(2x)/x^2)$; taking the neighboring half-integer extends the estimate to arbitrary cutoffs with an additive $O(1)$ change in the linear main term. For the fixed-character analytic inputs see C. S. Rajan, §§1–2, including (2). These bounds also apply after a fixed imaginary translation, so changing the norm section for a non-principal character only changes the constants. [Rajan, *Distribution of Values of Hecke Characters of Infinite Order*](https://matwbn.icm.edu.pl/ksiazki/aa/aa85/aa8537.pdf)

If $\Theta>1/2$, the derivative of $B_\chi(x)$ away from integer breakpoints is $\Re\psi_\chi(x)-\delta x$. On each sample gap at scale $X$, the preceding estimate bounds the change in $B_\chi$ by $O_\varepsilon(X^{1+\Theta-\alpha+\varepsilon})$. The sampled lower bound and the $O_F(X^{3/2})$ composite error therefore give a lower bound everywhere by $-O(X^{1+r})$ for some $r$ strictly between $\max(1/2,\Theta-\alpha)$ and $\Theta$. Choose $\varepsilon$ strictly inside this margin. The one-sided argument above forces $\Theta\le r$, a contradiction. Functional equation and conjugation supply the other half of the critical strip.

In the other direction assume the fixed-character Riemann hypothesis. Mellin inversion for $R_\chi(x)$ on a line right of one and shift to $\Re s=1/4$ give the main term $\delta x^2/2$ and the zero sum $-\sum_\rho m_\chi(\rho)x^{1+\rho}/(\rho(\rho+1))$. The shifted-line integral is $O_{F,\chi}(x^{5/4})$: it stays a fixed distance from the nontrivial zeros and from the trivial zeros of the finite L-function. The unit-height count and Stirling give an integrable vertical majorant of order $\log^2(2+|t|)/(1+t^2)$. Choose horizontal heights avoiding ordinates by a constant multiple of $1/\log T$ to make the horizontal contributions vanish. The zero sum has absolute bound $O_{F,\chi}(x^{3/2})$, including any central multiplicity. The composite-norm estimate then gives the eventual displayed inequality since $\log(2N)\to\infty$.

For the trivial character, $a_1(p)/\log p$ simply counts residue-degree-one primes above $p$. Testing these nonnegative integer local counts for every number field suffices for all **finite-order** Hecke characters: in the finite abelian class field cut out by such a character, Dedekind zeta factors as the product of its Hecke factors, and no factor has an interior pole that can cancel a zero. The general criterion above also covers infinite-order characters. Quantification over all normalized characters matches the repository’s equivalence between exterior cancellation and absence of off-line zeros in Theorem 12.5.1.1, pp. 519–520. [Artin formalism, formulas (39)–(42)](https://math.uchicago.edu/~emerton/pdffiles/reciprocity.pdf) · [Formal exterior-zero equivalence](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L1174)

The full equivalence in this note is a classical derivation. The linked Lean file proves the stated arithmetic inputs. The square-prefix sign criterion and verified finite ranges for the distinct rational two-cosine statistic use additional arguments. [Rational square-prefix results](https://github.com/mlyle/riemann-masullo/tree/94ece7d08889593fc40b4f31176b5dc7b8a1c2b1/research/5571/signed-riesz-margin)
