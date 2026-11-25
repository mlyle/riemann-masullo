# A nuclear-norm saving for genuine translated theta convolutions over the rationals

Let $G$ be the rational idèle class group with Tamagawa Haar measure, choose a norm section, write $x=\log|g|$, and let $V$ be the volume of the compact norm-one group. Fix the principal angular character, center $1/2$, full half-width $\beta=1/2$ and degree $s=3$. Let $W=L^2(G,e^{2\beta|x|}(1+x^2)^{s/2}d\mu)$ and let $P$ project orthogonally onto the complement of the genuine polar-free theta space. For arbitrary $H\in C^\infty_c(\mathbb R)$ and $R\ge0$, write $A_R$ for actual left convolution by $V^{-1}H(x-R)$. This normalization gives Mellin multiplier $e^{Rz}\mathcal LH(z)$ with $\mathcal LH(z)=\int_{\mathbb R}H(x)e^{zx}dx$.

For each $B>0$ and all sufficiently large $R$,
$$
 \|P A_R\|_1\ \le\ C_{H,B}
  \exp\left(\frac R2-B\frac{R^{3/5}}{(\log R)^{1/5}}\right).
 \tag{1}
$$
The same bound holds for the fully compressed operator $P A_R P$ and for the absolute value of its trace. Here $\|\cdot\|_1$ is the nuclear norm on the actual weighted Hilbert space. The estimate acts on the entire input space and applies to every fixed smooth compact radial profile. In particular it applies when the two polar moments of the test vanish. With those moments zero, the signed full-width trace is the signed adelic local distribution in the project's explicit formula. The rightmost divisor-free region is the only arithmetic input. This written proof uses the rational critical strip. The signed thin-strip comparison at fixed width $\alpha<1/2$ in #5571 requires a stronger scale. [Hecke common-kernel theorem](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L6596) · [Full-width trace and signed local terms](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L1558) · [Vinogradov–Korobov zero-free region, Theorem 1.1](https://arxiv.org/pdf/2212.06867#page=2)

## Uniform Mellin evaluations and the enclosing contours

For $q\in W$ define its principal-mode evaluation $E_w(q)=\int_G q(g)e^{wx}\,d\mu(g)$. Cauchy–Schwarz bounds its norm uniformly for $|\operatorname{Re}w|\le\beta$, because
$$
 \int_G \frac{|e^{wx}|^2}{e^{2\beta|x|}(1+x^2)^{3/2}}\,d\mu
   \le V\int_\mathbb R(1+x^2)^{-3/2}\,dx .
$$
The evaluations are continuous in operator norm on the closed strip and holomorphic on its interior by domination. Absolute integrability also gives $E_w(A_Rq)=e^{Rw}\mathcal LH(w)E_w(q)$ by Fubini. The output is constant along the compact angular group. All nonprincipal Mellin jets vanish for radial outputs.

Let $\eta(t)=[(\log(e^e+t^2))^{2/3}(\log\log(e^e+t^2))^{1/3}]^{-1}$. This even function is positive with bounded derivative, and the ratio of its values at heights at most one apart lies in a compact subinterval of $(0,\infty)$. The rational zeta zero-free region and the functional equation put every centered positive-order zero $z_\rho=\rho-1/2$ strictly between
$$
 w_\pm(t)=\pm(1/2-c\eta(t))+it
$$
when $c>0$ is small enough. Reduce $c$ so that $c\eta(0)<1/8$. Both curves lie strictly inside the region of analyticity of $E_w$ even at finite height. They can be moved slightly inward or outward, for example by replacing $c$ by $c/2$ or $2c$, while still enclosing all the zeros. This also follows on compact height ranges by discreteness and the zero-free vertical edges. Let $\Omega$ be the interior and orient the two boundary contours with the interior on the left.

On the band $-1\le\operatorname{Re}z\le1$ use
$$
 D(z)=\frac{(z-1/2)\zeta(z+1/2)}{(3+z)^N}.
$$
This function is holomorphic on a neighborhood of that band. Its zeros there are precisely the centered positive-order zeros, with their actual multiplicities. The pole at $s=1$ has been removed and the trivial zeta zeros lie outside the band. Take the integer $N$ large enough that $|D(u+it)|\le C(1+|t|)^{-4}$ on the full band, using polynomial vertical-strip growth from Euler–Maclaurin. On both contours, including the indicated small shifts, one has
$$
 |1/D(w_\pm(t))|\ll (1+|t|)^m \tag{2}
$$
for a fixed $m$. Here is a direct check of (2). At large $|t|$, the closed disk centered at $s_0=1+c\eta(t)+it$ with radius $6c\eta(t)$ is free of zeros and the pole for sufficiently small $c$. The uniform comparability of $\eta$ on unit intervals gives this from the region above. On this disk $\log|\zeta(s)|\le C\log(2+|t|)$. At its center the Euler product bounds $|\log\zeta(s_0)|$ by $\log\zeta(1+c\eta(t))\ll 1+\log(1/\eta(t))$, using the Euler branch. Borel–Carathéodory bounds the continuation of that logarithm by $O(\log(2+|t|))$ on the concentric disk of radius $4c\eta(t)$. This includes the right-hand contours with coefficients from $c/2$ to $2c$. On the left contours the functional equation reflects to these right contours. Stirling's formula bounds both the functional-equation gamma factor and its reciprocal by fixed powers of height on this band. On bounded height ranges the denominator is zero-free by the choice of $c$. Together with the polynomial factors in $D$ this proves (2).

## A nuclear interpolating operator

Write $F_q(w)=e^{Rw}\mathcal LH(w)E_w(q)$. Integration by parts gives $|\mathcal LH(u+it)|\ll_{H,j}(1+|t|)^{-j}$ uniformly on our bounded real band for every $j$. For $|\operatorname{Re}z|<1$ set
$$
 G_q(z)=\frac1{2\pi i}\int_{\partial\Omega}
     F_q(w)\frac{D(w)-D(z)}{(w-z)D(w)}\,dw. \tag{3}
$$
This is holomorphic on the band since the quotient is regular at $w=z$ and the boundary integrals converge locally normally by (2). Inside $\Omega$, Cauchy's formula makes $G_q-F_q$ divisible by $D$ near every zero. Outside $\overline\Omega$ the first term in the split numerator has zero Cauchy integral. Fix two lines $u_\pm=\pm3/4$. Thus for every $z$ on either line,
$$
 G_q(z)=-\frac{D(z)}{2\pi i}
   \int_{\partial\Omega}\frac{e^{Rw}\mathcal LH(w)E_w(q)}{(w-z)D(w)}\,dw .
 \tag{4}
$$
Here $|w-z|\ge1/4$.

For clarity, the vertical lines in (4) invert to the same function. On every intermediate vertical line (3) decays as $O_{R,H}(\|q\|(1+|\operatorname{Im}z|)^{-3})$, uniformly in its real coordinate. Use the two slightly deformed contours on the relevant side when $z$ is close to an original curve. At least one new contour stays distance $\gg\eta(\operatorname{Im}z)$ from $z$, since the two graphs are horizontally separated by this much there and have bounded slopes. Their deformation crosses no zeros of $D(w)$ and stays in the open Mellin strip, where $F_q$ is holomorphic. The potential diagonal singularity in (3) is removable. After the numerator is split, the Cauchy formula on finite rectangles with the curved vertical sides contributes $F_q(z)$ if $z$ is inside, and zero otherwise. The other term is $O_{R,H}(\|q\||D(z)|/\eta(\operatorname{Im}z))$. Horizontal far ends tend to zero by rapid decay, using (2) on the swept zero-free collars. These estimates prove the stated uniform decay and justify shifting the inverse transform across the band.

Invert $G_q$ using the right line for $x\ge0$ and the left line for $x<0$, and divide by $V$ to obtain a radial representative $T_Rq$ whose class-Haar Mellin transform is $G_q$. Indeed these lines give exponential tails with exponents $\pm3/4$. Fourier inversion then recovers $G_q$ throughout the open band between them. Equation (4) gives $T_R$ as a Bochner integral of rank-one operators. Explicitly, for $w$ on the boundary let
$$
 v_w(x)=-\frac1{2\pi V}\int_\mathbb R
  \frac{D(u_\pm+iv)e^{-(u_\pm+iv)x}}{w-u_\pm-iv}\,dv
$$
with sign chosen by the half-line containing $x$. Since $\int |D(u_\pm+iv)|dv$ is bounded and the lines are separated, $|v_w(x)|\le C e^{-3|x|/4}$. It follows that $\sup_w\|v_w\|_W<\infty$. These vectors vary continuously along each contour by dominance, as do the functionals $E_w$. The integral in the nuclear space is therefore well-defined and equals the interpolation operator by Fubini:
$$
 T_R=\frac1{2\pi i}\int_{\partial\Omega}
        \frac{e^{Rw}\mathcal LH(w)}{D(w)}\,(v_w\otimes E_w)\,dw .
$$
The orientation and factor $i$ have modulus one in the estimate apart from the stated $2\pi$. Equation (3) proves that principal jets of $T_Rq$ coincide with those of $A_Rq$ through their full multiplicities. All other angular jets vanish for both radial outputs. The exact genuine common-kernel theorem therefore gives $P A_R=P T_R$, whence
$$
 \|P A_R\|_1\ll\int_{\partial\Omega}
       \left|\frac{e^{Rw}\mathcal LH(w)}{D(w)}\right|\,|dw| . \tag{5}
$$

## The size of the integral

The left contour gives $O_H(e^{-3R/8})$. On the right contour use (2) and smoothness of $H$ to obtain, for each arbitrarily large fixed integer $j$,
$$
 O_{H,j}\left(e^{R/2}\int_\mathbb R
      e^{-cR\eta(t)}(1+|t|)^{-j}\,dt\right).
$$
Put $S(R)=R^{3/5}(\log R)^{-1/5}$ and split at $T=\exp(\kappa S(R))$, for a fixed small $\kappa>0$. At $|t|\le T$, one has $R\eta(T)\asymp\kappa^{-2/3}S(R)$ as $R\to\infty$, with limiting comparison constants independent of the fixed $\kappa$. First take $\kappa$ small enough that $cR\eta(T)\ge2B S(R)$ for all sufficiently large $R$. On $|t|>T$ the tail is $O(T^{1-j})$. Take $j$ large enough that $(j-1)\kappa\ge2B$. This proves (1). Constants and the starting height may depend on the chosen $B$.

For fixed small $\alpha$, (1) still permits growth faster than $e^{\alpha R}$. Multiplying the *compressed* operator on either side by contractions preserves (1). Moving an arbitrary physical output cutoff through $P$ would require a separate commutator estimate, since the original localized trace uses the order $M A_R P$. The preceding statements about the fully exhausted trace and the actual nuclear-norm saving require no such commutation.

## The exact rate for one compact polar-free multiplier

In the rational principal chart write $\lambda=\sup_\rho\operatorname{Re}(\rho-1/2)\in[0,1/2]$. If $\mathcal LH(z_\rho)\ne0$ at every positive-order zero, then
$$
 \lim_{R\to\infty}R^{-1}\log\|P A_R\|_1
 =\lim_{R\to\infty}R^{-1}\log\|P A_R P\|_1=\lambda. \tag{6}
$$
For any such zero choose a fixed radial Gaussian input $q$ of nonvanishing Mellin transform there. The functional $\ell_\rho$ annihilates the theta closure, so $\ell_\rho(Pq)=\ell_\rho(q)\ne0$. Hence
$|\ell_\rho(P A_R Pq)|=e^{R\operatorname{Re}z_\rho}|\mathcal LH(z_\rho)\ell_\rho(q)|$ and boundedness gives the desired lower exponent. Equation (1) gives the upper bound when $\lambda=1/2$. Otherwise fix $\lambda<\nu<1/2$. Reflection puts all the zeros between the two vertical contours $\operatorname{Re}w=\pm\nu$. The polynomial reciprocal bound (2) is now simpler. Take a fixed disk centered to the right of $\operatorname{Re}s=1$ which reaches the line $\operatorname{Re}s=1/2+\nu$ on a strictly smaller concentric disk and has left edge strictly to the right of $\operatorname{Re}s=1/2+\lambda$. At large heights the disk is free of zeros and the pole. Borel–Carathéodory and the Euler bound at the center again give $1/|\zeta|\ll_\nu(1+|t|)^{m_\nu}$ on the right contour and a collar. Reflection handles the left side. On compact heights $(s-1)\zeta(s)$ is bounded away from zero there. The construction in (3)–(5) therefore gives $\|P A_R\|_1\ll_{\nu,H}e^{\nu R}$. Let $\nu$ decrease to $\lambda$.

A single field-independent compact smooth polar-free profile detects all the required zeros. For an explicit choice, let $g$ be the density of the sum of independent uniforms on $[-2^{-k},2^{-k}]$ for $k\ge1$. The probability measures converge by absolute convergence of the supports. Their Fourier transform decays faster than any power by retaining any fixed number of sinc factors, each of size $O_k((1+|t|)^{-1})$ on the real line, while the remaining factors have modulus at most one. Fourier inversion gives a smooth compact density. Its bilateral transform is $\prod_{k\ge1}\sinh(2^{-k}z)/(2^{-k}z)$, with smooth value $1$ for a factor at zero. The sum of deviations of the tail factors from $1$ converges locally uniformly by $\sum4^{-k}<\infty$, so its only zeros are on the imaginary axis. Put $g_1(x)=e^x g(x)$ and $H=g_1''-g_1/4$. Then $\mathcal LH(z)=(z^2-1/4)\mathcal Lg(z+1)$, which vanishes at the two polar moments and is nonzero everywhere in the open critical strip. Translating its support to any prescribed positive location multiplies the transform by a nonvanishing exponential. Thus the rational critical-zero assertion is equivalent to a subexponential nuclear-norm bound along the positive integer translates of this one compact smooth genuine convolution. The proof of (6) identifies the exact exponent even when it is positive.
