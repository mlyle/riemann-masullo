# How much of one shared critical Riesz lift survives the wide projection?

Use rational $\zeta$, center $1/2$, full width $\beta=1/2$, degree $s=3$, and a fixed narrow width $0<\alpha<1/4$. Take a single known critical zero $1/2+i\gamma$. Write $\lambda=\sup_\rho\operatorname{Re}(\rho-1/2)$ as before. The canonical narrow Hilbert representative of the shared zeroth evaluation at $i\gamma$ is the radial function
$$
 r_\alpha(x)=e^{-i\gamma x}e^{-2\alpha|x|}(1+x^2)^{-s/2}.
$$
It belongs to the spectral orthogonal complement in $W_\alpha$. This follows directly from the project's bilinear Haar jet and its annihilation of the genuine theta space. Fix a real compact smooth $H$ with $\mathcal LH(2\alpha+i\gamma)\ne0$. The explicit compact polar-free detector in the previous note works simultaneously for all these $\alpha,\gamma$. Use the normalization $A_H$ of convolution by $V^{-1}H(\log|g|)$ and put $f=A_H r_\alpha$. In particular this is one actual output entering the mixed-width cutoff map in the signed subtraction formula. [Cutoff-strengthened operator, equation (6)](https://github.com/mlyle/riemann-masullo/blob/e27d9d34d86b1aea62bc4fff253c02707c912e8c/research/width-restriction-signed-defect.md#finite-physical-cutoffs-admit-an-exact-bounded-cross-width-factorization) · [One compact polar-free detector](https://github.com/mlyle/riemann-masullo/blob/4ffa1ed247556cd22edba631662ca6bc57d34dee/research/rational-nuclear-theta-convolution.md#the-exact-rate-for-one-compact-polar-free-multiplier)

## Unconditional ambient divergence

At the positive end,
$$
 f(x)=(C+o(1))e^{-(2\alpha+i\gamma)x}x^{-s},
 \qquad C=\mathcal LH(2\alpha+i\gamma)\ne0 .
$$
Indeed the ratio $r_\alpha(x-u)/r_\alpha(x)$ tends uniformly to $e^{(2\alpha+i\gamma)u}$ on the compact support of $H$. At either end, $f$ and every fixed derivative are $O_{H,j}(e^{-2\alpha|x|}(1+|x|)^{-s})$, by convolving with derivatives of $H$. Thus $f$ fails to belong to $W_\beta$ whenever $\beta>2\alpha$. For a true project cutoff of radius $\Lambda=e^L$, the positive shell $[L-2,L-1]$ lies on its plateau for all large $L$, by the stipulation $\varepsilon<\Lambda^{-1}$. Consequently the wide ambient norm of $m_L f$ is at least $c_H e^{(\beta-2\alpha)L}(1+L)^{-s/2}$. This holds for every such cutoff. The obstruction lives before the wide quotient is taken.

## Exact growth after projecting an average of genuine radius cutoffs

For each radius $e^{L+u}$, $0\le u\le1$, take any jointly measurable choice of project-admissible cutoff $m_{L+u}$, with arbitrary allowed transition width. Let $\kappa\in C_c^\infty([0,1])$ be a fixed nonnegative probability density whose bilateral transform has zeros only on the imaginary axis. For example affine-rescale the density of the symmetric infinite dyadic convolution from the linked note. Write
$$
 d_L=q_\beta\left(\int_0^1\kappa(u)m_{L+u} f\,du\right)\in Q_\beta .
$$
This averages actual eligible cutoffs before measuring the norm. It satisfies
$$
 \lim_{L\to\infty}\frac{\log(1+\|d_L\|)}{L}=(\lambda-2\alpha)_+ . \tag{1}
$$
If $\lambda<2\alpha$, the vectors $d_L$ even converge in $Q_\beta$ with error $O_{\nu,H}((1+L)e^{-(2\alpha-\nu)L})$ for every $\lambda<\nu<2\alpha$. In particular RH gives bounded, convergent wide quotient classes for these averaged physical cutoffs, although their ambient wide norms diverge. Conversely subexponential growth in (1) at any sequence of narrow $\alpha$ decreasing to zero would force the rational RH. The upper assertion concerns the norm of the averaged vectors. It does not bound the average of their norms.

To prove (1), write $m_L^0=\int_0^1\kappa(u)\mathbf1_{[-L-u,L+u]}du$. This profile is smooth, supported on $[-L-1,L+1]$, equals one on $[-L,L]$ and has all derivatives bounded independently of $L$. Inversion symmetry and the positive plateau show that each actual cutoff differs from its sharp interval on two log intervals of length $O(e^{-2(L+u)})$. The resulting error in $W_\beta$ for the packet $f$ is
$$
 \ll e^{(\beta-2\alpha-1)L}(1+L)^{-s/2}
$$
uniformly in $u$ and in the allowed cutoff. This tends to zero exponentially since $\beta=1/2$. It is enough to treat $q_\beta(m_L^0 f)$.

For a zero $z_\rho=b+i t$ with $b>2\alpha$, let $a=b-2\alpha+i(t-\gamma)$. Up to the fixed Haar factor $V$ the evaluation at that zero on the sharp radius $Y$ has asymptotic
$$
 \int_{-Y}^Y f(x)e^{z_\rho x}dx
 =\left(C/a+o(1)\right)e^{aY}Y^{-s}.
$$
The negative half is bounded, since $b>0$. On the positive half take $x=Y-v$ and integrate $e^{-av}$, obtaining $1/a$ by dominated convergence on $0\le v\le Y/2$. The part below $Y/2$ is exponentially smaller. The convergence remains uniform for $Y=L+u$ on $0\le u\le1$. The average multiplies its leading coefficient by $\mathcal L\kappa(a)\ne0$ since $\operatorname{Re}a>0$. Boundedness of this actual wide functional yields $\liminf\ge b-2\alpha$. Nonnegativity of $\log(1+\|\cdot\|)$ supplies the floor at zero. The same positive lower exponent holds for individual admissible cutoffs before averaging because of their exponentially small wide deviation from the sharp interval.

For the upper bound first suppose $\lambda<\beta$ and choose $\lambda<\nu<\beta$. All centered zeros lie strictly between the lines $\operatorname{Re}z=\pm\nu$ by rational reflection. Use the zero-free line interpolation from the preceding calculation, with $D(z)=(z-1/2)\zeta(z+1/2)/(3+z)^N$ for large fixed $N$. On those two lines and a collar its reciprocal is polynomially bounded. On outer inversion lines $\operatorname{Re}z=\pm3/4$ it decays faster than $(1+|\operatorname{Im}z|)^{-3}$ by the choice of $N$. For each fixed derivative count $j$ and $u=\pm\nu$, repeated integration by parts in the compact smoothed profile gives
$$
 |\mathcal L(m_L^0 f)(u+it)|
 \ll_{j,H,\nu}(1+L)e^{(\nu-2\alpha)_+L}(1+|t|)^{-j}.
$$
The uniform derivative bounds and exponential tail of $f$ give this same bound for each integral after differentiating $e^{ux}m_L^0f$. Choosing $j$ above the reciprocal growth and applying the two-line interpolation matches all completed jets, with wide representative of norm $O_{H,\nu}((1+L)e^{(\nu-2\alpha)_+L})$. Sending $\nu$ down to $\lambda$ proves the upper exponent. If $\lambda=\beta$, the elementary ambient bound $O_H((1+L)e^{(\beta-2\alpha)L})$ suffices. If $\lambda<\nu<2\alpha$ the same argument applied to two profiles $m_{L'}^0f-m_L^0 f$ for $L'\ge L$ gives the stated Cauchy rate, since every differentiated integrand vanishes on $[-L,L]$ and has tails bounded uniformly by a constant times $e^{-(2\alpha-\nu)|x|}$. The actual-mask error is smaller. [Full zero-free interpolation estimates and their actual quotient interpretation](https://github.com/mlyle/riemann-masullo/blob/4ffa1ed247556cd22edba631662ca6bc57d34dee/research/rational-nuclear-theta-convolution.md)

This test concerns the physical-radius dependence of one shared-mode lift. It identifies the exact surviving quotient growth in an averaged instance of one factor of the finite-cutoff formula. A signed thin-width estimate for the trace of the full composite operator, with its complete input space and the required order of limits, remains open.
