# The genuine theta distance of a translated Gaussian

Fix a number field, a norm section, and a unitary Hecke character $\chi$ normalized to be trivial on that section. Let $x=\log|g|$ in the idèle class group. Use Tamagawa Haar measure and the project's strip Hilbert space $W$ at center $a=1/2$, half-width $\beta=1/2$, and degree $s=3$. The squared weight relative to Haar measure is $w(x)=e^{2\beta|x|}(1+x^2)^{s/2}$. Let $P$ be the orthogonal projection onto the complement of the **genuine closed polar-free theta space** in $W$. For $R\geq0$ put
$$
 h(x)=(2\sqrt\pi)^{-1}e^{-x^2/4},\qquad h_R(g)=\chi(g)^{-1}h(x-R).
$$
Let $\lambda_\chi=\sup_{\rho}\operatorname{Re}(\rho-1/2)$ over the positive-order zeros of the completed Hecke function for $\chi$. This set is nonempty and $0<\operatorname{Re}\rho<1$. The Gaussian with this one angular character satisfies
$$
 \lim_{R\to\infty}R^{-1}\log\|P h_R\|_W=\lambda_\chi. \tag{1}
$$
In particular, bounding the distance of this field-independent *radial* packet to genuine theta lifts by $O_{\chi,\varepsilon}(e^{\varepsilon n})$ at the positive integers $R=n$, for every normalized character and every $\varepsilon>0$, would give the full central-zero statement. The functional equation accounts for the reflected zeros. Formula (1) provides both the lower bound from any single positive-order zero and the upper bound with full multiplicities and arbitrary clusters. It also gives an unconditional quantitative physical bound over rational $\zeta$ below. These are written deductions. The separate moving-window strong limit has a native Lean proof. [Positive-divisor infinitude](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch01_Introduction/Sec4.lean#L7129) · [Full open critical strip](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch01_Introduction/Sec4.lean#L7847) · [Native moving-window projection theorem](https://github.com/mccorvie/riemann-masullo/pull/7601)

## The exact quotient norm

Choose the normalized basepoint for each angular character. Chapter 10 identifies the theta closure with the common kernel of its bounded Mellin-jet functionals. At the full width all positive completed zeros are interior, so their full multiplicity is retained. For a physical representative $\chi^{-1}(g)f(x)$ with the exponential tails used below, the $k$th functional equals $V(\mathcal L f)^{(k)}(z_\rho)$ at $z_\rho=\rho-1/2$, with $V>0$ the fixed compact norm-one Haar volume and $\mathcal Lf(z)=\int_{\mathbb R}f(x)e^{zx}\,dx$. All other angular modes vanish by Haar orthogonality. The conventions are those of the project's bilinear moment integral, before the Hilbert dual is identified with the space by Riesz. Thus equal jets for two packets imply that their difference lies in the actual closure, yielding an upper bound by the norm of either representative of a quotient class. Each individual zeroth jet gives a lower bound for that same distance. [Jet convention](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L716) · [Full multiplicities in the interior](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L2086) · [Equality with the closed common kernel](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L6596)

The radial transform of $h_R$ is $F_R(z)=e^{Rz+z^2}$. For each zero, boundedness and annihilation of the theta space give
$$
 \|P h_R\|_W\geq V\,|e^{z_\rho^2}|\,e^{R\operatorname{Re}z_\rho}/\|\ell_\rho\|.
$$
This proves strict positivity for every $R$ and $\liminf\geq\lambda_\chi$. For the relative distance, dominated convergence after shifting $x=R+u$ gives $\|h_R\|_W\asymp e^{R/2}(1+R)^{3/2}$. In fact, the normalized squared norm tends to $V\int e^u|h(u)|^2du>0$ upon division by $e^R R^3$. The relative logarithmic rate in (1) is therefore $\lambda_\chi-1/2$.

## An interpolant which preserves all zero jets

Use the genus-one canonical product on the shifted full divisor with anchor $b=2$,
$$
 D_0(z)=\prod_\rho\left[\left(1-\frac{z-b}{z_\rho-b}\right)
                     \exp\left(\frac{z-b}{z_\rho-b}\right)\right]^{m_\rho},
 \qquad D(z)=e^{z^2/2}D_0(z).
$$
The project's canonical-product theorem proves that $D_0$ has exactly these zeros and orders. The multiplicity in any unit height band is $O_\chi(1+\log(2+|t|))$ by the project's Jensen rectangle estimate, applied with the finite Hecke companion, its vertical-strip polynomial growth, and its lower bound at $\operatorname{Re}s=2$. The cited Appendix B proof displays exactly these hypotheses for the completed divisor. The bounded-height remainder is finite by meromorphy. Summing the logarithmic unit-band estimate gives $M=\sum_\rho m_\rho|z_\rho-b|^{-3/2}<\infty$. [Canonical product and exact orders](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch01_Introduction/Sec4.lean#L10151) · [Jensen rectangle bound](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/ForMathlib/Analysis/Meromorphic/VerticalStripZeros.lean#L313) · [Verification of the Hecke hypotheses](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L9293)

Here are sufficient two-sided growth estimates. Write $T=2+|z-b|$. For $|z_\rho-b|>2T$, the absolute logarithm of the modulus of $E_1((z-b)/(z_\rho-b))$ is $O(T^2/|z_\rho-b|^2)$. Summed over the far sites this is $O(MT^{3/2})$. Among the near sites there are $O(MT^{3/2})$ with multiplicity, and the sum of $m_\rho T/|z_\rho-b|$ is $O(MT^{3/2})$. Since $\log|1-v|\le |v|$, these estimates give $\log^+|D_0(z)|=O(MT^{3/2})$ everywhere. If $z$ is distance at least $\delta\in(0,1]$ from every site, each near factor satisfies $|1-(z-b)/(z_\rho-b)|\ge\delta/(2T)$. Hence
$$
 \log^+|D_0(z)^{-1}|\ll M T^{3/2}(1+\log(2T/\delta)).
 \tag{2}
$$
In particular the logarithmic losses are $o(t^2)$ at vertical height $t$ on every uniformly separated vertical line, and on contours separated by an inverse power of $\log(3+|t|)$. The estimates allow arbitrarily close zero pairs.

Fix any $U>\lambda_\chi$ and $L<\min(-1,\lambda_\chi-1)$. Write $\Omega=\{L<\operatorname{Re}w<U\}$ and orient its two vertical lines with the interior on the left. Define
$$
 G_R(z)=\frac{1}{2\pi i}\int_{\partial\Omega}
             F_R(w)\frac{D(w)-D(z)}{(w-z)D(w)}\,dw . \tag{3}
$$
The singularity at $w=z$ is removable. On both lines $F_R(w)/D(w)$ decays as $\exp(-(\operatorname{Im}w)^2/2+o((\operatorname{Im}w)^2))$ times $e^{UR}$. Local normal convergence makes $G_R$ entire. By Cauchy's formula on rectangles, for $z\in\Omega$ the first term of the split numerator contributes $F_R(z)$. The other term is $D(z)$ times a holomorphic function locally about $z$. Thus (3) matches every required derivative of $F_R$. Outside the strip the first term vanishes. Fix $u_-<\min(-\beta,L)$ and $u_+>\max(\beta,U)$. On either outer line the separation between the lines gives
$$
 |G_R(u_\pm+it)|\le C_U e^{UR}|D(u_\pm+it)|
       \ll_U e^{UR} e^{-t^2/4}. \tag{4}
$$
For each fixed $R$, one also has Gaussian decay between the outer lines. To see this uniformly in the real coordinate, move $L$ or $U$ a small distance within its zero-free collar when the point lies near that boundary. The value of (3) is unchanged by deformation, since its apparent singularity at $w=z$ is removable and no zeros of $D(w)$ are crossed. The Cauchy formula now gives either $F_R(z)$ or zero plus an $O_R(|D(z)|)$ term with a uniformly separated denominator. The horizontal end segments vanish by (2) and its upper-modulus counterpart.

Invert $G_R$ on a vertical line using $(2\pi)^{-1}\int G_R(u+it)e^{-(u+it)x}dt$. All lines between the two outer ones give the same $g_R(x)$ by the preceding decay. For $x\ge0$ use $u_+$ and for $x<0$ use $u_-$. Equation (4) gives $|g_R(x)|\ll_U e^{UR}e^{-u_\pm x}$ on the respective half-lines. Consequently $\|\chi^{-1}g_R\|_W\ll_U e^{UR}$. Fourier inversion on an interior line recovers $\mathcal L g_R=G_R$ throughout the strip between the two outer lines. One can apply the $L^1$ inversion theorem since $G_R(u+i\cdot)$ is continuous and integrable there and its inverse times $e^{ux}$ is integrable by the two tail estimates. The Mellin-jet kernel now gives $\|P h_R\|_W\ll_U e^{UR}$. Sending $U$ down to $\lambda_\chi$ proves (1).

## An unconditional estimate for the rational principal character

The shape of the rational zeta zero-free region gives a physical rate at full width. For large $R$ there is $c>0$ such that
$$
 \|P h_R\|_W\ll
 \exp\left(\frac R2-
   \frac{cR}{(\log R)^{2/3}(\log\log R)^{1/3}}\right). \tag{5}
$$
This bound concerns the entire projected Gaussian vector. It saves more than every inverse power of $R$ even before normalizing by the full packet norm. Vinogradov–Korobov zero-freeness is used only for rational $\zeta$ in this estimate. A fixed positive exponential saving would require a fixed zero-free region by (1). [Mossinghoff, Trudgian and Yang, Theorem 1.1](https://arxiv.org/pdf/2212.06867#page=2)

For detail set $\eta(t)=[(\log(e^e+t^2))^{2/3}(\log\log(e^e+t^2))^{1/3}]^{-1}$. It is positive, even, smooth, decreasing on the positive axis and has bounded derivative. Its ratio at points distance at most one apart is bounded above and below by absolute positive constants. Centering the published zero-free region gives $\operatorname{Re}z_\rho\le1/2-c_0\eta(\operatorname{Im}\rho)$ at large height. A smaller positive $c_0$ works on the remaining compact interval by finiteness and strict inequality at the right edge. Choose $c_1>0$ less than half the product of $c_0$ and the lower unit-distance ratio. The contour $w(t)=1/2-c_1\eta(t)+it$ stays at distance $\gg\eta(t)$ from all sites. This follows by horizontal separation for sites within height one and vertical separation for the others.

Use this curve as the right boundary in (3), keeping the left side fixed below $-1$. Every zero is enclosed. The arclength element is $O(dt)$. Equations (2) and the Gaussian damping bound the $L^1$ mass of $F_R/D$ on this curve by
$$
 C e^{R/2}\int_{\mathbb R}e^{-c_1R\eta(t)-t^2/4}dt.
$$
For $|t|\le\sqrt R$ keep the factor $e^{-c_1R\eta(\sqrt R)}$ and integrate the Gaussian. On the complement its integral is $O(e^{-R/8})$. The left side contributes $O(e^{LR})$. This proves the improved version of (4) with the right side in (5) in place of $e^{UR}$. For the internal contour shifts used only for inversion, choose the two nearby graphs $1/2-c_j\eta(t)$ with $c_j$ slightly above and below $c_1$ inside the same zero-free corridor. At any $z$ of height $t$ one of these curves is separated by $\gg\eta(t)$: their horizontal separation at height $t$ has this size and their slopes are uniformly bounded. The extra denominator loss is polylogarithmic and is absorbed by the Gaussian. Deformation between the curves is legal at every height by the same divisor-distance bound. The common-kernel step is unchanged.

The missing estimate for centrality is $\|P h_n\|\ll_\varepsilon e^{\varepsilon n}$ for every $\varepsilon>0$ and every normalized character. Formula (5) supplies a quantitative unconditional saving at the full-width ambient boundary only. Turning an estimate on this particular packet into a signed trace estimate by operator-norm summation would require uniform control on a sufficiently rich family of packets.
