# Common central modes in the finite width difference

Fix the rational principal character, center $a=1/2$, positive widths $0<\alpha<\beta$ and common degree $s\ge0$. Use the norm section, log norm $x$, normalized probability on the norm-one compact group and its Tamagawa volume $V$. Thus the radial Hilbert norm squared is $V\int |f(x)|^2w_\eta(x)\,dx$, where $w_\eta=e^{2\eta|x|}(1+x^2)^{s/2}$. Let $I$ restrict physical representatives from the wide to the narrow space, and write $P_\beta$ for the genuine wide spectral projector and $G_\alpha$ for the genuine narrow geometric projector. At a central ordinate $\gamma$ the full-width Riesz representative of the bilinear jet $V\int f(x)e^{i\gamma x}\,dx$ is $r_{\beta,\gamma}(x)=e^{-i\gamma x}/w_\beta(x)$. Every central zero lies strictly in both strips, so the zeroth jet exists at both widths and $P_\beta r_{\beta,\gamma}=r_{\beta,\gamma}$. [Actual project jet](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L713)

## Infinite rank already on common zeros

Set $\delta=2(\beta-\alpha)>0$. For narrow theta vectors the radial pairing with $I r_{\beta,\gamma}$ is $V\int e^{-\delta|x|} f(x)e^{i\gamma x}\,dx$. In a finite linear relation between $G_\alpha I r_{\beta,\gamma_j}$ at distinct ordinates, this vanishes on every actual centered polar-free theta source. The corresponding Haar representative $e^{-\delta|x|}\sum_j c_j e^{-i\gamma_jx}$ belongs to ordinary class-Haar $L^2$. The very same physical theta sources are dense in that Haar space by the width-zero degree-zero theorem. Thus the exponential polynomial vanishes almost everywhere, hence everywhere by continuity; the Vandermonde system of its derivatives at zero gives $c_j=0$. There are infinitely many distinct central rational zeros unconditionally. In particular $G_\alpha I P_\beta$ has infinite rank even on the linear span of the modes known to be common to both widths. [Native density theorem](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L7887) · [Conrey, introduction and Theorem 1](https://aimath.org/~kaur/publications/24.pdf)

## A single geometric vector detects every sufficiently high common mode

There is a fixed radial $f\in\Theta_\alpha$ with $f(0)\ne0$ and $f,f',f''\in L^2(dx)$. Indeed a centered polar-free theta source with nonzero radial component exists by the same Haar density. Project it onto the trivial norm-one character using the normalized compact-group average. The closed narrow theta space is invariant under translations, so this average stays in it. Convolve in the real log coordinate with a smooth compact approximate identity. At least one of these convolutions is nonzero, since approximate identities converge in unweighted $L^2$. Every derivative up to order two is in $L^2$ by Young's inequality applied to the compact smoothing kernel and the unweighted radial source. The smooth radial function and its translates remain in the narrow theta space, by integrating translations over compact supports. Translate a nonzero value to zero. This construction needs neither zero ordinates nor RH. [Genuine theta translation invariance](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L1816)

For $k(x)=e^{-\delta|x|}f(x)$ the distributional second derivative is
$$
 k''=e^{-\delta|x|}\{f''-2\delta\operatorname {sgn}(x)f'+\delta^2f\}
       -2\delta f(0)\,\delta_0 .
$$
The ordinary density on the right lies in $L^1$ by Cauchy–Schwarz. The Riemann–Lebesgue lemma for that density and $\widehat{k''}(\gamma)=-\gamma^2\widehat k(\gamma)$, in the positive-exponent Fourier convention as well, give the explicit limit
$$
 \lim_{|\gamma|\to\infty}\gamma^2 V\int e^{-\delta|x|} f(x)e^{i\gamma x}\,dx
   =2\delta V f(0).
$$
For large central ordinates the magnitude of this scalar is at least $\delta V |f(0)|/\gamma^2$. Hence $\|G_\alpha I P_\beta r_{\beta,\gamma}\|_\alpha\ge c/(1+\gamma^2)$ at every central ordinate, for some $c>0$ depending on the two widths and the fixed degree. For the finitely many bounded ordinates use the preceding strictly positive individual norms. The wide Riesz norm is a fixed positive constant independent of $\gamma$, so the same lower order holds for unit-normalized inputs. This is a lower bound on the first geometric factor, before applying the mixed masked convolution. It does not give a signed lower bound on the composed trace. Common central modes cancel in the fully exhausted width-subtracted spectral sum. At a finite physical cutoff they cannot be discarded by asserting that this intermediate geometric projection kills them one at a time. [Exact finite-stage signed factorization](https://github.com/mlyle/riemann-masullo/blob/e27d9d34d86b1aea62bc4fff253c02707c912e8c/research/width-restriction-signed-defect.md#finite-physical-cutoffs-admit-an-exact-bounded-cross-width-factorization)

## The complete divisor on a fixed test

Take $\beta=1/2$. The fixed smoothed source just constructed can be chosen with $|f^{(j)}(x)|\le C_{A,j}e^{-A|x|}$ for every $A>0$ and integer $j\ge0$. The radial average of one genuine source belongs to every exponentially weighted $L^2$ by its genuine theta estimates at every width. Compactly supported smoothing and Cauchy–Schwarz on the translated support of each derivative of the smoothing kernel give the stated pointwise bounds. Fixed translation preserves them. Write $z=b+i\gamma=\rho-1/2$ and $r_{\beta,z}(x)=e^{\bar z x}/w_\beta(x)$. In the following scalar pairing the narrow geometric input is the first argument of the bilinear jet, so the integral has $e^{zx}$. As $|b|\le\beta$, the previous distributional computation applies to $f_b(x)=e^{bx}f(x)$. Its second-derivative density on the two open half-lines varies continuously in $L^1$ as $b$ ranges over a compact interval. A finite net and Riemann–Lebesgue therefore give, uniformly in $b$,
$$
 \gamma^2 V\int e^{-\delta|x|} f(x)e^{(b+i\gamma)x}\,dx
      \ \longrightarrow\ 2\delta V f(0).
$$
At full width, this pairing tests the actual mixed projector at every rational completed zero. Summing the magnitudes over the **entire** divisor, with multiplicities $m_\rho$, is absolutely convergent. Its tail over $|\gamma|>T$ is asymptotic to $(2\delta V|f(0)|/\pi)\log(T)/T$. Indeed $N_+(T)\sim T\log T/(2\pi)$ counts positive ordinates with multiplicity. Partial summation gives $-N_+(T)T^{-2}+2\int_T^\infty N_+(u)u^{-3}du\sim\log(T)/(2\pi T)$, and conjugation doubles this. [Hasanalizade, Shen and Wong, Theorem 1.1](https://arxiv.org/abs/2107.06506) · [Actual integrability for genuine sources](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L1435)

## Strict saving on translated genuine geometric test vectors

Let $f_y(x)=f(x-y)$ for $y\ge0$, and write $\mathcal L f(w)=\int f(u)e^{wu}du$. Every $f_y$ remains in the narrow theta subspace. The scalar pairing of $f_y$ with $G_\alpha I P_\beta r_{\beta,z}$ is
$$
 V\int e^{-\delta |x|} f(x-y)e^{z x}dx
 = V e^{(z-\delta)y}\mathcal L f(z-\delta)
       +O_{A,f}\left(\frac{e^{-Ay}}{1+\gamma^2}\right) . \tag{1}
$$
This holds uniformly for all $|b|\le\beta$, $y\ge0$, and any fixed $A>0$. On $x\ge0$ the absolute-value factor is exactly $e^{-\delta x}$. Extend that exponential across the whole line and substitute $x=y+u$ to obtain the explicit leading term. The remaining Fourier transform has density
$$
 \mathbf1_{x<0}\,(e^{\delta x}-e^{-\delta x})e^{bx} f(x-y).
$$
It vanishes at zero. On its support $|x-y|=y+|x|$. Take the preceding pointwise derivative bounds with rate greater than $A+\beta+\delta+1$. The density, its ordinary second derivative on the negative half-line, and the magnitude $2\delta |f(-y)|$ of the derivative jump at zero have $L^1$ or scalar bounds $\ll e^{-Ay}$, uniformly in $b$. The integral bound at low frequencies and two integrations by parts at high frequencies prove (1).

In particular, for **every fixed** $0<\alpha<\beta=1/2$,
$$
 \sum_\rho m_\rho
   \left|V\int e^{-\delta |x|}f_y(x)e^{(\rho-1/2)x}dx\right|
 \ \ll_f\ e^{(\beta-\delta)y}=e^{(2\alpha-\beta)y}.
$$
All constants may depend on the two fixed widths. Uniform integration by parts in the defining transform bounds $|\mathcal L f(b-\delta+i\gamma)|\ll_f(1+\gamma^2)^{-1}$ on the whole compact real strip. The multiplicity sum of this majorant is finite by the cited zero count. Choose $A>|\beta-\delta|+1$ for the error in (1). Consequently the absolute sum is $O(e^{-(\beta-\alpha)y})$ after division by the thin scale $e^{\alpha y}$. It can even decay before normalization when $\alpha<\beta/2$. This is a physical estimate on the genuine translated narrow geometric input with every full-width zeroth evaluation and its actual multiplicity. The unresolved mixed **trace** also involves the whole nuclear convolution and its Hilbert-space dual vectors; transferring this estimate to that trace needs quantitative control of those vectors or a separate trace argument.
