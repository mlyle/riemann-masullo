# The critical-line Sobolev limit and finite theta projections

The idèle-class measure in #7580 is Tamagawa Haar measure $\mu$. At half-width zero and Sobolev order $s=2k+3$ the Hilbert-space density relative to $\mu$ is $w_k(g)=(1+x^2)^{k+3/2}$, where $x=\log|g|$. The geometric kernel smooths the raw convolution kernel minus the Haar kernel of $P_k A_\varphi$, where $P_k$ is the spectral projection. The raw term vanishes on the smoothed diagonal for an admissible probe. The signed local scalar is $-\mathrm{PV}_\chi$, where $\mathrm{PV}_\chi$ already includes the norm-one volume and the finite-place factors. Thus

$$
 I_k=-\Re\operatorname{Tr}(P_k A_\varphi),\qquad
 \mathrm{PV}_\chi=-\sum_\rho m_\rho v_\rho,\qquad
 v_\rho=\Re M(\varphi,\chi,\rho)>0 .
$$

The desired inequality is $\lim_k I_k\le\mathrm{PV}_\chi$. [Definition and central expansion](https://github.com/willzh0/riemann-masullo/blob/cf0d54873308e0633e2ecceae4e2991cbdddbc96/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L1185) · [Local normalization and equivalence](https://github.com/willzh0/riemann-masullo/blob/cf0d54873308e0633e2ecceae4e2991cbdddbc96/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L1466)

## Fixed-degree physical comparison

For each fixed $k$, Penner’s genuine Fourier-stage trace theorem applies at half-width zero. Take the bandwidth limit at a fixed admissible physical cutoff, then exhaust the physical cutoff. The resulting scalar is $-\Re\operatorname{Tr}(A_\varphi P_k)$. The two constructions establish nuclearity of the respective projected products. Since $P_k^2=P_k$, cyclicity with a nuclear factor gives

$$
 \operatorname{Tr}(A_\varphi P_k)
 =\operatorname{Tr}((A_\varphi P_k)P_k)
 =\operatorname{Tr}(P_k A_\varphi P_k)
 =\operatorname{Tr}(P_k A_\varphi).
$$

This identifies the exhausted scalar with $I_k$. The kernels may differ before exhaustion. The argument uses no positive-width representing tensor. [Penner’s nested limits and nuclearity](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L212) · [Output-projected trace and Haar diagonal](https://github.com/willzh0/riemann-masullo/blob/cf0d54873308e0633e2ecceae4e2991cbdddbc96/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L742)

At fixed cutoff and degree one can also take the directed limit over finite spans of actual polar-free theta generators. Their orthogonal projections converge strongly to the geometric projection by density. The localized convolution $M_\rho A_\varphi$ is nuclear, so its traces against those projections converge. This finite-span limit can also be taken within each Fourier stage before exhausting bandwidth.

## Genuine theta vectors have unbounded logarithmic support

Fix a normalized unitary character over any number field. Let $u$ be a nonzero centered angular theta lift of a genuine polar-free source. If it had support in $[-L,L]$, the transform

$$
 F(s)=\int_{\mathbb R}u(x)e^{(s-1/2)x}\,dx
$$

would be entire and satisfy $|F(s)|\le\|u\|_1 e^{L|s-1/2|}$. Fourier uniqueness supplies a center $c$ on the line $\Re s=1/2$ with $F(c)\ne0$. Jensen’s bound on concentric discs of radii $r,2r$ about $c$ gives $O_{c,u,L}(1+r)$ zeros counted with multiplicity in the smaller disc.

The project identifies $F$ with the global theta Mellin transform. Its zero order dominates the **full** positive completed Hecke divisor at every site. Each interval $[17j-8,17j+8]$ contains more than $a\log(17j)$ units of that divisor for all sufficiently large $j$ and any fixed $0<a<[F:\mathbb Q]/4$. These intervals are disjoint. Taking $n\le j\le 2n$ gives $\gg n\log n$ zeros in a disc of radius $O_c(n)$, contradicting Jensen’s bound. For a nonzero full theta vector, restriction to each norm fibre and Fourier uniqueness on the compact norm-one group give a nonzero angular component. Bounded logarithmic support would pass to that component. Linearity of the theta map gives the assertion on every algebraic span of genuine polar-free sources. [Centered Mellin normalization](https://github.com/mlyle/riemann-masullo/blob/f91267e5b23bd0fc38beecfbad0d1277e4c1dd8e/RiemannMasullo/Ch12_TraceGeometric/ThetaLiftCost.lean#L164) · [Full Mellin divisibility](https://github.com/mlyle/riemann-masullo/blob/f91267e5b23bd0fc38beecfbad0d1277e4c1dd8e/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L2883) · [All-field radius-eight lower bound](https://github.com/mlyle/riemann-masullo/blob/f91267e5b23bd0fc38beecfbad0d1277e4c1dd8e/RiemannMasullo/Ch01_Introduction/Sec4.lean#L13283)

## A trace-norm bound for the whole finite stage

Let $E$ be a fixed nonzero $d$-dimensional algebraic span of genuine centered theta vectors. Embed its representatives in every critical-line Sobolev space, with $P_{E,k}$ the corresponding orthogonal projection. Write $\|\cdot\|_0$ for the unweighted $L^2(\mu)$ norm. Suppose $\rho=0$ for $|x|>R$. For a project cutoff of module radius $\Lambda$ take $R=\log\Lambda$, with $\|\rho\|_\infty\le1$. Introduce

$$
 \lambda(E,B)=\min_{\substack{u\in E\\\|u\|_0=1}}
                 \int_{|x|>B}|u|^2\,d\mu,\qquad B>R.
$$

Restriction to this tail is injective by noncompactness of the continuous representatives and full support of Haar measure. Its squared norm is continuous on the compact Haar-unit sphere of $E$, so $\lambda(E,B)>0$.

For $T=M_\rho A_\varphi$ one then has

$$
 \|P_{E,k}T P_{E,k}\|_1
 \le d\,\|\rho\|_\infty\|\varphi\|_{L^1(\mu)}\lambda(E,B)^{-1}
 \left(\frac{1+R^2}{1+B^2}\right)^{k+3/2}.
$$

For $u,v\in E$ the unweighted Haar convolution inequality and Cauchy–Schwarz give

$$
 |\langle Tu,v\rangle_k|\le
 \|\rho\|_\infty (1+R^2)^{k+3/2}\|\varphi\|_{L^1(\mu)}\|u\|_0\|v\|_0 .
$$

Each squared weighted norm dominates $(1+B^2)^{k+3/2}\lambda(E,B)\|u\|_0^2$. Division gives the compressed operator norm bound. Its rank is at most $d$. All norms here are for the indicated Haar or weighted measure. [Actual physical cutoff support](https://github.com/mlyle/riemann-masullo/blob/f91267e5b23bd0fc38beecfbad0d1277e4c1dd8e/RiemannMasullo/Ch09_HardySobolev/Sec3.lean#L2912)

For fixed $E,R$ the trace norm is $O_{E,R,q}(q^k)$ for **every** $0<q<1$, by taking $B$ arbitrarily large. For moving stages $E_k,R_k$, put $B_k=\sqrt{1+2R_k^2}$. If their signed traces stay at distance at least $\eta>0$ from zero, then

$$
 \lambda(E_k,B_k)\le \eta^{-1}d_k\|\rho_k\|_\infty\|\varphi\|_1\,2^{-k-3/2}.
$$

In particular, at subexponential rank, each sufficiently large approximating stage must contain a Haar-unit vector with exponentially small squared tail.

## Order of limits

The rational principal probe has positive central mass, since at least one certified zeta zero is central and the probe has strictly positive real Mellin value there. Hence $\lim_k I_k<0$. On every fixed finite theta span and fixed physical cutoff the high-degree-first trace is zero. For any sequence of finite stages and cutoff radii $(E_n,R_n)$, choose $k_n$ strictly increasing and sufficiently large at each $n$ so these traces tend to zero. For every individual stage, its absolute large-degree error against $I_k$ tends to the entire positive central mass. In particular an estimate for approximating $I_k$ by finite physical stages cannot hold with arbitrarily small error uniformly in $k$, even along an exhaustion dense at each fixed degree.

The same strict limit discrepancy holds in any character with a known central zero. For every character the divisor is nonempty, so $\mathrm{PV}_\chi<0$ on its detecting probe. The zero obtained by taking degree first cannot meet the required local upper bound. Fixed bandwidth can have infinite rank. Its pre-exhaustion degree limit, and the signed bound after exhausting the complete spaces, remain open. The finite-stage estimate above is a written deduction from the linked Lean and classical inputs. [Exact high-degree limit](https://github.com/willzh0/riemann-masullo/blob/cf0d54873308e0633e2ecceae4e2991cbdddbc96/RiemannMasullo/Ch12_TraceGeometric/Sec5_Isolated.lean#L1206) · [Platt and Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765) · [Earlier obstruction for the separate strip-width parameter](https://github.com/mccorvie/riemann-masullo/pull/7574)
