# The genuine theta projection at a moving physical window

Use Tamagawa Haar measure on the idèle classes $G$, a norm section, and log norm $x$. Write $L_r$ for ordinary left translation by a section element of logarithmic norm $r$. In the Hardy–Sobolev space of width $\beta\ge0$ and degree $s\ge0$ the squared density is $w(x)=e^{2\beta|x|}(1+x^2)^{s/2}$. Multiplication by $\sqrt w$ is a unitary $U$ from this weighted space to class-Haar $L^2$. Let $\Theta_a$ be the closed genuine theta space centered at $a$, $P$ its spectral orthogonal-complement projection, and $\widetilde P=UPU^{-1}$. For any field and center,
$$
 \mathrm{s}\!-\!\lim_{r\to+\infty} L_{-r}\widetilde P L_r
 =\mathrm{s}\!-\!\lim_{r\to-\infty} L_{-r}\widetilde P L_r=0. \tag{1}
$$
The limits for the genuine geometric projection are the identity, on the entire class-Haar Hilbert space. This is strong operator convergence for each fixed packet. A nonzero projection has operator norm one throughout. [Theta subspace and genuine representatives](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L624) · [Haar-density input at degree zero](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L7887)

Indeed write $h_f(g)=e^{ax}\theta_f(g)$ for a genuine polar-free source $f$. The theta subspace is translation invariant. Thus $L_{-r}\widetilde P L_r$ annihilates the actual vector $\sqrt{w(r+x)/w(r)}\,h_f(g)$, which is the normalized, recentered image of $L_r h_f$. The weight ratio under the square root converges to $e^{2\beta x}$ at the positive end and $e^{-2\beta x}$ at the negative end. Its uniform majorant $2^{s/2}w(x)$ follows from $1+(r+x)^2\le2(1+r^2)(1+x^2)$ and the triangle inequality. The project proves integrability of $w|h_f|^2$, so dominated convergence gives $L^2$ convergence to $e^{(a\pm\beta)x}\theta_f(g)$. At each end these limiting genuine functions span a dense subspace: they are exactly the theta generators at center $a\pm\beta$ and Sobolev degree and width zero, where the project proves the closed theta space is the whole Hilbert space. The norm-one contraction bound extends the result to every packet. The argument does not require a zero-free strip or a choice of Fourier bandwidth. [Translation invariance and the quotient action](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L1755) · [Actual weighted energy](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L1435)

## The endpoint at the ambient threshold

Take a single normalized angular character and a fixed smooth compact $H$ supported above norm one in logarithmic coordinates. For $\varphi_y(g)=\psi(g)H(x-y)$, write $A_y$ for convolution and $T_y=M_{\rho_y}A_y$ for the output-localized convolution. The cutoff function is bounded by one and has log radius $R(y)=\log\Lambda_y$. At $s=3$ and any $\alpha=\beta>0$, for every fixed real $C$ one may take
$$
 R(y)\le y-\frac{1}{2\alpha}\log y
            +\frac{3}{4\alpha}\log\log y+C.
$$
Then the weighted absolute Cesàro mean of $\operatorname{Tr}(T_y P)$ tends to zero. The geometric projection gives its negative, since the unprojected localized convolution has zero trace on these translated profiles. This concerns the full genuine projections. The ambient fixed projections displayed in the previous note have a nonzero limit at this exact scale. [Unit-cell estimates and counterexample](https://github.com/mlyle/riemann-masullo/blob/66d5980b94710c88464a3de4e425f65d6c2923d4/research/endpoint-physical-trace-window.md)

To verify the strict saving, use the unit-cell proof of estimate (1) in the linked note. Its input vector $\xi_{l,n}$, pulled back by the translation $L_{-l}$, is a fixed cell exponential times $\sqrt{w(l)/w(l+u)}$ on $0\le u<1$, with fixed normalization. It converges in $L^2$ as $l\to-\infty$, by the explicit density. Equation (1) here gives $\|\widetilde P \xi_{l,n}\|\to0$ for every fixed $n$. For the nonnegative output cells the input satisfies $l\le-\inf_{[Y,2Y]}(y-R(y))+O_H(1)$, which tends to $-\infty$. The Bessel bound for these cells now gains the factor
$$
 \sum_n(1+|n|)^{-2}
   \sup_{l\le-\inf(y-R(y))+O_H(1)}\|\widetilde P\xi_{l,n}\|=o(1).
$$
At the stated radius the power, exponential and logarithmic factors in the earlier fixed-projection bound have bounded product. The negative cells are exponentially small. Dyadic summation gives the claimed Cesàro limit on $(0,Y]$, with the usual local measurability and integrability. This remains true at widths whose boundaries contain completed zeros. No rate of strong convergence is assumed.

## Only a positive outer half-line enters the remaining comparison

Here use the nuclearity of the actual $C_\beta=A_0P_\beta$ from Penner’s theorem, for the fixed test with $H(0)=0$. By the norm section and the normalization of $\psi$, $A_y=L_y A_0$ in the weighted space. The same estimates in norm allow a unit scalar for a different character extension. For any strip width $\beta>0$,
$$
 \|1_{\{x\le0\}}A_yP_\beta\|_1\le e^{-\beta y}\|C_\beta\|_1 .
$$
Indeed the conjugated translation has factor $\sqrt{w_\beta(x)/w_\beta(x-y)}$, bounded by $e^{-\beta y}$ on all $x\le0$ for $y\ge0$. This removes the entire negative half-line, however far the physical cutoff extends. [Genuine nuclear product and physical-stage trace](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L212)

More generally fix $0<\alpha<\beta$, $c=(\alpha+\beta)/(2\beta)$, and any real $C$. One has the pointwise trace-norm estimate
$$
 e^{-\alpha y}\|1_{\{x\le cy+C\}}A_yP_\beta\|_1\longrightarrow0. \tag{2}
$$
Throughout $0\le x\le cy+C$, the exponential ratio after division by $e^{\alpha y}$ is bounded by $e^{2\beta C}$, and the polynomial ratio is bounded because $1-c>0$. The negative side has the preceding bound. All participating input coordinates obey $t=x-y\le-(1-c)y+C$. The corresponding input multipliers converge strongly to zero and are contractions, so their products with the fixed nuclear $C_\beta$ converge to zero in nuclear norm by finite-rank approximation. This proves (2). For a narrower strip of width $\alpha$ at this same cutoff there is a strict exponential saving, since $c<1$.

At the actual full width $\beta=1/2$, the wide quotient trace of a polar-free test equals its signed nonpolar adelic local terms. The narrow and wide quotient traces can be computed on the weighted ambient Hilbert spaces from $A_yP$ by projection cyclicity. Consequently, for any fixed $0<\alpha<1/2$, the narrow trace minus the signed local terms differs by $o(e^{\alpha y})$ from
$$
 \operatorname{Tr}\!\left(1_{\{x>(1/2+\alpha)y+C\}}A_yP_\alpha\right)
 -\operatorname{Tr}\!\left(1_{\{x>(1/2+\alpha)y+C\}}A_yP_{1/2}\right).
$$
The two positive exterior traces use their respective width and the same Haar and log normalizations. Controlling their signed difference in the absolute weighted Cesàro mean is the remaining arithmetic-geometric step. Sharp half-line multipliers here only split a nuclear operator; no smooth-cutoff identity for a discontinuous symbol is required. [Exact wide trace and local terms](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch12_TraceGeometric/Sec5.lean#L1558) · [Endpoint criterion](https://github.com/mccorvie/riemann-masullo/pull/7586)

These are written deductions from the cited project results and the indicated Hilbert-space estimates.
