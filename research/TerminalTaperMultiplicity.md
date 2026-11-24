# A multiple Dedekind zeta zero forces divergence for a specific moving Möbius taper

For the principal character of $F=\mathbb Q(\sqrt[3]{2},\zeta_3)$, the squared physical error of the moving taper below grows at least as fast as $\sqrt{\log X/\log\log X}$. This holds for every sufficiently large cutoff. It rules out using this particular family to obtain the all-fields density needed along one approach to Theorem 12.5.1.1, pp. 519–520. A separate conclusion for $F=\mathbb Q$ improves the lower rate while leaving convergence open. [Gap issue](https://github.com/mccorvie/riemann-masullo/issues/5571) · [Earlier rational normalization and physical estimates](./PrincipalThetaCofactorPairing.md#absolute-bounds-for-the-combined-signed-remainder)

## The family and its physical norm

Write $L=\log X$, $q=\log L$, $R=\sqrt{L/q}$, $S=L/(2q)$ and $Z=\log(S/(2R))$. Let $B$ be the increasing smooth step equal to $b(x)/(b(x)+b(1-x))$ on $(0,1)$, where $b(x)=e^{-1/x}$ for $x>0$ and zero otherwise. Extend it by zero to the left and one to the right. Normalize $w$ to one before $L-S$ and zero after $L-R$ with slope
$$\psi(t)=-w'(t)=\frac{B((L-t)/R-1)[1-B(2(L-t)/S-1)]}{Z(L-t)}$$
between those two endpoints. The two transition integrals at the opposite ends of the log scale give $\int\psi=1$. The finite inverse is $P_X(s)=\sum_{\mathfrak a}\mu_F(\mathfrak a)w(\log N\mathfrak a)(N\mathfrak a)^{-s}$.

Use the compact radial detector with Mellin transform
$$K(s)=(s-1)e^{-\pi^2s/384}\prod_{j\ge1}\frac{\sinh(s/(64j^2))}{s/(64j^2)}.$$
Its zeros do not meet the open critical strip. The normalized factors have zeros on the imaginary axis and their product converges absolutely and locally uniformly away from individual zeros. To realize the same transform at all archimedean places, partition the box factors by congruence classes of $j$ among the places. Each subsequence gives a compact Gevrey radial log density. Apply the radial derivative $-r\,d/dr-1$ at one place. This supplies the factor $s-1$ and kills the additive polar integral. Integer indicators at finite places give the ideal theta source $A_F(r)=\sum_{\mathfrak a} h(N\mathfrak a\,r)$ in the principal chart, with the common normalization of the detector $h$. [Source construction](https://github.com/mccorvie/riemann-masullo/pull/7437)

The original error is $E_X(y)=\sum_{\mathfrak a}\mu_F(\mathfrak a)w(\log N\mathfrak a)A_F(N\mathfrak a/y)-h(1/y)$. Its physical norm is measured with $dy/y^2$. Writing $f_X(x)=e^{-x/2}E_X(e^x)$, its Fourier transform at $\gamma$ is
$$K(s)[\zeta_F(s)P_X(s)-1],\qquad s=1/2+i\gamma.$$
This follows by Mellin transformation first to the right of one, followed by analytic continuation. With $d=[F:\mathbb Q]$, it suffices to retain the physical interval
$$J_{X,d}=[Xe^{-S+1/(4q)},Xe^{-R}L^{2d+1}].$$
The error vanishes below $Xe^{-S}$. On the remaining left edge only the full divisor can be off the plateau. Its coefficient is $O(1/X)$ by the flat step endpoint, and the ideal count through $y$ is $O_F(y)$. On the right edge the source arguments are at most $L^{-(2d+1)}$. The Gevrey Poisson bound $|A_F(r)|\ll_F r^{-1}e^{-c r^{-1/(2d)}}$ gives a tail smaller than every power of $X^{-1}$, with integrable decay through infinity. The left edge has norm $O_F(X^{-1/2})$. [Edge argument and Mellin identity](./PrincipalThetaCofactorPairing.md#absolute-bounds-for-the-combined-signed-remainder)

## Reducing the field assertion to one zero

If $\zeta_F$ has a zero $\rho$ with $\beta=\Re\rho-1/2>0$, the full Mellin moment equals $-K(\rho)\ne0$. On $x\ge L-S$ the $L^2(dx)$ norm of the weight $e^{-\beta x}$ is $e^{-\beta(L-S)}/\sqrt{2\beta}$. Cauchy–Schwarz and the negligible physical edges give exponential growth of the norm on $J_{X,d}$. The functional equation and conjugation cover zeros on the left as well.

It remains to consider the alternative that every nontrivial zero of this fixed field is on the critical line. In the stated nonabelian Galois field there are unconditionally multiple nontrivial zeros. Fix one of order $m\ge2$ at $\rho=1/2+i\gamma$. The following argument also applies with $m=1$. [Hu–Kaneko–Martin–Schildkraut, Theorem 1.1](https://arxiv.org/pdf/2107.03269#page=2) · [Lean result for this splitting field](https://github.com/mccorvie/riemann-masullo/pull/7483)

## The contour near the chosen zero

Set $H_X(z)=\int\psi(t)e^{zt}dt$ and $W_X(z)=H_X(z)/z$. For $\Re s=1/2$, smooth Perron inversion on $\Re z=1$ gives
$$P_X(s)=\frac{1}{2\pi i}\int_{(1)}\frac{W_X(z)}{\zeta_F(s+z)}\,dz.$$
The reciprocal series on this first line is absolutely convergent. Scalar inversion against the smooth density $\psi$ recovers each original weight $w$.

Two estimates justify a local contour shift. First, in the fixed-field critical-line alternative, uniformly for $1/2+1/L\le\sigma\le2$,
$$|1/\zeta_F(\sigma+it)|\le \exp(C_F\log(3+|t|)(1+\log L)).$$
Subtract the Hadamard logarithmic derivatives at $\sigma+it$ and $2+it$. The distant zeros, grouped by unit bands with all multiplicities, cost $O_F(\log(3+|t|))$ because the summands have inverse-square decay. The gamma factors and reference derivative satisfy the same bound for $|t|\ge3$. Horizontal integration of the remaining nearby zero terms costs at most $\log(CL)$ per zero. There are $O_F(\log(3+|t|))$ per unit band. For bounded heights factor the finitely many zeros in a compact neighborhood; the pole at one is a zero of the reciprocal. [Hadamard product](https://arxiv.org/pdf/1201.3932#page=12) · [Dedekind zero count with remainder](https://arxiv.org/pdf/2102.04663#page=1)

Second, integration by parts gives
$$|H_X(z)|\le C R\exp\!\big(\max\{(L-S)\Re z,(L-R)\Re z\}-c\sqrt{R|z|}\big).$$
In fact $\|\psi^{(k)}\|_1\le C(S/R) C_1^k(k!)^2R^{-k}$. Cauchy's derivative estimate on a disk of radius $u/2$ for $e^{-1/u}$ gives the order-two Gevrey bound. It is preserved by the smooth step's denominator, which is bounded below, by multiplication, and by the two rescalings. On the support $L-t\ge R$. Integrate by parts $k$ times and take $k$ a sufficiently small multiple of $\sqrt{R|z|}$. In particular on $\Re z=1/L$, outside $|\Im z|<\delta$ with fixed $\delta>0$, this decay beats the preceding reciprocal estimate on the entire infinite contour, since $\log L=o(\sqrt R)$. The tail integral is $O_{F,\delta,N}(L^{-N})$ for every fixed $N$.

Fix $v\ne0$, put $s=\rho+iv/R$ and $z_0=-iv/R$. Choose $\delta$ so that $\rho$ is the only zero or pole in its closed $4\delta$ neighborhood. Move the original contour to $1/L$, then move the segment with $|\Im z|\le\delta$ to $-1/R$. The short horizontals have superpolynomial decay and stay away from the chosen zero; on the new local vertical the reciprocal is $O_\rho(R^m)$ while the transform is exponentially small in $(L-S)/R$. The only poles crossed are $0,z_0$. Writing $c_{-k}$ for the Laurent coefficients of the reciprocal at $\rho$ gives
$$P_X(s)=\zeta_F(s)^{-1}+\sum_{k=1}^m\frac{c_{-k}}{(k-1)!}W_X^{(k-1)}(z_0)+O_{\rho,v,N}(L^{-N}).$$

For $x\ge1$ write $g(x)=B(x-1)/x$, extended by zero below one, and $\Phi(v)=\int_1^\infty g(x)e^{ivx}dx$ for $v\ne0$. Substitution $x=(L-t)/R$ in $H_X^{(j)}$ shows
$$Ze^{ivL/R}H_X^{(j)}(z_0)/L^j\longrightarrow\Phi(v).$$
The remote cutoff costs $O_v(R/S)$ by integration by parts. The factor $(1-Rx/L)^j$ costs $O_j(S/L)$ on the remaining support. Differentiations falling on $1/z$ in $W_X$ lose a factor $O_v(R/L)$ each. The highest Laurent term therefore gives the pointwise limit
$$Z(R/L)^{m-1}e^{ivL/R} K(s)[\zeta_F(s)P_X(s)-1]
\longrightarrow -\frac{K(\rho)(iv)^{m-1}}{(m-1)!}\Phi(v).$$

## Consequences in the original measure

Apply Fourier Plancherel in $x$ and keep frequencies $\gamma+v/R$ for $v$ in any fixed compact set excluding zero. Fatou's lemma, then exhaustion of the line, gives
$$\liminf_{X\to\infty} RZ^2(R/L)^{2m-2}\|E_X\|^2_{J_{X,d}}
\ \ge\ \frac{|K(\rho)|^2}{((m-1)!)^2}\,\|g^{(m-1)}\|_2^2
\ \ge\ \frac{|K(\rho)|^2}{(2m-1)2^{2m-1}}.$$
Here $g$ is smooth and $g(x)=1/x$ on $[2,\infty)$, where the derivative norm in the last inequality can be integrated explicitly. For a double zero the constant is $|K(\rho)|^2/24$. Since $L=R^2q$ and $2Z\le q$, for $m\ge2$ the resulting squared norm is $\gg_\rho L^2/(R^3Z^2)\gg R$. Together with the off-line case this proves unconditional divergence for the splitting field above.

Over $\mathbb Q$, summing over the disjoint shrinking neighborhoods of 1,024 distinct certified simple zeros gives $\liminf RZ^2\|E_X\|^2_{J_{X,1}}>333809$ in the critical-line alternative. The calculation uses $\sum|K(\rho)|^2>667619.59$ and $\int_2^\infty x^{-2}dx=1/2$. An off-line rational zero gives the stronger exponential bound. The previously established $O_h(X^{-.03})$ norm cost of matching and the superlogarithmically small cost of any polylogarithmic-degree graph preserve the rational lower bound for the combined sparse remainder. Its unscaled lower rate still tends to zero. [Certified rational detector calculation](./PrincipalThetaCofactorPairing.md#absolute-bounds-for-the-combined-signed-remainder) · [FLINT zero isolation and counting](https://flintlib.org/doc/acb_dirichlet/zeta-zeros.html)
