# The best cutoff in each short interval detects the rightmost zeta zero

For Theorem 12.5.1.1, pp. 519–520, let $w(u)=2-\cos u-\cos(\sqrt2\,u)$ and let
$$E(x)=\sum_{p\le x}(\log p)w(\log p)-\int_1^x w(\log t)\,dt.$$
Write $\Theta=\sup_\rho\Re\rho$ for the supremum over nontrivial ordinary zeta zeros. Fix $0<\alpha<1$ and a sign $s\in\{+1,-1\}$. For an integer $X\ge2$ define
$$B_{s,\alpha}(X)=\min_{n\in\mathbb Z,\,X\le n\le X+X^{1-\alpha}}\max(sE(n),0).$$

Then the exact classical exponent is
$$
\Theta=\max\!\left(\tfrac12,\ \limsup_{X\to\infty}
\frac{\log(1+B_{s,\alpha}(X))}{\log X}\right).
$$
In particular if $\Theta>1/2$, then for **each sign** and each $1/2<t<\Theta$ there are arbitrarily late intervals $[X,X+X^{1-\alpha}]$ throughout which $sE(n)>X^t$. This permits $\Theta=1$ and does not require a zero realizing the supremum. At $\Theta=1/2$ the maximum with $1/2$ is essential to the statement of what the argument proves.

## The one-sided full-cutoff inference

Fix $1/2<r<1$. A bound $sE(N)\le N^r$ for all sufficiently large integers implies the same with a fixed multiplicative constant at every sufficiently large real argument: inside each unit cell only the continuous compensator can change, by at most 4. Choose $C$ so that $F(x)=Cx^r-sE(x)\ge0$ throughout $[1,\infty)$. The Mellin transform of $E$ initially equals its first-prime expression on $\Re z>1$. Multiplying by $z$ yields five shifted prime Dirichlet series, with the elementary density poles removed. In $\Re z>1/2$ the higher prime powers converge normally. Thus this expression continues meromorphically as the corresponding sum of shifted logarithmic zeta derivatives with their density poles removed. On the real interval $(r,\infty)$ it is regular. The Euler poles are canceled by the compensator, real zeta has no zero in $(0,1)$, and there is no zero of real part $>1/2$ at height $1$ or $\sqrt2$. The latter needs only the classical, rigorously verified low-height region. [Rational Mellin calculation](https://github.com/mccorvie/riemann-masullo/pull/7545) · [Platt and Trudgian, verified low zeros](https://arxiv.org/abs/2004.09765)

The Mellin transform of $F$ has the same real-axis regularity above $r$, since the added transform is $C/(z-r)$. Landau's theorem for a nonnegative measure implies convergence for all real arguments greater than $r$: a finite abscissa greater than $r$ would be a real singularity. Consequently $|E(x)|\le F(x)+Cx^r$ gives absolute convergence and holomorphy of its Mellin transform on the whole half-plane $\Re z>r$. The rational five-shift residue criterion implies $\Theta\le r$. Explicitly, on any candidate line to the right of $r$, nonnegative zero multiplicities satisfy four-neighbor harmonicity with ordinates shifted by $\pm1$ and $\pm\sqrt2$. A dense orbit meets an open zero-free interval by local finiteness, and a zero value propagates to all its neighbors. This argument works for both signs. In particular if $1/2<r<\Theta$, arbitrarily large integers satisfy $sE(N)>N^r$. [Continuous-measure Landau theorem](https://github.com/mccorvie/riemann-masullo/pull/7555) · [Rational zero-exclusion criterion](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521)

## Persistence across a complete interval

Suppose $\Theta>1/2$ and decrease $\alpha$ to $\alpha_0=\min(\alpha,1/4)$ in the estimates. Fix $1/2<v<\Theta$. Ingham's exponent $d=3(1-v)/(2-v)$ satisfies $d<1$. Uniformly for $X\le a\le b\le X+X^{1-\alpha_0}$, the common-height explicit formula and zero-density summation give
$$
 |E(b)-E(a)|\ll_{\alpha_0,v} X^\eta \log^5(2X),
 \qquad \eta=\max(v,\Theta-\alpha_0(1-d))<\Theta .
$$
For each high zero the smaller of the two endpoint bounds contributes $O(X^{\Re\rho}/\max(X^{\alpha_0},|\Im\rho|))$. Sublinear counting saves the factor $X^{-\alpha_0(1-d)}$. The remaining zeros cost $O(X^v\log^2 X)$ and the two truncation errors and prime powers cost $O(\sqrt X\log^2X)$. Partial summation preserves the estimate for the stated two-cosine prime sum. The proof handles arbitrary real endpoints. [Detailed short-interval argument](https://github.com/mlyle/riemann-masullo/tree/d244706da56d1c76931abb295f67bef2396ec7c3/research/5571/polynomial-grid-zero-density) · [Cully-Hugill and Johnston, Theorem 1.2](https://arxiv.org/pdf/2111.10001) · [An explicit form of Ingham's estimate](https://arxiv.org/abs/2507.15184)

Given $t<\Theta$ with $t>1/2$, choose $r$ strictly between $\max(t,\eta)$ and $\Theta$. At arbitrarily late integers $X$ the chosen sign exceeds $X^r$. The entire interval then has $sE(n)\ge X^r-O(X^\eta\log^5(2X))>X^t$. This proves the lower exponent for the minimum in the displayed identity.

For the other direction the same explicit formula at a single endpoint with height $\sqrt X/8$ gives $\psi(X)-X=O(X^\Theta\log^2(2X))$, because the sum of $1/|\rho|$ up to that height is $O(\log^2(2X))$ and $\Theta\ge1/2$. Removing prime powers and integrating by parts against $w(\log t)$ gives $E(X)=O(X^\Theta\log^2(2X))$. Since the interval contains $X$, this bounds either minimum and proves the identity also when $\Theta=1/2$. Replacing the continuous mean by $\sum_{j\le N}w(\log j)$ changes the error by $O(\log N)$ uniformly, so all conclusions hold for it as well.

The existing recurrence of bounded-error crossings in $[X,X^{1+\varepsilon}]$ for every fixed $\varepsilon>0$ has a precise boundary. A single sign bounded by $O_\varepsilon(X^{1/2+\varepsilon})$ at even the most favorable point of every late interval of the power-saving additive length above, for every $\varepsilon>0$, already implies rational RH. The unconditional existence of such points remains open. [Power-interval recurrence](first-prime-window-spacing.md)
