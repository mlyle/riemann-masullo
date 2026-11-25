# A single compensated moment of the degree-one rational prime term

Fix $0<b<1/2$, write $s=1/2+b$, and let $\vartheta(X)=\sum_{p\le X}\log p$. On the positive log half-line consider the signed locally finite measure

$$
 d\nu_s(x)=e^{-sx}\big[d\vartheta(e^x)-e^x\,dx\big],\qquad
 B(x)=2-\cos x-\cos(\sqrt2 x)\ge0 .
$$

If for every $\delta>0$ the scalar partial integral $\int_{[0,L]}B(x)\,d\nu_s(x)$ is $O_\delta(e^{\delta L})$ as $L\to\infty$, then the Riemann zeta function has no zeros in $\Re z>s$. Boundedness, ordinary convergence and every polynomial growth bound are special cases. This criterion imposes only one partial-integral bound. The two individual cosine moments may have unrelated growth.

## Mellin transform and pole propagation

Writing $M(L)$ for that cumulative signed integral, the holomorphic function $w\int_0^\infty e^{-wL}M(L)\,dL$ on $\Re w>0$ equals the Laplace transform of $B\nu_s$ wherever the latter converges absolutely, by integration by parts. The growth assumption proves local uniform absolute convergence of this representation, including its derivatives. For $\Re z>1$ define

$$
 F(z)=\sum_p(\log p)p^{-z}-\frac{1}{z-1}
 =-\frac{\zeta'}{\zeta}(z)-\sum_{p,k\ge2}(\log p)p^{-kz}-\frac{1}{z-1}.
$$

This identity is the absolutely convergent Euler logarithmic derivative. The higher powers give a holomorphic function on $\Re z>1/2$ by locally uniform absolute convergence. The pole of $-\zeta'/\zeta$ at $1$ is canceled. At a zeta zero in this domain the residue of $F$ is minus its multiplicity. [Mathlib Euler logarithmic derivative](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/Dirichlet.html#ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div)

With $z=s+w$ the transform of $B\nu_s$ is the meromorphic expression

$$
 2F(z)-\tfrac12\big[F(z+i)+F(z-i)+F(z+i\sqrt2)+F(z-i\sqrt2)\big].
$$

Its equality with the above holomorphic function for $\Re z>1$ forces the poles of this combination to be removable throughout $\Re z>s$. Fix a real $\sigma>s$. Let $m(t)$ be the nonnegative order of the zero at $\sigma+it$, or zero at a regular nonzero point or the canceled pole at $1$. Taking the residue at every $\sigma+it$ gives

$$
 4m(t)=m(t+1)+m(t-1)+m(t+\sqrt2)+m(t-\sqrt2).
$$

At a zero value of $m$, all four neighbors vanish. The additive group $\mathbb Z+\sqrt2\mathbb Z$ is dense in $\mathbb R$. Every translate of it intersects an open interval disjoint from the locally finite zero set on this vertical line. Propagating zero values back by the four allowed steps proves $m(t)=0$ for every $t$. This uses no zero-density theorem or bound on multiplicities.

## Relation to the actual signed norm statistic

For even radial tests the two real branches give the same values. After one takes out the common factor $2$, the difference of the rational degree-one prime measure and the two classical polar terms in numerator coordinates has positive-half-line density/measure

$$
 d\omega_b(x)=
 \frac{e^{-x/2}d\vartheta(e^x)-2\cosh(x/2)\,dx}{\cosh(bx)}
 =\frac{2}{1+e^{-2bx}}\,d\nu_s(x)-\frac{e^{-x/2}}{\cosh(bx)}\,dx.
$$

The last term has finite variation. Any separately chosen overall normalization of the polar moment is fixed here by removal of the $1/(z-1)$ pole of the first-prime series. The previous construction enforces each polar moment individually. For $B\omega_b$ the same subexponential partial-integral condition is equivalent to the one for $B\nu_s$. In both directions the extra finite measure contributes a bounded amount, and the remaining reweighting function and its reciprocal are bounded and have bounded variation on $[0,\infty)$. Stieltjes integration by parts preserves each subexponential bound.

Even if RH holds, the total variation of $\nu_s$ is infinite at infinity. The atomic prime measure and the continuous pole measure are mutually singular, and $\int_0^\infty e^{(1-s)x}dx=\infty$. More generally, if $\nu_s$ extended by zero to the negative half-line were a tempered distribution, its one-sided Laplace transform would be holomorphic on $\Re w>0$, which again excludes zeros of $\zeta(s+w)$ in that half-plane by the formula for $F$. Thus assigning continuous cosine moments through meromorphic continuation alone does not justify the growing-test limits in the Fourier barycenter construction. The obstruction above already applies to one predetermined nonnegative cosine compensator.

The calculation leaves zeros exactly on $\Re z=s$ open. Extending the required subexponential bound to every $b>0$ tending to zero would exclude all zeros to the right of the critical line. All local convex cancellations proved for finite weighted variation remain available independently of this missing estimate. [Fourier barycenter and its hypotheses](fourier-barycenter-probes.md)

## The exact exponential growth rate

Let $\Theta=\sup_\rho\Re\rho$ over all nontrivial zeta zeros. Then

$$
 \limsup_{L\to\infty}\frac{\log(1+|M(L)|)}{L}
   =\max(0,\Theta-s).
$$

For the lower bound, if the limsup is $c$, the holomorphic transform and the residue argument above apply throughout $\Re z>s+c$ by integration by parts, so $\Theta\le s+c$. For the upper bound, Theorem 1.9 of *The sequence of prime gaps is graphic* gives the truncated explicit formula at height $2X$ for all large real $X$ with error $O(\log X\log\log X)$. The standard order count $N(T)=O(T\log T)$, with multiplicity, gives $\sum_{|\Im\rho|<2X}|\rho|^{-1}=O(\log^2 X)$ by partial summation. Hence $\psi(X)-X=O(X^\Theta\log^2 X)$. Subtracting higher prime powers costs $O(\sqrt X\log^2 X)$ by the elementary sum over their exponents, and $\Theta\ge1/2$ by functional equation and existence of nontrivial zeros. Thus $E(x)=\vartheta(e^x)-e^x=O((1+x)^2e^{\Theta x})$. The function $B$ and its derivative are bounded. One integration by parts against $dE$ now gives $M(L)=O((1+L)^3e^{\max(0,\Theta-s)L})$, proving the other inequality. In particular the cubic bound $M(L)=O((1+L)^3)$ is equivalent to absence of zeros strictly to the right of $s$. [Primary truncated formula, Theorem 1.9](https://link.springer.com/article/10.1007/s00208-023-02574-1)
