# An alternative for the actual signed first-prime statistic

Fix $0<b<1/2$, $s=1/2+b$, and the rational trivial chart. There is an alternative for the outstanding scalar first-prime coordinate. Either zeta is zero-free in $\Re z>s$, or the admissible edge probes can also be made to annihilate **all** first primes in aggregate while retaining every previously constructed finite-dimensional local cancellation and a fixed positive edge floor. The latter conclusion applies to the individual selected profiles. It gives no translated estimate or open-to-closed spectral trace inequality. [Existing finite-coordinate construction](fourier-barycenter-probes.md) · [Actual normalized prime-minus-pole measure](first-prime-topology.md)

## A compact probe with no Mellin zeros in the required strip

Let $\phi$ be the project Fabius probability density on $[-1,1]$. Its bilateral transform $\Phi(z)$ has no zeros when $\Re z\ne0$. Put $g(x)=e^{2x}\phi(x)$ and $K=g*g^\vee$, where $g^\vee(x)=g(-x)$. This is a nonnegative smooth compact even kernel with $K(0)>0$ and bilateral Laplace transform $\mathcal L K(w)=\Phi(2+w)\Phi(2-w)$. Hence $\mathcal L K$ has no zeros in $|\Re w|<2$ and $\widehat K(t)>0$ on the real line. This choice is an eligible baseline in the previous construction. [Lean verification of the Fabius transform](https://github.com/mlyle/riemann-masullo/blob/32b847f62ef847eb11ada13ab8a452fac6dd1139/RiemannMasullo/ForMathlib/Analysis/Fourier/Fabius.lean#L464)

Set $U_A(x)=K(x-A)+K(x+A)$ and write $p(P)=\int_{\mathbb R}P(x)\cosh(x/2)/\cosh(bx)\,dx$ for the common even polar moment. Let the full first-prime coordinate in the same numerator convention be

$$
 S(P)=2\sum_p(\log p)\frac{p^{-1/2}}{\cosh(b\log p)}P(\log p).
$$

With $R(P)=S(P)-2p(P)$, for $A$ larger than the support radius of $K$,

$$
 \tfrac12R(U_A)=\int_0^\infty K(x-A)\,d\omega_b(x).
$$

Here $\omega_b$ is the signed prime-minus-pole measure in the preceding note. For every such $A$ this is a finite ordinary arithmetic sum and an ordinary compact integral.

## Bounded discrepancy rules out more distant zeros

Suppose $R(U_A)$ is bounded for $A$ sufficiently large. The convolution $h(A)=\int K(A-x)\,d\omega_b(x)$ with the measure supported on $[0,\infty)$ vanishes for $A$ sufficiently negative and is bounded on bounded intervals. Its bilateral transform with weight $e^{-wA}$ is holomorphic for $\Re w>0$. On its initial half-plane $\Re(s+w)>1$, absolute Fubini identifies this transform as $\mathcal L K(-w)\int_0^\infty e^{-wx}d\omega_b(x)$. The nonvanishing just proved permits holomorphic continuation of the second factor throughout $0<\Re w<2$.

Put $d\widetilde\omega_b=d\omega_b+e^{-x/2}dx/\cosh(bx)$. The added integrable measure has a holomorphic transform in $\Re w>0$. In terms of the normalized prime error $\nu_s$ one has $2\,d\nu_s=(1+e^{-2bx})d\widetilde\omega_b$. Thus $\mathcal L\nu_s(w)$ continues holomorphically for $0<\Re w<1-s$ by taking half the sum of the two transforms at $w$ and $w+2b$. Both real parts belong to $(0,2)$. The same identity applies in a neighborhood of $\Re w=1-s$. But the meromorphic continuation of $\mathcal L\nu_s(w)$ is

$$
 -\zeta'(s+w)/\zeta(s+w)-\sum_{p,k\ge2}(\log p)p^{-k(s+w)}-1/(s+w-1).
$$

Every zero strictly to the right of $s$ would give a pole. The same proof works with a subexponential bound on $R(U_A)$ in place of boundedness. Consequently, in the presence of any such zero, the absolute values $|R(U_A)|$ are unbounded along positive $A$.

## Unbounded discrepancy gives a small exact arithmetic correction

The prime number theorem gives $S(U_A)/p(U_A)\to2$. Indeed $e^{-A}\vartheta(e^{A+u})\to e^u$ uniformly for $u$ in the fixed support interval of $K$. Testing its Stieltjes measures against the smooth weights from $K$ gives

$$
 p(U_A)\sim 2e^{(1/2-b)A}\int K(u)e^{(1/2-b)u}\,du,\qquad
 S(U_A)\sim 4e^{(1/2-b)A}\int K(u)e^{(1/2-b)u}\,du.
$$

The weights, after dividing out the displayed exponentials, converge in the uniform and first-derivative norms on this fixed compact interval. Thus the two asymptotics follow by integration by parts from the stated prime number theorem.

Assume now $\limsup_{A\to\infty}|R(U_A)|=\infty$. Pick $A$ so large that $|R(U_A)|$ exceeds a prescribed constant. For $B>A$ take the exactly polar-free numerator

$$
 V=U_A-\frac{p(U_A)}{p(U_B)}U_B .
$$

As $B\to\infty$, $S(V)=R(U_A)-p(U_A)R(U_B)/p(U_B)\to R(U_A)$ and $p(U_A)/p(U_B)\to0$. Thus $|S(V)|$ can be made arbitrarily large while $|\widehat V(t)|\le4\widehat K(t)$ at every frequency. Every finite-dimensional local coordinate allowed in the Fourier-barycenter argument stays bounded on $V$, since both translates escape the unit neighborhood and the measures have finite variation outside it.

Start with the finitely many polar-free vertices at stage $n$ of that argument. Replace each by

$$
 P_{n,i}-\frac{S(P_{n,i})}{S(V)}V .
$$

All first-prime coordinates and both polar coordinates now vanish identically. Choose $A,B$ so that the coefficients are at most $1/16$ in absolute value and the perturbations in the finite-dimensional local coordinates are smaller than $1/n$. The positive eventual floor at worst falls from $\widehat K/2$ to $\widehat K/4$. The interior margin in the convex hull of the other coordinates survives. Taking the final convex combination gives profiles with both poles, every normalized rational local term in aggregate, the higher powers in aggregate, any specified finite list of places, and the actual Sonin trace all zero. Individual first-prime places outside the selected list need not vanish.

The assumptions involving $R(U_A)$ make no reference to a spectral zero. An off-edge zero strictly beyond $b$ is one way to guarantee the unbounded case. A possible zero exactly on the edge need not produce unbounded smoothed discrepancy at that width. Simultaneous single-test cancellation leaves both the translated prime estimate and the project comparison of two different strip traces open.
