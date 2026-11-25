# Where the translated physical trace can affect the endpoint comparison

Fix a number field, a norm section, a unitary character $\psi$ trivial on that section, a strip half-width $\alpha>0$ and a Sobolev order $s>1$. Use the Haar measure of the project. The test is $\varphi_y(g)=\psi(g)H(\log|g|-y)$ with $H\in C_c^\infty((0,\infty))$ and $y\ge0$. The upper estimates also allow compactly supported smooth $H$ vanishing on $(-\infty,0]$. The open-to-closed criterion for #5571 uses $s=3$ and the two vanishing polar moments $\int H(h)e^{\pm h/2}dh=0$. Write $A_y$ for the Hardy–Sobolev convolution by this test. A physical cutoff $\rho_y$ of module radius $\Lambda_y$ is supported on $|x|\le R(y)=\log\Lambda_y$, where $x=\log|g|$, and $0\le\rho_y\le1$. The localized convolution used in Penner’s physical stages is $T_y=M_{\rho_y}A_y$. The trace of interest here is $\operatorname{Tr}(T_y P)$ or $\operatorname{Tr}(T_y P_{b(y)})$. [Project cutoff](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch09_HardySobolev/Sec3.lean#L2912) · [Physical operator, bandwidth and cutoff order](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L212) · [Fixed-width local and all-width trace criteria](https://github.com/mccorvie/riemann-masullo/pull/7586)

## Uniformity for actual increasing theta bands

Take $Y\ge2$, $0\le R(y)\le y$ on $[Y,2Y]$, and $D=\inf_{Y\le y\le2Y}(y-R(y))$. Suppose that the traces being integrated are measurable. For any **fixed contraction** $P$,
$$
 \frac1Y\int_Y^{2Y} e^{-\alpha y}|\operatorname{Tr}(T_yP)|dy
 \ \ll_{\alpha,s,H,F}\
 (1+Y)e^{-2\alpha Y}+
 \frac{Y^{(s-1)/2}\, e^{-2\alpha D}}{(1+D)^{s/2}}. \tag{1}
$$
For any choice $P_y$ from a **single nested family of orthogonal projections**, (1) holds with a further factor $1+\log(2+Y)$ on the second term. The choice can vary with $y$ without any bound on rank, bandwidth or rate. Penner’s global theta bands form such a family. Beyond a field-dependent bandwidth, the ordinary single finite-stage boxes at the primes below the bandwidth agree with it. For arbitrary projections varying without a nesting assumption, a pointwise bound holds with $Y^{s/2}$ in place of $Y^{(s-1)/2}$ and no extra logarithm. [Monotone bands](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L46) · [Identification of the actual single stages](https://github.com/sergmister/riemann-masullo/blob/394da1b3caac72bb160db3ee4007b320426a7556/RiemannMasullo/Research/TraceComparison/PhysicalThetaBands.lean#L139)

In particular, at $s=3$ one can use the growing physical cutoff
$$R(y)=y-\frac{1}{2\alpha}\log(2+y)$$
for all sufficiently large $y$. The absolute weighted dyadic mean is $O((\log Y)^{-3/2})$ for a fixed projection and $O((\log Y)^{-1/2})$ for any choice from nested bands. Summing backwards over dyadic intervals gives the same vanishing for the mean on $(0,Y]$, assuming local integrability there. This includes arbitrarily large bandwidths and the full theta or spectral projection. In module coordinates the cutoff is $\Lambda_y=e^y/(2+y)^{1/(2\alpha)}$. At $R(y)\le(1-\epsilon)y$ with fixed $\epsilon>0$, the pointwise bound gives absolute integrability at the endpoint even for arbitrary changing contractions.

### Proof of the localized trace bounds

In the coordinates $C^1\times\mathbb R$ the measure is kernel Haar measure times $dx$. Let $V$ be the kernel Haar volume. The convolution in the angular variable has rank one, with scalar $V$, and vanishes on the other angular modes. On its active mode conjugate the problem to unweighted $L^2(dx)$ by multiplication by $\sqrt{w(x)}$, where $w(x)=e^{2\alpha|x|}(1+x^2)^{s/2}$. The resulting kernel is
$$K_y(x,t)=V\,\rho_y(x) H(x-t-y)\sqrt{w(x)/w(t)}.$$
The same kernel calculation extends to every unitary character by using the angular and radial frame given by multiplication by the full character: convolution by the modulated kernel is its unitary conjugate of convolution by the unmodulated kernel. The radial cutoff preserves the angular modes. An arbitrary ambient contraction remains allowed in the trace, since the input and output vectors below are embedded in the active mode. We apply the nesting argument to the original ambient projections. [Actual weight](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch09_HardySobolev/Sec2.lean#L3069) · [Translation orientation](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch09_HardySobolev/Sec3.lean#L353) · [Haar normalization](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec4a.lean#L986)

Use output cells $I_j=[j,j+1)$ and input cells $I_l$, for integer $j,l$. A nonzero block requires $|j-l-y|\le C_H$. On that block, $H(x-t-y)$ has a separated Fourier series in $(x-j)-(t-l)$ with frequencies independent of $j,l,y$ and coefficients bounded by $C_H(1+|n|)^{-2}$. To see this, multiply $H(j-l-y+u)$ by one fixed smooth cutoff equal to one on $[-1,1]$ and supported in $(-2,2)$, extend with period $5$, and integrate by parts twice. Its coefficient bound is uniform. The weights on each unit cell are comparable to their value at its integer endpoint, with constants depending only on $\alpha,s$.

In particular, each block is nuclear. Its trace paired with $P_y$ has absolute value bounded by
$$
 C\sqrt{w(j)/w(l)}\sum_n(1+|n|)^{-2}
           \|1_{I_j}P_y^*\xi_{l,n}\|.
$$
Here $\xi_{l,n}$ is independent of $y,j$, supported in the active angular mode on $I_l$, and has norm at most one. Explicitly it is a unit-cell exponential times $\sqrt{w(l)/w(t)}$ and a fixed normalizing constant. The other vector, on $I_j$, absorbs $\rho_y(x)\sqrt{w(x)/w(j)}$ and has uniformly bounded norm. Only finitely many cells contribute for each $y$.

When $j<0$, the normalized weight ratio is $O(e^{-2\alpha y})$, since $l=j-y+O_H(1)$ and $(1+j^2)/(1+l^2)$ is bounded. There are $O(1+Y)$ output cells and only boundedly many input cells per output at each $y$. This proves the first term of (1). For $j\ge0$, put $m=-l$. Then $m\ge D-O_H(1)$, $j\le2Y+1$ and, up to fixed constants,
$$
 e^{-\alpha y}\sqrt{w(j)/w(l)}
 \ \ll\ e^{-2\alpha m}(1+Y)^{s/2}(1+|m|)^{-s/2}.
$$
Each $(j,l)$ can occur only on a set of $y$ of bounded length. For fixed $l,n$ and fixed $P$ the sum of the squares of $\|1_{I_j}P^*\xi_{l,n}\|$ over $j$ is at most one. Cauchy–Schwarz gives $O(\sqrt{Y})$ for its sum over the possible $j$. Sum the Fourier coefficients and the exponential tail in $m$, and divide by $Y$ to obtain (1). Bounding each vector norm by one before summing $m$ gives the pointwise version.

For nested projections, fix $l,n$ and select, for each of the $N=O(1+Y)$ output cells, one projection approximately maximizing $\|1_{I_j}P_y\xi_{l,n}\|$ over the relevant $y$. Sort the $N$ selected projections by inclusion and take the successive orthogonal differences, including the first projection as the first difference. The increments applied to $\xi_{l,n}$ are pairwise orthogonal and have total squared norm at most one. Every selected prefix is a sum of at most $1+\lceil\log_2 N\rceil$ dyadic blocks. By Cauchy–Schwarz over those blocks, then orthogonality of the output cells, the sum over $j$ of the squared restricted prefix norms is at most $(1+\lceil\log_2 N\rceil)^2$. Indeed each full dyadic level has total squared block norm at most one. Taking the supremum by approximation and applying Cauchy–Schwarz over $j$ gives $O(\sqrt Y(1+\log Y))$. The constant is independent of the family and choices.

## A sharp obstruction for fixed ambient projections

The power of $Y$ in (1) is attained on genuine translated symbols, with one fixed orthogonal projection on the actual weighted angular Hilbert space. Its range is described explicitly below. It has no asserted identification with the theta subspace.

Fix $0<\alpha<1/2$, take nonnegative nonzero $g\in C_c^\infty((0,\infty))$ and set $H=g''-g/4$. Both polar moments vanish by integration by parts. Its observable moment $J_\alpha=\int H(h)e^{\alpha h}\,dh=(\alpha^2-1/4)\int g(h)e^{\alpha h}dh$ is strictly negative. Let $d(x)=\kappa\log x+O(\log\log x)$, $\kappa>0$, be eventually increasing and differentiable, with $d'(x)\sim\kappa/x$. Use the partial isometry $U$ from the negative input half-line $t\le-d(x_0)$ onto the positive output half-line $x\ge x_0$ given by
$$
 (Uf)(x)=1_{[x_0,\infty)}(x)\sqrt{d'(x)}\, f(-d(x)).
$$
The Jacobian makes it unitary between those orthogonal subspaces. On their sum, $P_\pm=(U^*U+UU^*\pm U\pm U^*)/2$ are fixed orthogonal projections. Extend by zero on its orthogonal complement and use the inverse weight conjugation to realize them in the project’s Hilbert space.

For large $y$, the two diagonal blocks have zero trace as $H(-y)=0$, and the reverse cross term vanishes by support. The remaining cross term is
$$
 \operatorname{Tr}(T_y P_\pm)
 =\pm\frac V2\int_{x_0}^\infty \rho_y(x)H(x+d(x)-y)
              \sqrt{w(x)/w(-d(x))}\sqrt{d'(x)}\,dx .
$$
This diagonal calculation also follows by applying the absolutely summable unit-cell expansions above to each block and integrating its rank-one trace after the change of variable $t=-d(x)$. The compact output support permits a finite sum over cells. Choose the log radius $R(y)=y-d(y)+C_0$ with $C_0>\sup(\operatorname{supp}H)+2$. On the contributing values $h=x+d(x)-y$ one has $x=y-d(y)+h+o(1)$ uniformly, so every admissible project cutoff equals one there for all sufficiently large $y$. Indeed the inner upper plateau boundary is $\log(\Lambda_y-\epsilon_y)=R(y)+o(1)$ since $0<\epsilon_y<\Lambda_y^{-1}$. After substituting $h=x+d(x)-y$, the normalized expression is asymptotic to
$$
 \pm \frac{V\sqrt{\kappa}}2\,J_\alpha\,
 y^{(s-1)/2}(1+d(y))^{-s/2}\,e^{-2\alpha d(y)}. \tag{2}
$$
Here the exponential part of the weight divided by $e^{\alpha y}$ is exactly $e^{\alpha h-2\alpha d(x)}$, $dx/dh\to1$ uniformly, and $d(x)-d(y)=o(1)$. Smoothness at the origin plays no role, since the two half-lines are separated there.

For $d(y)=\kappa\log y$, every $\kappa<(s-1)/(4\alpha)$ permits a divergent normalized trace of either sign and hence a divergent absolute weighted Cesàro mean. At the finer fixed-projection threshold
$$
 d(y)=\frac{s-1}{4\alpha}\log y-\frac{s}{4\alpha}\log\log y
$$
the expression in (2) tends to a nonzero constant. Fixed additive shifts of the radius can instead be absorbed into $d$. This lower example and (1) pin the transition for fixed ambient projections. The nested-family upper bound has its stated additional logarithm.

## The remaining comparison

For every translated test, Penner supplies nuclearity of $A_yP_{\rm spec}$. Its trace agrees with the quotient trace by projection cyclicity and the Hilbert quotient identification. At every admissible cutoff the exact decomposition is
$$
 \operatorname{Tr}(A_yP_{\rm spec})
 =\operatorname{Tr}(M_{\rho_y}A_yP_{\rm spec})+
   \operatorname{Tr}((1-M_{\rho_y})A_yP_{\rm spec}).
$$
Formula (1) disposes of the first summand in #7586’s weighted absolute Cesàro mean, even at the stated growing cutoff. Thus in the strip-trace defect one can subtract the signed local-term scalar directly from the second summand. It includes the two outer tails of the physical cutoff. Penner’s theorem exhausts the cutoff at each fixed translate and gives no uniform rate for these tails. The example (2) shows precisely why an argument using only contractivity, nesting or rank-independent Hilbert projection bounds cannot extend the geometric estimate through the entire region. Estimating the actual outer term minus the normalized local principal values remains necessary. The estimates in this note are written proofs. The separate all-field result on individual genuine theta lifts at growing Sobolev degree is formalized in [PR #7588](https://github.com/mccorvie/riemann-masullo/pull/7588).

