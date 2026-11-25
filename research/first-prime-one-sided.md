# One frequency and one sign of the integrated first-prime error

**25 November 2026.** Theorem 12.5.1.1, pp. 519–520, rational principal character. This is a classical deduction. Its arithmetic estimate is open. The argument can be used independently of the zero samples or any computation of a zero ordinate.

Fix $1/2<s<1$, $h=1/2$, and $B(x)=1-\cos(hx)$. Write $\vartheta(X)=\sum_{p\le X}\log p$ and set
$$
 M(L)=\int_{[0,L]} B(x)e^{-sx}[d\vartheta(e^x)-e^x\,dx],\qquad
 M_+(L)=\max(M(L),0),\quad M_-(L)=\max(-M(L),0).
$$
For **either sign individually**, the following two statements are equivalent.

* For every $\delta>0$, $\int_0^\infty M_\pm(L)e^{-\delta L}\,dL<\infty$.
* The Riemann zeta function has no zero with real part strictly greater than $s$.

Thus an averaged upper bound on just one sign would be sufficient, even if it allows exceptional scales. The assertion at a single width is silent about zeros on the boundary.

### The small box

Put $z=\sigma+it$, $1/2\le\sigma\le1$, $|t|\le1/2$, $z\ne1$. Euler summation at $1$, centered by $1/2$, gives
$$
 \zeta(z)=\frac1{z-1}+\frac12-z\int_1^\infty (\{u\}-1/2)u^{-z-1}\,du.
$$
The integral has absolute value at most $1/(2\sigma)$. At a zero this would imply $\sigma|z+1|\le|z|\,|z-1|$. On the box, $|z|\le\sqrt2\sigma$ and $|z-1|\le1/\sqrt2$, whereas $|z+1|\ge1+\sigma>1$. This rules out every zero there. The pole at one is removed separately below. [NIST, equation 25.2.8](https://dlmf.nist.gov/25.2.E8)

### What one cosine detects

For $\Re z>1$ the unweighted transform is
$$
 F(z)=-\frac{\zeta'(z)}{\zeta(z)}
       -\sum_{p,k\ge2}(\log p)p^{-kz}-\frac1{z-1}.
$$
The higher powers converge locally uniformly for $\Re z>1/2$. The pole at $1$ cancels. The remaining poles in that half-plane have residue minus the zero multiplicity. Set $G(z)=F(z)-(F(z+ih)+F(z-ih))/2$. On $\Re w>1-s$, integration of the primitive gives $\mathcal L M(w)=G(s+w)/w$. The small-box result and the Euler product imply that this meromorphic expression is holomorphic in a neighborhood of **every real** $w>0$, including points for which $s+w=1$.

If $G$ is holomorphic for $\Re z>s$, then on every vertical line $\sigma>s$ the nonnegative zero multiplicities satisfy $2m(t)=m(t+h)+m(t-h)$. Each $t+h\mathbb Z$ contains a point of $[-h/2,h/2]$, where the small box and the Euler product give $m=0$. The recurrence propagates that zero along the entire progression. Hence $\zeta$ has no zero with real part $>s$.

### Why one sign suffices

For example, suppose the asserted weighted integrals of $M_+$ are finite. Its Laplace transform $P$ is holomorphic for $\Re w>0$. The negative part is nonnegative, locally integrable, and at most exponential in $L$ by the elementary bound $\vartheta(X)\le X\log X$. Its Laplace transform initially equals $P(w)-G(s+w)/w$. If its abscissa of convergence were a real number $a>0$, this meromorphic identity and the small box would continue its transform holomorphically through the real point $a$. Landau's nonnegative Laplace-transform theorem excludes this. Thus the negative part also has finite Laplace integrals throughout $\Re w>0$. Their difference makes $G(s+w)$ holomorphic there, and the recurrence applies. Interchanging the signs gives the other implication in the same way.

The version of Landau's argument needed here follows from positivity. If a nonnegative transform were regular near its finite real abscissa $a$, choose $q>a$ so close that the Taylor disc about $q$ extends to a real point $q-r<a$. For $0<r$ inside the disc the Taylor series at $q-r$ is the sum of the nonnegative moments $\int x^n e^{-qx}f(x)\,dx\,r^n/n!$. Monotone convergence then makes the Laplace integral finite at $q-r$, a contradiction.

Conversely, the classical truncated explicit formula and zero count give $\vartheta(X)-X=O(X^s\log^2 X)$ if all zeros have real part at most $s$. Stieltjes integration by parts using bounded $B,B'$ gives $M(L)=O((1+L)^3)$. Both sign integrals therefore converge for every $\delta>0$. [Truncated explicit formula, Theorem 1.9](https://link.springer.com/article/10.1007/s00208-023-02574-1) · [Details of the upper estimate](https://github.com/mlyle/riemann-masullo/blob/b52bf059948501197f970e032593f126ed817318/research/first-prime-topology.md)

More quantitatively, let $\Theta$ be the supremum of the real parts of the nontrivial zeros. For **every** $0<d<\Theta-s$, **both** $\int M_+(L)e^{-dL}dL$ and $\int M_-(L)e^{-dL}dL$ diverge. Finiteness at $d$ for either sign would give holomorphy on $\Re w>d$ by the same Landau argument and would exclude zeros with real part $>s+d$. For every $d>\max(0,\Theta-s)$ both integrals converge by the explicit formula. No claim is made at the critical exponent. A bound on one sign along only a subsequence does not imply the required integral estimate.
