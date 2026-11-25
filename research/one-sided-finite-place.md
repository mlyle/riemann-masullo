# Finite-place orthogonal projections and the one-sided first-prime norm

Fix the rational trivial character, $1/2<s<1$, $d>0$, and $B(x)=1-\cos(x/2)$. Write $\ell_p=\log p$. The finite-place formula in (12.5.1.2), on an even radial test $H(\log|g|)$ with $H(0)=0$, is

$$
 W_p(H)=\ell_p\sum_{k\in\mathbb Z\setminus\{0\}}p^{-|k|/2}H(k\ell_p).
$$

Each multiplicative valuation shell has the same Haar mass as the units. The coefficient $\log p/\mu_p(\mathbb Z_p^\times)$ cancels that mass, and the ultrametric denominator gives $p^{-|k|/2}$ for both signs. For a one-sided profile supported at positive log norm, only one copy per positive $k$ occurs. The two descriptions coincide after dividing the even formula by two. Finite sharp-cutoff formulas follow by smoothing near endpoints and hold almost everywhere in the cutoff coordinate. [Project shell decomposition](../RiemannMasullo/Ch01_Introduction/Sec4.lean#L765) · [Manuscript normalization](../transcription/chapters/chapter-12.md) · [One-sided prime criterion](https://github.com/mlyle/riemann-masullo/blob/f14d01f00a3b21cc18db8e22eb8ba7bd6adb51e2/research/first-prime-one-sided.md)

## Which positive projections extract the first prime?

In the unramified radial subspace of $L^2(\mathbb Q_p^\times,d^\times u)$, normalize the characteristic function of each valuation shell to unit norm. They identify the subspace with $\ell^2(\mathbb Z)$, and multiplication by a uniformizer induces the bilateral shift $S$. For $0<r<1$ and real $\theta$, set

$$
 v_{r,\theta}(n)=(1-r^2)^{1/2}r^ne^{in\theta}1_{\{n\ge0\}},
 \qquad P_{r,\theta}=|v_{r,\theta}\rangle\langle v_{r,\theta}|.
$$

The geometric series gives a unit vector and $\operatorname{Tr}(S^kP_{r,0})=r^{|k|}$. Thus at $r=p^{-1/2}$ the finite-place formula is the positive rank-one state, multiplied by $\log p$, applied to the integrated shifts with coefficients $H(k\ell_p)$. The central coefficient vanishes.

The phase factor $1-\cos(k\theta)$ corresponds exactly to the signed operator

$$
 D(r,\theta)=P_{r,0}-(P_{r,\theta}+P_{r,-\theta})/2 .
$$

It has rank at most three and trace zero. On the two genuine neighboring shell vectors $e_0,e_1$ its corner, in that order, is

$$
 (1-r^2)r(1-\cos\theta)
 \begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

This follows by taking the individual matrix coefficients, which on nonnegative indices are $(1-r^2)r^{n+m}(1-\cos((n-m)\theta))$. Accordingly the orthogonal projections $\Pi_\pm$ onto $(e_0\pm e_1)/\sqrt2$ have

$$
 \operatorname{Tr}(\Pi_\pm D(r,\theta))
 =\pm(1-r^2)r(1-\cos\theta).
$$

Both are positive projections, with opposite answers on the actual phase-compensated local state.

To test the positive-part variational formula at a scalar cutoff $L$, use $0\le f(L)\le1$ and $K_f(x)=\int_x^\infty f(L)e^{-dL}\,dL$. On a finite interval Fubini pairs the positive-branch first primes with $e^{-(s-1/2)x}B(x)K_f(x)$ in addition to their standard $p^{-1/2}$ weight. The allowed choice $f=1$ gives $K_f(x)=e^{-dx}/d$. On the first shell put $t=s+d$, $r=p^{-t}$ and $\theta=\ell_p/2$. The normalized local first-prime contribution to this one-sided dual pairing is exactly $\ell_p r(1-\cos\theta)/d$. The positive projection $\Pi_+$ recovers it with discrepancy $\ell_p r^3(1-\cos\theta)/d$, which is absolutely summable over all primes since $3t>1$. The negative choice of shell vector yields its opposite. This comparison uses finite partial sums when the separate prime and continuous terms diverge.

## The Schatten threshold

For any $q\ge1$ the direct sum $\bigoplus_p\ell_pD(p^{-t},\ell_p/2)$ belongs to the Schatten class $S_q$ exactly when $qt>1$. The trace distance between $P_{r,\theta}$ and the projection onto $e_0$ is $2r$, by the two-dimensional formula for unit pure states. Thus $\|D(r,\theta)\|_q\le\|D(r,\theta)\|_1\le4r$. For the converse use the $(0,1)$ entry above. On infinitely many disjoint intervals of $\log p$ of fixed length in each period of $\cos((\log p)/2)$, the factor $1-\cos\theta$ is at least one. The prime number theorem in these fixed relative intervals gives divergence of $\sum_p(\log p)^qp^{-qt}(1-\cos\theta)^q$ for $qt\le1$, including equality. In fact each positive and negative spectral part has the same trace, since $D$ has trace zero. Their traces each dominate the magnitude of the appropriate two-shell pairing.

So the genuine phase-compensated operator is unconditionally Hilbert–Schmidt for $t=s+d>1/2$, but the signed local states have divergent positive and negative trace masses for $t\le1$. Bounding the one-sided dual by the sum of positive trace norms of the individual places loses precisely the essential continuous-mean cancellation, already on the allowed constant dual weight. This rules out that specific domination. The signed global comparison is open.
