# The signed width defect and the failure of a bounded common-mode inverse

Fix a number field, a theta center $a$, two half-widths $0\le\alpha<\beta$, and a common Sobolev degree $s\ge0$. Write $W_\eta$ for the log-weighted class-Haar space with squared density $w_\eta(x)=e^{2\eta|x|}(1+x^2)^{s/2}$. Write $\Theta_\eta$ for the closure of the actual centered polar-free theta functions. Let $q_\eta:W_\eta\to Q_\eta=W_\eta/\Theta_\eta$ be the quotient and $l_\eta:Q_\eta\to W_\eta$ its isometric orthogonal lift. Thus $l_\eta q_\eta=P_\eta$ is the spectral projection. The identity of physical representatives is a dense contraction $i:W_\beta\to W_\alpha$, since continuous compactly supported packets belong to both spaces and are dense in the narrower one. It takes each actual theta source to the same source, and $\overline{i\Theta_\beta}=\Theta_\alpha$. It descends to the dense contraction
$$
 J:Q_\beta\longrightarrow Q_\alpha,\qquad Jq_\beta=q_\alpha i,\qquad
 K=\ker J=\{q_\beta u:iu\in\Theta_\alpha\}.
 \tag{1}
$$
The norm on this closed defect space is the wide quotient norm. Its elements have genuine theta approximations at the narrower width. Stronger control of the tails of those same approximations would be needed to conclude approximation at the wider width. [Genuine theta closure](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec1.lean#L638) · [Wide and narrow quotient definitions](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L96)

## Exact subtraction on the true Hilbert spaces

For a genuine convolution $A_\eta$ by the same test in each width, the weighted representatives agree after inclusion. Each theta space is invariant. The quotient actions $T_\eta=q_\eta A_\eta l_\eta$ therefore satisfy $J T_\beta=T_\alpha J$. Suppose these operators are nuclear, as in the supported polar-free comparison. Then the entire common-width contribution cancels exactly and
$$
 \operatorname{Tr} T_\beta-\operatorname{Tr} T_\alpha
       =\operatorname{Tr}(T_\beta\Pi_K)
       =\operatorname{Tr}(T_\beta|_K). \tag{2}
$$
Here $\Pi_K$ is the orthogonal projection in $Q_\beta$ and $K$ is invariant under $T_\beta$. No closed-range hypothesis on $J$ enters.

Indeed set $H=JJ^*$ and $S_\varepsilon=J^*(H+\varepsilon I)^{-1}$. Then $J S_\varepsilon\to I$ and $S_\varepsilon J\to I-\Pi_K$ strongly, and both products are positive contractions. The first convergence follows from the spectral theorem applied to $u/(u+\varepsilon)$ and density of the range of $J$. The second follows from $J^*(JJ^*+\varepsilon I)^{-1}J = (J^*J)(J^*J+\varepsilon I)^{-1}$. For fixed $\varepsilon$, cyclicity across the two Hilbert spaces and intertwining give $\operatorname{Tr}(T_\beta S_\varepsilon J)=\operatorname{Tr}(T_\alpha J S_\varepsilon)$. Uniformly bounded strong convergence against a fixed nuclear operator passes to the trace by approximation with finite-rank operators. This proves (2). In particular, over rational $\zeta$ a known central ordinate is interior to both positive widths and every one of its actual multiplicity jets is retained in both. Its entire translated coefficient cancels.

At a physical cutoff $m$ for which $X_\eta=q_\eta M_m A_\eta l_\eta$ is nuclear, without assuming that $M_m$ preserves the theta space, the same calculation instead gives
$$
 \operatorname{Tr}X_\beta-\operatorname{Tr}X_\alpha
 =\operatorname{Tr}(X_\beta\Pi_K)
    +\lim_{\varepsilon\downarrow0}\operatorname{Tr}\big[(JX_\beta-X_\alpha J)S_\varepsilon\big]. \tag{3}
$$
The coefficient of $S_\varepsilon$ has the actual physical formula
$$
 JX_\beta-X_\alpha J=q_\alpha M_m A_\alpha(i l_\beta-l_\alpha J).
 \tag{4}
$$
The difference of lifts takes values in $\Theta_\alpha$, since its narrow quotient is zero. Acting by $A_\alpha$ preserves that space. Thus (4) reconstructs exactly the narrow theta input which the physical truncation sends back to the spectral quotient. At full physical exhaustion this coefficient is identically zero for $m=1$. For finite stages the limit in (3) exists as a trace subtraction for each fixed translate. A uniform smallness estimate at the thin exponential rate on a family of translates requires further information. In particular, (4) concerns a physical norm cutoff. A finite-place cutoff dropping the first-power shells produces an additional arithmetic term. At a known rational central ordinate that extra term can carry the entire nonzero Abel coefficient in mrshu's test, even though (2) cancels the common central contribution exactly. [First-power prime-shell obstruction and scale](https://github.com/mccorvie/riemann-masullo/issues/7353#issuecomment-7153167593)

The project identifies $\Theta_\eta$ with the common kernel of the retained jets and constructs a packet with one prescribed jet equal to one and all other retained jets zero. On identical physical representatives a shared jet has exactly the same Haar moment. It follows that $K=0$ if and only if every jet retained at the wide width is retained at the narrow width. For the reverse direction take the wide single-jet packet for any missing jet. It lies in $\Theta_\alpha$ after inclusion and its wide class is nonzero. An interior jet at the narrow width always survives at the wider one. At a narrow boundary the surviving derivative orders obey $2k+1<s$, and an individual missing high order there contributes to $K$. These facts keep boundary-order loss separate from the exterior-zero sum. [Full common-kernel theorem](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L6596) · [Single-jet interpolation](https://github.com/mccorvie/riemann-masullo/blob/72a10ffc48c00276d45acb98b24a10816b253c54/RiemannMasullo/Ch10_TraceSpectral/Sec2.lean#L3565)

## A genuine obstruction on common rational modes

Over rational $\zeta$, fix $a=1/2$, $0<\alpha<\beta$, and $s\ge0$. The dense map $J$ is **never onto**. Already for linear combinations of shared zeroth evaluations at simple critical zeros, its adjoint is arbitrarily far from bounded below. This requires no assertion about off-line zeros. Conrey proves that a positive proportion of the zeros are simple and on the critical line. The total count is asymptotic to $T\log T/(2\pi)$. Pigeonholing in unit intervals supplies $k+1$ distinct simple ordinates $\gamma_0,\ldots,\gamma_k$ in an interval of length one, for arbitrarily large $k$. [Conrey, introduction and Theorem 1](https://aimath.org/~kaur/publications/24.pdf)

On the physical log line consider the exponential divided difference
$$
 F_k(x)=k!\sum_{j=0}^{k}\frac{e^{i\gamma_j x}}
       {\prod_{\ell\ne j} i(\gamma_j-\gamma_\ell)} .
$$
This is a finite linear combination of actual common zeroth jets. If $p=(p_0,\dots,p_k)$ is uniform on the standard probability simplex and $Z=\sum p_j\gamma_j$, the Hermite–Genocchi formula gives $F_k(x)=x^k\mathbb E[e^{ixZ}]$. It follows directly as well by iterating the fundamental theorem of calculus for the divided difference, with the simplex volume $1/k!$. In particular $|F_k(x)|\le|x|^k$. The simplex moments $\mathbb E p_j=1/(k+1)$ and $\mathbb E p_jp_l=(1+\mathbf1_{j=l})/((k+1)(k+2))$ follow by integrating monomials on the simplex. Hence $\mathbb E Z=\bar\gamma$ and
$$
 \operatorname{Var} Z=\frac{\sum_j(\gamma_j-\bar\gamma)^2}{(k+1)(k+2)}
 \le \frac{1}{4(k+2)}.
$$
The last estimate is the variance bound for a probability measure supported in a unit interval. By $\cos v\ge1-v^2/2$,
$|\mathbb E e^{ixZ}|\ge1-\tfrac12 x^2\operatorname{Var}Z\ge1/2$ on $[\sqrt k,\sqrt k+1]$ for $k\ge1$.

The shared functional $\ell_k(q)=\int_G q(g)F_k(x)\,d\mu(g)$ vanishes on the genuine narrow theta space. Its norm on $Q_\alpha$ therefore equals its full ambient dual norm, with square $V\int |F_k(x)|^2/w_\alpha(x)\,dx$. The norm on $Q_\beta$ of its pullback by $J$ has exactly the same expression with $\beta$ in place of $\alpha$. Let $M=\sqrt k/2$. The preceding lower bound on $[\sqrt k,\sqrt k+1]$ gives a narrow squared norm at least
$$
 \tfrac14 V k^k e^{-2\alpha(\sqrt k+1)}
              (1+(\sqrt k+1)^2)^{-s/2}.
$$
The mass on $|x|\le M$ is at most $2 V M^{2k+1}$, so its relative contribution to the narrow squared norm is $O_{\alpha,s}(4^{-k}e^{O_{\alpha,s}(\sqrt k)}k^{O_s(1)})$. Beyond $M$ the wide inverse weight is at most $e^{-(\beta-\alpha)\sqrt k}$ times the narrow one. Since $w_\beta^{-1}\le w_\alpha^{-1}$ everywhere, these two estimates give, for some $c_{\alpha,\beta}>0$ and all sufficiently large $k$,
$$
 \frac{\|J^*\ell_k\|}{\|\ell_k\|}\le e^{-c_{\alpha,\beta}\sqrt k}. \tag{5}
$$
Here $J^*$ denotes the pullback on the continuous dual, equivalently the Hilbert adjoint up to the Riesz identification. A surjective bounded operator between Hilbert spaces has adjoint bounded below by the open mapping theorem. This contradicts (5). The argument also works at $\alpha=0$ if $s>1$, when the critical zeroth jets are continuous.

Thus the common modes in (2) cancel in trace without a uniformly bounded inverse on them. Equations (3)–(5) show why an operator-norm bound for the physical cutoff error alone, multiplied by a putative uniform inverse constant, cannot justify that cancellation before exhaustion. A signed bound coupling the cutoff leakage to its singular directions, or direct control of the invariant defect action in (2), remains possible.

## Finite physical cutoffs admit an exact bounded cross-width factorization

There is a way to remove the regularized inverse in (3) **before** physical exhaustion. Suppose $m$ is bounded by one and supported in $|\log|g||\le L$. Multiplication by $m$ now strengthens the width, giving a bounded $\widetilde M:W_\alpha\to W_\beta$ with $\|\widetilde M\|\le e^{(\beta-\alpha)L}$. This follows from $w_\beta/w_\alpha=e^{2(\beta-\alpha)|x|}$ on the common physical model. The exact identities are $i\widetilde M=M_m$ on $W_\alpha$ and $\widetilde M i=M_m$ on $W_\beta$.

Use a single-character translated convolution with $H\in C^\infty_c(\mathbb R)$ and matching class-Haar normalization at both widths. The mixed operator $\widetilde M A_\alpha:W_\alpha\to W_\beta$ is nuclear for every fixed $L,R$. To verify this, conjugate both spaces to Haar coordinates. The angular factor has rank one. The radial kernel is $m(x)H(x-t-R)\sqrt{w_\beta(x)/w_\alpha(t)}$ up to the fixed Haar scalar. Only finitely many unit input and output rectangles occur since both $m$ and $H$ have bounded log support. On each rectangle the smooth factor $H(x-t-R)$ has an absolutely summable separated Fourier series after smooth extension. The two square-root weights and the bounded measurable $m$ stay with their respective factors. This is an explicit nuclear expansion. The finite statement holds over every number field for a single normalized angular character, and for bounded masks without differentiability assumptions. [Detailed unit-cell expansion](https://github.com/mlyle/riemann-masullo/blob/5978f01f22d8eff88a4c931a380b8c7a7ba734f2/research/rational-physical-cutoff-saving.md)

Set $B=q_\beta\widetilde M A_\alpha l_\alpha:Q_\alpha\to Q_\beta$, which is nuclear. Then $X_\alpha=JB$ and $X_\beta=q_\beta\widetilde M A_\alpha i l_\beta$. Moving the bounded $J$ across this mixed nuclear operator gives the exact signed identity
$$
 \boxed{\quad\operatorname{Tr}X_\beta-\operatorname{Tr}X_\alpha
   = \operatorname{Tr}_{Q_\beta}
        \left(q_\beta\widetilde M A_\alpha
               (1-P_\alpha)i l_\beta\right).\quad} \tag{6}
$$
Indeed the right side is the trace of $X_\beta-BJ$, since $l_\alpha J=P_\alpha i l_\beta$. The ordered physical trace at either width equals the trace of $X_\eta$ by its diagonal orthogonal block. Equation (6) contains no inverse of $J$. It combines the kernel term and the cutoff leakage of (3) into one physical operator. A lifted wide *spectral* packet is restricted and its *narrow geometric theta* component is isolated. Convolution keeps this component in the narrow theta space. Physical truncation cuts it off in the stronger norm, after which the wide quotient measures what survives. This describes exactly where cancellation can enter. Estimating its signed trace at the fixed thin exponent, with the required order of exhaustion in $L$ and translation in $R$, remains open. The factor $e^{(\beta-\alpha)L}$ explains why the fixed-cutoff factorization alone gives no uniform estimate when removing the physical cutoff.
