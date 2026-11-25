# A rational test separating the real orbital integral from a norm-window trace

Work over the rationals with the trivial character. Write $x=\log |g|$ and take the radial idèle-class test $\varphi(g)=H(x)$. Smooth compact profiles on the real line give genuine compact Bruhat tests by the norm-section construction. We use the real orbital sign of (12.5.1.1) on manuscript pp. 519–520 and the Fourier convention $\widehat H(t)=\int_{\mathbb R}H(x)e^{-itx}\,dx$. [Bruhat lift](../RiemannMasullo/Ch12_TraceGeometric/Sec5_PositiveEdgeProbes.lean) · [Manuscript](../transcription/chapters/chapter-12.md) · [Real Haar normalization](../RiemannMasullo/Ch01_Introduction/Sec4.lean#L2098)

## The trace of a norm-window compression

In the log-coordinate regular representation on $L^2(\mathbb R,dx)$, integrated scaling acts by $A_H f=H*f$. This is also the even real scaling representation in logarithmic half-density coordinates. Reversing translation conventions changes $H(x)$ to $H(-x)$, which agrees with $H$ for our even test. For any bounded interval $I$, let $P_I f=1_I f$. The following identity holds for every smooth compact $H$.

$$
 \operatorname{Tr}(P_I A_H P_I)=|I|H(0).
$$

Indeed set $e_{I,t}(x)=1_I(x)e^{itx}$. Fourier inversion writes the compression as

$$
 (2\pi)^{-1}\int_{\mathbb R}\widehat H(t)\,|e_{I,t}\rangle\langle e_{I,t}|\,dt.
$$

The integral converges in trace norm since $\widehat H$ is Schwartz and the rank-one trace norm is $|I|$. Taking the trace gives the identity with its constant. All nested differences of these traces vanish when $H(0)=0$.

## A prime-free shell with zero polar terms

Choose a nonzero real even smooth $\psi\ge0$ of compact support inside $6/5<e^{|x|}<4/3$. For example, add a nonnegative smooth bump in $(\log(6/5),\log(4/3))$ to its reflection. Define

$$
 H=\psi''-\tfrac14\psi .
$$

Every derivative has support in the same compact set. Thus $H(0)=0$ and every $P_I A_H P_I$ has trace zero. For either $a=\pm1/2$, two integrations by parts give $\int H(x)e^{ax}\,dx=(a^2-1/4)\int\psi(x)e^{ax}\,dx=0$. The two adelic polar Mellin moments have the same positive compact norm-one volume factor, so both vanish. At any finite rational prime $p$, a local unit has log norm zero, and a nonunit has $e^{|x|}\ge p\ge2$. The local pullback of the test vanishes identically at every finite place.

The real Connes–Weil principal value is an ordinary integral for a test vanishing at one. Its normalization here is

$$
 W_{\mathbb R}(H)=\tfrac12\int_{\mathbb R^\times}
   H(\log |u|)\frac{\sqrt{|u|}}{|1-u|}\frac{du}{|u|}
   =\int_{\mathbb R}H(x)J(x)\,dx .
$$

The substitutions $u=\pm e^x$ give, for $x\ne0$,

$$
 J(x)=\tfrac14\big(1/|\sinh(x/2)|+1/\cosh(x/2)\big)
     =\frac{e^{-|x|/2}}{1-e^{-2|x|}}
     =\sum_{k=0}^{\infty}e^{-(2k+1/2)|x|}.
$$

The series and its first two derivatives converge uniformly on both compact shell components. By integration by parts on them,

$$
 W_{\mathbb R}(H)
 =\int\psi(x)(J''(x)-J(x)/4)\,dx
 \ \ge\ 6\int\psi(x)e^{-5|x|/2}\,dx>0 .
$$

Here the $k=0$ coefficient vanishes, the $k=1$ coefficient is $6$, and all subsequent coefficients are positive. Equivalently, with $r=|x|>0$, the exact density is $e^{-5r/2}(6+2e^{-2r})/(1-e^{-2r})^3$. This is the entire normalized local sum for this test, and both polar corrections vanish. The computations depend only on the local formula and Mellin integration. [Project principal value at one](../RiemannMasullo/AppB_AnalyticNT/Sec4b.lean#L6829) · [Finite-place normalization](../transcription/chapters/chapter-12.md)

## Ordering and passage to a limit

For orthogonal projections $P\le Q$ on one Hilbert space and trace-class compressions of a self-adjoint $A$, block decomposition gives

$$
 \operatorname{Tr}(QAQ)-\operatorname{Tr}(PAP)=\operatorname{Tr}((Q-P)A(Q-P)).
$$

If $A\ge0$ the right side is nonnegative. With $P$ representing the open-width terms and $Q$ the closed-width terms, the required signed comparison $-\operatorname{Tr}_{\rm open}\le-\operatorname{Tr}_{\rm closed}+\varepsilon$ instead asks for an **upper** bound $\operatorname{Tr}_{\rm closed}-\operatorname{Tr}_{\rm open}\le\varepsilon$. The variable-width project uses different weighted Hilbert norms, so an identification of its actual quotient traces with a common pair of orthogonal compressions would itself require proof. [Project comparison with signs](../RiemannMasullo/Ch12_TraceGeometric/Sec5_AdmissibleEdgeProbes.lean#L460) · [Interval Sobolev density](../RiemannMasullo/Ch09_HardySobolev/Sec2.lean#L3069)

For the shell test above the trace norms of the compressions grow at least linearly. The bounded self-adjoint convolution $A_H$ is nonzero because $W_{\mathbb R}(H)>0$ implies $H\ne0$, and its Fourier transform is nonzero by inversion. By polarization and density choose a compactly supported unit vector $v$ with $c=|\langle A_H v,v\rangle|>0$, supported on an interval of length $d>0$. Inside $I$ pack $\lfloor|I|/d\rfloor$ disjoint translated copies $v_j$. Translation invariance gives each absolute diagonal entry $c$, hence

$$
 c\lfloor |I|/d\rfloor\le\|P_I A_H P_I\|_1
 \le |I|(2\pi)^{-1}\int |\widehat H(t)|\,dt .
$$

Consequently zero scalar traces here coexist with linear trace-norm growth. Even when trace norms are bounded, a strongly moving rank-one example has constant unit trace and strong limit zero. An ordinary trace-limit argument would therefore need trace-norm convergence or some independently established tail condition or relative-trace identity.

## The Sonin compression

Connes and Consani, Theorem 4.7, p. 27, equation (83), identify the trace on the Sonin space with $W_\infty(f)+\int f(\rho^{-1})\epsilon(\rho)d^\times\rho$, where $W_\infty=-W_{\mathbb R}$ in their convention. Their Theorem 1, p. 3, gives a lower bound on $W_\infty(g*g^*)$ for $g$ supported in $[2^{-1/2},2^{1/2}]$ with the two specified transform zeros. On the multiplicative group, $(g*g^*)(1)=\|g\|_2^2$, so a norm-one-vanishing test in that square class must be zero. Applying their inequality separately to two squares gives no order on the difference of their two remainders. [Connes and Consani, primary paper](https://arxiv.org/pdf/2006.13771)

This computation rules out identifying the bare rational log-position window trace with the normalized local functional on admissible polar-free profiles, even on a shell avoiding every finite prime. It leaves the all-width edge comparison open. A phase-space projection, a relative trace with a remainder, or a cancellation specific to the spectral quotient would require its own comparison with the normalized local term.
