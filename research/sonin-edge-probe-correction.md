# The correction from the actual real Sonin projection on admissible edge probes

Write $x=\log |g|$ in the rational trivial chart. The even scaling representation becomes translation in $L^2(\mathbb R,dx)$ under $U f(x)=\sqrt 2 e^{x/2}f(e^x)$. We use $C_H f=H*f$, $Rf(x)=f(-x)$, and $\widehat f(t)=\int f(x)e^{-itx}\,dx$. All estimates below are mathematical derivations. The compact admissible probe and its adelic realization at center $1$ have separately passed Lean. [Native robust probe](../RiemannMasullo/Ch12_TraceGeometric/Sec5_AdmissibleEdgeProbes.lean) · [Sharp norm-window calculation](rational-log-window-compression.md)

## Reflection and the true Fourier cutoff

On smooth even compact inputs the additive Fourier transform in log coordinates has kernel $2e^{(x+y)/2}\cos(2\pi e^{x+y})$. Indeed split the ordinary Fourier integral into its positive and negative real branches and substitute $u=e^y$. Its dependence on $x+y$ forces reflection. Connes and Consani give the precise bounded operator in Lemma 1.3, equation (25). In their order of composition it is the norm inversion $R$ composed with the Mellin multiplier $e^{2i\theta(t)}$. The multiplier is unitary and nonconstant. Their actual Sonin projection uses the intersection of the two nullspaces of the position cutoff and its conjugate by this full Fourier transform. [Primary paper, pp. 7–8 and 25](https://arxiv.org/pdf/2006.13771)

For comparison, the real principal value on $H(0)=0$ has a direct scalar Hankel realization. Let $J(x)=e^{-|x|/2}/(1-e^{-2|x|})$ off zero, choose even smooth compact cutoffs $0\le\chi_j\le1$ avoiding zero and tending pointwise to $1$ off zero, and put $w_j(x)=\chi_j(x)\sqrt{2J(2x)}$. The operator $M_{w_j}C_H R M_{w_j}$ has diagonal $w_j(x)^2 H(2x)$. Its trace is the integral of that diagonal. To see trace class, use Fourier inversion for $H(x+y)$ to integrate rank-one operators with trace norms $\|w_j\|_2^2|\widehat H(t)|/(2\pi)$. Consequently the traces tend to $\int J(u)H(u)\,du$ by dominated convergence, since $H(0)=0$ and $H$ is smooth and compactly supported. If $H$ and $w_j$ are even, this is the difference of the even and odd traces of $M_{w_j}C_HM_{w_j}$. This identity recovers the scalar orbital integral directly. Identifying this operator with a Sonin compression would also require the Mellin phase and the prolate correction below.

## A polar-free test that detects the actual Sonin correction

Connes and Consani's Theorem 4.7, equations (83)–(84), gives $\mathrm{Tr}(\vartheta(f)S)=W_\infty(f)+E(f)$, with $W_\infty=-W_{\mathbb R}$ and

$$
 E(f)=\int_{\mathbb R}H(x)e(x)\,dx,\qquad e(x)=\epsilon(e^{|x|}),\quad f(\rho)=H(\log\rho)
$$

for even tests. The eigenvalue bound (71), unitarity of scaling, and the unit norms of the prolate vectors in (84) give uniform absolute convergence and boundedness of $e$. Strong continuity gives continuity. The two inner-product vectors $\xi_n,\zeta_n$ have disjoint interiors of support, so $e(0)=0$. By Lemma 5.4 and Remark 4.6(i),

$$
 a=\epsilon'(1+)=\sum_n\frac{\lambda_n^2}{1-\lambda_n^2}\xi_n(1)^2
 \ \ge\ \sum_n\lambda_n^2\xi_n(1)^2=2 .
$$

Only the inequalities $|\lambda_n|<1$ and the exact sum identity are used here. Thus $e(x)=a|x|+o(|x|)$ at zero. [Primary paper, pp. 24, 26–27 and 32–33](https://arxiv.org/pdf/2006.13771)

Choose an even compact smooth cutoff $\chi$ supported in $(-1,1)$ and equal to $1$ on $[-1/2,1/2]$. Set $\psi_\delta(x)=\chi(x/\delta)\cosh(x/2)$ and $H_\delta=\psi_\delta''-\psi_\delta/4$. The profile vanishes for $|x|<\delta/2$ and $|x|\ge\delta$. Both polar Mellin moments vanish by integration by parts. For $0<\delta<\log 2$ every finite rational orbital integral vanishes. The true Sonin remainder satisfies

$$
 \lim_{\delta\downarrow0} E(H_\delta)=2a\ \ge 4 .
$$

Indeed $\int |x|\psi_\delta''(x)\,dx=2\psi_\delta(0)=2$ by separate integrations by parts on the two half-lines, while $\int |x||\psi_\delta(x)|\,dx=O(\delta^2)$. Differentiating the cutoff gives $\int |x||H_\delta(x)|\,dx=O(1)$ uniformly for $0<\delta\le1$. The remainder $o(|x|)$ therefore contributes $o(1)$. This also follows directly from their equation (102) with $Q_+=-D^2+1/4$. Changing the sign of $H_\delta$ changes the sign of the correction. The tests and the strict lower bound use no zeta zero data.

## Opposite corrections with uniformly detectable spectral edges

Fix any $0<b<1/2$. Put $a_b(x)=e(x)/\cosh(bx)$. This continuous real even function is integrable, vanishes at zero, and has positive right derivative there. Its real Fourier transform takes both strictly positive and strictly negative values. For a proof, if $\widehat a_b$ were nonnegative, Gaussian Fourier inversion at the continuity point zero would give

$$
 (2\pi)^{-1}\int e^{-\eta t^2}\widehat a_b(t)\,dt \longrightarrow a_b(0)=0
 \qquad(\eta\downarrow0).
$$

The Gaussian identity follows from Fourier transformation of the Gaussian and Fubini against $a_b\in L^1$. Positivity and monotone convergence would imply $\widehat a_b=0$ almost everywhere. Continuity and injectivity of the $L^1$ Fourier transform then give $a_b=0$, contradicting the right derivative. Applying the argument to $-a_b$ gives both signs. By evenness and continuity the two frequencies can be chosen strictly positive.

Here is an explicit way to retain the quantitative detection property while choosing either sign. Start from the fixed real even compact smooth kernel $K$ with $K(0)>0$ and $\widehat K>0$ everywhere. Choose $M>0$, put $K_M(x)=K(Mx)$, and choose

$$
 d=K_M''(0)/K(0)-1,\qquad
 G=dK_M-K_M'',\qquad R=1+|d| .
$$

Then $G(0)=-K(0)$ and $\widehat G(t)=(d+t^2)\widehat K_M(t)>0$ for $|t|>R$. Choose any fixed $T>0$, put $u_n=1/(n+1)$, $T_n=T+u_n$, $L_n=2(R+1)/u_n$, and define at each width $v$

$$
 H_{n,v}(x)=\frac{K_M(x)+G(x/L_n)\cos(T_nx)}{\cosh(vx)}.
$$

These are real even compact smooth tests vanishing at zero. At either edge $\pm v+it$, the real part of the bilateral Laplace transform equals

$$
 \widehat K_M(t)+\tfrac12 L_n
 \left(\widehat G(L_n(t-T_n))+\widehat G(L_n(t+T_n))\right).
$$

For a fixed locally finite complex divisor, there are finitely many critical-strip ordinates with $||t|-T|\le1$. The nonzero distances from $T$ among these have positive minimum if any exist. For all sufficiently large $n$, both $|t\pm T_n|\ge u_n/2$ for every ordinate of that divisor. This includes the ordinates $\pm T$ themselves. Both extra summands above are then positive. Thus $\widehat K_M(t)=M^{-1}\widehat K(t/M)>0$ is a fixed lower bound at every critical-strip ordinate, simultaneously for every tested width. The adelic test from the project lift has the same bound times the positive norm-one class volume. The parameters $M$ and $T$ are independent of the divisor and every number field. [Native fixed-center construction and norm lift](../RiemannMasullo/Ch12_TraceGeometric/Sec5_AdmissibleEdgeProbes.lean#L255)

At the fixed rational width $b$ the actual Sonin correction has the limit

$$
 \lim_{n\to\infty}E(H_{n,b})
 =\int a_b(x)K(Mx)\,dx-K(0)\widehat a_b(T).
$$

This follows by dominated convergence from $a_b\in L^1$, $G(0)=-K(0)$ and boundedness of $G$. The integral involving $K(Mx)$ tends to zero as $M\to\infty$. Select two positive frequencies $T$ where $\widehat a_b$ has opposite signs, then fix one sufficiently large $M$ for both. The two resulting field-independent families satisfy the quantitative edge lower bound above, but their genuine archimedean Sonin corrections eventually have opposite strict signs at $b$. The selected frequencies may depend on $b$ through the known archimedean kernel, independently of zeta zeros. This last construction imposes norm-one vanishing. The preceding cutoff construction separately imposes both polar moment conditions.

The argument establishes a sign obstruction for the isolated Sonin correction, even under detection of all critical-strip ordinates. Whether the full arithmetic signed width difference meets the desired comparison remains open.
