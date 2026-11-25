# A power-saving signed estimate on actual first primes, and the cube-sized obstruction

Use the fixed weight \(w(\log x)=2-\cos(\log x)-\cos(\sqrt2\log x)\). Write \(S=\{0,\pm1,\pm\sqrt2\}\), \(c_0=2,\ c_t=-1/2\ (t\ne0)\). As in the preceding notes, \(E(X)=\sum_{p\le X}\log p\,w(\log p)-\int_1^Xw(\log x)dx\), \(B(X)=\int_1^{\sqrt X} E(u^2)\,du\), \(A(k)=\sum_{j\le k}E(j^2)\), and \(A_d(k)\) denotes the integer-compensated version. Set \(F(u)=A(\lfloor e^{u/2}\rfloor)/\lfloor e^{u/2}\rfloor^2\) for \(u\ge0\), zero for \(u<0\), with the identical convention for \(A_d\) or \(B(e^u)/e^u\).

There is an explicit positive probability density \(H\), fixed independently of every scale and every zero location, such that for **both actual physical prefixes** and all \(Y\to\infty\),
\[
 \int_{\mathbb R}H(v)F(\log Y+v)\,dv
      = -1+O_H\big(Y^{-1/6}\log^{11/2}(2Y)\big).
\]
For the continuous Riesz sum over the **same first primes**, set \(m=\widehat H(-1/6)>0\). At every sufficiently large \(Y\),
\[
 -1-\tfrac32 mY^{-1/6}
 < \int H(v)\frac{B(Ye^v)}{Ye^v}\,dv
 < -1-\tfrac9{10}mY^{-1/6}.
\]
This second inequality gives the sign and the order of the first surviving correction. No zero-free hypothesis is used. The stronger square-root discrepancy estimate proved in the final section gives these same strict inequalities for both physical prefixes.

## Exact positive weight and its cost

Write \(Q(z)=\xi(1/2+z)\) and
\[
 D_a(z)=Q(z)\prod_{t=1,\sqrt2}Q(z+iat)Q(z-iat).
\]
Take the bilateral transform of \(H\) proportional to
\[
 D_1(z)\,D_1(z+1/2)\,D_2(2z+1/2)\,\widehat U_1(z)\widehat U_{\sqrt2}(z),
\]
normalizing at zero. Here \(U_t\) is the uniform probability on \([-\pi/t,\pi/t]\). No summation or choice over zeros defines this observable. The second copy of \(D_1\) compensates for dividing a physical floor cell by \(k^2\); the dilated \(D_2\) treats the genuine prime-square component. The two uniforms remove the four nonconstant frequencies of the square drift. The density weights integer \(k\) by the positive \(H\)-mass of \([2\log k-\log Y,\,2\log(k+1)-\log Y)\).

To check positivity at the larger shifts, let \(\Phi\) be [Romik's even theta density, (1.8)–(1.11)](https://arxiv.org/pdf/1902.06330), and put
\[
 r_1(u)=e^{9|u|/2-\pi e^{2|u|}}\big(1-\tfrac7{15} e^{-2|u|}\big).
\]
Then uniformly
\[
 .975\,r_1(u)\le \Phi(u)/(4\pi^2)\le1.02\,r_1(u).
\]
Indeed the first summand in \(\Phi\), after removing the leading exponential, is \(1-(3/2\pi)e^{-2|u|}\). The inequalities \(25/8<\pi<22/7\) give \(7/15<3/(2\pi)<12/25\). The smallest possible ratio for the first term occurs at zero and is at least \((1-12/25)/(1-7/15)=.975\). The other terms cost \(<.01/(1-7/15)<.02\) by the [geometric theta tail estimate](../square-prefix-theta-annihilator/README.md#the-two-shifted-theta-factors-have-a-positive-inverse-transform).

On \(u>0\), \((\log r_1)''\le-4\pi\): the additional logarithm has second derivative \(-4c'e^{-2u}/(1-c'e^{-2u})^2<0,\ c'=7/15\). The derivative on the right at zero equals \(25/4-2\pi<0\), so the even extension retains this strong concavity in the sense that \(\log r_1+2\pi u^2\) is concave on \(\mathbb R\). As in the linked proof, the \(h\)-variance under the probability proportional to \(\Phi(v/2+h)\Phi(v/2-h)\) is at most \((1.02/.975)^2/(8\pi)<.044\). Therefore the physical inverse of \(Q(z+it)Q(z-it)\), given by that unnormalized integral times \(\cos(2th)\) in its integrand, lies between \((1-16\cdot.044)(\Phi*\Phi)\) and \(\Phi*\Phi\) for every \(t^2\le8\). This includes all shifts used here. The positive inverse of \(D_1(z+1/2)\) is the inverse of \(D_1(z)\) multiplied by \(e^{v/2}\); the inverse of \(D_2(2z+1/2)\) is \(e^{v/4}/2\) times the inverse of \(D_2\) at \(v/2\).

All central quantile widths of \(H\) are fixed in the variable \(\log X\). There are constants \(c,C>0\) such that
\[
 H(v)+|H'(v)|\ll e^{-c e^{|v|/10}},\qquad H(v)\gg e^{-C e^{|v|/10}}.
\]
For the upper bound the three convolutions have five theta factors each, with scales \(1,1,2\) in their groups. In any representation of a sum at \(v\) one unscaled variable has modulus at least \((|v|-O(1))/20\). The linear exponential tilts are absorbed in the individual theta bounds, including their \(L^1\) norms. For the lower bound restrict the unscaled variables to fixed-width boxes around \(v/20\), using their bounded scale factors; the remaining variable is within bounded distance of this center. The pair lower comparisons above justify this argument for the physical convolutions. Differentiating one final box gives two translates of the remaining convolution, which obeys the same upper bound. As \(|F(\log Y+v)|\ll Y^{1/2}e^{|v|/2}\), discarding \(|v|>10\log\log Y+C_0\) costs \(O(Y^{-1})\) for \(C_0\) sufficiently large. Thus the integer square indices needed at this precision are within a factor \(C_1(\log Y)^5\) of \(\sqrt Y\); the infinite positive average is fixed.

## Prime and prime-power terms

Let \(\rho\) run over all nontrivial zeta zeros with multiplicities. The [unconditional weighted Riesz formula](../signed-riesz-margin/README.md#exact-weighted-riesz-formula) at exponent \(1/2\) applies to the full von Mangoldt sum. To remove prime squares insert the same formula at exponent \(1\), argument \(\sqrt X\), and frequency \(2t\). Replacing actual primes in this square correction by all von Mangoldt weights costs \(O(X^{3/4})\) before dividing by \(X\), using Chebyshev's bound on composite-power mass at \(\sqrt X\). All prime powers of exponent at least four cost \(O(X^{3/4}\log(2X))\) before division. The lower integration limit and the fixed kernel and trivial-zero residues from the two formulas contribute \(O(X^{-1/2})\) after division. Consequently
\[
\begin{split}
 B(X)/X={}&-\tfrac12\sum_{t\in S}c_t\sum_\rho
 \frac{X^{\rho-1/2+it}}{(\rho+it)(\rho+1/2+it)}
 -\sum_{t\in S}\frac{c_t X^{it}}{(1+2it)(2+2it)}\\
 &+\sum_{t\in S}c_t\sum_\rho
 \frac{X^{(\rho-1)/2+it}}{(\rho+2it)(\rho+1+2it)}
 -C_3(X)/X + O(X^{-1/4}\log(2X)),
\end{split}
\]
where \(C_3(X)=\sum_{p^3\le X}(\log p)w(3\log p)(\sqrt X-p^{3/2})\). The displayed zero sums have absolutely summable coefficients. Convolution with \(H\) kills the first and third terms exactly by \(D_1(z)\) and \(D_2(2z+1/2)\). The second term contributes exactly \(-1\). Using the spectral formula only for \(X\ge2\) causes super-exponentially small tails as \(\log Y\to\infty\), by its finite absolute coefficient masses and \(|\Re(\rho)|\le1\).

By ordinary PNT and partial summation at the five fixed frequencies,
\[
 \frac{C_3(X)}{X^{5/6}}=\sum_{t\in S}
 c_t X^{it} \frac{3/2}{(1+3it)(5/2+3it)}+o(1).
\]
One can first replace \(d\vartheta(p)\) by \(dp\) by integrating by parts against the bounded rescaled weight on \(p\le X^{1/3}\); on \(p\le\epsilon X^{1/3}\) the error costs \(O(\epsilon)\) after normalization by Chebyshev, and on the remainder the derivatives are uniformly bounded after rescaling. The elementary integral gives the displayed coefficient. The limit error is uniformly bounded, so dominated convergence with measure \(e^{-v/6}H(v)\,dv\) preserves \(o(1)\). The constant is \(6/5\). The sum of the two nonconstant real amplitudes is less than \(1/4\): their denominators have modulus greater than \((3t)^2\) for \(t=1,\sqrt2\), and each conjugate pair's two weights have total absolute value one. Since \(|\widehat H(-1/6+it)|\le m\), the averaged coefficient lies between \(19m/20\) and \(29m/20\), up to \(o(1)\). This proves the strict two-sided inequality and shows that the exponent \(1/6\) is sharp around \(-1\) for the continuous prime probe.

## Integer square cells, including the actual denominator

For \(X=(k+s)^2,\ k=\lfloor\sqrt X\rfloor,\ 0\le s<1,\ k\ge2\), the exact square identity and Zhai's Proposition 3.4 give
\[
 A(k)=B(k^2)+\tfrac12 E(k^2)+O(k^{5/3}\log^{11/2}(2k)).
\]
The centered prime saw is the only non-elementary term in this comparison. The integer rather than integral compensator costs another \(O(k\log(2k))\). Within a square cell the trivial integer count bounds \(E((k+s)^2)-E(k^2)\) by \(O(k\log(2k))\), and Chebyshev gives \(E(X)=O(X), B(X)=O(X^{3/2})\). Hence \(B(X)-B(k^2)=sE(X)+O(k\log(2k))\) and \(k^{-2}=X^{-1}+2sX^{-3/2}+O(X^{-2})\). Combining yields
\[
 \frac{A(k)}{k^2}=\frac{B(X)}X+\frac{B(X)}{X^{3/2}}
 +(s-\tfrac12)\left(\frac{2B(X)}{X^{3/2}}-\frac{E(X)}X\right)
 +O(X^{-1/6}\log^{11/2}(2X)).
\]
The same expansion holds for \(A_d\). [Exact centered identity](https://github.com/mccorvie/riemann-masullo/pull/7592) · [Zhai, Proposition 3.4](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1274-27.pdf) · [Weighted saw discrepancy derivation](../sparse-prime-cutoffs/README.md).

The mean-zero \(s-1/2\) term costs \(O_H((1+\log Y)Y^{-1/2})\) after averaging. In \(u=\sqrt X\), its coefficient in parentheses is bounded and varies by \(O(\log(2k)/k)\) on \([k,k+1]\) by the same elementary estimates. The integration weight is \(2H(2\log u-\log Y)/u\). Subtract the constant cell value of the product of these two functions. The per-cell bound is \(\ll \log(2k)k^{-2}\) times the supremum of \(|H|+|H'|\) over the translated cell. Replacing that supremum by its supremum on arguments within two units of \(2\log u-\log Y\) leaves double-exponential decay. Summation and \(v=2\log u-\log Y\) give the stated bound. The integrated absolute Zhai error is \(O_H(Y^{-1/6}\log^{11/2}(2Y))\) by the finite exponential moments.

For the remaining \(B(X)/X^{3/2}\), multiply the displayed Riesz formula by \(X^{-1/2}\). The first sum shifts to \(\rho-1+it\); it is annihilated by \(D_1(z+1/2)\). All other terms are \(O(X^{-1/2})\), since the square-zero exponents have nonpositive real part. This finishes the signed bound for the original floor-normalized physical observable.

## Comparison with direct PNT and with sign counts

Using PNT only as an absolute pointwise bound on \(E\) before integration would give at best \(O_H(Y^{1/2}\exp(-c(\log Y)^{3/5}/(\log\log Y)^{1/5}))\) via the classical Vinogradov–Korobov error. PNT applied to squares after the first-degree spectral cancellation still supplies only a subpower remainder by that argument. The new fixed filter removes the first-degree, square-degree, and denominator-shifted zero contributions exactly; Zhai's classical \(5/6\) saw estimate and the ordinary PNT for cubes control the arithmetic remainder. The cube coefficient and the factor \(\log^{11/2}Y\) specify why the sharper negative correction is proved for \(B\) but not for its literal square prefix by these estimates. This does not assert optimality of the available prime discrepancy methods.

The power saving is signed. If an exterior zero exists, write \(b_*=\sup_\rho\Re\rho-1/2>0\). Both positive and negative \(H\)-masses have exact exponential rate \(b_*\) in \(\log Y\) at every large center, by the [isolated-term kernels](../square-prefix-theta-annihilator/README.md#isolating-one-exterior-zero-and-forcing-both-signs-in-the-same-window). Indeed each fixed complex selector there decays like \(\exp(-c e^{2|v|/5})\), so the lower bound on the new \(H\) dominates its absolute value globally up to a constant. The isolated correlation gives the lower rate for total variation; the signed bound above splits it between the parts. The ordinary absolute Riesz envelope gives the matching upper rate. Thus a positive-part saving for this observable would need information beyond the signed cancellation just proved.

These are classical paper derivations. [PR 7612](https://github.com/mccorvie/riemann-masullo/pull/7612) certifies the original theta-pair positivity through \(t^2\le2\). The refined-envelope bound through \(t^2\le8\), the explicit formula manipulations and the physical power-saving statements on this page have not been formalized.

## The exact signed correction measured on primes

One can isolate the entire logarithmic uncertainty on the literal samples. Let \(k=\lfloor\sqrt{Ye^v}\rfloor\) in the weight below (take zero for \(k<1\)), and define a second physical measurement
\[
 S_H(Y)=\int H(v)k^{-2}
    \sum_{p\le k^2}\log(p)\,w(\log p)\big(\tfrac12-\{\sqrt p\}\big)\,dv .
\]
The saw here has exactly the indicated sign: for every prime \(p\), its square root is nonintegral, so \(\lceil\sqrt p\rceil-\sqrt p-1/2=1/2-\{\sqrt p\}\). The continuous mean's centered saw costs \(O(k)\) before division, by its bounded primitive in the variable \(\sqrt x\) and partial summation. In the square-cell expansion one can therefore **retain** the prime sum instead of appealing to Zhai, with all remaining floor errors bounded by \(O(k^{-1}\log(2k))\) after normalization. The other terms have the same cellwise cancellation and shifted spectral annihilation proved above. Hence for either compensator,
\[
 \int H(v)F(\log Y+v)dv + S_H(Y)
 = \int H(v)B(Ye^v)/(Ye^v)\,dv + O_H(Y^{-1/2}\log(2Y)).
\]
In particular the sum of these two independently defined first-prime measurements lies strictly between \(-1-\tfrac32mY^{-1/6}\) and \(-1-\tfrac9{10}mY^{-1/6}\) for all sufficiently large \(Y\), using the slack in the cube coefficient. Thus to erase the negative cube drift in the literal prefix average, the centered prime saw must itself be **negative** with magnitude at least \((9/10)mY^{-1/6}\) there. The available \(O_H(Y^{-1/6}\log^{11/2}(2Y))\) discrepancy estimate allows that sign and magnitude.

## A prime-cube lower bound requiring only Chebyshev, before any smoothing

The cube effect has an elementary positive lower bound on the actual prime numbers, uniformly even before taking the moving average. Write \(U=X^{1/3}\), and choose \(B=\exp((3\pi/2+2\pi n)/3)\) the largest such number with \(B\le U/2\). Then \(B>e^{-2\pi/3}U/2\); on \(Be^{-\pi/3}\le p\le B\) one has \(w(3\log p)\ge1\). Also \(U^{3/2}-p^{3/2}\ge(1-2^{-3/2})U^{3/2}\). The elementary Chebyshev inequalities \(\vartheta(x)\le x\log4,\ \vartheta(x)\ge(x-1)\log2-\log(x+2)-2\sqrt{x}\log x\) show
\[
 \vartheta(B)-\vartheta(Be^{-\pi/3})
 \ge B\log2(1-2e^{-\pi/3})-o(B).
\]
All errors are uniform as \(U\to\infty\). Consequently
\[
 \liminf_{X\to\infty} C_3(X)/X^{5/6}
 \ge c_0=\tfrac12 e^{-2\pi/3}(1-2^{-3/2})\log2\,(1-2e^{-\pi/3})>0.
\]
This uses only Chebyshev bounds and fixed-phase positivity. The stronger explicit cube-coefficient interval for the continuous prime probe uses the ordinary PNT. The finite-sum lower bound and the rational coefficient \(1/200<c_0\) are now verified in [upstream PR 7622](https://github.com/mccorvie/riemann-masullo/pull/7622). The module and full build, lint, 14,842 unchanged declaration signatures, five standard-only axiom checks, a separate consumer of the literal finite-sum inequality and the [hosted Verdict](https://github.com/mccorvie/riemann-masullo/actions/runs/45554589041/job/139003466634) all passed. [Mathlib's native Chebyshev bounds](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Chebyshev.html).


## The physical prime saw is smaller than the cube correction

For either literal square prefix and every fixed \(\varepsilon>0\), the stronger unconditional signed estimate is
\[
 \int_{\mathbb R}H(v)F(\log Y+v)\,dv
 =-1-\int_{\{Ye^v\ge1\}}H(v)\frac{C_3(Ye^v)}{Ye^v}\,dv
       +O_{H,\varepsilon}(Y^{-1/5+\varepsilon}).
\]
Thus the physical observable itself satisfies the strict bounds
\[
 -1-\tfrac32 mY^{-1/6}
 <\int H(v)F(\log Y+v)\,dv
 <-1-\tfrac9{10}mY^{-1/6}
\]
for every sufficiently large \(Y\), with the *same* fixed \(H\) and \(m=\widehat H(-1/6)>0\). The saving on the centered prime saw has a positive exponent margin of \(1/30\) over the cube. This is a signed average across indices. The separate positive and negative variation estimates in this note continue to apply.

**Prime discrepancy input.** For \(N\ge2\), \(N/2\le U\le N\) and \(H_0=\lfloor N^{1/5}/4\rfloor\), write \(V_h=\sum_{N/2<p\le U}e(h\sqrt p)\), \(e(x)=e^{2\pi i x}\). The proof of Gritsenko’s Theorem 2 gives, uniformly,
\[
 \sum_{h=1}^{H_0}\frac{|V_h|}{h}\ll_\varepsilon N^{4/5+\varepsilon}.
\]
His stated theorem counts primes in the intervals \([(2n)^2,(2n+1)^2)\). The estimate above uses the freedom in the Fourier coefficients *in its proof*. Here are the details of that specialization. [Gritsenko, *A problem of I. M. Vinogradov*, Mat. Zametki 39 (1986), 625–640, Theorems 1–2](https://www.mathnet.ru/eng/mzm5085) · [original proof, pp. 625–640](https://www.mathnet.ru/links/e16b4615972e1d7f547a3d59d47633f0/mzm5085.pdf).

1. The phase in equations (3)–(13) is \(e^{\pi i m\sqrt n}\). Take \(\Delta=N^{-1/5}\) as in the proof of Theorem 2. Given the \(V_h\), set \(c(2h)=\overline{V_h}/(2\pi h|V_h|)\) when \(V_h\ne0\), and set all remaining coefficients to zero. The support satisfies \(m\le N^{1/5}/2\), inside \(\Delta^{-1}\log N\) for sufficiently large \(N\). The coefficients obey (4), \(|c(m)|\le1/(\pi m)\). The infinite tail in (7) is empty. Therefore the sum with these coefficients is exactly \((2\pi)^{-1}\sum |V_h|/h\).
2. Equations (8)–(13) reduce to logarithmically many blocks \(M<m\le M_1\le 2M\), with a variable upper endpoint \(N_1\in[N/2,N]\) for the prime-power sum. The nonstationary and endpoint errors use absolute values of \(c(m)\). For the stationary part, (37) retains a Dirichlet polynomial in \(m\) with these coefficients. The completion of the variable \(m\)-interval can be written as the sum over additive twists with weights \(O((1+\min(a,P-a))^{-1})\). Sum over zeros before taking the maximum over twists, which costs \(O(\log P)\) and gives one common twist. The twist in (38) preserves the coefficient magnitudes. For the \(k\)-th power in (39)–(44), the coefficient at \(r\) is bounded by \(\tau_k(r)/r\) for **every** such twist. The separated-zero large sieve and the Ingham and Huxley density estimates in (48)–(52) therefore give the same \(N^{4/5+\varepsilon}\) bound for these finitely supported coefficients. The proof treats small and large \(M\) and every partial block. Its inner prime-power bounds are uniform in \(N_1\), so partial summation removing \(\log p\) on \((N/2,U]\) has the same bound. The cost of removing proper prime powers in (8) is \(O(\sqrt N\log^2 N)\). No phase information about \(V_h\) is needed in these estimates.
3. The Erdős–Turán inequality for the points \(\{\sqrt p\}\) gives an unnormalized star discrepancy over the block bounded by a constant times \(\#\{N/2<p\le U\}/(H_0+1)+\sum |V_h|/h\). Both terms are \(O_\varepsilon(N^{4/5+\varepsilon})\). Summing dyadic blocks proves, for all \(x\ge2\),
\[
 \sup_{0\le a\le1}\left|\sum_{p\le x}
       \left(\mathbf 1_{\{\sqrt p\}<a}-a\right)\right|
       \ll_\varepsilon x^{4/5+\varepsilon}.
\]
Strict or weak endpoints within the integral below give identical results.

**Signed application.** Integrating the discrepancy in \(a\) gives exactly \(\sum_{p\le x}(1/2-\{\sqrt p\})\). With \(g(x)=\log(x)w(\log x)\), we have \(|g(x)|\le4\log x\) and \(|g'(x)|\le[4+(1+\sqrt2)\log x]/x\). Partial summation, starting with a slightly smaller value of \(\varepsilon\), proves
\[
 \left|\sum_{p\le x}\log(p)w(\log p)\big(\tfrac12-\{\sqrt p\}\big)\right|
      \ll_\varepsilon x^{4/5+\varepsilon}.
\]
For \(k=\lfloor\sqrt{Ye^v}\rfloor\ge1\), one has \(k\ge\sqrt{Ye^v}/2\). The preceding estimate divided by \(k^2\), together with the exponential moments of \(H\), gives \(S_H(Y)=O_{H,\varepsilon}(Y^{-1/5+\varepsilon})\). The exact signed square-cell formula above transfers this to both physical compensators. All the other exposed terms after subtracting the actual cubes are \(O_H(Y^{-1/4}\log(2Y)+Y^{-1/2}\log(2Y))\). For the stated numerical interval, use the two Fourier-amplitude bounds for the main cube coefficient above and take \(\varepsilon<1/30\). Even Chebyshev’s prime-cube lower bound alone gives a strictly negative correction once this saw estimate is in place, with a smaller coefficient.

The discrepancy specialization and its application here are classical paper proofs. The finite prime-cube lower bound in PR 7622 is machine checked.
