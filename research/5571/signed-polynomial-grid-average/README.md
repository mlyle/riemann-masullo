# One signed average on a sparse grid suffices for rational zero exclusion

Fix \(1/2\le\sigma<1\), \(b>1\), \(n_k=\lfloor k^b\rfloor\), and either of the two exact two-cosine rational first-prime errors \(E(n)\). The integral-compensated version is
\[
 E(n)=\sum_{p\le n}\log p\,[2-\cos(\log p)-\cos(\sqrt2\log p)]
       -\int_1^n[2-\cos(\log t)-\cos(\sqrt2\log t)]\,dt.
\]
If for every \(\sigma<r<1\) one has
\[
 \left|\sum_{k=1}^{K} E(n_k)\right|\le C_r K^{1+br}
 \qquad\text{for every sufficiently large positive integer }K ,
\]
then \(\zeta(s)\ne0\) for \(\Re s>\sigma\), and the actual rational principal completed divisor is nonpositive there. This concerns the signed sum: there is no absolute value on the individual \(E(n_k)\). Constants may depend on \(b,\sigma,r\); both thresholds and constants are uniform over \(K\). Checking only the distinct dyadic \(K=2^j\) would not justify the following subtractions.

## Persistence of a large arithmetic excursion

Let \(\Theta\) be the supremum of real parts of all nontrivial rational zeta zeros. Euler convergence gives \(\Theta\le1\). Suppose \(\Theta>\sigma\), and put \(v=(\sigma+\Theta)/2\), \(d=1/b\), \(d_v=3(1-v)/(2-v)<1\). Choose a fixed number
\[
 0<\alpha<\min\{d,1/4,(\Theta-\sigma)/4\}.
\]
The common-height truncated explicit formula and Ingham's zero-density theorem yield, for every sufficiently large \(X\), uniformly in \(X\le y\le X+X^{1-\alpha}\),
\[
 |E(y)-E(X)|\ll
 X^\eta\log^5(2X),\qquad
 \eta=\max\{v,\Theta-\alpha(1-d_v)\}<\Theta .
\]
The proof applies also when \(\Theta=1\): for the high zeros it only uses \(\beta\le\Theta\) and \(d_v<1\). The theorem for the inclusive prime-power count is valid at all real endpoints. Removing composite powers and partially summing the trigonometric weight preserve the displayed exponent. For the discrete compensator at integer arguments the difference between means contributes \(O(\log(2X))\). [Full derivation with both endpoint conventions](https://github.com/mlyle/riemann-masullo/tree/d244706da56d1c76931abb295f67bef2396ec7c3/research/5571/polynomial-grid-zero-density) · [Ingham's density bound](https://doi.org/10.1093/qmath/os-11.1.201) · [Cully-Hugill and Johnston, Theorem 1.2](https://arxiv.org/pdf/2111.10001).

Choose a fixed \(t\) with \(\max\{\eta,\sigma+\alpha\}<t<\Theta\). There are arbitrarily large integers \(X\) with \(|E(X)|>X^t\). Otherwise the full-cutoff rational criterion at \(t\) would exclude all zeta zeros with real part greater than \(t\), contradicting the definition of \(\Theta\). On each such interval, for all large enough \(X\), every integer sample value \(E(n_k)\) with \(X<n_k\le X+X^{1-\alpha}\) has the sign of \(E(X)\) and magnitude at least \(X^t/2\). There is no assumption of a dominant zero, a zero at \(\Theta\), or a pre-existing zero-free vertical strip. [Verified all-cutoff rational detection theorem](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521).

## Two signed prefix values

The sample indices in that interval form a consecutive block of length \(B\asymp_b X^{d-\alpha}\). Indeed for real \(u\) the number of indices \(\lfloor k^b\rfloor\le u\) is \(u^d+O_b(1)\), and \((X+X^{1-\alpha})^d-X^d\sim dX^{d-\alpha}\). The sign and magnitude bounds imply that the absolute sum of errors *with their signs retained inside the sum* over this block is at least \(BX^t/2\). Its initial and final index are both \(O_b(X^d)\). Subtracting two signed prefixes at these endpoints bounds the absolute block sum by \(O_r(X^{d+r})\), for every fixed \(\sigma<r<1\). Choose \(r\in(\sigma,t-\alpha)\). The required lower bound is \(\gg X^{d-\alpha+t}\), a contradiction. Thus \(\Theta\le\sigma\). As in the full-grid note, the rational completed and ordinary comparison gives the divisor conclusion. Equivalently the full explicit formula with \(\Theta\le\sigma\) restores \(|E(x)|=O(x^\sigma\log^2(2x))\), and one may apply the checked full-cutoff theorem directly.

It also suffices that the same signed prefix bounds hold at every \(K=\lfloor j^c\rfloor\) for any *fixed* \(c>1\). In the argument decrease \(\alpha\) further so that \(\alpha<d/c\). The gaps between those tested prefix indices near \(X^d\) are \(O_{b,c}(X^{d-d/c})=o(B)\). Within the stable-sign block choose a tested prefix index near each end; the retained intervening block still contains \(\gg B\) terms of the same sign. The sample values between tested prefix indices need no individual bound.

## Fixed higher signed partial sums

For a fixed positive integer \(m\), let \(a_k=E(n_k)\), extended by zero for \(k\le0\), and set \(A_0(K)=a_K\), \(A_j(K)=\sum_{1\le k\le K}A_{j-1}(k)\) for \(1\le j\le m\). It suffices that \(|A_m(K)|\ll_r K^{m+br}\) for every \(\sigma<r<1\) and every large \(K\). In this extension the assumption is for all \(K\). Let the operator be \(\Delta_L F(K)=F(K+L)-F(K)\). Then
\[
 \Delta_L^m A_m(K)=\sum_{1\le j_1,\ldots,j_m\le L}
                         a_{K+j_1+\cdots+j_m}.
\]
Choose \(\alpha<(\Theta-\sigma)/(4m)\) as well as before, take \(L=\lfloor B/(2m)\rfloor\), and position the difference inside the stable-sign block. Its magnitude is at least \(L^m X^t/2\) for a choice \(\max(\eta,\sigma+m\alpha)<t<\Theta\). The assumed growth at the \(m+1\) prefix arguments gives \(O_r(X^{md+r})\), contradicting \(X^{m(d-\alpha)+t}\) when \(\sigma<r<t-m\alpha\). For \(m>1\) only the higher signed partial sum is constrained.

All assertions on this page are classical consequences of the cited actual-statistic detector and zero-density estimates. No signed sample-average bound in the interior exponent strip is proved here. The remaining arithmetic objective is to establish such a bound, even for one fixed choice of \(b,m,\sigma\).
