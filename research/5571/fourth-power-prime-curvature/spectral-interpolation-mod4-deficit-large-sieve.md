# Mean square at high zeros for the actual clipped fourth-power samples

This improves the [modulo-four first-prime certificate](spectral-interpolation-mod4-deficit.md) to \(D(J)<0.173J^7\) for \(J\le5000\), \(D(J)<0.221J^7\) for \(J\le10000\), and \(D(J)<J^7\) for \(J\le44000\). The last prime cutoff is \(3{,}748{,}096{,}000{,}000{,}000{,}000\). These are unconditional bounds for the fixed primitive character of conductor four. The high-zero term costs a factor \(J^{1/2}\) less than addition of the individual Riesz error bars. The same estimate yields a smaller secondary saving for this signed statistic at arbitrarily large indices; see the last section. [Numerical check](spectral-interpolation-mod4-deficit-large-sieve.py) · [128-bit receipt](spectral-interpolation-mod4-deficit-large-sieve-128.receipt) · [192-bit receipt](spectral-interpolation-mod4-deficit-large-sieve-192.receipt).

## Treat the actual negative part

The finite identity \(D(J)=\max_{0\le c_j\le1}-\sum_{j\le J}c_j S(j^4)\) supplies the same real coefficients for every zero before taking absolute values. For the finite verification split off \(j\le1000\) using the prior \(0.173\,1000^7\) bound. In the tail calculation below allow *any* coefficients \(0\le c_j\le1\), including zero for these small \(j\). The per-sample argument replacing each triangular prime sum by its explicit formula is exact. Put \(H=25{,}000{,}000\) and use \(K_H\) and \(B\) as in the earlier certificate.

For any \(j\ge1000,\ x=j^4\), the total signed proper-power correction \(C(x)\) has absolute value at most
\[
 1.01624 x^{3/2}\{2/3+x^{-1/6}+x^{-1/4}\log_2 x\}
 <0.728167 x^{3/2}.
\]
The square-prime sum is bounded by integrating \(2u\theta(u)\) up to \(\sqrt x\). Use the Chebyshev bound individually for exponent three and for each exponent \(k\ge4\), the latter numbering at most \(\log_2x\). Both additional displayed functions decrease for \(x\ge10^{12}\). The gamma residues have absolute value below \(2j^4\le2\cdot10^{-6}j^6\), from the explicitly enclosed coefficients in the previous note. All low zeros contribute at most \(Bj^6\) and all high zeros with \(\Re\rho\le1/2\) at most \(K_H j^6\). Summing \(\sum_{j\le J}j^6\le J^7/7+J^6\), and using \(J\ge2100\), bounds the normalized subtotal by \(0.127630\). [Rosser and Schoenfeld, Theorem 9](https://doi.org/10.1215/ijm/1255631807).

## The sampled exponential sum

Let \({\cal Z}=\{\rho=\beta+i\gamma:\beta>1/2,\gamma>H\}\), including multiplicities. Both functional-equation reflection and complex conjugation are available for the actual character, so \(\sum_{{\cal Z}}\gamma^{-2}\le K_H/4\). Set \(A=H-1/2\) and \(W(v)=\log(v)/v^2\). For \(v\ge A\),
\[
 \sum_{\rho\in{\cal Z}:|\gamma-v|\le1/2}\gamma^{-2}\le0.39 W(v).
\]
Indeed the zero count remainder from Bennett et al. is at most \(0.6\log t\) for every \(t\ge H-1\), as is checked by monotonicity of \((2\log(1+u)-1/2)/u\) for \(u\ge16\). The main term has derivative \(\pi^{-1}\log(2t/\pi)\le\pi^{-1}\log t\). Counting both signs and both sides of the line incurs a factor four for the indicated right, positive ordinates. Thus their local count is at most \((\pi^{-1}+1.2)\log(v+1/2)/4\). Use \(\gamma^{-2}\le(v-1/2)^{-2}\). The spare margin in 0.39 covers both replacements at \(v\ge A\). Endpoints can be taken by one-sided limits in the counting function. [Bennett, Martin, O'Bryant and Rechnitzer, Theorem 1.1](https://arxiv.org/pdf/2005.02989).

For \(P(v)=\sum b_j e^{4iv\log(j/J)}\), write \(\nu_j=4\log(j/J)\). Averaging the fundamental theorem of calculus over \([\gamma-1/2,\gamma+1/2]\) gives
\[
 |P(\gamma)|^2\le \int_{\gamma-1/2}^{\gamma+1/2}(|P|^2+|P P'|)\,dv .
\]
In the derivative term the path lengths on each side give weights at most \(1/2\), canceling the factor two in \(|(|P|^2)'|\le2|P P'|\). For any \(z\ge A\), expand the integral of \(|P|^2\) explicitly. The diagonal gives \(z-A\) and the off-diagonal kernel satisfies \(2/|\nu_j-\nu_k|\le J/(2|j-k|)\) by the mean value theorem. Summing the absolute matrix row and column bounds, or applying \(2|b_jb_k|\le|b_j|^2+|b_k|^2\), yields
\[
 \int_A^z |P(v)|^2dv\le(z-A+J(1+\log J))\sum|b_j|^2 .
\]
Since \(W\) decreases, integration by parts gives \(\int_A^\infty W|P|^2\le V\sum|b_j|^2\), where \(V=(\log A+1)/A+J(1+\log J)\log(A)/A^2\). The same bound holds for \(P'\) with coefficient vector \(i\nu_j b_j\). Apply Cauchy–Schwarz first to the points of \({\cal Z}\) with measure \(\gamma^{-2}\) and again to the integral of \(|PP'|\). This proves
\[
 2\sum_{\cal Z}\frac{|P(\gamma)|}{\gamma^2}
 \le \sqrt{0.39 K_H V}\,
 \left[\sum|b_j|^2+\sqrt{\sum|b_j|^2\sum|\nu_j b_j|^2}\right]^{1/2}.
\]

Write \(z_j=j/J\). For a right zero put \(u=4+4\beta\in(6,8)\). Take
\(P_{a,k}(v)=\sum c_jz_j^a|\log z_j|^k e^{4iv\log z_j}\).
The exact identity \(z_j^u=z_j^8+\int_u^8 z_j^a|\log z_j|\,da\) reduces the varying abscissas to \(P_{8,0}\) and \(P_{a,1}\), \(6\le a\le8\). The integral's indicator, depending on the zero, can be discarded after taking absolute values. The outside factor \(J^{4+4\beta}\) is at most \(J^8\). With the convention \(0^0=1\), put
\[
 L_{a,k}=\frac{(2k)!}{(2a+1)^{2k+1}}
       +\frac{2}{2100}\left(\frac{k}{ae}\right)^{2k},\qquad
 M_{a,k}=(L_{a,k}+4\sqrt{L_{a,k}L_{a,k+1}})^{1/2}.
\]
For \(J\ge2100\) the normalized energy of \(P_{a,k}\) is bounded by \(L_{a,k}\): the integral of \(v^{2a}|\log v|^{2k}\) on \([0,1]\) is the first displayed term, and the Riemann-sum error is at most its total variation divided by \(J\). This nonnegative unimodal function has variation at most twice its displayed maximum. The derivative multiplies its coefficients by \(4i\log z_j\). \(M_{a,1}\le M_{6,1}\) uniformly on the needed interval. Conjugating adds the negative ordinates, already accounted for in the factor two above. The high right-side contribution to \(D(J)/J^7\) is bounded by
\[
 J^{3/2}\sqrt{0.39 K_H V}\,(M_{8,0}+2M_{6,1}),\qquad
 M_{8,0}+2M_{6,1}<0.368954.
\]
The expression is increasing in \(J\). Including the earlier subtotal gives \(0.160396\) at \(J=5000\), \(0.220403\) at \(J=10000\) and \(0.990495\) at \(J=44000\). Combine with the independent small-\(J\) certificate for \(J\le2100\).

In order of magnitude, if the same character is verified through any height \(H\), this argument gives \(D(J)\ll J^7+J^{17/2}\log(H)/H\) for \(J(1+\log J)\le H\), with constants bounded independently of \(H\). The guaranteed \(J^7\) range thus extends to \(J\ll(H/\log H)^{2/3}\). This use of the verified high zero range improves on adding individual Riesz error bars, whose cutoff is only of square-root order.

## All-height improvement over the absolute zero-density envelope

Here \(L=4\log J\), \(T=e^t\), and \(\kappa(T)=[10.1\log4+49.13(\log T)^{2/3}(\log\log T)^{1/3}]^{-1}\) for the fixed modulo-four character at sufficiently large height. At \(T\le J\) group the zeros in dyadic height shells and bins \(\beta\in(1-r-1/L,1-r]\), with \(r\ge0\). A bin containing \(n\) members contributes at most
\[
 \ll J^9 e^{-Lr}T^{-2}
      \min\{n,\ \sqrt{n\log(2T)(1+\log J+T/J)}\}.
\]
For the second bound, use the same varying-abscissa reduction, now on \(\beta\ge4/5\), and Cauchy–Schwarz on these \(n\) zeros with the ordinary counting measure. The local zero-count bound is \(O(\log T)\). On an interval of length \(O(T)\), the consecutive-frequency row-sum bound above gives mean square \(O((T+J(1+\log J))J)\) for all the required polynomials and their derivatives. \(J^{4+4\beta}\le J^8e^{-Lr}\). The first bound is direct termwise summation. No nonnegativity of individual spectral contributions is used. Contributions of \(\beta\le4/5\) or \(T\ge J\) are \(O(J^{8.2}+J^8\log J)\).

For every \(h>0\), Jutila's fixed-conductor density estimate gives \(n\ll_h\exp[(2+h)(r+1/L)\log(2T)]\) for the bins above \(4/5\) (bins straddling \(4/5\) can be discarded with a fixed power saving). A nonempty bin has \(r\ge\kappa(2T)-1/L\). All factors of \(\log J\), and the polynomially many bins and shells, can be kept outside the exponential. Put
\[
 \mu_b(L)=\inf_{t_0\le t\le L/4}
 \big\{2t+[L-bt]\kappa(2e^t)\big\}.
\]
For fixed small \(h>0\),
\[
 D(J)\ll_h J^9(\log J)^{O(1)} e^{-\mu_{1+h/2}(L)}+O_\chi(J^{9-\eta})
\]
for some fixed \(\eta>0\) absorbing small heights and the discarded ranges. The comparison obtained by taking absolute values at each sample with the very same region and density input has \(\mu_{2+h}(L)\). Both are unconditional upper envelopes, and neither need have the same order as the true deficit. [Khale, Theorem 1.1, equation (1.3), and zero-density input on page 5](https://arxiv.org/pdf/2210.06457) · [Jutila, Theorem 1](https://doi.org/10.7146/math.scand.a-11701).

For fixed \(b\), each minimizing \(t\) divided by \(\Phi(L)=L^{3/5}(\log L)^{-1/5}\) tends to the unique positive minimizer \(u_*\) of \(2u+49.13^{-1}(5/3)^{1/3}u^{-2/3}\). This follows from compact uniform convergence after rescaling, with both endpoint regions excluded by the two positive main terms. At all these minimizers \(t\kappa(2e^t)\sim k_* L^{1/5}(\log L)^{-2/5}\) with \(k_*=49.13^{-1}(5u_*/3)^{1/3}>0\). Evaluating either objective at the other's minimizer sandwiches their difference, so
\[
 \mu_{1+h/2}(L)-\mu_{2+h}(L)
 \sim (1+h/2)k_*L^{1/5}(\log L)^{-2/5}.
\]
This yields a second strictly growing exponential saving for the signed, clipped prime statistic relative to the specified absolute envelope, in addition to the earlier \(2^{2/5}\) gain in the leading Riesz saddle constant. It does not supply the requested fixed-power bound or change the leading VK constant. The sparse simulated divisor in the [earlier comparison](spectral-interpolation-fourth-deficit-vk.md#what-the-zero-free-curve-and-sparse-counting-alone-allow) shows why one near-extremal pair at each of very sparse heights can suffice to saturate the leading constant in that model. No such near-extremal sequence of actual Dirichlet zeros is asserted.

**Comparison with stronger density input.** Pintz's Corollary 2, (2.15) gives, for fixed conductor and every fixed positive δ, a bound of the form exp(δrt) for the number of zeros with real part above 1−r through height exp(t) once r is sufficiently small in terms of δ. Absolute Riesz summation using this result already changes the saddle density coefficient from 2 to an arbitrarily small positive constant. The preceding strictly growing gain is a comparison at fixed Jutila input. It is not an improvement over every known density theorem. In the zeta case Bellotti's uniform near-one density theorem gives at most a fixed power of log T across the extreme zero-free boundary, even with absolute summation. The unconditional half-power improvement in the finite verified range uses a different comparison and persists. [Pintz, Corollary 2, (2.15)](https://arxiv.org/pdf/1804.05552) · [Bellotti, near-unity density, Theorem 1.1](https://arxiv.org/pdf/2311.05136).

For the fixed modulus-four character, writing Ψ(L)=L^(1/5)/(log L)^(2/5), Pintz therefore gives the actual bound D(J) ≤ J⁹ exp(−μ₀(L)+o(Ψ(L))). Fix any positive tolerance and apply (2.15) with a sufficiently small fixed epsilon, then let J grow past its resulting fixed threshold. The polynomial-log factors are absorbed in that tolerance. For ζ, Bellotti's theorem instead gives D(J) ≪ J⁹(log J)^C exp(−μ₀(L)), with the zeta zero-free curve in μ₀. Indeed its loss for a bin at distance r is exp(O(t r^(3/2)))(log T)^C. Restrict to a sufficiently small fixed near-one strip so that −Lr+O(t r^(3/2)) decreases for t ≤ L/4. At r equal to the VK boundary, t r^(3/2) is bounded. The remaining zeros are a fixed power smaller. These two strengthened statements already follow by absolute Riesz summation and classical inputs. Neither gives J^(7+ε).

## The rational principal character

For \(S_1(x)=\sum_{p\le x}\log p\,(x-p)-x^2/2\) and \(D_1(J)=\sum_{j\le J}(-S_1(j^4))_+\), the same method gives **\(D_1(J)<J^7\) for every integer \(1\le J\le 75{,}000{,}000\)**. Between indices 2100 and 10,000,000 it gives \(D_1(J)<0.152J^7\). A sample at the upper endpoint sums primes through \(3.1640625\cdot10^{31}\). No prime enumeration to such a cutoff is used. [Principal certificate](spectral-interpolation-rational-deficit-large-sieve.py) · [128-bit receipt](spectral-interpolation-rational-deficit-large-sieve-128.receipt) · [192-bit receipt](spectral-interpolation-rational-deficit-large-sieve-192.receipt).

Use \(H=3\cdot10^{12}\) from Platt and Trudgian. The full central Hadamard allowance is \(B=2+\gamma_E-\log(4\pi)<0.046192\). The Riesz kernel applied to \(-\zeta'/\zeta\) has main term \(x^2/2\), already subtracted. Its other real residues contribute
\[
 -x\log(2\pi)+\frac{\zeta'}{\zeta}(-1)
 -\sum_{k\ge1}\frac{x^{1-2k}}{2k(2k-1)}.
\]
There is no trivial-zero collision at \(-1\). The last sum has absolute value below one for \(x\ge2\). The two finite constants are also enclosed using native Arb Taylor jets. [Platt and Trudgian, Theorem 1](https://doi.org/10.1112/blms.12460).

For \(t\ge H-1\), Rosser's Theorem 19 writes the count of zeros with **positive** ordinates as \(t\log(t/(2\pi e))/(2\pi)+7/8\) with error at most \(0.137\log t+0.443\log\log t+1.588\). Doubling for both signs gives an error below \(0.6\log t\) in this range. This yields the same local squared-weight coefficient 0.39, with the derivative of the new principal main term even smaller. The doubled constant \(7/4\) cancels in the summation-by-parts tail. Thus the earlier formula applies with \(K_H=[\log(H/(2\pi e))+2]/(\pi H)+(2\log H+1/2)/H^2<2.960\cdot10^{-12}\). [Rosser, Theorem 19](https://doi.org/10.2307/2371291).

The direct small-prefix comparison to \(J=1000\), including the prime 2 in all powers and the pole center even at \(x=1\), gives \(D_1(1000)<0.104\cdot1000^7\). From 1001 through 2100 the individual high-zero estimate covers the transition. For \(J\ge2100\), using the weaker \(D_1(1000)<0.12\cdot1000^7\), the normalized subtotal before the high right-hand zeros is at most 0.111658. The same increasing mean-square bound as above gives 0.151118 rounded upward at 10 million and 0.922307 at 75 million. All real-power and log bounds in the accompanying receipt have outward rounding. This is a finite arithmetic result, together with the separately documented classical all-height asymptotics.
