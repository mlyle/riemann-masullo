# Explicit density for the one-sided fourth-power prime deficit

For the actual principal rational character, \(D_1(J)<J^7\) for every \(1\le J\le20{,}000{,}000{,}000\). For the nonprincipal character modulo four, \(D_{-4}(J)<J^7\) for every \(1\le J\le150{,}000\). For the same index ranges starting at 2100, the respective upper constants are \(0.912\) and \(0.891\). The endpoint ratios delivered by the proof are bounded by \(0.911014434\) and \(0.890688390\). The principal prime cutoff is \(1.6\cdot10^{41}\); the modulo-four prime cutoff is \(5.0625\cdot10^{20}\). These are finite unconditional arithmetic estimates. [Python proof constants](spectral-interpolation-rational-deficit-density.py) · [128-bit receipt](spectral-interpolation-rational-deficit-density-128.receipt) · [192-bit receipt](spectral-interpolation-rational-deficit-density-192.receipt).

Use the notation and small-index/archimedean ledgers in the [previous mean-square proof](spectral-interpolation-mod4-deficit-large-sieve.md). In particular \(H=3\cdot 10^{12}\) for zeta and \(H=25{,}000{,}000\) for the modulo-four character. Write \(J_0=2100\), \(K_H\) for the upper bound on the full \(\sum_{|\gamma|>H}\gamma^{-2}\), and \(V\), \(M_{a,k}\) for the explicitly computed coefficients. For \(J\ge J_0\) all terms other than the positive/right high zeros and their conjugates cost at most \(0.111658 J^7\) or \(0.127630 J^7\), respectively. The optimization \(D=\max_{0\le c_j\le1}-\sum c_j S(j^4)\) uses a common sequence of coefficients on all ordinate and abscissa shells.

For \(\sigma\in[1/2,1]\) let \(K(\sigma)=\sum_{\gamma>H,\beta>1/2,\,\beta\ge\sigma}\gamma^{-2}\). It is at most \(K_H/4\). For \(\sigma\ge0.52\) there is a second upper bound. Ramaré's theorem counts both signs of the ordinates, so integration by parts and conjugation give \(K(\sigma)\le \int_H^\infty N(\sigma,T)T^{-3}\,dT\), where zero counting begins above the verified height. For the principal character use the majorant \(9.8(3T)^{8(1-\sigma)/3}\log^{5-2\sigma}T+103\log^2T\). For the modulo-four character, set \(Q=10\) and discard the other nonnegative character counts on the left of the family bound. Its coefficient \(4/\varphi(4)=2\) gives \(10(56\cdot10^5T^3)^{1-\sigma}\log^{5-2\sigma}(100T)+1600\log^2(100T)\). For each monomial \(T^a\log^d(bT)\), the integral is at most
\[
 \frac{H^{a-2}\log^d(bH)}{2-a-d/\log(bH)} .
\]
Indeed \(1+\log(T/H)/\log(bH)\le(T/H)^{1/\log(bH)}\), and the displayed denominator is positive throughout this application. Let \(k_l\) be the smaller of the resulting bound and \(K_H/4\) at \(l\), using the latter alone below \(0.52\). [Ramaré, Theorem 1.1, equations (1.1)–(1.2)](https://doi.org/10.1090/mcom/2991) · [Author's PDF and count convention](https://ramare-olivier.github.io/Maths/DensityEstimate-34.pdf).

For an individual high right-hand zero, integrate the sample amplitude in its abscissa before taking absolute values:
\[
 j^{4+4\beta}=j^6+4\int_{1/2}^{\beta} j^{4+4v}\log j\,dv.
\]
At each \(v\) the new prime-sample coefficient is \(c_j\log j/\log J\), again in \([0,1]\). Reserve \(2 k_{1/2}(1/7+1/J_0)\) of the normalized error budget for the first term and its conjugates. Partition \(v\in[1/2,1]\) at \(0.5,\ 0.625,\ 0.626,\ldots,1\). On each interval \([l,u]\), \(K(v)\le k_l\) and \(M_{4+4v,0}\le M_{4+4l,0}\). The common-mask mean square from the previous note and conjugation bound the normalized integral over this band by
\[
 2\sqrt{0.39\, k_l V}\,M_{4+4l,0}
 \big[J^{4u-5/2}-J^{4l-5/2}\big].
\]
The independent alternative of adding each sample absolutely gives
\[
 2k_l \big[(5+4l)^{-1}+J_0^{-1}\big]
 \big[J^{4u-2}-J^{4l-2}\big].
\]
The formulas use \(4\log J\int_l^u J^{4v-c}\,dv = J^{4u-c}-J^{4l-c}\). One may choose the smaller bound separately on each band because all the input inequalities hold for the actual optimizing coefficients. Both expressions are monotone in \(J\ge J_0\), including the first band with upper exponent zero in the mean-square bound. Sum the band minima, the low-index/low-frequency ledger, and the initial high-right term. The script verifies the claimed endpoints with outward rounding. The other small indices were covered in the [principal](spectral-interpolation-mod4-deficit-large-sieve.md#the-rational-principal-character) and [modulo-four](spectral-interpolation-mod4-deficit.md#actual-primes-through-fourth-power-index-2100) calculations.

The same code also evaluates each band's absolute-only option for a matched comparison. Its endpoint constants are \(14.38131\) and \(15.66639\), respectively, both above one. Thus the zero-sampled mean square supplies a numerical gain for this finite one-sided certificate. Those larger constants are upper estimates from a particular calculation, not lower estimates for either arithmetic deficit.

For perspective, keeping the conductor fixed and treating a verified height \(H\) as a parameter, Ramaré's density theorem already extends the natural square-root-order *pointwise Riesz* range to \(J\le H^{1-\epsilon}\) as \(H\to\infty\), for any fixed \(\epsilon>0\). On the high right of the strip at distance \(r=1-\beta\), bound the \(K\)-factor by \(\min(H^{-1},H^{-2+Ar})\) up to powers of \(\log H\), where \(A=8/3\) for zeta and \(A=3\) for the modulo-four specialization. At \(J=H^{1-\epsilon}\) splitting \(r\) at \(1/A\) shows that \(J^{2-4r}K(1-r)\) has a strictly negative power of \(H\) uniformly for \(0\le r\le1/2\); the layer integral costs only a logarithm. The new finite cutoff comparison above is at the actual published heights and explicit constants. An unbounded \(J^7\)-sized upper bound for either fixed character remains unproved.
