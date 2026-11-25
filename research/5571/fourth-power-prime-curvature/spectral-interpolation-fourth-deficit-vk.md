# Direct fourth-power deficit estimates for the rational characters

Let \(\chi=\chi_{-4}\) or the trivial rational character of conductor one. Put \(\delta_\chi=0\) or \(1\), respectively, and
\[
 S_\chi(x)=\sum_{p\le x}\chi(p)\log p\,(x-p)-\delta_\chi x^2/2,\qquad
 D_\chi(J)=\sum_{1\le j\le J}(-S_\chi(j^4))_+ .
\]
All the bounds in this note concern these unsmoothed, clipped first-prime measurements. The target is \(D_\chi(J)\ll_\varepsilon J^{7+\varepsilon}\).

## A fixed-character upper bound with the Riesz denominator retained

Write \(\Phi(L)=L^{3/5}(\log L)^{-1/5}\) for large \(L\), and set
\[
 c_\chi=4^{3/5}\left(\frac{15625\cdot 4}{324\,C_\chi^3}\right)^{1/5}.
\]
With \(C_{\chi_{-4}}=49.13\) and \(C_{\bf1}=48.1588\), for all \(\eta>0\) and all sufficiently large \(J\),
\[
 D_\chi(J)\ll_{\chi,\eta} J^9\exp(-(c_\chi-\eta)\Phi(\log J)).
\]
The two values of \(c_\chi\) are approximately \(0.63605539\) and \(0.64372089\). These are numbers calculated from the cited zero-free regions, with the implicit asymptotic slack \(\eta\); an effective onset is not supplied. The strict power-scale gap to \(J^{7+\varepsilon}\) remains.

For the signed sum before clipping, the first-Riesz explicit formula gives
\[
 S_\chi(x)=-\sum_{\rho}\frac{x^{1+\rho}}{\rho(1+\rho)}
             +O_\chi(x^{3/2}\log^2(2x)).
\]
Indeed apply Perron with \(x^{s+1}/[s(s+1)]\) to \(-L'/L\). The pole at one is subtracted by the chosen centering. The two kernel poles and trivial zeros contribute \(O_\chi(x\log(2x))\) by the usual zero-avoiding rectangle shift. The nontrivial zero coefficients are absolutely summable. Removing proper prime powers costs \(O(x^{3/2}\log^2(2x))\) by Chebyshev. In particular this proof works at integers and prime powers themselves because the Riesz weight vanishes at the endpoint.

For sufficiently large ordinates the zero-free regions give \(1-\beta\ge (C+o(1))^{-1}(\log |t|)^{-2/3}(\log\log |t|)^{-1/3}\) for fixed conductor. In the modulus-four case the fixed extra \(10.1\log 4\) in the denominator is absorbed into the indicated asymptotic constant. At bounded height \(\beta<1\), hence the finitely many zeros are absorbed in an \(O_\chi(x^{2-a})\) bound for some \(a>0\). [Khale, Theorem 1.1, equation (1.3)](https://arxiv.org/pdf/2210.06457) · [Mossinghoff, Trudgian and Yang, Theorem 1.2](https://doi.org/10.1007/s40993-023-00498-y).

For each \(\xi>0\) choose a small fixed \(\tau>0\) so that \(N_\chi(1-\tau,2T)\ll_{\chi,\xi} T^\xi\). This is immediate from the fixed-conductor zero-density bound near one; in particular a bound \(N_\chi(\sigma,T)\ll_{\chi,\epsilon}(qT)^{(2+\epsilon)(1-\sigma)}\) for \(4/5\le\sigma<1\) suffices. The usual Ingham density bound also suffices for zeta. All zeros with \(\beta<1-\tau\) contribute \(O(x^{2-\tau})\) in total. Each remaining dyadic shell costs at most
\[
 O_{\chi,\xi}\!\left(x^2 T^{-2+\xi}
   \exp\left[-\frac{(1-o(1))\log x}{C(\log T)^{2/3}(\log\log T)^{1/3}}\right]\right).
\]
The power \(-2+\xi\) uses both the actual Riesz denominator and the density estimate. [Jutila, *On Linnik’s constant*, Theorem 1](https://doi.org/10.7146/math.scand.a-11701) · [Khale’s fixed-character application of this density input, p. 5](https://arxiv.org/pdf/2210.06457).

For \(L=\log x,\ t=\log T,\ d>0\), the minimum of \(dt+L/[Ct^{2/3}(\log t)^{1/3}]\) over sufficiently large \(t\) is \((K_d+o(1))\Phi(L)\), with
\[
 K_d=\left(\frac{15625\,d^2}{324 C^3}\right)^{1/5}.
\]
Substitute \(t=u\Phi(L)\). On compact subintervals of \(u>0\), the normalized objective tends uniformly to \(du+C^{-1}(5/3)^{1/3}u^{-2/3}\). Outside a sufficiently wide such compact interval the objective exceeds the minimum, by monotonicity of its two summands separately; direct minimization of the limit gives \(K_d\). There are only \(O(L)\) dyadic shells with \(t\le L\), whose count is absorbed in the arbitrary exponential slack; those with \(t>L\) form a negligible geometric tail. Let \(d=2-\xi\) and then choose \(\xi\) arbitrarily small. Thus \(|S_\chi(x)|\ll x^2\exp(-(K_2-\epsilon)\Phi(\log x))\). The upper envelope increases for sufficiently large \(x\); applying it at \(x=J^4\) and summing \(J\) terms proves the bound for the actual negative parts. An ordinary one-denominator zero-density PNT estimate, or applying just \(N(T)\ll T\log T\) to the Riesz formula, gives the corresponding saddle with \(d=1\). The gain in its leading exponential constant from the same zero-free curve is \(2^{2/5}\). This comparison makes no claim about a world record.

## Selecting quadratic classes and a sharp exceptional-pair scale

Take ordered independent prime pairs \(q,d\in(Q,2Q]\), \(Q=J^{12}\), and let \(S_{e,f}(j;q,d)\) be four times the degree-one sum restricted by \((q/p)=e,(d/p)=f\), with the same centering. For arbitrary sample- and pair-dependent choices \(e,f=\pm1\), denote the resulting deficit by \(D^{e,f}\). The maximum below includes these adaptive strategies. For each integer \(k\ge1\) and \(\varepsilon>0\),
\[
 \left\|\sup_{e,f}|D^{e,f}-D_\chi|\right\|_{L^{2k}(q,d)}
 \ll_{k,\chi,\varepsilon} J^{7+\varepsilon}
        (1+J^{4k-12})^{1/(2k)}.
\]
The same estimate holds for any fixed field whose actual real degree-one coefficients are bounded by \([F:\mathbf Q]\log p\), including any real sequence of centers in the differences. At \(k=3\) it gives the sixth moment at the target exponent. Consequently, if \(D_\chi(J)\ge J^{7+\delta}\), the fraction of pairs that can halve the deficit using any selections is at most \(O_{\chi,\delta,\varepsilon}(J^{-6\delta+\varepsilon})\). At all large \(J\) the fixed-character upper bound of the preceding section applies to all selections outside \(J^{-12+o(1)}\) of the pairs, with any slightly smaller exponential constant. This still allows the unrestricted deficit to exceed \(J^{7+\varepsilon}\).

To prove the moment bound, fix one sample \(x=j^4\) and let \(a_p\) be its real coefficient times \(x-p\). The odd-prime class difference consists of the three sums twisted by \((q/p),(d/p),(qd/p)\), with unit coefficients, by expanding \((1+e(q/p))(1+f(d/p))\). Handle the single prime 2 trivially, with \(O_\chi(x)\) cost. The function \(z\mapsto(c-z)_+\) is 1-Lipschitz. The same pointwise sum of absolute twists therefore majorizes every allowed class selection.

For a single variable \(q\), raise the prime sum to its \(k\)-th power. Group the products of primes by their odd squarefree kernel \(r\le x^k\), with coefficient \(b_r\). This identity holds on our prime rows, since \(q>p\). Even exponents disappear there. The coefficient energy satisfies
\[
 \sum_r|b_r|^2\le (2k-1)!!\left(\sum_p|a_p|^2\right)^k.
\]
Indeed every contributing \(2k\)-tuple has even total multiplicity of each prime, and hence can be paired into equal entries. Summing the absolute products on each of the \((2k-1)!!\) possible pairings gives this inequality, allowing overcounting.

Heath-Brown’s quadratic large sieve with odd squarefree row and column variables bounds the \(q\)-sum of squares of this new polynomial by \(O_\epsilon((Qx^k)^\epsilon(Q+x^k)\sum|b_r|^2)\). Extend the prime rows to all squarefree rows *after* grouping since the larger sum is nonnegative. Quadratic reciprocity, if needed for the symbol orientation in the quoted theorem, splits the two residue classes of \(q\bmod4\) and twists the coefficients by signs independent of \(q\) within each class. The same proof, with \(d\) held fixed, applies to \((qd/p)\); the factors \((d/p)\) have modulus one. Divide the large-sieve estimate by the number \(\gg Q/\log Q\) of actual prime rows and use \(\sum |a_p|^2\ll_\chi x^3\log(2x)\) by Chebyshev. Minkowski across \(j\le J\) yields the stated result. [Heath-Brown, *A mean value estimate for real character sums*, Theorem 1](https://ora.ox.ac.uk/objects/uuid%3Ab188b365-d8d1-4267-8548-49f01e6cb6a7) · [actual pair and cell definitions, PR 7627](https://github.com/mlyle/riemann-masullo/blob/49ba04e6e47304030c6011df83878b42420acbb7/RiemannMasullo/Ch13_ZerosHecke/QuadraticPrimeTwists.lean#L291).

There is an exact arithmetic example at the exceptional-pair scale. For \(d=q\) the class with opposite signs is empty for every sample. For \(\chi_{-4}\) it has deficit **zero** for every \(J\), on a genuine family of relative size \(1/\#\{Q<q\le2Q\}\asymp J^{-12}\log J\). For the principal character this same empty class has deficit \(\frac12\sum_{j\le J}j^8\asymp J^9\), whereas \(D_{\bf1}=o(J^9)\) by the PNT. Hence a \(J^9\)-sized class discrepancy occurs on a fraction \(\gg J^{-12}\log J\) of actual prime pairs. In particular for every integer \(k\ge3\) the \(L^{2k}\) discrepancy exponent for the principal character is *exactly* \(9-6/k\): the diagonal lower bound matches the quadratic large-sieve upper bound in power. Any claim of a \(J^{7+o(1)}\) bound for every finite norm greater than six on this product family would contradict those genuine diagonal pairs. The definition really uses all of \(U\times U\); there is no distinctness restriction. The example does not apply after imposing \(q\ne d\).

These are classical derivations, not Lean-certified consequences. The large sieve controls selection errors around the true first-prime deficit. The missing fixed-character arithmetic estimate is an upper bound of order \(J^{7+\varepsilon}\) for \(D_\chi(J)\) itself.

## A second moment range for the product twist on distinct pairs

Remove the diagonal and put \(m=qd\). Now \(m\) is squarefree, \(m\le4Q^2\), and it has at most two ordered representations. The same coefficient pairing and large-sieve argument, dividing by a row population \(\gg Q^2/\log^2 Q\), gives an \(L^{2k}\) bound of \(J^{7+\epsilon}(1+J^{4k-24})^{1/(2k)}\) for the cumulative product twist on distinct pairs. At \(k=6\) its twelfth moment is \(\ll J^{84+\epsilon}\). Fix \(\delta>0\). Remove auxiliary primes \(q\) whose single-twist cumulative sum exceeds \(J^{7+\delta}/10\); the deleted population is \(O(J^{-6\delta+\epsilon})\) of the primes by the sixth moment. Among remaining ordered distinct pairs, at most \(O(J^{-12\delta+\epsilon})\) of the original population has product twist exceeding \(J^{7+\delta}/10\). For every other pair, no choice of the four classes can halve an unrestricted deficit at least \(J^{7+\delta}\), including the negligible isolated contribution of 2. This refinement concerns the geometry of the exceptional pairs. It does not estimate the unrestricted deficit itself.

## What the zero-free curve and sparse counting alone allow

Take synthetic simple zero quadruples \(\beta_n\pm i\gamma_n,\ 1-\beta_n\pm i\gamma_n\) with \(\gamma_n=e^{t_n}\), \(\beta_n=1-(1+o(1))/(Ct_n^{2/3}(\log t_n)^{1/3})\), always just inside the permitted curve. The \(t_n\) can grow arbitrarily fast. Form the absolutely convergent first-Riesz zero series with its literal coefficients \(-1/[\rho(1+\rho)]\) and measure the same clipped sum on \(j^4\). Choose \(4\log J_n=3C t_n^{5/3}(\log t_n)^{1/3}(1+o(1))\), which places this shell at the stationary point for \(d=2\). Each earlier prescribed pair has strictly smaller \(\beta\) and can be made \(o(J_n^{4+4\beta_n}/\gamma_n^2)\) on \(J_n/2\le j\le J_n\) by enlarging \(t_n\). Choose later heights inductively so their absolutely summed contributions are smaller on all preceding finite target windows. The reflected left-hand members are smaller in the same sense.

The dominating pair has real part proportional to a cosine with phase \(4\gamma_n\log j+\varphi_n\). Its negative part has a fixed positive mean on the target window. Indeed summation versus the integral costs \(O(\gamma_n/J_n)\) after normalization by the number of samples, using a uniform total variation bound \(O(\gamma_n)\). In the integral, substitute \(j=J_nv\), with \(1/2\le v\le1\), and integrate fixed nonzero Fourier frequencies by parts as \(\gamma_n\to\infty\). This leaves the strictly positive circular mean of the clipped cosine, uniformly in its phase. The additional \(v^{4+4\beta_n}\) factor is bounded below on this compact interval. Thus
\[
 D_{\rm model}(J_n)\gg J_n^{5+4\beta_n}\gamma_n^{-2}
 =J_n^9\exp[-(4^{3/5}K_2+o(1))\Phi(\log J_n)] .
\]
The model has sparser zeros than any of the counting bounds used above. It is a limitation of that information and absolute Riesz summation, not a counterexample for either arithmetic character. Additional arithmetic correlation or a stronger zero-free region could improve the true deficit.

**Updated classical constants.** Bellotti's Theorem 1.3 replaces 48.1588 with 48.0718 for ζ. Her Theorem 1.1 has the uniform Hurwitz-zeta form requested by Khale's hypothesis (2.4), with A=70.6995 and B=4.43795≤4.45. Khale's Corollary 3.2 therefore applies directly with this value and gives a conductor-four denominator coefficient B^(2/3)/0.05507 = 49.0388029230510… rather than the rounded 49.13 obtained with B=4.45. The above leading constants in the exponent of the rational-prime deficit become **0.6444196367005… for ζ and 0.6367648473441… for χ₋₄**, with the same arbitrary asymptotic slack. This is a substitution in the published theorems. [Bellotti, Theorems 1.1 and 1.3](https://arxiv.org/pdf/2306.10680) · [Khale, Corollary 3.2](https://arxiv.org/pdf/2210.06457).

The [mean-square note](spectral-interpolation-mod4-deficit-large-sieve.md) compares all-height clipped summation with the exact absolute Jutila saddle and quantifies the stronger fixed-character Pintz input.
