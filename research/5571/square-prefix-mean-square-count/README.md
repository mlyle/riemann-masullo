# Counting nonnegative square prefixes by the high-zero mean square

Let \(w(t)=2-\cos t-\cos(\sqrt2t)\), \(I(x)=\int_1^x w(\log v)dv\), \(E(x)=\sum_{p\le x}\log(p)w(\log p)-I(x)\), \(A(k)=\sum_{j=1}^k E(j^2)\), and let \(A_d\) use the discrete integer compensator. With \(J=3\cdot10^{13}\), **fewer than \(0.000234J\)** integer indices \(J\le k<2J\) have either \(A(k)\ge0\) or \(A_d(k)\ge0\). Consequently, for every integer \(5.8\cdot10^{13}\le T\le6\cdot10^{13}\),
\[
 \#\{1\le k\le T:\max(A(k),A_d(k))\ge0\}<T^{49/50}.
\]
The latter bound charges every earlier, untested prefix as nonnegative. This proves the desired exceptional-count shape on a bounded band of terminal indices. Its extension to an unbounded sequence remains open. The proof uses ordinary primes, the verified zeta height \(H=3\cdot10^{12}\), and no assumption on the higher zeros.

## An unconditional mean-square tail in the square index

Set \(a=\alpha=1/2\), \(S=\{0,\pm1,\pm\sqrt2\}\), \(c_0=2\), \(c_{t\ne0}=-1/2\), and \(B(x)=\frac12\int_1^x E(v)v^{-1/2}dv\). Write \(V_H(u)\) for the part of the exact \(B(u^2)/u^2\) zero sum having \(|\gamma|>H\). It suffices here to allow \(H\ge3\cdot10^{12}\), \(J\ge1\). The following bound is independent of any zero verification:
\[
 \left(\frac1J\int_J^{2J}|V_H(u)|^2du\right)^{1/2}
 \le 19.36\frac{J\log(4H)}{H^{3/2}}
 \qquad(H\ge3\cdot10^{12}).
\]
For comparison the direct absolute sum costs a multiple of \(J\log H/H\). This extra square root of the height permits arithmetic sign counts far beyond the previous pointwise test.

Here are the constants. For positive zeros, Hasanalizade–Shen–Wong, Corollary 1.2, bounds the difference between \(N(v)\) and \((v/2\pi)\log(v/(2\pi e))\) by \(0.1038\log v+0.2573\log\log v+9.3675\) for \(v\ge e\). On a two-sided shell \(T<|\gamma|\le2T\), \(T\ge H\), the total number with multiplicity is at most \(0.7T\log(4T)\). Each interval of length one contains at most \(1.25\log(4T)\) zeros from this shell. For the latter clip to the shell, use symmetry, and enlarge the clipped terminal interval by at most 0.1 on each side to include endpoints. The derivative of the main counting term is bounded by \(\log(4T)/(2\pi)\). Each evaluation of the counting remainder costs at most \(R\log(4T)\), with \(R=0.1038+0.2573\log\log(4H)/\log(4H)+9.3675/\log(4H)<0.444\); both ratios used here decrease as \(H\) grows. Thus the two coefficients required are at most \(2/\pi+2R/H<0.7\) and \(1.2/(2\pi)+2R<1.25\). [Hasanalizade, Shen and Wong, Corollary 1.2](https://arxiv.org/pdf/2107.06506).

For a fixed \(t\), put \(v=\log(u/J)\). Each term in this finite shell has the form \(d_\rho\exp(2(b+i(\gamma+t))v)\), \(b=\beta-1/2\), with
\[
 |d_\rho|\le\frac{\alpha|c_t|J}{T^2(1-\sqrt2/H)^2}.
\]
This follows from the denominators \((\rho+it)(\rho+\alpha+it)\), the common normalization, and \(J^{2b}\le J\). To bound its squared integral on \(0\le v\le\log2\), majorize the interval indicator by \(e^{(\log2)^2}e^{-v^2}\). The Gaussian Gram integral for a pair has modulus at most \(\sqrt\pi e\, e^{-(\gamma-\gamma')^2}\), since \(|b+b'|\le1\). For each fixed row, the sum of the latter Gaussian factors is at most \(3.5\log(4T)\): count the two bins at each integer distance and use \(2(1+e^{-1}+e^{-4}/(1-e^{-5}))\cdot1.25<3.5\). Symmetry and \(2|d_\rho d_{\rho'}|\le |d_\rho|^2+|d_{\rho'}|^2\) bound the Gram form by the row bound times \(\sum |d_\rho|^2\). The normalized physical measure \(du/J=e^v dv\) costs at most 2. The resulting norm on one shell is bounded by
\[
 \sqrt{2 e^{(\log 2)^2}\sqrt\pi e\cdot3.5\cdot0.7}\,
 \frac{\alpha|c_t|J}{(1-\sqrt2/H)^2}\frac{\log(4T)}{T^{3/2}}.
\]
Apply the triangle inequality first to the five shifts, with \(\sum|c_t|=4\), then to \(T=2^jH\). With \(r=2^{-3/2}\) the extra geometric factor is \(1/(1-r)+(\log2/\log(4H))r/(1-r)^2\). The coefficient at the initial height is below 19.355 and decreases with \(H\). Absolute convergence on each bounded physical interval justifies the infinite-shell limit.

## Every exceptional integer spends a unit of real length above the threshold

Hereafter take the stated numerical \(J,H\). For \(J\le u\le2J\) the ordinary endpoint satisfies \(|E(u^2)|\le e_0 u^2\) with \(e_0<1.185\cdot10^{-9}\). Set \(D=1+\sqrt2\). Use Johnston's Theorem 4.1, Table 2 row \(a=1\), which gives \(|\vartheta(v)-v|\le\sqrt v\log^2v\) from 3 to \(2.165\cdot10^{30}\). Partial summation with \(|w|\le4\), \(|w'|\le D\) costs at most \((4+2D)\log^2(4J^2)/J+2D/J^2\) after normalization. The last term covers \([1,3]\) using \(|\vartheta(v)-v|\le v\). [Johnston, Theorem 4.1, Table 2](https://arxiv.org/pdf/2109.02249).

The [exact square identity and the one-sided saw estimate](../signed-riesz-margin/README.md#a-million-consecutive-large-square-prefix-cutoffs) give \(A_d(k),A(k)\le B(k^2)+E(k^2)+I(k^2)/2+k[(8+4D)/8+D\log(k^2)]\). If either prefix is nonnegative, then at every \(u\in[k,k+1]\),
\[
 0\le B(u^2)/u^2+I(u^2)/(2u^2)+2e_0+[(8+4D)/8+D\log(4J^2)]/J .
\]
Indeed \(B(u^2)-B(k^2)=\int_k^u E(v^2)dv\ge-e_0u^2\), and \(I(k^2)\le I(u^2)\) by weight positivity. Thus counting the exceptional integers requires only a continuous mean square, with no sampling error at the high frequencies.

In the exact Riesz upper bound, subtract only the ordinary prime squares; the higher prime powers have nonnegative weights. The term \(I(u^2)/2\) cancels the square constant, and the two rotating contributions combine into
\[
 -\Re\sum_{t=1,\sqrt2}\frac{it\,u^{2it}}{(1+2it)(1+it)}.
\]
On the full interval this is at most \(-0.33459\), by 4,000 enclosing real cells. The verified low zeros contribute at most \(0.114311\) in absolute value by the positive Hadamard reciprocal-square identity. The prime-square PNT error is at most \((2D+4)(598/J+\log^2J/(4\pi\sqrt J))<0.000124\), using Johnston's Corollary 3.3 through \(2J\). The finite Riesz kernel terms, trivial zeros and lower limit correction cost less than \(7\cdot10^{-13}\); the verifier evaluates the needed logarithmic derivatives with interval arithmetic. The preceding [finite Riesz derivation](../signed-riesz-margin/README.md#unconditional-finite-height-interval) gives these terms individually. [Platt and Trudgian's verified height](https://arxiv.org/abs/2004.09765) · [Johnston, Corollary 3.3](https://arxiv.org/pdf/2109.02249).

Inserting all interval enclosures gives \(V_H(u)>0.22015\) throughout each exceptional unit interval, whereas its full-band root mean square is below \(0.003366\). Chebyshev's inequality bounds the exceptional fraction by \(0.000233658\) using the unrounded enclosures. Since \(k=J,\ldots,2J-1\) indexes disjoint unit interiors, the terminal count is at most \((1+0.000234)J\), including the potentially untested last point \(k=2J\). The verifier compares this with \((5.8\cdot10^{13})^{49/50}\).

Replay with `uv run --no-project --with python-flint==0.9.0 python prefix-count-rms.py --precision 192`. The two receipts use 128 and 192 bits. These are classical analytic arguments and rigorous numerical enclosures; the existing native results supply the exact square identity separately. [Verifier](prefix-count-rms.py) · [128-bit receipt](prefix-count-rms-128.txt) · [192-bit receipt](prefix-count-rms-192.txt).
