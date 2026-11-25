# Uniform prime-error control from perfect-square cutoffs

Let \(E(N)\) be either of the exact rational first-prime errors with \(w(t)=2-\cos t-\cos(\sqrt2t)\), including \(\log p\,w(\log p)\) for every prime \(p\le N\). The integral mean is \(\int_1^N w(\log t)\,dt\), and the discrete mean is \(\sum_{n\le N}w(\log n)\).

For \(1/2\le r\le1\), a number \(C\ge0\), and all positive integer \(k\), assume \(|E(k^2)|\le C(k^2)^r\). Then, unconditionally from that sampling assumption,
\[
       |E(n)|\le (4C+12)n^r\qquad(n\ge1).
\]
Both public specializations use the literal prime sums and compensators. The positive-cutoff restriction matters, since the oriented integral at the formal argument zero is not the zero of the discrete mean. [Lean certificate](SquareSamples.lean) · [Verified axiom receipt](lean-axioms.txt).

Indeed every integer step has \(E(j+1)\ge E(j)-4\), because the arithmetic mass is nonnegative and the mean increases by at most four. For \(L=k^2\le n<U=(k+1)^2\), monotonicity of \(E(j)+4j\) gives
\[
 E(L)-4(n-L)\le E(n)\le E(U)+4(U-n).
\]
Here \(U-L=2k+1\le3\sqrt n\), \(U\le4n\), and \(\sqrt n\le n^r\). These inequalities prove the formal bound. For \(r>1/2\), \(U/n,L/n\to1\) and the additive error is \(o(n^r)\), giving even the extended-real equality
\[
 \limsup_n |E(n)|/n^r=\limsup_k |E(k^2)|/k^{2r}.
\]
At \(r=1/2\) the limsup over all \(n\) exceeds the square-sample limsup by at most eight when the latter is finite. Under the downward-step hypothesis alone the constant eight is sharp: set a real sequence equal to zero on squares and to \(4((k+1)^2-n)\) for \(k^2<n<(k+1)^2\). Its downward steps have size four, and the ratio at \(n=k^2+1\) tends to eight. The sharpness example is an abstract sequence, distinct from the prime sum.

Together with the [actual zero-exclusion criterion](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521), bounds on the positive square cutoffs at every exponent \(r\in(\sigma,1)\) suffice to exclude zeros with \(\Re s>\sigma\), for \(1/2\le\sigma<1\). To extend the hypothesis to any \(r\ge1\) use one fixed \(r_0\in(\sigma,1)\) and \(N^{r_0}\le N^r\) on \(N\ge1\). For the discrete mean \(E(0)=0\). Both end-to-end square-cutoff implications for the actual named compensators are also Lean-checked. The consumer imports the [ordinary rational zero-exclusion join](https://github.com/mlyle/riemann-masullo/commit/8c19dd0f1b0224b6c960adb2580f922620a82521) with the [updated public formula lemmas from the arithmetic dependency](https://github.com/mlyle/riemann-masullo/commit/16cec310a8e1a83053d68c04528efbea3aace70e). All five public roots use only propext, Classical.choice, and Quot.sound.

The [unconditional Fejér crossings](../two-cosine-fejer-crossings/README.md) and their square-root windows yield the desired power bound on arbitrarily late square cutoffs. Every large interval centered on an integer \(N\) with radius \(\lfloor\sqrt N\rfloor+1\) contains a square. The all-square estimate here is still an arithmetic input.
