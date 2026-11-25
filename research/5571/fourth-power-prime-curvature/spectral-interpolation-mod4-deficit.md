# The modulo-four character at the fourth-power deficit endpoint

For the primitive real character \(\chi=\chi_{-4}\), write \(S(x)=\sum_{p\le x}\chi(p)\log p\,(x-p)\) and \(D(J)=\sum_{j\le J}(-S(j^4))_+\). These are the physical first-prime observables. The all-height upper bound of order \(J^{7+\epsilon}\) remains open. There is a finite unconditional range at that exponent and an unconditional positive lower floor at infinity.

## Actual primes through fourth-power index 2100

For \(1\le J\le2100\), \(D(J)<0.173J^7\). For \(2\le j\le2100\), \(S(j^4)<-0.0174j^6\). The last prime cutoff is 19,448,100,000,000. A finite proper-power sieve needs primes only through 4,410,000. The first 20 samples are summed directly. Every reported inequality was checked independently with 128-bit and 192-bit Arb arithmetic. [Python certificate](spectral-interpolation-mod4-deficit.py) · [128-bit receipt](spectral-interpolation-mod4-deficit-128.receipt) · [192-bit receipt](spectral-interpolation-mod4-deficit-192.receipt).

Put \(L(s)=\beta(s)=\sum_{n\ge0}(-1)^n(2n+1)^{-s}\), \(A=-L'/L\), \(\ell=\log(4/\pi)\), and \(C(x)=\sum_{k\ge2,p^k\le x}\chi(p)^k\log p\,(x-p^k)\). The completion \(\Lambda(s)=(4/\pi)^{(s+1)/2}\Gamma((s+1)/2)\beta(s)\) is entire of order one and unchanged by \(s\mapsto1-s\). Its Hadamard identity at one yields
\[
 B=2\sum_\rho\Re\frac1{1-\rho}=2\frac{\Lambda'}{\Lambda}(1)
   =\ell-\gamma_E+2\frac{\beta'(1)}{\beta(1)}
   =0.1555679799235859288\ldots .
\]
The zeros include both signs and algebraic multiplicities. Each summand is positive. In particular the contribution of any collection of on-line zeros to \(\sum |\rho(1+\rho)|^{-1}\) is at most \(B\), since on the line \(2\Re(1/(1-\rho))=1/|\rho|^2\). This comparison allows off-line zeros outside the verified strip. [Rubinstein and Sarnak, *Chebyshev's Bias*, §4.3](https://www.math.uwaterloo.ca/~mrubinst/publications/Chebyshev.pdf).

For \(x>1\), with \(a_0=A(0)\) and \(a_1=\operatorname{fp}_{s=-1}A(s)\), the triangular Perron kernel gives
\[
 S(x)+C(x)=
 -\sum_\rho \frac{x^{1+\rho}}{\rho(1+\rho)}
 +a_0x+1+\log x-a_1
 -\sum_{m\ge1}\frac{x^{-2m}}{(2m+1)2m}.
\]
Its kernel vanishes at an upper endpoint that is a prime power. For the sign of the collision at \(s=-1\), put \(s=-1+h\). The two Laurent expansions are \(A=-1/h+a_1+O(h)\) and \(x^{s+1}/[s(s+1)]=-1/h-1-\log x+O(h)\). The functional equation gives \(a_0=\ell-\gamma_E-\log2+\beta'(1)/\beta(1)\) and \(a_1=\ell-\gamma_E-\log2+1+\beta'(2)/\beta(2)\). The last series has absolute value less than one for \(x\ge2\). For a contour justification shift to the left between two successive negative odd integers, using the functional equation, Stirling's formula and heights bounded away from the completions' zeros. The Riesz denominator makes the horizontal integrals vanish and the zero sum absolutely convergent. Letting the negative real part go to minus infinity kills the remaining vertical integral when \(x>1\).

Platt's verified height here is \(H=10^8/4=25{,}000{,}000\). Write \(N(t)\) for the count with \(|\Im\rho|\le t\). For \(t\ge H\) the explicit zero-count bound implies \(|N(t)-t\log(2t/(\pi e))/\pi-1/4|\le \log t\). Indeed its \(\ell'=\log(4(t+2)/(2\pi))\) satisfies \(0<\ell'\le\log t\), and \(0.22737u+2\log(1+u)-0.5\le u\) for \(u\ge16\). Stieltjes integration gives
\[
 \sum_{|\gamma|>H}\gamma^{-2}
 =-N(H)/H^2+2\int_H^\infty N(t)t^{-3}\,dt
 \le K_H=\frac{\log(2H/(\pi e))+2}{\pi H}
    +\frac{2\log H+1/2}{H^2}<2.238713\cdot10^{-7}.
\]
Pair \(\beta+i\gamma\) with \(1-\beta+i\gamma\) at each height. Convexity shows the average of \(x^{\beta-1/2}\) and its reciprocal is at most \((\sqrt x+1/\sqrt x)/2\). This includes the fixed points on the line. Bound each high denominator below by \(\gamma^2\). Thus for \(x\ge2\),
\[
 |S(x)+C(x)-(a_0x+1+\log x-a_1)|
 \le 1+x^{3/2}\{ B+(\sqrt x+1/\sqrt x)K_H/2\}.
\]
The script computes \(C(j^4)\) exactly up to enclosed logarithms, with the signs of **all** powers. The smallest certified lower bound for \(-S(j^4)/j^6\) and largest upper bound for \(D(J)/J^7\) occur at the upper endpoint in this certificate. The latter is \(0.172616936\) rounded upward. [Platt's verification, Theorem 7.1](https://arxiv.org/pdf/1305.3087) · [Bennett, Martin, O'Bryant and Rechnitzer, Theorem 1.1](https://arxiv.org/pdf/2005.02989).

## Asymptotic drift and an unconditional nonprincipal endpoint

If GRH holds for this one character, the prime-square PNT gives \(C(x)=(2/3+o(1))x^{3/2}\). Indeed the square contribution is \(\int_0^{\sqrt x}2u\theta_{\rm odd}(u)\,du\), and all terms of exponent at least three are \(O(x^{4/3}\log^2(2x))\). The entire nontrivial-zero sum has modulus at most \(Bx^{3/2}\). Thus \(S(x)<0\) for every sufficiently large real \(x\), and clipping changes only finitely many sampled terms. A uniformly convergent series then describes the *actual* deficit on this hypothesis:
\[
 \frac{D(J)}{J^7}=\frac{2}{21}+P(\log J)+o(1),\qquad
 P(y)=\sum_\rho
 \frac{e^{4i\gamma y}}{\rho(1+\rho)(7+4i\gamma)} .
\]
For each fixed \(\gamma\), partial summation or Riemann sums give the multiplier \((7+4i\gamma)^{-1}\) at \(j=J\). The normalized partial sums all have modulus bounded by \(J^{-7}\sum_{j\le J}j^6\le1\), so the absolutely summable first-Riesz coefficients justify passing to the full series. By interval evaluation the Hardy function stays positive on \([0,6]\), and is negative at 6.1. Platt's verification and these segment enclosures give \(|\gamma|>6\) for all zeros, and at least one zero with \(6<\gamma<6.1\). Thus \(|P|\le B/25\) since \(|7+4i\gamma|\ge25\). Under GRH the limiting range is contained in
\[
 [\,2/21-B/25,\ 2/21+B/25\,]
 =[\,0.08901537604115\ldots,\ 0.10146081443503\ldots\,].
\]
These are bounding endpoints. No claim is made that simultaneous zero phases attain them.

The continuous almost periodic function \(P\) has logarithmic mean zero. Its coefficient at any one of the located ordinates is at least
\[
 a_*=[((6.1)^2+1/4)((6.1)^2+9/4)(49+16(6.1)^2)]^{-1/2}
      >0.00102464.
\]
Coincident ordinates on the critical line add with positive multiplicity. For any bounded nonnegative almost periodic \(f\), its mean dominates the modulus of each coefficient. Apply this to \(\sup P-P\) and \(P-\inf P\). Consequently \(\sup P\ge a_*\) and \(\inf P\le-a_*\). Almost periodic recurrence and \(\log(J+1)-\log J\to0\) transfer these extrema arbitrarily closely to the discrete grid. This gives oscillations at least \(0.00102464\) to both sides of \(2/21\) on the GRH branch.

If the character has any exterior zero, the previously published all-field every-prefix theorem gives \(D(J)/J^7\to+\infty\). Combining the two exhaustive cases gives \(\liminf D(J)/J^7\ge2/21-B/25\) **unconditionally**. The quotient cannot converge to any finite constant. In particular the nuisance maximum with 7 in the all-field power-law formula can be dropped at this nonprincipal endpoint. The lower floor rules out \(o(J^7)\) even on an arbitrary unbounded subsequence. It leaves the requested upper estimate open beyond the finite certified range. [All-field every-prefix theorem, PR 7628 research proof](https://github.com/willzh0/riemann-masullo/blob/719213f260386a753004ab3b23596c8caa0f42c5/research/5571/fourth-power-deficit-boundary/subsequence.md).

The derivation is classical. The interval receipts use python-flint 0.9.0, direct native FLINT Dirichlet-function Taylor coefficients and Hardy interval evaluations, plus elementary Eratosthenes sieving. The cited Platt and zero-count theorems are external mathematical inputs. No statement in this report is asserted as a new Lean theorem.
