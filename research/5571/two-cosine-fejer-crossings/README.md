# Bounded errors at arbitrarily late cutoffs for the actual two-cosine prime count

Let \(w(t)=2-\cos t-\cos(\sqrt2\,t)\), \(S=\{0,\pm1,\pm\sqrt2\}\), \(c_0=2\), \(c_{\pm1}=c_{\pm\sqrt2}=-1/2\), and \(a=1/2\). Write
\[
 E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log t)\,dt .
\]
Unconditionally, for integer cutoffs the limsup of \(E(N)/\sqrt N\) is at least \(0.1992738068088042\), and its liminf is at most \(-4.6489811143273203\). In particular \(-4<E(N)\le0\) for infinitely many integers \(N\). For the discrete mean, the bounded-error cutoffs can all be chosen composite. These conclusions also hold after replacing the integral with \(\sum_{n\le N}w(\log n)\). The two sets of cutoffs may differ. For real cutoffs the integral-compensated \(E(x)\) actually reaches zero arbitrarily late. This is an unbounded subsequence. The proof provides neither an upper bound on its gaps nor a bound on the error at all integer cutoffs. The result uses only classical finite-height zeta information.

## Prime, pole and time normalizations

Put \(P(s)=\sum_p\log(p)p^{-s}\) and \(L(s)=-\zeta'(s)/\zeta(s)\). For \(\Re s>1\),
\[
 M(s)=\int_1^\infty E(x)x^{-s-1}\,dx
 =s^{-1}\sum_{t\in S}c_t\big(P(s-it)-(s-1-it)^{-1}\big).
\]
The factor \(1/s\) is common to the five shifts. The identity \(P(s)=L(s)-L(2s)+\sum_{k\ge2}P(2ks)-\sum_{k\ge3}P(ks)\) gives meromorphic continuation to \(\Re s>1/3\); the two infinite tails converge normally there. On the real segment \(s>a\) the poles at one cancel; an Euler–Maclaurin bound excludes zeros of \(\zeta\) for \(1/2\le\Re s\le1,\ |\Im s|\le\sqrt2\). The zeta function is nonzero on \(\Re s=1\) except for its pole at 1. Therefore \(M\) is regular on the whole real ray \(s>a\).

At \(a+i v\), each positive or negative critical ordinate \(\gamma\), of multiplicity \(m_\gamma\), contributes a pole at \(v=\gamma+t\) with residue \(-m_\gamma c_t/(a+iv)\). The prime squares contribute five further residues \(-c_t/[2(a+it)]\) at \(v=t\). Coincident residues add. The real residue is \(-2\). The tails from prime powers of order three and higher are holomorphic at every point used. [Complete derivation and elementary low-ordinate bound](../two-cosine-square-drift/README.md) · [Hadamard on the 1-line](https://www.numdam.org/item/BSMF_1896__24__199_1/).

## One-sided Fejér bounds without RH

Write \(g(u)=e^{-au}E(e^u)\) for \(u\ge0\), extended by zero to negative arguments. Its Laplace transform is \(M(a+s)\) in the initial half-plane. Fix \(T>0\) with no pole at the band endpoints. Set \(\Phi_T(v)=(1-|v|/T)_+\). Its inverse Fourier transform is the nonnegative unit-integral kernel \(K_T(y)=(1-\cos(Ty))/(\pi T y^2)\), continuously extended at zero. Let \(R_v\) be all residues on the finite segment \(a+i[-T,T]\), and put
\[
 Q_T(y)=\sum_{|v|<T}R_v\,\Phi_T(v)e^{ivy}.
\]
Then \(\limsup_{u\to\infty} g(u)\ge Q_T(y)\) and \(\liminf_{u\to\infty}g(u)\le Q_T(y)\) for every real \(y\).

Here are details addressing one-sided convergence. Under a putative eventual upper bound \(g\le C\), delete a finite initial interval on which necessary. The tail Laplace transform of \(C-g\ge0\) agrees with \(C/s-M(a+s)\) up to an entire function. This has no real singularity for \(s>0\). Landau's positive-transform argument gives convergence of that tail integral for all positive real \(s\). Indeed, if its abscissa of convergence were positive, a Taylor series at a real point just to its right, inside a disk of continuation across the abscissa, would have nonnegative coefficients when expanded to the left. Monotone convergence would extend the integral through the abscissa. It follows that \(M(a+s)\) is the absolutely converging Laplace transform of \(g\) for \(\Re s>0\). Its meromorphic continuation has just a simple pole on the real axis at zero. Since \(\int_0^\infty (C-g(u))e^{-\eta u}du=O(1/\eta)\) as \(\eta\downarrow0\) up to the bounded initial contribution, positivity on the tail and \(e^{-u/U}\ge e^{-1}\) on \([0,U]\) give \(\int_0^U|g(u)|du=O(U+1)\).

For \(\eta>0\), absolute convergence and Fourier inversion give
\[
 \int_0^\infty e^{-\eta u}g(u)K_T(y-u)\,du
  =\frac1{2\pi}\int_{-T}^T\Phi_T(v)e^{ivy}M(a+\eta+iv)\,dv.
\]
Subtract on the right the finite principal parts \(R_\lambda/(\eta+i(v-\lambda))\). The difference tends uniformly on the compact segment to its continuous boundary value. Its inverse Fourier integral tends to zero as \(y\to+\infty\) by Riemann–Lebesgue. Each subtracted term is the convolution of \(K_T\) with \(R_\lambda e^{(-\eta+i\lambda)u}1_{u\ge0}\). Upon taking \(\eta\downarrow0\) and then \(y\to+\infty\), this equals \(R_\lambda e^{i\lambda y}\Phi_T(\lambda)+o(1)\). The first limit on the left follows by dominated convergence, using \(K_T(y-u)=O_y((1+u)^{-2})\) and the preceding linear \(L^1\) growth bound. Thus \((g*K_T)(y)=Q_T(y)+o(1)\). Because \(K_T\ge0\) has mass one and tends to zero away from its center, any eventual bound \(g\le C\) gives \(\limsup(g*K_T)\le C\). For any specified \(y_0\), finite-dimensional simultaneous recurrence supplies \(y_j\to+\infty\) with \(Q_T(y_j)\to Q_T(y_0)\). For instance, pigeonholing integer multiples of the finite list of frequencies modulo \(2\pi\) gives unbounded near periods, with exact periodicity also covered. Hence \(Q_T(y_0)\le C\). Repeat with \(-g\) for the lower inequality. No rational independence of ordinates enters this argument. The above is the elementary Fejér form of Ingham's oscillation method. [Ingham, *On two conjectures in the theory of numbers*](https://www.jstor.org/stable/2371685).

## Two rigorous sample values

For \(T=200\) the verifier encloses all indexed critical zeros through \(200+\sqrt2\). It finds 80 and verifies that zero 81 has ordinate greater than \(202.4935\). Consecutive indexed enclosures are disjoint. The 797 pole contributions include both signs of every in-band translated critical ordinate and all five square-prime terms. The code checks the side of the cutoff for each contribution and adds any coincidences by linearity. The argument requires the complete low zero list with multiplicities only on this finite band. FLINT's indexed zero isolation provides these enclosures. The published complete verification of the zeros up to \(3\cdot10^{12}\) far exceeds the band used. [FLINT rigorous zeta-zero isolation](https://flintlib.org/doc/acb_dirichlet/index.html) · [Platt and Trudgian, *The Riemann hypothesis is true up to \(3\cdot 10^{12}\)*](https://arxiv.org/abs/2004.09765).

At \(y_+=3005769/1000\) one obtains \(Q_{200}(y_+)=0.19927380680880423756\ldots\). At \(y_-=1423955/1000\) one obtains \(Q_{200}(y_-)=-4.64898111432732033679\ldots\). Both signs were established independently at 128 and 192 bits from the exact rational arguments. These are evaluations of a finite polynomial. The witnesses for the arithmetic error are furnished by the one-sided inequality and recurrence. [Verifier](verify.py) · [128-bit receipt](fejer-128.txt) · [192-bit receipt](fejer-192.txt).

## Quantized downward crossings

Rounding \(x\) down to \(N=\lfloor x\rfloor\) changes \(E(x)\) by at most four, since the count is constant on \([N,N+1)\) and \(0\le w\le4\). Changing the mean at integer \(N\) from the integral to the discrete sum introduces \(O(\log(N+1))\), by partial summation or the native comparison. Both corrections vanish after square-root normalization. For either integer mean, \(E(N+1)\ge E(N)-4\) since the summatory arithmetic mass has nonnegative increments and the step of the mean is at most four. Given \(M\), pick an \(n\ge M\) with \(E(n)>0\). There is a first \(N>n\) with \(E(N)\le0\), as negative values occur cofinally. This gives \(-4<E(N)\le0\). For the discrete mean a prime cutoff N≥3 adds (log(N)−1)w(log N)≥0, so a downcrossing at such an N must be composite. For the continuous mean, the error is continuous between consecutive primes and all jumps are upwards. A passage from a positive value to a strictly negative value on a finite interval therefore attains zero. [Arithmetic statistic and the comparison of means](https://github.com/mlyle/riemann-masullo/blob/26726e5236b0053f61b5b0b4931552244d5dbe54/RiemannMasullo/Ch13_ZerosHecke/RationalCompensatedPrimeError.lean).

More generally the same argument gives \(c\sqrt N-4<E(N)\le c\sqrt N\) cofinally for each \(-4.6489811143273203<c\le0\), because \(E(N)-c\sqrt N\) then has downward increments bounded by four. For \(0<c<0.1992738068088042\) the same downward passage has overshoot at most \(4+c/(\sqrt N+\sqrt{N-1})\). Thus the normalized cluster set contains the whole interval between the certified Fejér values.

## A simpler check after removing prime powers

Let \(S_2(x)=\sum_{k\ge2,p^k\le x}\log(p)w(k\log p)\). For \(V=E+S_2\) the above Mellin formula has \(L\) in place of \(P\). Its real residue at \(a\) is zero. If \(\rho=a+i\gamma\) is the first indexed zero, its translates by the four nonzero frequencies have nonzero zeta value, as verified at both precisions. Hence the nonreal residue at \(\rho\) is \(-2m_\rho/\rho\). For a putative eventual bound \(\pm V(x)\le C\sqrt x\), apply Landau positivity as above. The triangle inequality for the Laplace transform of \(C\mp e^{-au}V(e^u)\), started after a sufficiently large cutoff, gives \(C\ge 2m_\rho/|\rho|\) upon multiplication by \(\eta\downarrow0\) at heights zero and \(\gamma\). Thus \(V/\sqrt x\) has two-sided excursion of at least \(0.14140705546\), and \(-4<V(N)\le0\) infinitely often using its own downward step. [First-zero and four-translates verifier](verify-first-zero.py) · [128-bit receipt](first-zero-128.txt) · [192-bit receipt](first-zero-192.txt) · [Native full composite correction](https://github.com/mlyle/riemann-masullo/compare/951a318969dfccd6fbbac6687124ff330b626d13...50c33a73a02c4eca003b1d82b2abbaba752a0429).

## Entire intervals of controlled first-prime error

For every sufficiently large bounded-error crossing \(N\), take \(H=\lfloor\sqrt N\rfloor\). The Brun–Titchmarsh inequality with modulus 1 bounds the number of primes in each of \((N-H,N]\) and \((N,N+H]\) by \(2H/\log H\). Consequently, if \(N-H\le M\le N+H\), the absolute difference of the weighted prime counts at \(N,M\) is at most \(8H\log(N+H)/\log H\). The absolute difference of the two mean values, separately for either convention, is at most \(4H\). The two unsigned increments have the same orientation, so the difference between the *signed* errors is bounded by the maximum of these two bounds. Thus, at arbitrarily large \(N\),
\[
 \sup_{|M-N|\le\lfloor\sqrt N\rfloor}|E(M)|
 \le 4+\max\{4H,8H\log(N+H)/\log H\}
 =(16+o(1))\sqrt N .
\]
For the integral mean the supremum may range over real \(M\) in the given window as well, using the same prime intervals and the same bound on the change of the mean. For every \(\varepsilon>0\), the set of integers satisfying \(|E(M)|\le(16+\varepsilon)\sqrt M\) contains intervals of unbounded length. At every fixed \(r>1/2\) the supremum of \(|E(M)|/M^r\) over these intervals tends to zero. The centers supplied by the Fejér argument may be sparse. [Montgomery and Vaughan, *The large sieve*, Theorem 2](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf).

## Formal verification scope

A standalone Lean certificate proves the downward crossing theorem for both actual integral and discrete means with any nonnegative arithmetic coefficients. Two public specializations give the literal first-prime formulas. They assume the cofinal sign change established by the classical argument above. A further specialization locates the discrete crossings at composite integers. Each of the five checked roots has exactly the standard axioms propext, Classical.choice and Quot.sound. The Mellin continuation, Fejér inequality, interval calculations and Brun–Titchmarsh application are classical or external interval-arithmetic inputs. [Lean source](Crossings.lean) · [Axiom check](lean-axioms.txt).


Run `uv run --no-project --with python-flint==0.9.0 python verify.py --precision 192` to replay the two Fejér values. The Lean scratch certificate compiles against the public physical-statistic module at [commit 26726e5](https://github.com/mlyle/riemann-masullo/commit/26726e5236b0053f61b5b0b4931552244d5dbe54). The [global and finite-range bounds](classical-rates.md) cover the full finite verification range and the classical zero-free-region rate at infinity.
