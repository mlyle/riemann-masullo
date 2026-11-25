# Square-root lower excursions of the two-cosine first-prime error

## Result and scope

Put \(w(t)=2-\cos t-\cos(\sqrt2t)\) and
\[
 E(x)=\sum_{p\le x}\log(p)w(\log p)-\int_1^x w(\log u)\,du .
\]
For \(B=2+2\cos(\pi/65)\bigl(1/(2\sqrt5)+1/6\bigr)\),
\[
 \liminf_{N\to\infty,\ N\in\mathbb N}\frac{E(N)}{\sqrt N}\le -B,
 \qquad B>2.77963542707368 .
\]
The same conclusion holds after replacing the continuous mean with \(\sum_{n\le N}w(\log n)\). The arithmetic estimate at every exponent strictly greater than \(1/2\) remains compatible with this result. This is a paper proof with a finite rigorous Arb computation. The separate [Lean join](https://github.com/mlyle/riemann-masullo/compare/55bfd9944976e016435ac2d8e357ead5650ff77f...8c19dd0f1b0224b6c960adb2580f922620a82521) proves the implication from first-prime estimates to zero exclusion.

## Euler factors and residues

Write \(a=1/2\), \(T=\{0,1,-1,\sqrt2,-\sqrt2\}\), \(c_0=2\), and \(c_t=-1/2\) for the four nonzero indices. Put \(P(s)=\sum_p\log(p)p^{-s}\) and \(L(s)=-\zeta'(s)/\zeta(s)\). Absolute convergence for \(\Re s>1\) gives \(L(s)=\sum_{k\ge1}P(ks)\). Consequently
\[
 P(s)= L(s)-L(2s)+
 \sum_{k\ge2}P(2ks)-\sum_{k\ge3}P(ks).
\]
Both last sums converge absolutely and locally uniformly on \(\Re s>1/3\). On a compact set with \(\Re s\ge b>1/3\), sum the geometric series in \(p^{-b}\) and dominate by a constant times \(\sum_{n\ge2}\log(n)n^{-3b}\). This continues the prime sum meromorphically there. At \(s=1\) it has residue \(1\). At \(s=a\), the term \(-L(2s)\) has residue \(-1/2\).

By integration by parts, for \(\Re s>1\),
\[
 M(s):=\int_1^\infty E(x)x^{-s-1}\,dx
 = \frac{1}{s}\sum_{t\in T}c_t
 \left(P(s-it)-\frac{1}{s-1-it}\right).
\]
The pole at \(s=1+it\) is removed with the same residue as the weighted prime density. On the real axis \(M\) is analytic for \(s>a\). For \(a\le u\le1,\ |v|\le\sqrt2,\ u+iv\ne1\), Euler–Maclaurin at 1, with \(|B_2(\{x\})|\le1/6\), gives
\[
 \left|\zeta(s)-\frac1{s-1}-\frac12\right|
 \le\frac{|s|}{12}\left(1+\frac{|s+1|}{u+1}\right)<\frac49.
\]
Indeed \(|s|<2,\ |s+1|<5/2,\ u+1\ge3/2\), while \(|1/(s-1)+1/2|=|s+1|/(2|s-1|)\ge1/2\). Thus all five \(L(s-it)\) have the required real-axis regularity except the canceled pole. At points of the line \(\Re s=1\) other than its simple pole at 1, zeta is nonzero. This controls \(L(2s-2it)\) on the boundary used below. [Hadamard, 1896](https://www.numdam.org/item/BSMF_1896__24__199_1/).

## A finite positivity test

Suppose \(E(x)+C\sqrt x\ge0\) eventually, and integrate this nonnegative function from some such cutoff \(A\ge1\). Its Mellin transform \(J(s)\) continues as \(M(s)+C/(s-a)\) up to an entire function. It has no real singularity on \((a,\infty)\). Its defining integral therefore converges absolutely on \(\Re s>a\). For completeness, if its real convergence abscissa \(b>a\) were finite, continuation across \(b\) would give a disk of analyticity about a real \(d>b\) extending to the left of \(b\). The Taylor coefficients of \(J(d-h)\) as a power series in \(h\) are the integrals of \((\log x)^n/n!\) against the nonnegative defining measure at \(d\). Monotone convergence for positive \(h\) inside that disk would give convergence to the left of \(b\), a contradiction. Initial convergence for \(\Re s>1\) follows already from \(E(x)=O(x\log x)\).

Take the \(64^2\) frequencies \(u_{k\ell}=k+\ell\sqrt2\), \(0\le k,\ell<64\). For \(\eta>0\) the Hermitian matrix whose entries are
\[
 \eta\,J(a+\eta+i(u_{k\ell}-u_{mn}))
\]
is positive semidefinite by integrating the squared modulus of the corresponding finite linear combination of \(x^{iu_{k\ell}}\). In the entrywise limit \(\eta\downarrow0\), each entry is a meromorphic residue, with zero at regular points. For every difference \(d=u_{k\ell}-u_{mn}\) and \(t\in T\), the ordinate \(d-t\) belongs to \(\{j+h\sqrt2:|j|,|h|\le64\}\). The attached certificate proves that \(\zeta(a+i(d-t))\ne0\) at all these finitely many ordinates. Therefore only the square-prime poles survive. The residue of \(M\) at \(a+id\) is \(-c_d/[2(a+id)]\) for \(d\in T\), and zero otherwise. In particular the diagonal of the limiting matrix is \(C-2\). Its two directed edge coefficients have magnitudes \(1/(2\sqrt5)\) and \(1/6\). Irrationality gives a unique integer-coordinate representation for each frequency difference, so the only nonzero off-diagonal entries connect nearest neighbours along one coordinate.

A diagonal unitary with linearly varying phases in \(k,\ell\) makes both edge coefficients positive real. The resulting matrix is
\[
 (C-2)I+\frac{1}{2\sqrt5}A_{64}\otimes I+
                \frac16 I\otimes A_{64},
\]
where \(A_n\) is the adjacency matrix of the path on \(n\) vertices. The sine vector with entries \((-1)^j\sin(\pi(j+1)/(n+1))\), \(0\le j<n\), has eigenvalue \(-2\cos(\pi/(n+1))\). Test with its two-coordinate product. Positivity forces \(C\ge B\). This proves the continuous-variable liminf. Replacing \(x\) by its integer part changes \(E(x)\) by at most four, since no additional prime occurs between consecutive integers and \(0\le w\le4\). Under a hypothetical lower bound at integer arguments this rounding preserves an eventual lower bound at real arguments after an arbitrarily small increase in the constant. The established \(O(\log N)\) error between the integral and discrete means also vanishes upon division by \(\sqrt N\). [Formal comparison of the two means](https://github.com/mlyle/riemann-masullo/blob/26726e5236b0053f61b5b0b4931552244d5dbe54/RiemannMasullo/Ch13_ZerosHecke/RationalCompensatedPrimeError.lean).

## Certificate

The verifier uses complex Arb balls at 128 bits, with a second replay at 192 bits. Conjugation reduces the \(129^2\) points to 8,321 checks. Both runs bound the minimum of the absolute values from below by \(0.0003530\). The analytic argument uses these pointwise enclosures only at the specified boundary ordinates. [Verifier](verify.py) · [128-bit receipt](receipt-128.txt) · [192-bit receipt](receipt-192.txt) · [Johansson's rigorous zeta algorithms](https://arxiv.org/abs/1309.2877) · [Arb ball arithmetic](https://arxiv.org/abs/1611.02831).

Reproduce with `uv run --no-project --with python-flint==0.9.0 python verify.py --precision 192`.
