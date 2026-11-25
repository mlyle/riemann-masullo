# The real axis of the fourth Gaussian angular Hecke L-function

On \(\mathbf Q(i)\) take \(\lambda((z))=\overline z^4/|z|^4\) in the canonical unitary normalization. Every Gaussian ideal is principal and multiplication by a unit preserves the value. Put
\[
 A(y)=\tfrac14\sum_{(a,b)\in\mathbf Z^2}\Re (a+bi)^4e^{-\pi y(a^2+b^2)}.
\]
Poisson summation gives \(A(y)=y^{-5}A(1/y)\). In the Fourier convention \(e^{-2\pi i x\cdot\xi}\), the planar Gaussian transforms to \(y^{-1}e^{-\pi |\xi|^2/y}\). Applying \((i/(2\pi))^4(\partial_{\xi_1}+i\partial_{\xi_2})^4\) multiplies the result by \(y^{-4}(\xi_1+i\xi_2)^4\) because the differential operator annihilates the linear factor between derivatives. The constant Fourier coefficient vanishes.

For \(y\ge1\), \(A(y)>\tfrac34e^{-\pi y}\). The first three coefficients are \(1,-4,0\). For \(n\ge4\) the absolute coefficient is at most \(n^2r_2(n)/4\le n^2d(n)\le n^3\). Since \(e^{-\pi}<1/20\), the relative absolute error is bounded by \(4/20+\sum_{n\ge4}n^3/20^{n-1}<1/4\) (successive terms in this tail have ratio less than \(1/10\)). Poisson summation now gives \(A(y)>0\) for \(0<y<1\) as well, and gives exponential decay up to a power at both ends.

Consequently \(\int_0^\infty A(y)y^{s+2-1}dy>0\) at every real \(s\). Termwise Mellin integration for \(\Re s>1\) identifies this convergent entire transform with \(\pi^{-(s+2)}\Gamma(s+2)L(s,\lambda)\), since each nonzero ideal has four generators and conjugation pairs up the imaginary parts. Analytic continuation gives the claimed positivity for the completion on the real critical segment. [CM normalization of the basic Gaussian character](https://sigma-journal.com/2018/090/sigma18-090.pdf).
