# Centering the first-prime error on the gaps between consecutive primes

**25 November 2026.** For Theorem 12.5.1.1, pp. 519–520, fix rational zeta, $1/2<s<1$, $h=1/2$ and $B(x)=1-\cos(hx)$. Write $q=p_{\rm next}$, $g_p=q-p$. The following is a classical calculation.

### A signed sequence on primes

Put $a_p=(\log p-g_p)B(\log p)p^{-s}$ and $A_p=\sum_{r\le p}a_r$ with the sum over primes. For **either sign separately** and every $d>0$, exponential integrability of that sign of the original physical error
$$M(L)=\int_{[0,L]} B(x)e^{-sx}[d\vartheta(e^x)-e^x\,dx]$$
is equivalent to
$$\sum_p (p^{-d}-q^{-d}) (A_p)_\pm <\infty.$$
In particular, for one sign this last series converges for every $d>0$ exactly when there are no zeta zeros with real part $>s$. It is an estimate solely in terms of the primes, their successors and their running signed discrepancy. [One-sided criterion](https://github.com/mlyle/riemann-masullo/blob/f14d01f00a3b21cc18db8e22eb8ba7bd6adb51e2/research/first-prime-one-sided.md)

Indeed, move the Lebesgue mass on $[p,q)$ to the single point $p$; the interval $[1,2)$ contributes a bounded error. For $p\le u<q$, the $e^{-dL}dL$-integral of the absolute change in the cumulative contribution of one unit of mass is at most $C_{s,d}(u-p)p^{-1-s-d}$. To see this, split at $\log p$ and $\log u$. On the middle interval the cutoff mismatch costs at most $\|B\|_\infty p^{-s-d}\log(u/p)$. Above $\log u$, the derivative of $v^{-s}B(\log v)$ is $O_s(v^{-s-1})$, and the remaining exponential mass is $u^{-d}/d$. Integrate over $u\in[p,q)$ and sum. The total cost is at most a constant plus $C_{s,d}\sum_p g_p^2p^{-1-s-d}$. Stadlmann gives $\sum_{X\le p<2X}g_p^2\ll_\varepsilon X^{1.23+\varepsilon}$, using Bertrand to include the last endpoint if needed. Dyadic summation gives convergence for $s+d>0.23$. Taking either sign is 1-Lipschitz. The collapsed primitive equals $A_p$ on $[\log p,\log q)$, whose exact weighted length is $(p^{-d}-q^{-d})/d$. [Stadlmann, On the mean square gap between primes](https://arxiv.org/abs/2212.10867)

### Even these locally centered rows cannot be summed by sign

For every $t\le1$, both the positive and negative parts of $(\log p-g_p)B(\log p)p^{-t}$ have infinite sum. It suffices to prove the assertion at $t=1$.

For $p>2$, $g_p$ is even. Each log band $[4\pi k+\pi,4\pi k+3\pi]$ contains an interval $[m-1/4,m+1/4]$ centered at an odd integer, because its width exceeds $2+1/2$. Throughout the interval, $B\ge1$ and the distance from any even integer is at least $3/4$. The PNT gives $\gg e^m/m$ primes in the corresponding interval of prime sizes. Hence the sum of the absolute values at $t=1$ receives $\gg1/m$ from this band. The bands are disjoint and $m=4\pi k+O(1)$.

The signed series stays bounded as $t\downarrow1$ from above. For $\Re z>1$ write
$$
 Q(z)=\sum_p(\log p-g_p)p^{-z}
 =-\zeta'(z)/\zeta(z)-\sum_{p,k\ge2}(\log p)p^{-kz}
   -\bigg[\sum_p\left(g_pp^{-z}-\int_p^q u^{-z}\,du\right)
                 +\frac{2^{1-z}}{z-1}\bigg].
$$
The bracketed series of differences is locally uniformly convergent for $\Re z>0.23$, by the same gap-square bound and the derivative of $u^{-z}$. The elementary pole at one cancels the Euler pole. The higher powers are holomorphic for $\Re z>1/2$. Zeta has no zero at $1$ or $1\pm ih$, with its pole at $1$ removed as above. Thus $Q(t)-(Q(t+ih)+Q(t-ih))/2$ stays bounded through $t=1$. Meanwhile its absolute prime sum tends to infinity by monotone convergence. Its positive and negative prime sums must therefore both tend to infinity. This also proves the claim for all smaller $t$ by comparison. [Zero-free line](https://dlmf.nist.gov/25.10)

Consequently a bound by summing the favorable local signs fails even after assigning each prime its own full interval of continuous mean. Taking the sign after forming the running sum remains essential. No upper bound for that running signed discrepancy has been obtained.
