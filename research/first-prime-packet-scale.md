# The sharp spatial resolution of the averaged signed first-prime statistic

Use $B(x)=1-\cos(x/2)$, $1/2<s<1$, $d>0$. The original numerator is

$$
 M(L)=\sum_{p\le e^L}(\log p)p^{-s}B(\log p)
       -\int_0^L e^{(1-s)x}B(x)\,dx .
$$

Its first-prime measure has exactly the mass from the one-sided normalized finite-place orbital term. Replace each point $p$ by any probability measure $\eta_p$ on $[1,\infty)$, replacing its entire summand by

$$
 (\log p)\int_{u\le e^L}u^{-s}B(\log u)\,d\eta_p(u).
$$

Keep the continuous term exactly as above, and denote the new statistic by $M_\eta$. The result below gives a uniform bound on the change of each positive- and negative-part integral over **all** choices of packets on the stated supports. [Exact finite-place normalization](one-sided-finite-place.md) · [One-sign criterion](https://github.com/mlyle/riemann-masullo/blob/f14d01f00a3b21cc18db8e22eb8ba7bd6adb51e2/research/first-prime-one-sided.md)

## Exact single-atom cost

Put $g(x)=e^{-sx}B(x)$. For $0\le x\le y$, compare the two cutoff rows $g(x)1_{\{L\ge x\}}$ and $g(y)1_{\{L\ge y\}}$. Their $L^1(e^{-dL}dL)$ distance is exactly

$$
 \frac{g(x)(e^{-dx}-e^{-dy})+|g(x)-g(y)|e^{-dy}}{d}.
$$

The two summands come from $[x,y)$ and $[y,\infty)$, respectively. Since $0\le B\le2$ and $|B'|\le1/2$, one has $|g(x)-g(y)|\le(2s+1/2)e^{-sx}(y-x)$. Therefore for either ordering of $x,y$ the row distance is at most

$$
 C_{s,d}e^{-(s+d)\min(x,y)}|x-y|,
 \qquad C_{s,d}=2+(2s+1/2)/d .
$$

This compares genuinely different sharp cutoffs and includes the change of the numerator at the relocated location.

## The packet bound and its arithmetic consequence

Jensen's inequality for the absolute value, followed by Tonelli for the nonnegative costs, gives

$$
 \int_0^\infty |M(L)-M_\eta(L)|e^{-dL}\,dL
 \le C_{s,d}\sum_p\log p\int
 \min(p,u)^{-(s+d)}|\log(p/u)|\,d\eta_p(u).
$$

First apply this to finitely many places, then pass to the limit. For the supports below each bounded cutoff sees only finitely many packets, making this passage immediate by Fatou. Both scalar maps $a\mapsto a_+$ and $a\mapsto a_-$ are 1-Lipschitz, so the same bound applies to the signed parts separately.

If $|u-p|\le p^\alpha$ for a fixed $\alpha<1$, then for all sufficiently large $p$ the last integrand is bounded by $C'_{s,d}p^{\alpha-s-d-1}$. This is summable with $\log p$ whenever $\alpha<s+d$. In particular every displacement of size $p^{s+o(1)}$ leaves the finiteness of **each** all-$d>0$ weighted one-sided integral unchanged, allowing nonuniform signs and arbitrary packet shapes. One concrete choice spreads $\log p$ uniformly over $[p,p+\log p]$. Its new density is the genuine coverage count $\sum_p1_{[p,p+\log p]}(u)$, and the entire atomic-to-coverage change has finite one-sided cost. The outstanding estimate compares the accumulated overlap of these intervals to their accumulated uncovered length.

## Sharpness for unrestricted positive packets

Suppose $s+d\le\alpha<1$. Choose repeated closed subintervals of the log phase, strictly inside bands where $B(x)\ge1$ and $B'(x)\le0$. For sufficiently large primes with log in these subintervals, set $u_p=p+p^\alpha$. Leave all other primes fixed. The shifted point stays in the same favorable band because $\log(u_p/p)\to0$. On the whole affected interval $g$ is decreasing, so the individual original-minus-shifted cumulative row is nonnegative at **every** $L$. Its exact weighted integral is

$$
 \frac{\log p}{d}\left[p^{-(s+d)}B(\log p)-u_p^{-(s+d)}B(\log u_p)\right]
 \ \ge c_{s,d,\alpha}(\log p)p^{\alpha-s-d-1}.
$$

The estimate follows by integrating the derivative of $u^{-(s+d)}B(\log u)$ on $[p,u_p]$. At every favorable phase period the prime number theorem gives the expected positive mass in the fixed relative interval. Summing over periods yields divergence also when $\alpha=s+d$. All contributions have the same sign, so the averaged positive difference really diverges. Shifting to the left within the same decreasing bands gives the corresponding result for the opposite sign.

Sharpness concerns the change under unrestricted redistributions. It does not imply divergence of either signed part of the original $M$. The bound shows exactly how much local rearrangement is harmless without input on the global compensation.
