# A signed estimate on the density-one part of the original quartic cofactor sum

Fix either quartic Dirichlet character χ modulo five. For X large write L=log X, Φ(L)=L^(3/5)(log L)^(−1/5), S(t)=Σₚχ(p)log p·(t−p)₊, and N=X^0.21. Fix a smooth W between zero and one, equal to one on [0,1] and zero on [2,∞). The original complex sum is U(X)=Σₘ W(m/N)χ(m)m S(X/m). The n=1 coefficient equals one. The [complete periodic calculation](spectral-interpolation-periodic-prime-convolution.md) gives B(X)=Σₘχ(m)m S(X/m)≪X^(3/2)exp(−cΦ(L)). The absence of a real square-prime drift uses χ² nonprincipal.

## Uniform cutoff slack

Write U(Y,M)=ΣₖW(k/M)χ(k)kS(Y/k). The earlier reciprocal-prime proof gives U(Y,M)=B(Y)+Oε(Y^(1.48+ε)) uniformly for every M≥Y^0.209. To check, the discarded boundary uses p≤Y/M≤Y^0.791. Split off p≤Y^0.74 at cost O(Y^1.48), and take dyadic P in [Y^0.74,Y^0.791]. For retained 1≤|k|≤P^(1/7) the phase F=|k|Y/(5P) is at least (1/5)P^(209/791) and at most (1/5)P^(128/259), below the same first-derivative threshold by 3/518. The four per-dyadic costs are Y^(1/2)P^(7/6), P^(11/6), P^(5/2)/√Y, P^(13/7), with respective exponents at P=Y^0.791 equal to 8537/6000, 8701/6000, 591/400, 10283/7000. All lie below 1.48; the smooth error Y²/M³≤Y^1.373. If the upper cutoff is below Y^0.74, the short dyadics are simply absent. The constants in the partial summations use the same fixed W and do not depend on M. Thus for 1≤d≤X^0.001 one has N/d≥(X/d)^0.209 and the estimate applies at Y=X/d, always with the original W(m/N) after m=dk. This follows since .21−.209>.001(1−.209).

## The removed terms are an actual subset

Let y=10⁻⁴ log X and P(y)=∏_{p≤y}p. The elementary Chebyshev bound for θ(y) implies P(y)≤X^0.001 for all sufficiently large X. Möbius inclusion-exclusion gives exactly

\[
 \sum_{(m,P(y))=1} W(m/N)\chi(m)m S(X/m)
 =\sum_{d\mid P(y)}\mu(d)\chi(d)d\,U(X/d,N/d).
\]

For d≤X^0.001, Φ(log(X/d))≥c₁Φ(L) for a fixed c₁>0. Absolute summation of the main complete bound costs at most ∏_{p≤y}(1+p^(−1/2)), whose logarithm is O(√y)=o(Φ(L)). The polynomial truncation error costs at most ∏_{p≤y}(1+p^(−0.48))=exp(O(y^0.52))=X^o(1). Thus both the coprime sum displayed above and U(X) are O(X^(3/2)exp(−c₂Φ(L))). Their difference is the **original fixed-weight signed sum of exactly those m with a prime divisor ≤y**. It obeys the same upper bound in complex modulus. No cofactor weights have been altered on that subset. For any real T≥X^a with fixed a>0, inclusion-exclusion directly counts the survivors up to T as T∏_{p≤y}(1−1/p)+O(2^π(y)); here 2^π(y)=X^o(1) and the elementary Mertens product bound is O(1/log y). In particular their relative number tends to zero in every polynomial-size dyadic subinterval of the original cofactor support. This assertion is about the unweighted cofactor count; pointwise signs and clipped masses may concentrate in the survivors.

For X=j⁴ one can omit the removed signed sum while changing the cumulative physical clip by O(J⁷exp(−c₃Φ(log J))). This follows by 1-Lipschitz continuity of t↦max(t,0) before summing over j. The remaining naked-prime terms have no cofactor between 2 and y.

## A positive sieve with a larger gap and thinner average

For a small fixed λ>0 put R=exp(λΦ(L)). Let λ_d vanish beyond R and equal

\[
 \mu(d)\frac{\log^+(R/d)-\log^+(\sqrt R/d)}{(\log R)/2}
\]

elsewhere, with log⁺t=max(0,log t). Then |λ_d|≤1. Define w(m)=(Σ_{d|m}λ_d)². It is nonnegative and w(1)=1. For 2≤m≤√R, each divisor satisfies d≤√R and λ_d=μ(d), so w(m)=0.

Write ℓ=[d,e]. The joint weighted sum equals exactly

\[
 V(X)=\sum_m W(m/N)w(m)\chi(m)m S(X/m)
 =\sum_{d,e\le R}\lambda_d\lambda_e\chi(\ell)\ell\,U(X/\ell,N/\ell).
\]

Here ℓ≤R²=X^o(1), hence ℓ≤X^0.001 eventually. For the complete term one has Φ(log(X/ℓ))=(1+o(1))Φ(L) uniformly over every pair. The independent absolute cost of summing these measurements is ≤4Rζ(3/2), since for g=gcd(d,e) one may discard coprimality after d=ga, e=gb, then bound Σ_{a≤R/g}a^(−1/2)≤2√(R/g). The exponentially saved term in V is O(X^(3/2)exp(−c′Φ(L))) for each λ<c, c′<c−λ. For the cutoff error the crude ≤R² multiplier is already X^o(1). This also shows that the long signed weighted sum with factor 1−W(m/N) has a power saving Oε(X^(1.48+ε)) across all the long cofactors jointly.

Writing V−S and using the clip at X=j⁴ shows the physical deficit, up to O(J⁷exp(−c″Φ(log J))), equals

\[
 \sum_{j\le J}\left(\Re\sum_{\sqrt{R}<m\le 2j^{0.84}}w(m)W(m/j^{0.84})\chi(m)mS(j^4/m)\right)_+,
\]

with R chosen separately at each X=j⁴. Every remaining first-prime cutoff is ≤X/√R. The contribution from m≤√R vanishes identically apart from the anchor. Residual weights may exceed one, which is why the preceding exact-subset result is stated separately.

With Λ_R(n)=Σ_{d|n,d≤R}μ(d)log(R/d), one has w(n)=4(Λ_R(n)−Λ_{√R}(n))²/log²R. The second moment Σ_{n≤Y}Λ_R(n)²=Ylog R+O(Y)+O(R²) gives Σ_{n≤Y}w(n)≪Y/log R+R²/log²R. This applies in particular to every dyadic block of size ≥R², by positivity, with the same absolute implicit constant. Thus on every polynomial-size cofactor range the positive weights have mean O(1/Φ(log X)). No independent estimate for their remaining correlation with χ(m)mS(X/m) at the anchored exponent is proved here. [Goldston and Yıldırım, *Higher correlations of divisor sums related to primes I*, Theorem 5.1, equation (5.3)](https://math.colgate.edu/~integers/d5/d5.pdf).

The small average alone cannot exclude a coherent exterior frequency. At any fixed hypothetical zero ρ with β=Reρ>1/2, substituting the model input S*(t)=t^(1+ρ) gives the normalized multiplier Σ w(m)W(m/N)χ(m)m^(−ρ). Expand over the same least common multiples. Each inner smooth sum equals L(ρ,χ)+O_{k,ρ,W}((N/ℓ)^(1−β−k)) for every integer k≥1, by repeated integration against bounded periodic primitives. Since L(ρ,χ)=0 and ℓ≤R²=X^o(1), the entire multiplier is O_{A,ρ,W}(X^(−A)) for every A>0 by increasing k. Thus a thin remaining set of positively weighted cofactors can still match the negative of the anchor on an oscillatory input. This substitution tests the inference from the sieve bounds and does not assert the existence of an exterior zero.

A separate elementary version uses no reciprocal-prime estimates. For any real λ_d, d≤R, a nonprincipal character on a cofactor interval has weighted sum bounded by q(Σ|λ_d|)², since the interval of multiples of [d,e] is one complete-character row with a remainder of length <q. For each p≤X/(M+1), express (X−mp) on m>M as a sum over 0≤u<X of indicators mp≤u. Summing over primes now costs at most q(Σ|λ_d|)² X θ(X/(M+1)), including M=0. In particular, for any fixed η>0 and R=X^o(1) the actual unsmoothed weighted contribution of all m>X^(1/2+η) is O(X^(3/2−η+o(1))) on each cutoff X, by the elementary upper bound θ(t)≪t.
