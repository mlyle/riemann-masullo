# Consecutive shallow and deep fourth-power samples for the character modulo four

Let χ be the primitive character of conductor four, S(x)=Σₚχ(p)log p (x−p)₊, and d(j)=max(0,−S(j⁴))/j⁶. For every 0<ε<1 and every sufficiently large real J, the interval
\[
 [J,\;4J(\log J)^{1/4}]
\]
contains a block of at least ⌊J^(1−ε)⌋ consecutive integers with **d(j)<0.65918 throughout**, and another such block with **d(j)>0.67415 throughout**. This is unconditional for the fixed genuine character. It excludes a permanently deep run and a permanently shallow run in those windows. It does not upper-bound Σ_{j≤J}j⁶d(j) by J⁷ on an unbounded sequence. [Interval script](spectral-interpolation-mod4-shallow-runs.py) · [128-bit replay](spectral-interpolation-mod4-shallow-runs-128.receipt) · [192-bit replay](spectral-interpolation-mod4-shallow-runs-192.receipt).

## A positive kernel retaining a certified critical zero

Write β(s)=L(s,χ), Λ(s)=(4/π)^((s+1)/2)Γ((s+1)/2)β(s), and let z=s−1/2. With a=π/4, set
\[
 K(t)=2e^{3t/2}\sum_{n\ge0}(-1)^n(2n+1)e^{-a(2n+1)^2e^{2t}}
      =2e^{3t/2-ae^{2t}}\prod_{m\ge1}(1-e^{-2\pi m e^{2t}})^3 .
\]
The derivative version of Jacobi's product gives the second identity. Poisson summation for the odd primitive character, equivalently the η transformation, makes K even. The bilaterally transformed function ∫K(t)e^{zt}dt is Λ(1/2+z). Indeed u=e^(2t) gives its gamma integral when Re(s)>1; evenness and the doubly exponential tails extend the identity to all z. K is strictly positive and strictly decreasing on (0,∞). To see monotonicity, log K is strictly concave: every term log(1−exp(−b exp(2t))) has derivative 2v/(exp(v)−1), v=b exp(2t), which decreases strictly. The linear term has zero second derivative and the leading negative exponential is strictly concave. Passing to the locally convergent series preserves concavity. Evenness gives the required decrease. [Jacobi, *Fundamenta nova*](https://www.digitale-sammlungen.de/en/details/bsb10053556) · [Derivative product, DLMF 20.4.2](https://dlmf.nist.gov/20.4.E2) · [Odd-character Poisson formula, Koukoulopoulos, proof of Theorem 11.1](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).

Let γ∈(6.02094890469,6.02094890471) be a critical zero ordinate, ρ=1/2+iγ. The Hardy function has strictly opposite signs at the endpoints, and the Arb enclosure of β′(1/2+it) throughout the box has modulus >1, so any such zero is simple. Define
\[
 V(t)=\int_0^\infty K(t+u)\frac{\sin(\gamma u)}{\gamma}\,du.
\]
For t≥0 it is strictly positive by pairing successive sine half-waves using strict decrease of K. On the whole line the same function is also ∫₀∞K(t−u)sin(γu)/γ du: the difference of the two formulas is a linear combination of the full cos/sin moments at γ, which vanish. Hence V is even and positive everywhere. Its two tail formulas give V≪K. In detail, for t,u≥0 the first alternating terms imply
\[
 K(t+u)/K(t)\le (1-3e^{-2\pi})^{-1}
     \exp(3u/2-a(e^{2u}-1))\le (1-3e^{-2\pi})^{-1}e^{-\pi u^2/2}.
\]
By differentiating the right-tail integral written with lower endpoint t, V″+γ²V=K. The same tails control V′. Integration by parts therefore gives the entire transform Λ(1/2+z)/(z²+γ²), at its removable points by continuity. In particular M=∫V=Λ(1/2)/γ²>0.

## From the signed mean to physical cutoffs

Write F(y)=e^(−3y/2)S(eʸ). The [exact integrated explicit formula](spectral-interpolation-mod4-deficit.md) gives for y≥0
\[
 F(y)=-\Re\sum_\omega\frac{e^{(\omega-1/2)y}}{\omega(1+\omega)}
      -\frac23+R(y),\qquad R(y)\to0 ,
\]
where R is bounded there. The signed prime squares contribute (2/3+o(1))x³ᐟ² by the ordinary PNT over odd primes. All higher prime powers and the real archimedean terms are lower order. The sum is over nontrivial zeros with multiplicities and Σ|ω(1+ω)|⁻¹<∞. At y<0 the actual S vanishes, while the absolute spectral terms grow by at most a constant times exp(|y|/2). Convolution with V/M keeps this far-left contribution o(1). Absolute summability and the two kernel tails justify termwise integration. Only ρ and its conjugate survive. Thus
\[
 \int_{\mathbb R}F(y+t)V(t)\,dt/M
   =-2/3+A\cos(\gamma y+\phi)+o(1),\qquad
 A=\frac{\gamma|\Lambda'(\rho)|}{\Lambda(1/2)|\rho(1+\rho)|}.
\]
The constant phase includes the residue signs. The interval computations give 0.00749220<A<0.00749222, 2/3−A<0.65918, and 2/3+A>0.67415, all strictly.

Let B=(1/2)log(16log J) and choose center y between 4log J+B+1 and 4log J+B+2.1. This center interval contains both a maximum and a minimum phase on separate choices since 2π/γ<1.1. On either choice the absolute contribution from |t|>B tends to zero: |F(y+t)|≪1+exp((y+t)/2), K(t)≪exp(−(π/8)exp(2|t|)), and (π/8)exp(2B)=2πlog J. The latter dominates y/2=2log J+O(log log J), including the integrable tail in t. The same truncation holds for V. Positivity and its normalized mass give a real cutoff with F above the shallow threshold and another below the deep threshold by a fixed positive margin. Both fourth roots of these cutoffs lie in the interior range
\[
 e^{1/4}J\le x^{1/4}\le 2e^{2.1/4}J(\log J)^{1/4}
        <3.39J(\log J)^{1/4}.
\]

There is also a direct, unconditional transfer of these *fixed-level* excursions from real cutoffs to their adjacent physical fourth powers. Between b=j⁴ and c=(j+1)⁴, randomly choose b or c with weights giving expectation x. The centered interval-prime identity in the signed short-interval estimate yields uniformly
\[
 S(x)=\frac{c-x}{c-b}S(b)+\frac{x-b}{c-b}S(c)+o(x^{3/2}).
\]
Indeed, the displacement is O(x^(3/4)); for t<x^0.70 the absolute integer count costs O((t+1)log(2x)), and for larger t the signed interval PNT gives o(t) uniformly. The integral in t is o(x³ᐟ²). Endpoints at primes change neither the integrated comparisons nor the cancellation of the tangent. Since b/x,c/x→1, strict margins survive at some adjacent sample. This interpolation conclusion holds without any hypothesis on high zeros. For the interval PNT, apply the truncated explicit formula at both endpoints with T=x^0.31. Ramaré’s fixed-modulus density estimate N(σ,T)≪T^{3(1−σ)}log^K T and the fixed-character Vinogradov–Korobov region imply a stretched-log relative saving: each zero costs O(x^{Re ρ−1}) after division by the interval length, and 3·0.31<1. The truncation is O(x^0.69 log²x), covered by the lengths at least x^0.70. Slight changes of these exponents give the same result for any fixed interval-length power θ>2/3. [Ramaré, Theorem 1.1](https://ramare-olivier.github.io/Maths/DensityEstimate-34.pdf) · [Khale, Theorem 1.1](https://arxiv.org/pdf/2210.06457).

## Why the excursions last for almost a linear number of indices

Let Θ=sup Re ω. The actual prime sum satisfies, for every η>0 and real k≥2,
\[
 \left|\frac{d}{dk}\frac{S(k^4)}{k^6}\right|\ll_{\chi,\eta}k^{4\Theta-3+\eta}
 \quad\text{almost everywhere}.
\]
Use the explicit formula for ψ(x,χ) at height x: the nontrivial zero term is O(x^Θlog²x) by Σ_|γ|≤x 1/|ρ|=O(log²x), and the endpoint remainder is O(log²x) at fixed modulus. Removing other powers costs O(√x log²x). Therefore S′(x)=Oη(x^{Θ+η}) off the prime jumps, and S(x)=Oη(x^{1+Θ+η}). The function itself is locally absolutely continuous, so its derivative bound integrates across prime breakpoints. [Koukoulopoulos, Theorem 11.3](https://dms.umontreal.ca/~koukoulo/documents/publications/primes.pdf).

If Θ=1/2, the bound is Oη(k^(−1+η)). Choosing η<ε/2 gives o(1) total variation over J^(1−ε) steps in the displayed range. The two fixed level margins persist throughout the two integer blocks.

If Θ>1/2, choose an actual right-hand zero ω with β=Re ω>1/2 and 4(Θ−β)<ε/4. Put α=β−1/2, g=|Im ω|, m=ord ω. No positive real β(s) zero occurs since its alternating series is strictly positive for real s>0. The verified conductor-four rectangle ensures all right-hand zero ordinates satisfy g>25,000,000, in particular 2π/g<1.1. There is a strictly positive kernel, bounded above by a constant times K, which kills every nontrivial zero in the spectral sum except β±ig. Here is an explicit construction permitting multiplicities.

For a real H bounded in modulus by CK and whose transform vanishes at α±ig, form its right-tail inverse
\[
 D H(t)=\int_0^\infty e^{\alpha u}\frac{\sin(gu)}gH(t+u)\,du .
\]
It agrees on the entire line with the left-tail expression using e^(−αu)H(t−u). The two full exponential moments at α±ig vanish. In each appropriate half-line the displayed K(t+u)/K(t) estimate (or its reflection), even after multiplication by exp(|α|u), gives |DH|≪K. Its derivative has the same two-sided decay. The ordinary differential identity ((d/dt+α)²+g²)DH=H follows by differentiating tails. Thus its bilateral transform is the transform of H divided by (z−α)²+g². Iterating m times beginning with K is legitimate, as the zero order drops by one each time. Then K+λDᵐK is strictly positive for any sufficiently small nonzero real λ. Its transform still vanishes at all the other zeros and is nonzero at α±ig.

Convolving F with this normalized positive kernel yields a nonzero real cosine of frequency g times exp(αy), plus the bounded drift and o(1). Its amplitude includes the strictly positive multiplicity m. Selecting both phases and truncating exactly as above produces actual real cutoffs where S(k⁴)/k⁶ is respectively ≥cJ^(4β−2) and ≤−cJ^(4β−2), with c>0 depending on the chosen zero. The derivative estimate on the enlarged localization interval is O(J^(4Θ−3+2η)), including its fixed power of log J after a harmless change of η. On any adjacent J^(1−ε) steps its cumulative variation is O(J^(4Θ−2−ε+2η)), strictly smaller than the detected magnitude when η<ε/8. Those contiguous blocks satisfy the claimed fixed thresholds, and their margins from both shell endpoints accommodate all those steps. The two cases cover all possibilities for this fixed character without assuming GRH in the conclusion.

## What local curvature alone allows

Fix any finite prime prefix N and any 0<δ<1/2. Keep the coefficients χ₋₄(p) through N. Starting with the next odd prime, round the cumulative target sums Σ(1−p^(−δ))/2 down to integers. On a floor increment set aₚ=1 and otherwise aₚ=−1. Extend these real unit signs completely multiplicatively on odd integers and keep a₂=0. Every interval of larger primes satisfies |Σ(aₚ+p^(−δ))|≤2 by telescoping, and partial summation gives log-weighted interval discrepancy O(log(2x)) for endpoints comparable to x. Thus every window of length x^0.70≤t≤x/2 has centered signed first-prime weight O(t x^(−δ)log x+log x), smaller than the relative stretched-log bound used in the genuine short-interval curvature estimate. The construction can agree on any prescribed finite cutoff.

Nevertheless the ordinary PNT and summation by parts give
\[
 S_a(x)\sim-\frac{x^{2-\delta}}{(1-\delta)(2-\delta)},\qquad
 D_a(J)\sim\frac{J^{9-4\delta}}{(1-\delta)(2-\delta)(9-4\delta)}.
\]
Indeed the signed Chebyshev sum is −Σₚ≤ₓp^(−δ)log p+O_N(log(2x)), asymptotic to −x^(1−δ)/(1−δ). Integrate once and sum at j⁴. These genuine prime-supported weights obey even stronger signed curvature and local PNT estimates, while every sufficiently large sample is deeply negative. They are not the Hecke character: their global signed Chebyshev bias forces a real-axis Mellin singularity, excluded for the actual β function. Local curvature and all finite prime checks alone therefore cannot justify an upper bound for the cumulative deficit. The positive θ identity uses precisely additional arithmetic structure. The almost-linear shallow blocks from that identity still leave room for much larger deficits elsewhere in the same shells.

The numerical inputs above are rigorous Arb enclosures. The kernel division, interpolation and consecutive-block results are classical arguments on paper, separate from the [formal arithmetic tangent and curvature bounds](https://github.com/mccorvie/riemann-masullo/pull/7653).

## A fixed ratio when its numerical value is left unspecified

There is also a finite Cχ>1, independent of ε, for which each of the two blocks occurs in every sufficiently large [J,CχJ]. The preceding completely specified 4(log J)^(1/4) window avoids choosing Cχ from unknown zeros. This qualitative fixed-ratio improvement applies a previously available compact selector to the present modulus-four prime statistic. [Earlier fixed-window construction on the rational square prefixes](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md).

If Θ=1/2, the absolutely convergent critical zero series makes F uniformly bounded for y≥0. In the proof with V, a sufficiently large fixed B makes both tails smaller than half the fixed harmonic margins, uniformly as y→∞. The part with y+t<0 is simply zero. This gives a fixed shell and the derivative argument gives the block lengths there.

If Θ>1/2 fix σ with 1/2<σ<Θ. Fixed-conductor zero density gives Σ_{β≥σ,γ>0}1/γ<∞, counting multiplicities. For y large and true F as above, construct a positive compact probability measure by convolving, for each such zero, the two-point probability on 0,π/γ whose weights have ratio exp((β−1/2)π/γ) to one. Each factor kills z=(β−1/2)±iγ. Their independent increments have a summable deterministic length, so the infinite convolution is a probability of compact support. Convolve with a nonnegative smooth compact probability bump to obtain a bounded density K₀ on a fixed interval I. Its transform is nonzero at zero, hence its zero orders at any selected z are finite. Convolve K₀ with a uniform probability on an interval centered at zero and long enough to cover all of I−I. The resulting bounded probability density P has the same transform zeros and is a positive constant on I. [Montgomery, *Topics in Multiplicative Number Theory*, zero-density estimates](https://link.springer.com/book/10.1007/BFb0060851) · [Compact-support construction](https://github.com/mlyle/riemann-masullo/blob/69f6639d0e53c2a04aa3b5f8487a1be237274b97/research/5571/square-prefix-fixed-window-count/README.md).

For each chosen z₀=β−1/2+iγ with β>σ, divide the transform of K₀ by (z−z₀) raised to its full zero order there. The inverse is bounded and supported on the same I: successive complex right-tail primitive integrals vanish to the left because the matching exponential moment vanishes. Thus its absolute value is ≤C(z₀)P. The P average of F is O(exp((σ−1/2)y)+1). The complex quotient average equals a nonzero coefficient times exp(z₀y), with an error of that same smaller order; only the selected member of the pair is retained. The latter forces the P average of |F| to be ≫exp((β−1/2)y), and the former forces each sign to have this lower order. All support intervals are fixed independently of the subsequent β selection. Enlarge the resulting fourth-root ratio slightly to leave room for the derivative argument and choose β near Θ as before. This proves the fixed-ratio assertion for all ε. If Θ is unattained, taking σ↑Θ drives the sum of the two-point support lengths to zero by dominated convergence. An arbitrarily small bump then gives the same result on every prescribed [J,(1+δ)J], δ>0 fixed.

## Even density-one agreement and the genuine positive residue class are insufficient locally

A different construction preserves the true positive-prime support condition throughout. Fix N≥3 and 0<δ<1/2, agree with χ through N and set B=0. At each subsequent prime p tentatively add (χ(p)+p^(−δ))log p to B. If the tentative value is positive, choose aₚ=−1 and subtract 2log p from that tentative value. Otherwise choose aₚ=χ(p) and accept the tentative value. Extend multiplicatively from the primes with a₂=0. A flip can take place only when χ(p)=1, since B≤0 and p^(−δ)<1. After a flip B lies in (−2log p,0); at other steps B stays nonpositive. In particular every p with aₚ>0 is a genuine p≡1 (mod 4), and all good-prime Euler coefficients are real unit signs.

For every x>N, defining Θₐ(x)=Σₚ≤ₓaₚlog p gives
\[
 \Theta_a(x)\le O_N(1)-\sum_{N<p\le x}p^{-\delta}\log p .
\]
After integrating this pointwise inequality and applying the ordinary prime number theorem,
\[
 S_a(x)\le -(1+o(1))\frac{x^{2-\delta}}{(1-\delta)(2-\delta)},\qquad
 \liminf_{J\to\infty}D_a(J)/J^{9-4\delta}
 \ge[(1-\delta)(2-\delta)(9-4\delta)]^{-1}.
\]
Here the first display means the corresponding normalized upper limit is at most the indicated negative constant. The stronger exact asymptotic earlier in the note is for the unconstrained rounding rule, not this one.

The flip operation also preserves the useful short-interval bounds. For I=(x,x+h], h≤x/2, let E(I)=2Σ_{p flipped in I} log p. If at least one flip occurs, take the last such p₀. The balance at x is nonpositive and B(p₀)>−2log p₀, so
\[
 E(I)\le 2\log(2x)+
 \sup_{x\le t\le x+h}\left(\sum_{x<p\le t}\chi(p)\log p\right)_+
 + \sum_{x<p\le x+h} p^{-\delta}\log p .
\]
This holds trivially for a flip-free interval. The last term is O((h+1)x^(−δ)log(2x)). For h≥x^θ with θ a fixed number close below 3/4, use the genuine χ short-interval PNT on prefix lengths ≥x^{θ′} for any 2/3<θ′<θ and elementary counting below that. By choosing θ′ sufficiently close to θ in the previous proof, all the stretched-log estimates there pass through, including each exponent with arbitrary positive slack. The new signed interval differs from the original by exactly −E(I). For the global flip count start the same last-flip argument at N and allow all t≤x. The ordinary PNT for the genuine χ gives sup_{t≤x}|Θχ(t)|=o(x), while Σp^(−δ)log p is o(x). Thus the total flipped log weight is o(x), and the altered signs agree with χ on a natural-density-one subset of the primes. For the last deduction, primes ≤√x are negligible in prime count and every larger flipped prime costs at least (log x)/2.

The altered signs cannot form a Dirichlet character: any different periodic character disagrees on a positive density of primes by the PNT in its joint modulus, and the preceding genuine-character shallow blocks rule out equality away from finitely many primes. This uses no assumption about high β zeros. Therefore permanence of a large negative bias is compatible with the local estimates even when the genuine positive class, the order-two Euler factors, an arbitrarily long exact initial prime segment, and density-one agreement with the target are all retained. The true character's periodicity and completed transform supply substantive information beyond these conditions.
