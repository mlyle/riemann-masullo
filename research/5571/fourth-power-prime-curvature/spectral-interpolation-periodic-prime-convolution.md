# A power-short multiplicative convolution for the fixed modulus-five variance

Let χ be a fixed nonprincipal Dirichlet character, q its modulus, and Sχ(x)=Σₚχ(p)log p (x−p)₊. Fix a smooth real W equal to one on [0,1], zero on [2,∞), with 0≤W≤1. For x≥2 let N=x^(21/100) and
\[
 B_{\chi,N}(x)=\sum_{n\ge1}W(n/N)\chi(n)n S_\chi(x/n),\qquad
 B_\chi(x)=\sum_{n\ge1}\chi(n)n S_\chi(x/n).
\]
Both sums are finite. Write Φ(u)=u^(3/5)(log u)^(−1/5) for large u. The unconditional estimates are
\[
 B_{\chi,N}(x)-B_\chi(x)=O_{q,W,\epsilon}(x^{1.48+\epsilon}),\qquad
 B_{\chi,N}(x)=-\tfrac23\mathbf1_{\chi^2=\chi_0} L(1/2,\chi)x^{3/2}
          +O_{q,W}\big(x^{3/2}e^{-c_q\Phi(\log x)}\big)
\]
for some c_q>0. A weaker proof using only two integrations against a periodic primitive requires N of order x^(1/4) to reach the same square-root scale. Here the largest arithmetic dilator at x=j⁴ is 2j^0.84. The upper bound is for a specific complex combination of actual first-prime sums. Taking the modulus of that combination or its negative real part preserves the estimate on a quartic character.

## Complete periodic convolution and its drift

Multiplicativity and the condition p|m give the exact finite identities
\[
 B_\chi(x)=\sum_{m\le x}\chi(m)(x-m)\log\operatorname{rad}(m),\quad
 \sum_n\chi(n)n\sum_{b\le x/n}\chi(b)\Lambda(b)(x/n-b)
   =\sum_{m\le x}\chi(m)(x-m)\log m .
\]
The full von Mangoldt expression is O_q(x). For example integrate twice against a bounded periodic second primitive of the mean-zero lattice measure Σχ(n)δₙ; the variation of the derivative of (x−t)log t on [1,x] is O(x+log x), including the endpoint terms. Put A(t)=Σ_{m≤t}χ(m)(t−m). Periodicity gives |A′(t)|≪_q off integer breakpoints and |A(t)|≪_q t. Removing powers of order at least three costs O_q(x^(4/3)log²(2x)), by counting the primes and exponents and using |pᵏ A(x/pᵏ)|≪_q x.

Write y=√x and G(v)=v² A(v^(−2)) for 0<v≤1. The square contribution is xΣ_{p≤y}χ(p)²log p G(p/y). G is bounded and is continuous with |G′(v)|≪_q/v on its smooth pieces. Partial summation and the fixed-modulus prime number theorem give the expression
\[
 \mathbf1_{\chi^2=\chi_0}xy\int_0^1G(v)dv
       +O_q\big(xy e^{-c_q\Phi(\log x)}\big).
\]
Primes below √y cost O(x√y); on the remaining interval use the PNT error O_q(t exp(−cΦ(log t))) and derivative bound O_q(1/t) after rescaling. For fixed q any bounded-height exceptional real zero gives a lower power that is absorbed as x tends to infinity. Furthermore G(v)=Σ_{m≤1/v²}χ(m)(1−mv²). The sums cut additionally at m≤M are uniformly bounded by partial summation of the monotone nonnegative weights. Dominated convergence then gives ∫G=(2/3)Σχ(m)/√m=(2/3)L(1/2,χ). This square contribution is subtracted to obtain the first-prime identity. [Fixed-modulus zero-free estimate, Khale](https://arxiv.org/pdf/2210.06457) · [The elementary prime-power Riesz formula and conventions](spectral-interpolation-mod4-deficit.md).

## Exact source of the cutoff error

Let h=1−W, defined to vanish also on the negative real line. The mean-zero periodic distribution Σ_{n∈ℤ}χ(n)δₙ has a continuous bounded period-q second primitive U₂ of mean zero. Its Fourier coefficients in the convention e(kt/q), e(t)=exp(2πit), satisfy c₀=0 and |cₖ|≪_q(1+|k|)⁻². This follows by dividing the finite periodic Gauss coefficients by (2πik/q)². Its mean-zero primitive U₃ is also bounded. For each prime p≤x/N apply the identity U₂″=Σχ(n)δₙ to (x−pt)₊h(t/N). Distributional integration by parts is legitimate at t=x/p, even when x/p is an integer: the function is continuous and the endpoint term is p h(x/(pN))U₂(x/p). The integral of the ordinary second derivative is
\[
 \int_0^{x/p} U_2(t)\left[(x-pt)h''(t/N)/N^2-2p h'(t/N)/N\right]dt .
\]
Integrating this against U₃′ costs O_{q,W}(p/N+x/N²). The endpoint at x/p contributes only O(p/N) and the smooth cutoff derivatives are supported on [N,2N]. This proof can equivalently use piecewise differentiable periodic primitives. Consequently
\[
 B_\chi(x)-B_{\chi,N}(x)
 =\sum_{p\le x/N}\chi(p)\log p\,p\,h(x/(pN))U_2(x/p)
       +O_{q,W}(x²/N³).
\]
Chebyshev bounds suffice for the last summation. The boundary frequency zero is absent through the deliberate choice of the mean-zero primitive.

## Uniform reciprocal-prime lemma

For P≤P′≤2P, P sufficiently large, let A be a nonzero real and F=|A|/P. For each fixed q and κ>0, uniformly for 1≤F≤P^(1/2−κ),
\[
 \left|\sum_{P<p\le P'}\chi(p)\log p\, e(A/p)\right|
 \ll_{q,\kappa,\epsilon} P^\epsilon
       \left(P^{2/3}\sqrt F+P^{5/6}+P/\sqrt F\right).
\]
The same proof handles a subinterval of [P,2P] with arbitrary endpoints. Apply Vaughan's identity with both cutoffs P^(1/3), and remove powers of order at least two at cost O(√P log²P). The coefficientwise identity can be written as
Λ=Λ_{≤V}+μ_{≤U}*log−μ_{≤U}*1*Λ_{≤V}+(μ_{>U}*1)*Λ_{>V}. The first term is empty on the selected interval. [Montgomery and Vaughan, Chapter 17, equations (17.5)–(17.9)](https://personal.science.psu.edu/rcv4/Vol2/Vol2.pdf).

* In a Type I piece, fix d≤P^(2/3). The free variable m is of size M=P/d. Separate its character into q residue classes. The second derivative of A/(dm) along each progression in the progression index has fixed sign and size comparable to q²F/M². The second-derivative test on any subinterval gives O_q(√F+M/√F) uniformly in both endpoints. A logarithmic coefficient on the free variable is removed by partial summation. Summing the small-divisor weights (bounded by log P or divisor bounds) gives O(P^ε(P^(2/3)√F+P/√F)).
* In Type II dyadically decompose the two variables. Both are ≫P^(1/3), and write M for the *shorter* dyadic length and D for the longer, so D≫√P and MD is comparable to P. All separated coefficients, including the character factors, have magnitude O(P^ε). Cauchy–Schwarz over D, expanding the shorter variables m,b, leaves a sum of a pure phase in the longer variable d. For fixed m,b the restrictions P<dm,db≤P′ and all dyadic cutoffs intersect in a single interval in d. The derivative of A(1/m−1/b)/d has constant sign, is monotone, and on this interval has absolute size comparable to F|m−b|/(MD). Its upper bound O(F/D) is <1/2 for large P by the specified fixed κ, so its distance from all integers is bounded below by a constant times F|m−b|/P. The first-derivative estimate gives O(P/(F|m−b|)). For the diagonal use O(D). Summing h=|m−b| gives O(P+MP log P/F) inside the expansion, up to P^ε factors. After the Cauchy factor D and the square root the bound is O(P^ε(P/√M+P/√F)), hence the claimed P^(5/6) term. This step never requires spacing between zeros or periodic coefficients in the longer-variable correlation.

Both derivative estimates also hold on intervals shorter than a full dyadic block; the usual second-derivative upper bound uses that shorter length in its first term and the same inverse-square-root term. [Montgomery and Vaughan, chapter on exponential sums](https://personal.science.psu.edu/rcv4/Vol2/Vol2.pdf).

## The phase and dyadic ledgers for the physical weight

Take N=x^0.21. The boundary contribution from p≤x^0.74 costs O(x^1.48) by boundedness of U₂ and Chebyshev. Partition the remaining primes into intervals starting at P=x^0.74 and doubling, ending at P′=min(2P,x^0.79); thus x^0.74≤P≤x^0.79 on every used interval. Expand U₂ in its absolutely summable Fourier series. The total from |k|>P^(1/7) is O_q(P^(13/7)) per interval, including the factor p. For 1≤|k|≤P^(1/7), put A=kx/q. Then
\[
 F=|k|x/(qP)\gg_q P^{21/79},\qquad
 F\ll_q P^{13/37+1/7}=P^{128/259}.
\]
The last exponent is strictly below 1/2 by 3/518. Dyadic constants can be absorbed by using any fixed κ<3/518. This checks uniformity over *every* sign and retained harmonic, including the smallest allowed P. The weight p h(x/(pN)) is O_W(P) and its total variation is O_W(P) on the interval since its derivative is h(t)−t h′(t). Partial summation therefore costs O_W(P), using the reciprocal-prime lemma with arbitrary upper endpoint. Since |cₖ|≪_q k⁻², the √F term incurs Σk⁻³ᐟ², and the 1/√F term incurs Σk⁻⁵ᐟ². The normalized bound per interval, with its factor p included, is
\[
 O_{q,W,\epsilon}\!\left(P^\epsilon\left[x^{1/2}P^{7/6}
      +P^{11/6}+P^{5/2}x^{-1/2}+P^{13/7}\right]\right).
\]
At P=x^0.79 the four powers of x are respectively 853/600, 869/600, 59/40 and 1027/700. They are all below 1.48. The smooth derivative remainder is x²/N³=x^1.37. Summing O(log x) intervals gives the stated O(x^(1.48+ε)) difference. These rational inequalities can be checked with the [exact exponent replay](spectral-interpolation-periodic-prime-convolution.py).

## The reduced classes and the unsmoothed anchored deficit

For q=5 put Cₐ(x;N)=Σ_{n,p:np≡a (5)}W(n/N)log p (x−np)₊ for the four reduced a, and let C̄ be their mean. These are positive genuine arithmetic masses for W≥0 and Bχ,N=Σₐχ(a)Cₐ. By exact character Parseval the two quartics each contribute o(x³) to the variance; the unique nontrivial quadratic η contributes its explicit square drift. In particular,
\[
 x^{-3}\sum_{a=1}^4|C_a-\bar C|^2
 =\frac{|L(1/2,\eta)|^2}{9}+O_W(e^{-c\Phi(\log x)}).
\]
The componentwise statement after subtracting the corresponding quadratic bias even has variance O_W(x³e^(−cΦ(log x))). These masses adjoin the short complete-character factor n. The variance of the four naked prime masses in [PR 7663](https://github.com/mccorvie/riemann-masullo/pull/7663) is still open at this order.

For either quartic χ, write
\[
 T_j=\Re\!\sum_{2\le n\le 2j^{0.84}}W(n/j^{0.84})\chi(n)nS_\chi(j^4/n).
\]
The coefficient at n=1 is exactly one. Pointwise |(−Re Sχ(j⁴))₊−(Tⱼ)₊|≤|Bχ,N(j⁴)|. Thus summation gives
\[
 D_\chi(J)=\sum_{j\le J}(T_j)_+
      +O_W\!\left(J^7 e^{-c\Phi(\log J)}\right).
\]
For small j use the elementary O(j⁶) convolution bound with an enlarged constant; the large-j stretched-log envelope sums by monotonicity or a fixed-power split. Every remaining prime cutoff is at most j⁴/2 and there are at most 2j^0.84 dilation indices. The explicit formula for B proves a global constraint discriminating a purely coherent bias, but the mixed-sign residual is an actual open arithmetic term. Taking absolute values term by term in the residual loses a factor as large as Σ_{n≤2N}n⁻¹ᐟ².

In particular the known global constraint is consistent with an oscillatory exterior mode. For a fixed hypothetical zero ρ, a test input S*(x)=x^(1+ρ) gives the truncated multiplier ΣₙW(n/N)χ(n)n^(−ρ). By repeated integration against periodic primitives, this equals L(ρ,χ)+O_{ρ,q,W,A}(N^(1−Reρ−A)) for every integer A≥1. First justify the ordinary tail by summation by parts for Reρ>0; bound the A-th derivative of t^(−ρ)h(t/N) in L¹ on [N,∞). Hence at a zero the measured global convolution is smaller than any power of N after normalizing by x^(1+Reρ). This shows exactly why the new variance cannot simply be inverted uniformly.

For the balanced permanent-bias model in the [preceding report](spectral-interpolation-mod4-shallow-runs.md), one instead has S*(x)∼−c x^(2−δ), S*′(x)=O(x^(1−δ)). Partial summation in n against the bounded partial sums of the **true** χ shows its truncated normalized bilinear tends to −cL(1−δ,χ). Indeed the tail n>M is O_{q,W}(M^(δ−1)) after normalization, using the derivative of nS*(x/n), and each fixed smaller n has the stated limit. For χ₋₄ the L value is positive on the real interval. For the quartic with χ(2)=i modulo five its real part on s>0 is the strictly positive alternating-class difference Σ_k[(5k+1)^(−s)−(5k+4)^(−s)]. Thus a coherent bias at exponent δ<1/2 would violate the genuine global constraint. For the separate density-one feedback model the pointwise bounds do not give regular variation; the complete convolution still detects the obstruction by Landau on its real abscissa, since the true L is nonzero there. No fake character is used when proving the genuine estimates above.
