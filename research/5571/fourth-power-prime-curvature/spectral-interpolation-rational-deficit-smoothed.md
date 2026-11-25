# Curvature at actual primes on the fourth-power grid

For the trivial rational character let δ=1, and for the primitive real character χ₋₄ let δ=0. Define
\[
 S(x)=\sum_p\chi(p)\log p\,(x-p)_+-\delta x^2/2,\qquad
 D(J)=\sum_{j=1}^J(-S(j^4))_+ .
\]
Then **D(J)<J⁷ for every integer 1≤J≤1,750,000,000,000** in the principal case and **every 1≤J≤16,000,000** for χ₋₄. For J from 20 billion to the principal endpoint the uniform upper constant is 0.965472. For J from 150,000 to the χ₋₄ endpoint it is 0.948602. The preceding [density certificate](spectral-interpolation-rational-deficit-density.md) covers the smaller positive indices. The bounds use intervals of verified zeros of finite height and arithmetic inequalities on the positive prime coefficients. Behavior on an unbounded sequence remains open. [Executable constants](spectral-interpolation-rational-deficit-smoothed.py) · [128-bit replay](spectral-interpolation-rational-deficit-smoothed-128.receipt) · [192-bit replay](spectral-interpolation-rational-deficit-smoothed-192.receipt).

## The one-sided arithmetic comparison

Fix J and a real c>0. Take v=c²/J² and Y=exp(√v Z−v/2) for Z standard normal. In particular EY=1. For composite x=j⁴, j≥2, subtract the tangent at x from the real function (u−p)₊. Its remainder hₚ(u) is nonnegative and vanishes unless p lies between x and u. Exact Gaussian expectation gives
\[
 -S(x)\le -\mathbb E S(xY)+\mathbb E\sum_{\chi(p)>0}\log p\,h_p(xY)
                 -\tfrac12\delta x^2(e^v-1).
\]
Both steps preserve the physical negative part after multiplication by its optimizing mask, aⱼ=1 when S(j⁴)<0 and 0 otherwise. The case χ₋₄ retains only p≡1 (mod 4) in the local curvature sum. The principal pole has the favorable displayed sign.

Put d=|xY−x|, q=4 or 1 and φ=φ(q). With t between 0 and d, let N(t) count positive-coefficient primes on the appropriate side of x within distance t. The identity for a tent gives Σhₚ=∫N(t)dt. Each log p is at most log x+(log Y)₊. Since x is an integer composite, N(t)≤t. For t≥x^α, α=2/3, use Montgomery–Vaughan's inequality N(t)≤2t/[φ log(t/q)]. On the left x−t>0. On both sides the choice of endpoint convention affects at most a discrete set of t of measure zero. Here x^α>q. Thus
\[
 \sum_{\chi(p)>0}\log p\,h_p(xY)
 \le(\log x+(\log Y)_+)\left\{x^{2\alpha}/2
      +\frac{d^2}{\varphi(\alpha\log x-\log q)}\right\}.
\]
This estimate uses the interval sieve at each sample, with no distribution hypotheses on the primes. [Montgomery and Vaughan, *The large sieve*, Theorem 2, equation (1.10)](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf).

Let J₀=20 billion and m=10 million for the principal character, or J₀=150,000 and m=10,000 for χ₋₄. For J≥J₀ we remove j≤m at total normalized cost (m/J₀)⁷. Write x₀=m⁴, v₀=c²/J₀². The numerical choices below satisfy E|log Y|≤√(v₀+v₀²/4)<0.001,
E(Y−1)²=eᵛ−1≤1.00001v and E(Y−1)⁴≤4v². For the last inequality differentiate e⁶ᵛ−4e³ᵛ+6eᵛ−3 twice. Its second derivative is bounded by 108v exp(6v)+6exp(v)<8, and both values of order zero and one vanish at the origin. Cauchy–Schwarz gives E[(Y−1)²|log Y|]≤3v³ᐟ². Since eᵛ−1≥v, the total extra curvature, after the pole correction and division by J⁷, is at most
\[
 \frac{4\log J_0+0.001}{2}\left(\frac{1}{8\alpha+1}+\frac1{J_0}\right)J_0^{8\alpha-6}
 +c^2\left(\frac19+\frac1{J_0}\right)
 \left\{\frac{1.00001+3\sqrt{v_0}/\log x_0}
  {\varphi(\alpha-\log q/\log x_0)}-\frac\delta2\right\}.
\]
The brace is positive. Sum j⁸ before dividing by J² from v, and use the monotone decrease of (4log J+0.001)J^(8α−6) on this range. The chosen m makes all short windows legal.

## The full lognormal tail and the zero sum

The [two exact Riesz formulas](spectral-interpolation-mod4-deficit-large-sieve.md#the-rational-principal-character), with the [modulo-four residues](spectral-interpolation-mod4-deficit.md#actual-primes-through-fourth-power-index-2100), imply the following uniform lower estimate for every real y>0,
\[
 S(y)\ge-\Re\sum_\rho\frac{y^{1+\rho}}{\rho(1+\rho)}
      -0.729y^{3/2}-4{,}000{,}004y-8.
\]
Indeed the unsigned proper powers cost at most
1.01624 y³ᐟ²(2/3+y⁻¹ᐟ⁶+y⁻¹ᐟ⁴log₂y). The coefficient is ≤0.729 for y≥10¹² and ≤4 for 1≤y≤10¹² (use sup y⁻¹ᐟ⁴log y=4/e). On that smaller interval 4y³ᐟ²≤4·10⁶y. The remaining real residues in both formulas cost at most 3y+8 for y≥1; at y=1 take the right limit. For 0<y<1 the actual prime sum is empty, and the modulus of the zero series is ≤(B+K_H)y. This gives the stated global bound even on the far left Gaussian tail. Here B=0.046192 for ζ and B=0.155568 for χ₋₄ are upper bounds for the critical-line coefficient mass below the respective verified heights H=3·10¹² and H=25·10⁶. K_H is the explicit upper bound on Σ_|γ|>H γ⁻² given in the density certificate. [Rosser and Schoenfeld, Theorem 9](https://doi.org/10.1215/ijm/1255631807) · [Platt and Trudgian, Theorem 1](https://doi.org/10.1112/blms.12460) · [Platt, Theorem 7.1](https://arxiv.org/pdf/1305.3087).

Absolute integrability follows from Σ|ρ(1+ρ)|⁻¹≤B+K_H and EY²<∞. On taking expectation, every complex zero coefficient acquires the exact multiplier
\[
 \mathbb E Y^{1+\rho}=\exp\!\big(v\rho(1+\rho)/2\big).
\]
Below H its modulus is at most exp(3v₀/8), and at all |γ|>H it is at most exp(v₀−c²H²/(2J²)). The latter is uniform in the abscissa and the sample index. In the [common-mask density proof](spectral-interpolation-rational-deficit-density.md), this multiplier depends only on the zero and can be bounded in modulus after summing in j, including on every abscissa layer. Thus the old high-right budget, including the initial right-hand j⁶ term, is multiplied by this same exponential. High zeros with Reρ≤1/2 cost at most K_H exp(v₀)(1/7+1/J₀). The low zeros and the term 0.729y³ᐟ² cost at most (B+0.729)exp(3v₀/8)(1/7+1/J₀). The remaining affine terms cost at most 4,000,004(1/5+1/J₀)/J₀²+8/J₀⁶. These bounds hold for every allowed optimizing prime mask. Each high budget is monotone in J; its common Gaussian factor increases with J too.

For the principal case c=2.65 gives D(J)/J⁷≤0.965471386 on the asserted large-index interval. For χ₋₄ use c=2.91 to obtain ≤0.948601939. Both endpoint computations use outward-rounded Arb operations. With the same sieve and smoothing but with the zero sums bounded absolutely on every abscissa layer, the best upper constants on the tested c-grid 0.50,0.51,…,3.70 exceed 1.19657 and 1.21624 respectively. These comparison values describe that calculation. They provide no lower bound on D. The finite cutoff proof is classical with interval-checked constants.
