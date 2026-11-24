module

public import RiemannMasullo.AppB_AnalyticNT.Sec7b

/-!
# Appendix B.7.2: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Paragraph after Equation (B.7.2.12), p. 650. At the pole ordinate
the printed value of the normalized oscillatory term is minus one. -/
def Printed.heckePrimePowerTailOscillation_at_pole : Prop :=
  ∀ (t₀ : ℝ) (n : ℕ), 2 ≤ n →
    Tendsto (fun t : ℝ ↦ heckePrimePowerTailOscillation t₀ n ⟨1, t⟩ / (Real.log n : ℂ))
      (𝓝[≠] t₀) (𝓝 (-1))

/-- Paper: Paragraph after Equation (B.7.2.12), p. 650. With `t₀ = 0` and
`n = 2`, the quotient off the pole has limit `log 2` at `s = 1`, giving
normalized value one. -/
theorem Printed.heckePrimePowerTailOscillation_at_pole_false :
    ¬ Printed.heckePrimePowerTailOscillation_at_pole := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equations (B.7.2.18)–(B.7.2.19), p. 652.
In the printed product comparison the first term of `G_x` has the sign
corresponding to denominator `i log(M - 1) (t - t₀)`. -/
def Printed.reciprocalHeckeEulerProductBelow_mul_normTwist : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
    ∀ (K : Set ℝ), IsCompact K → t₀ ∉ K → ∀ ε > (0 : ℝ),
      ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℕ, x₀ ≤ (x : ℝ) →
        ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
          let G := heckePrimePowerTailOscillation t₀ (x - 1) ⟨1, t⟩ /
              (Real.log ((x - 1 : ℕ) : ℝ) : ℂ) -
            ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n
          ‖error t‖ ≤ 2 * ε / Real.log x ∧
          reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
            Complex.exp (error t + G + heckeEulerProductLogCorrection χ x ⟨1, t⟩)

/-- Paper: Theorem B.7.2.4(1), pp. 652–653. Take `F = ℚ`, `χ = 1`, `t₀ = 0`,
`K = {1}`, and `x = 1 + floor(exp((2k + 1)π))`. The printed and corrected
oscillations differ by `2 g_{x-1}(1+i) / log(x-1)`. Its norm times
`log x` tends to four, whereas both error bounds with `ε = 1/4` give a
combined bound of one. The difference of the exponents tends to zero,
so equality of the exponentials would force the difference to vanish. -/
theorem Printed.reciprocalHeckeEulerProductBelow_mul_normTwist_false :
    ¬ Printed.reciprocalHeckeEulerProductBelow_mul_normTwist := by
  sorry

open Classical in
/-- Paper: Equation (B.7.2.23), p. 653. On and to the right of the 1-line,
excluding the pole of a pure norm character, the printed second equality
subtracts `H_x` from the ordered prime-power tail. Its left side sums over
primes in norm order, taking all positive powers at each prime. -/
def Printed.heckePrimePowerLogTail_sub_correction : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (x : ℕ), 1 < x → ∀ s : ℂ, 1 ≤ s.re →
    (∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
      s ≠ ⟨1, t₀⟩) →
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      Tendsto (fun y : ℝ ↦
        ∑ v ∈ heckePrimesBelow F y \ heckePrimesBelow F x,
          ∑' k : ℕ, heckePrimePowerLogTerm χ v k s) atTop
        (𝓝 (heckePrimePowerLogTail χ x s - heckeEulerProductLogCorrection χ x s))

/-- Paper: Equation (B.7.2.23), p. 653. Over `ℚ` take the trivial character,
`x = 3`, and ordinate `2π / log 2` on the 1-line. The grouped tail includes
all powers of two with exponent at least two, whose sum is `log 2 - 1/2 > 0`.
The prime tail omits them and the printed subtraction counts them twice. -/
theorem Printed.heckePrimePowerLogTail_sub_correction_false :
    ¬ Printed.heckePrimePowerLogTail_sub_correction := by
  sorry

/-- Paper: Remark B.7.2.7, p. 653. For every pure norm character and every
interval with the pole ordinate in its interior, convergence of the
reciprocal products is claimed to fail to be uniform on that interval. -/
def Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
    ∀ (J : Set ℝ), OrdConnected J → t₀ ∈ interior J →
      ¬ TendstoUniformlyOn
        (fun x : ℕ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
        (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop J

/-- Paper: Remark B.7.2.7, p. 653. Take `F = ℚ`, `χ = 1`, `t₀ = 0`, and
`J = [-1, 1]`. A comparison of log moduli at abscissa `1 + 1 / log x`
bounds the reciprocal product near zero by a constant times
`|t| + 1 / log x`. This gives uniform convergence near the pole together
with the compact-uniform convergence away from it (R27). -/
theorem Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole_false :
    ¬ Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole := by
  sorry

end RiemannMasullo
