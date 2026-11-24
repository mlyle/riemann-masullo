module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletPrimeError
public import RiemannMasullo.Ch13_ZerosHecke.DirichletPrimeSquares

/-!
# Critical-line divergence for character-weighted prime counts

For a Dirichlet character χ let θχ be the sum of χ(p) log p over primes p ≤ x.
The squared relative error of this count has divergent integral if L(s,χ) has
a critical-line zero. If χ² is principal, the same conclusion follows unconditionally.
The Mellin transform of the prime-square contribution then has positive residue at 1/2,
which cannot cancel the nonpositive residue from the logarithmic derivative.

This gives the prime-only endpoint of the rational prime-counting criterion for
Theorem 12.5.1.1, pp. 519–520, including ordinary Chebyshev θ.
-/

open Set MeasureTheory Classical

public noncomputable section
namespace RiemannMasullo

/-- The centered prime-only error has infinite critical energy at any critical-line zero, or at the real
point one half when the character square is principal. -/
theorem dirichletLFunction_critical_prime_energy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hr : ρ.re = 1 / 2) (hz : χ.LFunction ρ = 0 ∨ (ρ = 1 / 2 ∧ χ^2 = 1)) :
    ¬ IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖^2 / x^2)
      (Ioi 1) := by
  intro hE
  let D (x : ℝ) := dirichletChebyshevPsi χ x - dirichletChebyshevTheta χ x
  have hm : Measurable D := (dirichletChebyshevPsi_theta_measurable χ).1.sub (dirichletChebyshevPsi_theta_measurable χ).2
  have hD (x : ℝ) (hx : 1 ≤ x) : ‖D x‖ ≤ 3 * (Real.log 4 + 4) * x^ρ.re := by
    rw [hr, ← Real.sqrt_eq_rpow]
    exact dirichletChebyshevPsi_sub_theta_norm_le χ hx
  have he : ρ.re < 1 := by rw [hr]; norm_num
  have hv := dirichletChebyshevError_correction_residue χ ρ he D hm hD (dirichletChebyshevPsi_sub_theta_mellin_boundary χ ρ hr) (by
    apply hE.congr_fun _ measurableSet_Ioi
    intro x hx
    have hx₀ := lt_trans zero_lt_one hx
    have hp : dirichletChebyshevError χ x - D x = dirichletChebyshevTheta χ x -
        (if χ = 1 then (x : ℂ) else 0) := by
      change (dirichletChebyshevPsi χ x - _) - (dirichletChebyshevPsi χ x - _) = _
      ring
    dsimp only
    rw [hp, show -2*ρ.re-1 = -(2:ℝ) by rw [hr]; norm_num, Real.rpow_neg hx₀.le, Real.rpow_two, div_eq_mul_inv])
  by_cases hs : ρ = 1 / 2 ∧ χ^2 = 1
  · simp only [ite_eq_left hs, mul_one] at hv
    have hreal := congrArg Complex.re hv
    simp only [hr, Complex.neg_re, Complex.natCast_re] at hreal
    linarith [Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt χ.LFunction ρ)]
  · simp only [ite_eq_right hs, mul_zero] at hv
    have hord : analyticOrderNatAt χ.LFunction ρ = 0 := by simpa using hv.symm
    exact dirichletLFunction_zero_order_ne_zero χ he (hz.resolve_right hs) hord

/-- The relative error of the prime-only count for a character of order dividing two is never
square-integrable on the upper half-line. -/
theorem dirichletQuadratic_prime_relative_error_not_square_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ^2 = 1) :
    ¬ IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevTheta χ x - (if χ = 1 then (x : ℂ) else 0)‖^2 / x^2)
      (Ioi 1) := by
  exact dirichletLFunction_critical_prime_energy χ (ρ := 1/2) (by norm_num) (.inr ⟨rfl,hχ⟩)

/-- The relative error of the ordinary Chebyshev prime count has divergent square integral above one. -/
theorem chebyshevTheta_relative_error_not_square_integrable : ¬ IntegrableOn (fun x : ℝ ↦ ((Chebyshev.theta x - x) / x)^2) (Ioi 1) := by
  have h := dirichletQuadratic_prime_relative_error_not_square_integrable (1 : DirichletCharacter ℂ 1) (by simp)
  have hs (x : ℝ) : dirichletChebyshevTheta (1 : DirichletCharacter ℂ 1) x =
      ((Chebyshev.theta x : ℝ) : ℂ) := by
    simp only [dirichletChebyshevTheta, Chebyshev.theta, Complex.ofReal_sum, ← Finset.Icc_succ_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro n _
    have hn : (n : ZMod 1) = 1 := Subsingleton.elim ..
    simp [hn]
  simpa only [ite_true, hs, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow] using h

end RiemannMasullo
