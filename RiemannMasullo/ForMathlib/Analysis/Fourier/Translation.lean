module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation estimates for circle characters and Fourier integrals -/

@[expose] public noncomputable section

open Function MeasureTheory Set

namespace RiemannMasullo

/-- A continuous circle character on a normed additive group is Lipschitz. The geometric
sum of its first n powers has real part at least n / 2 while the multiples stay near zero. -/
theorem exists_circleCharacter_norm_sub_one_le {E : Type*} [NormedAddCommGroup E]
    (χ : Multiplicative E →ₜ* Circle) :
    ∃ C > 0, ∀ x : E, ‖(χ (Multiplicative.ofAdd x) : ℂ) - 1‖ ≤ C * ‖x‖ := by
  have hc : Continuous (fun x : E ↦ (χ (Multiplicative.ofAdd x) : ℂ)) :=
    continuous_subtype_val.comp (χ.continuous.comp continuous_ofAdd)
  obtain ⟨r, hr, hd⟩ := (Metric.continuousAt_iff.mp (hc.continuousAt (x := 0))) (1 / 2) (by norm_num)
  have hsmall (y : E) (hy : ‖y‖ < r) : ‖(χ (Multiplicative.ofAdd y) : ℂ) - 1‖ < 1 / 2 := by
    simpa [dist_eq_norm] using hd (show dist y 0 < r by simpa using hy)
  refine ⟨8 / r, by positivity, fun x ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : ℂ := χ (Multiplicative.ofAdd x)
  let n := ⌊r / (2 * ‖x‖)⌋₊ + 1
  have hn : r / (2 * ‖x‖) < (n : ℝ) := by simpa [n] using Nat.lt_floor_add_one (r / (2 * ‖x‖))
  have hpow (k : ℕ) (hk : k ∈ Finset.range n) : 1 / 2 ≤ (z ^ k).re := by
    have hk' : (k : ℝ) ≤ r / (2 * ‖x‖) :=
      (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans (Nat.floor_le (by positivity))
    have hky : ‖k • x‖ < r := norm_nsmul_le.trans_lt (by
      have H := (le_div_iff₀ (show 0 < 2 * ‖x‖ by positivity)).mp hk'
      nlinarith)
    have h := hsmall (k • x) hky
    have he : (χ (Multiplicative.ofAdd (k • x)) : ℂ) = z ^ k := by rw [ofAdd_nsmul, map_pow, Circle.coe_pow]
    rw [he] at h
    have hl := (Complex.abs_re_le_norm (z ^ k - 1)).trans h.le
    simp only [Complex.sub_re, Complex.one_re, abs_le] at hl
    linarith
  let b := ∑ k ∈ Finset.range n, z ^ k
  have hb : (n : ℝ) / 2 ≤ ‖b‖ := by
    refine le_trans ?_ (Complex.re_le_norm b)
    change _ ≤ (∑ k ∈ Finset.range n, z ^ k).re
    rw [Complex.re_sum]
    have hh := Finset.sum_le_sum hpow
    simpa [div_eq_mul_inv] using hh
  have hz : ‖z‖ = 1 := Circle.norm_coe _
  have hb' : ‖b‖ * ‖z - 1‖ ≤ 2 := by
    rw [← norm_mul, show b * (z - 1) = z ^ n - 1 from geom_sum_mul z n]
    simpa [hz, one_add_one_eq_two] using norm_sub_le (z ^ n) (1 : ℂ)
  change ‖z - 1‖ ≤ 8 / r * ‖x‖
  have H := (mul_le_mul_of_nonneg_right hb (norm_nonneg (z - 1))).trans hb'
  have ha := (div_lt_iff₀ (show 0 < 2 * ‖x‖ by positivity)).mp hn
  have hbnd := (mul_le_mul_of_nonneg_right ha.le (norm_nonneg (z - 1)))
  have hc' := mul_le_mul_of_nonneg_right H hnx.le
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  nlinarith

/-- Translating the oscillatory integral turns the distance of a character value from one
into an L¹ difference of its amplitude. -/
theorem fourierIntegral_circleCharacter_translation_bound {E : Type*} [NormedCommRing E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (χ : Multiplicative E →ₜ* Circle) (k : E → ℂ) (hk : Integrable k μ) (r h : E) :
    ‖∫ x, k x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ‖ *
      ‖(χ (Multiplicative.ofAdd (r * h)) : ℂ) - 1‖ ≤ ∫ x, ‖k (x + h) - k x‖ ∂μ := by
  let p (x : E) : ℂ := χ (Multiplicative.ofAdd (x * r))
  have hp : Continuous p := continuous_subtype_val.comp
    (χ.continuous.comp (continuous_ofAdd.comp (continuous_id.mul continuous_const)))
  have hp0 (x) : ‖p x‖ = 1 := Circle.norm_coe _
  have ha (x : E) : p (x + h) = p x * p h := by
    simp only [p, add_mul, ofAdd_add, map_mul, Circle.coe_mul]
  let I := ∫ x, k x * p x ∂μ
  have hki : Integrable (fun x ↦ k x * p x) μ := hk.mul_bdd hp.aestronglyMeasurable
    (ae_of_all _ fun x ↦ (hp0 x).le)
  have hshift : Integrable (fun x ↦ k (x + h)) μ := (measurePreserving_add_right μ h).integrable_comp_of_integrable hk
  have hD := (hshift.sub hk).mul_bdd ((hp.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ (hp0 (x + h)).le)
  have hDI : (∫ x, (k (x + h) - k x) * p (x + h) ∂μ) = I * (1 - p h) := by
    have h₁ : Integrable (fun x ↦ k (x + h) * p (x + h)) μ :=
      (measurePreserving_add_right μ h).integrable_comp_of_integrable hki
    have h₂ : Integrable (fun x ↦ k x * p (x + h)) μ := hk.mul_bdd
      ((hp.comp (continuous_id.add continuous_const)).aestronglyMeasurable) (ae_of_all _ fun x ↦ (hp0 _).le)
    simp_rw [sub_mul]
    rw [integral_sub h₁ h₂, integral_add_right_eq_self (fun x ↦ k x * p x) h]
    simp_rw [ha, ← mul_assoc, integral_mul_const]
    change I - I * p h = _
    ring
  change ‖I‖ * ‖(χ (Multiplicative.ofAdd (r * h)) : ℂ) - 1‖ ≤ _
  rw [mul_comm r h]
  change ‖I‖ * ‖p h - 1‖ ≤ _
  rw [norm_sub_rev (p h) 1, ← norm_mul, ← hDI]
  exact norm_integral_le_of_norm_le (hshift.sub hk).norm
    (ae_of_all _ fun x ↦ by simp only [norm_mul, hp0, mul_one, le_refl])

end RiemannMasullo
