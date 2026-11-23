module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.Inversion

/-!
# Controlling radial profile seminorms by Fourier moments
-/

@[expose] public noncomputable section

open MeasureTheory Function Set
open scoped FourierTransform ContDiff

namespace RiemannMasullo.StripNuclearity

/-- For a smooth compact profile in a fixed set $J$, its jth physical
derivative has L¹ norm at most the volume of $J$ times the jth absolute
frequency moment. The factor $(2π)^j$ uses Mathlib's real Fourier convention. -/
theorem integral_norm_iteratedDeriv_le_fourier_moment {J : Set ℝ} (hJ : IsCompact J)
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (hsupp : tsupport p ⊆ J) (j : ℕ) :
    (∫ x : ℝ, ‖iteratedDeriv j p x‖) ≤
      volume.real J * (2*Real.pi)^j * ∫ u : ℝ, |u|^j * ‖𝓕 p u‖ := by
  have hcomp (k : ℕ) : tsupport (iteratedDeriv k p) ⊆ J := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hsupp
    | succ k ih => simpa only [iteratedDeriv_succ] using tsupport_deriv_subset.trans ih
  have hsm (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k p) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hp
    | succ k ih => simpa only [iteratedDeriv_succ] using (contDiff_infty_iff_deriv.mp ih).2
  have hcs (k : ℕ) : HasCompactSupport (iteratedDeriv k p) := hJ.of_isClosed_subset isClosed_closure (hcomp k)
  have hint (k : ℕ) : Integrable (iteratedDeriv k p) := (hsm k).continuous.integrable_of_hasCompactSupport (hcs k)
  let q := iteratedDeriv j p
  let Q := (hcs j).toSchwartzMap (hsm j)
  have hFi : Integrable (𝓕 q) := (𝓕 Q).integrable
  have hF := Real.fourier_iteratedDeriv (N := ⊤) (n := j) hp (fun k _ ↦ hint k) le_top
  have hcost : ∀ x, ‖q x‖ ≤ (2*Real.pi)^j * ∫ u : ℝ, |u|^j * ‖𝓕 p u‖ := by
    intro x
    have hinv := (hint j).fourierInv_fourier_eq (v := x) hFi (hsm j).continuous.continuousAt
    change 𝓕⁻ (𝓕 q) x = q x at hinv
    rw [← hinv,Real.fourierInv_eq_fourier_neg]
    apply (Real.norm_fourier_le_integral_norm (𝓕 q) (-x)).trans_eq
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine .of_forall fun u ↦ ?_
    change ‖𝓕 (iteratedDeriv j p) u‖ = _
    rw [hF]
    simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_pow]
    ring
  let C := (2*Real.pi)^j * ∫ u : ℝ, |u|^j * ‖𝓕 p u‖
  have hass : ∫ x in J, ‖q x‖ = ∫ x, ‖q x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      change ‖iteratedDeriv j p x‖ = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hcomp j h)),norm_zero]
  have hC : IntegrableOn (fun _ : ℝ ↦ C) J := integrableOn_const hJ.measure_lt_top.ne
  calc
    _ = ∫ x in J, ‖q x‖ := hass.symm
    _ ≤ ∫ _ in J, C := setIntegral_mono (hint j).norm.integrableOn hC hcost
    _ = _ := by rw [setIntegral_const]; exact (mul_assoc _ _ _).symm

end RiemannMasullo.StripNuclearity
