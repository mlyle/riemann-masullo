module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The first Riesz mean of the Hecke logarithmic derivative

The Mellin transform of the finite ideal sum weighted by the ramp `max (x - N I) 0`
recovers the negative logarithmic derivative with denominator `s * (s + 1)`.
This is the arithmetic transform for the one-sided comparison for Theorem 12.5.1.1,
pp. 519–520, with the Hecke Euler series of equation (B.6.1.12), p. 638.
-/

@[expose] public noncomputable section

open Set MeasureTheory NumberField
open scoped ENNReal NNReal

namespace RiemannMasullo

local notation "K(" q ", " s ", " x ")" =>
  Complex.ofReal (max ((x : ℝ) - (q : ℝ)) 0) * (x : ℂ) ^ (-(s : ℂ) - 2)

private theorem riesz_kernel_indicator {q : ℝ} (hq : 0 < q) (s : ℂ) (x : ℝ) :
    K(q, s, x) = (Ioi q).indicator
      (fun t : ℝ ↦ (t : ℂ) ^ (-s - 1) - (q : ℂ) * (t : ℂ) ^ (-s - 2)) x := by
  by_cases h : q < x
  · rw [indicator_of_mem (show x ∈ Ioi q from h), max_eq_left (sub_nonneg.mpr h.le), Complex.ofReal_sub,
      sub_mul, show -s - 1 = 1 + (-s - 2) by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hq.trans h).ne'), Complex.cpow_one]
  · rw [indicator_of_notMem (show x ∉ Ioi q from h),
      max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), Complex.ofReal_zero, zero_mul]

private theorem riesz_kernel_integrable {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ K(q, s, x)) (Ioi 1) := by
  simp_rw [riesz_kernel_indicator (zero_lt_one.trans_le hq)]
  have h₁ : (-s - 1).re < -1 := by simp; linarith
  have h₂ : (-s - 2).re < -1 := by simp; linarith
  exact ((integrableOn_Ioi_cpow_of_lt h₁ zero_lt_one).sub
    ((integrableOn_Ioi_cpow_of_lt h₂ zero_lt_one).const_mul (q : ℂ))).indicator measurableSet_Ioi

private theorem riesz_kernel_integral {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), K(q, s, x)) = (q : ℂ) ^ (-s) / (s * (s + 1)) := by
  have hq₀ := zero_lt_one.trans_le hq
  have hqℂ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have h₁ : (-s - 1).re < -1 := by simp; linarith
  have h₂ : (-s - 2).re < -1 := by simp; linarith
  have hs₀ : s ≠ 0 := fun e ↦ (ne_of_gt hs) (congrArg Complex.re e)
  have hs₁ : s + 1 ≠ 0 := by
    intro e
    have hh := congrArg Complex.re e
    simp at hh
    linarith
  simp_rw [riesz_kernel_indicator hq₀]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hq,
    integral_sub (integrableOn_Ioi_cpow_of_lt h₁ hq₀)
      ((integrableOn_Ioi_cpow_of_lt h₂ hq₀).const_mul _), integral_const_mul,
    integral_Ioi_cpow_of_lt h₁ hq₀, integral_Ioi_cpow_of_lt h₂ hq₀,
    show -s - 1 + 1 = -s by ring, show -s - 2 + 1 = -s - 1 by ring,
    Complex.cpow_sub _ _ hqℂ, Complex.cpow_one, show -s - 1 = -(s + 1) by ring]
  simp only [div_neg, neg_div, neg_neg]
  field_simp
  ring

private theorem riesz_kernel_norm_integral_le {q : ℝ} (hq : 1 ≤ q) {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), ‖K(q, s, x)‖) ≤ (q ^ s.re)⁻¹ / s.re := by
  have hq₀ := zero_lt_one.trans_le hq
  have hd : -s.re - 1 < -1 := by linarith
  let f := (Ioi q).indicator (fun x : ℝ ↦ x ^ (-s.re - 1))
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ), f x := by
      apply setIntegral_mono_on (riesz_kernel_integrable hq hs).norm
        ((integrableOn_Ioi_rpow_of_lt hd zero_lt_one).indicator measurableSet_Ioi) measurableSet_Ioi
      intro x hx
      by_cases h : q < x
      · have hx₀ := hq₀.trans h
        rw [indicator_of_mem (show x ∈ Ioi q from h),
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_max_right _ _),
          max_eq_left (sub_nonneg.mpr h.le), Complex.norm_cpow_eq_rpow_re_of_pos hx₀]
        have he : (-s - 2).re = -s.re - 2 := by simp
        rw [he, show -s.re - 1 = 1 + (-s.re - 2) by ring, Real.rpow_add hx₀, Real.rpow_one]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hx₀.le _)
      · simp [indicator_of_notMem (show x ∉ Ioi q from h), max_eq_right (sub_nonpos.mpr (le_of_not_gt h))]
    _ = _ := by
      dsimp only [f]
      rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hq,
        integral_Ioi_rpow_of_lt hd hq₀, show -s.re - 1 + 1 = -s.re by ring,
        Real.rpow_neg hq₀.le, neg_div_neg_eq]

private theorem mellin_firstRieszMean_integrable_eq {ι : Type*} (q : ι → ℝ) (a : ι → ℂ)
    (hq : ∀ i, 1 ≤ q i) (hfin : ∀ x : ℝ, {i | q i ≤ x}.Finite) {s : ℂ} (hs : 0 < s.re)
    {A : ℂ} (hA : HasSum (fun i ↦ a i / (q i : ℂ) ^ s) A) :
    IntegrableOn (fun x : ℝ ↦ (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) * (x : ℂ) ^ (-s - 2)) (Ioi 1) ∧
    (∫ x in Ioi (1 : ℝ), (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) *
      (x : ℂ) ^ (-s - 2)) = A / (s * (s + 1)) := by
  classical
  let _ : Countable ι := by
    apply countable_univ_iff.mp
    apply (countable_iUnion (fun n : ℕ ↦ (hfin n).countable)).mono
    exact fun i _ ↦ mem_iUnion.mpr ⟨⌈q i⌉₊, (show q i ≤ (⌈q i⌉₊ : ℝ) from Nat.le_ceil (q i))⟩
  let f (i : ι) (x : ℝ) := a i * K(q i, s, x)
  have hi (i : ι) : IntegrableOn (f i) (Ioi 1) := (riesz_kernel_integrable (hq i) hs).const_mul _
  have hn : Summable (fun i ↦ ∫ x in Ioi (1 : ℝ), ‖f i x‖) := by
    apply (hA.summable.norm.div_const s.re).of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro i
    have hnrm (x : ℝ) : ‖f i x‖ = ‖a i‖ * ‖K(q i, s, x)‖ := norm_mul ..
    simp_rw [hnrm]
    rw [integral_const_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hq i))]
    calc
      _ ≤ ‖a i‖ * ((q i ^ s.re)⁻¹ / s.re) :=
        mul_le_mul_of_nonneg_left (riesz_kernel_norm_integral_le (hq i) hs) (norm_nonneg (a i))
      _ = _ := by ring
  have he (x : ℝ) : (∑' i, f i x) = (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) * (x : ℂ) ^ (-s - 2) := by
    let g (i : ι) : ℂ := a i * (max (x - q i) 0 : ℝ)
    have hgf : (Function.support g).Finite := (hfin x).subset fun i hi ↦ by
      change q i ≤ x
      by_contra! h
      apply hi
      simp [g, max_eq_right (sub_nonpos.mpr h.le)]
    calc
      _ = ∑' i, g i * (x : ℂ) ^ (-s - 2) := tsum_congr fun i ↦ by dsimp [f, g]; ring
      _ = _ := by rw [tsum_mul_right, tsum_eq_finsum hgf]
  constructor
  · simp_rw [← he]
    refine ⟨.tsum (fun i ↦ (hi i).aestronglyMeasurable), hasFiniteIntegral_iff_eNorm.mpr ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x ↦ eNorm_tsum_le_tsum_eNorm) ?_
    rw [lintegral_tsum (fun i ↦ (hi i).aestronglyMeasurable.eNorm), lt_top_iff_ne_top]
    have hv (i : ι) : (∫⁻ x in Ioi (1 : ℝ), ‖f i x‖ₑ) = ‖∫ x in Ioi (1 : ℝ), ‖f i x‖‖ₑ := by
      dsimp [eNorm]
      rw [lintegral_coe_eq_integral _ (hi i).norm, ENNReal.coe_nnreal_eq, coe_nnNorm,
        Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
      simp only [coe_nnNorm]
    rw [funext hv]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hn.abs)
  have he' (i : ι) : (∫ x in Ioi (1 : ℝ), f i x) = (a i / (q i : ℂ) ^ s) / (s * (s + 1)) := by
    dsimp only [f]
    rw [integral_const_mul, riesz_kernel_integral (hq i) hs, Complex.cpow_neg]
    ring
  simpa only [he] using ((hasSum_integral_of_summable_integral_norm hi hn).congr_fun
    (fun i ↦ (he' i).symm)).unique (hA.div_const _)

/-- Mellin transform of a first Riesz mean on a locally finite family of real norms.
Absolute convergence of the Dirichlet series at `s` justifies summing the ramp integrals. -/
theorem mellin_firstRieszMean {ι : Type*} (q : ι → ℝ) (a : ι → ℂ)
    (hq : ∀ i, 1 ≤ q i) (hfin : ∀ x : ℝ, {i | q i ≤ x}.Finite) {s : ℂ} (hs : 0 < s.re)
    {A : ℂ} (hA : HasSum (fun i ↦ a i / (q i : ℂ) ^ s) A) :
    (∫ x in Ioi (1 : ℝ), (∑ᶠ i, a i * (max (x - q i) 0 : ℝ)) *
      (x : ℂ) ^ (-s - 2)) = A / (s * (s + 1)) := by
  exact (mellin_firstRieszMean_integrable_eq q a hq hfin hs hA).2

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "I₀" => {I : Ideal (𝓞 F) // I ≠ ⊥}
local notation "Λ(" χ ", " I ")" => heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (Subtype.val (I : I₀))

/-- The first Riesz mean of the finite Hecke logarithmic derivative, summed over ideals
with absolute norm below the real cutoff. -/
def heckeFirstRieszMean (χ : U) (x : ℝ) : ℂ :=
  ∑ᶠ I : I₀, Λ(χ, I) * (max (x - (I.val.absNorm : ℝ)) 0 : ℝ)

private theorem heckeFirstRieszMean_finite (x : ℝ) :
    {I : I₀ | (I.val.absNorm : ℝ) ≤ x}.Finite := by
  apply ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌈x⌉₊).preimage
    (Subtype.val_injective (p := fun I : Ideal (𝓞 F) ↦ I ≠ ⊥)).injOn).subset
  intro I hI
  change I.val.absNorm ≤ ⌈x⌉₊
  exact_mod_cast (show (I.val.absNorm : ℝ) ≤ x from hI).trans (Nat.le_ceil x)

/-- The Mellin transform of the actual finite Hecke Riesz mean on the Euler half-plane.
The same continuation and Euler-series hypotheses are used in Appendix B.6. -/
theorem heckeFirstRieszMean_mellin (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), heckeFirstRieszMean χ x * (x : ℂ) ^ (-s - 2)) =
      -logDeriv L s / (s * (s + 1)) := by
  have hq (I : I₀) : (1 : ℝ) ≤ I.val.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  apply mellin_firstRieszMean (fun I : I₀ ↦ (I.val.absNorm : ℝ)) (fun I ↦ Λ(χ, I)) hq
    (heckeFirstRieszMean_finite (F := F)) (zero_lt_one.trans hs)
  simpa only [Complex.ofReal_natCast, neg_div, neg_neg] using
    (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨s, hs⟩).2.2.neg

private theorem riesz_ramp_interp (n m : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    max ((n : ℝ) + t - m) 0 =
      (1 - t) * max ((n : ℝ) - m) 0 + t * max ((n : ℝ) + 1 - m) 0 := by
  by_cases h : m ≤ n
  · have h' : (m : ℝ) ≤ n := by exact_mod_cast h
    rw [max_eq_left (by linarith [ht.1]), max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have h' : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (by linarith [ht.2]), max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

/-- Between consecutive integers the first Hecke Riesz mean is exactly affine. This
allows the continuous statistic to be recovered from the integer cutoffs. -/
theorem heckeFirstRieszMean_interp (χ : U) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    heckeFirstRieszMean χ ((n : ℝ) + t) =
      (1 - (t : ℂ)) * heckeFirstRieszMean χ n + t * heckeFirstRieszMean χ (n + 1 : ℕ) := by
  classical
  let S := (heckeFirstRieszMean_finite (F := F) ((n : ℝ) + 1)).toFinset
  have hcut (x : ℝ) (hx : x ≤ n + 1) :
      heckeFirstRieszMean χ x = ∑ I ∈ S, Λ(χ, I) * (max (x - I.val.absNorm) 0 : ℝ) := by
    unfold heckeFirstRieszMean
    apply finsum_eq_sum_of_support_subset
    intro I hI
    apply (Set.Finite.mem_toFinset _).mpr
    change (I.val.absNorm : ℝ) ≤ n + 1
    by_contra! h
    exact hI (by simp [max_eq_right (sub_nonpos.mpr (hx.trans h.le))])
  rw [hcut _ (by linarith [ht.2]), hcut _ (by linarith), hcut _ (by norm_num),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I _
  rw [riesz_ramp_interp _ _ ht]
  push_cast
  ring

/-- After subtracting a real quadratic main term, the interpolation correction is
exactly `c * t * (1-t) / 2`. It is nonnegative for the trivial-character main term. -/
theorem heckeFirstRieszMean_centered_interp (χ : U) (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) (c : ℝ) :
    (heckeFirstRieszMean χ ((n : ℝ) + t)).re - c * ((n : ℝ) + t) ^ 2 / 2 =
      (1 - t) * ((heckeFirstRieszMean χ n).re - c * (n : ℝ) ^ 2 / 2) +
      t * ((heckeFirstRieszMean χ (n + 1 : ℕ)).re - c * ((n : ℝ) + 1) ^ 2 / 2) +
      c * t * (1 - t) / 2 := by
  rw [heckeFirstRieszMean_interp χ n ht]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul]
  ring

/-- Group the ideal Riesz mean by its rational integer norm. -/
theorem heckeFirstRieszMean_eq_norm_sum (χ : U) {x : ℝ} (hx : 0 ≤ x) :
    heckeFirstRieszMean χ x =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n * (x - n : ℝ) := by
  classical
  let T := (heckeFirstRieszMean_finite (F := F) x).toFinset
  have hT (I : I₀) : I ∈ T ↔ (I.val.absNorm : ℝ) ≤ x := Set.Finite.mem_toFinset _
  let f (I : I₀) := Λ(χ, I) * (x - I.val.absNorm : ℝ)
  have hbase : heckeFirstRieszMean χ x = ∑ I ∈ T, f I := by
    unfold heckeFirstRieszMean
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · exact Finset.sum_congr rfl fun I hi ↦ by simp [f, max_eq_left (sub_nonneg.mpr ((hT I).mp hi))]
    · intro I hi
      apply (hT I).mpr
      by_contra! h
      exact hi (by simp [max_eq_right (sub_nonpos.mpr h.le)])
  rw [hbase, ← Finset.sum_fiberwise_of_maps_to (t := Finset.Ioc 0 ⌊x⌋₊)
    (g := fun I : I₀ ↦ I.val.absNorm) (fun I hi ↦ Finset.mem_Ioc.mpr
      ⟨Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property), Nat.le_floor ((hT I).mp hi)⟩) f]
  apply Finset.sum_congr rfl
  intro n hn
  let V := T.filter (fun I : I₀ ↦ I.val.absNorm = n)
  let A := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
  let e : (V : Type _) ≃ A :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property, (Finset.mem_filter.mp I.property).2⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, Finset.mem_filter.mpr
        ⟨(hT _).mpr (by change (I.val.absNorm : ℝ) ≤ x; rw [I.property.2]; exact
          (Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2), I.property.2⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  change (∑ I ∈ V, f I) = (∑ᶠ I : A, heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val) * _
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Finset.sum_mul, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro I _
  dsimp [f, e]
  rw [(Finset.mem_filter.mp I.property).2]

/-- Keeping only the rational-prime norms in the first Riesz mean costs at most a universal
constant times the degree and `x * sqrt x`. -/
theorem heckeFirstRieszMean_sub_prime_le :
    ∃ C : ℝ, ∀ (F : Type*) [Field F] [NumberField F]
      (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {x : ℝ}, 0 ≤ x →
      ‖heckeFirstRieszMean χ x - ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime,
        heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p * (x - p : ℝ)‖ ≤
        Module.finrank ℚ F * x * (C * Real.sqrt x) := by
  obtain ⟨C, hC⟩ := heckeLogDerivCoefficient_sum_sub_sum_prime_le_mul_sqrt
  refine ⟨C, fun F _ _ χ x hx ↦ ?_⟩
  let b (n : ℕ) : ℂ := (max (x - n) 0 : ℝ)
  have hb (n : ℕ) (hn : n ∈ Finset.Ioc 0 ⌊x⌋₊) : b n = (x - n : ℝ) := by
    exact congrArg Complex.ofReal (max_eq_left (sub_nonneg.mpr ((Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2)))
  have hb' (n : ℕ) : ‖b n‖ ≤ x := by
    rw [show ‖b n‖ = |max (x - n) 0| from Complex.norm_real _, abs_of_nonneg (le_max_right ..)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg n)) hx
  rw [heckeFirstRieszMean_eq_norm_sum χ hx]
  convert hC F χ x b x hb' using 2
  congr 1 <;> apply Finset.sum_congr rfl <;> intro n hn
  all_goals first | rw [hb n hn] | rw [hb n (Finset.mem_filter.mp hn).1]

open Filter Topology in
private theorem riesz_rat_prime_power_sqrt :
    Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - Chebyshev.theta x) / Real.sqrt x) atTop (𝓝 1) := by
  have small (r : ℝ) (hr : 0 < r) (hr' : r < 1 / 2) :
      Tendsto (fun x : ℝ ↦ Chebyshev.psi (x ^ r) / Real.sqrt x) atTop (𝓝 0) := by
    have h := (Chebyshev.tendsto_psi_div_atTop.comp (tendsto_rpow_atTop hr)).mul
      (tendsto_rpow_neg_atTop (sub_pos.mpr hr'))
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Function.comp_apply, neg_sub, Real.sqrt_eq_rpow, Real.rpow_sub hx]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hx r)]
  have hmain : Tendsto (fun x : ℝ ↦ Chebyshev.psi (x ^ (2 : ℝ)⁻¹) / Real.sqrt x) atTop (𝓝 1) := by
    simpa only [Real.sqrt_eq_rpow, one_div, Function.comp_def] using
      Chebyshev.tendsto_psi_div_atTop.comp (tendsto_rpow_atTop (by norm_num : 0 < (2 : ℝ)⁻¹))
  have hup := (hmain.add (small (3 : ℝ)⁻¹ (by norm_num) (by norm_num))).add
    (small (5 : ℝ)⁻¹ (by norm_num) (by norm_num))
  simp only [add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hup
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    linarith [Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx,
      Chebyshev.psi_nonneg (x ^ (3 : ℝ)⁻¹), Chebyshev.psi_nonneg (x ^ (7 : ℝ)⁻¹)]
  · filter_upwards with x
    simp only [← add_div]
    exact div_le_div_of_nonneg_right (Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x)
      (Real.sqrt_nonneg x)

open Filter Topology in
private theorem riesz_rat_prime_power_integral :
    Tendsto (fun x : ℝ ↦ (∫ t in (0 : ℝ)..x, Chebyshev.psi t - Chebyshev.theta t) /
      (x * Real.sqrt x)) atTop (𝓝 (2 / 3 : ℝ)) := by
  let g : ℝ → ℝ := fun t ↦ Chebyshev.psi t - Chebyshev.theta t
  have hg : Measurable g := Chebyshev.psi_mono.measurable.sub Chebyshev.theta_mono.measurable
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs : Tendsto (fun x : ℝ ↦ ∫ u in (0 : ℝ)..1, g (x * u) / Real.sqrt x)
      atTop (𝓝 (∫ u in (0 : ℝ)..1, Real.sqrt u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun u ↦ C * Real.sqrt u)
    · exact .of_forall fun x ↦ ((hg.comp (measurable_const.mul measurable_id)).div_const _).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact .of_forall fun u hu ↦ by
        rw [Set.uIoc_of_le zero_le_one] at hu
        have hpos := Real.sqrt_pos.2 hx
        have hu0 : 0 ≤ g (x * u) := sub_nonneg.mpr (Chebyshev.theta_le_psi _)
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hu0 hpos.le), div_le_iff₀ hpos]
        calc g (x * u) ≤ C * Real.sqrt (x * u) := hC _
             _ = C * Real.sqrt u * Real.sqrt x := by rw [Real.sqrt_mul hx.le]; ring
    · exact (continuous_const.mul Real.continuous_sqrt).intervalIntegrable ..
    · exact .of_forall fun u hu ↦ by
        rw [Set.uIoc_of_le zero_le_one] at hu
        have ht := (riesz_rat_prime_power_sqrt.comp (tendsto_id.atTop_mul_const hu.1)).mul_const (Real.sqrt u)
        rw [one_mul] at ht
        refine ht.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simp only [Function.comp_apply, id_eq, Real.sqrt_mul hx.le]
        change g (x * u) / (Real.sqrt x * Real.sqrt u) * Real.sqrt u = _
        field_simp [(Real.sqrt_pos.2 hx).ne', (Real.sqrt_pos.2 hu.1).ne']
  have he : (∫ u in (0 : ℝ)..1, Real.sqrt u) = 2 / 3 := by
    simp only [Real.sqrt_eq_rpow]
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
  rw [he] at hs
  refine hs.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_mul_left g hx.ne']
  simp only [mul_zero, mul_one, smul_eq_mul]
  dsimp [g]
  ring

private theorem riesz_rat_nonprime_sum_eq_integral {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime, ArithmeticFunction.vonMangoldt n * (x - n)) =
      ∫ t in (0 : ℝ)..x, Chebyshev.psi t - Chebyshev.theta t := by
  let a (n : ℕ) : ℝ := if n.Prime then 0 else ArithmeticFunction.vonMangoldt n
  have hA (t : ℝ) : ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, a n = Chebyshev.psi t - Chebyshev.theta t := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, Chebyshev.psi_sub_theta_eq_sum_not_prime,
      Finset.sum_filter]
    simp [a]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x - s) (-1) t := by
    exact (hasDerivAt_id' t).const_sub x
  have hv : deriv (fun s : ℝ ↦ x - s) = fun _ ↦ -1 := funext fun t ↦ (hd t).deriv
  have hab := sum_mul_eq_sub_sub_integral_mul a (f := fun t : ℝ ↦ x - t) (a := (0 : ℝ))
    le_rfl hx (fun t _ ↦ (hd t).differentiableAt) (by rw [hv]; exact continuous_const.integrableOn_Icc)
  simp only [Nat.floor_zero, sub_self, zero_mul, Finset.Icc_self, Finset.sum_singleton,
    show a 0 = 0 by simp [a], mul_zero, sub_zero, hv, neg_one_mul, hA, integral_neg, zero_sub, neg_neg] at hab
  rw [intervalIntegral.integral_of_le hx, ← hab, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [a, hp, mul_comm]

open Filter Topology in
/-- For the trivial rational character the contribution removed by retaining only primes in the
first Riesz mean is asymptotic to two thirds of `x * sqrt x`. The prime number theorem and the
Costa–Pereira inequalities give this limit unconditionally. -/
theorem heckeFirstRieszMean_rat_sub_prime_tendsto :
    Tendsto (fun x : ℝ ↦ ((heckeFirstRieszMean (F := ℚ) 1 x).re -
      ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p * (x - p)) /
      (x * Real.sqrt x)) atTop (𝓝 (2 / 3 : ℝ)) := by
  refine riesz_rat_prime_power_integral.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [← riesz_rat_nonprime_sum_eq_integral hx, heckeFirstRieszMean_eq_norm_sum _ hx]
  simp only [heckeLogDerivCoefficient_trivial_rat, ← Complex.ofReal_mul, Complex.re_sum,
    Complex.ofReal_re]
  congr 1
  rw [eq_sub_iff_add_eq]
  conv_rhs => rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊x⌋₊) Nat.Prime]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]

/-- The discrete derivative of the Riesz mean is exactly the unsmoothed Hecke sum.
A rational-norm atom at `n` is included in this forward difference. -/
theorem heckeFirstRieszMean_forward_sub (χ : U) (n : ℕ) :
    heckeFirstRieszMean χ (n + 1 : ℕ) - heckeFirstRieszMean χ n =
      ∑ k ∈ Finset.Ioc 0 n, heckeLogDerivCoefficient (ideleClassNormTwist χ 0) k := by
  rw [heckeFirstRieszMean_eq_norm_sum _ (Nat.cast_nonneg _), heckeFirstRieszMean_eq_norm_sum _ (Nat.cast_nonneg _)]
  simp only [Nat.floor_natCast]
  rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  simp only [Nat.cast_add, Nat.cast_one,
    sub_self, Complex.ofReal_zero, mul_zero, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

private theorem heckeFirstRieszMean_re_eq (χ : U) (x : ℝ) :
    ((heckeFirstRieszMean χ x).re : ℂ) =
      ∑ᶠ I : I₀, ((Λ(χ, I)).re : ℂ) * (max (x - I.val.absNorm) 0 : ℝ) := by
  classical
  let S := (heckeFirstRieszMean_finite (F := F) x).toFinset
  have hm (I : I₀) (hi : I ∉ S) : max (x - (I.val.absNorm : ℝ)) 0 = 0 := by
    apply max_eq_right
    exact sub_nonpos.mpr (le_of_not_ge (fun h ↦ hi ((Set.Finite.mem_toFinset _).mpr h)))
  have he (f : I₀ → ℂ) : (∑ᶠ I : I₀, f I * (max (x - I.val.absNorm) 0 : ℝ)) =
      ∑ I ∈ S, f I * (max (x - I.val.absNorm) 0 : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro I hi
    by_contra hn
    exact hi (by simp [hm I hn])
  rw [heckeFirstRieszMean, he, he, Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp [Complex.mul_re]

private theorem heckeFirstRieszMean_re_integrable_eq (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) (Ioi 1) ∧
    (∫ x in Ioi (1 : ℝ), ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) =
      ((-logDeriv L s - star (logDeriv L (star s))) / 2) / (s * (s + 1)) := by
  have hq (I : I₀) : (1 : ℝ) ≤ I.val.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  have hsum (w : ℂ) (hw : 1 < w.re) : HasSum (fun I : I₀ ↦ Λ(χ, I) / (I.val.absNorm : ℂ) ^ w)
      (-logDeriv L w) := by
    simpa only [neg_div, neg_neg] using (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨w, hw⟩).2.2.neg
  simp_rw [heckeFirstRieszMean_re_eq]
  apply mellin_firstRieszMean_integrable_eq (fun I : I₀ ↦ (I.val.absNorm : ℝ)) (fun I ↦ ((Λ(χ, I)).re : ℂ)) hq
    (heckeFirstRieszMean_finite (F := F)) (zero_lt_one.trans hs)
  have h := ((hsum s hs).add (Complex.hasSum_conj'.mpr (hsum (star s) hs))).div_const 2
  rw [map_neg] at h
  apply h.congr_fun
  intro I
  have harg : (I.val.absNorm : ℂ).arg ≠ Real.pi := by
    simpa only [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)] using
      Real.pi_pos.ne
  have hv := Complex.conj_cpow (I.val.absNorm : ℂ) s harg
  simp only [map_natCast] at hv
  have hv' : (starRingEnd ℂ) ((I.val.absNorm : ℂ) ^ star s) = (I.val.absNorm : ℂ) ^ s := hv.symm
  simp only [Complex.ofReal_natCast, map_div₀, hv']
  rw [← add_div, show Λ(χ, I) + (starRingEnd ℂ) (Λ(χ, I)) = 2 * ((Λ(χ, I)).re : ℂ) from
    RCLike.add_conj _]
  ring

/-- The readout from a single real arithmetic inequality averages the logarithmic derivative
at `s` with the conjugate of its value at the reflected argument. Thus coincident zero
residues in the two terms have the same sign. -/
theorem heckeFirstRieszMean_re_mellin (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z)
    {s : ℂ} (hs : 1 < s.re) :
    (∫ x in Ioi (1 : ℝ), ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2)) =
      ((-logDeriv L s - star (logDeriv L (star s))) / 2) / (s * (s + 1)) := by
  exact (heckeFirstRieszMean_re_integrable_eq χ L hL hSeries hs).2

/-- The ideal ramp sum is continuous at every real cutoff. Locally it is a finite
sum of ordinary continuous ramps, including at an integral norm. -/
theorem continuous_heckeFirstRieszMean (χ : U) : Continuous (heckeFirstRieszMean χ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  let S := (heckeFirstRieszMean_finite (F := F) (x + 1)).toFinset
  let G (y : ℝ) := ∑ I ∈ S, Λ(χ, I) * (max (y - I.val.absNorm) 0 : ℝ)
  have hG : Continuous G := by unfold G; fun_prop
  apply hG.continuousAt.congr
  filter_upwards [gt_mem_nhds (lt_add_one x)] with y hy
  symm
  apply finsum_eq_sum_of_support_subset
  intro I hi
  apply (Set.Finite.mem_toFinset _).mpr
  change (I.val.absNorm : ℝ) ≤ x + 1
  by_contra! h
  exact hi (by simp [max_eq_right (sub_nonpos.mpr (hy.trans h).le)])

private theorem riesz_log_kernel (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Complex.exp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) ∧
      (x : ℂ) ^ (-s - 2) = (x : ℂ) ^ (-s) / (x : ℂ)^2 := by
  constructor
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le, mul_comm]
  · rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_ofNat]

/-- With log norm as the Laplace variable and ordinary measure on cutoffs above one,
the real centered density is the real ideal ramp sum divided by the cutoff squared,
less half the principal coefficient. Its Laplace integral is absolutely convergent
on the Euler half-plane and has the displayed meromorphic expression there. -/
theorem heckeFirstRieszMean_centered_laplace (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : Complex.re ⁻¹' Ioi (1 : ℝ), L z = finiteHeckeL χ z) (c : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    let f (x : ℝ) : ℝ := (heckeFirstRieszMean χ x).re / x^2 - c/2
    IntegrableOn (fun x : ℝ ↦ (f x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))) (Ioi 1) ∧
      (∫ x in Ioi (1 : ℝ), (f x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))) =
      ((-logDeriv L s - star (logDeriv L (star s))) / 2) / (s * (s + 1)) -
        (c : ℂ) / (2 * (s-1)) := by
  intro f
  obtain ⟨hInt, hEq⟩ := heckeFirstRieszMean_re_integrable_eq χ L hL hSeries hs
  have hr : (-s).re < -1 := by simp; linarith
  have hpow := (integrableOn_Ioi_cpow_of_lt hr zero_lt_one).const_mul ((c : ℂ)/2)
  have he : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), (f x : ℂ) * Complex.exp (-s * (Real.log x : ℂ)) =
      ((heckeFirstRieszMean χ x).re : ℂ) * (x : ℂ) ^ (-s - 2) - (c/2 : ℂ) * (x : ℂ)^(-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    obtain ⟨he, he'⟩ := riesz_log_kernel s (zero_lt_one.trans hx)
    dsimp only [f]
    push_cast
    rw [he, he']
    ring
  constructor
  · exact (hInt.sub hpow).congr (Filter.EventuallyEq.symm he)
  · rw [integral_congr_ae he, integral_sub hInt hpow, hEq, integral_const_mul, integral_Ioi_cpow_of_lt hr zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow, show -s + 1 = -(s-1) by ring, neg_div_neg_eq]
    congr 1
    simp [div_eq_mul_inv, mul_left_comm, mul_comm]

end RiemannMasullo
