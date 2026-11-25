module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Uniqueness of coefficients of exponential sums on a half-line

If `∑ i, b i * exp (w i * y) = 0` for every `y ≥ 0`, where the frequencies `w i` are distinct,
have no accumulation point in `ℂ` and real parts at most `1/2`, and the coefficients are
summable, then every coefficient vanishes. More generally, if the sum is `O(exp (c * y))` on
the half-line, every coefficient whose frequency has real part greater than `c` vanishes.
-/

public section

open Filter Topology Set MeasureTheory

namespace RiemannMasullo

/-- A set without accumulation points in `ℂ` is closed and countable. -/
private theorem expSum_range_closed_countable {ι : Type*} (w : ι → ℂ)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ Set.range w) :
    IsClosed (range w) ∧ (range w).Countable := by
  have h : IsClosed (range w) ∧ IsDiscrete (range w) :=
    isClosed_and_discrete_iff.2 fun x => Filter.disjoint_principal_right.2 (hdisc x)
  exact ⟨h.1, h.1.isLindelof.countable_of_isDiscrete h.2⟩

private theorem expSum_norm_div_le {a x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hx : ρ ≤ ‖x‖) :
    ‖a / x‖ ≤ ‖a‖ * (1 / ρ) := by
  rw [norm_div, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by rw [one_div]; exact inv_anti₀ hρ hx) (norm_nonneg _)

private theorem expSum_aux_dist {x z w : ℂ} {r : ℝ} (h1 : dist x z < r / 2) (h2 : r ≤ dist w z) :
    r / 2 ≤ ‖x - w‖ := by
  rw [← dist_eq_norm]
  have := dist_triangle w x z
  rw [dist_comm w x] at this
  linarith

/-- Laplace transform step: for `Re z > 1/2` the resolvent sum is the Laplace transform of the
exponential sum. -/
private theorem expSum_resolvent_eq_laplace {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hre : ∀ i, (w i).re ≤ 1 / 2) (hb : Summable b) (z : ℂ) (hz : 1 / 2 < z.re) :
    ∑' i, b i / (z - w i) =
      ∫ y in Ioi (0 : ℝ), (∑' i, b i * Complex.exp (w i * y)) * Complex.exp (-(z * y)) := by
  set F : ι → ℝ → ℂ := fun i y => b i * Complex.exp ((w i - z) * y) with hF
  have hlt : ∀ i, (w i - z).re < 0 := fun i => by simp; linarith [hre i]
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_exp_mul_complex_Ioi (hlt i) 0).const_mul (b i)
  have hval : ∀ i, ∫ y in Ioi (0:ℝ), F i y = b i / (z - w i) := by
    intro i
    simp only [F]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (hlt i)]
    have h1 : w i - z ≠ 0 := fun h0 => by have := hlt i; rw [h0] at this; simp at this
    have h2 : z - w i ≠ 0 := fun h0 => h1 (by rw [← neg_sub, h0, neg_zero])
    field_simp
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have hnorm : ∀ i, ∫ y in Ioi (0:ℝ), ‖F i y‖ = ‖b i‖ * (1 / (z.re - (w i).re)) := by
    intro i
    have : ∀ y : ℝ, ‖F i y‖ = ‖b i‖ * Real.exp ((w i - z).re * y) := by
      intro y; simp [F, Complex.norm_exp]
    simp_rw [this]
    rw [integral_const_mul, integral_exp_mul_Ioi (hlt i)]
    congr 1
    simp only [mul_zero, Real.exp_zero, Complex.sub_re]
    rw [neg_div, ← div_neg, neg_sub]
  have hsum : Summable fun i => ∫ y in Ioi (0:ℝ), ‖F i y‖ := by
    simp_rw [hnorm]
    refine (hb.norm.mul_right (1 / (z.re - 1 / 2))).of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    · have := hre i
      exact mul_nonneg (norm_nonneg _) (by rw [one_div]; exact inv_nonneg.2 (by linarith))
    · have := hre i
      gcongr
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hval] at key
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  have : ∀ i, F i y = Complex.exp (-(z * y)) * (b i * Complex.exp (w i * y)) := by
    intro i
    simp only [F, sub_eq_add_neg, add_mul, Complex.exp_add, neg_mul]
    ring
  simp_rw [this, tsum_mul_left]
  ring

/-- Laplace transform step: the resolvent sum vanishes on `Re z > 1/2`. -/
private theorem expSum_resolvent_eq_zero {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hre : ∀ i, (w i).re ≤ 1 / 2) (hb : Summable b)
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) 0)
    (z : ℂ) (hz : 1 / 2 < z.re) :
    ∑' i, b i / (z - w i) = 0 := by
  rw [expSum_resolvent_eq_laplace w b hre hb z hz]
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  rw [(h y (le_of_lt hy)).tsum_eq, zero_mul]

/-- The resolvent sum is holomorphic off the (closed) range of `w`. -/
private theorem expSum_resolvent_differentiableOn {ι : Type*} (w b : ι → ℂ) (hb : Summable b)
    (hcl : IsClosed (range w)) :
    DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (range w)ᶜ := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl z hz
  have hfar : ∀ i, r ≤ dist (w i) z := fun i => by
    by_contra hcon
    exact hball (Metric.mem_ball.2 (not_le.1 hcon)) ⟨i, rfl⟩
  have hd : DifferentiableOn ℂ (fun z => ∑' i, b i / (z - w i)) (Metric.ball z (r / 2)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (F := fun i x => b i / (x - w i)) (u := fun i => ‖b i‖ * (1 / (r / 2)))
      (hb.norm.mul_right _) (fun i => ?_) Metric.isOpen_ball (fun i x hx => ?_)
    · have hne : ∀ x ∈ Metric.ball z (r / 2), x - w i ≠ 0 := fun x hx h0 => by
        have := expSum_aux_dist (Metric.mem_ball.1 hx) (hfar i)
        rw [h0, norm_zero] at this
        linarith
      exact (differentiableOn_const (b i)).div (differentiableOn_id.sub_const (w i)) hne
    · exact expSum_norm_div_le (by linarith) (expSum_aux_dist (Metric.mem_ball.1 hx) (hfar i))
  exact (hd.differentiableAt (Metric.ball_mem_nhds z (by linarith))).differentiableWithinAt

attribute [local instance 3000] SeminormedAddCommGroup.toPseudoMetricSpace
  NormedAddCommGroup.toSeminormedAddCommGroup in
/-- Uniqueness of coefficients of an exponential sum on a half-line. Let the frequencies `w i`
be distinct, have no accumulation point in `ℂ`, and satisfy `Re (w i) ≤ 1/2`. If the
coefficients `b` are summable and `∑ i, b i * exp (w i * y) = 0` for every `y ≥ 0`, then every
`b i` is zero. The proof takes a Laplace transform for `Re z > 1/2`, which gives
`∑ i, b i / (z - w i) = 0`, extends this to the complement of the frequencies by the identity
theorem, and lets `z` tend to each frequency. -/
theorem eq_zero_of_hasSum_exp_eq_zero {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b)
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) 0) :
    ∀ i, b i = 0 := by
  classical
  obtain ⟨hcl, hcount⟩ := expSum_range_closed_countable w hdisc
  have hre' : ∀ i, (w i).re ≤ 1 / 2 := hre
  have : Countable ι := by
    have := hcount.to_subtype
    exact Function.Injective.countable (f := fun i => (⟨w i, i, rfl⟩ : range w))
      fun a b hab => hw (congrArg Subtype.val hab)
  set R : ℂ → ℂ := fun z => ∑' i, b i / (z - w i) with hR
  have hU : IsPreconnected (range w)ᶜ :=
    (hcount.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])).isPreconnected
  have han : AnalyticOnNhd ℂ R (range w)ᶜ :=
    (expSum_resolvent_differentiableOn w b hb hcl).analyticOnNhd hcl.isOpen_compl
  have h1 : (1 : ℂ) ∈ (range w)ᶜ := by
    rintro ⟨i, hi⟩
    have := hre' i
    rw [hi] at this
    norm_num at this
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ), R z = 0 := by
    have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})] with z hz
    exact expSum_resolvent_eq_zero w b hre' hb h z hz
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h1
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  intro i₀
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hdisc (w i₀)))
  have hfar : ∀ i, i ≠ i₀ → ε ≤ dist (w i) (w i₀) := fun i hi => by
    by_contra hcon
    exact hεball (not_le.1 hcon) (fun h0 => hi (hw h0)) ⟨i, rfl⟩
  set C := (∑' i, ‖b i‖) * (1 / (ε / 2)) with hC
  have hbound : ∀ δ : ℝ, δ ∈ Ioo 0 (ε / 2) → ‖b i₀‖ ≤ δ * C := by
    rintro δ ⟨hδ0, hδε⟩
    set z : ℂ := w i₀ + δ with hz
    have hzw : z - w i₀ = δ := by rw [hz]; ring
    have hdist : dist z (w i₀) = δ := by
      rw [dist_eq_norm, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have hzU : z ∈ (range w)ᶜ :=
      hεball (by rw [hdist]; linarith) (fun h0 => by
        rw [h0, dist_self] at hdist; linarith)
    have hRz : R z = 0 := hzero hzU
    have hfar' : ∀ i, i ≠ i₀ → ε / 2 ≤ ‖z - w i‖ := fun i hi => by
      have := hfar i hi
      have := expSum_aux_dist (x := z) (z := w i₀) (w := w i) (r := ε) (by rw [hdist]; linarith) this
      exact this
    have hsumm : Summable fun i => b i / (z - w i) := by
      refine Summable.of_norm_bounded (g := fun i => ‖b i‖ * (1 / δ)) (hb.norm.mul_right _)
        fun i => ?_
      by_cases hi : i = i₀
      · subst hi
        exact expSum_norm_div_le hδ0 (by rw [hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0])
      · exact expSum_norm_div_le hδ0 (by linarith [hfar' i hi])
    have hsplit := hsumm.tsum_eq_add_tsum_ite i₀
    have hS : ‖∑' i, if i = i₀ then 0 else b i / (z - w i)‖ ≤ C := by
      rw [hC, ← tsum_mul_right]
      refine tsum_of_norm_bounded (hb.norm.mul_right (1 / (ε / 2))).hasSum fun i => ?_
      · by_cases hi : i = i₀
        · simp only [hi, ite_true, norm_zero]
          exact mul_nonneg (norm_nonneg _) (by positivity)
        · simp only [hi, ite_false]
          exact expSum_norm_div_le (by linarith) (hfar' i hi)
    have h0 : b i₀ / (z - w i₀) = -∑' i, if i = i₀ then 0 else b i / (z - w i) := by
      have : R z = ∑' i, b i / (z - w i) := rfl
      rw [hRz, hsplit] at this
      linear_combination -this
    have hn : ‖b i₀‖ / δ ≤ C := by
      have := congrArg norm h0
      rw [norm_neg, norm_div, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at this
      rw [this]; exact hS
    rw [div_le_iff₀ hδ0] at hn
    linarith
  have hlim : Tendsto (fun δ : ℝ => δ * C) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => δ * C) (𝓝 0) (𝓝 (0 * C)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖b i₀‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hε))
      fun δ hδ => hbound δ hδ)
  exact norm_le_zero_iff.1 hle

/-! ### Exponential sums of slow growth -/

/-- The half-plane `c < re z` with a countable set removed is preconnected: it is the image of
the complement of a countable set under a homeomorphism of `ℂ` onto the half-plane. -/
private theorem expSum_halfPlane_diff_isPreconnected (c : ℝ) {A : Set ℂ} (hA : A.Countable) :
    IsPreconnected ({z : ℂ | c < z.re} \ A) := by
  let f : ℂ → ℂ := fun ζ ↦ ((c + Real.exp ζ.re : ℝ) : ℂ) + (ζ.im : ℂ) * Complex.I
  have hf : Continuous f := by fun_prop
  have hre (ζ : ℂ) : (f ζ).re = c + Real.exp ζ.re := by simp [f, Complex.exp_ofReal_re]
  have him (ζ : ℂ) : (f ζ).im = ζ.im := by simp [f]
  have hinj : Function.Injective f := fun ζ ξ h ↦ by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    rw [hre, hre, add_right_inj] at h1
    rw [him, him] at h2
    exact Complex.ext (Real.exp_injective h1) h2
  have himg : f '' (f ⁻¹' A)ᶜ = {z : ℂ | c < z.re} \ A := by
    ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      exact ⟨by rw [mem_ofPred_eq, hre]; linarith [Real.exp_pos ζ.re], hζ⟩
    · rintro ⟨hz, hzA⟩
      have hz' : 0 < z.re - c := sub_pos.mpr hz
      have hfz : f (((Real.log (z.re - c) : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) = z := by
        apply Complex.ext
        · rw [hre]; simp [Real.exp_log hz']
        · rw [him]; simp
      exact ⟨_, by rw [mem_compl_iff, mem_preimage, hfz]; exact hzA, hfz⟩
  rw [← himg]
  exact ((hA.preimage hinj).isConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex])).isPreconnected.image f hf.continuousOn

/-- An exponential sum with frequencies of real part at most `1/2` is continuous on the
half-line `y ≥ 0`. -/
private theorem expSum_continuousOn {ι : Type*} (w b : ι → ℂ) (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) :
    ContinuousOn (fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) (Ici 0) := by
  intro y₀ hy₀
  have hY : ContinuousOn (fun y : ℝ ↦ ∑' i, b i * Complex.exp (w i * y)) (Icc 0 (y₀ + 1)) := by
    refine continuousOn_tsum (u := fun i ↦ ‖b i‖ * Real.exp ((y₀ + 1) / 2))
      (fun i ↦ (by fun_prop : Continuous fun y : ℝ ↦ b i * Complex.exp (w i * y)).continuousOn)
      (hb.norm.mul_right _) (fun i y hy ↦ ?_)
    rw [norm_mul, Complex.norm_exp]
    gcongr
    have hwy : (w i * (y : ℂ)).re = (w i).re * y := by simp
    rw [hwy]
    nlinarith [hre i, hy.1, hy.2]
  exact (hY.continuousWithinAt ⟨hy₀, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_of_superset (inter_mem_nhdsWithin _ (Iio_mem_nhds (by linarith : y₀ < y₀ + 1)))
      fun y hy ↦ ⟨hy.1, hy.2.le⟩)

/-- The Laplace transform of a function with a majorant `D`, such that `D y * exp (-σ * y)` is
integrable on the half-line, converges for `Re z ≥ σ`, with modulus at most that integral. -/
private theorem expSum_laplace_integrable (S : ℝ → ℂ) (hS : ContinuousOn S (Ici 0)) (D : ℝ → ℝ)
    (hD : ∀ y, 0 ≤ y → ‖S y‖ ≤ D y) {σ : ℝ}
    (hDi : IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi 0)) {z : ℂ} (hz : σ ≤ z.re) :
    IntegrableOn (fun y : ℝ ↦ S y * Complex.exp (-(z * y))) (Ioi 0) ∧
      ‖∫ y in Ioi (0 : ℝ), S y * Complex.exp (-(z * y))‖ ≤
        ∫ y in Ioi (0 : ℝ), D y * Real.exp (-σ * y) := by
  have hle : ∀ y ∈ Ioi (0 : ℝ),
      ‖S y * Complex.exp (-(z * y))‖ ≤ D y * Real.exp (-σ * y) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hzy : (-(z * (y : ℂ))).re = -(z.re * y) := by simp
    rw [norm_mul, Complex.norm_exp, hzy]
    exact mul_le_mul (hD y hy0.le) (Real.exp_le_exp.mpr (by nlinarith))
      (Real.exp_pos _).le ((norm_nonneg _).trans (hD y hy0.le))
  have hmeas : AEStronglyMeasurable (fun y : ℝ ↦ S y * Complex.exp (-(z * y)))
      (volume.restrict (Ioi 0)) :=
    ((hS.mono Ioi_subset_Ici_self).mul
      (Continuous.continuousOn (by fun_prop))).aestronglyMeasurable measurableSet_Ioi
  have hae : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖S y * Complex.exp (-(z * y))‖ ≤ D y * Real.exp (-σ * y) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy using hle y hy
  exact ⟨hDi.mono' hmeas hae, norm_integral_le_of_norm_le hDi hae⟩

/-- The Laplace transform of a function with a majorant `D`, such that `D y * exp (-σ * y)` is
integrable on the half-line for every `σ > c`, is holomorphic on `Re z > c`. -/
private theorem expSum_laplace_differentiableAt (S : ℝ → ℂ) (hS : ContinuousOn S (Ici 0))
    (D : ℝ → ℝ) (hD : ∀ y, 0 ≤ y → ‖S y‖ ≤ D y) {c : ℝ}
    (hDi : ∀ σ, c < σ → IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi 0)) {z₀ : ℂ}
    (hz₀ : c < z₀.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ ∫ y in Ioi (0 : ℝ), S y * Complex.exp (-(z * y))) z₀ := by
  set ε := (z₀.re - c) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hcont (z : ℂ) : ContinuousOn (fun y : ℝ ↦ S y * Complex.exp (-(z * y))) (Ioi 0) :=
    (hS.mono Ioi_subset_Ici_self).mul (Continuous.continuousOn (by fun_prop))
  have hcont' : ContinuousOn (fun y : ℝ ↦ S y * (-(y : ℂ) * Complex.exp (-(z₀ * y)))) (Ioi 0) :=
    (hS.mono Ioi_subset_Ici_self).mul (Continuous.continuousOn (by fun_prop))
  have hbound : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ Metric.ball z₀ ε,
      ‖S y * (-(y : ℂ) * Complex.exp (-(z * y)))‖ ≤
        1 / ε * (D y * Real.exp (-(c + ε) * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    have hy0 : (0 : ℝ) < y := hy
    have hzre : z₀.re - ε < z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [← dist_eq_norm, Complex.sub_re] at h1
      have h2 := (abs_lt.mp (h1.trans_lt (Metric.mem_ball.mp hz))).1
      linarith
    have hzy : (-(z * (y : ℂ))).re = -(z.re * y) := by simp
    have hy1 : y ≤ Real.exp (ε * y) / ε := by
      rw [le_div_iff₀ hε0]
      have := Real.add_one_le_exp (ε * y)
      linarith
    have hDy : ‖S y‖ ≤ D y := hD y hy0.le
    have hD0 : 0 ≤ D y := (norm_nonneg _).trans hDy
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
      Complex.norm_exp, hzy]
    calc ‖S y‖ * (y * Real.exp (-(z.re * y)))
        ≤ D y * (Real.exp (ε * y) / ε * Real.exp (-(z.re * y))) :=
          mul_le_mul hDy (mul_le_mul_of_nonneg_right hy1 (Real.exp_pos _).le)
            (mul_nonneg hy0.le (Real.exp_pos _).le) hD0
      _ = 1 / ε * (D y * Real.exp ((ε - z.re) * y)) := by
          rw [show (ε - z.re) * y = ε * y + -(z.re * y) by ring, Real.exp_add]
          ring
      _ ≤ 1 / ε * (D y * Real.exp (-(c + ε) * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hD0)
            (by positivity)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun z y ↦ S y * Complex.exp (-(z * y)))
    (F' := fun z y ↦ S y * (-(y : ℂ) * Complex.exp (-(z * y))))
    (bound := fun y ↦ 1 / ε * (D y * Real.exp (-(c + ε) * y))) (Metric.ball_mem_nhds z₀ hε0)
    (Eventually.of_forall fun z ↦ (hcont z).aestronglyMeasurable measurableSet_Ioi)
    (expSum_laplace_integrable S hS D hD (hDi z₀.re hz₀) le_rfl).1
    (hcont'.aestronglyMeasurable measurableSet_Ioi) hbound
    ((hDi (c + ε) (by linarith)).const_mul _)
    (ae_of_all _ fun y z _ ↦ by
      convert ((hasDerivAt_mul_const (y : ℂ)).neg.cexp).const_mul (S y) using 1
      simp only [Pi.neg_apply]
      ring)
  exact hderiv.2.differentiableAt

/-- Exponential sums of slow growth on a half-line. Let the frequencies `w i` be distinct, have
no accumulation point in `ℂ`, and satisfy `Re (w i) ≤ 1/2`, and let the coefficients `b` be
summable. Suppose the sum `S y = ∑ i, b i * exp (w i * y)` has a majorant `D` on `y ≥ 0` such
that `D y * exp (-σ * y)` is integrable on the half-line for every `σ > c`. Then `b i = 0` for
every frequency with `c < Re (w i)`. The Laplace transform of `S` is holomorphic on `Re z > c`
and equals `∑ i, b i / (z - w i)` for `Re z > 1/2`. By the identity theorem on the half-plane
`Re z > c` with the frequencies removed, the resolvent sum stays bounded as `z` tends to a
frequency to the right of `c`. -/
theorem eq_zero_of_hasSum_exp_of_integrable {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (D : ℝ → ℝ) (hS : ∀ y : ℝ, 0 ≤ y → ‖S y‖ ≤ D y)
    (hDi : ∀ σ, c < σ → IntegrableOn (fun y ↦ D y * Real.exp (-σ * y)) (Ioi (0 : ℝ))) :
    ∀ i, c < (w i).re → b i = 0 := by
  classical
  intro i₀ hi₀
  obtain ⟨hcl, hcount⟩ := expSum_range_closed_countable w hdisc
  have : Countable ι := by
    have := hcount.to_subtype
    exact Function.Injective.countable (f := fun i => (⟨w i, i, rfl⟩ : range w))
      fun a b hab => hw (congrArg Subtype.val hab)
  set T : ℝ → ℂ := fun y ↦ ∑' i, b i * Complex.exp (w i * y) with hT
  have hTb : ∀ y, 0 ≤ y → ‖T y‖ ≤ D y := fun y hy ↦ by
    rw [show T y = S y from (h y hy).tsum_eq]; exact hS y hy
  have hTc : ContinuousOn T (Ici 0) := expSum_continuousOn w b hre hb
  set R : ℂ → ℂ := fun z => ∑' i, b i / (z - w i) with hR
  set L : ℂ → ℂ := fun z => ∫ y in Ioi (0 : ℝ), T y * Complex.exp (-(z * y)) with hL
  have hc : c < 1 / 2 := hi₀.trans_le (hre i₀)
  set V : Set ℂ := {z : ℂ | c < z.re} \ range w with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).sdiff hcl
  have hRa : AnalyticOnNhd ℂ R V :=
    ((expSum_resolvent_differentiableOn w b hb hcl).mono fun z (hz : z ∈ V) ↦ hz.2).analyticOnNhd hVo
  have hLa : AnalyticOnNhd ℂ L V :=
    DifferentiableOn.analyticOnNhd (fun z (hz : z ∈ V) ↦
      (expSum_laplace_differentiableAt T hTc D hTb hDi hz.1).differentiableWithinAt) hVo
  have h1 : (1 : ℂ) ∈ V := by
    refine ⟨by change c < (1 : ℂ).re; simp; linarith, ?_⟩
    rintro ⟨i, hi⟩
    have := hre i
    rw [hi] at this
    norm_num at this
  have hev : ∀ᶠ z in 𝓝 (1 : ℂ), (R - L) z = 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℂ) ∈ {z : ℂ | 1 / 2 < z.re})] with z hz
    rw [Pi.sub_apply, sub_eq_zero]
    exact expSum_resolvent_eq_laplace w b hre hb z hz
  have hzero := (hRa.sub hLa).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (expSum_halfPlane_diff_isPreconnected c hcount) h1
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.1
    (eventually_nhdsWithin_iff.1 (hdisc (w i₀)))
  have hfar : ∀ i, i ≠ i₀ → ε ≤ dist (w i) (w i₀) := fun i hi => by
    by_contra hcon
    exact hεball (not_le.1 hcon) (fun h0 => hi (hw h0)) ⟨i, rfl⟩
  set C₂ := (∑' i, ‖b i‖) * (1 / (ε / 2)) with hC₂
  set σ' := (c + (w i₀).re) / 2 with hσ'
  set C₁ := ∫ y in Ioi (0 : ℝ), D y * Real.exp (-σ' * y) with hC₁
  have hbound : ∀ δ : ℝ, δ ∈ Ioo 0 (ε / 2) → ‖b i₀‖ ≤ δ * (C₁ + C₂) := by
    rintro δ ⟨hδ0, hδε⟩
    set z : ℂ := w i₀ + δ with hz
    have hzw : z - w i₀ = δ := by rw [hz]; ring
    have hdist : dist z (w i₀) = δ := by
      rw [dist_eq_norm, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0]
    have hzre : z.re = (w i₀).re + δ := by simp [hz]
    have hzU : z ∈ V := by
      refine ⟨by change c < z.re; rw [hzre]; linarith, ?_⟩
      exact hεball (by rw [hdist]; linarith) (fun h0 => by
        rw [h0, dist_self] at hdist; linarith)
    have hRz : R z = L z := sub_eq_zero.mp (hzero hzU)
    have hLz : ‖L z‖ ≤ C₁ :=
      (expSum_laplace_integrable T hTc D hTb (hDi σ' (by rw [hσ']; linarith))
        (by rw [hzre, hσ']; linarith)).2
    have hfar' : ∀ i, i ≠ i₀ → ε / 2 ≤ ‖z - w i‖ := fun i hi =>
      expSum_aux_dist (x := z) (z := w i₀) (w := w i) (r := ε) (by rw [hdist]; linarith)
        (hfar i hi)
    have hsumm : Summable fun i => b i / (z - w i) := by
      refine Summable.of_norm_bounded (g := fun i => ‖b i‖ * (1 / δ)) (hb.norm.mul_right _)
        fun i => ?_
      by_cases hi : i = i₀
      · subst hi
        exact expSum_norm_div_le hδ0
          (by rw [hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0])
      · exact expSum_norm_div_le hδ0 (by linarith [hfar' i hi])
    have hsplit := hsumm.tsum_eq_add_tsum_ite i₀
    have hS' : ‖∑' i, if i = i₀ then 0 else b i / (z - w i)‖ ≤ C₂ := by
      rw [hC₂, ← tsum_mul_right]
      refine tsum_of_norm_bounded (hb.norm.mul_right (1 / (ε / 2))).hasSum fun i => ?_
      · by_cases hi : i = i₀
        · simp only [hi, ite_true, norm_zero]
          exact mul_nonneg (norm_nonneg _) (by positivity)
        · simp only [hi, ite_false]
          exact expSum_norm_div_le (by linarith) (hfar' i hi)
    have h0 : b i₀ / (z - w i₀) = L z - ∑' i, if i = i₀ then 0 else b i / (z - w i) := by
      have : R z = ∑' i, b i / (z - w i) := rfl
      rw [hRz, hsplit] at this
      linear_combination -this
    have hn : ‖b i₀‖ / δ ≤ C₁ + C₂ := by
      have := congrArg norm h0
      rw [norm_div, hzw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0] at this
      rw [this]
      exact (norm_sub_le _ _).trans (add_le_add hLz hS')
    rw [div_le_iff₀ hδ0] at hn
    linarith
  have hlim : Tendsto (fun δ : ℝ => δ * (C₁ + C₂)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => δ * (C₁ + C₂)) (𝓝 0) (𝓝 (0 * (C₁ + C₂))) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ‖b i₀‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hε))
      fun δ hδ => hbound δ hδ)
  exact norm_le_zero_iff.1 hle

/-- Exponential sums of slow growth on a half-line, with a pointwise bound: if
`‖∑ i, b i * exp (w i * y)‖ ≤ C * exp (c * y)` for every `y ≥ 0`, then `b i = 0` for every
frequency with `c < Re (w i)` (`eq_zero_of_hasSum_exp_of_integrable`). -/
theorem eq_zero_of_hasSum_exp_of_norm_le {ι : Type*} (w : ι → ℂ) (b : ι → ℂ)
    (hw : Function.Injective w)
    (hdisc : ∀ z : ℂ, ∀ᶠ u in nhdsWithin z {z}ᶜ, u ∉ Set.range w)
    (hre : ∀ i, (w i).re ≤ 1 / 2)
    (hb : Summable b) (S : ℝ → ℂ) {C c : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    (hS : ∀ y : ℝ, 0 ≤ y → ‖S y‖ ≤ C * Real.exp (c * y)) :
    ∀ i, c < (w i).re → b i = 0 :=
  eq_zero_of_hasSum_exp_of_integrable w b hw hdisc hre hb S h (fun y ↦ C * Real.exp (c * y)) hS
    fun σ hσ ↦ by
      have h1 : IntegrableOn (fun y ↦ C * Real.exp ((c - σ) * y)) (Ioi 0) :=
        (integrableOn_exp_mul_Ioi (by linarith : c - σ < 0) 0).const_mul C
      refine h1.congr_fun (fun y _ ↦ ?_) measurableSet_Ioi
      show C * Real.exp ((c - σ) * y) = C * Real.exp (c * y) * Real.exp (-σ * y)
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end RiemannMasullo
