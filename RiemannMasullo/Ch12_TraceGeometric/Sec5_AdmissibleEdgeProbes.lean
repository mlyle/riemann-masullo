module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_PositiveEdgeProbes
import all RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Admissible probes on the ordinates of a completed zero divisor

For the signed width comparison in §12.5, pp. 519–520, construct compact smooth probes
vanishing on norm-one classes. The same radial profiles can be prescribed for every field.
-/

@[expose] public noncomputable section

open Set Function MeasureTheory Metric Filter
open scoped ContDiff Topology

namespace RiemannMasullo

private def cosine (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x : ℝ, f x * Real.cos (t*x)

private theorem ibp (f q q' : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (fc : HasCompactSupport f)
    (hq : ∀ x, HasDerivAt q (q' x) x) (hq' : Continuous q') :
    ∫ x, deriv f x * q x = -∫ x, f x * q' x := by
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x ↦ (hq x).continuousAt
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := q) (u' := q') (v := f) (v' := deriv f) (fun x _ ↦ hq x)
    (fun x _ ↦ (hf.differentiable (by simp) x).hasDerivAt)
    ((hqc.mul (hf.continuous_deriv (by simp))).integrable_of_hasCompactSupport fc.deriv.mul_left)
    ((hq'.mul hf.continuous).integrable_of_hasCompactSupport fc.mul_left)
    ((hqc.mul hf.continuous).integrable_of_hasCompactSupport fc.mul_left)
  simpa only [mul_comm] using h

private theorem cosine_second (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (fc : HasCompactSupport f) (t : ℝ) :
    cosine (deriv (deriv f)) t = -t^2 * cosine f t := by
  have hc (x : ℝ) : HasDerivAt (fun x ↦ Real.cos (t*x)) (-t * Real.sin (t*x)) x := by
    convert! ((hasDerivAt_id x).const_mul t).cos using 1; simp; ring
  have hs (x : ℝ) : HasDerivAt (fun x ↦ Real.sin (t*x)) (t * Real.cos (t*x)) x := by
    convert! ((hasDerivAt_id x).const_mul t).sin using 1; simp; ring
  have h₁ := ibp (deriv f) _ _ ((contDiff_infty_iff_deriv.mp hf).2) fc.deriv hc (by fun_prop)
  have h₂ := ibp f _ _ hf fc hs (by fun_prop)
  simp only [cosine]
  rw [h₁]
  simp_rw [show ∀ x, deriv f x * (-t * Real.sin (t*x)) =
    -t * (deriv f x * Real.sin (t*x)) from fun _ ↦ by ring]
  rw [integral_const_mul, h₂]
  simp_rw [show ∀ x, f x * (t * Real.cos (t*x)) = t * (f x * Real.cos (t*x)) from fun _ ↦ by ring]
  rw [integral_const_mul]
  ring

private theorem cosine_gap_filter (K : ℝ → ℝ) (hs : ContDiff ℝ ∞ K) (hc : HasCompactSupport K)
    (h0 : 0 < K 0) (hpos : ∀ t, 0 < cosine K t) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ G 0 = 0 ∧
      ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R < |t| → 0 < cosine G t := by
  let c := deriv (deriv K) 0 / K 0
  let G := fun x ↦ c * K x - deriv (deriv K) x
  have hss := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hs).2).2
  have hGs : ContDiff ℝ ∞ G := (contDiff_const.mul hs).sub hss
  refine ⟨G, hGs, (hc.mul_left (f := fun _ ↦ c)).sub hc.deriv.deriv, ?_, |c|+1, by positivity, ?_⟩
  · dsimp [G, c]
    rw [div_mul_cancel₀ _ h0.ne', sub_self]
  intro t ht
  have hq : Continuous fun x : ℝ ↦ Real.cos (t*x) := by fun_prop
  have h1 : Integrable (fun x ↦ (c * K x) * Real.cos (t*x)) := (((continuous_const.mul hs.continuous).mul hq).integrable_of_hasCompactSupport
    ((hc.mul_left (f := fun _ ↦ c)).mul_right (f' := fun x ↦ Real.cos (t*x))))
  have h2 : Integrable (fun x ↦ deriv (deriv K) x * Real.cos (t*x)) := (hss.continuous.mul hq).integrable_of_hasCompactSupport hc.deriv.deriv.mul_right
  have heq : cosine G t = (c+t^2) * cosine K t := by
    unfold cosine G
    simp_rw [sub_mul]
    rw [integral_sub h1 h2]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    change c * cosine K t - cosine (deriv (deriv K)) t = _
    rw [cosine_second K hs hc]
    unfold cosine
    ring
  rw [heq]
  apply mul_pos _ (hpos t)
  nlinarith [neg_abs_le c, sq_abs t, abs_nonneg t, mul_self_nonneg (|t|-1)]



private theorem cosine_dilate (G : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (t : ℝ) :
    cosine (fun x ↦ G (L⁻¹*x)) t = L * cosine G (L*t) := by
  let f := fun x : ℝ ↦ G x * Real.cos ((L*t)*x)
  calc
    cosine (fun x ↦ G (L⁻¹*x)) t = ∫ x : ℝ, f (L⁻¹*x) := by
      apply integral_congr_ae
      filter_upwards with x
      change _ = G (L⁻¹*x) * Real.cos ((L*t)*(L⁻¹*x))
      rw [show L*t*(L⁻¹*x) = t*x by field_simp]
    _ = |L| • ∫ y, f y := Measure.integral_comp_inv_mul_left f L
    _ = _ := by rw [abs_of_pos hL]; rfl

private theorem cosine_modulate (G : ℝ → ℝ) (hc : Continuous G) (hs : HasCompactSupport G) (T t : ℝ) :
    cosine (fun x ↦ G x * Real.cos (T*x)) t =
      (cosine G (t-T) + cosine G (t+T))/2 := by
  have hi (u : ℝ) : Integrable (fun x ↦ G x * Real.cos (u*x)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  unfold cosine
  rw [← integral_add (hi _) (hi _), ← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
  ring

private theorem cosine_positive_on_gap (G : ℝ → ℝ) (hGs : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G)
    (hG0 : G 0 = 0) {R T d : ℝ} (hR : 0 < R)
    (hg : ∀ t : ℝ, R < |t| → 0 < cosine G t) (hd : 0 < d) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ P 0 = 0 ∧
      ∀ t : ℝ, d ≤ |t - T| → d ≤ |t + T| → 0 < cosine P t := by
  let L := (R+1)/d
  have hL : 0 < L := div_pos (by positivity) hd
  have hLd : L*d = R+1 := div_mul_cancel₀ _ hd.ne'
  let U := fun x : ℝ ↦ G (L⁻¹*x)
  have hUs : ContDiff ℝ ∞ U := hGs.comp (contDiff_const.mul contDiff_id)
  have hUc : HasCompactSupport U := hGc.comp_homeomorph (Homeomorph.mulLeft₀ _ (inv_ne_zero hL.ne'))
  refine ⟨fun x ↦ U x * Real.cos (T*x), hUs.mul (by fun_prop), hUc.mul_right, by simp [U,hG0], ?_⟩
  intro t hm hp
  rw [cosine_modulate U hUs.continuous hUc]
  have hu (u : ℝ) (hu : d ≤ |u|) : 0 < cosine U u := by
    rw [show U = fun x ↦ G (L⁻¹*x) from rfl, cosine_dilate G hL]
    apply mul_pos hL (hg _ ?_)
    rw [abs_mul, abs_of_pos hL]
    linarith [mul_le_mul_of_nonneg_left hu hL.le]
  positivity [hu _ hm, hu _ hp]


private def realEdge (H : ℝ → ℝ) (b t : ℝ) : ℝ := ∫ x : ℝ, H x * Real.exp (b*x) * Real.cos (t*x)
private def balanced (P : ℝ → ℝ) (b x : ℝ) : ℝ :=
  (P x + P (-x)) / (Real.exp (b*x) + Real.exp (-b*x))

private theorem balanced_properties (P : ℝ → ℝ) (hPs : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (hP0 : P 0 = 0) (b : ℝ) :
    ContDiff ℝ ∞ (balanced P b) ∧ HasCompactSupport (balanced P b) ∧
    balanced P b 0 = 0 ∧ ∀ x, balanced P b (-x) = balanced P b x := by
  have hneg : HasCompactSupport (fun x ↦ P (-x)) := by
    convert! hPc.comp_homeomorph (Homeomorph.neg ℝ) using 1
  refine ⟨(hPs.add (hPs.comp contDiff_neg)).div (by fun_prop) (fun x ↦ ?_), ?_, ?_, ?_⟩
  · exact (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  · change HasCompactSupport (fun x : ℝ ↦ (P x + P (-x)) / (Real.exp (b*x)+Real.exp (-b*x)))
    simp only [div_eq_mul_inv]
    exact (hPc.add hneg).mul_right
  · simp [balanced, hP0]
  · intro x
    simp [balanced, add_comm]

private theorem integral_reflect (f : ℝ → ℝ) : (∫ x : ℝ, f (-x)) = ∫ x, f x := by
  simpa using Measure.integral_comp_mul_left f (-1)

private theorem realEdge_balanced (P : ℝ → ℝ) (hPs : Continuous P) (hPc : HasCompactSupport P)
    (b t : ℝ) : realEdge (balanced P b) b t = cosine P t := by
  let W (a x : ℝ) := P x * (Real.exp (a*x) / (Real.exp (a*x)+Real.exp (-a*x))) * Real.cos (t*x)
  have hden (a x : ℝ) : Real.exp (a*x) + Real.exp (-a*x) ≠ 0 := by positivity
  have hi (a : ℝ) : Integrable (W a) := by
    have hnum : Continuous fun x : ℝ ↦ Real.exp (a*x) := by fun_prop
    have hdenC : Continuous fun x : ℝ ↦ Real.exp (a*x)+Real.exp (-a*x) := by fun_prop
    have hc : Continuous (W a) := (hPs.mul (hnum.div hdenC (hden a))).mul (by fun_prop)
    exact hc.integrable_of_hasCompactSupport (hPc.mul_right.mul_right)
  have hneg : Integrable (fun x ↦ W (-b) (-x)) := by
    simpa using (hi (-b)).comp_neg
  calc
    realEdge (balanced P b) b t = ∫ x : ℝ, W b x + W (-b) (-x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [realEdge, balanced, W]
      simp only [neg_neg, mul_neg, Real.cos_neg, neg_mul]
      field_simp
    _ = (∫ x, W b x) + ∫ x, W (-b) x := by rw [integral_add (hi b) hneg, integral_reflect]
    _ = cosine P t := by
      rw [← integral_add (hi b) (hi (-b))]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [W]
      rw [neg_neg, add_comm (Real.exp (-b*x)) (Real.exp (b*x))]
      field_simp [hden b x]

private theorem realEdge_balanced_neg (P : ℝ → ℝ) (hPs : Continuous P) (hPc : HasCompactSupport P)
    (b t : ℝ) : realEdge (balanced P b) (-b) t = cosine P t := by
  have h : balanced P b = balanced P (-b) := by
    funext x
    simp [balanced, add_comm]
  rw [h, realEdge_balanced P hPs hPc]

private theorem laplace_realEdge (H : ℝ → ℝ) (hH : Continuous H) (hHc : HasCompactSupport H)
    (b t : ℝ) :
    (bilateralLaplace (fun x ↦ (H x : ℂ)) ((b : ℂ) + (t : ℂ) * Complex.I)).re =
      realEdge H b t := by
  have hint : Integrable (fun x : ℝ ↦ (H x : ℂ) *
      Complex.exp (((b : ℂ) + (t : ℂ) * Complex.I) * x)) :=
    ((Complex.continuous_ofReal.comp hH).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hHc.comp_left Complex.ofReal_zero).mul_right)
  rw [bilateralLaplace, ← RCLike.re_eq_complex_re, ← integral_re hint,
    RCLike.re_eq_complex_re]
  simp [realEdge, Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_assoc]

private theorem punctured_divisor_ordinates (D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) :
    ∃ d : ℝ, 0 < d ∧ ∀ z : ℂ, D z ≠ 0 → z.re ∈ Icc 0 1 →
      |z.im| = 1 ∨ d ≤ abs (|z.im| - 1) := by
  let S := Metric.closedBall (0:ℂ) 4 ∩ D.support
  have hfin : S.Finite :=
    ((isCompact_closedBall _ _).inter_right (D.closedSupport isClosed_univ)).finite
      (D.discreteSupport.mono inter_subset_right)
  let E := (fun z : ℂ ↦ |z.im|) '' S \ {1}
  have hE : E.Finite := (hfin.image _).sdiff
  have hnot : (1:ℝ) ∈ Eᶜ := by simp [E]
  obtain ⟨d, hd, hb⟩ := Metric.isOpen_iff.mp hE.isClosed.isOpen_compl 1 hnot
  refine ⟨min d 1, lt_min hd zero_lt_one, ?_⟩
  intro z hz hr
  by_cases heq : |z.im| = 1
  · exact Or.inl heq
  right
  by_cases him : |z.im| ≤ 3
  · have hS : z ∈ S := by
      refine ⟨?_, hz⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (Complex.norm_le_abs_re_add_abs_im z).trans
        (by rw [abs_of_nonneg hr.1]; linarith [hr.2])
    apply (min_le_left _ _).trans
    by_contra! h
    exact (hb (by simpa [Metric.mem_ball, Real.dist_eq] using h)) ⟨⟨z, hS, rfl⟩, heq⟩
  · exact (min_le_right _ _).trans (by rw [abs_of_nonneg (by linarith : 0 ≤ |z.im|-1)]; linarith)

private theorem eventual_prescribed_gaps (D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ) :
    let u := fun n : ℕ ↦ 1 / ((n:ℝ)+1)
    ∀ᶠ n in atTop, ∀ z : ℂ, D z ≠ 0 → z.re ∈ Icc 0 1 →
      u n / 2 ≤ |z.im - (1+u n)| ∧ u n / 2 ≤ |z.im + (1+u n)| := by
  dsimp only
  obtain ⟨d, hd, hd'⟩ := punctured_divisor_ordinates D
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually_lt_const (by linarith : 0 < d/2)] with n hn
  let v := 1/((n:ℝ)+1)
  have hv : 0 < v := by dsimp [v]; positivity
  have hvd : v < d/2 := hn
  intro z hz hr
  have hsep : v/2 ≤ abs (|z.im| - (1+v)) := by
    obtain h | h := hd' z hz hr
    · rw [h, show (1:ℝ) - (1+v) = -v by ring, abs_neg, abs_of_pos hv]
      linarith
    by_cases hg : 1 ≤ |z.im|
    · rw [abs_of_nonneg (sub_nonneg.mpr hg)] at h
      exact (by linarith : v/2 ≤ |z.im| - (1+v)) |>.trans (le_abs_self _)
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hg))] at h
      exact (by linarith : v/2 ≤ -(|z.im| - (1+v))) |>.trans (neg_le_abs _)
  have hT : 0 ≤ 1+v := by positivity
  change v/2 ≤ |z.im - (1+v)| ∧ v/2 ≤ |z.im + (1+v)|
  exact ⟨hsep.trans (by simpa only [abs_of_nonneg hT] using abs_abs_sub_abs_le_abs_sub z.im (1+v)),
    hsep.trans (by simpa only [abs_neg, abs_of_nonneg hT, sub_neg_eq_add] using abs_abs_sub_abs_le_abs_sub z.im (-(1+v)))⟩

/-- One sequence of compact real even profiles works for every locally finite divisor. For each
divisor, all sufficiently late profiles are positive at both edges, at every ordinate of its
support in the critical strip, simultaneously for every width. Each profile vanishes at zero. -/
theorem exists_universal_admissible_positive_edge_profiles :
    ∃ H : ℕ → ℝ → ℝ → ℝ,
      (∀ n b, ContDiff ℝ ∞ (H n b) ∧ HasCompactSupport (H n b) ∧ H n b 0 = 0 ∧
        ∀ x : ℝ, H n b (-x) = H n b x) ∧
      ∀ D : Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ, ∀ᶠ n in atTop,
        ∀ b : ℝ, ∀ z : ℂ, D z ≠ 0 → z.re ∈ Icc 0 1 →
          0 < (bilateralLaplace (fun x ↦ (H n b x : ℂ))
            ((b : ℂ) + (z.im : ℂ) * Complex.I)).re ∧
          0 < (bilateralLaplace (fun x ↦ (H n b x : ℂ))
            ((-(b : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)).re := by
  obtain ⟨K, hs, hc, -, h0, hp⟩ := RiemannMasullo.exists_compact_pos_cosineTransform
  obtain ⟨G, hGs, hGc, hG0, R, hR, hGr⟩ := cosine_gap_filter K hs hc h0 hp
  let u := fun n : ℕ ↦ 1/((n:ℝ)+1)
  have hu (n : ℕ) : 0 < u n / 2 := by dsimp [u]; positivity
  choose P hPs hPc hP0 hP using fun n : ℕ ↦
    cosine_positive_on_gap G hGs hGc hG0 (T := 1+u n) hR hGr (hu n)
  refine ⟨fun n b ↦ balanced (P n) b, fun n b ↦ balanced_properties _ (hPs n) (hPc n) (hP0 n) b, ?_⟩
  intro D
  filter_upwards [eventual_prescribed_gaps D] with n hn
  intro b z hz hr
  obtain ⟨hm, hp⟩ := hn z hz hr
  have h := hP n z.im hm hp
  obtain ⟨hHs, hHc, -, -⟩ := balanced_properties _ (hPs n) (hPc n) (hP0 n) b
  rw [← Complex.ofReal_neg, laplace_realEdge _ hHs.continuous hHc b z.im,
    laplace_realEdge _ hHs.continuous hHc (-b) z.im,
    realEdge_balanced _ (hPs n).continuous (hPc n), realEdge_balanced_neg _ (hPs n).continuous (hPc n)]
  exact ⟨h,h⟩


section NumberField

open IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "m𝔽" => (continuousIdeleClassNorm F : C →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "M(" φ ", " χ ", " w ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C).val
    (ideleClassNormTwist (F := F) χ w)
local notation "ord(" χ "," z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "Off(" z ")" => ((z).val.re - 1/2)

/-- At each character, all sufficiently late compact Bruhat tests vanish on the norm-one
classes and have strictly positive real Mellin values at every completed zero on either
edge. The threshold for the index works for all the widths simultaneously. -/
theorem exists_eventually_admissible_hecke_edge_probes :
    ∃ probe : ℕ → PontryaginDual C → ℝ → BruhatCompactSupport C,
      (∀ n χ b, ∀ g : C₁, (probe n χ b).val g = 0) ∧
      ∀ χ : PontryaginDual C, ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, b < 1/2 →
        ∀ z : Sites(χ), |Off(z)| = b → 0 < (M(probe n χ b, χ, z.val - 1/2)).re := by
  obtain ⟨H, hs, hp⟩ := exists_universal_admissible_positive_edge_profiles
  choose probe hprobe hM using fun (n : ℕ) (χ : PontryaginDual C) (b : ℝ) ↦
    exists_characterNormTest_laplace χ (fun x ↦ (H n b x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (hs n b).1) ((hs n b).2.1.comp_left Complex.ofReal_zero)
  refine ⟨probe, ?_, ?_⟩
  · intro n χ b g
    rw [hprobe, MonoidHom.mem_ker.mp g.property, Units.val_one, NNReal.coe_one,
      Real.log_one, (hs n b).2.2.1, Complex.ofReal_zero, mul_zero]
  intro χ
  filter_upwards [hp (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ)] with n hn
  intro b hb z hz
  have hb0 : 0 ≤ b := hz ▸ abs_nonneg _
  have hbounds := abs_le.mp hz.le
  have hr : z.val.re ∈ Icc 0 1 := ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩
  have hpos := hn b z.val z.property.ne' hr
  rw [hM, Complex.re_ofReal_mul]
  apply mul_pos
  · exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Complex.ofReal_ne_zero.mp (grh_classVolume_ne_zero (F := F))).symm
  have heq : z.val - 1/2 = ((Off(z) : ℝ) : ℂ) + (z.val.im : ℂ)*Complex.I := by
    apply Complex.ext <;> norm_num [Complex.sub_re, Complex.sub_im]
  rw [heq]
  obtain he | he := abs_eq_abs.mp (hz.trans (abs_of_nonneg hb0).symm)
  · rw [he]; exact hpos.1
  · rw [he, Complex.ofReal_neg]; exact hpos.2

namespace Isolated

local notation "Chars(" τ ")" => {χ : PontryaginDual C // ∀ t : ℝ≥0ˣ, χ ((τ) t) = 1}
local notation "m(" χ "," z ")" => (ord(χ,(z).val)).toNat
local notation "Ext(" τ ", " α ")" => {p : Chars(τ) × ℂ // 0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re - 1/2|}
local notation "widthComparison(" χ ", " b ", " s ", " φ ")" =>
  -(∑' z : Sites(χ), if |Off(z)| < b then (m(χ,z) : ℝ) * (M(φ, χ, z.val - 1/2)).re else 0) ≤
    -(∑' z : Sites(χ), (spectralStripMultiplicity b s Off(z) m(χ,z) : ℝ) * (M(φ, χ, z.val - 1/2)).re)

/-- For Theorem 12.5.1.1, pp. 519–520, a sequence of probes vanishes on the norm-one
classes and detects all occupied edges. For each normalized character and width, it suffices
that the signed width comparison holds for arbitrarily late indices in this sequence. -/
theorem exists_admissible_probe_exteriorZeros_of_frequentWidthComparison (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) {α s : ℝ} (hα : 0 < α) (hs : 1 < s) :
    ∃ probe : ℕ → Chars(τ) → ℝ → BruhatCompactSupport C,
      (∀ n χ b, ∀ g : C₁, (probe n χ b).val g = 0) ∧
      (∀ χ : Chars(τ), ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, b < 1/2 → ∀ z : Sites(χ.val),
        |Off(z)| = b → 0 < (M(probe n χ b, χ.val, z.val - 1/2)).re) ∧
      ((∀ (χ : Chars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
          ∃ᶠ n : ℕ in atTop, widthComparison(χ.val, b, s, probe n χ b)) →
        ∀ φ : BruhatCompactSupport C, HasSum (fun p : Ext(τ, α) ↦
          ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ, p.val.1.val, p.val.2 - 1/2)) 0) := by
  obtain ⟨probe, hvan, hpos⟩ := exists_eventually_admissible_hecke_edge_probes (F := F)
  refine ⟨fun n χ b ↦ probe n χ.val b, fun n χ b ↦ hvan n χ.val b, fun χ ↦ hpos χ.val, ?_⟩
  intro hcomp
  have hchoose (χ : Chars(τ)) (b : ℝ) :
      ∃ n, α ≤ b → b < 1/2 →
        (∀ z : Sites(χ.val), |Off(z)| = b → 0 < (M(probe n χ.val b, χ.val, z.val - 1/2)).re) ∧
          widthComparison(χ.val, b, s, probe n χ.val b) := by
    by_cases h : α ≤ b ∧ b < 1/2
    · obtain ⟨n, hn, hp⟩ := ((hcomp χ b h.1 h.2).and_eventually (hpos χ.val)).exists
      exact ⟨n, fun _ _ ↦ ⟨hp b h.2, hn⟩⟩
    · exact ⟨0, fun ha hb ↦ (h ⟨ha,hb⟩).elim⟩
  choose k hk using hchoose
  exact traceFormula_exteriorZeros_of_signedWidthComparison τ hτ hα hs
    (fun χ b ↦ probe (k χ b) χ.val b) (fun χ b ha hb ↦ (hk χ b ha hb).1)
    (fun χ b ha hb ↦ (hk χ b ha hb).2)

end Isolated

end NumberField

end RiemannMasullo
