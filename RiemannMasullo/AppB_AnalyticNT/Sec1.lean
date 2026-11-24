module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Order.Lattice

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.ForMathlib.Analysis.Complex.Hadamard
import RiemannMasullo.ForMathlib.Analysis.Complex.Liouville
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Bounds
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction

/-!
# Convexity bounds for finite Hecke L-functions

Masullo, §B.1, pp. 588–591. The estimates concern both directions on vertical
lines and are uniform in the real part when stated on a strip.
-/

@[expose] public noncomputable section

open Filter Function NumberField Set
open scoped Asymptotics ComplexConjugate ENNReal NNReal Topology

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

-- TODO(paper-gap): If the introductory critical-line estimate refers to the
-- finite L-function, its exponent 1/4 + ε omits the degree in (B.1.1.12).

/-- Paper: Equation (B.1.1.2), p. 589. The vertical growth order is the infimum
of the nonnegative exponents that bound the function along `Re(s) = σ`.
Deviation: The infimum takes values in `ℝ≥0∞`, with `⊤` when no polynomial bound exists. -/
def verticalGrowthOrder (f : ℂ → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  sInf ((fun k : ℝ≥0 ↦ (k : ℝ≥0∞)) ''
    {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)})

/-- Paper: Equation (B.1.1.2), p. 589. As a check on the definition, the identity
function has growth order one on every vertical line. -/
theorem verticalGrowthOrder_id (σ : ℝ) : verticalGrowthOrder (id : ℂ → ℂ) σ = 1 := by
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) l atTop := tendsto_inf_left tendsto_comap
  unfold verticalGrowthOrder
  apply le_antisymm
  · refine sInf_le ⟨1, ?_, by simp⟩
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ ((1 : ℝ≥0) : ℝ)
    have hRe : ∀ᶠ z in l, z.re = σ :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hz ↦ hz)
    refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [hRe, hHeight.eventually_ge_atTop |σ|] with z hre hσz
    simp only [id_eq, NNReal.coe_one, Real.rpow_one, Real.norm_of_nonneg (abs_nonneg _)]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * |z.im| := by
        rw [hre, two_mul]
        exact add_le_add_left hσz _
  · apply le_sInf
    rintro _ ⟨k, hk, rfl⟩
    by_contra! hlt
    have hklt : (k : ℝ) < 1 := by exact_mod_cast hlt
    have hRay : Tendsto (fun t : ℝ ↦ (⟨σ, t⟩ : ℂ)) atTop l := by
      refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr (by simp)⟩
      exact tendsto_id.congr' <| (eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦
        (abs_of_nonneg ht).symm
    have : NeBot l := hRay.neBot
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ (k : ℝ) at hk
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hk
    have hLarge : ∀ᶠ z in l, C < |z.im| ^ (1 - (k : ℝ)) :=
      ((tendsto_rpow_atTop (sub_pos.mpr hklt)).comp hHeight).eventually_gt_atTop C
    obtain ⟨z, hz, hlarge, hbound⟩ := ((hHeight.eventually_gt_atTop 0).and (hLarge.and hC)).exists
    rw [Real.rpow_sub hz, Real.rpow_one] at hlarge
    rw [id_eq, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _)] at hbound
    exact (not_lt_of_ge ((Complex.abs_im_le_norm z).trans hbound))
      ((lt_div_iff₀ (Real.rpow_pos_of_pos hz _)).mp hlarge)

variable {f : ℂ → ℂ}

/-- Raising the height to a larger real power only enlarges the vertical majorant. -/
lemma isBigO_im_rpow_of_le {p q : ℝ} (hpq : p ≤ q) :
    (fun s : ℂ ↦ |s.im| ^ p) =O[atHeight] fun s : ℂ ↦ |s.im| ^ q := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [tendsto_comap.eventually_ge_atTop (1 : ℝ)] with s hs
  have hp : 0 ≤ |s.im| ^ p := Real.rpow_nonneg (abs_nonneg _) _
  have hq : 0 ≤ |s.im| ^ q := Real.rpow_nonneg (abs_nonneg _) _
  simpa [Real.norm_of_nonneg hp, Real.norm_of_nonneg hq] using
    Real.rpow_le_rpow_of_exponent_le hs hpq

/-- A vertical big-O bound places the growth order at most at that exponent. -/
lemma verticalGrowthOrder_toReal_le_of_isBigO {f : ℂ → ℂ} {σ r : ℝ} (hr : 0 ≤ r)
    (hO : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r) :
    (verticalGrowthOrder f σ).toReal ≤ r := by
  let k : ℝ≥0 := ⟨r, hr⟩
  have hk : k ∈ {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)} :=
    hO
  have hle : verticalGrowthOrder f σ ≤ k := by
    unfold verticalGrowthOrder
    exact sInf_le (mem_image_of_mem _ hk)
  exact ENNReal.toReal_le_coe_of_le_coe hle

/-- A vertical big-O bound keeps the growth order finite. -/
lemma verticalGrowthOrder_ne_top_of_isBigO {f : ℂ → ℂ} {σ r : ℝ} (hr : 0 ≤ r)
    (hO : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r) :
    verticalGrowthOrder f σ ≠ ⊤ := by
  let k : ℝ≥0 := ⟨r, hr⟩
  have hk : k ∈ {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)} :=
    hO
  refine ne_top_of_le_ne_top (b := (k : ℝ≥0∞)) (by simp) ?_
  unfold verticalGrowthOrder
  exact sInf_le (mem_image_of_mem _ hk)

/-- An exponent strictly above the growth order is admissible. -/
lemma isBigO_of_verticalGrowthOrder_toReal_lt {f : ℂ → ℂ} {σ r : ℝ}
    (hne : verticalGrowthOrder f σ ≠ ⊤) (hr : (verticalGrowthOrder f σ).toReal < r) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ r := by
  have hr0 : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hr
  have hlt : verticalGrowthOrder f σ < ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_toReal hne]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 hr
  rw [verticalGrowthOrder] at hlt
  obtain ⟨x, hx, hxlt⟩ := (sInf_lt_iff).1 hlt
  obtain ⟨k, hk, rfl⟩ := hx
  have hklt : (k : ℝ) < r := by
    have hxlt' : (k : ℝ≥0∞) < ENNReal.ofReal r := hxlt
    rw [ENNReal.coe_nnreal_eq] at hxlt'
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).1 hxlt'
  exact hk.trans ((isBigO_im_rpow_of_le hklt.le).mono inf_le_left)

open Complex in
/-- Modulus of the affine-logarithmic weight used to interpolate vertical exponents. -/
lemma norm_affineLogWeight {p q eps : ℝ} {z0 s : ℂ} (hs : 0 < (s - z0).re) :
    ‖exp (((↑p + ↑q * s) * log (s - z0)) + ((↑(-eps * q * Real.pi / 2) * I) * s))‖ =
      ‖s - z0‖ ^ (p + q * s.re) *
        Real.exp (q * s.im * (eps * Real.pi / 2 - (s - z0).arg)) := by
  have hpos : 0 < ‖s - z0‖ := lt_of_lt_of_le hs ((le_abs_self _).trans (abs_re_le_norm _))
  rw [norm_exp]
  set μ : ℂ := ↑(-eps * q * Real.pi / 2) * I
  have hμre : μ.re = 0 := by simp [μ]
  have hμim : μ.im = -eps * q * Real.pi / 2 := by simp [μ]
  have hαre : (↑p + ↑q * s).re = p + q * s.re := by simp
  have hαim : (↑p + ↑q * s).im = q * s.im := by simp
  have hre :
      (((↑p + ↑q * s) * log (s - z0)) + μ * s).re =
        (p + q * s.re) * Real.log ‖s - z0‖ +
          q * s.im * (eps * Real.pi / 2 - (s - z0).arg) := by
    rw [add_re, mul_re, mul_re, log_re, log_im, hμre, hμim, hαre, hαim]
    ring
  rw [hre, Real.exp_add, mul_comm (p + q * s.re), ← Real.rpow_def_of_pos hpos]

/-- On the closed right half of a vertical line, `t · (ε π/2 - arg)` stays between `0` and the
real part. `\u03b5 = 1` is the upper half-plane and `\u03b5 = -1` the lower one. -/
lemma im_mul_halfArg_bounds {z : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : 0 < z.re)
    (hy : 0 ≤ ε * z.im) :
    0 ≤ z.im * (ε * Real.pi / 2 - z.arg) ∧
      z.im * (ε * Real.pi / 2 - z.arg) ≤ z.re := by
  rcases hε with rfl | rfl
  · simp only [one_mul] at hy ⊢
    have him : 0 ≤ z.im := hy
    have harg_lt : z.arg < Real.pi / 2 := Complex.arg_lt_pi_div_two_iff.2 (Or.inl hx)
    refine ⟨mul_nonneg him (sub_nonneg.2 harg_lt.le), ?_⟩
    rcases him.eq_or_lt with him0 | him0
    · have him0' : z.im = 0 := him0.symm
      simp [him0', Complex.arg_eq_zero_iff.2 ⟨hx.le, him0'⟩, hx.le]
    · have harg_pos : 0 < z.arg := by
        refine lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him) ?_
        intro hzero
        exact him0.ne' ((Complex.arg_eq_zero_iff.1 hzero.symm).2)
      have hpos : 0 < Real.pi / 2 - z.arg := sub_pos.2 harg_lt
      have hlt : Real.pi / 2 - z.arg < Real.pi / 2 := sub_lt_self _ harg_pos
      have htan : Real.tan (Real.pi / 2 - z.arg) = z.re / z.im := by
        rw [Real.tan_pi_div_two_sub, Complex.tan_arg, inv_div]
      have hle : Real.pi / 2 - z.arg ≤ z.re / z.im := by
        rw [← htan]
        exact Real.le_tan hpos.le hlt
      have : (Real.pi / 2 - z.arg) * z.im ≤ z.re := (le_div_iff₀ him0).1 hle
      simpa [mul_comm] using this
  · simp only [neg_one_mul] at hy ⊢
    have him : z.im ≤ 0 := by linarith
    rcases him.eq_or_lt with him0 | him0
    · have harg : z.arg = 0 := Complex.arg_eq_zero_iff.2 ⟨hx.le, him0⟩
      simp [him0, harg, hx.le]
    · have harg_gt : -(Real.pi / 2) < z.arg :=
        Complex.neg_pi_div_two_lt_arg_iff.2 (Or.inl hx)
      have harg_neg : z.arg < 0 := Complex.arg_neg_iff.2 him0
      have hφpos : 0 < Real.pi / 2 + z.arg := by linarith
      have hφlt : Real.pi / 2 + z.arg < Real.pi / 2 := by linarith
      have htan : Real.tan (Real.pi / 2 + z.arg) = z.re / -z.im := by
        rw [show Real.pi / 2 + z.arg = Real.pi / 2 - (-z.arg) by ring,
          Real.tan_pi_div_two_sub, Real.tan_neg, Complex.tan_arg]
        field_simp [hx.ne', him0.ne]
      have hle : Real.pi / 2 + z.arg ≤ z.re / -z.im := by
        rw [← htan]
        exact Real.le_tan hφpos.le hφlt
      have himabs : 0 < -z.im := neg_pos.2 him0
      have hmul : (Real.pi / 2 + z.arg) * -z.im ≤ z.re := (le_div_iff₀ himabs).1 hle
      constructor
      · rw [show z.im * (-Real.pi / 2 - z.arg) = -z.im * (Real.pi / 2 + z.arg) by ring]
        exact mul_nonneg himabs.le hφpos.le
      · rw [show z.im * (-Real.pi / 2 - z.arg) = (Real.pi / 2 + z.arg) * -z.im by ring]
        exact hmul

open Complex in
/-- Over a compact set of real parts, a vertical power bound for large heights and continuity
give a global bound by the same power of the distance to a real point on the left. -/
lemma exists_norm_le_mul_norm_sub_rpow {F : ℂ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hc : ContinuousOn F (re ⁻¹' K)) {A : ℝ} (hA : 0 ≤ A)
    (hO : F =O[atHeight ⊓ 𝓟 (re ⁻¹' K)] fun s ↦ |s.im| ^ A) {x0 : ℝ}
    (hx0 : ∀ σ ∈ K, x0 + 1 ≤ σ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ K → ‖F s‖ ≤ C * ‖s - x0‖ ^ A := by
  obtain ⟨c, hc'⟩ := Asymptotics.isBigO_iff.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hc'
  obtain ⟨T, hT⟩ := hc'
  obtain ⟨M, hM⟩ := (hK.reProdIm (isCompact_Icc (a := -T) (b := T))).exists_bound_of_continuousOn
    (hc.mono fun s hs ↦ hs.1)
  refine ⟨max c 0 + max M 0, by positivity, fun s hs ↦ ?_⟩
  have h1 : 1 ≤ ‖s - x0‖ := by
    have := hx0 _ hs
    calc (1:ℝ) ≤ (s - x0).re := by simp; linarith
      _ ≤ |(s - x0).re| := le_abs_self _
      _ ≤ ‖s - x0‖ := abs_re_le_norm _
  have hpow : 1 ≤ ‖s - x0‖ ^ A := Real.one_le_rpow h1 hA
  by_cases hs' : T ≤ |s.im|
  · have hb := hT _ hs' s rfl hs
    have him : |s.im| ≤ ‖s - x0‖ := by
      have := abs_im_le_norm (s - x0); simpa using this
    calc ‖F s‖ ≤ c * ‖|s.im| ^ A‖ := hb
      _ ≤ max c 0 * |s.im| ^ A := by
        rw [Real.norm_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max c 0 * ‖s - x0‖ ^ A := by
        gcongr
      _ ≤ (max c 0 + max M 0) * ‖s - x0‖ ^ A := by
        gcongr; exact le_add_of_nonneg_right (le_max_right _ _)
  · replace hs' := not_le.mp hs'
    have hmem : s ∈ K ×ℂ Icc (-T) T := ⟨hs, abs_le.mp hs'.le⟩
    calc ‖F s‖ ≤ M := hM s hmem
      _ ≤ max c 0 + max M 0 := by linarith [le_max_left M 0, le_max_right c 0]
      _ ≤ (max c 0 + max M 0) * ‖s - x0‖ ^ A := le_mul_of_one_le_right (by positivity) hpow

/-- On the right half-plane, `t · (ε π / 2 - arg)` never exceeds the real part. -/
lemma im_mul_halfArg_le_re {z : ℂ} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hx : 0 < z.re) :
    z.im * (ε * Real.pi / 2 - z.arg) ≤ z.re := by
  by_cases hy : 0 ≤ ε * z.im
  · exact (im_mul_halfArg_bounds hε hx hy).2
  · replace hy := not_le.mp hy
    refine le_trans ?_ hx.le
    rcases hε with rfl | rfl
    · have him : z.im < 0 := by linarith
      have harg : z.arg < 0 := Complex.arg_neg_iff.2 him
      have := mul_nonneg (neg_nonneg.2 him.le) (by linarith [Real.pi_pos] :
        (0:ℝ) ≤ 1 * Real.pi / 2 - z.arg)
      linarith
    · have him : 0 < z.im := by linarith
      have harg : 0 ≤ z.arg := Complex.arg_nonneg_iff.2 him.le
      have := mul_nonneg him.le (by linarith [Real.pi_pos] :
        (0:ℝ) ≤ -(-1 * Real.pi / 2 - z.arg))
      linarith

/-- A positive power is dominated by the exponential of the same multiple. -/
lemma rpow_le_exp_mul {y r : ℝ} (hy : 0 < y) (hr : 0 ≤ r) : y ^ r ≤ Real.exp (r * y) := by
  rw [Real.rpow_def_of_pos hy, mul_comm r y]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (Real.log_le_self hy.le) hr)

open Complex in
/-- Phragmén–Lindelöf interpolation of polynomial vertical bounds when the exponent on the right
edge is at most the one on the left edge. -/
lemma isBigO_rpow_of_verticalStrip_of_le {σ₁ σ₂ : ℝ} (h₁₂ : σ₁ < σ₂) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (re ⁻¹' Icc σ₁ σ₂)) {ξ : ℝ}
    (hpoly : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ ξ)
    {A B : ℝ} (hB0 : 0 ≤ B) (hBA : B ≤ A)
    (hA : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₁})] fun s ↦ |s.im| ^ A)
    (hB : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₂})] fun s ↦ |s.im| ^ B)
    {σ : ℝ} (hσ : σ ∈ Icc σ₁ σ₂) :
    F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ})]
      fun s ↦ |s.im| ^ (((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁)) := by
  have hA0 : 0 ≤ A := hB0.trans hBA
  have hw : 0 < σ₂ - σ₁ := sub_pos.mpr h₁₂
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (B - A) / (σ₂ - σ₁) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = A - q * σ₁ := ⟨_, rfl⟩
  have hq0 : q ≤ 0 := hq ▸ div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  have hℓ : ∀ x : ℝ, p + q * x = ((σ₂ - x) * A + (x - σ₁) * B) / (σ₂ - σ₁) := by
    intro x
    rw [hp, hq]
    field_simp
    ring
  have hℓ₁ : p + q * σ₁ = A := by rw [hℓ]; field_simp; ring
  have hℓ₂ : p + q * σ₂ = B := by rw [hℓ]; field_simp; ring
  have hℓ0 : ∀ x ∈ Icc σ₁ σ₂, 0 ≤ p + q * x := by
    intro x hx
    rw [hℓ]
    apply div_nonneg _ hw.le
    have := mul_nonneg (sub_nonneg.2 hx.2) hA0
    have := mul_nonneg (sub_nonneg.2 hx.1) hB0
    linarith
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, x0 = σ₁ - 1 := ⟨_, rfl⟩
  have hFc : ContinuousOn F (re ⁻¹' Icc σ₁ σ₂) := hF.continuousOn
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_norm_le_mul_norm_sub_rpow (K := {σ₁}) isCompact_singleton
    (hFc.mono (preimage_mono (by simp [h₁₂.le]))) hA0 hA (x0 := x0)
    (by intro y hy; rw [mem_singleton_iff.mp hy]; linarith)
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_norm_le_mul_norm_sub_rpow (K := {σ₂}) isCompact_singleton
    (hFc.mono (preimage_mono (by simp [h₁₂.le]))) hB0 hB (x0 := x0)
    (by intro y hy; rw [mem_singleton_iff.mp hy]; linarith)
  have hpoly' : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ (max ξ 0) :=
    hpoly.trans ((isBigO_im_rpow_of_le (le_max_left ξ 0)).mono inf_le_left)
  obtain ⟨Cξ, hCξ0, hCξ⟩ := exists_norm_le_mul_norm_sub_rpow isCompact_Icc hFc
    (le_max_right ξ 0) hpoly' (x0 := x0) (by intro y hy; linarith [hy.1])
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = σ₂ - x0 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR, hx0]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (-q * R) := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = E * max C₁ C₂ := ⟨_, rfl⟩
  have hE0 : 0 < E := hE ▸ Real.exp_pos _
  set z0 : ℂ := (x0 : ℂ) with hz0
  -- basic facts about `s - z0` on the strip
  have hre : ∀ s : ℂ, (s - z0).re = s.re - x0 := by intro s; simp [z0]
  have him : ∀ s : ℂ, (s - z0).im = s.im := by intro s; simp [z0]
  have hnorm1 : ∀ s : ℂ, σ₁ ≤ s.re → 1 ≤ ‖s - z0‖ := by
    intro s hs
    calc (1:ℝ) ≤ (s - z0).re := by rw [hre, hx0]; linarith
      _ ≤ |(s - z0).re| := le_abs_self _
      _ ≤ ‖s - z0‖ := abs_re_le_norm _
  have hnormle : ∀ s : ℂ, σ₁ ≤ s.re → ‖s - z0‖ ≤ (s.re - x0) + |s.im| := by
    intro s hs
    have := norm_le_abs_re_add_abs_im (s - z0)
    rwa [hre, him, abs_of_nonneg (by rw [hx0]; linarith)] at this
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg hE0.le (hC₁0.trans (le_max_left _ _))
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = Real.pi / (σ₂ - σ₁) / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  have hc_lt : c < Real.pi / (σ₂ - σ₁) := hc_def ▸ half_lt_self (by positivity)
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → 0 ≤ ε * s.im →
      ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * s.re) := by
    intro ε hε
    set W : ℂ → ℂ := fun s ↦ exp (((↑(-p) + ↑(-q) * s) * log (s - z0)) +
      ((↑(-ε * -q * Real.pi / 2) * I) * s)) with hW
    have hWnorm : ∀ s : ℂ, σ₁ ≤ s.re → ‖W s‖ = (‖s - z0‖ ^ (p + q * s.re))⁻¹ *
        Real.exp (-q * (s - z0).im * (ε * Real.pi / 2 - (s - z0).arg)) := by
      intro s hs
      have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith
      rw [hW, norm_affineLogWeight hpos, him, ← Real.rpow_neg (norm_nonneg _)]
      congr 2; ring
    have hWup : ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → ‖W s‖ ≤ (‖s - z0‖ ^ (p + q * s.re))⁻¹ * E := by
      intro s hs
      have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith [hs.1]
      rw [hWnorm s hs.1]
      have hX := im_mul_halfArg_le_re hε hpos
      have hle : -q * (s - z0).im * (ε * Real.pi / 2 - (s - z0).arg) ≤ -q * R := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [hre] at hX
        linarith [hs.2]
      rw [hE]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)
    have hWd : DifferentiableOn ℂ W (re ⁻¹' Icc σ₁ σ₂) := by
      intro s hs
      have hslit : s - z0 ∈ slitPlane :=
        mem_slitPlane_iff.2 (Or.inl (by rw [hre, hx0]; linarith [(show σ₁ ≤ s.re from hs.1)]))
      refine DifferentiableAt.differentiableWithinAt ?_
      exact ((((differentiableAt_const _).add ((differentiableAt_const _).mul
        differentiableAt_id)).mul ((differentiableAt_id.sub_const _).clog hslit)).add
        ((differentiableAt_const _).mul differentiableAt_id)).cexp
    have hGd : DiffContOnCl ℂ (fun s ↦ W s * F s) (re ⁻¹' Ioo σ₁ σ₂) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_preimage_re, closure_Ioo h₁₂.ne]
      exact hWd.mul hF
    have hGgrowth : (fun s ↦ W s * F s) =O[atHeight ⊓ 𝓟 (re ⁻¹' Ioo σ₁ σ₂)]
        fun s ↦ Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)) := by
      refine Asymptotics.IsBigO.of_bound (E * Cξ * Real.exp (max ξ 0 * R)) ?_
      rw [eventually_inf_principal]
      refine Eventually.of_forall fun s hs ↦ ?_
      have hs' : s.re ∈ Icc σ₁ σ₂ := ⟨hs.1.le, hs.2.le⟩
      have hξ' : 0 ≤ max ξ 0 := le_max_right _ _
      have hn1 := hnorm1 s hs'.1
      have hu : 1 ≤ ‖s - z0‖ ^ (p + q * s.re) := Real.one_le_rpow hn1 (hℓ0 _ hs')
      have hW1 : ‖W s‖ ≤ E := (hWup s hs').trans
        (mul_le_of_le_one_left hE0.le (inv_le_one_of_one_le₀ hu))
      have hF1 := hCξ s hs'
      have hpow : ‖s - z0‖ ^ max ξ 0 ≤
          Real.exp (max ξ 0 * R) * Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)) := by
        rw [← Real.exp_add]
        refine (rpow_le_exp_mul (by linarith) hξ').trans (Real.exp_le_exp.mpr ?_)
        have h1 : ‖s - z0‖ ≤ R + |s.im| :=
          (hnormle s hs'.1).trans (by rw [hR]; linarith [hs'.2])
        have h2 : c * |s.im| ≤ Real.exp (c * |s.im|) := by
          linarith [Real.add_one_le_exp (c * |s.im|)]
        have h3 : max ξ 0 * |s.im| ≤ max ξ 0 / c * Real.exp (c * |s.im|) := by
          calc max ξ 0 * |s.im| = max ξ 0 / c * (c * |s.im|) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
        nlinarith [mul_le_mul_of_nonneg_left h1 hξ']
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc ‖W s‖ * ‖F s‖ ≤ E * (Cξ * ‖s - z0‖ ^ max ξ 0) :=
            mul_le_mul hW1 hF1 (norm_nonneg _) (by positivity)
        _ ≤ E * (Cξ * (Real.exp (max ξ 0 * R) *
              Real.exp (max ξ 0 / c * Real.exp (c * |s.im|)))) := by gcongr
        _ = _ := by ring
    have hbound : ∀ s : ℂ, s.re ∈ Icc σ₁ σ₂ → ‖W s * F s‖ ≤ D := by
      intro s hs
      refine PhragmenLindelof.vertical_strip (a := σ₁) (b := σ₂) (f := fun s ↦ W s * F s)
        (C := D) (z := s) hGd ⟨c, hc_lt, max ξ 0 / c, hGgrowth⟩ ?_ ?_ hs.1 hs.2
      · intro z hz
        have hz' : z.re ∈ Icc σ₁ σ₂ := by rw [hz]; exact ⟨le_rfl, h₁₂.le⟩
        have hu : 0 < ‖z - z0‖ ^ A := Real.rpow_pos_of_pos (by linarith [hnorm1 z hz'.1]) _
        have hWz := hWup z hz'
        rw [hz, hℓ₁] at hWz
        rw [norm_mul]
        calc ‖W z‖ * ‖F z‖ ≤ ((‖z - z0‖ ^ A)⁻¹ * E) * (C₁ * ‖z - z0‖ ^ A) :=
              mul_le_mul hWz (hC₁ z hz) (norm_nonneg _) (by positivity)
          _ = E * C₁ := by field_simp
          _ ≤ D := by rw [hD]; gcongr; exact le_max_left _ _
      · intro z hz
        have hz' : z.re ∈ Icc σ₁ σ₂ := by rw [hz]; exact ⟨h₁₂.le, le_rfl⟩
        have hu : 0 < ‖z - z0‖ ^ B := Real.rpow_pos_of_pos (by linarith [hnorm1 z hz'.1]) _
        have hWz := hWup z hz'
        rw [hz, hℓ₂] at hWz
        rw [norm_mul]
        calc ‖W z‖ * ‖F z‖ ≤ ((‖z - z0‖ ^ B)⁻¹ * E) * (C₂ * ‖z - z0‖ ^ B) :=
              mul_le_mul hWz (hC₂ z hz) (norm_nonneg _) (by positivity)
          _ = E * C₂ := by field_simp
          _ ≤ D := by rw [hD]; gcongr; exact le_max_right _ _
    intro s hs hεs
    have hpos : 0 < (s - z0).re := by rw [hre, hx0]; linarith [hs.1]
    have hu : 0 < ‖s - z0‖ ^ (p + q * s.re) :=
      Real.rpow_pos_of_pos (by linarith [hnorm1 s hs.1]) _
    have hlow : (‖s - z0‖ ^ (p + q * s.re))⁻¹ ≤ ‖W s‖ := by
      rw [hWnorm s hs.1]
      refine le_mul_of_one_le_right (by positivity) (Real.one_le_exp ?_)
      rw [mul_assoc]
      exact mul_nonneg (by linarith) (im_mul_halfArg_bounds hε hpos (by rwa [him])).1
    have hb := hbound s hs
    rw [norm_mul] at hb
    have h' : (‖s - z0‖ ^ (p + q * s.re))⁻¹ * ‖F s‖ ≤ D :=
      (mul_le_mul_of_nonneg_right hlow (norm_nonneg _)).trans hb
    rw [inv_mul_le_iff₀ hu] at h'
    linarith
  have hσ0 : 0 ≤ p + q * σ := hℓ0 σ hσ
  rw [← hℓ σ]
  refine Asymptotics.IsBigO.of_bound (D * 2 ^ (p + q * σ)) ?_
  filter_upwards [(tendsto_comap.eventually_ge_atTop R).filter_mono inf_le_left,
    mem_inf_of_right (mem_principal_self _)] with s hsR hs
  have hs' : s.re = σ := hs
  have hsR' : R ≤ |s.im| := hsR
  have hsI : s.re ∈ Icc σ₁ σ₂ := by rw [hs']; exact hσ
  have hFs : ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * s.re) := by
    rcases le_total 0 s.im with h | h
    · exact key 1 (Or.inl rfl) s hsI (by linarith)
    · exact key (-1) (Or.inr rfl) s hsI (by linarith)
  rw [hs'] at hFs
  have h2 : ‖s - z0‖ ≤ 2 * |s.im| := by
    have := hnormle s hsI.1
    rw [hs'] at this
    have : σ - x0 ≤ R := by rw [hR]; linarith [hσ.2]
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖F s‖ ≤ D * ‖s - z0‖ ^ (p + q * σ) := hFs
    _ ≤ D * (2 * |s.im|) ^ (p + q * σ) := by gcongr
    _ = D * 2 ^ (p + q * σ) * |s.im| ^ (p + q * σ) := by
      rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]; ring

open Complex in
/-- Under the reflection `s ↦ c - s`, vertical power bounds over one set of real parts become
bounds over the reflected set. -/
lemma isBigO_comp_const_sub {F : ℂ → ℂ} {c : ℝ} {S T : Set ℝ} (hST : ∀ x ∈ T, c - x ∈ S)
    {r : ℝ} (h : F =O[atHeight ⊓ 𝓟 (re ⁻¹' S)] fun s ↦ |s.im| ^ r) :
    (fun s ↦ F (↑c - s)) =O[atHeight ⊓ 𝓟 (re ⁻¹' T)] fun s ↦ |s.im| ^ r := by
  have ht : Tendsto (fun s : ℂ ↦ (c : ℂ) - s) (atHeight ⊓ 𝓟 (re ⁻¹' T))
      (atHeight ⊓ 𝓟 (re ⁻¹' S)) := by
    refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
    · have : (abs ∘ im) ∘ (fun s : ℂ ↦ (c : ℂ) - s) = abs ∘ im := by
        funext s; simp
      rw [this]
      exact tendsto_comap.mono_left inf_le_left
    · exact mem_inf_of_right (mem_principal.mpr fun s hs ↦ by simpa using hST _ hs)
  have := h.comp_tendsto ht
  simpa [Function.comp_def] using this

open Complex in
/-- Phragmén–Lindelöf interpolation of polynomial vertical bounds on a closed vertical strip:
a function holomorphic near the strip, polynomially bounded on it, and `O(|t|^A)`, `O(|t|^B)` on
the two edges is `O(|t|^e)` on each intermediate line, with `e` the affine interpolation. -/
lemma isBigO_rpow_of_verticalStrip {σ₁ σ₂ : ℝ} (h₁₂ : σ₁ < σ₂) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (re ⁻¹' Icc σ₁ σ₂)) {ξ : ℝ}
    (hpoly : F =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc σ₁ σ₂)] fun s ↦ |s.im| ^ ξ)
    {A B : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₁})] fun s ↦ |s.im| ^ A)
    (hB : F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ₂})] fun s ↦ |s.im| ^ B)
    {σ : ℝ} (hσ : σ ∈ Icc σ₁ σ₂) :
    F =O[atHeight ⊓ 𝓟 (re ⁻¹' {σ})]
      fun s ↦ |s.im| ^ (((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁)) := by
  rcases le_total B A with hBA | hAB
  · exact isBigO_rpow_of_verticalStrip_of_le h₁₂ hF hpoly hB0 hBA hA hB hσ
  · obtain ⟨c, hc⟩ : ∃ c : ℝ, c = σ₁ + σ₂ := ⟨_, rfl⟩
    have hmaps : ∀ x ∈ Icc σ₁ σ₂, c - x ∈ Icc σ₁ σ₂ := fun x hx ↦
      ⟨by rw [hc]; linarith [hx.2], by rw [hc]; linarith [hx.1]⟩
    have hG : DifferentiableOn ℂ (fun s ↦ F (↑c - s)) (re ⁻¹' Icc σ₁ σ₂) := by
      refine hF.comp ((differentiableOn_const _).sub differentiableOn_id) ?_
      intro s hs
      have := hmaps _ hs
      simpa using this
    have h := isBigO_rpow_of_verticalStrip_of_le h₁₂ hG
      (isBigO_comp_const_sub hmaps hpoly) hA0 hAB
      (isBigO_comp_const_sub (S := {σ₂}) (T := {σ₁})
        (by intro x hx; rw [mem_singleton_iff.mp hx, hc]; simp) hB)
      (isBigO_comp_const_sub (S := {σ₁}) (T := {σ₂})
        (by intro x hx; rw [mem_singleton_iff.mp hx, hc]; simp) hA)
      (hmaps σ hσ)
    have h' := isBigO_comp_const_sub (c := c) (S := {c - σ}) (T := {σ})
      (by intro x hx; rw [mem_singleton_iff.mp hx]; simp) h
    have e : ((σ₂ - (c - σ)) * B + (c - σ - σ₁) * A) / (σ₂ - σ₁) =
        ((σ₂ - σ) * A + (σ - σ₁) * B) / (σ₂ - σ₁) := by
      rw [hc]; ring
    rw [e] at h'
    simpa using h'

open Complex in
/-- Clearing finitely many simple poles over a closed strip of real parts inside the half-plane:
multiplying by the polynomial with the poles as roots and passing to normal form gives a function
holomorphic on the strip which, for large heights, equals that product, while the polynomial has
size `|t| ^ N` from above and below. -/
lemma exists_clearPoles_verticalStrip {f : ℂ → ℂ} {a : ℝ}
    (hf : MeromorphicNFOn f (re ⁻¹' Ioi a))
    (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
    (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
    {l u : ℝ} (hl : a < l) :
    ∃ g P : ℂ → ℂ, ∃ N : ℕ, DifferentiableOn ℂ g (re ⁻¹' Icc l u) ∧
      (∀ᶠ s in atHeight ⊓ 𝓟 (re ⁻¹' Icc l u), g s = P s * f s ∧ P s ≠ 0) ∧
      P =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc l u)] (fun s ↦ |s.im| ^ (N : ℝ)) ∧
      (fun s ↦ (P s)⁻¹) =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc l u)]
        (fun s ↦ |s.im| ^ (-(N : ℝ))) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℂ, Z = hFinite.toFinset := ⟨_, rfl⟩
  have hmemZ : ∀ x, x ∈ Z ↔ a < x.re ∧ meromorphicOrderAt f x < 0 := by
    intro x; rw [hZ, Set.Finite.mem_toFinset]; rfl
  obtain ⟨P, hP⟩ : ∃ P : ℂ → ℂ, P = fun s ↦ ∏ ρ ∈ Z, (s - ρ) := ⟨_, rfl⟩
  have hPd : Differentiable ℂ P := by
    rw [hP]; fun_prop
  have hPa : ∀ x, AnalyticAt ℂ P x := fun x ↦ hPd.analyticAt x
  have hggm : MeromorphicOn (P * f) (re ⁻¹' Ioi a) :=
    MeromorphicOn.mul (fun x _ ↦ (hPa x).meromorphicAt) hf.meromorphicOn
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = toMeromorphicNFOn (P * f) (re ⁻¹' Ioi a) := ⟨_, rfl⟩
  have hfa : ∀ x : ℂ, a < x.re → x ∉ Z → AnalyticAt ℂ f x := by
    intro x hx hxZ
    refine (hf hx).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    by_contra h
    exact hxZ ((hmemZ x).mpr ⟨hx, not_le.mp h⟩)
  have hga : ∀ x : ℂ, a < x.re → AnalyticAt ℂ g x := by
    intro x hx
    rw [hg]
    refine (meromorphicNFOn_toMeromorphicNFOn (P * f) _
      (show x ∈ re ⁻¹' Ioi a from hx)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_toMeromorphicNFOn hggm hx,
      meromorphicOrderAt_mul (hPa x).meromorphicAt (hf hx).meromorphicAt]
    by_cases hxZ : x ∈ Z
    · have hxp := (hmemZ x).mp hxZ
      have hfo : meromorphicOrderAt f x = -1 := hSimple x hxp.1 hxp.2
      have hPx : P x = 0 := by rw [hP]; exact Finset.prod_eq_zero hxZ (sub_self x)
      have hne : analyticOrderAt P x ≠ 0 := (hPa x).analyticOrderAt_ne_zero.mpr hPx
      rw [(hPa x).meromorphicOrderAt_eq, hfo]
      cases h : analyticOrderAt P x with
      | top => simp
      | coe n =>
        rw [h] at hne
        have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
        simp only [ENat.map_natCast]
        have : ((n : ℤ) : WithTop ℤ) + -1 = ((n - 1 : ℤ) : WithTop ℤ) := by
          rw [sub_eq_add_neg]; norm_cast
        rw [this]
        exact_mod_cast (by omega : (0 : ℤ) ≤ n - 1)
    · exact add_nonneg (hPa x).meromorphicOrderAt_nonneg (hfa x hx hxZ).meromorphicOrderAt_nonneg
  have hgeq : ∀ x : ℂ, a < x.re → x ∉ Z → g x = P x * f x := by
    intro x hx hxZ
    rw [hg, toMeromorphicNFOn_eq_toMeromorphicNFAt hggm hx,
      toMeromorphicNFAt_eq_self.2 (((hPa x).mul (hfa x hx hxZ)).meromorphicNFAt)]
    rfl
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ ρ ∈ Z, ‖ρ‖ := ⟨_, rfl⟩
  have hρS : ∀ ρ ∈ Z, ‖ρ‖ ≤ S := fun ρ hρ ↦
    hS ▸ Finset.single_le_sum (f := fun i ↦ ‖i‖) (fun i _ ↦ norm_nonneg i) hρ
  have hS0 : 0 ≤ S := hS ▸ Finset.sum_nonneg fun i _ ↦ norm_nonneg i
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = 2 * S + |l| + |u| + 1 := ⟨_, rfl⟩
  have hfactor : ∀ s : ℂ, s.re ∈ Icc l u → T ≤ |s.im| → ∀ ρ ∈ Z,
      |s.im| / 2 ≤ ‖s - ρ‖ ∧ ‖s - ρ‖ ≤ 2 * |s.im| := by
    intro s hs hT' ρ hρ
    have h1 := hρS ρ hρ
    have hre : |s.re| ≤ |l| + |u| := abs_le.mpr
      ⟨by linarith [neg_abs_le l, abs_nonneg u, hs.1],
        by linarith [le_abs_self u, abs_nonneg l, hs.2]⟩
    constructor
    · have h4 := abs_im_le_norm (s - ρ)
      have h2 : |ρ.im| ≤ ‖ρ‖ := abs_im_le_norm ρ
      rw [sub_im] at h4
      have h3 : |s.im| - |ρ.im| ≤ |s.im - ρ.im| := abs_sub_abs_le_abs_sub _ _
      linarith [abs_nonneg l, abs_nonneg u]
    · have h4 := norm_sub_le s ρ
      have h2 := norm_le_abs_re_add_abs_im s
      linarith [abs_nonneg l, abs_nonneg u]
  have hev : ∀ᶠ s in atHeight ⊓ 𝓟 (re ⁻¹' Icc l u), T ≤ |s.im| ∧ s.re ∈ Icc l u :=
    ((tendsto_comap.eventually_ge_atTop T).filter_mono inf_le_left).and
      (mem_inf_of_right (mem_principal_self _))
  have hPnorm : ∀ s : ℂ, s.re ∈ Icc l u → T ≤ |s.im| →
      (|s.im| / 2) ^ Z.card ≤ ‖P s‖ ∧ ‖P s‖ ≤ (2 * |s.im|) ^ Z.card := by
    intro s hs hT'
    rw [hP, norm_prod]
    constructor
    · rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun ρ hρ ↦ (hfactor s hs hT' ρ hρ).1
    · rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun ρ hρ ↦ (hfactor s hs hT' ρ hρ).2
  refine ⟨g, P, Z.card, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hga s (lt_of_lt_of_le hl hs.1)).differentiableAt.differentiableWithinAt
  · filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    have him0 : 0 < |s.im| := by linarith [abs_nonneg l, abs_nonneg u]
    have hsZ : s ∉ Z := by
      intro hsZ
      have h1 := hρS s hsZ
      have h2 := abs_im_le_norm s
      linarith [abs_nonneg l, abs_nonneg u]
    refine ⟨hgeq s (lt_of_lt_of_le hl hs.1) hsZ, ?_⟩
    have h1 := (hPnorm s hs hT').1
    have hpos : 0 < (|s.im| / 2) ^ Z.card := pow_pos (half_pos him0) _
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  · refine Asymptotics.IsBigO.of_bound (2 ^ Z.card) ?_
    filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_natCast, ← mul_pow]
    exact (hPnorm s hs hT').2
  · refine Asymptotics.IsBigO.of_bound (2 ^ Z.card) ?_
    filter_upwards [hev] with s hs'
    obtain ⟨hT', hs⟩ := hs'
    have him0 : 0 < |s.im| := by linarith [abs_nonneg l, abs_nonneg u]
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg him0.le, Real.rpow_natCast, norm_inv]
    have h1 := (hPnorm s hs hT').1
    have hpos : 0 < (|s.im| / 2) ^ Z.card := pow_pos (half_pos him0) _
    calc ‖P s‖⁻¹ ≤ ((|s.im| / 2) ^ Z.card)⁻¹ := inv_anti₀ hpos h1
      _ = 2 ^ Z.card * (|s.im| ^ Z.card)⁻¹ := by rw [div_pow]; field_simp

section GrowthOrder

variable {f : ℂ → ℂ} {a : ℝ}
variable (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
  (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
  (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
  (hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] fun s ↦ |s.im| ^ ξ)

include hf hFinite hSimple hGrowth

-- Retain the meromorphicity and pole hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma B.1.1.1, p. 589. In the open half-plane the vertical growth
order is finite under the uniform polynomial bound.
Deviation: This and the other parts use meromorphic functions in normal form
and omit the unused parameter `b > a`. -/
theorem verticalGrowthOrder_ne_top {σ : ℝ} (hσ : a < σ) :
    verticalGrowthOrder f σ ≠ ⊤ := by
  obtain ⟨ξ, hξ, hBound⟩ := hGrowth
  let k : ℝ≥0 := ⟨ξ, hξ.le⟩
  have hLine : ({σ} : Set ℝ) ⊆ Ioi a := singleton_subset_iff.mpr hσ
  refine lt_top_iff_ne_top.mp (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top (r := k)))
  unfold verticalGrowthOrder
  refine sInf_le ⟨k, ?_, rfl⟩
  exact hBound.mono (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hLine)))

-- TODO(paper-gap): The proof's equality `μ_g = μ + N` fails for `f(s) = 1/s`
-- on `Re(s) > -1`. Clearing its one pole gives `g(s) = 1`, and both orders are zero.

omit hf hFinite hSimple hGrowth in
/-- Simple poles can be removed by factors tending to one at large absolute height.
The resulting holomorphic function has the same asymptotic size on the half-plane. -/
private theorem exists_analyticOnNhd_isTheta_atHeight {f : ℂ → ℂ} {a : ℝ}
    (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
    (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
    (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Complex.re ⁻¹' Ioi a) ∧
      g =Θ[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] f := by
  classical
  let poles := hFinite.toFinset
  let factor (p z : ℂ) := (z - p) / (z - (a : ℂ))
  let multiplier : ℂ → ℂ := ∏ p ∈ poles, factor p
  let product : ℂ → ℂ := multiplier * f
  let U := Complex.re ⁻¹' Ioi a
  have hDen (z : ℂ) (hz : z ∈ U) : z - (a : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hz' : a < z.re := hz
    simp [h] at hz'
  have hFactor (p : ℂ) {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ (factor p) z :=
    (show AnalyticAt ℂ (fun w : ℂ ↦ w - p) z by fun_prop).div (by fun_prop) (hDen z hz)
  have hMultiplier : AnalyticOnNhd ℂ multiplier U := fun z hz ↦
    Finset.analyticAt_prod _ (fun p _ ↦ hFactor p hz)
  have hProduct : MeromorphicOn product U := fun z hz ↦
    (hMultiplier z hz).meromorphicAt.mul (hf hz).meromorphicAt
  have hOrder (z : ℂ) (hz : z ∈ U) : 0 ≤ meromorphicOrderAt product z := by
    rw [meromorphicOrderAt_mul (hMultiplier z hz).meromorphicAt (hf hz).meromorphicAt]
    by_cases hp : meromorphicOrderAt f z < 0
    · have hmem : z ∈ poles := hFinite.mem_toFinset.mpr ⟨hz, hp⟩
      have hsum : 1 ≤ meromorphicOrderAt multiplier z := by
        change 1 ≤ meromorphicOrderAt (∏ p ∈ poles, factor p) z
        rw [meromorphicOrderAt_prod (fun p _ ↦ (hFactor p hz).meromorphicAt)]
        have hself : meromorphicOrderAt (factor z) z = 1 := by
          have hinv : AnalyticAt ℂ (fun w : ℂ ↦ (w - (a : ℂ))⁻¹) z :=
            (show AnalyticAt ℂ (fun w : ℂ ↦ w - (a : ℂ)) z by fun_prop).inv (hDen z hz)
          have h := meromorphicOrderAt_mul_of_ne_zero (f := fun w ↦ w - z)
            hinv (inv_ne_zero (hDen z hz))
          simpa only [Pi.mul_def, ← div_eq_inv_mul, factor, meromorphicOrderAt_id_sub_const] using h
        rw [← hself]
        exact Finset.single_le_sum (fun p _ ↦ (hFactor p hz).meromorphicOrderAt_nonneg) hmem
      rw [hSimple z hz hp]
      exact (by decide : (0 : WithTop ℤ) ≤ 1 + (-1)).trans (add_le_add_left hsum _)
    · exact add_nonneg (hMultiplier z hz).meromorphicOrderAt_nonneg (le_of_not_gt hp)
  let g := toMeromorphicNFOn product U
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    exact ((meromorphicNFOn_toMeromorphicNFOn product U) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by simpa only [g, meromorphicOrderAt_toMeromorphicNFOn hProduct hz] using hOrder z hz)
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  have hNorm : Tendsto (fun z : ℂ ↦ ‖z - (a : ℂ)‖) atHeight atTop :=
    tendsto_atTop_mono (fun z ↦ by simpa using Complex.abs_im_le_norm (z - (a : ℂ))) hHeight
  have hFactorLimit (p : ℂ) : Tendsto (factor p) atHeight (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hLimit : Tendsto (fun z : ℂ ↦ ‖(a : ℂ) - p‖ * ‖z - (a : ℂ)‖⁻¹)
        atHeight (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hNorm).const_mul ‖(a : ℂ) - p‖
    refine hLimit.congr' ?_
    filter_upwards [hNorm.eventually_gt_atTop 0] with z hz
    have hd := norm_pos_iff.mp hz
    have hEq : factor p z - 1 = ((a : ℂ) - p) / (z - (a : ℂ)) := by
      dsimp [factor]
      field_simp
      ring
    rw [hEq, norm_div, div_eq_mul_inv]
  have hLimit : Tendsto multiplier atHeight (𝓝 1) := by
    have h := tendsto_finsetProd poles (a := fun _ ↦ (1 : ℂ)) (fun p _ ↦ hFactorLimit p)
    rw [Finset.prod_const_one] at h
    exact h.congr (fun z ↦ (Finset.prod_apply z poles factor).symm)
  let heightInU := atHeight ⊓ 𝓟 U
  have hEq : g =ᶠ[heightInU] product := by
    have hAvoid : ∀ᶠ z in atHeight, z ∉ poles := by
      have hAvoidEach : ∀ᶠ z in atHeight, ∀ p ∈ poles, z ≠ p := by
        apply (Filter.eventually_all_finset poles).2
        intro p _
        filter_upwards [hHeight.eventually_gt_atTop |p.im|] with z hz
        rintro rfl
        exact (lt_irrefl _ hz)
      exact hAvoidEach.mono fun z hz hp ↦ hz z hp rfl
    change ∀ᶠ z in atHeight ⊓ 𝓟 U, g z = product z
    rw [eventually_inf_principal]
    filter_upwards [hAvoid] with z hz hzU
    have hzNonneg : 0 ≤ meromorphicOrderAt f z :=
      le_of_not_gt (fun hp ↦ hz (hFinite.mem_toFinset.mpr ⟨hzU, hp⟩))
    have hprod : AnalyticAt ℂ product z :=
      (hMultiplier z hzU).mul ((hf hzU).meromorphicOrderAt_nonneg_iff_analyticAt.mp hzNonneg)
    dsimp only [g]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hProduct hzU,
      toMeromorphicNFAt_eq_self.mpr hprod.meromorphicNFAt]
  have hT : multiplier =Θ[atHeight] (fun _ ↦ (1 : ℂ)) := by
    refine ⟨Asymptotics.isBigO_const_of_tendsto hLimit one_ne_zero, ?_⟩
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have hclose := (tendsto_iff_norm_sub_tendsto_zero.mp hLimit).eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hclose] with z hz
    have H := norm_sub_norm_le (1 : ℂ) (multiplier z)
    rw [norm_sub_rev, norm_one] at H
    rw [norm_one]
    linarith
  refine ⟨g, hg, hEq.isTheta.trans ?_⟩
  have hh := (hT.mono (show heightInU ≤ atHeight from inf_le_left)).mul
    (Asymptotics.isTheta_refl f heightInU)
  exact hh.trans_eventuallyEq (Eventually.of_forall fun z ↦ one_mul (f z))

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is convex as a function
of the real part in the open half-plane. -/
theorem convexOn_verticalGrowthOrder :
    ConvexOn ℝ (Ioi a) (fun σ ↦ (verticalGrowthOrder f σ).toReal) := by
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_isTheta_atHeight hf hFinite hSimple
  obtain ⟨K, hK, hGrowth⟩ := hGrowth
  have line_le_halfPlane {x : ℝ} (hx : a < x) :
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x}) ≤ atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a) :=
    inf_le_inf_left _ (Filter.principal_mono.mpr (preimage_mono (singleton_subset_iff.mpr hx)))
  have approx {x ε : ℝ} (hx : a < x) (hε : 0 < ε) :
      ∃ k : ℝ≥0, (k : ℝ) < (verticalGrowthOrder f x).toReal + ε ∧
        f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
    let k : ℝ≥0 := ⟨K, hK.le⟩
    have hKBound : verticalGrowthOrder f x ≤ (k : ℝ≥0∞) :=
      sInf_le ⟨k, hGrowth.mono (line_le_halfPlane hx), rfl⟩
    have htop : verticalGrowthOrder f x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hKBound
    have hlt : verticalGrowthOrder f x < ENNReal.ofReal ((verticalGrowthOrder f x).toReal + ε) :=
      (ENNReal.lt_ofReal_iff_toReal_lt htop).mpr (lt_add_of_pos_right _ hε)
    unfold verticalGrowthOrder at hlt
    obtain ⟨_, ⟨k, hk, rfl⟩, hlt⟩ := sInf_lt_iff.mp hlt
    exact ⟨k, ENNReal.coe_lt_ofReal.mp hlt, hk⟩
  refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro x hx y hy hne p q hp hq hpq
  change (verticalGrowthOrder f (p * x + q * y)).toReal ≤
    p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal
  wlog hxy : x < y generalizing x y p q
  · simpa only [add_comm] using this hy hx hne.symm hq hp (by rwa [add_comm])
      (lt_of_le_of_ne (le_of_not_gt hxy) hne.symm)
  have strip_sub : Complex.re ⁻¹' Icc x y ⊆ Complex.re ⁻¹' Ioi a :=
    fun _ hz ↦ hx.trans_le hz.1
  have hStrip := inf_le_inf_left atHeight (Filter.principal_mono.mpr strip_sub)
  have hInt : a < p * x + q * y := by
    have hx' : a < x := hx
    have hprod : 0 < q * (y - x) := mul_pos hq (sub_pos.mpr hxy)
    nlinarith [congrArg (fun t : ℝ ↦ t * x) hpq]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k₀, hk₀, h₀⟩ := approx hx hε
  obtain ⟨k₁, hk₁, h₁⟩ := approx hy hε
  have hInterp := isBigO_rpow_verticalStrip_interpolate hxy hK.le k₀.coe_nonneg k₁.coe_nonneg
    hp.le hq.le hpq (hg.differentiableOn.mono strip_sub)
    ((hgf.mono hStrip).trans_isBigO (hGrowth.mono hStrip))
    ((hgf.mono (line_le_halfPlane hx)).trans_isBigO h₀)
    ((hgf.mono (line_le_halfPlane hy)).trans_isBigO h₁)
  have hBound := (hgf.symm.mono (line_le_halfPlane hInt)).trans_isBigO hInterp
  let k : ℝ≥0 := ⟨p * (k₀ : ℝ) + q * (k₁ : ℝ), by positivity⟩
  have hOrder : verticalGrowthOrder f (p * x + q * y) ≤ (k : ℝ≥0∞) :=
    sInf_le ⟨k, hBound, rfl⟩
  calc
    _ ≤ (k : ℝ) := ENNReal.toReal_mono ENNReal.coe_ne_top hOrder
    _ ≤ p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal + ε := by
      change p * (k₀ : ℝ) + q * (k₁ : ℝ) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hk₀.le hp.le, mul_le_mul_of_nonneg_left hk₁.le hq.le,
        congrArg (fun t : ℝ ↦ t * ε) hpq]

/-- The convexity inequality behind Lemma B.1.1.1: for `a < σ₁ < σ < σ₂`, the growth order at
`σ` is at most the affine interpolation of the orders at `σ₁` and `σ₂`. -/
theorem verticalGrowthOrder_toReal_le_interp {σ₁ σ σ₂ : ℝ} (h₁ : a < σ₁) (h₁σ : σ₁ < σ)
    (hσ₂ : σ < σ₂) :
    (verticalGrowthOrder f σ).toReal ≤
      ((σ₂ - σ) * (verticalGrowthOrder f σ₁).toReal +
        (σ - σ₁) * (verticalGrowthOrder f σ₂).toReal) / (σ₂ - σ₁) := by
  obtain ⟨ξ, hξ, hO⟩ := hGrowth
  have h₁₂ : σ₁ < σ₂ := h₁σ.trans hσ₂
  have hw : 0 < σ₂ - σ₁ := sub_pos.2 h₁₂
  have hsub : ∀ K : Set ℝ, K ⊆ Icc σ₁ σ₂ →
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' K) ≤ atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂) :=
    fun K hK ↦ inf_le_inf_left _ (principal_mono.2 (preimage_mono hK))
  have hIcc : atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂) ≤
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a) :=
    inf_le_inf_left _ (principal_mono.2 (preimage_mono fun x hx ↦ lt_of_lt_of_le h₁ hx.1))
  have hne : ∀ x ∈ Icc σ₁ σ₂, verticalGrowthOrder f x ≠ ⊤ := fun x hx ↦
    verticalGrowthOrder_ne_top_of_isBigO hξ.le
      ((hO.mono hIcc).mono (hsub {x} (singleton_subset_iff.2 hx)))
  obtain ⟨g, P, N, hgd, hgeq, hPO, hPinv⟩ :=
    exists_clearPoles_verticalStrip hf hFinite hSimple (u := σ₂) h₁
  have htrans : ∀ K : Set ℝ, K ⊆ Icc σ₁ σ₂ → ∀ r : ℝ, 0 ≤ r →
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' K)] (fun s ↦ |s.im| ^ r) →
      g =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' K)] (fun s ↦ |s.im| ^ ((N : ℝ) + r)) := by
    intro K hK r hr hfK
    have e : (fun s : ℂ ↦ |s.im| ^ ((N : ℝ) + r)) = fun s ↦ |s.im| ^ (N : ℝ) * |s.im| ^ r :=
      funext fun s ↦ Real.rpow_add_of_nonneg (abs_nonneg _) (Nat.cast_nonneg _) hr
    rw [e]
    refine Asymptotics.IsBigO.congr' ((hPO.mono (hsub K hK)).mul hfK) ?_ EventuallyEq.rfl
    filter_upwards [hgeq.filter_mono (hsub K hK)] with s hs
    exact hs.1.symm
  have hφ₁ : 0 ≤ (verticalGrowthOrder f σ₁).toReal := ENNReal.toReal_nonneg
  have hφ₂ : 0 ≤ (verticalGrowthOrder f σ₂).toReal := ENNReal.toReal_nonneg
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  have hA := isBigO_of_verticalGrowthOrder_toReal_lt (hne σ₁ ⟨le_rfl, h₁₂.le⟩)
    (lt_add_of_pos_right (verticalGrowthOrder f σ₁).toReal hδ)
  have hB := isBigO_of_verticalGrowthOrder_toReal_lt (hne σ₂ ⟨h₁₂.le, le_rfl⟩)
    (lt_add_of_pos_right (verticalGrowthOrder f σ₂).toReal hδ)
  have hgA := htrans {σ₁} (singleton_subset_iff.2 ⟨le_rfl, h₁₂.le⟩) _ (by positivity) hA
  have hgB := htrans {σ₂} (singleton_subset_iff.2 ⟨h₁₂.le, le_rfl⟩) _ (by positivity) hB
  have hgpoly := htrans (Icc σ₁ σ₂) subset_rfl ξ hξ.le (hO.mono hIcc)
  have hgσ := isBigO_rpow_of_verticalStrip h₁₂ hgd hgpoly (by positivity) (by positivity) hgA hgB
    (σ := σ) ⟨h₁σ.le, hσ₂.le⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ((σ₂ - σ) * (verticalGrowthOrder f σ₁).toReal +
      (σ - σ₁) * (verticalGrowthOrder f σ₂).toReal) / (σ₂ - σ₁) + δ := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    rw [he]
    have := mul_nonneg (sub_pos.2 hσ₂).le hφ₁
    have := mul_nonneg (sub_pos.2 h₁σ).le hφ₂
    positivity
  have hexp : ((σ₂ - σ) * ((N : ℝ) + ((verticalGrowthOrder f σ₁).toReal + δ)) +
      (σ - σ₁) * ((N : ℝ) + ((verticalGrowthOrder f σ₂).toReal + δ))) / (σ₂ - σ₁) =
      (N : ℝ) + e := by
    rw [he]; field_simp; ring
  rw [hexp] at hgσ
  have hlσ := hsub {σ} (singleton_subset_iff.2 ⟨h₁σ.le, hσ₂.le⟩)
  have hfσ : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ e := by
    refine Asymptotics.IsBigO.congr' (hgσ.mul (hPinv.mono hlσ)) ?_ ?_
    · filter_upwards [hgeq.filter_mono hlσ] with s hs
      rw [hs.1]
      field_simp [hs.2]
    · filter_upwards [(tendsto_comap.eventually_gt_atTop (0:ℝ)).filter_mono inf_le_left] with s hs
      have hs' : 0 < |s.im| := hs
      rw [← Real.rpow_add hs']
      congr 1
      ring
  rw [← he]
  exact verticalGrowthOrder_toReal_le_of_isBigO he0 hfσ

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is continuous in the
open half-plane. -/
theorem continuousOn_verticalGrowthOrder :
    ContinuousOn (fun σ ↦ (verticalGrowthOrder f σ).toReal) (Ioi a) := by
  refine ConvexOn.continuousOn isOpen_Ioi (convexOn_of_slope_mono_adjacent (convex_Ioi a) ?_)
  intro x y z hx hz hxy hyz
  have h := verticalGrowthOrder_toReal_le_interp hf hFinite hSimple hGrowth hx hxy hyz
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  rw [le_div_iff₀ (by linarith)] at h
  linarith

omit hf hFinite hSimple hGrowth

/-- A height bound on a set of real parts is equivalent to a single estimate
past a common height threshold. -/
private theorem isBigO_height_iff {f : ℂ → ℂ} {S : Set ℝ} {p : ℝ → ℝ} :
    (f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)] fun z ↦ |z.im| ^ p z.re) ↔
      ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ S → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ p z.re := by
  simp only [Asymptotics.isBigO_iff', eventually_inf_principal, eventually_comap, eventually_atTop,
    Function.comp_apply, mem_preimage, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  constructor
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun z hz h ↦ hT _ h z rfl hz⟩
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun t ht z hz h ↦ hT z h (hz ▸ ht)⟩

/-- A nonnegative affine exponent interpolates the two vertical boundary
bounds on a strip where the function is polynomially bounded and eventually
holomorphic at large absolute height. -/
private theorem isBigO_height_affine {f : ℂ → ℂ} {u v ξ p q : ℝ} (huv : u < v)
    (hξ : 0 ≤ ξ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hAnalytic : ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc u v → T ≤ |z.im| →
      AnalyticAt ℂ f z)
    (hGrowth : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)] fun z ↦ |z.im| ^ ξ)
    (hLeft : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ p)
    (hRight : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {v})] fun z ↦ |z.im| ^ q) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
      fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * p + (z.re - u) / (v - u) * q) := by
  obtain ⟨T, hT⟩ := hAnalytic
  obtain ⟨C₀, hC₀, T₀, hT₀⟩ := (isBigO_height_iff (p := fun _ ↦ ξ)).mp hGrowth
  obtain ⟨C₁, hC₁, T₁, hT₁⟩ := (isBigO_height_iff (p := fun _ ↦ p)).mp hLeft
  obtain ⟨C₂, hC₂, T₂, hT₂⟩ := (isBigO_height_iff (p := fun _ ↦ q)).mp hRight
  let K := max (C₀ * (3 / 2 : ℝ) ^ ξ) (max (C₁ * (3 / 2 : ℝ) ^ p) (C₂ * (3 / 2 : ℝ) ^ q))
  have hK : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let A : ℂ → ℂ := fun w ↦ (1 - (w - u) / (v - u)) * p + (w - u) / (v - u) * q
  let E : ℝ → ℝ := fun x ↦ (1 - (x - u) / (v - u)) * p + (x - u) / (v - u) * q
  have hA (w : ℂ) : (A w).re = E w.re := by
    simp [A, E, ← Complex.ofReal_sub, Complex.div_ofReal_re, Complex.mul_re]
  have hAu : E u = p := by simp [E]
  have hAv : E v = q := by simp [E, sub_ne_zero.mpr huv.ne']
  have hE {x : ℝ} (hx : x ∈ Icc u v) : 0 ≤ E x := by
    have hθ₀ := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr huv.le)
    have hθ₁ : (x - u) / (v - u) ≤ 1 := by
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hx.2 _
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ₁) hp) (mul_nonneg hθ₀ hq)
  refine (isBigO_height_iff (p := E)).mpr ⟨K * Real.exp ((v - u) ^ 2), by positivity,
    max 1 (max (4 * ξ) (2 * max (max T T₀) (max T₁ T₂))), ?_⟩
  intro z hz hHeight
  let R := |z.im|
  have hR₁ : 1 ≤ R := (le_max_left _ _).trans hHeight
  have hR : 0 < R := zero_lt_one.trans_le hR₁
  have hRξ : 4 * ξ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hHeight)
  have hRT : max (max T T₀) (max T₁ T₂) ≤ R / 2 := by
    have := (le_max_right _ _).trans ((le_max_right _ _).trans hHeight)
    linarith
  -- The rectangle stays at absolute heights between R / 2 and 3 * R / 2.
  let L := z.im - R / 2
  let U := z.im + R / 2
  have hLU : L < U := by dsimp [L, U]; linarith
  have hHeights {w : ℂ} (hw : w.im ∈ Icc L U) :
      R / 2 ≤ |w.im| ∧ |w.im| ≤ (3 / 2 : ℝ) * R := by
    have hlo : z.im - R / 2 ≤ w.im := hw.1
    have hhi : w.im ≤ z.im + R / 2 := hw.2
    have hclose : |w.im - z.im| ≤ R / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    constructor <;> linarith [abs_sub_abs_le_abs_sub z.im w.im,
      abs_sub_abs_le_abs_sub w.im z.im, abs_sub_comm z.im w.im]
  -- The square in the exponential suppresses the polynomial bound on the horizontal edges.
  let g : ℂ → ℂ := fun w ↦ f w * Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))
  have hgNorm (w : ℂ) :
      ‖g w‖ = (‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) / R ^ E w.re) *
        Real.exp ((w.re - z.re) ^ 2) := by
    simp only [g, norm_mul, Complex.norm_exp, Complex.sub_re, pow_two, Complex.mul_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hA,
      Real.rpow_def_of_pos hR, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hg : DiffContOnCl ℂ g (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    intro w hw
    have hw' := Complex.mem_reProdIm.mp hw
    have hfw := hT w hw'.1 ((le_max_left _ _).trans ((le_max_left _ _).trans
      (hRT.trans (hHeights hw'.2).1)))
    have hA' : Differentiable ℂ A := by unfold A; fun_prop
    have hWeight : Differentiable ℂ
        (fun w ↦ Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))) := by
      fun_prop
    exact (hfw.differentiableAt.mul hWeight.differentiableAt).differentiableWithinAt
  have hPower (w : ℂ) (hw : w.im ∈ Icc L U) {k : ℝ} (hk : 0 ≤ k) :
      |w.im| ^ k ≤ (3 / 2 : ℝ) ^ k * R ^ k := by
    rw [← Real.mul_rpow (by norm_num) hR.le]
    exact Real.rpow_le_rpow (abs_nonneg _) (hHeights hw).2 hk
  have hDamp : R ^ ξ * Real.exp (-(R / 2) ^ 2) ≤ 1 := by
    rw [Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
    have hlog : Real.log R ≤ R := (Real.log_le_sub_one_of_pos hR).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hlog hξ, mul_nonneg (sub_nonneg.mpr hRξ) hR.le]
  have hFront : ∀ w ∈ frontier (Complex.reProdIm (Ioo u v) (Ioo L U)),
      ‖g w‖ ≤ K * Real.exp ((v - u) ^ 2) := by
    intro w hw
    have hw' := frontier_subset_closure hw
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne] at hw'
    obtain ⟨hwRe, hwIm⟩ := Complex.mem_reProdIm.mp hw'
    rw [Complex.frontier_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne, frontier_Ioo huv,
      frontier_Ioo hLU] at hw
    rw [hgNorm]
    refine mul_le_mul ?_ ?_ (by positivity) hK.le
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos hR _)).mpr
      rcases hw with hw | hw
      · have hs : w.im = L ∨ w.im = U := hw.2
        have hsq : (w.im - z.im) ^ 2 = (R / 2) ^ 2 := by
          rcases hs with h | h <;> rw [h] <;> dsimp [L, U] <;> ring
        have hBound := hT₀ w hwRe ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hRT.trans (hHeights hwIm).1)))
        rw [hsq]
        calc
          _ ≤ (C₀ * ((3 / 2 : ℝ) ^ ξ * R ^ ξ)) * Real.exp (-(R / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right (hBound.trans
              (mul_le_mul_of_nonneg_left (hPower w hwIm hξ) hC₀.le)) (by positivity)
          _ = (C₀ * (3 / 2 : ℝ) ^ ξ) * (R ^ ξ * Real.exp (-(R / 2) ^ 2)) := by ring
          _ ≤ K := by
            simpa only [mul_one] using mul_le_mul (le_max_left _ _) hDamp (by positivity) hK.le
          _ ≤ K * R ^ E w.re := le_mul_of_one_le_right hK.le
            (Real.one_le_rpow hR₁ (hE hwRe))
      · have hs : w.re = u ∨ w.re = v := hw.1
        have hExp : Real.exp (-(w.im - z.im) ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
        have hSide {C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hEk : E w.re = k)
            (hB : ‖f w‖ ≤ C * |w.im| ^ k) (hCK : C * (3 / 2 : ℝ) ^ k ≤ K) :
            ‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) ≤ K * R ^ E w.re := by
          rw [hEk]
          calc
            _ ≤ ‖f w‖ := mul_le_of_le_one_right (norm_nonneg _) hExp
            _ ≤ C * |w.im| ^ k := hB
            _ ≤ C * ((3 / 2 : ℝ) ^ k * R ^ k) :=
              mul_le_mul_of_nonneg_left (hPower w hwIm hk) hC
            _ = (C * (3 / 2 : ℝ) ^ k) * R ^ k := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hCK (by positivity)
        rcases hs with h | h
        · exact hSide hC₁.le hp (h ▸ hAu)
            (hT₁ w h ((le_max_left _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_left _ _).trans (le_max_right _ _))
        · exact hSide hC₂.le hq (h ▸ hAv)
            (hT₂ w h ((le_max_right _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_right _ _).trans (le_max_right _ _))
    · apply Real.exp_le_exp.mpr
      have hwidth : |w.re - z.re| ≤ v - u :=
        abs_le.mpr ⟨by linarith [hwRe.1, hz.2], by linarith [hwRe.2, hz.1]⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hwidth 2
  have hz' : z ∈ closure (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    exact ⟨hz, ⟨by dsimp [L]; linarith, by dsimp [U]; linarith⟩⟩
  have hMax := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)) hg hFront hz'
  rw [hgNorm, sub_self, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero,
    Real.exp_zero, mul_one, mul_one, div_le_iff₀ (Real.rpow_pos_of_pos hR _)] at hMax
  exact hMax

include hf hFinite hSimple hGrowth

/-- Paper: Lemma B.1.1.1, p. 589. On each closed strip inside the half-plane,
the growth order at the real part plus any positive ε gives a uniform exponent. -/
theorem isBigO_verticalGrowthOrder_add (σ₁ σ₂ : ℝ) (h₁ : a < σ₁) (h₂ : σ₁ < σ₂)
    (ε : ℝ) (hε : 0 < ε) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂)]
      fun s ↦ |s.im| ^ ((verticalGrowthOrder f s.re).toReal + ε) := by
  classical
  let μ : ℝ → ℝ := fun x ↦ (verticalGrowthOrder f x).toReal
  have hμ₀ (x : ℝ) : 0 ≤ μ x := ENNReal.toReal_nonneg
  have hμFinite {x : ℝ} (hx : a < x) : verticalGrowthOrder f x ≠ ⊤ :=
    verticalGrowthOrder_ne_top hf hFinite hSimple hGrowth hx
  have hAnalytic : ∃ T : ℝ, ∀ z : ℂ, a < z.re → T ≤ |z.im| → AnalyticAt ℂ f z := by
    obtain ⟨T, hT⟩ := (hFinite.image (fun z ↦ |z.im|)).bddAbove
    refine ⟨T + 1, fun z hz hHeight ↦
      (hf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_⟩
    by_contra! hPole
    have := hT ⟨z, ⟨hz, hPole⟩, rfl⟩
    linarith
  obtain ⟨ξ, hξ, hξBound⟩ := hGrowth
  have hLine {x k : ℝ} (hx : a < x) (hk : μ x < k) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ k := by
    let k' : ℝ≥0 := ⟨k, (lt_of_le_of_lt (hμ₀ x) hk).le⟩
    have hk' : verticalGrowthOrder f x < (k' : ℝ≥0∞) :=
      (ENNReal.toReal_lt_toReal (hμFinite hx) ENNReal.coe_ne_top).mp hk
    rw [verticalGrowthOrder, sInf_lt_iff] at hk'
    obtain ⟨_, ⟨j, hj, rfl⟩, hjk⟩ := hk'
    have hjk' : (j : ℝ) ≤ k := by
      change (j : ℝ) ≤ (k' : ℝ)
      exact NNReal.coe_le_coe.mpr (by simpa only [ENNReal.coe_le_coe] using hjk.le)
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun _ ↦ (j : ℝ))).mp hj
    refine (isBigO_height_iff (p := fun _ ↦ k)).mpr
      ⟨C, hC, max T 1, fun z hz hHeight ↦ (hT z hz ((le_max_left _ _).trans hHeight)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hjk') hC.le
  have hInterp {u v δ : ℝ} (hu : a < u) (huv : u < v) (hδ : 0 < δ) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
        fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * (μ u + δ) +
          (z.re - u) / (v - u) * (μ v + δ)) := by
    obtain ⟨T, hT⟩ := hAnalytic
    refine isBigO_height_affine huv hξ.le (by linarith [hμ₀ u]) (by linarith [hμ₀ v])
      ⟨T, fun z hz ↦ hT z (hu.trans_le hz.1)⟩ (hξBound.mono ?_)
      (hLine hu (lt_add_of_pos_right _ hδ)) (hLine (hu.trans huv) (lt_add_of_pos_right _ hδ))
    exact inf_le_inf_left _ (principal_mono.mpr (preimage_mono fun _ hx ↦ hu.trans_le hx.1))
  -- Restrict the strip estimate to a single line and let the exponent slack tend to zero.
  have hChord {u v α β : ℝ} (hu : a < u) (huv : u < v) (hα : 0 < α) (hβ : 0 < β)
      (hab : α + β = 1) : μ (α * u + β * v) ≤ α * μ u + β * μ v := by
    let x := α * u + β * v
    have hx : x ∈ Icc u v := (convex_Icc u v) (left_mem_Icc.mpr huv.le)
      (right_mem_Icc.mpr huv.le) hα.le hβ.le hab
    have hθ : (x - u) / (v - u) = β := by
      apply (div_eq_iff (sub_ne_zero.mpr huv.ne')).mpr
      dsimp [x]
      linear_combination u * hab
    apply le_of_forall_pos_le_add
    intro δ hδ
    let k : ℝ≥0 := ⟨α * μ u + β * μ v + δ, by positivity⟩
    have hBound : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
      have hSub : ({x} : Set ℝ) ⊆ Icc u v := singleton_subset_iff.mpr hx
      have hb := (hInterp hu huv hδ).mono
        (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hSub)))
      refine hb.congr' Filter.EventuallyEq.rfl (eventually_inf_principal.mpr ?_)
      refine Eventually.of_forall fun z hz ↦ ?_
      have hz' : z.re = x := hz
      simp only [hz', hθ]
      congr 1
      change _ = α * μ u + β * μ v + δ
      have hα' : 1 - β = α := by linarith
      rw [hα']
      have hδsum : (α + β) * δ = δ := by rw [hab, one_mul]
      linear_combination hδsum
    exact (ENNReal.toReal_le_toReal (hμFinite (hu.trans_le hx.1)) ENNReal.coe_ne_top).mpr
      (sInf_le ⟨k, hBound, rfl⟩)
  have hConvex : ConvexOn ℝ (Ioi a) μ := by
    refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro u hu v hv huv α β hα hβ hab
    simp only [smul_eq_mul]
    rcases lt_or_gt_of_ne huv with h | h
    · exact hChord hu h hα hβ hab
    · simpa only [add_comm] using hChord hv h hβ hα (by rwa [add_comm])
  have hCont := hConvex.continuousOn isOpen_Ioi
  -- On a small interval, both endpoint orders are close to the order at any interior point.
  let S := Icc σ₁ σ₂
  have hLocal (x : S) : ∃ r > 0, ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ,
      z.re ∈ Metric.ball (x : ℝ) r → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ (μ z.re + ε) := by
    have hx : a < (x : ℝ) := h₁.trans_le x.property.1
    have hAt := (hCont (x : ℝ) hx).continuousAt (Ioi_mem_nhds hx)
    obtain ⟨d, hd, hNear⟩ := Metric.continuousAt_iff.mp hAt (ε / 4) (by positivity)
    let r := min (d / 2) (((x : ℝ) - a) / 2)
    have hr : 0 < r := lt_min (by positivity) (by linarith)
    let u := (x : ℝ) - r
    let v := (x : ℝ) + r
    have hu : a < u := by
      have := min_le_right (d / 2) (((x : ℝ) - a) / 2)
      dsimp [u]
      linarith
    have huv : u < v := by dsimp [u, v]; linarith
    have hNear' {y : ℝ} (hy : y ∈ Icc u v) : |μ y - μ (x : ℝ)| < ε / 4 := by
      apply hNear
      rw [Real.dist_eq]
      have hDy : |y - (x : ℝ)| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      exact hDy.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun y ↦
      (1 - (y - u) / (v - u)) * (μ u + ε / 4) +
        (y - u) / (v - u) * (μ v + ε / 4))).mp (hInterp hu huv (by positivity))
    refine ⟨r, hr, C, hC, max T 1, fun z hz hHeight ↦ ?_⟩
    have hz' : z.re ∈ Icc u v := Ioo_subset_Icc_self (by rwa [Real.ball_eq_Ioo] at hz)
    have hNearLeft := (abs_lt.mp (hNear' (left_mem_Icc.mpr huv.le))).2
    have hNearRight := (abs_lt.mp (hNear' (right_mem_Icc.mpr huv.le))).2
    have hNearPoint := (abs_lt.mp (hNear' hz')).1
    let t := (z.re - u) / (v - u)
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz'.1) (sub_nonneg.mpr huv.le)
    have ht' : t ≤ 1 := by
      dsimp [t]
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hz'.2 _
    have hExponent : (1 - t) * (μ u + ε / 4) + t * (μ v + ε / 4) ≤ μ z.re + ε := by
      calc
        _ ≤ (1 - t) * (μ z.re + ε) + t * (μ z.re + ε) := add_le_add
          (mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr ht'))
          (mul_le_mul_of_nonneg_left (by linarith) ht)
        _ = _ := by ring
    exact (hT z hz' ((le_max_left _ _).trans hHeight)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hExponent) hC.le)
  choose r hr C hC T hT using hLocal
  obtain ⟨J, hJ⟩ := (isCompact_Icc (a := σ₁) (b := σ₂)).elim_finite_subcover
    (fun x : S ↦ Metric.ball (x : ℝ) (r x)) (fun _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  obtain ⟨C', hC'⟩ := (J.finite_toSet.image C).bddAbove
  obtain ⟨T', hT'⟩ := (J.finite_toSet.image T).bddAbove
  obtain ⟨x₀, hx₀, _⟩ := mem_iUnion₂.mp (hJ (left_mem_Icc.mpr h₂.le))
  refine (isBigO_height_iff (p := fun x ↦ μ x + ε)).mpr
    ⟨C', (hC x₀).trans_le (hC' ⟨x₀, hx₀, rfl⟩), T', fun z hz hHeight ↦ ?_⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hJ hz)
  exact (hT x z hzx ((hT' ⟨x, hx, rfl⟩).trans hHeight)).trans
    (mul_le_mul_of_nonneg_right (hC' ⟨x, hx, rfl⟩) (Real.rpow_nonneg (abs_nonneg _) _))

end GrowthOrder

section Hecke

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- TODO(paper-gap): In Lemma B.1.1.2 the exponent must be allowed to depend on
-- the strip. For ζ on each line σ < 0 the growth order is 1/2 - σ.

/-- The finite Dirichlet series is bounded on every closed half-plane strictly to the right of
one. The absolute series at the real endpoint majorizes the series throughout the half-plane. -/
private theorem finiteHeckeL_continuation_boundedOn_right (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, ∀ s : ℂ, r ≤ s.re → ‖L s‖ ≤ C := by
  let c := (ideleClassNormTwist χ 0).LFunction
  have hsum : Summable (fun n ↦ ‖LSeries.term c (r : ℂ) n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), by simpa using hr⟩).norm
  refine ⟨∑' n, ‖LSeries.term c (r : ℂ) n‖, fun s hs ↦ ?_⟩
  have hs' : 1 < s.re := hr.trans_le hs
  rw [show L s = finiteHeckeL χ ⟨s, hs'⟩ from hSeries ⟨s, hs'⟩]
  change ‖∑' n, LSeries.term c s n‖ ≤ _
  have hsSum : Summable (fun n ↦ ‖LSeries.term c s n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨s, hs'⟩).norm
  exact (norm_tsum_le_tsum_norm hsSum).trans
    (hsSum.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re c (by simpa using hs)) hsum)

/-- On any right half-plane the finite continuation has only finitely many poles, all simple.
The completed continuation has this property, and its reciprocal gamma factor is entire. -/
private theorem exists_analyticOnNhd_isTheta_finiteHeckeL_continuation
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (a : ℝ) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Complex.re ⁻¹' Ioi a) ∧
      G =Θ[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] L := by
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let H := Λ * R
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun s hs ↦
    (hΛ hs).meromorphicAt.mul (hR.analyticAt s).meromorphicAt
  have hAgree : ∀ s : halfPlane, (L - H) s = 0 := by
    intro s
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
    change L s - Λ s * (heckeGammaFactor χ s)⁻¹ = 0
    rw [hSeries s, hΛSeries s, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ s), mul_assoc, mul_inv_cancel₀ hne, mul_one, sub_self]
  have hAtTwo : meromorphicOrderAt (L - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ hAgree ⟨s, hs⟩
  have hOrd (s : ℂ) :
      meromorphicOrderAt L s = meromorphicOrderAt Λ s + meromorphicOrderAt R s := by
    have ho := (hL.meromorphicOn.sub hH).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
    have he : L =ᶠ[𝓝[≠] s] H := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun z hz ↦
      sub_eq_zero.mp hz
    rw [meromorphicOrderAt_congr he]
    exact meromorphicOrderAt_mul (hΛ (mem_univ s)).meromorphicAt (hR.analyticAt s).meromorphicAt
  have hCompare (s : ℂ) : meromorphicOrderAt Λ s ≤ meromorphicOrderAt L s := by
    rw [hOrd]
    exact le_add_of_nonneg_right (hR.analyticAt s).meromorphicOrderAt_nonneg
  have hPoles : ∃ S : Set ℂ, S.Finite ∧
      (∀ s ∉ S, AnalyticAt ℂ Λ s) ∧ ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Λ s := by
    have hNeg : (-1 : WithTop ℤ) ≤ 0 := by decide
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨_, hp, hq, ha⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ Λ hΛ hΛSeries hχ
      refine ⟨_, (finite_singleton (1 + Complex.I * (t : ℂ))).insert _, ha, fun s ↦ ?_⟩
      by_cases h : s = Complex.I * (t : ℂ)
      · rw [h, hp]
      by_cases h' : s = 1 + Complex.I * (t : ℂ)
      · rw [h', hq]
      exact hNeg.trans (ha s (by simp [h, h'])).meromorphicOrderAt_nonneg
    · have h := completedHeckeL_continuation_entire χ Λ hΛ hΛSeries hχ
      exact ⟨∅, finite_empty, fun s _ ↦ h.analyticAt s, fun s ↦
        hNeg.trans (h.analyticAt s).meromorphicOrderAt_nonneg⟩
  obtain ⟨S, hS, hAway, hLower⟩ := hPoles
  apply exists_analyticOnNhd_isTheta_atHeight (fun {_} _ ↦ hL (mem_univ _))
  · refine hS.subset fun s hs ↦ ?_
    by_contra h
    exact (not_lt_of_ge ((hAway s h).meromorphicOrderAt_nonneg.trans (hCompare s))) hs.2
  · intro s _ hs
    have hBound := (hLower s).trans (hCompare s)
    generalize meromorphicOrderAt L s = m at hs hBound ⊢
    cases m with
    | top => simp at hs
    | coe m =>
      have hm₁ : (-1 : ℤ) ≤ m := WithTop.coe_le_coe.mp hBound
      have hm₂ : m < (0 : ℤ) := WithTop.coe_lt_coe.mp hs
      have hm : m = -1 := by omega
      simp [hm]

/-- The product of the reciprocal archimedean factors has an exponential bound on each
closed strip. A complex factor is handled as two real factors via the duplication formula. -/
private theorem inv_heckeGammaFactor_isBigO_exp (χ : U[F]) (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧
      (fun s ↦ (heckeGammaFactor χ s)⁻¹) =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
        fun s ↦ Real.exp (B * |s.im|) := by
  classical
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)
  let P (v : InfinitePlace F) (s : ℂ) :=
    (if hv : v.IsReal then
      let d := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + d.1 + (d.2.val : ℂ))
    else
      let d := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + d.1 + (d.2.natAbs : ℂ) / 2) / 2)⁻¹
  have hP (v : InfinitePlace F) : P v =O[l] fun s ↦ Real.exp (Real.pi * |s.im|) := by
    by_cases hv : v.IsReal
    · let d := (realHeckeCharacter_parameters χ v hv).exists.choose
      have h := inv_Gammaℝ_add_isBigO_exp a b (d.1 + (d.2.val : ℂ))
      refine (show P v =O[l] fun s ↦ Real.exp ((Real.pi / 2) * |s.im|) by
        simpa only [P, dite_eq_left hv, d, add_assoc] using h).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s ↦ ?_)
      rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      gcongr
      linarith [Real.pi_pos]
    · let d := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      let w := d.1 + (d.2.natAbs : ℂ) / 2
      have h := ((inv_Gammaℝ_add_isBigO_exp a b w).mul
        (inv_Gammaℝ_add_isBigO_exp a b (w + 1))).const_mul_left (2 : ℂ)
      have hLocal (s : ℂ) : P v s =
          2 * ((Complex.Gammaℝ (s + w))⁻¹ * (Complex.Gammaℝ (s + (w + 1)))⁻¹) := by
        simp only [P, dite_eq_right hv, d, w, ← add_assoc, div_eq_mul_inv, mul_inv_rev, inv_inv,
          ← Complex.Gammaℝ_mul_Gammaℝ_add_one]
        ring
      simpa only [← hLocal, ← Real.exp_add, ← add_mul, add_halves] using h
  have hProd := Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ ↦ hP v)
  have hInv : (fun s ↦ (heckeGammaFactor χ s)⁻¹) =O[l]
      fun s ↦ Real.exp ((Fintype.card (InfinitePlace F) * Real.pi) * |s.im|) := by
    simpa only [P, heckeGammaFactor, Finset.prod_inv_distrib, Finset.prod_const,
      Finset.card_univ, ← Real.exp_nat_mul, mul_assoc] using hProd
  refine ⟨Fintype.card (InfinitePlace F) * Real.pi + 1, by positivity, hInv.trans ?_⟩
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s ↦ ?_)
  rw [one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  exact le_add_of_nonneg_right zero_le_one

section TateBound

open MeasureTheory
open scoped NumberField.AdeleRing

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "classNormℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)

local instance instMeasurableClassTateBound : MeasurableSpace C[F] := borel _
local instance instBorelClassTateBound : BorelSpace C[F] := ⟨rfl⟩

/-- The absolute value of the theta integrand depends on the exponent only through
its real part. -/
private theorem norm_theta_twist (f : ℬ[F]) (χ : U[F]) (s : ℂ) (g : C[F]) :
    ‖adelicTheta f g * ideleClassNormTwist χ s g‖ =
      ‖adelicTheta f g‖ * classNormℝ g ^ s.re := by
  change ‖adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ s)‖ = _
  rw [norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]

/-- Paper: Equation (3.1.1.2), p. 119. A norm twist of a unitary character lies
in the absolute convergence half-plane when the real exponent is greater than one. -/
private theorem twist_mem_rightHalfPlane (χ : U[F]) (s : ℂ) (hs : 1 < s.re) :
    ideleClassNormTwist χ s ∈
      (↑(relativeRightHalfPlane (G := C[F]) (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) 1) : Set (HeckeCharacter (𝓞 F) F)) := by
  change 1 < quasiCharacterAbscissa (G := C[F]) (ideleClassNorm F) _ _ (ideleClassNormTwist χ s)
  rw [quasiCharacterAbscissa_of_unitary_twist (G := C[F]) _ _ _ _ χ s (fun _ ↦ rfl)]
  exact hs

/-- Absolute convergence of the theta integral at any real exponent greater than one
provides an integrable majorant on the large-norm domain. -/
private theorem integrableOn_norm_theta_twist (f : ℬ[F]) (r : ℝ) (hr : 1 < r)
    (S : Set C[F]) :
    IntegrableOn (fun g ↦ ‖adelicTheta f g‖ * classNormℝ g ^ r) S
      (ideleClassTamagawaMeasure F) := by
  let c := ideleClassNormTwist (1 : U[F]) (r : ℂ)
  have hc := twist_mem_rightHalfPlane (1 : U[F]) (r : ℂ) (by simpa using hr)
  have h := (globalThetaMellinIntegral_integrable f c hc).norm.integrableOn (s := S)
  simpa only [c, norm_theta_twist, Complex.ofReal_re] using h

/-- Paper: Equation (3.2.2.3), p. 124. The theta Mellin integral restricted to
a specified set of idele classes. -/
private def thetaMellinOn (f : ℬ[F]) (χ : U[F]) (S : Set C[F]) (s : ℂ) : ℂ :=
  ∫ g in S, adelicTheta f g * ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F

/-- Paper: Equations (3.2.2.7)–(3.2.2.9), pp. 126–127. On a domain with norm at
least one, the theta Mellin integral is bounded uniformly when the real exponent
is bounded above. -/
private theorem norm_thetaMellinOn_le (f : ℬ[F]) (χ : U[F]) {S : Set C[F]}
    (hS : MeasurableSet S) (hNorm : ∀ g ∈ S, 1 ≤ classNormℝ g)
    {r : ℝ} (hr : 1 < r) {s : ℂ} (hs : s.re ≤ r) :
    ‖thetaMellinOn f χ S s‖ ≤
      ∫ g in S, ‖adelicTheta f g‖ * classNormℝ g ^ r ∂ideleClassTamagawaMeasure F := by
  apply norm_integral_le_of_norm_le (integrableOn_norm_theta_twist f r hr S)
  refine (ae_restrict_mem hS).mono fun g hg ↦ ?_
  rw [norm_theta_twist]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hNorm g hg) hs)
    (norm_nonneg _)

private theorem classNormReal_pos (g : C[F]) : 0 < classNormℝ g :=
  NNReal.coe_pos.mpr (Units.zero_lt _)

private theorem continuous_classNormReal : Continuous (fun g : C[F] ↦ classNormℝ g) :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)

/-- The large-norm theta integral is entire. On a neighborhood of a given exponent,
one larger real exponent dominates both the integrand and its derivative. -/
private theorem differentiable_thetaMellinOn (f : ℬ[F]) (χ : U[F]) {S : Set C[F]}
    (hS : MeasurableSet S) (hNorm : ∀ g ∈ S, 1 ≤ classNormℝ g) :
    Differentiable ℂ (thetaMellinOn f χ S) := by
  intro s
  let μ := (ideleClassTamagawaMeasure F).restrict S
  let W (z : ℂ) (g : C[F]) := adelicTheta f g * ideleClassNormTwist χ z g
  let D (z : ℂ) (g : C[F]) := W z g * Complex.log (classNormℝ g : ℂ)
  let r := max (s.re + 2) 2
  let V := {z : ℂ | z.re < s.re + 1}
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  have hV : V ∈ 𝓝 s :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      change s.re < s.re + 1
      linarith)
  have hW (z : ℂ) : Continuous (W z) :=
    (adelicTheta f).continuous.mul (ideleClassNormTwist χ z).continuous
  have hμ := ae_restrict_mem (μ := ideleClassTamagawaMeasure F) hS
  have hMajorant := integrableOn_norm_theta_twist f r hr S
  have hsInt : Integrable (W s) μ := by
    refine hMajorant.mono' (hW s).aestronglyMeasurable (hμ.mono fun g hg ↦ ?_)
    change ‖adelicTheta f g * ideleClassNormTwist χ s g‖ ≤ _
    rw [norm_theta_twist]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (hNorm g hg) ?_)
      (norm_nonneg _)
    exact (by linarith : s.re ≤ s.re + 2).trans (le_max_left _ _)
  have hDMeas : AEStronglyMeasurable (D s) μ :=
    (hW s).aestronglyMeasurable.mul
      (Complex.measurable_log.comp
        (Complex.continuous_ofReal.comp continuous_classNormReal).measurable).aestronglyMeasurable
  have hDBound : ∀ᵐ g ∂μ, ∀ z ∈ V, ‖D z g‖ ≤ ‖adelicTheta f g‖ * classNormℝ g ^ r := by
    refine hμ.mono fun g hg z hz ↦ ?_
    have hg₁ := hNorm g hg
    have hgPos := zero_lt_one.trans_le hg₁
    change z.re < s.re + 1 at hz
    change ‖(adelicTheta f g * ideleClassNormTwist χ z g) * _‖ ≤ _
    rw [norm_mul, norm_theta_twist, ← Complex.ofReal_log hgPos.le,
      Complex.norm_of_nonneg (Real.log_nonneg hg₁)]
    calc
      _ ≤ (‖adelicTheta f g‖ * classNormℝ g ^ z.re) * classNormℝ g :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hgPos.le) (by positivity)
      _ = ‖adelicTheta f g‖ * classNormℝ g ^ (z.re + 1) := by
        rw [Real.rpow_add hgPos, Real.rpow_one, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hg₁
          ((by linarith : z.re + 1 ≤ s.re + 2).trans (le_max_left _ _))) (norm_nonneg _)
  have hDiff : ∀ᵐ g ∂μ, ∀ z ∈ V, HasDerivAt (fun w ↦ W w g) (D z g) z := by
    refine Eventually.of_forall fun g z _ ↦ ?_
    have hg : (classNormℝ g : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change HasDerivAt (fun w : ℂ ↦ adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ w))
      ((adelicTheta f g * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ z)) *
        Complex.log (classNormℝ g : ℂ)) z
    simpa only [id_eq, mul_assoc, mul_one] using
      (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul (χ g : ℂ)).const_mul (adelicTheta f g)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV
    (Eventually.of_forall fun z ↦ (hW z).aestronglyMeasurable) hsInt hDMeas hDBound hMajorant
    hDiff).2.differentiableAt

local notation "largeNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Ici 1)
local notation "strictLargeNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Ioi 1)

local notation "smallNorm[" F "]" => ((classNormℝ : C[F] → ℝ) ⁻¹' Iio 1)

/-- The logarithmic norm sends the class Haar measure to a multiple of Lebesgue
measure, since the class norm is proper and surjective. -/
private theorem exists_map_logClassNorm_eq_smul_volume :
    ∃ c : ℝ≥0, (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log (classNormℝ g)) =
      c • (volume : Measure ℝ) := by
  let μ := ideleClassTamagawaMeasure F
  let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
  let : ν.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts ν :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure ν :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : ν.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let m : C[F] →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (e (ideleClassNorm F g))
      map_one' := by
        change e (ideleClassNorm F 1) = 0
        simp [he]
      map_mul' := fun g h ↦ by
        change e (ideleClassNorm F (g * h)) = e (ideleClassNorm F g) + e (ideleClassNorm F h)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (classNormReal_pos g).ne' (classNormReal_pos h).ne' }
  have hm : IsProperMap m :=
    e.isProperMap.comp (isProperMap_ideleClassNorm F)
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hsurj : Surjective m := e.surjective.comp hsurj
  let : (μ.map m).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ m hm.continuous hsurj (isProperMap_iff_tendsto_cocompact.mp hm).2
  refine ⟨Measure.haarScalarFactor (μ.map m) ν, ?_⟩
  have hMap := Measure.isMulLeftInvariant_eq_smul (μ.map m) ν
  have hFun : (m : C[F] → ℝ) = fun g ↦ Real.log (classNormℝ g) :=
    funext fun g ↦ he (ideleClassNorm F g)
  rw [← hFun]
  exact hMap

/-- On the norm-below-one domain a pure power has Mellin integral equal to a
constant divided by the exponent. -/
private theorem integral_classNorm_cpow_smallNorm :
    ∃ c : ℝ≥0, ∀ s : ℂ, 0 < s.re →
      IntegrableOn (fun g ↦ (classNormℝ g : ℂ) ^ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], (classNormℝ g : ℂ) ^ s ∂ideleClassTamagawaMeasure F) =
        (c : ℝ) / s := by
  obtain ⟨c, hc⟩ := exists_map_logClassNorm_eq_smul_volume (F := F)
  refine ⟨c, fun s hs ↦ ?_⟩
  let μ := ideleClassTamagawaMeasure F
  let l (g : C[F]) := Real.log (classNormℝ g)
  let E (t : ℝ) := Complex.exp (s * (t : ℂ))
  have hl : Continuous l :=
    continuous_classNormReal.log fun g ↦ (classNormReal_pos g).ne'
  have hSmall : l ⁻¹' Iio 0 = smallNorm[F] := by
    ext g
    exact Real.log_neg_iff (classNormReal_pos g)
  have hmap : (μ.restrict smallNorm[F]).map l = c • (volume.restrict (Iio 0)) := by
    rw [← hSmall, ← Measure.restrict_map hl.measurable measurableSet_Iio, hc, Measure.restrict_smul]
  have hE : Continuous E := Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hInt : Integrable E ((μ.restrict smallNorm[F]).map l) := by
    rw [hmap]
    exact ((integrableOn_exp_mul_complex_Iic hs 0).mono_set Iio_subset_Iic_self).smul_measure
      ENNReal.coe_ne_top
  have hPow (g : C[F]) : E (l g) = (classNormℝ g : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (classNormReal_pos g).ne'),
      ← Complex.ofReal_log (classNormReal_pos g).le, mul_comm]
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, hPow, IntegrableOn, μ] using
      (integrable_map_measure hE.aestronglyMeasurable hl.measurable.aemeasurable).mp hInt
  · simp_rw [← hPow]
    rw [← integral_map hl.measurable.aemeasurable hE.aestronglyMeasurable, hmap,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
      ← integral_Iic_eq_integral_Iio]
    simp only [E, integral_exp_mul_complex_Iic hs, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      div_eq_mul_inv, one_mul]

/-- The Mellin transform of the cut-off quasi-character on the norm-below-one
domain is a simple polar term. Integration over the norm-one subgroup kills a
nontrivial restriction of the character. For a norm character, the logarithmic
norm coordinate reduces the integral to an exponential integral on `(-∞, 0)`. -/
private theorem integral_twist_smallNorm (χ : U[F]) :
    ∃ p c : ℂ, p.re = 0 ∧ ∀ s : ℂ, 0 < s.re →
      IntegrableOn (ideleClassNormTwist χ s) smallNorm[F] (ideleClassTamagawaMeasure F) ∧
      (∫ g in smallNorm[F], ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F) =
        c / (s - p) := by
  obtain ⟨c, hc⟩ := integral_classNorm_cpow_smallNorm (F := F)
  let μ := ideleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := F)).1
  by_cases hχ : ∃ g : C[F], ideleClassNorm F g = 1 ∧ χ g ≠ 1
  · obtain ⟨g, hg, hne⟩ := hχ
    refine ⟨0, 0, Complex.zero_re, fun s hs ↦ ?_⟩
    obtain ⟨hPow, -⟩ := hc s hs
    let W : C[F] → ℂ := ideleClassNormTwist χ s
    have hInt : IntegrableOn W smallNorm[F] μ := by
      refine hPow.norm.mono' (ideleClassNormTwist χ s).continuous.aestronglyMeasurable
        (Eventually.of_forall fun x ↦ ?_)
      change ‖(χ x : ℂ) * (classNormℝ x : ℂ) ^ s‖ ≤ ‖(classNormℝ x : ℂ) ^ s‖
      rw [norm_mul, Circle.norm_coe, one_mul]
    refine ⟨hInt, ?_⟩
    have hPre : (fun x : C[F] ↦ g * x) ⁻¹' smallNorm[F] = smallNorm[F] := by
      ext x
      change classNormℝ (g * x) < 1 ↔ classNormℝ x < 1
      dsimp only
      rw [map_mul, hg, one_mul]
    have hInv := (measurePreserving_mul_left μ g).setIntegral_preimage_emb
      (Homeomorph.mulLeft g).toMeasurableEquiv.measurableEmbedding W smallNorm[F]
    rw [hPre] at hInv
    have hWg : W g = (χ g : ℂ) := by
      change (χ g : ℂ) * (classNormℝ g : ℂ) ^ s = _
      simp [hg]
    change (∫ x in smallNorm[F], W (g * x) ∂μ) = (∫ x in smallNorm[F], W x ∂μ) at hInv
    have hMul (x : C[F]) : W (g * x) = (χ g : ℂ) * W x := by
      rw [← hWg]
      exact (ideleClassNormTwist χ s).map_mul g x
    simp_rw [hMul] at hInv
    rw [integral_const_mul, ← sub_eq_zero, ← sub_one_mul] at hInv
    have : (χ g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h ↦ hne (Subtype.ext h)
    rw [zero_div]
    exact (mul_eq_zero.mp hInv).resolve_left this
  · have hTriv (g : C[F]) (hg : ideleClassNorm F g = 1) : χ g = 1 := by
      by_contra h
      exact hχ ⟨g, hg, h⟩
    let q : IdeleGroup (𝓞 F) F →ₜ* C[F] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C[F] := q.comp
      ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    have hσ : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    obtain ⟨w, hw, -⟩ := existsUnique_complexPower (j.comp (χ.comp σ))
    have hParam (t : ℝ≥0ˣ) : (χ (σ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ w := hw t
    have hwRe : w.re = 0 := by
      let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
      have h := congrArg norm (hParam t)
      rw [Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num [t])] at h
      change 1 = (2 : ℝ) ^ w.re at h
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_zero] at h
      exact (mul_eq_zero.mp (Real.exp_injective h.symm)).resolve_left
        (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    refine ⟨-w, (c : ℝ), by simpa using hwRe, fun s hs ↦ ?_⟩
    have hTwist (g : C[F]) : ideleClassNormTwist χ s g = (classNormℝ g : ℂ) ^ (s + w) := by
      have hn : ideleClassNorm F (g * (σ (ideleClassNorm F g))⁻¹) = 1 := by
        rw [map_mul, map_inv, hσ _, mul_inv_cancel]
      have h := hTriv _ hn
      rw [map_mul, map_inv, mul_inv_eq_one] at h
      change (χ g : ℂ) * (classNormℝ g : ℂ) ^ s = _
      rw [h, hParam, add_comm s w, Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr (classNormReal_pos g).ne')]
    have hs' : 0 < (s + w).re := by simpa only [Complex.add_re, hwRe, add_zero] using hs
    rw [show (ideleClassNormTwist χ s : C[F] → ℂ) = _ from funext hTwist, sub_neg_eq_add]
    exact hc (s + w) hs'

/-- Multiplication by the inverse class norm subtracts one from the twist exponent. -/
private theorem inv_norm_mul_twist (χ : U[F]) (s : ℂ) (g : C[F]) :
    (classNormℝ g : ℂ)⁻¹ * ideleClassNormTwist χ s g = ideleClassNormTwist χ (s - 1) g := by
  have hn : (classNormℝ g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change _ * ((χ g : ℂ) * (classNormℝ g : ℂ) ^ s) =
    (χ g : ℂ) * (classNormℝ g : ℂ) ^ (s - 1)
  rw [Complex.cpow_sub _ _ hn, Complex.cpow_one, div_eq_mul_inv]
  ring

/-- Evaluating the reflected twist on the inverse class supplies the inverse norm
factor in adelic Riemann–Roch. -/
private theorem twist_inv_apply (χ : U[F]) (s : ℂ) (g : C[F]) :
    ideleClassNormTwist χ⁻¹ (1 - s) g⁻¹ = ideleClassNormTwist χ (s - 1) g := by
  change (((χ⁻¹) g⁻¹ : Circle) : ℂ) * (classNormℝ g⁻¹ : ℂ) ^ (1 - s) =
    (χ g : ℂ) * (classNormℝ g : ℂ) ^ (s - 1)
  have hχ : (χ⁻¹) g⁻¹ = χ g := by
    rw [map_inv]
    change (χ g)⁻¹⁻¹ = χ g
    exact inv_inv _
  rw [hχ]
  simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _),
    ← Complex.cpow_neg, neg_sub]

/-- Paper: Theorems 2.2.3.2 and 3.2.2.1, pp. 82 and 124. Splitting the theta
Mellin integral at norm one and applying adelic Riemann–Roch on the small-norm
part gives the two large-norm integrals and the simple polar terms.
Deviation: The boundary of norm one is assigned to the original test function.
Zero residues are allowed, including when the continuation is entire. -/
private theorem globalIdelicZFunction_eq_thetaMellin_split (f : ℬ[F]) (χ : U[F]) :
    ∃ p q A B : ℂ, ∀ s : ℂ, s ≠ p → s ≠ q →
      globalIdelicZFunction f (ideleClassNormTwist χ s) =
        thetaMellinOn f χ largeNorm[F] s +
        thetaMellinOn (adeleSchwartzFourier f) χ⁻¹ strictLargeNorm[F] (1 - s) +
        A / (s - p) + B / (s - q) := by
  obtain ⟨p, c, hp, hpol⟩ := integral_twist_smallNorm χ
  let μ := ideleClassTamagawaMeasure F
  let f₀ := f (Multiplicative.ofAdd (0 : 𝔸[F]))
  let fFourier := adeleSchwartzFourier f
  let fFourier₀ := fFourier (Multiplicative.ofAdd (0 : 𝔸[F]))
  let A := fFourier₀ * c
  let B := -(f₀ * c)
  let Z (s : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ s)
  let G (s : ℂ) :=
    thetaMellinOn f χ largeNorm[F] s + thetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - s) +
      A / (s - (1 + p)) + B / (s - p)
  refine ⟨1 + p, p, A, B, ?_⟩
  have hBig : MeasurableSet largeNorm[F] :=
    measurableSet_le measurable_const continuous_classNormReal.measurable
  have hStrictBig : MeasurableSet strictLargeNorm[F] :=
    measurableSet_lt measurable_const continuous_classNormReal.measurable
  have hSmall : MeasurableSet smallNorm[F] :=
    measurableSet_lt continuous_classNormReal.measurable measurable_const
  have hComp : (largeNorm[F])ᶜ = smallNorm[F] := by
    ext g
    exact not_le
  have hInv : (fun g : C[F] ↦ g⁻¹) ⁻¹' strictLargeNorm[F] = smallNorm[F] := by
    ext g
    change 1 < classNormℝ g⁻¹ ↔ classNormℝ g < 1
    simp only [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
    exact one_lt_inv₀ (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hWeil := ideleClassTamagawaMeasure_isWeil (F := F)
  let : μ.IsHaarMeasure := hWeil.1
  let : μ.Regular := hWeil.2.1
  let : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hAgree (s : ℂ) (hs : 1 < s.re) : Z s = G s := by
    let W (z : ℂ) (g : C[F]) := ideleClassNormTwist χ z g
    let D (g : C[F]) := adelicTheta fFourier g⁻¹ * W (s - 1) g
    have hc := twist_mem_rightHalfPlane χ s hs
    have hInt := globalThetaMellinIntegral_integrable f (ideleClassNormTwist χ s) hc
    have hWhole : Z s = ∫ g, adelicTheta f g * W s g ∂μ :=
      (globalIdelicZFunction_eq_integral f hc).trans
        (globalThetaMellinIntegral_eq_idelic f hc).symm
    have hRiemann (g : C[F]) :
        adelicTheta f g * W s g = D g + fFourier₀ * W (s - 1) g - f₀ * W s g := by
      change adelicTheta f g * ideleClassNormTwist χ s g =
        adelicTheta fFourier g⁻¹ * ideleClassNormTwist χ (s - 1) g +
          fFourier₀ * ideleClassNormTwist χ (s - 1) g - f₀ * ideleClassNormTwist χ s g
      rw [← inv_norm_mul_twist, adelicTheta_riemannRoch]
      simp only [Complex.real_smul, Complex.ofReal_inv]
      ring
    have hs' : 0 < (s - 1).re := by simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hs
    obtain ⟨hInt₀, hPolar₀⟩ := hpol s (zero_lt_one.trans hs)
    obtain ⟨hInt₁, hPolar₁⟩ := hpol (s - 1) hs'
    have hD : IntegrableOn D smallNorm[F] μ := by
      refine (integrableOn_congr_fun (g := D) (fun g _ ↦ ?_) hSmall).mp
        ((hInt.integrableOn.add (hInt₀.const_mul f₀)).sub (hInt₁.const_mul fFourier₀))
      change adelicTheta f g * W s g + f₀ * W s g - fFourier₀ * W (s - 1) g = D g
      rw [hRiemann]
      ring
    have hInvInt : (∫ g in smallNorm[F], D g ∂μ) =
        thetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - s) := by
      have h := (Measure.measurePreserving_inv μ).setIntegral_preimage_emb
        (Homeomorph.inv (C[F])).toMeasurableEquiv.measurableEmbedding
        (fun g ↦ adelicTheta fFourier g * ideleClassNormTwist χ⁻¹ (1 - s) g) strictLargeNorm[F]
      rw [hInv] at h
      refine Eq.trans (setIntegral_congr_fun hSmall fun g _ ↦ ?_) h
      dsimp [D, W]
      rw [twist_inv_apply]
    calc
      Z s = thetaMellinOn f χ largeNorm[F] s +
          (∫ g in smallNorm[F], adelicTheta f g * W s g ∂μ) := by
        rw [hWhole, thetaMellinOn, ← hComp]
        exact (integral_add_compl hBig hInt).symm
      _ = G s := by
        simp_rw [hRiemann]
        have hAdd := integral_add hD (hInt₁.const_mul fFourier₀)
        have hSub := integral_sub (hD.add (hInt₁.const_mul fFourier₀)) (hInt₀.const_mul f₀)
        simp only [Pi.add_apply] at hSub
        rw [hSub, hAdd, integral_const_mul, integral_const_mul, hInvInt, hPolar₁, hPolar₀]
        dsimp only [G, W, A, B]
        rw [show s - 1 - p = s - (1 + p) by ring]
        ring
  have h₁ := differentiable_thetaMellinOn f χ hBig (fun _ hg ↦ hg)
  have h₂ := differentiable_thetaMellinOn fFourier χ⁻¹ hStrictBig (fun _ hg ↦ le_of_lt hg)
  have hG₁ := h₁.analyticAt
  have hG₂ (s : ℂ) :
      AnalyticAt ℂ (fun z ↦ thetaMellinOn fFourier χ⁻¹ strictLargeNorm[F] (1 - z)) s :=
    (h₂.analyticAt (1 - s)).comp (by fun_prop)
  have hDen₁ (s : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z - (1 + p)) s := by fun_prop
  have hDen₀ (s : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ z - p) s := by fun_prop
  have hG : MeromorphicOn G univ := by
    intro s _
    exact (((hG₁ s).meromorphicAt.add (hG₂ s).meromorphicAt).add
      (analyticAt_const.meromorphicAt.div (hDen₁ s).meromorphicAt)).add
      (analyticAt_const.meromorphicAt.div (hDen₀ s).meromorphicAt)
  have hZ : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hAtTwo : meromorphicOrderAt (Z - G) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ sub_eq_zero.mpr (hAgree s hs)
  intro s hs₁ hs₀
  have hOrd := (hZ.meromorphicOn.sub hG).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
  have hNear : Z =ᶠ[𝓝[≠] s] G :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  have ha : AnalyticAt ℂ G s := by
    exact (((hG₁ s).add (hG₂ s)).add
      (analyticAt_const.div (hDen₁ s) (sub_ne_zero.mpr hs₁))).add
      (analyticAt_const.div (hDen₀ s) (sub_ne_zero.mpr hs₀))
  exact (((hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    ha.meromorphicNFAt).mp hNear).eq_of_nhds

/-- A simple polar term is bounded once the absolute imaginary part exceeds the
absolute imaginary part of its pole by at least one. -/
private theorem norm_div_sub_le_atHeight (A p : ℂ) {s : ℂ}
    (hs : |p.im| + 1 ≤ |s.im|) : ‖A / (s - p)‖ ≤ ‖A‖ := by
  have hdiff := abs_sub_abs_le_abs_sub s.im p.im
  have hden : 1 ≤ ‖s - p‖ := by
    have h := Complex.abs_im_le_norm (s - p)
    rw [Complex.sub_im] at h
    linarith
  rw [norm_div]
  exact div_le_self (norm_nonneg _) hden

/-- On each closed vertical strip the global zeta continuation is bounded at
large absolute height by the absolute integrals at fixed real exponents and the
norms of its two residues. -/
private theorem globalIdelicZFunction_isBigO_one (f : ℬ[F]) (χ : U[F]) (a b : ℝ) :
    (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s))
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨p, q, A, B, hSplit⟩ := globalIdelicZFunction_eq_thetaMellin_split f χ
  let r := max b 2
  let r' := max (1 - a) 2
  let C₁ := ∫ g in largeNorm[F], ‖adelicTheta f g‖ * classNormℝ g ^ r ∂ideleClassTamagawaMeasure F
  let C₂ := ∫ g in strictLargeNorm[F], ‖adelicTheta (adeleSchwartzFourier f) g‖ *
    classNormℝ g ^ r' ∂ideleClassTamagawaMeasure F
  have hHeight : ∀ᶠ s : ℂ in atHeight, max |p.im| |q.im| + 1 ≤ |s.im| :=
    tendsto_comap.eventually (eventually_ge_atTop _)
  have hStrip : ∀ᶠ s : ℂ in 𝓟 (Complex.re ⁻¹' Icc a b), s.re ∈ Icc a b :=
    eventually_mem_principal _
  refine Asymptotics.IsBigO.of_bound (C₁ + C₂ + ‖A‖ + ‖B‖) ?_
  filter_upwards [hHeight.filter_mono inf_le_left, hStrip.filter_mono inf_le_right]
    with s hsHeight hsStrip
  have hp : |p.im| + 1 ≤ |s.im| := (add_le_add (le_max_left |p.im| |q.im|) le_rfl).trans hsHeight
  have hq : |q.im| + 1 ≤ |s.im| := (add_le_add (le_max_right |p.im| |q.im|) le_rfl).trans hsHeight
  have hp' : s ≠ p := fun h ↦ by subst s; linarith
  have hq' : s ≠ q := fun h ↦ by subst s; linarith
  have hr : 1 < r := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  have hr' : 1 < r' := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  have h₁ : ‖thetaMellinOn f χ largeNorm[F] s‖ ≤ C₁ :=
    norm_thetaMellinOn_le f χ (measurableSet_le measurable_const continuous_classNormReal.measurable)
      (fun _ hg ↦ hg) hr (hsStrip.2.trans (le_max_left _ _))
  have h₂ : ‖thetaMellinOn (adeleSchwartzFourier f) χ⁻¹ strictLargeNorm[F] (1 - s)‖ ≤ C₂ :=
    norm_thetaMellinOn_le _ _
      (measurableSet_lt measurable_const continuous_classNormReal.measurable)
      (fun _ hg ↦ le_of_lt hg) hr' (by
        simp only [Complex.sub_re, Complex.one_re]
        exact (sub_le_sub_left hsStrip.1 1).trans (le_max_left _ _))
  rw [norm_one, mul_one, hSplit s hp' hq']
  exact norm_add₄_le.trans (add_le_add
    (add_le_add (add_le_add h₁ h₂) (norm_div_sub_le_atHeight A p hp))
    (norm_div_sub_le_atHeight B q hq))

/-- The completed Hecke continuation is uniformly bounded at large absolute height on
each fixed closed vertical strip. In Tate's split zeta integral the two integrals over
idele classes of norm at least one are bounded by absolute integrals at the extreme real
exponents, and the simple polar terms are bounded away from their pole heights. -/
private theorem completedHeckeL_continuation_isBigO_one (χ : U[F]) (Λ : ℂ → ℂ)
    (hΛ : MeromorphicNFOn Λ univ) (hSeries : ∀ s : halfPlane, Λ s = completedHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    Λ =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  let f := adelicStandardGaussian χ
  let k : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  let Z (s : ℂ) := globalIdelicZFunction f (ideleClassNormTwist χ s)
  let H (s : ℂ) := k * Λ s
  have hk : k ≠ 0 := by
    have hd : (NumberField.discr F : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.discr_ne_zero F
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (abs_pos.mpr hd)))
  have hZ : MeromorphicNFOn Z univ := globalIdelicZFunction_meromorphic f χ
  have hH : MeromorphicNFOn H univ := fun _ hs ↦ (meromorphicNFAt_fun_const_smul_iff_meromorphicNFAt hk).mpr (hΛ hs)
  have hAgree : ∀ s : ℂ, 1 < s.re → Z s = H s := by
    intro s hs
    rw [show Z s = gaussianCompletedHeckeL χ s from rfl,
      gaussianCompletedHeckeL_eq_completedHeckeL χ s hs, ← hSeries ⟨s, hs⟩]
  have hNearTwo : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hOrd : meromorphicOrderAt (Z - H) (2 : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr
      ((hNearTwo.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ sub_eq_zero.mpr (hAgree s hs))
  have hEq (s : ℂ) : Z s = H s := by
    have h := (hZ.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hOrd
    have hNear : Z =ᶠ[𝓝[≠] s] H :=
      (meromorphicOrderAt_eq_top_iff.mp h).mono fun _ hz ↦ sub_eq_zero.mp hz
    have he := (hZ (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))
    exact (he.mp hNear).eq_of_nhds
  have hScale : Λ = fun s ↦ k⁻¹ * Z s := by
    funext s
    rw [hEq s]
    change Λ s = k⁻¹ * (k * Λ s)
    rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  rw [hScale]
  exact (globalIdelicZFunction_isBigO_one f χ a b).const_mul_left _

end TateBound

section HeckeDiscBound

open IsDedekindDomain Metric

/-- The finite Hecke product on a line to the right of one is bounded below by
the reciprocal norm of the Dedekind zeta value on the real axis. -/
private theorem finiteHeckeL_disc_center_lower (χ : U[F]) (x : ℝ) (hx : 1 < x)
    (s : halfPlane) (hs : (s : ℂ).re = x) :
    1 ≤ ‖finiteHeckeL χ s‖ * ‖dedekindZeta F (x : ℂ)‖ := by
  classical
  have hp := ((finiteHeckeL_hasProd χ s).mul
    (dedekindZeta_hasProd F (s := (x : ℂ)) (by simpa using hx))).norm
  rw [norm_mul] at hp
  apply ge_of_tendsto' hp
  intro T
  rw [norm_prod]
  refine Finset.one_le_prod₀ fun v _ ↦ ?_
  let q : ℝ := v.asIdeal.absNorm
  let b := q ^ (-x)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hb : 0 ≤ b := Real.rpow_nonneg (zero_lt_one.trans hq).le _
  have hb₁ : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hzb : (1 - (v.asIdeal.absNorm : ℂ) ^ (-(x : ℂ))) = ((1 - b : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, show (v.asIdeal.absNorm : ℂ) = (q : ℂ) by
      exact (Complex.ofReal_natCast _).symm, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (zero_lt_one.trans hq).le]
  rw [norm_mul, hzb, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr hb₁), finiteHeckeEulerFactor]
  split_ifs
  · let u := (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))
    change 1 ≤ ‖(1 - u)⁻¹‖ * (1 - b)⁻¹
    have hu : ‖u‖ = b := by
      dsimp only [u, b]
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re, hs]
    have hne : 1 - u ≠ 0 := fun h ↦ hb₁.ne (by rw [← hu, ← sub_eq_zero.mp h, norm_one])
    rw [norm_inv, ← mul_inv]
    apply (one_le_inv₀ (mul_pos (norm_pos_iff.mpr hne) (sub_pos.mpr hb₁))).2
    have htriangle := norm_sub_le (1 : ℂ) u
    rw [norm_one, hu] at htriangle
    exact (mul_le_mul_of_nonneg_right htriangle (sub_nonneg.mpr hb₁.le)).trans (by nlinarith)
  · rw [norm_one, one_mul]
    exact (one_le_inv₀ (sub_pos.mpr hb₁)).2 (sub_le_self _ hb)

/-- On any disc of fixed radius centred on a line to the right of one, the ratio of
the completed continuation to its value at the centre grows at most exponentially
at large absolute heights. -/
theorem completedHeckeL_continuation_disc_bound (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (x r : ℝ) (hx : 1 < x) (hr : 0 ≤ r) :
    ∃ C > (0 : ℝ), ∀ᶠ t : ℝ in comap abs atTop,
      L ⟨x, t⟩ ≠ 0 ∧
        ∀ u ∈ closedBall (⟨x, t⟩ : ℂ) r, ‖L u / L ⟨x, t⟩‖ ≤ Real.exp (C * (1 + |t|)) := by
  obtain ⟨M, hM⟩ := Asymptotics.isBigO_iff.mp
    (completedHeckeL_continuation_isBigO_one χ L hL hAgree (x - r - 1) (x + r + 1) (by linarith))
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hM
  obtain ⟨T₁, hT₁⟩ := hM
  obtain ⟨B, hB, hGamma⟩ := inv_heckeGammaFactor_isBigO_exp χ (x - 1) (x + 1)
  obtain ⟨N, hN⟩ := Asymptotics.isBigO_iff.mp hGamma
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hN
  obtain ⟨T₂, hT₂⟩ := hN
  let Z := ‖dedekindZeta F (x : ℂ)‖
  let E := max (M * N * Z) 1
  have hE : 1 ≤ E := le_max_right _ _
  let C := B + Real.log E
  have hC : 0 < C := add_pos_of_pos_of_nonneg hB (Real.log_nonneg hE)
  refine ⟨C, hC, ?_⟩
  filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (max (T₁ + r) T₂))] with t ht
  change max (T₁ + r) T₂ ≤ |t| at ht
  let z : ℂ := ⟨x, t⟩
  let w : halfPlane := ⟨z, hx⟩
  have hZ : 1 ≤ ‖finiteHeckeL χ w‖ * Z := finiteHeckeL_disc_center_lower χ x hx w rfl
  have hn : finiteHeckeL χ w ≠ 0 := by
    intro hzero
    norm_num [hzero] at hZ
  have hg : heckeGammaFactor χ z ≠ 0 := heckeGammaFactor_ne_zero_of_re_pos _ (zero_lt_one.trans hx)
  have hEq : L z = heckeGammaFactor χ z * finiteHeckeL χ w := hAgree w
  refine ⟨by rw [hEq]; exact mul_ne_zero hg hn, fun u hu ↦ ?_⟩
  change ‖L u / L z‖ ≤ _
  rw [mem_closedBall, Complex.dist_eq] at hu
  have hr' : |u.re - x| ≤ r := by
    have hh := Complex.abs_re_le_norm (u - z)
    rw [Complex.sub_re] at hh
    exact hh.trans hu
  have hi' : |u.im - t| ≤ r := by
    have hh := Complex.abs_im_le_norm (u - z)
    rw [Complex.sub_im] at hh
    exact hh.trans hu
  have hTU : T₁ ≤ |u.im| := by
    have := abs_sub_abs_le_abs_sub t u.im
    rw [abs_sub_comm t u.im] at this
    linarith [le_trans (le_max_left (T₁ + r) T₂) ht]
  have hU := hT₁ _ hTU u rfl (show u.re ∈ Icc (x - r - 1) (x + r + 1) by
    have hh := abs_le.mp hr'
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩)
  have hNZ := hT₂ _ ((le_max_right (T₁ + r) T₂).trans ht) z rfl
    (show z.re ∈ Icc (x - 1) (x + 1) by constructor <;> dsimp [z] <;> linarith)
  simp only [norm_one, mul_one] at hU
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hNZ
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans hU
  have hFin : ‖(finiteHeckeL χ w)⁻¹‖ ≤ Z := by
    rw [norm_inv, ← one_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hn)).mpr (by simpa [mul_comm] using hZ)
  rw [div_eq_mul_inv, hEq, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ M * (Z * (N * Real.exp (B * |t|))) := by
      exact mul_le_mul hU (mul_le_mul hFin hNZ (norm_nonneg _) (norm_nonneg _))
        (by positivity) hM₀
    _ = (M * N * Z) * Real.exp (B * |t|) := by ring
    _ ≤ E * Real.exp (B * |t|) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ = Real.exp (Real.log E + B * |t|) := by
      rw [Real.exp_add, Real.exp_log (zero_lt_one.trans_le hE)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (Real.log_nonneg hE) (abs_nonneg t)
      dsimp [C]
      nlinarith

end HeckeDiscBound

/-- A preliminary exponential bound for the finite continuation on a fixed strip.
Tate's split zeta integral gives boundedness of the completed function at large height, and
reciprocal gamma factors cost at most an exponential in the absolute height. -/
theorem finiteHeckeL_continuation_isBigO_exp (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ B : ℝ, 0 < B ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ Real.exp (B * |s.im|) := by
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let H := Λ * R
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun s hs ↦
    (hΛ hs).meromorphicAt.mul (hR.analyticAt s).meromorphicAt
  have hAtTwo : meromorphicOrderAt (L - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with s hs
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs)
    change L s - Λ s * (heckeGammaFactor χ s)⁻¹ = 0
    rw [hSeries ⟨s, hs⟩, hΛSeries ⟨s, hs⟩, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ s), mul_assoc, mul_inv_cancel₀ hne, mul_one, sub_self]
  have hAnalytic : ∀ᶠ s in atHeight, AnalyticAt ℂ Λ s := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨_, _, _, ha⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ Λ hΛ hΛSeries hχ
      filter_upwards [tendsto_comap.eventually_gt_atTop |t|] with s hs
      apply ha
      have hp : s ≠ Complex.I * (t : ℂ) := by
        rintro rfl
        simp at hs
      have hq : s ≠ 1 + Complex.I * (t : ℂ) := by
        rintro rfl
        simp at hs
      simp [hp, hq]
    · exact Eventually.of_forall (completedHeckeL_continuation_entire χ Λ hΛ hΛSeries hχ).analyticAt
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)
  have hAgree : L =ᶠ[l] H := by
    filter_upwards [hAnalytic.filter_mono (show l ≤ atHeight from inf_le_left)] with s hs
    have ho := (hL.meromorphicOn.sub hH).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
    have he : L =ᶠ[𝓝[≠] s] H := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun z hz ↦
      sub_eq_zero.mp hz
    exact (((hL (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hs.mul (hR.analyticAt s)).meromorphicNFAt).mp he).eq_of_nhds
  obtain ⟨B, hB, hΓ⟩ := inv_heckeGammaFactor_isBigO_exp χ a b
  refine ⟨B, hB, ?_⟩
  have hBound := (completedHeckeL_continuation_isBigO_one χ Λ hΛ hΛSeries a b hab).mul hΓ
  have hHO : H =O[l] fun s ↦ Real.exp (B * |s.im|) := by
    change (fun s ↦ Λ s * (heckeGammaFactor χ s)⁻¹) =O[l] _
    simpa only [one_mul] using hBound
  exact hHO.congr' hAgree.symm EventuallyEq.rfl

/-- A finite Hecke continuation is nonzero somewhere because its Dirichlet
series tends to its first coefficient, one, along the positive real axis. -/
private theorem finiteHeckeL_continuation_exists_ne_zero (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) : ∃ s, L s ≠ 0 := by
  let ψ := ideleClassNormTwist χ 0
  have hCoeff : ψ.LFunction 1 = 1 := by
    have hLocal (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ψ.localEulerFactor v 1 = 1 := by
      simp [NumberField.HeckeCharacter.localEulerFactor, NumberField.HeckeCharacter.localPowerSeries,
        ArithmeticFunction.ofPowerSeries_apply_one, PowerSeries.constantCoeff_invOfUnit]
    obtain ⟨S, hS⟩ := (heckeLocalEulerFactor_eventually_prod_eq ψ 1).exists
    rw [← hS]
    clear hS
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
        rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply_one, hLocal, ih, one_mul]
  have hAbscissa : LSeries.abscissaOfAbsConv ψ.LFunction < ⊤ :=
    (finiteHeckeL_seriesSummable χ ⟨2, by change 1 < (2 : ℂ).re; norm_num⟩).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  have hLimit : Tendsto (fun t : ℝ ↦ L (t : ℂ)) atTop (𝓝 1) := by
    rw [← hCoeff]
    apply (LSeries.tendsto_atTop hAbscissa).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    exact (hSeries ⟨(t : ℂ), by change 1 < (t : ℂ).re; simpa using ht⟩).symm
  by_contra! h
  exact one_ne_zero (tendsto_nhds_unique_of_eventuallyEq hLimit tendsto_const_nhds
    (Eventually.of_forall fun t ↦ h (t : ℂ)))

/-- Paper: Equation (B.1.1.11), p. 590. The modulus of the completed functional equation's
epsilon factor is unchanged by imaginary translation. In Tate's local factorization the
archimedean phases have constant modulus and the finite norm powers have positive real bases. -/
private theorem completedHeckeL_continuation_epsilon_norm
    (χ : U[F]) (Λ Λdual ε : ℂ → ℂ)
    (hΛ : MeromorphicNFOn Λ univ) (hSeries : ∀ s : halfPlane, Λ s = completedHeckeL χ s)
    (hΛdual : MeromorphicNFOn Λdual univ)
    (hDualSeries : ∀ s : halfPlane, Λdual s = completedHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hε₀ : ∀ s, ε s ≠ 0)
    (hEq : ∀ s, Λdual (1 - s) = ε s * Λ s) (s : ℂ) (t : ℝ) :
    ‖ε (s + (t : ℂ) * Complex.I)‖ = ‖ε s‖ := by
  obtain ⟨fArch, fArchDual, c, hc, hFourier, hArch, hArchDual⟩ :=
    exists_archimedeanHeckeTest_fourier χ
  obtain ⟨f, a, b, q, ha, hb, hq, hf, hfDual⟩ :=
    exists_globalHeckeTest_fourier χ fArch fArchDual c hc hFourier
  let B (z : ℂ) := b * (q : ℂ) ^ z
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (z : ℂ) : B z ≠ 0 := mul_ne_zero hb (Complex.cpow_ne_zero_iff.mpr (Or.inl hq₀))
  let Z (z : ℂ) := globalIdelicZFunction (adeleSchwartzFourier f) (ideleClassNormTwist χ⁻¹ z)
  have hZ := globalIdelicZFunction_meromorphic (adeleSchwartzFourier f) χ⁻¹
  have hProd : MeromorphicNFOn (B * Λdual) univ := fun z hz ↦
    (meromorphicNFAt_mul_iff_right (hB.analyticAt z) (hB₀ z)).mpr (hΛdual hz)
  have hNear : ∀ᶠ z in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  -- Continue the Fourier-transformed integral from the half-plane of convergence.
  have hOrd : meromorphicOrderAt (Z - B * Λdual) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds] with z hz
    apply sub_eq_zero.mpr
    change globalIdelicZFunction _ _ = B z * Λdual z
    rw [globalIdelicZFunction_eq_integral _ (twist_mem_rightHalfPlane χ⁻¹ z hz),
      hfDual ⟨z, hz⟩, hArchDual ⟨z, hz⟩, hDualSeries ⟨z, hz⟩]
    rfl
  have hZeq (z : ℂ) : Z z = B z * Λdual z := by
    have h := (hZ.meromorphicOn.sub hProd.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) hOrd
    have he : Z =ᶠ[𝓝[≠] z] B * Λdual :=
      (meromorphicOrderAt_eq_top_iff.mp h).mono fun _ hz ↦ sub_eq_zero.mp hz
    exact (((hZ (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hProd (mem_univ z))).mp he).eq_of_nhds
  have hDual (z : ℂ) : dualQuasiCharacter (G := IdeleClassGroup (𝓞 F) F)
      (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous (ideleClassNormTwist χ z) =
      ideleClassNormTwist χ⁻¹ (1 - z) := by
    ext1 g
    let N : ℂ := (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ)
    have hN : N ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    change N * ideleClassNormTwist χ z g⁻¹ = _
    rw [map_inv]
    change N * ((χ g : ℂ) * N ^ z)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1 - z)
    rw [mul_inv_rev, Complex.cpow_sub _ _ hN, Complex.cpow_one, div_eq_mul_inv]
    ac_rfl
  -- Cancel the completed L-function near 2 and extend the resulting entire identity.
  obtain ⟨z₀, hz₀⟩ := finiteHeckeL_continuation_exists_ne_zero χ
    (fun z ↦ Λ z / heckeGammaFactor χ z) (fun z ↦ by
      rw [hSeries z, completedHeckeL, mul_div_cancel_left₀ _
        (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property))]
      rfl)
  have hNotTop : meromorphicOrderAt Λ 2 ≠ ⊤ := by
    intro h
    have h₀ := hΛ.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
      (mem_univ (2 : ℂ)) (mem_univ z₀) h
    have hn : Λ z₀ ≠ 0 := fun he ↦ hz₀ (by simp [he])
    rw [(hΛ (mem_univ z₀)).meromorphicOrderAt_eq_zero_iff.mpr hn] at h₀
    exact WithTop.zero_ne_top h₀
  have hConst : (fun z ↦ B (1 - z) * ε z) = fun _ ↦ a := by
    apply AnalyticOnNhd.eq_of_frequently_eq (z₀ := 2)
    · exact fun z _ ↦ ((hB.analyticAt (1 - z)).comp (analyticAt_const.sub analyticAt_id)).mul
        (hε.analyticAt z)
    · exact fun _ _ ↦ analyticAt_const
    apply Eventually.frequently
    filter_upwards [hNear.filter_mono nhdsWithin_le_nhds,
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hΛ (mem_univ _)).meromorphicAt).mp hNotTop]
      with z hz hne
    have he := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ z)
    rw [hDual] at he
    change globalIdelicZFunction f (ideleClassNormTwist χ z) = Z (1 - z) at he
    rw [globalIdelicZFunction_eq_integral _ (twist_mem_rightHalfPlane χ z hz), hf ⟨z, hz⟩,
      hArch ⟨z, hz⟩, hZeq, hEq] at he
    change a * completedHeckeL χ ⟨z, hz⟩ = B (1 - z) * (ε z * Λ z) at he
    rw [← hSeries ⟨z, hz⟩, ← mul_assoc] at he
    exact mul_right_cancel₀ hne he.symm
  have hNorm (z : ℂ) : ‖a / ε z‖ = ‖b‖ * q ^ (1 - z.re) := by
    rw [(div_eq_iff (hε₀ z)).mpr (congrFun hConst z).symm]
    simp only [B, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.sub_re, Complex.one_re]
  apply inv_injective
  apply mul_left_cancel₀ (norm_ne_zero_iff.mpr ha)
  change ‖a‖ / ‖ε (s + (t : ℂ) * Complex.I)‖ = ‖a‖ / ‖ε s‖
  rw [← norm_div, ← norm_div, hNorm, hNorm]
  simp [Complex.add_re, Complex.mul_re]

/-- Paper: Equation (B.1.1.11), p. 590. The finite functional equation has a
multiplier given by the archimedean gamma ratio and a nonzero constant times a
real-scale exponential. Deviation: The conductor and phase are absorbed into
the real exponent coefficient and the nonzero constant. -/
private theorem finiteHeckeL_functionalEquation_conductorScale (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s) :
    ∃ (c : ℂ) (r : ℝ), c ≠ 0 ∧
      L =ᶠ[codiscreteWithin univ] fun s ↦
        (c * Complex.exp ((r : ℂ) * s) *
          toMeromorphicNFOn (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z)
            univ s) * Ldual (1 - s) := by
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  obtain ⟨Λdual, hΛdual, hΛdualSeries⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨ε, hε, hε₀, hEq⟩ :=
    completedHeckeL_continuation_functionalEquation χ Λ Λdual hΛ hΛSeries hΛdual hΛdualSeries
  have hNorm := completedHeckeL_continuation_epsilon_norm χ Λ Λdual ε
    hΛ hΛSeries hΛdual hΛdualSeries hε hε₀ hEq
  obtain ⟨r, hr⟩ := exists_eq_const_mul_exp_of_norm_add_mul_I (f := fun s ↦ (ε s)⁻¹) (hε.inv hε₀)
    (fun s ↦ inv_ne_zero (hε₀ s)) (fun s t ↦ by simp only [norm_inv, hNorm s t])
  have hContinue {f g : ℂ → ℂ} (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ)
      (h : ∀ s : halfPlane, f s = g s) (s : ℂ) : f =ᶠ[𝓝[≠] s] g := by
    have hTwo : meromorphicOrderAt (f - g) (2 : ℂ) = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
      exact sub_eq_zero.mpr (h ⟨z, hz⟩)
    exact (meromorphicOrderAt_eq_top_iff.mp
      ((hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
        (mem_univ (2 : ℂ)) (mem_univ s) hTwo)).mono fun _ hz ↦ sub_eq_zero.mp hz
  have hInv := differentiable_inv_heckeGammaFactor χ
  have hFinite (s : ℂ) : L =ᶠ[𝓝[≠] s] fun z ↦ Λ z * (heckeGammaFactor χ z)⁻¹ := by
    refine hContinue hL.meromorphicOn (fun z hz ↦
      (hΛ hz).meromorphicAt.mul (hInv.analyticAt z).meromorphicAt) (fun z ↦ ?_) s
    change L z = Λ z * (heckeGammaFactor χ z)⁻¹
    rw [hSeries z, hΛSeries z, completedHeckeL, finiteHeckeL,
      mul_comm (heckeGammaFactor χ (z : ℂ)), mul_assoc,
      mul_inv_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans z.property)), mul_one]
  have hGammaDual := meromorphic_heckeGammaFactor χ⁻¹
  have hCompletedDual (s : ℂ) :
      Λdual =ᶠ[𝓝[≠] s] fun z ↦ heckeGammaFactor χ⁻¹ z * Ldual z := by
    refine hContinue hΛdual.meromorphicOn (fun z hz ↦
      (hGammaDual z).mul (hLdual hz).meromorphicAt) (fun z ↦ ?_) s
    change Λdual z = heckeGammaFactor χ⁻¹ z * Ldual z
    rw [hΛdualSeries z, hDualSeries z, completedHeckeL, finiteHeckeL]
  let G (z : ℂ) := heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z
  have hG : MeromorphicOn G univ := fun s _ ↦
    ((hGammaDual (1 - s)).comp_analyticAt (analyticAt_const.sub analyticAt_id)).div
      (meromorphic_heckeGammaFactor χ s)
  have hNF := toMeromorphicNFOn_eqOn_codiscrete hG
  refine ⟨(ε 0)⁻¹, r, inv_ne_zero (hε₀ 0), ?_⟩
  apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
  intro s
  have hReflect : Tendsto (fun z : ℂ ↦ 1 - z) (𝓝[≠] s) (𝓝[≠] (1 - s)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (s := ({s} : Set ℂ)ᶜ)] with z hz
      simpa using hz
  filter_upwards [hFinite s, hReflect.eventually (hCompletedDual (1 - s)),
    hNF.filter_mono (nhdsNE_le_codiscrete s)] with z hLeft hRight hGamma
  change Λdual (1 - z) = heckeGammaFactor χ⁻¹ (1 - z) * Ldual (1 - z) at hRight
  have hUnscale : Λ z = (ε z)⁻¹ * Λdual (1 - z) := by
    rw [hEq z, ← mul_assoc, inv_mul_cancel₀ (hε₀ z), one_mul]
  change L z = ((ε 0)⁻¹ * Complex.exp ((r : ℂ) * z) * toMeromorphicNFOn G univ z) * Ldual (1 - z)
  rw [hLeft, hUnscale, hRight, ← hr z, ← hGamma]
  dsimp only [G]
  rw [div_eq_mul_inv]
  ac_rfl

/-- At twist zero, restriction of the inverse unitary character gives reciprocal values. -/
private theorem infinitePlaceRestriction_inv_twist_zero (χ : U[F]) (v : InfinitePlace F)
    (x : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
      (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero, mul_one]
  rfl

/-- Inversion negates the real place's radial exponent and preserves its sign parity. -/
private theorem realHeckeCharacter_parameters_inv (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(realHeckeCharacter_parameters χ v hv).exists.choose.1,
        (realHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inv_twist_zero, ha.2 x, mul_inv, Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

/-- Inversion negates both the radial exponent and the angular weight at a complex place. -/
private theorem complexHeckeCharacter_parameters_inv (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(complexHeckeCharacter_parameters χ v hv).exists.choose.1,
        -(complexHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ v hv).unique
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inv_twist_zero, ha.2 x, mul_inv, Complex.cpow_neg, zpow_neg]

/-- Each application of the Deligne gamma recurrence costs at most one power of the
height on a fixed vertical line. The step is two for `Gammaℝ` and one for `Gammaℂ`. -/
private theorem gamma_shift_isBigO (G : ℂ → ℂ) (d : ℕ)
    (hStep : ∀ z : ℂ, z ≠ 0 → G (z + (d : ℂ)) = G z * z / 2 / Real.pi)
    (σ : ℝ) (a : ℂ) (m : ℕ) :
    (fun s ↦ G (s + a + (m : ℂ) * d) / G (s + a))
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ m := by
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) l atTop := tendsto_inf_left tendsto_comap
  have hRe : ∀ᶠ s : ℂ in l, s.re = σ :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  change _ =O[l] _
  induction m with
  | zero =>
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s ↦ ?_)
    simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, norm_one, one_mul, norm_div]
    exact div_self_le_one _
  | succ m ih =>
    let b : ℂ := a + (m : ℂ) * d
    have hFactor : (fun s : ℂ ↦ (s + b) / 2 / Real.pi) =O[l] fun s ↦ |s.im| := by
      refine Asymptotics.IsBigO.of_bound (1 + |σ| + ‖b‖) ?_
      filter_upwards [hRe, hHeight.eventually_ge_atTop (1 : ℝ)] with s hs ht
      rw [Real.norm_of_nonneg (abs_nonneg _), norm_div, norm_div, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      calc
        _ ≤ ‖s + b‖ := (div_le_self (by positivity) (by linarith [Real.one_le_pi_div_two])).trans
          (div_le_self (norm_nonneg _) (by norm_num))
        _ ≤ ‖s‖ + ‖b‖ := norm_add_le _ _
        _ ≤ |s.im| + (|σ| + ‖b‖) := by
          rw [← hs]
          linarith [Complex.norm_le_abs_re_add_abs_im s]
        _ ≤ |s.im| + (|σ| + ‖b‖) * |s.im| :=
          add_le_add (le_refl _) (le_mul_of_one_le_right
            (add_nonneg (abs_nonneg σ) (norm_nonneg b)) ht)
        _ = _ := by ring
    refine (ih.mul hFactor).congr' ?_ (Eventually.of_forall fun s ↦ (pow_succ _ _).symm)
    filter_upwards [hHeight.eventually_ge_atTop (|b.im| + 1)] with s ht
    have hne : s + b ≠ 0 := by
      intro hz
      have hz' : s.im = -b.im := by
        simpa [Complex.add_im, eq_neg_iff_add_eq_zero] using congrArg Complex.im hz
      rw [hz', abs_neg] at ht
      linarith
    have hOld : s + a + (m : ℂ) * d = s + b := by dsimp [b]; ring
    have hNew : s + a + ((m + 1 : ℕ) : ℂ) * d = s + b + (d : ℂ) := by
      push_cast
      dsimp [b]
      ring
    simp only [hOld, hNew, hStep _ hne]
    ring

/-- Paper: Equations (B.1.1.7)–(B.1.1.11), p. 590. On a negative half-integer line,
the norm of each reflected gamma quotient is the norm of an integer-shift quotient
by conjugation. Multiplying the recurrence bounds gives a polynomial bound. -/
private theorem heckeGammaRatio_isBigO_on_neg_halfInteger_line (χ : U[F]) (k : ℕ) :
    ∃ n : ℕ, (fun s ↦ heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s)
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {-(k : ℝ) - 1 / 2})] fun s ↦ |s.im| ^ n := by
  classical
  let σ : ℝ := -(k : ℝ) - 1 / 2
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  let m : InfinitePlace F → ℕ := fun v ↦ if v.IsReal then k + 1 else 2 * (k + 1)
  let γ (ψ : U[F]) (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters ψ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters ψ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  have hShift {a : ℂ} (ha : a.re = 0) (b : ℝ) {s : ℂ} (hs : s.re = σ) :
      conj (1 - s + -a + (b : ℂ)) = s + (a + (b : ℂ)) + (2 * ((k : ℂ) + 1)) := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, ha, hs, σ]; ring
  have hLocal (v : InfinitePlace F) :
      (fun s ↦ γ χ⁻¹ v (1 - s) / γ χ v s) =O[l] fun s ↦ |s.im| ^ m v := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      have ha : a.1.re = 0 := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
      have h := gamma_shift_isBigO Complex.Gammaℝ 2
        (fun _ hz ↦ Complex.Gammaℝ_add_two hz) σ (a.1 + (a.2.val : ℂ)) (k + 1)
      rw [show m v = k + 1 by simp [m, hv]]
      apply Asymptotics.IsBigO.of_norm_left
      refine h.norm_left.congr' (eventually_inf_principal.mpr (Eventually.of_forall ?_))
        EventuallyEq.rfl
      intro s hs
      change s.re = σ at hs
      simp only [γ, dite_eq_left hv, realHeckeCharacter_parameters_inv, norm_div]
      change ‖Complex.Gammaℝ (s + (a.1 + (a.2.val : ℂ)) + ↑(k + 1) * 2)‖ /
          ‖Complex.Gammaℝ (s + (a.1 + (a.2.val : ℂ)))‖ =
        ‖Complex.Gammaℝ (1 - s + -a.1 + (a.2.val : ℂ))‖ /
          ‖Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))‖
      rw [← add_assoc s, ← Complex.norm_conj (Complex.Gammaℝ (1 - s + -a.1 + (a.2.val : ℂ))),
        ← Complex.Gammaℝ_conj, ← Complex.ofReal_natCast, hShift ha _ hs]
      push_cast
      ring_nf
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
      have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
      have h := gamma_shift_isBigO Complex.Gammaℂ 1
        (fun _ hz ↦ by simpa only [Nat.cast_one] using Complex.Gammaℂ_add_one hz) σ (a.1 + (a.2.natAbs : ℂ) / 2) (2 * (k + 1))
      rw [show m v = 2 * (k + 1) by simp [m, hv]]
      apply Asymptotics.IsBigO.of_norm_left
      refine h.norm_left.congr' (eventually_inf_principal.mpr (Eventually.of_forall ?_))
        EventuallyEq.rfl
      intro s hs
      change s.re = σ at hs
      simp only [γ, dite_eq_right hv, complexHeckeCharacter_parameters_inv, Int.natAbs_neg,
        div_div_div_cancel_right₀ (two_ne_zero' ℂ), norm_div, Nat.cast_one]
      change ‖Complex.Gammaℂ (s + (a.1 + (a.2.natAbs : ℂ) / 2) + ↑(2 * (k + 1)) * 1)‖ /
          ‖Complex.Gammaℂ (s + (a.1 + (a.2.natAbs : ℂ) / 2))‖ =
        ‖Complex.Gammaℂ (1 - s + -a.1 + (a.2.natAbs : ℂ) / 2)‖ /
          ‖Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2)‖
      rw [← add_assoc s, ← Complex.norm_conj (Complex.Gammaℂ (1 - s + -a.1 + (a.2.natAbs : ℂ) / 2)),
        ← Complex.Gammaℂ_conj]
      rw [show (↑a.2.natAbs : ℂ) / 2 = (((a.2.natAbs : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl,
        hShift ha _ hs]
      push_cast
      ring_nf
  refine ⟨∑ v, m v, ?_⟩
  convert (Asymptotics.IsBigO.finsetProd (s := Finset.univ)
    (fun v _ ↦ hLocal v)) using 1
  · funext s
    change (∏ v, γ χ⁻¹ v (1 - s)) / (∏ v, γ χ v s) = ∏ v, γ χ⁻¹ v (1 - s) / γ χ v s
    exact (Finset.prod_div_distrib _ _).symm
  · funext s
    exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

/-- Paper: Equations (B.1.1.9)–(B.1.1.11), p. 590. On each negative half-integer line,
the explicit functional equation bounds the finite continuation by a power of the height.
The conductor factor has constant norm on that line, and the reflected series is absolutely
convergent. After conjugation the two gamma arguments differ by `k + 1` at real places and
`2 * (k + 1)` at complex places, so their quotients reduce in norm to finite products. -/
theorem finiteHeckeL_continuation_isBigO_pow_on_neg_halfInteger_line
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (k : ℕ) :
    ∃ n : ℕ, 0 < n ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {-(k : ℝ) - 1 / 2})]
      fun s ↦ |s.im| ^ n := by
  let σ : ℝ := -(k : ℝ) - 1 / 2
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  let G (s : ℂ) := heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s
  have hσ : σ < 0 := by
    dsimp [σ]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hLine : ∀ᶠ s : ℂ in l, s.re = σ :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  obtain ⟨Ldual, hDual, hDualSeries⟩ := finiteHeckeL_exists_continuation χ⁻¹
  obtain ⟨c, r, _, hEq⟩ :=
    finiteHeckeL_functionalEquation_conductorScale χ L Ldual hL hSeries hDual hDualSeries
  let E (s : ℂ) := c * Complex.exp ((r : ℂ) * s)
  have hReflection (s : ℂ) : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s :=
    analyticAt_const.sub analyticAt_id
  have hGMero : MeromorphicOn G univ := by
    intro s _
    simpa only [G, div_eq_mul_inv, Function.comp_apply] using
      (((meromorphic_heckeGammaFactor χ⁻¹ (1 - s)).comp_analyticAt (hReflection s)).fun_mul
        ((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicAt)
  have hEqRaw : L =ᶠ[codiscreteWithin univ] fun s ↦ (E s * G s) * Ldual (1 - s) := by
    filter_upwards [hEq, toMeromorphicNFOn_eqOn_codiscrete hGMero] with s hs hG
    simpa only [G, E, ← hG] using hs
  -- The reflected series and the raw gamma quotient are analytic on this line.
  have hPoint {s : ℂ} (hs : s.re = σ) : L s = (E s * Ldual (1 - s)) * G s := by
    have hRe : 1 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re, hs]
      linarith
    let f := (ideleClassNormTwist χ⁻¹ 0).LFunction
    have hA : LSeries.abscissaOfAbsConv f < (1 - s).re := by
      obtain ⟨t, ht, ht'⟩ := exists_between hRe
      have htS := finiteHeckeL_seriesSummable χ⁻¹ ⟨(t : ℂ), by simpa using ht⟩
      exact htS.abscissaOfAbsConv_le.trans_lt
        (EReal.coe_lt_coe_iff.mpr (by simpa only [Complex.ofReal_re] using ht'))
    have hD : AnalyticAt ℂ Ldual (1 - s) := by
      refine (LSeries_analyticOnNhd f _ hA).congr ?_
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hRe]
        with z hz
      exact (hDualSeries ⟨z, hz⟩).symm
    have hNum : AnalyticAt ℂ (heckeGammaFactor χ⁻¹) (1 - s) := by
      simpa only [inv_inv] using
        (((differentiable_inv_heckeGammaFactor χ⁻¹).analyticAt (1 - s)).fun_inv
          (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (zero_lt_one.trans hRe))))
    have hG : AnalyticAt ℂ G s := by
      simpa only [G, div_eq_mul_inv, Function.comp_apply] using
        ((hNum.comp (hReflection s)).fun_mul ((differentiable_inv_heckeGammaFactor χ).analyticAt s))
    have hE : AnalyticAt ℂ E s := by dsimp [E]; fun_prop
    have hProduct : AnalyticAt ℂ (fun z ↦ (E z * G z) * Ldual (1 - z)) s :=
      (hE.mul hG).mul (hD.comp (hReflection s))
    have hNear := hEqRaw.filter_mono (nhdsNE_le_codiscrete s)
    have hAt := (((hL (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      hProduct.meromorphicNFAt).mp hNear).eq_of_nhds
    simpa only [mul_right_comm] using hAt
  obtain ⟨D, hD⟩ := finiteHeckeL_continuation_boundedOn_right χ⁻¹ Ldual hDualSeries
    (r := 1 - σ) (by linarith)
  have hBound : (fun s ↦ E s * Ldual (1 - s)) =O[l] fun _ ↦ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (‖c‖ * Real.exp (r * σ) * D) ?_
    filter_upwards [hLine] with s hs
    rw [norm_mul, show ‖E s‖ = ‖c‖ * Real.exp (r * σ) by
      simp [E, Complex.norm_exp, Complex.mul_re, hs], norm_one, mul_one]
    apply mul_le_mul_of_nonneg_left (hD _ ?_) (by positivity)
    simp [Complex.sub_re, hs]
  obtain ⟨n, hGamma⟩ := heckeGammaRatio_isBigO_on_neg_halfInteger_line χ k
  have hPoly : L =O[l] fun s ↦ |s.im| ^ n := by
    simpa only [one_mul] using (hBound.mul hGamma).congr'
      (hLine.mono fun _ hs ↦ (hPoint hs).symm) EventuallyEq.rfl
  refine ⟨n + 1, Nat.succ_pos _, hPoly.trans (Asymptotics.IsBigO.of_bound 1 ?_)⟩
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) l atTop := tendsto_inf_left tendsto_comap
  filter_upwards [hHeight.eventually_ge_atTop (1 : ℝ)] with s hs
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _),
    Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _), one_mul, pow_succ]
  exact le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) _) hs

/-- Paper: Lemma B.1.1.2, p. 590. The finite L-function of a unitary Hecke
character grows at most polynomially on each fixed closed vertical strip.
Deviation: `M` is chosen after the strip endpoints, as required even for ζ. -/
theorem finiteHeckeL_continuation_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-a)
  let l : ℝ := -(k : ℝ) - 1 / 2
  let u : ℝ := max b 2
  have hl : l ≤ a := by dsimp [l]; linarith
  have hu : b ≤ u := le_max_left _ _
  have hlu := hl.trans_lt (hab.trans_le hu)
  let strip (S : Set ℝ) := atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)
  have hFilter {S₁ S₂ : Set ℝ} (h : S₁ ⊆ S₂) : strip S₁ ≤ strip S₂ :=
    inf_le_inf_left _ (principal_mono.mpr (preimage_mono h))
  have hHeight {S : Set ℝ} : Tendsto (fun s : ℂ ↦ |s.im|) (strip S) atTop :=
    tendsto_inf_left tendsto_comap
  obtain ⟨G, hG, hGL⟩ := exists_analyticOnNhd_isTheta_finiteHeckeL_continuation χ L hL hSeries (l - 1)
  have hSub : Icc l u ⊆ Ioi (l - 1) := fun _ hs ↦
    (sub_lt_self l zero_lt_one).trans_le hs.1
  have hStrip := hFilter hSub
  have hLeftFilter : strip {l} ≤ strip (Ioi (l - 1)) :=
    hFilter (singleton_subset_iff.mpr (sub_lt_self l zero_lt_one))
  have hRightFilter : strip {u} ≤ strip (Ioi (l - 1)) :=
    hFilter (singleton_subset_iff.mpr ((sub_lt_self l zero_lt_one).trans hlu))
  obtain ⟨n, hn, hLeft⟩ := finiteHeckeL_continuation_isBigO_pow_on_neg_halfInteger_line χ L hL hSeries k
  have hLeftG : G =O[strip {l}] fun s ↦ |s.im| ^ n :=
    (hGL.isBigO.mono hLeftFilter).trans hLeft
  obtain ⟨C, hC⟩ := finiteHeckeL_continuation_boundedOn_right χ L hSeries
    (r := u) (one_lt_two.trans_le (le_max_right _ _))
  have hRightG : G =O[strip {u}] fun s ↦ |s.im| ^ n := by
    apply (hGL.isBigO.mono hRightFilter).trans
    refine Asymptotics.IsBigO.of_bound (max C 0) ?_
    have hLine : ∀ᶠ s in strip {u}, s.re = u :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
    filter_upwards [hLine, hHeight.eventually_ge_atTop (1 : ℝ)] with s hs ht
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact ((hC s hs.ge).trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right (le_max_right _ _) (one_le_pow₀ ht))
  obtain ⟨B, _, hExp⟩ := finiteHeckeL_continuation_isBigO_exp χ L hL hSeries l u hlu
  have hGPoly := isBigO_pow_verticalStrip_of_exp hlu
    (hG.differentiableOn.mono (preimage_mono hSub))
    ((hGL.isBigO.mono hStrip).trans hExp) hLeftG hRightG
  refine ⟨(n : ℝ), by exact_mod_cast hn, ?_⟩
  simpa only [Real.rpow_natCast] using ((hGL.symm.isBigO.mono hStrip).trans hGPoly).mono
    (hFilter (Icc_subset_Icc hl hu))

/-- Each application of the Deligne gamma recurrence in the denominator gains one inverse
power of the height, uniformly in the real part. The step is two for `Gammaℝ` and one for
`Gammaℂ`. -/
private theorem gamma_shift_inv_isBigO (G : ℂ → ℂ) (d : ℕ)
    (hStep : ∀ z : ℂ, z ≠ 0 → G (z + (d : ℂ)) = G z * z / 2 / Real.pi)
    (a : ℂ) (m : ℕ) :
    (fun s ↦ G (s + a) / G (s + a + (m : ℂ) * d)) =O[atHeight] fun s ↦ (|s.im| ^ m)⁻¹ := by
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) atHeight atTop := tendsto_comap
  induction m with
  | zero =>
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun s ↦ ?_)
    simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, inv_one, norm_one, one_mul, norm_div]
    exact div_self_le_one _
  | succ m ih =>
    let b : ℂ := a + (m : ℂ) * d
    have hFactor : (fun s : ℂ ↦ 2 * Real.pi / (s + b)) =O[atHeight] fun s ↦ |s.im|⁻¹ := by
      refine Asymptotics.IsBigO.of_bound (4 * Real.pi) ?_
      filter_upwards [hHeight.eventually_ge_atTop (2 * |b.im| + 1)] with s ht
      have hpos : 0 < |s.im| := by linarith [abs_nonneg b.im]
      have hlow : |s.im| / 2 ≤ ‖s + b‖ := by
        have h₁ := Complex.abs_im_le_norm (s + b)
        have h₂ := abs_sub_abs_le_abs_sub s.im (-b.im)
        rw [Complex.add_im] at h₁
        rw [abs_neg, sub_neg_eq_add] at h₂
        linarith
      rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, norm_inv, Real.norm_of_nonneg (abs_nonneg _),
        div_le_iff₀ (by linarith)]
      calc
        2 * Real.pi = 4 * Real.pi * |s.im|⁻¹ * (|s.im| / 2) := by
          field_simp
          ring
        _ ≤ 4 * Real.pi * |s.im|⁻¹ * ‖s + b‖ :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
    refine (ih.mul hFactor).congr' ?_ (Eventually.of_forall fun s ↦ ?_)
    · filter_upwards [hHeight.eventually_ge_atTop (|b.im| + 1)] with s ht
      have hne : s + b ≠ 0 := by
        intro hz
        have hz' : s.im = -b.im := by
          simpa [Complex.add_im, eq_neg_iff_add_eq_zero] using congrArg Complex.im hz
        rw [hz', abs_neg] at ht
        linarith
      have hOld : s + a + (m : ℂ) * d = s + b := by dsimp [b]; ring
      have hNew : s + a + ((m + 1 : ℕ) : ℂ) * d = s + b + (d : ℂ) := by
        push_cast
        dsimp [b]
        ring
      simp only [hOld, hNew, hStep _ hne]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    · simp only [pow_succ, mul_inv]

/-- A real archimedean gamma factor has no zero off the real axis. -/
private theorem Gammaℝ_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gammaℝ z ≠ 0 := by
  rw [Ne, Complex.Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  apply hz
  rw [hn]
  simp

/-- Away from the finitely many heights of its poles, the archimedean factor does not vanish,
with Mathlib's convention that a gamma function is zero at its poles. -/
private theorem heckeGammaFactor_eventually_ne_zero (χ : U[F]) :
    ∀ᶠ s : ℂ in atHeight, heckeGammaFactor χ s ≠ 0 := by
  classical
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) atHeight atTop := tendsto_comap
  unfold heckeGammaFactor
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const]
  rw [eventually_all]
  intro v
  by_cases hv : v.IsReal
  · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
    filter_upwards [hHeight.eventually_gt_atTop |a.1.im|] with s hs
    simp only [dite_eq_left hv]
    apply Gammaℝ_ne_zero_of_im_ne_zero
    change (s + a.1 + (a.2.val : ℂ)).im ≠ 0
    intro him
    have him' : s.im + a.1.im = 0 := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using him
    rw [eq_neg_of_add_eq_zero_left him', abs_neg] at hs
    exact lt_irrefl _ hs
  · let a := (complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
    filter_upwards [hHeight.eventually_gt_atTop |a.1.im|] with s hs
    simp only [dite_eq_right hv]
    change Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2 ≠ 0
    apply (div_ne_zero · two_ne_zero)
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
    have him : (s + a.1 + (a.2.natAbs : ℂ) / 2).im ≠ 0 := by
      intro him
      have him' : s.im + a.1.im = 0 := by
        simpa only [Complex.add_im, Complex.div_ofNat_im, Complex.natCast_im, zero_div,
          add_zero] using him
      rw [eq_neg_of_add_eq_zero_left him', abs_neg] at hs
      exact lt_irrefl _ hs
    exact mul_ne_zero (Gammaℝ_ne_zero_of_im_ne_zero him)
      (Gammaℝ_ne_zero_of_im_ne_zero (by simpa using him))

/-- Conjugating the argument and inverting the unitary character preserves the norm of the
archimedean factor: inversion negates the imaginary radial exponents, which is what
conjugation does to them, and keeps the real shifts. -/
private theorem norm_heckeGammaFactor_inv_conj (χ : U[F]) (s : ℂ) :
    ‖heckeGammaFactor χ⁻¹ (conj s)‖ = ‖heckeGammaFactor χ s‖ := by
  classical
  unfold heckeGammaFactor
  rw [norm_prod, norm_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have hconj {a : ℂ} (ha : a.re = 0) : conj a = -a := by
    apply Complex.ext <;> simp [ha]
  by_cases hv : v.IsReal
  · have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [dite_eq_left hv, realHeckeCharacter_parameters_inv]
    rw [← Complex.norm_conj (Complex.Gammaℝ _), ← Complex.Gammaℝ_conj]
    simp only [map_add, map_neg, Complex.conj_conj, hconj ha, neg_neg, Complex.conj_natCast]
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have ha := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    simp only [dite_eq_right hv, complexHeckeCharacter_parameters_inv, Int.natAbs_neg, norm_div]
    rw [← Complex.norm_conj (Complex.Gammaℂ _), ← Complex.Gammaℂ_conj]
    simp only [map_add, map_neg, Complex.conj_conj, hconj ha, neg_neg, Complex.conj_natCast,
      map_div₀, map_ofNat]

/-- A real archimedean gamma factor is bounded on each closed vertical strip inside the right
half-plane, by the gamma integral at the real part. -/
private theorem exists_norm_Gammaℝ_le {c d : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc c d → ‖Complex.Gammaℝ z‖ ≤ C := by
  have hCont : ContinuousOn (fun x : ℝ ↦ Real.Gamma (x / 2)) (Icc c d) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp (by fun_prop) fun x hx ↦
      show 0 < x / 2 from half_pos (hc.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  refine ⟨C, fun z hz ↦ ?_⟩
  have hz₀ : 0 < z.re := hc.trans_le hz.1
  have hPi : ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have hGamma : ‖Complex.Gamma (z / 2)‖ ≤ C := by
    have h := norm_Gamma_le_real_Gamma (z := z / 2) (by simpa using hz₀)
    rw [Complex.div_ofNat_re] at h
    exact h.trans ((le_abs_self _).trans (hC z.re hz))
  rw [Complex.Gammaℝ_def, norm_mul]
  exact (mul_le_mul hPi hGamma (norm_nonneg _) zero_le_one).trans_eq (one_mul C)

/-- The archimedean factor is bounded on each closed vertical strip inside the right
half-plane. A complex factor is handled as two real factors via the duplication formula. -/
private theorem exists_norm_heckeGammaFactor_le (χ : U[F]) {c d : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc c d → ‖heckeGammaFactor χ s‖ ≤ C := by
  classical
  have hLocal (v : InfinitePlace F) : ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc c d →
      ‖(if hv : v.IsReal then
        let a := (realHeckeCharacter_parameters χ v hv).exists.choose
        Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
      else
        let a := (complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
        Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2)‖ ≤ C := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
      obtain ⟨C, hC⟩ := exists_norm_Gammaℝ_le (c := c) (d := d + a.2.val) hc
      refine ⟨C, fun s hs ↦ ?_⟩
      simp only [dite_eq_left hv]
      apply hC
      rw [mem_Icc, Complex.add_re, Complex.add_re, Complex.natCast_re, ha, add_zero]
      exact ⟨by linarith [hs.1, Nat.cast_nonneg (α := ℝ) a.2.val], by linarith [hs.2]⟩
    · let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
      obtain ⟨C₁, hC₁⟩ := exists_norm_Gammaℝ_le (c := c) (d := d + a.2.natAbs / 2) hc
      obtain ⟨C₂, hC₂⟩ := exists_norm_Gammaℝ_le (c := c) (d := d + a.2.natAbs / 2 + 1) hc
      refine ⟨C₁ * C₂ / 2, fun s hs ↦ ?_⟩
      simp only [dite_eq_right hv]
      change ‖Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2‖ ≤ _
      have hRe : (s + a.1 + (a.2.natAbs : ℂ) / 2).re = s.re + (a.2.natAbs : ℝ) / 2 := by
        simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, add_zero]
      have hNonneg : (0 : ℝ) ≤ (a.2.natAbs : ℝ) / 2 := by positivity
      rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, norm_div, norm_mul, Complex.norm_two]
      apply div_le_div_of_nonneg_right _ zero_le_two
      have h₁ := hC₁ (s + a.1 + (a.2.natAbs : ℂ) / 2) (by
        rw [hRe]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      have h₂ := hC₂ (s + a.1 + (a.2.natAbs : ℂ) / 2 + 1) (by
        rw [Complex.add_re, hRe, Complex.one_re]
        exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      exact mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)
  choose C hC using hLocal
  refine ⟨∏ v, C v, fun s hs ↦ ?_⟩
  unfold heckeGammaFactor
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ hC v s hs

/-- Raising the argument of the archimedean factor by `2 * M` costs at most the height to the
power `[F : ℚ] * M` on a fixed vertical line: the recurrence is applied `M` times at a real
place and `2 * M` times at a complex one. -/
private theorem heckeGammaFactor_shift_isBigO (χ : U[F]) (σ : ℝ) (M : ℕ) :
    (fun s ↦ heckeGammaFactor χ (s + 2 * (M : ℂ)) / heckeGammaFactor χ s)
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (Module.finrank ℚ F * M) := by
  classical
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  let γ (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  have hLocal (v : InfinitePlace F) :
      (fun s ↦ γ v (s + 2 * (M : ℂ)) / γ v s) =O[l] fun s ↦ |s.im| ^ (v.mult * M) := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      have h := gamma_shift_isBigO Complex.Gammaℝ 2
        (fun _ hz ↦ Complex.Gammaℝ_add_two hz) σ (a.1 + (a.2.val : ℂ)) M
      rw [hv.mult_eq_one, one_mul]
      refine h.congr_left fun s ↦ ?_
      simp only [γ, a, dite_eq_left hv]
      congr 2 <;> push_cast <;> ring
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
      have h := gamma_shift_isBigO Complex.Gammaℂ 1
        (fun _ hz ↦ by simpa only [Nat.cast_one] using Complex.Gammaℂ_add_one hz) σ
        (a.1 + (a.2.natAbs : ℂ) / 2) (2 * M)
      rw [hv'.mult_eq_two]
      refine h.congr_left fun s ↦ ?_
      simp only [γ, a, dite_eq_right hv, div_div_div_cancel_right₀ (two_ne_zero' ℂ)]
      congr 2 <;> push_cast <;> ring
  convert Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ ↦ hLocal v) using 1
  · funext s
    change (∏ v, γ v (s + 2 * (M : ℂ))) / (∏ v, γ v s) = ∏ v, γ v (s + 2 * (M : ℂ)) / γ v s
    exact (Finset.prod_div_distrib _ _).symm
  · funext s
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, InfinitePlace.sum_mult_eq]

/-- Raising the argument of the archimedean factor in the denominator by `2 * K` gains the
height to the power `-[F : ℚ] * K`, uniformly in the real part. -/
private theorem heckeGammaFactor_shift_inv_isBigO (χ : U[F]) (K : ℕ) :
    (fun s ↦ heckeGammaFactor χ s / heckeGammaFactor χ (s + 2 * (K : ℂ)))
      =O[atHeight] fun s ↦ (|s.im| ^ (Module.finrank ℚ F * K))⁻¹ := by
  classical
  let γ (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  have hLocal (v : InfinitePlace F) :
      (fun s ↦ γ v s / γ v (s + 2 * (K : ℂ))) =O[atHeight]
        fun s ↦ (|s.im| ^ (v.mult * K))⁻¹ := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      have h := gamma_shift_inv_isBigO Complex.Gammaℝ 2
        (fun _ hz ↦ Complex.Gammaℝ_add_two hz) (a.1 + (a.2.val : ℂ)) K
      rw [hv.mult_eq_one, one_mul]
      refine h.congr_left fun s ↦ ?_
      simp only [γ, a, dite_eq_left hv]
      congr 2 <;> push_cast <;> ring
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
      have h := gamma_shift_inv_isBigO Complex.Gammaℂ 1
        (fun _ hz ↦ by simpa only [Nat.cast_one] using Complex.Gammaℂ_add_one hz)
        (a.1 + (a.2.natAbs : ℂ) / 2) (2 * K)
      rw [hv'.mult_eq_two]
      refine h.congr_left fun s ↦ ?_
      simp only [γ, a, dite_eq_right hv, div_div_div_cancel_right₀ (two_ne_zero' ℂ)]
      congr 2 <;> push_cast <;> ring
  convert Asymptotics.IsBigO.finsetProd (s := Finset.univ) (fun v _ ↦ hLocal v) using 1
  · funext s
    change (∏ v, γ v s) / (∏ v, γ v (s + 2 * (K : ℂ))) = ∏ v, γ v s / γ v (s + 2 * (K : ℂ))
    exact (Finset.prod_div_distrib _ _).symm
  · funext s
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul,
      InfinitePlace.sum_mult_eq]

/-- Paper: Equations (B.1.1.7)–(B.1.1.11), p. 590. Uniform Stirling estimates
at the real and complex places bound the normal form of the archimedean gamma
ratio by the height to the power `[F : ℚ] * (1 / 2 - Re(s))`. -/
private theorem heckeGammaRatio_isBigO_on_strip (χ : U[F]) (a b : ℝ) (hab : a < b) :
    toMeromorphicNFOn (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z) univ
      =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
        fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  -- Mathlib has no Stirling formula on vertical strips. The exponent is affine in the real
  -- part, so it is interpolated between the lines `Re s ∈ 1 / 2 + ℤ`, where conjugation turns
  -- the two gamma arguments into integer shifts of each other. Raising the numerator's
  -- argument by `2 * K` first makes the quotient holomorphic on the whole strip.
  let n := Module.finrank ℚ F
  obtain ⟨K, hK⟩ := exists_nat_ge (b - 1 / 2)
  obtain ⟨M, hMa⟩ := exists_nat_ge (1 / 2 + K - a)
  let u : ℝ := 1 / 2 + K - M
  let v : ℝ := 1 / 2 + K
  have hau : u ≤ a := by
    dsimp only [u]
    linarith
  have hbv : b ≤ v := by
    dsimp only [v]
    linarith
  have huv : u < v := hau.trans_lt (hab.trans_le hbv)
  have hvu : v - u = M := by simp [u, v]
  have hM : (0 : ℝ) < M := hvu ▸ sub_pos.mpr huv
  let strip (S : Set ℝ) := atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)
  have hHeight {S : Set ℝ} : Tendsto (fun s : ℂ ↦ |s.im|) (strip S) atTop :=
    tendsto_inf_left tendsto_comap
  have hReflect : Tendsto (fun s : ℂ ↦ 1 - s) atHeight atHeight := by
    refine tendsto_comap_iff.mpr ?_
    have : (abs ∘ Complex.im) ∘ (fun s : ℂ ↦ 1 - s) = abs ∘ Complex.im := by
      funext s
      simp
    rw [this]
    exact tendsto_comap
  let G (s : ℂ) := heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ s
  let H (s : ℂ) := heckeGammaFactor χ⁻¹ (1 - s + 2 * (K : ℂ)) * (heckeGammaFactor χ s)⁻¹
  have hInv := differentiable_inv_heckeGammaFactor χ
  have hNumRe (s : ℂ) : (1 - s + 2 * (K : ℂ)).re = 1 - s.re + 2 * K := by simp
  have hNumPos {s : ℂ} (hs : s.re ≤ v) : 0 < (1 - s + 2 * (K : ℂ)).re := by
    rw [hNumRe]
    dsimp only [v] at hs
    linarith [Nat.cast_nonneg (α := ℝ) K]
  -- The shifted quotient is holomorphic on the strip.
  have hHAnalytic {s : ℂ} (hs : s.re ≤ v) : AnalyticAt ℂ H s := by
    have hShift : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z + 2 * (K : ℂ)) s :=
      (analyticAt_const.sub analyticAt_id).add analyticAt_const
    have hNum : AnalyticAt ℂ (heckeGammaFactor χ⁻¹) (1 - s + 2 * (K : ℂ)) := by
      simpa only [inv_inv] using
        (((differentiable_inv_heckeGammaFactor χ⁻¹).analyticAt _).fun_inv
          (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (hNumPos hs))))
    simpa only [H, Function.comp_apply] using
      (hNum.comp (f := fun z : ℂ ↦ 1 - z + 2 * (K : ℂ)) hShift).fun_mul (hInv.analyticAt s)
  -- On the line `Re s = 1 / 2 + K - m` its norm is that of an integer-shift quotient.
  have hLine (m : ℕ) {s : ℂ} (hs : s.re = 1 / 2 + K - m) :
      ‖H s‖ = ‖heckeGammaFactor χ (s + 2 * (m : ℂ)) / heckeGammaFactor χ s‖ := by
    have hconj : conj (s + 2 * (m : ℂ)) = 1 - s + 2 * (K : ℂ) := by
      apply Complex.ext
      · simp only [Complex.conj_re, Complex.add_re, Complex.sub_re, Complex.one_re,
          Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
          Complex.natCast_im, mul_zero, sub_zero, hs]
        ring
      · simp
    change ‖_ * _‖ = _
    rw [norm_mul, norm_inv, norm_div, ← hconj, norm_heckeGammaFactor_inv_conj, div_eq_mul_inv]
  have hLeft : H =O[strip {u}] fun s ↦ |s.im| ^ (n * M) := by
    apply Asymptotics.IsBigO.of_norm_left
    refine (heckeGammaFactor_shift_isBigO χ u M).norm_left.congr'
      (eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ ?_)) EventuallyEq.rfl
    exact (hLine M hs).symm
  have hRightOne (s : ℂ) (hs : s.re = v) : ‖H s‖ ≤ 1 := by
    rw [hLine 0 (by simpa only [Nat.cast_zero, sub_zero] using hs)]
    simp only [Nat.cast_zero, mul_zero, add_zero, norm_div]
    exact div_self_le_one _
  have hRight : H =O[strip {v}] fun s ↦ |s.im| ^ (n * M) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [show ∀ᶠ s : ℂ in strip {v}, s.re = v from
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs),
      hHeight.eventually_ge_atTop (1 : ℝ)] with s hs ht
    rw [one_mul, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact (hRightOne s hs).trans (one_le_pow₀ ht)
  have hRight₀ : H =O[strip {v}] fun s ↦ |s.im| ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1
      (eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ ?_))
    simpa only [Real.rpow_zero, norm_one, mul_one] using hRightOne s hs
  -- A bounded numerator and the exponential bound for the reciprocal factor give the
  -- preliminary growth bound that Phragmén–Lindelöf needs.
  obtain ⟨C, hC⟩ := exists_norm_heckeGammaFactor_le χ⁻¹ (c := 1 / 2 + K) (d := 1 / 2 + K + M)
    (by positivity)
  obtain ⟨B, -, hΓ⟩ := inv_heckeGammaFactor_isBigO_exp χ u v
  have hNum : (fun s : ℂ ↦ heckeGammaFactor χ⁻¹ (1 - s + 2 * (K : ℂ)))
      =O[strip (Icc u v)] fun _ ↦ (1 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound C
      (eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ ?_))
    rw [norm_one, mul_one]
    apply hC
    rw [hNumRe]
    have hs' : u ≤ s.re ∧ s.re ≤ v := hs
    dsimp only [u, v] at hs'
    exact ⟨by linarith [hs'.2], by linarith [hs'.1]⟩
  have hExp : H =O[strip (Icc u v)] fun s ↦ Real.exp (B * |s.im|) := by
    simpa only [one_mul] using hNum.mul hΓ
  have hPoly := isBigO_pow_verticalStrip_of_exp huv
    (fun s hs ↦ (hHAnalytic hs.2).differentiableAt.differentiableWithinAt) hExp hLeft hRight
  have hAffine := isBigO_height_affine (ξ := ((n * M : ℕ) : ℝ)) (p := ((n * M : ℕ) : ℝ))
    (q := 0) huv (Nat.cast_nonneg _) (Nat.cast_nonneg _) le_rfl
    ⟨0, fun s hs _ ↦ hHAnalytic hs.2⟩
    (by simpa only [Real.rpow_natCast] using hPoly)
    (by simpa only [Real.rpow_natCast] using hLeft) hRight₀
  -- Undoing the shift of the numerator gains the height to the power `-n * K`.
  have hQuot : (fun s : ℂ ↦
      heckeGammaFactor χ⁻¹ (1 - s) / heckeGammaFactor χ⁻¹ (1 - s + 2 * (K : ℂ)))
      =O[strip (Icc u v)] fun s ↦ (|s.im| ^ (n * K))⁻¹ := by
    refine ((heckeGammaFactor_shift_inv_isBigO χ⁻¹ K).comp_tendsto
      (hReflect.mono_left (inf_le_left : strip (Icc u v) ≤ atHeight))).congr (fun _ ↦ rfl)
      fun s ↦ ?_
    simp only [Function.comp_apply, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
    rfl
  have hRaw : G =O[strip (Icc u v)] fun s ↦ |s.im| ^ ((n : ℝ) * (1 / 2 - s.re)) := by
    refine (hAffine.mul hQuot).congr' ?_ ?_
    · refine eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ ?_)
      have hne := heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (hNumPos hs.2)
      change _ * _⁻¹ * (_ / _) = _ / _
      rw [mul_div_assoc', div_eq_iff hne, div_eq_mul_inv]
      ring
    · filter_upwards [hHeight.eventually_ge_atTop (1 : ℝ)] with s ht
      have hpos : 0 < |s.im| := zero_lt_one.trans_le ht
      rw [← Real.rpow_natCast _ (n * K), ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos, hvu]
      congr 1
      have hu : u = 1 / 2 + K - M := rfl
      rw [hu]
      push_cast
      field_simp
      ring
  -- At large height the raw quotient is holomorphic, so it is its own normal form.
  have hGMero : MeromorphicOn G univ := by
    intro s _
    simpa only [G, div_eq_mul_inv, Function.comp_apply] using
      (((meromorphic_heckeGammaFactor χ⁻¹ (1 - s)).comp_analyticAt
        (analyticAt_const.sub analyticAt_id)).fun_mul (hInv.analyticAt s).meromorphicAt)
  have hNF : toMeromorphicNFOn G univ =ᶠ[atHeight] G := by
    filter_upwards [hReflect.eventually (heckeGammaFactor_eventually_ne_zero χ⁻¹)] with s hs
    have hNum : AnalyticAt ℂ (heckeGammaFactor χ⁻¹) (1 - s) := by
      simpa only [inv_inv] using
        (((differentiable_inv_heckeGammaFactor χ⁻¹).analyticAt (1 - s)).fun_inv (inv_ne_zero hs))
    have hG : AnalyticAt ℂ G s := by
      simpa only [G, div_eq_mul_inv, Function.comp_apply] using
        ((hNum.comp (f := fun z : ℂ ↦ 1 - z) (analyticAt_const.sub analyticAt_id)).fun_mul
          (hInv.analyticAt s))
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hGMero (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr hG.meromorphicNFAt]
  exact (hRaw.mono (inf_le_inf_left _ (principal_mono.mpr
    (preimage_mono (Icc_subset_Icc hau hbv))))).congr' (hNF.filter_mono inf_le_left).symm
    EventuallyEq.rfl

/-- Paper: Equation (B.1.1.10), p. 590. The reflection factor in the functional
equation satisfies the stated power bound on every fixed closed vertical strip. -/
theorem finiteHeckeReflectionFactor_isBigO_on_strip (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hεNe : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ]
      (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (a b : ℝ) (hab : a < b) :
    finiteHeckeReflectionFactor χ ε =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by
  -- The functional equation determines the multiplier in meromorphic normal form.
  clear hε hεNe
  let G := toMeromorphicNFOn
    (fun z ↦ heckeGammaFactor χ⁻¹ (1 - z) / heckeGammaFactor χ z) univ
  obtain ⟨c, r, hc, hExplicit⟩ :=
    finiteHeckeL_functionalEquation_conductorScale χ L Ldual hL hSeries hLdual hDualSeries
  let E (s : ℂ) := c * Complex.exp ((r : ℂ) * s)
  let D (s : ℂ) := Ldual (1 - s)
  have hD : MeromorphicOn D univ := fun s _ ↦
    (hLdual (mem_univ (1 - s))).meromorphicAt.comp_analyticAt
      (analyticAt_const.sub analyticAt_id)
  obtain ⟨s₀, hs₀⟩ := finiteHeckeL_continuation_exists_ne_zero χ⁻¹ Ldual hDualSeries
  have hD₀ : meromorphicOrderAt D (1 - s₀) ≠ ⊤ := by
    have hL₀ : AnalyticAt ℂ Ldual s₀ := by
      rcases meromorphicNFAt_iff_analyticAt_or.mp (hLdual (mem_univ s₀)) with h | ⟨_, h⟩
      · exact h
      · exact (hs₀ h.2).elim
    have h : AnalyticAt ℂ D (1 - s₀) :=
      hL₀.comp_of_eq (analyticAt_const.sub analyticAt_id) (sub_sub_cancel 1 s₀)
    rw [h.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by simpa [D] using hs₀)]
    exact WithTop.zero_ne_top
  have hDne := hD.eventually_codiscreteWithin_apply_ne_zero fun s hs ↦
    hD.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ _) hs hD₀
  have hAgree : finiteHeckeReflectionFactor χ ε =ᶠ[codiscreteWithin univ] E * G := by
    filter_upwards [hEq, hExplicit, hDne] with s hs ht hsne
    exact mul_right_cancel₀ hsne (hs.symm.trans ht)
  have hE : Differentiable ℂ E := by
    dsimp [E]
    fun_prop
  have hEG : MeromorphicNFOn (E * G) univ :=
    (meromorphicNFOn_mul_iff_right_of_analyticOnNhd (fun s _ ↦ hE.analyticAt s)
      (fun s _ ↦ mul_ne_zero hc (Complex.exp_ne_zero _))).mpr (meromorphicNFOn_toMeromorphicNFOn _ _)
  have hW : MeromorphicNFOn (finiteHeckeReflectionFactor χ ε) univ :=
    meromorphicNFOn_toMeromorphicNFOn _ _
  have hEqW : finiteHeckeReflectionFactor χ ε = E * G := by
    funext s
    have hs := (eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hAgree) s (mem_univ s)
    exact (((hW (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hEG (mem_univ s))).mp (hs.mono fun z hz ↦ hz (mem_univ z))).eq_of_nhds
  have hBound : E =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
      (f := fun x ↦ ‖c‖ * Real.exp (r * x)) (by fun_prop)
    refine Asymptotics.IsBigO.of_bound C (eventually_inf_principal.mpr (Eventually.of_forall ?_))
    intro s hs
    simpa [E, norm_mul, Complex.norm_exp, Complex.mul_re,
      Real.norm_of_nonneg (by positivity : 0 ≤ ‖c‖ * Real.exp (r * s.re))] using hC s.re hs
  rw [hEqW]
  change (fun s ↦ E s * G s) =O[_] _
  simpa only [one_mul] using hBound.mul (heckeGammaRatio_isBigO_on_strip χ a b hab)

-- TODO(paper-gap): After (B.1.1.11), the displayed multiplier is called entire
-- and zero-free. For F = ℚ and χ trivial, its gamma quotient has a pole at 1
-- and a zero at 0. The explicit conductor normalization also needs an ideal conductor API.

/-- On a line to the left of zero, the reflected Dirichlet series is bounded,
so the reflection factor determines the power of the height in the upper bound. -/
private theorem finiteHeckeL_isBigO_on_left_line (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {u : ℝ} (hu : u < 0) :
    L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - u)) := by
  obtain ⟨Ldual, hDual, hDualSeries⟩ := finiteHeckeL_exists_continuation χ⁻¹
  obtain ⟨ε, hε, hεNe, hEq⟩ :=
    finiteHeckeL_continuation_functionalEquation χ L Ldual hL hSeries hDual hDualSeries
  have hUpper : u < u / 2 := by linarith
  let p (x : ℝ) := (Module.finrank ℚ F : ℝ) * (1 / 2 - x)
  obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := p)).mp
    (finiteHeckeReflectionFactor_isBigO_on_strip χ L Ldual ε hL hSeries hDual hDualSeries
      hε hεNe hEq (u - 1) (u / 2) (by linarith))
  obtain ⟨D, hD⟩ := finiteHeckeL_continuation_boundedOn_right χ⁻¹ Ldual hDualSeries
    (r := 1 - u / 2) (by linarith)
  refine (isBigO_height_iff (p := fun _ ↦ p u)).mpr
    ⟨C * max D 1, by positivity, max T 0 + 1, fun s hs ht ↦ ?_⟩
  change s.re = u at hs
  let B (z : ℂ) := C * max D 1 * |z.im| ^ p z.re
  suffices h : ‖L s‖ ≤ B s by simpa [B, hs] using h
  -- The functional equation holds on a punctured neighborhood, so take limits at regular points.
  rcases meromorphicNFAt_iff_analyticAt_or.mp (hL (mem_univ s)) with hAnalytic | ⟨_, _, hZero⟩
  · have hB : ContinuousAt B s := by
      refine continuousAt_const.mul (ContinuousAt.rpow
        Complex.continuous_im.continuousAt.abs ?_ (Or.inl ?_))
      · dsimp [p]
        fun_prop
      · exact (show 0 < |s.im| by linarith [le_max_right T 0]).ne'
    apply le_of_tendsto_of_tendsto (b := 𝓝[≠] s)
      (hAnalytic.continuousAt.norm.tendsto.mono_left nhdsWithin_le_nhds)
      (hB.tendsto.mono_left nhdsWithin_le_nhds)
    have hre : ∀ᶠ z : ℂ in 𝓝 s, z.re ∈ Ioo (u - 1) (u / 2) :=
      Complex.continuous_re.continuousAt (Ioo_mem_nhds (by rw [hs]; linarith) (by rwa [hs]))
    have him : ∀ᶠ z : ℂ in 𝓝 s, T < |z.im| :=
      Complex.continuous_im.continuousAt.abs (Ioi_mem_nhds (by linarith [le_max_left T 0]))
    filter_upwards [hEq.filter_mono (nhdsNE_le_codiscrete s),
      hre.filter_mono nhdsWithin_le_nhds, him.filter_mono nhdsWithin_le_nhds] with z hz hzr hzi
    have hReflected : 1 - u / 2 ≤ (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith [hzr.2]
    rw [hz, norm_mul]
    calc
      _ ≤ (C * |z.im| ^ p z.re) * max D 1 :=
        mul_le_mul (hT z (Ioo_subset_Icc_self hzr) hzi.le)
          ((hD _ hReflected).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ = B z := by dsimp [B]; ring
  · rw [hZero, norm_zero]
    dsimp [B]
    positivity

/-- Paper: Proposition B.1.1.3, p. 591. On the closed critical strip the
convexity bound has a common constant for all positive ε and all real parts.
The height from which the estimate holds may depend on ε. -/
theorem finiteHeckeL_continuation_convexity_bound (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > (0 : ℝ),
      Asymptotics.IsBigOWith C (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (0 : ℝ) 1)) L
        (fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε)) := by
  refine ⟨1, zero_lt_one, fun ε hε ↦ ?_⟩
  let d : ℝ := Module.finrank ℚ F
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let δ := ε / (d + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hdδ : d * δ ≤ ε := by
    have h := (eq_div_iff (show d + 1 ≠ 0 by positivity)).mp (rfl : δ = ε / (d + 1))
    nlinarith
  let u := -δ
  let v := 1 + δ
  have hu : u < 0 := neg_lt_zero.mpr hδ
  have hv : 1 < v := lt_add_of_pos_right _ hδ
  have huv : u < v := hu.trans (zero_lt_one.trans hv)
  let heightIn (S : Set ℝ) := atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)
  have hFilter {S S' : Set ℝ} (h : S ⊆ S') : heightIn S ≤ heightIn S' :=
    inf_le_inf_left _ (principal_mono.mpr (preimage_mono h))
  obtain ⟨G, hG, hGL⟩ :=
    exists_analyticOnNhd_isTheta_finiteHeckeL_continuation χ L hL hSeries (u - 1)
  have hSub : Icc u v ⊆ Ioi (u - 1) := fun _ hs ↦
    (sub_lt_self u zero_lt_one).trans_le hs.1
  have hLeft := finiteHeckeL_isBigO_on_left_line χ L hL hSeries hu
  obtain ⟨D, hD⟩ := finiteHeckeL_continuation_boundedOn_right χ L hSeries hv
  have hRight : L =O[heightIn {v}] fun s ↦ |s.im| ^ (0 : ℝ) := by
    refine (isBigO_height_iff (p := fun _ ↦ 0)).mpr
      ⟨max D 1, by positivity, 0, fun s hs _ ↦ ?_⟩
    simpa only [Real.rpow_zero, mul_one] using
      (hD s (le_of_eq (mem_singleton_iff.mp hs).symm)).trans (le_max_left D 1)
  obtain ⟨M, hM, hPoly⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries u v huv
  have hθ := hGL.mono (hFilter hSub)
  have hInterp := isBigO_height_affine (f := G) (p := d * (1 / 2 - u)) (q := 0) huv
    hM.le (mul_nonneg hd (by linarith)) le_rfl
    ⟨0, fun s hs _ ↦ hG s (hSub hs)⟩ (hθ.isBigO.trans hPoly)
    ((hθ.isBigO.mono (hFilter (singleton_subset_iff.mpr (left_mem_Icc.mpr huv.le)))).trans hLeft)
    ((hθ.isBigO.mono (hFilter (singleton_subset_iff.mpr (right_mem_Icc.mpr huv.le)))).trans hRight)
  have hExponent (x : ℝ) :
      (1 - (x - u) / (v - u)) * (d * (1 / 2 - u)) + (x - u) / (v - u) * 0 =
        d * ((1 + δ - x) / 2) := by
    have hWidth : v - u = 2 * (1 / 2 - u) := by dsimp [u, v]; ring
    field_simp [sub_ne_zero.mpr huv.ne']
    rw [hWidth]
    ring
  simp only [hExponent] at hInterp
  have hBound := (hθ.symm.isBigO.trans hInterp).mono (hFilter (Icc_subset_Icc hu.le hv.le))
  obtain ⟨C, _, hC⟩ := Asymptotics.isBigO_iff'.mp hBound
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) (heightIn (Icc 0 1)) atTop :=
    tendsto_inf_left tendsto_comap
  -- The remaining ε / 2 absorbs the interpolation constant at sufficiently large height.
  apply Asymptotics.IsBigOWith.of_bound
  filter_upwards [hC, hHeight.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp hHeight).eventually_ge_atTop C]
    with s hs ht hLarge
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hs ⊢
  rw [one_mul]
  calc
    ‖L s‖ ≤ C * |s.im| ^ (d * ((1 + δ - s.re) / 2)) := hs
    _ ≤ |s.im| ^ (d * ((1 + δ - s.re) / 2)) * |s.im| ^ (ε / 2) := by
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left hLarge (Real.rpow_nonneg (abs_nonneg _) _)
    _ ≤ _ := by
      rw [← Real.rpow_add (zero_lt_one.trans_le ht)]
      apply Real.rpow_le_rpow_of_exponent_le ht
      change d * ((1 + δ - s.re) / 2) + ε / 2 ≤ d * ((1 - s.re) / 2) + ε
      linarith only [hdδ]

-- TODO(paper-gap): Footnote 2 asks for a bound on [-1, 2] without specifying
-- an exponent there. The exponent in (B.1.1.12) fails at σ = -1 even for ζ.
-- TODO(paper-gap): The bound on the dual L-factor gives an upper bound by
-- the reflection factor on fixed left-hand lines. The printed asymptotic
-- equivalence would require the dual L-factor to tend to one in absolute value.
-- TODO(paper-gap): In (B.1.1.14), the bounds on μ at 0 and 1 give an inequality
-- for the interpolation term. The printed equality needs a separate argument.

/-- Paper: Remark B.1.1.4, p. 591. On each fixed vertical line the continued
finite L-function is eventually holomorphic, and each of its holomorphic
derivatives grows at most polynomially as the absolute height tends to infinity. -/
theorem finiteHeckeL_continuation_iteratedDeriv_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (k : ℕ) (σ : ℝ) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
      ∀ᶠ s in atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ}),
        AnalyticAt ℂ L s ∧ ‖iteratedDeriv k L s‖ ≤ C * |s.im| ^ M := by
  obtain ⟨M, hM, hGrowth⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries
    (σ - 2) (σ + 2) (by linarith)
  obtain ⟨D, hD, T, hT⟩ := (isBigO_height_iff (p := fun _ ↦ M)).mp hGrowth
  have hIm : Continuous (fun w : ℂ ↦ |w.im|) := Complex.continuous_im.abs
  -- A pole would contradict the local bound in the interior of the strip.
  have hAnalytic {w : ℂ} (hRe : w.re ∈ Ioo (σ - 2) (σ + 2)) (hHeight : T < |w.im|) :
      AnalyticAt ℂ L w := by
    apply (hL (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hPole
    have hNearRe : ∀ᶠ z : ℂ in 𝓝 w, z.re ∈ Ioo (σ - 2) (σ + 2) :=
      (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hRe
    have hNearIm : ∀ᶠ z : ℂ in 𝓝 w, |z.im| ∈ Ioo T (|w.im| + 1) :=
      (isOpen_Ioo.preimage hIm).mem_nhds ⟨hHeight, lt_add_of_pos_right _ zero_lt_one⟩
    have hBound : ∀ᶠ z in 𝓝 w, ‖L z‖ ≤ D * (|w.im| + 1) ^ M := by
      filter_upwards [hNearRe, hNearIm] with z hzRe hzIm
      exact (hT z (Ioo_subset_Icc_self hzRe) hzIm.1.le).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hzIm.2.le hM.le) hD.le)
    have hBlowup := (tendsto_norm_cobounded_atTop.comp
      (tendsto_cobounded_of_meromorphicOrderAt_neg hPole)).eventually_gt_atTop
        (D * (|w.im| + 1) ^ M)
    obtain ⟨z, hz, h'z⟩ := ((hBound.filter_mono nhdsWithin_le_nhds).and hBlowup).exists
    exact h'z.not_ge hz
  refine ⟨M, (k.factorial : ℝ) * (D * (2 : ℝ) ^ M), hM, by positivity, ?_⟩
  have hLine : ∀ᶠ s in atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ}), s.re = σ :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ hs ↦ hs)
  have hHeight : Tendsto (fun s : ℂ ↦ |s.im|) (atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})) atTop :=
    tendsto_inf_left tendsto_comap
  filter_upwards [hLine, hHeight.eventually_ge_atTop (max 1 (T + 2))] with s hs hts
  have hOne : 1 ≤ |s.im| := (le_max_left _ _).trans hts
  have hLarge : T + 2 ≤ |s.im| := (le_max_right _ _).trans hts
  -- The unit disk stays inside the strip and its boundary heights are at most twice the center's.
  have hDisk {w : ℂ} (hw : w ∈ Metric.closedBall s 1) :
      w.re ∈ Ioo (σ - 2) (σ + 2) ∧ T < |w.im| ∧ |w.im| ≤ 2 * |s.im| := by
    have hdist := mem_closedBall_iff_norm.mp hw
    have hre := (Complex.abs_re_le_norm (w - s)).trans hdist
    have him := (Complex.abs_im_le_norm (w - s)).trans hdist
    rw [Complex.sub_re, hs, abs_le] at hre
    rw [Complex.sub_im] at him
    refine ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ?_, ?_⟩
    · linarith [(abs_sub_abs_le_abs_sub s.im w.im).trans (by simpa [abs_sub_comm] using him)]
    · linarith [(abs_sub_abs_le_abs_sub w.im s.im).trans him]
  have hDiskAnalytic (w : ℂ) (hw : w ∈ Metric.closedBall s 1) : AnalyticAt ℂ L w :=
    hAnalytic (hDisk hw).1 (hDisk hw).2.1
  refine ⟨hDiskAnalytic s (Metric.mem_closedBall_self zero_le_one), ?_⟩
  have hDiff : DiffContOnCl ℂ L (Metric.ball s 1) :=
    (show DifferentiableOn ℂ L (Metric.closedBall s 1) from fun w hw ↦
      (hDiskAnalytic w hw).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
  have hCircle (w : ℂ) (hw : w ∈ Metric.sphere s 1) :
      ‖L w‖ ≤ (D * (2 : ℝ) ^ M) * |s.im| ^ M := by
    obtain ⟨hRe, hLow, hHigh⟩ := hDisk (Metric.sphere_subset_closedBall hw)
    calc
      ‖L w‖ ≤ D * |w.im| ^ M := hT w (Ioo_subset_Icc_self hRe) hLow.le
      _ ≤ D * (2 * |s.im|) ^ M :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hHigh hM.le) hD.le
      _ = (D * (2 : ℝ) ^ M) * |s.im| ^ M := by
        rw [Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (abs_nonneg _), mul_assoc]
  simpa only [one_pow, div_one, mul_assoc] using
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k zero_lt_one hDiff hCircle

-- TODO(paper-gap): Footnotes 3 and 4 leave the intended uniform derivative
-- bounds on strips open. Proposition 3.3.1.5 is stated on fixed lines with σ > 0.

end Hecke

end RiemannMasullo
