module

public import RiemannMasullo.Ch01_Introduction.Sec4
import all RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.Continuity
public import RiemannMasullo.Research.StripNuclearity.HeckeAngularWeights
import RiemannMasullo.Research.StripNuclearity.HeckePairedDivisor
import RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import all RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Absolute spectral approximation at the norm-one idèle classes

A single cutoff approximates both sides of the explicit formula in §1.4.6, p. 30.
The input on simultaneous angular Fourier costs is the theorem on Sergii
Penner’s strip-kernel branch at revision 394da1b3.
-/

@[expose] public noncomputable section

section
open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology
namespace RiemannMasullo
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "zeroOrder(" χ ", " s ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros(" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder(χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}
private theorem introTrace_shrinking_profile_bounds
    (f b : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {P Q : ℝ} (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q)
    (hP : ∀ i : ℕ, i ≤ 2 → ∀ x ∈ Icc (1/2:ℝ) (3/2), ‖iteratedDeriv i f x‖ ≤ P)
    (hQ : ∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedDeriv i b x‖ ≤ Q)
    (hsb : tsupport b ⊆ Ioo (-1 : ℝ) 1) (hf1 : f 1 = 0) :
    ∀ c : ℝ, 4 ≤ c →
      let v (x : ℝ) := f x * b (c * (x - 1))
      ContDiff ℝ 2 v ∧ tsupport v ⊆ Ioo (1 - c⁻¹) (1 + c⁻¹) ∧
      ∀ x ∈ Icc (1 - c⁻¹) (1 + c⁻¹), ‖v x‖ ≤ 4*P*Q ∧ ‖deriv (deriv v) x‖ ≤ 4*P*Q*c := by
  intro c hc v
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hcI : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0.ne'
  let g (t : ℝ) := b (c * (t - 1))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hb.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hgd (i : ℕ) (hi : i ≤ 2) (x : ℝ) : ‖iteratedDeriv i g x‖ ≤ c ^ i * Q := by
    have he : iteratedDeriv i g x = c ^ i • iteratedDeriv i b (c * (x - 1)) := by
      change iteratedDeriv i (fun t : ℝ ↦ (fun y : ℝ ↦ b (c * y)) (t - 1)) x = _
      exact (congrFun (iteratedDeriv_comp_sub_const i (fun y : ℝ ↦ b (c*y)) 1) x).trans
        (congrFun (iteratedDeriv_comp_const_smul (hb.of_le (by simp) : ContDiff ℝ i b) c) (x - 1))
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc0.le _)]
    exact mul_le_mul_of_nonneg_left (hQ i hi _) (pow_nonneg hc0.le _)
  have hs : tsupport v ⊆ (fun t : ℝ ↦ c * (t - 1)) ⁻¹' tsupport b := by
    refine closure_minimal (fun x hx ↦ subset_tsupport _ (right_ne_zero_of_mul hx)) ?_
    exact (isClosed_tsupport _).preimage (continuous_const.mul (continuous_id.sub continuous_const))
  refine ⟨(hf.mul hg).of_le (by simp), fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨hl, hu⟩ := hsb (hs hx)
    constructor <;> nlinarith
  · have hi4 : c⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ hc0 (by norm_num)]; norm_num; linarith
    have hx' : x ∈ Icc (1/2:ℝ) (3/2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hf0 : ‖f x‖ ≤ P := by simpa using hP 0 (by decide) x hx'
    have hf' (y : ℝ) (hy : y ∈ Icc (1/2:ℝ) (3/2)) : ‖deriv f y‖ ≤ P := by
      simpa using hP 1 (by decide) y hy
    have hb0 (y : ℝ) : ‖g y‖ ≤ Q := by simpa using hgd 0 (by decide) y
    have hb' (y : ℝ) : ‖deriv g y‖ ≤ c * Q := by simpa using hgd 1 (by decide) y
    have hfx : ‖f x‖ ≤ P * c⁻¹ := by
      have h := (convex_Icc (1/2:ℝ) (3/2)).norm_image_sub_le_of_norm_deriv_le
        (fun y _ ↦ hf.differentiable (by simp) y) hf' (by constructor <;> norm_num : (1:ℝ) ∈ Icc (1/2) (3/2)) hx'
      rw [hf1, sub_zero, Real.norm_eq_abs] at h
      exact h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩) hP0)
    constructor
    · change ‖f x * g x‖ ≤ _
      rw [norm_mul]
      exact (mul_le_mul hf0 (hb0 x) (norm_nonneg _) hP0).trans (by nlinarith [mul_nonneg hP0 hQ0])
    · have h := norm_iteratedFDeriv_mul_le hf hg x (n := 2) (by simp)
      simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
      have hprod : ‖deriv (deriv v) x‖ ≤ ‖f x‖ * ‖iteratedDeriv 2 g x‖ +
          2 * ‖deriv f x‖ * ‖deriv g x‖ + ‖iteratedDeriv 2 f x‖ * ‖g x‖ := by
        simpa [v, g, Finset.sum_range_succ, Nat.choose, iteratedDeriv_succ] using h
      calc _ ≤ _ := hprod
           _ ≤ P * c⁻¹ * (c ^ 2 * Q) + 2 * P * (c * Q) + P * Q := by
             gcongr
             · exact hgd 2 le_rfl x
             · exact hf' x hx'
             · exact hb' x
             · exact hP 2 le_rfl x hx'
             · exact hb0 x
           _ = (3 * P * Q) * c + P * Q := by
             field_simp
             ring
           _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hP0 hQ0)]
private theorem introTrace_shrinking_mellin_majorant {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) :
    let K := 8 * C * (4 : ℝ) ^ (B + 1)
    ∀ c : ℝ, 4 ≤ c → ∀ v : ℝ → ℂ,
      ContDiff ℝ 2 v → tsupport v ⊆ Ioo (1 - c⁻¹) (1 + c⁻¹) →
      (∀ x ∈ Icc (1 - c⁻¹) (1 + c⁻¹), ‖v x‖ ≤ C ∧ ‖deriv (deriv v) x‖ ≤ C * c) →
      ∀ s : ℂ, |s.re| ≤ B → ‖introTraceMellin v s‖ ≤ K * c⁻¹ ∧
        ‖introTraceMellin v s‖ ≤ K / (1 + |s.im|) ^ 2 := by
  let D := (4 : ℝ) ^ (B + 1)
  have hD : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  intro K c hc v hv hs hbd s hsr
  change _ ≤ 8*C*D*c⁻¹ ∧ _ ≤ 8*C*D / _
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hi : 0 < c⁻¹ := inv_pos.mpr hc0
  have hi4 : c⁻¹ ≤ 1 / 4 := by rw [inv_le_comm₀ hc0 (by norm_num)]; norm_num; linarith
  let l := 1 - c⁻¹
  let r := 1 + c⁻¹
  have hl : 0 < l := by dsimp [l]; linarith
  have hlr : l ≤ r := by dsimp [l, r]; linarith
  have hM : max r l⁻¹ + 1 ≤ 4 := by
    have hinv : l⁻¹ ≤ 2 := (inv_le_comm₀ hl (by norm_num)).mpr (by dsimp [l]; linarith)
    linarith [max_le (by dsimp [r]; linarith : r ≤ 2) hinv]
  have hleft : l ∉ tsupport v := fun h ↦ (lt_irrefl _) (hs h).1
  have hright : r ∉ tsupport v := fun h ↦ (lt_irrefl _) (hs h).2
  rw [introTraceApprox_spectral_differentiable_mellin_interval v hl hlr (fun t ht ↦ hs (subset_tsupport _ ht))]
  constructor
  · have hnorm (t : ℝ) (ht : t ∈ Icc l r) : ‖(t : ℂ) ^ (s - 1) * v t‖ ≤ D * C := by
      have ht0 : 0 < t := hl.trans_le ht.1
      have ht2 : t ≤ 4 := by dsimp [r] at ht; linarith [ht.2]
      have hti : t⁻¹ ≤ 4 := (inv_le_comm₀ ht0 (by norm_num)).mpr (by dsimp [l] at ht; linarith [ht.1])
      have hlog : |Real.log t| ≤ Real.log 4 := abs_le.mpr
        ⟨by have h := Real.log_le_log (inv_pos.mpr ht0) hti; rw [Real.log_inv] at h; linarith,
         Real.log_le_log ht0 ht2⟩
      have hre : |(s - 1).re| ≤ B + 1 := by
        simp only [Complex.sub_re, Complex.one_re]
        exact (abs_sub s.re 1).trans (by rw [abs_one]; linarith)
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      refine mul_le_mul ?_ (hbd t ht).1 (norm_nonneg _) hD.le
      rw [Real.rpow_def_of_pos ht0, show D = Real.exp (Real.log 4 * (B + 1)) from
        Real.rpow_def_of_pos (by norm_num) _]
      apply Real.exp_le_exp.mpr
      calc _ ≤ |Real.log t * (s - 1).re| := le_abs_self _
           _ = |Real.log t| * |(s - 1).re| := abs_mul _ _
           _ ≤ _ := mul_le_mul hlog hre (abs_nonneg _) (Real.log_nonneg (by norm_num))
    have hx := intervalIntegral.norm_integral_le_of_norm_le_const (C := D * C)
      (f := fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * v t) (a := l) (b := r) fun t ht ↦
        hnorm t (Ioc_subset_Icc_self (Set.uIoc_of_le hlr ▸ ht))
    rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hx
    calc _ ≤ _ := hx
         _ = 2 * C * D * c⁻¹ := by dsimp [l, r]; ring
         _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC hD.le) hi.le]
  · have h := introTraceApprox_spectral_differentiable_parts hl hlr hv
      (image_eq_zero_of_notMem_tsupport hleft) (image_eq_zero_of_notMem_tsupport hright)
      (deriv_of_notMem_tsupport hleft) (deriv_of_notMem_tsupport hright)
      (fun t ht ↦ ((hbd t ht).1).trans (le_mul_of_one_le_right hC hc1))
      (fun t ht ↦ (hbd t ht).2) s hsr
    rw [max_self] at h
    have hM0 : 0 ≤ max r l⁻¹ + 1 := by have := le_max_left r l⁻¹; dsimp [r] at *; linarith
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    calc _ ≤ 4 * (r-l) * D * (C*c) := by
           gcongr
           exact Real.rpow_le_rpow hM0 hM (by linarith)
         _ = 8 * C * D := by
           dsimp [r,l]
           field_simp
           ring
/-- Paper: §1.4.6, p. 30. For a smooth profile vanishing at norm one, the Mellin
transform of its part in a shrinking neighborhood of one tends to zero with a
height-square majorant. Both bounds are linear in the local two-derivative bound
for the profile and in the corresponding bound for the fixed cutoff. -/
private theorem introTrace_shrinking_mellin_bound (f b : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf1 : f 1 = 0) (hsb : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hfD : ∀ j : ℕ, j ≤ 2 → ∀ x ∈ Icc (1/2 : ℝ) (3/2), ‖iteratedDeriv j f x‖ ≤ P)
    (hbD : ∀ j : ℕ, j ≤ 2 → ∀ x, ‖iteratedDeriv j b x‖ ≤ Q)
    {B c : ℝ} (hB : 0 ≤ B) (hc : 4 ≤ c) (s : ℂ) (hs : |s.re| ≤ B) :
    let v (t : ℝ) := f t * b (c * (t - 1))
    let K := 32 * P * Q * (4 : ℝ) ^ (B+1)
    ‖introTraceMellin v s‖ ≤ K * c⁻¹ ∧
      ‖introTraceMellin v s‖ ≤ K / (1 + |s.im|) ^ 2 := by
  intro v K
  obtain ⟨hv, hvS, hvD⟩ := introTrace_shrinking_profile_bounds f b hf hb hP hQ hfD hbD hsb hf1 c hc
  have h := introTrace_shrinking_mellin_majorant (C := 4*P*Q) (by positivity) hB c hc v hv hvS hvD s hs
  simpa only [show 8 * (4 * P * Q) * (4 : ℝ) ^ (B + 1) = K by dsimp [K]; ring] using h

end RiemannMasullo
end

section
open Filter MeasureTheory Function Set
open scoped FourierTransform ContDiff Topology

namespace RiemannMasullo

/-- Fourier inversion bounds the first three pointwise radial seminorms by
one quadratic Fourier moment, with a constant independent of the profile. -/
private theorem norm_jet_le_quadratic_fourier_moment
    (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p) (hc : HasCompactSupport p)
    (hi : Integrable (fun u : ℝ ↦ (1 + u^2) * ‖𝓕 p u‖))
    (j : ℕ) (hj : j ≤ 2) (x : ℝ) :
    ‖iteratedDeriv j p x‖ ≤ (1 + 2 * Real.pi)^2 * ∫ u : ℝ, (1 + u^2) * ‖𝓕 p u‖ := by
  have hcs (k : ℕ) : HasCompactSupport (iteratedDeriv k p) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hc
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hsm (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k p) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hp
    | succ k ih => simpa only [iteratedDeriv_succ] using (contDiff_infty_iff_deriv.mp ih).2
  have hint (k : ℕ) : Integrable (iteratedDeriv k p) := (hsm k).continuous.integrable_of_hasCompactSupport (hcs k)
  let q := iteratedDeriv j p
  let Q := (hcs j).toSchwartzMap (hsm j)
  have hFi : Integrable (𝓕 q) := (𝓕 Q).integrable
  have hF := Real.fourier_iteratedDeriv (N := ⊤) (n := j) hp (fun k _ ↦ hint k) le_top
  have hinv := (hint j).fourierInv_fourier_eq (v := x) hFi (hsm j).continuous.continuousAt
  change 𝓕⁻ (𝓕 q) x = q x at hinv
  change ‖q x‖ ≤ _
  rw [← hinv, Real.fourierInv_eq_fourier_neg]
  apply (Real.norm_fourier_le_integral_norm (𝓕 q) (-x)).trans
  rw [← integral_const_mul]
  apply integral_mono hFi.norm (hi.const_mul _) (fun u ↦ ?_)
  change ‖𝓕 (iteratedDeriv j p) u‖ ≤ _
  rw [hF]
  simp only [norm_smul,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg Real.pi_pos.le,Complex.norm_I,mul_pow]
  have hw : |u|^j ≤ 1 + u^2 := by
    interval_cases j <;> simp only [pow_zero,pow_one,sq_abs] <;>
      nlinarith [sq_nonneg u,sq_nonneg (|u| - 1 / 2),sq_abs u]
  have hk : (2 * Real.pi)^j ≤ (1 + 2 * Real.pi)^2 := by
    interval_cases j <;> try simp only [pow_zero,pow_one]
    all_goals nlinarith [Real.pi_pos, sq_nonneg (2 * Real.pi)]
  calc
    _ = (2 * Real.pi)^j * |u|^j * ‖𝓕 p u‖ := by ring
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hk hw (pow_nonneg (abs_nonneg _) _) (sq_nonneg _)) (norm_nonneg _)

/-- One summable majorant controls the radial derivatives of orders zero,
one and two in every angular component, with the divisor weights retained. -/
private theorem exists_weighted_summable_radial_majorant {ι : Type*} (p : ι → ℝ → ℂ) (M : ι → ℝ)
    (hm : ∀ i, 0 ≤ M i) (hp : ∀ i, ContDiff ℝ ∞ (p i)) (hc : ∀ i, HasCompactSupport (p i))
    (hi : ∀ i, Integrable (fun u : ℝ ↦ (1 + u^2) * ‖𝓕 (p i) u‖))
    (hs : Summable fun i ↦ (1 + M i)^2 * ∫ u : ℝ, (1 + u^2) * ‖𝓕 (p i) u‖) :
    ∃ A : ι → ℝ, (∀ i, 0 ≤ A i) ∧ Summable (fun i ↦ (1 + M i) * A i) ∧
      ∀ i j, j ≤ 2 → ∀ x, ‖iteratedDeriv j (p i) x‖ ≤ A i := by
  let A (i : ι) := (1 + 2 * Real.pi)^2 * ∫ u : ℝ, (1 + u^2) * ‖𝓕 (p i) u‖
  have hA (i) : 0 ≤ A i := mul_nonneg (sq_nonneg _) (integral_nonneg fun _ ↦ mul_nonneg (by positivity) (norm_nonneg _))
  refine ⟨A, hA, ?_, fun i j hj x ↦ norm_jet_le_quadratic_fourier_moment _ (hp i) (hc i) (hi i) j hj x⟩
  refine (hs.mul_left ((1 + 2 * Real.pi)^2)).of_nonneg_of_le
    (fun i ↦ mul_nonneg (by linarith [hm i]) (hA i)) fun i ↦ ?_
  calc
    _ ≤ (1 + M i)^2 * A i := mul_le_mul_of_nonneg_right
      (by nlinarith [hm i, sq_nonneg (M i)]) (hA i)
    _ = _ := by dsimp only [A]; ring

end RiemannMasullo
end

section
open Filter Function Set
open scoped Topology ContDiff

namespace RiemannMasullo

/-- A compact smooth log profile vanishing at log norm zero gives a smooth
multiplicative profile, including at the totalized value of the logarithm at zero. -/
private theorem contDiff_log_radial_of_vanishing (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p)
    (hc : HasCompactSupport p) (hzero : p 0 = 0) : ContDiff ℝ ∞ (p ∘ Real.log) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    obtain ⟨b, hb⟩ := hc.bddBelow
    have hne : ∀ᶠ x in 𝓝[≠] (0 : ℝ), (p ∘ Real.log) x = 0 := by
      filter_upwards [Real.tendsto_log_nhdsNE_zero.eventually_lt_atBot b] with x hx
      change p (Real.log x) = 0
      exact image_eq_zero_of_notMem_tsupport fun h ↦ (hb h).not_gt hx
    have heq : (p ∘ Real.log) =ᶠ[𝓝 (0 : ℝ)] 0 := by
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne] with x hh
      by_cases he : x = 0
      · simpa [he] using hzero
      · exact hh he
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hp.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)

/-- On the multiplicative norm interval used by the shrinking cutoff, the
first three derivatives are bounded by eight times a common additive jet bound. -/
private theorem norm_log_radial_jet_le (p : ℝ → ℂ) (hp : ContDiff ℝ ∞ p)
    {A : ℝ} (hA : 0 ≤ A) (h : ∀ j : ℕ, j ≤ 2 → ∀ t, ‖iteratedDeriv j p t‖ ≤ A)
    (j : ℕ) (hj : j ≤ 2) (x : ℝ) (hx : x ∈ Icc (1/2 : ℝ) (3/2)) :
    ‖iteratedDeriv j (p ∘ Real.log) x‖ ≤ 8 * A := by
  have hx' : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) hx.1
  have h1 (t : ℝ) (ht : t ≠ 0) : deriv (p ∘ Real.log) t = t⁻¹ • deriv p (Real.log t) :=
    (((hp.differentiable (by simp)).differentiableAt.hasDerivAt).scomp t (Real.hasDerivAt_log ht)).deriv
  have hi : ‖x⁻¹‖ ≤ 2 := by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr hx'.le), ← one_div, div_le_iff₀ hx']
    linarith [hx.1]
  have h1p : ‖deriv p (Real.log x)‖ ≤ A := by simpa using h 1 (by omega) (Real.log x)
  have h2p : ‖deriv (deriv p) (Real.log x)‖ ≤ A := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using h 2 (by omega) (Real.log x)
  have h2 : deriv (deriv (p ∘ Real.log)) x =
      x⁻¹ • (x⁻¹ • deriv (deriv p) (Real.log x)) + (-(x^2)⁻¹) • deriv p (Real.log x) := by
    have he : deriv (p ∘ Real.log) =ᶠ[𝓝 x] fun t ↦ t⁻¹ • deriv p (Real.log t) := by
      filter_upwards [eventually_ne_nhds hx'.ne'] with t ht using h1 t ht
    have hpd : HasDerivAt (deriv p) (deriv (deriv p) (Real.log x)) (Real.log x) :=
      ((contDiff_infty_iff_deriv.mp hp).2.differentiable (by simp)).differentiableAt.hasDerivAt
    exact (((hasDerivAt_inv hx'.ne').smul (hpd.scomp x (Real.hasDerivAt_log hx'.ne'))).congr_of_eventuallyEq he).deriv
  interval_cases j
  · simpa only [iteratedDeriv_zero, Function.comp_apply] using (h 0 (by omega) (Real.log x)).trans
      (show A ≤ 8*A by linarith)
  · simp only [iteratedDeriv_one,h1 x hx'.ne',norm_smul]
    exact (mul_le_mul hi h1p (norm_nonneg _) (by norm_num)).trans (by linarith)
  · simp only [iteratedDeriv_succ,iteratedDeriv_zero,h2]
    apply (norm_add_le _ _).trans
    simp only [norm_smul,norm_neg,← inv_pow,norm_pow]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hi 2
    have hfst := mul_le_mul hi (mul_le_mul hi h2p (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    have hsnd := mul_le_mul hsq h1p (norm_nonneg _) (by norm_num)
    linarith

end RiemannMasullo
end

section
open Filter Set
open scoped Topology

namespace RiemannMasullo

/-- When the reciprocal-height majorants of all angular fibers have summable
weighted masses, any varying selection of their Mellin residuals tends to zero
in absolute sum as soon as the individual residuals do. -/
private theorem summable_tendsto_joint_window_residuals
    {J ι E : Type*} [NormedAddCommGroup E] {κ : ι → Type*} (l : Filter J)
    (m : (i : ι) → κ i → ℝ) (M A : ι → ℝ)
    (hm : ∀ i j, 0 ≤ m i j) (hA : ∀ i, 0 ≤ A i)
    (hs : ∀ i, Summable (m i)) (hM : ∀ i, (∑' j, m i j) ≤ M i)
    (hb : Summable (fun i ↦ (1 + M i) * A i))
    (f : J → (i : ι) → κ i → E)
    (hlim : ∀ i j, Tendsto (fun c ↦ f c i j) l (𝓝 0))
    (hdom : ∀ c i j, ‖f c i j‖ ≤ A i * m i j)
    (win : J → Set ((i : ι) × κ i)) :
    (∀ c, Summable (fun q : (i : ι) × κ i ↦ (win c).indicator (fun q ↦ ‖f c q.1 q.2‖) q)) ∧
    Tendsto (fun c ↦ ∑' q : (i : ι) × κ i, (win c).indicator (fun q ↦ ‖f c q.1 q.2‖) q) l (𝓝 0) := by
  classical
  let B (q : (i : ι) × κ i) := A q.1 * m q.1 q.2
  have hB : Summable B := by
    apply (summable_sigma_of_nonneg (fun q ↦ mul_nonneg (hA q.1) (hm q.1 q.2))).2
    constructor
    · intro i
      exact (hs i).mul_left (A i)
    · apply hb.of_nonneg_of_le (fun i ↦ tsum_nonneg fun j ↦ mul_nonneg (hA i) (hm i j))
      intro i
      change (∑' j, A i * m i j) ≤ (1 + M i) * A i
      rw [tsum_mul_left, mul_comm]
      exact mul_le_mul_of_nonneg_right ((hM i).trans (by linarith)) (hA i)
  let g (c : J) (q : (i : ι) × κ i) := (win c).indicator (fun q ↦ ‖f c q.1 q.2‖) q
  have bounds (c : J) (q : (i : ι) × κ i) : 0 ≤ g c q ∧ g c q ≤ ‖f c q.1 q.2‖ := by
    by_cases hq : q ∈ win c <;> simp [g,hq]
  have h0 (q : (i : ι) × κ i) : Tendsto (fun c ↦ g c q) l (𝓝 0) := by
    exact squeeze_zero (fun c ↦ (bounds c q).1) (fun c ↦ (bounds c q).2)
      (by simpa only [norm_zero] using (hlim q.1 q.2).norm)
  have hbd : ∀ᶠ c in l, ∀ q, ‖g c q‖ ≤ B q := by
    refine .of_forall fun c q ↦ ?_
    rw [Real.norm_of_nonneg (bounds c q).1]
    exact (bounds c q).2.trans (hdom c q.1 q.2)
  refine ⟨fun c ↦ hB.of_nonneg_of_le (fun q ↦ (bounds c q).1)
    (fun q ↦ (bounds c q).2.trans (hdom c q.1 q.2)), ?_⟩
  simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence hB h0 hbd)

end RiemannMasullo
end

section
open Filter Function MeasureTheory Set
open scoped Topology ContDiff FourierTransform

namespace RiemannMasullo

/-- A summable Fourier moment weighted by the divisor mass permits shrinking the
norm cutoff simultaneously over every angular character and every zero. The choice
of retained terms can vary with the cutoff. -/
private theorem summable_tendsto_joint_shrinking_mellin {ι : Type*} (p : ι → ℝ → ℂ)
    (D : ι → ℂ → ℝ) (hp : ∀ i, ContDiff ℝ ∞ (p i)) (hc : ∀ i, HasCompactSupport (p i))
    (hp0 : ∀ i, p i 0 = 0) (hD : ∀ i z, 0 ≤ D i z)
    (hstrip : ∀ i z, D i z ≠ 0 → |z.re - 1/2| ≤ 1)
    (hm : ∀ i, Summable (fun z : ℂ ↦ D i z / (1 + |z.im|)^2))
    (hi : ∀ i, Integrable (fun u : ℝ ↦ (1 + u^2) * ‖𝓕 (p i) u‖))
    (hs : Summable fun i ↦ (1 + ∑' z : ℂ, D i z / (1 + |z.im|)^2)^2 *
      ∫ u : ℝ, (1 + u^2) * ‖𝓕 (p i) u‖)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hsb : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hbD : ∀ j : ℕ, j ≤ 2 → ∀ x, ‖iteratedDeriv j b x‖ ≤ Q)
    (win : ℕ → Set ((i : ι) × ℂ)) :
    let v (n : ℕ) (i : ι) (r : ℝ) := p i (Real.log r) * b (((n : ℝ) + 4) * (r-1))
    (∀ n, Summable (fun q : (_ : ι) × ℂ ↦ (win n).indicator
      (fun q ↦ ‖(D q.1 q.2 : ℂ) * introTraceMellin (v n q.1) (q.2 - 1/2)‖) q)) ∧
    Tendsto (fun n ↦ ∑' q : (i : ι) × ℂ, (win n).indicator
      (fun q ↦ ‖(D q.1 q.2 : ℂ) * introTraceMellin (v n q.1) (q.2 - 1/2)‖) q) atTop (𝓝 0) := by
  classical
  intro v
  let m (i : ι) (z : ℂ) := D i z / (1 + |z.im|)^2
  let M (i : ι) := ∑' z, m i z
  have hm0 (i : ι) (z : ℂ) : 0 ≤ m i z := div_nonneg (hD i z) (sq_nonneg _)
  obtain ⟨A, hA, hsum, hjet⟩ := exists_weighted_summable_radial_majorant p M (fun i ↦ tsum_nonneg (hm0 i))
    hp hc hi hs
  let C := 32 * 8 * Q * (4 : ℝ)^((1:ℝ)+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmajor : Summable (fun i ↦ (1 + M i) * (C * A i)) :=
    (hsum.mul_left C).congr fun i ↦ by ring
  have bnd (n : ℕ) (i : ι) (z : ℂ) (hd : D i z ≠ 0) :
      ‖introTraceMellin (v n i) (z-1/2)‖ ≤ (C * A i) * ((n : ℝ) + 4)⁻¹ ∧
      ‖introTraceMellin (v n i) (z-1/2)‖ ≤ (C * A i) / (1 + |z.im|)^2 := by
    have hh := introTrace_shrinking_mellin_bound (p i ∘ Real.log) b
      (contDiff_log_radial_of_vanishing (p i) (hp i) (hc i) (hp0 i)) hb
      (by simpa using hp0 i) hsb (P := 8*A i) (Q := Q) (mul_nonneg (by norm_num) (hA i)) hQ
      (norm_log_radial_jet_le (p i) (hp i) (hA i) (hjet i)) hbD (B := 1) (by norm_num)
      (c := (n : ℝ)+4) (by linarith [Nat.cast_nonneg (α := ℝ) n]) (z-1/2)
      (by simpa using hstrip i z hd)
    simpa only [C, v, Function.comp_apply, show (32:ℝ)*(8*A i)*Q*4^((1:ℝ)+1) =
      32*8*Q*4^((1:ℝ)+1)*A i by ring, Complex.sub_im,Complex.div_ofNat_im,
      Complex.one_im,zero_div,sub_zero] using hh
  let f (n : ℕ) (i : ι) (z : ℂ) := (D i z : ℂ) * introTraceMellin (v n i) (z - 1/2)
  have hf (n : ℕ) (i : ι) (z : ℂ) : ‖f n i z‖ = D i z * ‖introTraceMellin (v n i) (z - 1/2)‖ := by
    simp only [f,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hD i z)]
  have hlim (i : ι) (z : ℂ) : Tendsto (fun n ↦ f n i z) atTop (𝓝 0) := by
    by_cases hd : D i z = 0
    · simp [f, hd]
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have hc0 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 4)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop)
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) (by
      simpa only [mul_zero] using (hc0.const_mul (C*A i)).const_mul (D i z))
    rw [hf]
    exact mul_le_mul_of_nonneg_left (bnd n i z hd).1 (hD i z)
  apply summable_tendsto_joint_window_residuals atTop m M (fun i ↦ C * A i)
    hm0 (fun i ↦ mul_nonneg hC (hA i)) hm (fun _ ↦ le_rfl) hmajor f hlim _ win
  intro n i z
  rw [hf]
  by_cases hd : D i z = 0
  · simp [m,hd]
  calc _ ≤ D i z * ((C*A i) / (1 + |z.im|)^2) := mul_le_mul_of_nonneg_left (bnd n i z hd).2 (hD i z)
       _ = _ := by dsimp only [m]; ring

end RiemannMasullo
end

section
open Function MeasureTheory NumberField Set Filter
open scoped NNReal Topology ContDiff FourierTransform

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "U" => PontryaginDual C𝔽
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ

/-- A single shrinking radial cutoff gives absolute convergence to zero simultaneously over
all angular components of an idèle-class Bruhat test vanishing at norm one and the entire
positive divisor of the associated completed Hecke functions, for arbitrary varying windows. -/
private theorem summable_tendsto_hecke_angular_zero_cutoff_residual
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ k : C₁, φ.val k.val = 0)
    (μ : Measure C₁) [μ.IsHaarMeasure] (χ : X →* U) (hχ : IsSpectralBasepointChoice χ)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hsb : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hbD : ∀ j : ℕ, j ≤ 2 → ∀ x, ‖iteratedDeriv j b x‖ ≤ Q)
    (win : ℕ → Set ((ξ : X) × ℂ)) :
    let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
    let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
    let p (ξ : X) (t : ℝ) :=
      ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) * (ξ k : ℂ) ∂μ
    let v (n : ℕ) (ξ : X) (r : ℝ) := p ξ (Real.log r) * b (((n : ℝ) + 4) * (r-1))
    (∀ n, Summable (fun pair : (_ : X) × ℂ ↦ (win n).indicator (fun pair ↦
      ‖(((D(χ pair.1) pair.2).toNat : ℝ) : ℂ) * introTraceMellin (v n pair.1) (pair.2 - 1/2)‖) pair)) ∧
    Tendsto (fun n ↦ ∑' pair : (ξ : X) × ℂ, (win n).indicator (fun pair ↦
      ‖(((D(χ pair.1) pair.2).toNat : ℝ) : ℂ) * introTraceMellin (v n pair.1) (pair.2 - 1/2)‖) pair)
      atTop (𝓝 0) := by
  classical
  intro q σ p v
  obtain ⟨J, hJ, hprof, _⟩ := ideleClass_summable_angularProfile_derivatives μ φ
  apply summable_tendsto_joint_shrinking_mellin p
    (fun ξ z ↦ ((D(χ ξ) z).toNat : ℝ)) (fun ξ ↦ (hprof ξ).2)
    (fun ξ ↦ hJ.of_isClosed_subset isClosed_closure (hprof ξ).1) _ (fun _ _ ↦ Nat.cast_nonneg _)
    _ (fun ξ ↦ summable_heckePositiveDivisor_mass (χ ξ)) _
    (summable_heckePositiveDivisorMass_angular_fourierCost φ μ χ hχ) b hb hsb hQ hbD win
  · intro ξ
    change (∫ k : C₁, φ.val (k.val * σ (radialExponential 1)) * (ξ k : ℂ) ∂μ) = 0
    calc _ = ∫ k : C₁, (0 : ℂ) ∂μ := by
           refine integral_congr_ae (.of_forall fun k ↦ ?_)
           have e : k.val * σ (radialExponential 1) = k.val := by
             rw [map_one, map_one]
             exact mul_one (k.val : C𝔽)
           exact (congrArg (fun a : ℂ ↦ a * (ξ k : ℂ)) ((congrArg φ.val e).trans (hφ k))).trans (zero_mul _)
         _ = 0 := integral_zero _ _
  · intro ξ z hn
    have hd : 0 < D(χ ξ) z := by
      by_contra h
      exact hn (by simp [Int.toNat_of_nonpos (le_of_not_gt h)])
    obtain ⟨hl, hr⟩ := heckePositiveDivisor_open_strip (χ ξ) hd
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro ξ
    simpa only [pow_one] using (ideleClass_summable_angularProfile_fourierMoments μ φ [] 1).1 ξ

end RiemannMasullo.StripNuclearity
end

section
open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology ContDiff FourierTransform

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U" => PontryaginDual C𝔽
local notation "X" => PontryaginDual C₁
local notation "N(" g ")" => ((ideleClassNorm F g).val : ℝ)
local notation "σ" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

/-- Multiplying a compact idèle-class test by any continuous radial cutoff multiplies
its angular Mellin profile by the same cutoff, with both Tamagawa measures explicit. -/
private theorem ideleClass_radial_cutoff_mellin (φ : BruhatCompactSupport C𝔽) (ψ : U)
    (hψ : ∀ r, ψ (σ r) = 1) (b : ℝ → ℂ) (hb : Continuous b) (s : ℂ) :
    let p (x : ℝ) := ∫ u : C₁, φ.val (u.val * σ (radialExponential (Multiplicative.ofAdd x))) *
      (ψ u.val : ℂ) ∂normOneIdeleClassTamagawaMeasure F
    (∫ g, φ.val g * b (N(g)) * ideleClassNormTwist ψ s g ∂ideleClassTamagawaMeasure F) =
      introTraceMellin (fun r ↦ p (Real.log r) * b r) s := by
  intro p
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let : IsFiniteMeasure (normOneIdeleClassTamagawaMeasure F) :=
    ⟨by rw [normOneIdeleClassTamagawaMeasure_volume]; exact ENNReal.ofReal_lt_top⟩
  let H (g : C𝔽) := φ.val g * b (N(g)) * ideleClassNormTwist ψ s g
  have hφ : Continuous φ.val := schwartzBruhat_continuous
    (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hnorm : Continuous (fun g : C𝔽 ↦ N(g)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hH : Continuous H := (hφ.mul (hb.comp hnorm)).mul (ideleClassNormTwist ψ s).continuous
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hi : Integrable H (ideleClassTamagawaMeasure F) :=
    hH.integrable_of_hasCompactSupport (φ.property.2.mul_right.mul_right)
  let j (v : ℝ≥0ˣ × C₁) := σ v.1 * v.2.val
  have hjc : Continuous j := ((σ).continuous.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let mK : MeasurableSpace C₁ := Subtype.instMeasurableSpace
  have hO : @OpensMeasurableSpace C₁ _ mK := Subtype.opensMeasurableSpace (α := C𝔽) _
  have hPO : @OpensMeasurableSpace (ℝ≥0ˣ × C₁) _ (@Prod.instMeasurableSpace _ _ _ mK) :=
    @Prod.opensMeasurableSpace ℝ≥0ˣ C₁ _ _ _ _ mK hO _
  have hj : @Measurable _ _ (@Prod.instMeasurableSpace _ _ _ mK) _ j :=
    @Continuous.measurable _ _ _ (@Prod.instMeasurableSpace _ _ _ mK) hPO _ _ _ j hjc
  have hs : RightInverse σ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  have hprod := classTamagawa_normProduct (fun t ↦ σ t) (σ).continuous hs
  rw [← hprod] at hi
  change ∫ g, H g ∂ideleClassTamagawaMeasure F = _
  rw [← hprod, integral_map hj.aemeasurable hH.aestronglyMeasurable]
  have hi' : Integrable (H ∘ j) (positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)) :=
    (integrable_map_measure hH.aestronglyMeasurable hj.aemeasurable).mp hi
  refine (integral_prod (fun z ↦ H (j z)) hi').trans ?_
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hE : positiveRealHaar = volume.map E := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext y
    exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
  rw [hE, E.isClosedEmbedding.measurableEmbedding.integral_map]
  rw [introTraceMellin, mellin, ← integral_comp_exp]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  have hx : ((E x).val : ℝ) = Real.exp x := rfl
  have hinner (u : C₁) : H (j (E x, u)) =
      φ.val (u.val * σ (radialExponential (Multiplicative.ofAdd x))) * (ψ u.val : ℂ) *
       (b (Real.exp x) * ((Real.exp x : ℝ) : ℂ) ^ s) := by
    have hn : ideleClassNorm F (σ (E x) * u.val) = E x := by
      rw [map_mul, hs, MonoidHom.mem_ker.mp u.property, mul_one]
    change φ.val (σ (E x) * u.val) * b (_) *
      ((ψ (σ (E x) * u.val) : ℂ) * (N(σ (E x) * u.val) : ℂ) ^ s) = _
    rw [hn, hx, map_mul, hψ, one_mul, mul_comm (σ (E x)) u.val]
    have perm (a b c d : ℂ) : a*b*(c*d) = a*c*(b*d) := by ring
    exact perm (φ.val (u.val * σ (E x))) (b (Real.exp x)) (ψ u.val : ℂ) (((Real.exp x : ℝ) : ℂ)^s)
  have he0 : ((Real.exp x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
  have he : ((Real.exp x : ℝ) : ℂ)^s = ((Real.exp x : ℝ) : ℂ)^(s-1) * (Real.exp x : ℝ) := by
    calc _ = ((Real.exp x : ℝ) : ℂ)^((s-1)+1) := by rw [sub_add_cancel]
         _ = _ := by rw [Complex.cpow_add _ _ he0, Complex.cpow_one]
  refine (integral_congr_ae (.of_forall hinner)).trans ?_
  rw [integral_mul_const]
  change p x * (b (Real.exp x) * _) = _
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul, he]
  ring

end RiemannMasullo.StripNuclearity
end

section
open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "U" => PontryaginDual C𝔽
local notation "N(" g ")" => ((ideleClassNorm F g).val : ℝ)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ
local notation "σ" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

/-- For a compact idèle-class test vanishing on the norm-one classes, the residual of a
shrinking cutoff tends to zero in the absolute sum of the global Mellin evaluations on
the completed Hecke divisors, simultaneously across all angular components and any
varying selection of zeros. -/
private theorem summable_tendsto_idelic_hecke_zero_cutoff_residual
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ k : C₁, φ.val k.val = 0)
    (χ : X →* U) (hχ : IsSpectralBasepointChoice χ) (hr : ∀ ξ t, χ ξ (σ t) = 1)
    (b : ℝ → ℂ) (hb : ContDiff ℝ ∞ b) (hsb : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hbD : ∀ j : ℕ, j ≤ 2 → ∀ x, ‖iteratedDeriv j b x‖ ≤ Q)
    (win : ℕ → Set ((_ : X) × ℂ)) :
    (∀ n : ℕ, Summable (fun pair : (_ : X) × ℂ ↦ (win n).indicator (fun pair ↦
      ‖(((D(χ pair.1) pair.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, φ.val g *
        b (((n : ℝ) + 4) * (N(g) - 1)) * ideleClassNormTwist (χ pair.1) (pair.2 - 1/2) g
          ∂ideleClassTamagawaMeasure F‖) pair)) ∧
    Tendsto (fun n ↦ ∑' pair : (_ : X) × ℂ, (win n).indicator (fun pair ↦
      ‖(((D(χ pair.1) pair.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, φ.val g *
        b (((n : ℝ) + 4) * (N(g) - 1)) * ideleClassNormTwist (χ pair.1) (pair.2 - 1/2) g
          ∂ideleClassTamagawaMeasure F‖) pair) atTop (𝓝 0) := by
  let μ := normOneIdeleClassTamagawaMeasure F
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have h := summable_tendsto_hecke_angular_zero_cutoff_residual φ hφ μ χ hχ b hb hsb hQ hbD win
  let M (n : ℕ) (pair : (_ : X) × ℂ) := (win n).indicator (fun pair ↦
      ‖(((D(χ pair.1) pair.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, φ.val g *
        b (((n : ℝ) + 4) * (N(g) - 1)) * ideleClassNormTwist (χ pair.1) (pair.2 - 1/2) g
          ∂ideleClassTamagawaMeasure F‖) pair
  let P (ξ : X) (t : ℝ) := ∫ k : C₁, φ.val (k.val * σ (radialExponential (Multiplicative.ofAdd t))) *
      (ξ k : ℂ) ∂μ
  let A (n : ℕ) (pair : (_ : X) × ℂ) := (win n).indicator (fun q ↦
    ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * introTraceMellin
      (fun r ↦ P q.1 (Real.log r) * b (((n : ℝ)+4)*(r-1))) (q.2 - 1/2)‖) pair
  have equal (n : ℕ) (q : (_ : X) × ℂ) : A n q = M n q := by
    dsimp only [A, M]
    by_cases hq : q ∈ win n
    case neg => simp only [Set.indicator_of_notMem hq]
    simp only [Set.indicator_of_mem hq]
    let cutoff (r : ℝ) := b (((n : ℝ) + 4) * (r-1))
    have hcont : Continuous cutoff := hb.continuous.comp (continuous_const.mul (continuous_id.sub continuous_const))
    have eq := ideleClass_radial_cutoff_mellin φ (χ q.1) (hr q.1) cutoff hcont (q.2 - 1/2)
    have he (u : C₁) : χ q.1 u.val = q.1 u :=
      DFunLike.congr_fun (hχ q.1) u
    simpa only [he] using congrArg (fun v : ℂ ↦ ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * v‖) eq.symm
  refine ⟨fun n ↦ (h.1 n).congr (equal n), ?_⟩
  exact h.2.congr' (.of_forall fun n ↦ tsum_congr (equal n))

end RiemannMasullo.StripNuclearity
end

section
open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology
open Classical
namespace RiemannMasullo
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "N(" g ")" => (((ideleClassNorm F) (g : C𝔽)).val : ℝ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v

private theorem introTrace_cutoff_pointwise (b : ℝ → ℂ) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {r : ℝ} (hr : r ≠ 1) : ∀ᶠ n : ℕ in atTop, b (((n : ℝ) + 4) * (r - 1)) = 0 := by
  obtain ⟨k : ℕ, hk⟩ := exists_nat_ge (1 / |r-1|)
  filter_upwards [eventually_ge_atTop k] with n hn
  have hp := abs_pos.mpr (sub_ne_zero.mpr hr)
  have hk' : 1 ≤ (n : ℝ) * |r-1| := (div_le_iff₀ hp).mp (hk.trans (by exact_mod_cast hn))
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have hm' := abs_lt.mpr (hs hm)
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ n + 4)] at hm'
  nlinarith

private theorem introTrace_finite_norm_gap (v : V) (u : (v.adicCompletion F)ˣ) :
    ‖u.val‖ = 1 ∨ 1/2 ≤ |‖u.val‖ - 1| := by
  let q := (v.asIdeal.absNorm : ℝ)
  let k := WithZero.log (Valued.v u.val)
  have hq : (2:ℝ) ≤ q := by
    change (2:ℝ) ≤ (v.asIdeal.absNorm : ℝ)
    exact_mod_cast (show 2 ≤ v.asIdeal.absNorm from HeightOneSpectrum.one_lt_absNorm v)
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hN : ‖u.val‖ = q ^ k := norm_adicCompletion_eq_zpow F v u.ne_zero
  rcases lt_trichotomy k 0 with hk | hk | hk
  · right
    have hh := zpow_le_zpow_right₀ hq1 (show k ≤ -1 by omega)
    rw [zpow_neg_one] at hh
    have h' : q⁻¹ ≤ 1/2 := by simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 2) hq
    rw [hN, abs_of_nonpos (by linarith : q ^ k - 1 ≤ 0)]
    linarith
  · left
    simp [hN, hk]
  · right
    have hh := zpow_le_zpow_right₀ hq1 (show (1:ℤ) ≤ k by omega)
    rw [zpow_one] at hh
    rw [hN, abs_of_nonneg (by linarith : 0 ≤ q^k-1)]
    linarith

/-- Paper: §1.4.6, p. 30. The shrinking norm-one residual vanishes identically on
the image of every finite completion. This gives exact equality of the finite-place
Connes–Weil terms at every cutoff. -/
theorem introTrace_cutoff_finite_restriction (φ : D𝔽)
    (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1) (n : ℕ)
    (v : V) (u : (v.adicCompletion F)ˣ) :
    φ.val (finiteClass(v) u) * b (((n : ℝ) + 4) * (N(finiteClass(v) u) - 1)) = 0 := by
  have hN : N(finiteClass(v) u) = ‖u.val‖ := by rw [ideleClassNorm_ofAdicCompletion]; rfl
  rcases introTrace_finite_norm_gap v u with hu | hu
  · have hm : ideleClassNorm F (finiteClass(v) u) = 1 := by
      apply Units.ext
      apply NNReal.eq
      exact hN.trans hu
    rw [hφ ⟨_, hm⟩, zero_mul]
  · apply mul_eq_zero_of_right
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hh := abs_lt.mpr (hs h)
    rw [abs_mul, hN, abs_of_nonneg (by positivity : (0:ℝ) ≤ n + 4)] at hh
    have hn : 0 ≤ (n:ℝ) * |‖u.val‖ - 1| := by positivity
    linarith [show ((n:ℝ)+4)*|‖u.val‖-1| = (n:ℝ)*|‖u.val‖-1|+4*|‖u.val‖-1| by ring]

private theorem introTrace_archimedean_test_kernel (w : InfinitePlace F)
    (f : BruhatCompactSupport w.Completionˣ) (hf : f.val 1 = 0) :
    let K := fun u : w.Completionˣ ↦ f.val u * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
      ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
    Integrable K (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      infiniteConnesWeilPrincipalValue w f =
        (if w.IsReal then (1/2:ℂ) else 1/(2*(Real.pi:ℂ))) *
          ∫ u, K u ∂infiniteLocalMultiplicativeTamagawaMeasure F w := by
  intro K
  by_cases hr : w.IsReal
  · simpa only [K, hr.mult_eq_one, pow_one, ite_eq_left hr] using
      And.intro (introTraceArchimedean_real_integrable w hr f hf)
        (realConnesWeilPrincipalValue_of_apply_one_zero w hr f hf)
  · simpa only [K, ite_eq_right hr] using
      introTrace_characterTrace_complex_place w (InfinitePlace.not_isReal_iff_isComplex.mp hr) f hf

private theorem introTrace_cutoff_integral_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (R : X → ℝ) (hR : Measurable R) (K : X → ℂ) (hK : Integrable K μ)
    (hK1 : ∀ x, R x = 1 → K x = 0) (b : ℝ → ℂ) (hb : Measurable b)
    (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1) {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) :
    Tendsto (fun n : ℕ ↦ ∫ x, ‖K x * b (((n:ℝ)+4)*(R x-1))‖ ∂μ) atTop (𝓝 0) := by
  let s (n : ℕ) (x : X) := b (((n:ℝ)+4)*(R x-1))
  have hsm (n : ℕ) : Measurable (s n) := hb.comp (measurable_const.mul (hR.sub measurable_const))
  have hcon := tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖K x‖ * Q)
    (μ := μ) (l := atTop) (F := fun n x ↦ ‖K x * s n x‖) (f := fun _ ↦ (0:ℝ))
    (.of_forall fun n ↦ (hK.aestronglyMeasurable.mul (hsm n).aestronglyMeasurable).norm)
    (.of_forall fun n ↦ .of_forall fun x ↦ by
      simp only [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
      exact mul_le_mul_of_nonneg_left (hQ _) (norm_nonneg _))
    (hK.norm.mul_const Q) (.of_forall fun x ↦ ?_)
  · simpa only [s, integral_zero] using hcon
  · by_cases hx : R x = 1
    · simp [hK1 x hx]
    · apply tendsto_const_nhds.congr'
      filter_upwards [introTrace_cutoff_pointwise b hs hx] with n hn
      simp [s, hn]


/-- Paper: §1.4.6, p. 30. At every archimedean place the shrinking norm-one
residual tends to zero in the integral of the absolute value of the normalized
local kernel. The corresponding local Connes–Weil principal values converge. -/
theorem introTrace_cutoff_archimedean (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (v : ℕ → D𝔽)
    (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n:ℝ)+4)*(N(g)-1))))
    (w : InfinitePlace F) :
    let R := (idelicExplicitFormula_infiniteTestMap (F := F) w).choose
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
    let K := fun (f : D𝔽) (u : w.Completionˣ) ↦
      f.val (archClass(w) u) * (Real.sqrt (‖u.val‖ ^ w.mult) : ℂ) /
        ((‖1 - u.val‖ ^ w.mult : ℝ) : ℂ)
    Tendsto (fun n ↦ ∫ u, ‖K φ u - K (v n) u‖ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ infiniteConnesWeilPrincipalValue w (R (v n))) atTop
        (𝓝 (infiniteConnesWeilPrincipalValue w (R φ))) := by
  intro R μ K
  let : MeasurableSpace w.Completion := instMeasurableSpaceCompletion_riemannMasullo F w
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let Nw := fun u : w.Completionˣ ↦ ‖u.val‖ ^ w.mult
  have hN (u : w.Completionˣ) : N(archClass(w) u) = Nw u := by
    rw [ideleClassNorm_ofCompletion]; rfl
  have hR (f : D𝔽) (u : w.Completionˣ) : (R f).val u = f.val (archClass(w) u) :=
    (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec f u
  have hφ1 : φ.val 1 = 0 := hφ 1
  have hPV (f : D𝔽) (hf : f.val 1 = 0) : Integrable (K f) μ ∧
      infiniteConnesWeilPrincipalValue w (R f) =
        (if w.IsReal then (1/2:ℂ) else 1/(2*(Real.pi:ℂ))) * ∫ u, K f u ∂μ := by
    simpa only [K, hR] using introTrace_archimedean_test_kernel w (R f) (by simp [hR, hf])
  have hK1 (u : w.Completionˣ) (hu : Nw u = 1) : K φ u = 0 := by
    have hmem : ideleClassNorm F (archClass(w) u) = 1 := by
      apply Units.ext
      apply NNReal.eq
      exact (hN u).trans hu
    simp only [K, hφ ⟨_, hmem⟩, zero_mul, zero_div]
  have hEq (n : ℕ) (u : w.Completionˣ) : K φ u - K (v n) u =
      K φ u * b (((n:ℝ)+4)*(Nw u-1)) := by
    simp only [K, hv, hN]
    ring
  have h := introTrace_cutoff_integral_norm μ Nw (by dsimp [Nw]; fun_prop) _ (hPV φ hφ1).1
    hK1 b hb hs hQ
  have habs : Tendsto (fun n ↦ ∫ u, ‖K φ u - K (v n) u‖ ∂μ) atTop (𝓝 0) := by
    simpa only [hEq] using h
  refine ⟨habs, ?_⟩
  have h0 : Tendsto (fun n ↦ ∫ u, K φ u - K (v n) u ∂μ) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun n ↦ norm_integral_le_integral_norm _) habs)
  have hV (n : ℕ) := hPV (v n) (by simp [hv, hφ1])
  have hV' := (tendsto_const_nhds (x := ∫ u, K φ u ∂μ)).sub h0
  simp only [integral_sub (hPV φ hφ1).1 (hV _).1, sub_sub_cancel, sub_zero] at hV'
  simpa only [(hPV φ hφ1).2, fun n ↦ (hV n).2] using
    hV'.const_mul (if w.IsReal then (1/2:ℂ) else 1/(2*(Real.pi:ℂ)))

/-- Paper: §1.4.6, p. 30. The Mellin residual of the shrinking cutoff converges
absolutely at any fixed quasi-character. In particular this applies at both
polar characters in the geometric trace formula. -/
theorem introTrace_cutoff_mellin (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (c : C𝔽 → ℂ) (hc : Continuous c)
    (v : ℕ → D𝔽) (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n:ℝ)+4)*(N(g)-1)))) :
    Tendsto (fun n ↦ ∫ g, ‖(φ.val g - (v n).val g) * c g‖ ∂ideleClassTamagawaMeasure F)
      atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ g, (v n).val g * c g ∂ideleClassTamagawaMeasure F) atTop
        (𝓝 (∫ g, φ.val g * c g ∂ideleClassTamagawaMeasure F)) := by
  let K (f : D𝔽) (g : C𝔽) := f.val g * c g
  have hI (f : D𝔽) : Integrable (K f) (ideleClassTamagawaMeasure F) :=
    ((schwartzBruhat_continuous (⟨f.val, bruhatCompactSupport_mem_schwartz f.property⟩ :
      SchwartzBruhat C𝔽)).mul hc).integrable_of_hasCompactSupport f.property.2.mul_right
  have hN : Measurable fun g : C𝔽 ↦ N(g) := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable
  have h1 (g : C𝔽) (hg : N(g) = 1) : K φ g = 0 := by
    have hm : ideleClassNorm F g = 1 := Units.ext (NNReal.eq hg)
    exact mul_eq_zero_of_left (hφ ⟨g, hm⟩) _
  have habs := introTrace_cutoff_integral_norm _ _ hN _ (hI φ) h1 b hb hs hQ
  have hEq (n : ℕ) (g : C𝔽) : (φ.val g - (v n).val g) * c g =
      K φ g * b (((n:ℝ)+4)*(N(g)-1)) := by rw [hv]; dsimp only [K]; ring
  refine ⟨by simpa only [hEq] using habs, ?_⟩
  have h0 : Tendsto (fun n ↦ ∫ g, K φ g - K (v n) g ∂ideleClassTamagawaMeasure F) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ norm_integral_le_integral_norm _)
    simpa only [K, ← sub_mul, hEq] using habs
  have h := (tendsto_const_nhds (x := ∫ g, K φ g ∂ideleClassTamagawaMeasure F)).sub h0
  simpa only [integral_sub (hI φ) (hI _), sub_sub_cancel, sub_zero] using h

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

open Classical in
/-- Paper: §1.4.6, p. 30, and Theorem 12.5.1.1, pp. 519–520. For a compact Bruhat
test vanishing on the norm-one subgroup, removing a shrinking neighborhood of that
subgroup preserves every finite-place term exactly. The two polar Mellin terms and
the normalized archimedean principal values converge to those of the original test,
so the entire geometric side converges. -/
theorem introTrace_norm_one_geometric_cutoff (φ : D𝔽) (hφ : ∀ g : (ideleClassNorm F).ker, φ.val g = 0)
    (b : ℝ → ℂ) (hb : Measurable b) (hs : tsupport b ⊆ Ioo (-1 : ℝ) 1)
    {Q : ℝ} (hQ : ∀ x, ‖b x‖ ≤ Q) (v : ℕ → D𝔽)
    (hv : ∀ n g, (v n).val g = φ.val g * (1 - b (((n:ℝ)+4)*(N(g)-1)))) :
    let pole (f : D𝔽) (s : ℂ) := ∫ g, f.val g * ideleClassNormTwist 1 s g ∂ideleClassTamagawaMeasure F
    let arch (f : D𝔽) := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
      ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose f)
    let prime (f : D𝔽) (p : V) := ((Real.log (p.asIdeal.absNorm : ℝ) /
      ((finiteLocalMultiplicativeTamagawaMeasure F p) (p.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue p 1 ((idelicExplicitFormula_finiteTestMap (F := F) p).choose f)
    let geom (f : D𝔽) := pole f (1/2) + pole f (-1/2) -
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * (arch f + ∑' p, prime f p)
    (∀ n p, prime (v n) p = prime φ p) ∧ Tendsto (geom ∘ v) atTop (𝓝 (geom φ)) := by
  intro pole arch prime geom
  have hP (n : ℕ) (p : V) : prime (v n) p = prime φ p := by
    let R := (idelicExplicitFormula_finiteTestMap (F := F) p).choose
    have he (f : D𝔽) (u : (p.adicCompletion F)ˣ) :
        (R f).val u = f.val (finiteClass(p) u) :=
      (idelicExplicitFormula_finiteTestMap (F := F) p).choose_spec f u
    have hr : R (v n) = R φ := by
      apply Subtype.ext
      funext u
      rw [he, he, hv, mul_sub, mul_one, introTrace_cutoff_finite_restriction φ hφ b hs n p u, sub_zero]
    change _ * finiteConnesWeilPrincipalValue p 1 (R (v n)) =
      _ * finiteConnesWeilPrincipalValue p 1 (R φ)
    rw [hr]
  have hPole (s : ℂ) : Tendsto (fun n ↦ pole (v n) s) atTop (𝓝 (pole φ s)) :=
    (introTrace_cutoff_mellin φ hφ b hb hs hQ _ (ideleClassNormTwist (F := F) 1 s).continuous v hv).2
  have hA : Tendsto (fun n ↦ arch (v n)) atTop (𝓝 (arch φ)) := by
    apply tendsto_finsetSum
    intro w _
    exact (introTrace_cutoff_archimedean φ hφ b hb hs hQ v hv w).2
  refine ⟨hP, ?_⟩
  have hfin (n : ℕ) : (∑' p, prime (v n) p) = ∑' p, prime φ p := tsum_congr (hP n)
  change Tendsto (fun n ↦ geom (v n)) atTop (𝓝 (geom φ))
  simpa only [geom, hfin] using
    ((hPole (1/2)).add (hPole (-1/2))).sub ((hA.add_const (∑' p, prime φ p)).const_mul
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ))

end RiemannMasullo
end

section
open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "U" => PontryaginDual C𝔽
local notation "N(" g ")" => ((ideleClassNorm F g).val : ℝ)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ
local notation "σ" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

/-- For the norm-one extension in §1.4.6, p. 30, a single sequence of tests supported away
from norm one preserves every finite-place contribution and converges in the full geometric
side and in the absolute sum over all angular characters and completed Hecke zeros. -/
theorem exists_bruhat_test_approximation_spectral_geometric (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ k : C₁, φ.val k.val = 0) :
    let pole (f : BruhatCompactSupport C𝔽) (s : ℂ) := ∫ g, f.val g * ideleClassNormTwist 1 s g ∂ideleClassTamagawaMeasure F
    let arch (f : BruhatCompactSupport C𝔽) := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
      ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose f)
    let prime (f : BruhatCompactSupport C𝔽) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ((Real.log (p.asIdeal.absNorm : ℝ) /
      ((finiteLocalMultiplicativeTamagawaMeasure F p) (p.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue p 1 ((idelicExplicitFormula_finiteTestMap (F := F) p).choose f)
    let geom (f : BruhatCompactSupport C𝔽) := pole f (1/2) + pole f (-1/2) -
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * (arch f + ∑' p, prime f p)
    ∃ v : ℕ → BruhatCompactSupport C𝔽,
      (∀ n, tsupport (v n).val ⊆ tsupport φ.val ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ g : C𝔽, |N(g)-1| < ε → (v n).val g = 0) ∧
      ((∀ n p, prime (v n) p = prime φ p) ∧ Tendsto (geom ∘ v) atTop (𝓝 (geom φ))) ∧
      ∀ (χ : X →* U), IsSpectralBasepointChoice χ → (∀ ξ t, χ ξ (σ t) = 1) →
        ∀ (win : ℕ → Set ((_ : X) × ℂ)),
          (∀ n : ℕ, Summable (fun q : (_ : X) × ℂ ↦ (win n).indicator (fun q ↦
            ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, (φ.val g - (v n).val g) *
              ideleClassNormTwist (χ q.1) (q.2 - 1/2) g ∂ideleClassTamagawaMeasure F‖) q)) ∧
          Tendsto (fun n ↦ ∑' q : (_ : X) × ℂ, (win n).indicator (fun q ↦
            ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, (φ.val g - (v n).val g) *
              ideleClassNormTwist (χ q.1) (q.2 - 1/2) g ∂ideleClassTamagawaMeasure F‖) q)
            atTop (𝓝 0) := by
  classical
  intro pole arch prime geom
  let a : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  let b (t : ℝ) : ℂ := (a t : ℝ)
  have hb : ContDiff ℝ ∞ b := Complex.ofRealCLM.contDiff.comp a.contDiff
  have hbc : HasCompactSupport b := a.hasCompactSupport.comp_left Complex.ofReal_zero
  have hbs : tsupport b ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have ht := tsupport_comp_subset Complex.ofReal_zero a hx
    rw [a.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    change |x| ≤ 1/2 at ht
    exact ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩
  let c (n : ℕ) : ℝ := (n : ℝ) + 4
  have hc (n : ℕ) : 0 < c n := by dsimp [c]; positivity
  let l := ideleClassLogNorm F
  let h (n : ℕ) (t : ℝ) := 1 - b (c n * (Real.exp t - 1))
  have hh (n : ℕ) : ContDiff ℝ ∞ (h n) :=
    contDiff_const.sub (hb.comp (contDiff_const.mul (Real.contDiff_exp.sub contDiff_const)))
  have hsm (n : ℕ) : IsBruhatSmooth (fun g : C𝔽 ↦ φ.val g * h n (l g).toAdd) :=
    IsBruhatSmooth.mul_comp_realHom ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1) l
      (continuous_ideleClassLogNorm (F := F)) (hh n)
  let v (n : ℕ) : BruhatCompactSupport C𝔽 := ⟨_,
    (mem_bruhatSmoothSubmodule_iff _).mpr (hsm n), φ.property.2.mul_right⟩
  have hv (n : ℕ) (g : C𝔽) : (v n).val g = φ.val g * (1 - b (c n * (N(g)-1))) := by
    change φ.val g * (1 - b (c n * (Real.exp (Real.log (N(g))) - 1))) = _
    rw [Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hbound (x : ℝ) : ‖b x‖ ≤ 1 := by
    simpa only [b, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ a x from a.nonneg)] using (show a x ≤ 1 from a.le_one)
  have hgeo := introTrace_norm_one_geometric_cutoff φ hφ b hb.continuous.measurable hbs hbound v hv
  refine ⟨v, fun n ↦ ⟨tsupport_mul_subset_left, 1/4 / c n, div_pos (by norm_num) (hc n), ?_⟩, hgeo, ?_⟩
  · intro g hg
    have hsmall : |c n * (N(g)-1)| < 1/4 := by
      rw [abs_mul, abs_of_pos (hc n), mul_comm]
      exact (lt_div_iff₀ (hc n)).mp hg
    have hinside : c n * (N(g)-1) ∈ Metric.closedBall (0 : ℝ) a.rIn := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hsmall.le
    rw [hv]
    simp only [b, a.one_of_mem_closedBall hinside, Complex.ofReal_one, sub_self, mul_zero]
  · intro χ hχ hr win
    obtain ⟨Q, hQ, hQD⟩ := hbc.exists_bound_iteratedFDeriv hb 2
    simp_rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hQD
    have hlim := summable_tendsto_idelic_hecke_zero_cutoff_residual φ hφ χ hχ hr b hb hbs hQ hQD win
    have eq (g : C𝔽) (n : ℕ) : φ.val g - (v n).val g = φ.val g * b (c n * (N(g)-1)) := by rw [hv]; ring
    simpa only [eq, c] using hlim


end RiemannMasullo.StripNuclearity
end
section
open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff
namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
private theorem exteriorZeros_exists_inverse_test (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ g : C𝔽, ψ.val g = φ.val g⁻¹ := by
  obtain ⟨m, _, hm, hms⟩ := exists_ideleClassModulation F
  have hdecay := bruhatCompactSupport_le_modulatedExponentialDecay m univ hm hms φ.property
  have hweight : modulationWeight m 0 φ.val ∈ schwartzBruhatSubmodule C𝔽 :=
    (Submodule.mem_iInf _).mp hdecay ⟨0, mem_univ _⟩
  have hid : modulationWeight m 0 φ.val = φ.val := by
    funext g
    simp [modulationWeight, LinearMap.mulLeft_apply]
  let i : C𝔽 ≃ₜ* C𝔽 := {
    toFun := Inv.inv, invFun := Inv.inv, left_inv := inv_inv, right_inv := inv_inv
    map_mul' := fun x y ↦ by simp [mul_comm]
    continuous_toFun := continuous_inv, continuous_invFun := continuous_inv }
  let f : SchwartzBruhat C𝔽 := ⟨φ.val ∘ i, schwartzBruhat_mem_comp_equiv i (hid ▸ hweight)⟩
  exact ⟨⟨φ.val ∘ i, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth f),
    φ.property.2.comp_homeomorph (Homeomorph.inv _)⟩, fun _ ↦ rfl⟩

/-- A test vanishing on a neighborhood of norm one is the sum of a positive-side
test and the inversion pullback of another positive-side test, as required in §1.4.6. -/
theorem exists_above_norm_one_test_split (v : BruhatCompactSupport C𝔽) {ε : ℝ} (hε : 0 < ε)
    (hv : ∀ g : C𝔽, |((ideleClassNorm F g).val : ℝ) - 1| < ε → v.val g = 0) :
    ∃ p q : BruhatCompactSupport C𝔽,
      (tsupport p.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) ∧
      (tsupport q.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) ∧
      ∀ g : C𝔽, v.val g = p.val g + q.val g⁻¹ := by
  let N (g : C𝔽) := ((ideleClassNorm F g).val : ℝ)
  have hN : Continuous N :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hpN (g : C𝔽) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  let a (x : ℝ) : ℂ := (Real.smoothTransition ((Real.exp x - 1) / ε) : ℝ)
  have ha : ContDiff ℝ (∞) a := Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp ((Real.contDiff_exp.sub contDiff_const).div_const ε))
  let u (g : C𝔽) := v.val g * a (ideleClassLogNorm F g).toAdd
  have hu : IsBruhatSmooth u := IsBruhatSmooth.mul_comp_realHom
    ((mem_bruhatSmoothSubmodule_iff _).mp v.property.1) (ideleClassLogNorm F)
    continuous_ideleClassLogNorm ha
  let p : BruhatCompactSupport C𝔽 := ⟨u, (mem_bruhatSmoothSubmodule_iff _).mpr hu, v.property.2.mul_right⟩
  have hp (g : C𝔽) : p.val g = v.val g * (Real.smoothTransition ((N g - 1) / ε) : ℝ) := by
    change v.val g * (Real.smoothTransition ((Real.exp (Real.log (N g)) - 1) / ε) : ℝ) = _
    rw [Real.exp_log (hpN g)]
  let r := v - p
  have hr (g : C𝔽) : r.val g = v.val g - p.val g := rfl
  have hhi : tsupport p.val ⊆ {g : C𝔽 | 1 + ε / 2 ≤ N g} := by
    refine closure_minimal ?_ (isClosed_le continuous_const hN)
    intro g hg
    change 1 + ε / 2 ≤ N g
    by_contra! h
    apply hg
    rw [hp]
    rcases le_or_gt (N g) 1 with hn | hn
    · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le),
        Complex.ofReal_zero, mul_zero]
    · have hm : |N g - 1| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
      rw [hv g hm, zero_mul]
  have hlo : tsupport r.val ⊆ {g : C𝔽 | N g ≤ 1 - ε / 2} := by
    refine closure_minimal ?_ (isClosed_le hN continuous_const)
    intro g hg
    change N g ≤ 1 - ε / 2
    by_contra! h
    apply hg
    rw [hr, hp]
    rcases le_or_gt (1 + ε) (N g) with hn | hn
    · rw [Real.smoothTransition.one_of_one_le ((le_div_iff₀ hε).2 (by linarith)),
        Complex.ofReal_one, mul_one, sub_self]
    · have hm : |N g - 1| < ε := abs_lt.mpr ⟨by linarith, by linarith⟩
      rw [hv g hm, zero_mul, sub_self]
  obtain ⟨q, hq⟩ := exteriorZeros_exists_inverse_test r
  refine ⟨p, q, ?_, ?_, ?_⟩
  · intro g hg
    have h : 1 + ε / 2 ≤ N g := hhi hg
    change 1 < N g
    linarith
  · have hcomp : q.val = r.val ∘ (Homeomorph.inv C𝔽) := funext hq
    rw [hcomp, tsupport_comp_eq_preimage]
    intro g hg
    have hm : N g⁻¹ ≤ 1 - ε / 2 := hlo hg
    have hi : N g⁻¹ = (N g)⁻¹ := by simp [N, map_inv]
    rw [hi] at hm
    change 1 < N g
    by_contra! h
    have : 1 ≤ (N g)⁻¹ := (one_le_inv₀ (hpN g)).mpr h
    linarith
  · intro g
    rw [hq, inv_inv, hr]
    abel

end RiemannMasullo
end

section
open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "U" => PontryaginDual C𝔽
local notation "N(" g ")" => ((ideleClassNorm F g).val : ℝ)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ
local notation "σ" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

/-- The positive-support tests on p. 495 suffice, together with their inverses, for numerical approximation on both sides of the normalized trace formula (§1.4.6, p. 30). -/
theorem exists_above_norm_one_approximation_spectral_geometric (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ k : C₁, φ.val k.val = 0) :
    let pole (f : BruhatCompactSupport C𝔽) (s : ℂ) := ∫ g, f.val g * ideleClassNormTwist 1 s g ∂ideleClassTamagawaMeasure F
    let arch (f : BruhatCompactSupport C𝔽) := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w
      ((idelicExplicitFormula_infiniteTestMap (F := F) w).choose f)
    let prime (f : BruhatCompactSupport C𝔽) (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := ((Real.log (p.asIdeal.absNorm : ℝ) /
      ((finiteLocalMultiplicativeTamagawaMeasure F p) (p.adicCompletionIntegers F).units).toReal : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue p 1 ((idelicExplicitFormula_finiteTestMap (F := F) p).choose f)
    let geom (f : BruhatCompactSupport C𝔽) := pole f (1/2) + pole f (-1/2) -
      (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * (arch f + ∑' p, prime f p)
    ∃ v p q : ℕ → BruhatCompactSupport C𝔽,
      (∀ n, tsupport (p n).val ⊆ {g : C𝔽 | 1 < N(g)} ∧
        tsupport (q n).val ⊆ {g : C𝔽 | 1 < N(g)} ∧
        ∀ g : C𝔽, (v n).val g = (p n).val g + (q n).val g⁻¹) ∧
      (∀ n, tsupport (v n).val ⊆ tsupport φ.val ∧
        ∃ ε : ℝ, 0 < ε ∧ ∀ g : C𝔽, |N(g)-1| < ε → (v n).val g = 0) ∧
      ((∀ n p, prime (v n) p = prime φ p) ∧ Tendsto (geom ∘ v) atTop (𝓝 (geom φ))) ∧
      ∀ (χ : X →* U), IsSpectralBasepointChoice χ → (∀ ξ t, χ ξ (σ t) = 1) →
        ∀ (win : ℕ → Set ((_ : X) × ℂ)),
          (∀ n : ℕ, Summable (fun q : (_ : X) × ℂ ↦ (win n).indicator (fun q ↦
            ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, (φ.val g - (v n).val g) *
              ideleClassNormTwist (χ q.1) (q.2 - 1/2) g ∂ideleClassTamagawaMeasure F‖) q)) ∧
          Tendsto (fun n ↦ ∑' q : (_ : X) × ℂ, (win n).indicator (fun q ↦
            ‖(((D(χ q.1) q.2).toNat : ℝ) : ℂ) * ∫ g : C𝔽, (φ.val g - (v n).val g) *
              ideleClassNormTwist (χ q.1) (q.2 - 1/2) g ∂ideleClassTamagawaMeasure F‖) q)
            atTop (𝓝 0) := by
  classical
  intro pole arch prime geom
  obtain ⟨v, hv, hgeom, hspec⟩ := exists_bruhat_test_approximation_spectral_geometric φ hφ
  choose p q hpair using fun n ↦ exists_above_norm_one_test_split (v n)
    (hv n).2.choose_spec.1 (hv n).2.choose_spec.2
  exact ⟨v, p, q, hpair, hv, hgeom, hspec⟩

end RiemannMasullo.StripNuclearity
end

section
open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology ContDiff

namespace RiemannMasullo.StripNuclearity

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassHaarMeasureSec1
set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "X" => PontryaginDual C₁
local notation "U" => PontryaginDual C𝔽
local notation "N(" g ")" => ((ideleClassNorm F g).val : ℝ)
local notation "D(" ψ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ
local notation "σ" => (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
  IdeleGroup (𝓞 F) F →ₜ* C𝔽).comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

private theorem window_divisor_reflection (χ : PontryaginDual C𝔽) (z : ℂ) :
    D(χ⁻¹) (1-z) = D(χ) z := by
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL hl hD hd
  have he : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1-s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1-z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := continuedCompletedHeckeL χ⁻¹) (show AnalyticAt ℂ (fun s : ℂ ↦ 1-s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1-s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1-s)) = ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at he
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← he]

private theorem window_twist_inverse (χ : U) (w : ℂ) (g : C𝔽) : ideleClassNormTwist χ⁻¹ (-w) g = ideleClassNormTwist χ w g⁻¹ := by
    change (((χ⁻¹ g : Circle)) : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-w) =
      ((χ g⁻¹ : Circle) : ℂ) * ((((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)) : ℂ) ^ w
    have hp : 0 < ((ideleClassNorm F g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have harg : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hp.le]
      exact Real.pi_ne_zero.symm
    rw [map_inv χ g, map_inv (ideleClassNorm F) g, Units.val_inv_eq_inv_val, NNReal.coe_inv,
      Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
    rfl

private theorem hasSum_zero_of_approximation {ι : Type*} (f : ι → ℂ) (a : ℕ → ι → ℂ)
    (ha : ∀ n, HasSum (a n) 0) (he : ∀ n, Summable fun i ↦ ‖f i - a n i‖)
    (hl : Tendsto (fun n ↦ ∑' i, ‖f i - a n i‖) atTop (𝓝 0)) : HasSum f 0 := by
  have h (n : ℕ) : HasSum f (∑' i, (f i - a n i)) := by
    have hsum := (he n).of_norm.hasSum.add (ha n)
    simpa only [Pi.add_apply, sub_add_cancel, add_zero] using hsum
  have hb (n : ℕ) : ‖∑' i, f i‖ ≤ ∑' i, ‖f i - a n i‖ := by
    rw [(h n).tsum_eq]
    exact norm_tsum_le_tsum_norm (he n)
  have hzero : ‖∑' i, f i‖ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hl hb
  exact (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))) ▸ (h 0).summable.hasSum

local notation "zeroWeight(" χ ", " q ")" =>
  (((D((χ) (q).1) (q).2).toNat : ℝ) : ℂ)
local notation "windowTerm(" χ ", " f ", " q ")" =>
  zeroWeight(χ, q) * ∫ g : C𝔽, (f : BruhatCompactSupport C𝔽).val g *
    ideleClassNormTwist ((χ) (q).1) ((q).2 - 1/2) g ∂ideleClassTamagawaMeasure F

private theorem window_mellin_integrable (f : BruhatCompactSupport C𝔽) (c : QuasiCharacter C𝔽) :
    Integrable (fun g : C𝔽 ↦ f.val g * c g) (ideleClassTamagawaMeasure F) :=
  ((continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)).mul c.continuous).integrable_of_hasCompactSupport
    f.property.2.mul_right

private theorem hasSum_window_inverse (χ : X →* U) (win : Set ((_ : X) × ℂ))
    (hw : ∀ ξ s, (⟨ξ⁻¹, 1-s⟩ ∈ win ↔ ⟨ξ, s⟩ ∈ win))
    (f r : BruhatCompactSupport C𝔽) (hr : ∀ g : C𝔽, r.val g = f.val g⁻¹)
    (hs : HasSum (win.indicator (fun q ↦ windowTerm(χ, f, q))) 0) :
    HasSum (win.indicator (fun q ↦ windowTerm(χ, r, q))) 0 := by
  classical
  let e : ((_ : X) × ℂ) ≃ ((_ : X) × ℂ) := {
    toFun := fun q ↦ ⟨q.1⁻¹, 1-q.2⟩
    invFun := fun q ↦ ⟨q.1⁻¹, 1-q.2⟩
    left_inv := by rintro ⟨ξ, s⟩; simp
    right_inv := by rintro ⟨ξ, s⟩; simp }
  apply e.hasSum_iff.mp
  convert hs using 1
  funext q
  change win.indicator (fun t ↦ windowTerm(χ, r, t)) ⟨q.1⁻¹, 1-q.2⟩ =
    win.indicator (fun t ↦ windowTerm(χ, f, t)) q
  by_cases hq : q ∈ win
  · rw [Set.indicator_of_mem ((hw q.1 q.2).mpr hq), Set.indicator_of_mem hq]
    dsimp only
    rw [map_inv, window_divisor_reflection, show (1-q.2)-1/2 = -(q.2-1/2) by ring]
    congr 1
    rw [← integral_inv_eq_self _ (ideleClassTamagawaMeasure F)]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    change r.val g⁻¹ * ideleClassNormTwist (χ q.1)⁻¹ (-(q.2-1/2)) g⁻¹ =
      f.val g * ideleClassNormTwist (χ q.1) (q.2-1/2) g
    rw [hr, inv_inv, window_twist_inverse, inv_inv]
  · rw [Set.indicator_of_notMem (fun h ↦ hq ((hw q.1 q.2).mp h)), Set.indicator_of_notMem hq]

/-- For any reflection-invariant selection of Hecke zeros, cancellation on all tests
supported strictly above norm one extends to every test vanishing on the norm-one
classes. The spectral error tends to zero in absolute sum, as required in §1.4.6, p. 30. -/
theorem hasSum_window_zero_of_above_norm_one (χ : X →* U) (hχ : IsSpectralBasepointChoice χ)
    (hr : ∀ ξ t, χ ξ (σ t) = 1) (win : Set ((_ : X) × ℂ))
    (hw : ∀ ξ s, (⟨ξ⁻¹, 1-s⟩ ∈ win ↔ ⟨ξ, s⟩ ∈ win))
    (hpos : ∀ f : BruhatCompactSupport C𝔽, tsupport f.val ⊆ {g : C𝔽 | 1 < N(g)} →
      HasSum (win.indicator (fun q ↦ windowTerm(χ, f, q))) 0)
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ k : C₁, φ.val k.val = 0) :
    HasSum (win.indicator (fun q ↦ windowTerm(χ, φ, q))) 0 := by
  classical
  obtain ⟨v, p, r, hsplit, _, _, hs⟩ := exists_above_norm_one_approximation_spectral_geometric φ hφ
  have hv (n : ℕ) : HasSum (win.indicator (fun q ↦ windowTerm(χ, v n, q))) 0 := by
    let f := v n - p n
    have hinv (g : C𝔽) : f.val g = (r n).val g⁻¹ := by
      change (v n).val g - (p n).val g = _
      rw [(hsplit n).2.2]
      abel
    have hr' := hasSum_window_inverse χ win hw (r n) f hinv (hpos _ (hsplit n).2.1)
    have hp := (hpos _ (hsplit n).1).add hr'
    rw [add_zero] at hp
    convert hp using 1
    funext q
    by_cases hq : q ∈ win
    · simp only [Set.indicator_of_mem hq]
      have e (g : C𝔽) : (v n).val g = (p n).val g + f.val g := by
        change _ = _ + ((v n).val g - (p n).val g)
        abel
      simp only [e, add_mul, integral_add (window_mellin_integrable _ _) (window_mellin_integrable _ _), mul_add]
    · simp [hq]
  apply hasSum_zero_of_approximation _ _ hv
  all_goals
    obtain ⟨hsum, hlim⟩ := hs χ hχ hr (fun _ ↦ win)
    have e (n : ℕ) (q : (_ : X) × ℂ) :
        ‖win.indicator (fun t ↦ windowTerm(χ, φ, t)) q -
          win.indicator (fun t ↦ windowTerm(χ, v n, t)) q‖ =
        win.indicator (fun t ↦ ‖zeroWeight(χ,t) * ∫ g : C𝔽, (φ.val g - (v n).val g) *
          ideleClassNormTwist (χ t.1) (t.2-1/2) g ∂ideleClassTamagawaMeasure F‖) q := by
      by_cases hq : q ∈ win
      · simp only [Set.indicator_of_mem hq, sub_mul,
          integral_sub (window_mellin_integrable _ _) (window_mellin_integrable _ _), mul_sub]
      · simp [hq]
    simp only [e]
    first | exact hsum | exact hlim

/-- If the window distribution annihilates tests above norm one, any two tests
with equal restrictions to the norm-one classes have exactly the same Hecke zero sum. -/
theorem hasSum_window_iff_of_eq_on_norm_one (χ : X →* U) (hχ : IsSpectralBasepointChoice χ)
    (hr : ∀ ξ t, χ ξ (σ t) = 1) (win : Set ((_ : X) × ℂ))
    (hw : ∀ ξ s, (⟨ξ⁻¹, 1-s⟩ ∈ win ↔ ⟨ξ, s⟩ ∈ win))
    (hpos : ∀ f : BruhatCompactSupport C𝔽, tsupport f.val ⊆ {g : C𝔽 | 1 < N(g)} →
      HasSum (win.indicator (fun q ↦ windowTerm(χ, f, q))) 0)
    (φ ψ : BruhatCompactSupport C𝔽) (he : ∀ k : C₁, φ.val k.val = ψ.val k.val) (z : ℂ) :
    HasSum (win.indicator (fun q ↦ windowTerm(χ, φ, q))) z ↔
      HasSum (win.indicator (fun q ↦ windowTerm(χ, ψ, q))) z := by
  classical
  have h (u v : BruhatCompactSupport C𝔽) (hu : ∀ k : C₁, u.val k.val = v.val k.val)
      (hs : HasSum (win.indicator (fun q ↦ windowTerm(χ, v, q))) z) :
      HasSum (win.indicator (fun q ↦ windowTerm(χ, u, q))) z := by
    have h0 := hasSum_window_zero_of_above_norm_one χ hχ hr win hw hpos (u-v) (fun k ↦ by
      change u.val k.val - v.val k.val = 0
      rw [hu, sub_self])
    have hsum := h0.add hs
    rw [zero_add] at hsum
    convert hsum using 1
    funext q
    by_cases hq : q ∈ win
    · simp only [Set.indicator_of_mem hq]
      change _ = zeroWeight(χ,q) * (∫ g, (u.val g - v.val g) * _ ∂ideleClassTamagawaMeasure F) + _
      rw [show (fun g : C𝔽 ↦ (u.val g - v.val g) * ideleClassNormTwist (χ q.1) (q.2-1/2) g) =
        (fun g ↦ u.val g * ideleClassNormTwist (χ q.1) (q.2-1/2) g -
          v.val g * ideleClassNormTwist (χ q.1) (q.2-1/2) g) from funext fun _ ↦ sub_mul _ _ _,
        integral_sub (window_mellin_integrable _ _) (window_mellin_integrable _ _), mul_sub, sub_add_cancel]
    · simp [hq]
  exact ⟨h ψ φ (fun k ↦ (he k).symm), h φ ψ he⟩

end RiemannMasullo.StripNuclearity
end
