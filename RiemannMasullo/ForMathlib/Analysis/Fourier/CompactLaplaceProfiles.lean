module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Compactness.Lindelof

/-!
# Vertical lines detected by compactly supported Laplace profiles

In any open interval of the real line one can support two smooth functions
whose bilateral Laplace transforms, on each vertical line, have exactly the
prescribed finite zero set for at least one of the two functions. A single
profile suffices on any given countable collection of vertical lines.

The construction uses a small real exponential modulation of a bump. Its
transform is translated horizontally, so a countable set of forbidden shifts
can be avoided. Constant-coefficient differentiation then inserts the specified
zeros while preserving the support restriction. The polar exponents of the
translated trace comparison in Theorem 12.5.1.1, pp. 519–520, are one application.
-/

open Complex MeasureTheory Set Filter
open scoped ContDiff Topology

public noncomputable section

namespace RiemannMasullo

private theorem countable_bilateralLaplace_zeros {H : ℝ → ℂ} (hH : Continuous H)
    (hc : HasCompactSupport H) (hi : (∫ x, H x) ≠ 0) :
    {w | bilateralLaplace H w = 0}.Countable := by
  have hd : Differentiable ℂ (bilateralLaplace H) := by
    intro w
    let a := |w.re| + 1
    have hw : |w.re| < a := by
      dsimp [a]
      linarith
    have hcont : Continuous (fun x : ℝ ↦ Real.exp (a * |x|) • H x) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).smul hH
    have hcomp : HasCompactSupport (fun x : ℝ ↦ Real.exp (a * |x|) • H x) :=
      HasCompactSupport.smul_left (f := fun x : ℝ ↦ Real.exp (a * |x|)) hc
    exact (hasDerivAt_bilateralLaplace (hcont.memLp_of_hasCompactSupport hcomp) hw).differentiableAt
  have ha : AnalyticOnNhd ℂ (bilateralLaplace H) univ := fun w _ ↦ hd.analyticAt w
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact (hi (by simpa [bilateralLaplace] using h (mem_univ (0 : ℂ)))).elim
  · have hh : {w | bilateralLaplace H w = 0}ᶜ ∈ codiscrete ℂ := h
    exact (isLindelof_iff_lindelofSpace.mpr inferInstance).countable_of_isDiscrete
      (compl_mem_codiscrete_iff.mp hh).2

private theorem exists_bump_integral_ne_zero_in_interval {a b : ℝ} (hab : a < b) :
    ∃ B : ℝ → ℂ, ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧ tsupport B ⊆ Ioo a b ∧
      (∫ x, B x) ≠ 0 := by
  let q := (a + b) / 2
  let β : ContDiffBump q := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  let B := fun x : ℝ ↦ (β x : ℂ)
  refine ⟨B, Complex.ofRealCLM.contDiff.comp β.contDiff,
    β.hasCompactSupport.comp_left Complex.ofReal_zero, ?_, ?_⟩
  · have hsub : tsupport B ⊆ tsupport β := by
      apply closure_mono
      intro x hx
      exact fun h ↦ hx (by simp [B, h])
    rw [β.tsupport_eq] at hsub
    intro x hx
    have hdist := Metric.mem_closedBall.mp (hsub hx)
    change dist x ((a + b) / 2) ≤ (b - a) / 4 at hdist
    rw [Real.dist_eq, abs_le] at hdist
    constructor <;> linarith [hdist.1, hdist.2]
  · rw [show (∫ x, B x) = ((∫ x, β x : ℝ) : ℂ) from integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr β.integral_pos.ne'

/-- A real exponential modulation of the given profile makes its transform nonzero
on any prescribed countable family of vertical lines. The modulation parameter can
be chosen in any nonempty open interval. -/
theorem exists_bilateralLaplace_modulation_avoiding_lines {H : ℝ → ℂ} (hH : Continuous H)
    (hc : HasCompactSupport H) (hi : (∫ x, H x) ≠ 0) (S : Set ℝ) (hS : S.Countable)
    {a b : ℝ} (hab : a < b) :
    ∃ l ∈ Ioo a b, ∀ w : ℂ, w.re ∈ S →
      bilateralLaplace (fun x : ℝ ↦ H x * Complex.exp ((l : ℂ) * x)) w ≠ 0 := by
  let Z := Complex.re '' {w | bilateralLaplace H w = 0}
  let bad := (fun p : ℝ × ℝ ↦ p.1 - p.2) '' (Z ×ˢ S)
  have hZ : Z.Countable := (countable_bilateralLaplace_zeros hH hc hi).image _
  have hbad : bad.Countable := (hZ.prod hS).image _
  have hsub : ¬ Ioo a b ⊆ bad := fun h ↦
    hab.not_ge (Cardinal.Real.Ioo_countable_iff.mp (hbad.mono h))
  obtain ⟨l, hlab, hl⟩ := Set.not_subset.mp hsub
  let P := fun x : ℝ ↦ H x * Complex.exp ((l : ℂ) * x)
  refine ⟨l, hlab, fun w hw ↦ ?_⟩
  change bilateralLaplace P w ≠ 0
  have hmod : bilateralLaplace P w = bilateralLaplace H (w + l) := by
    unfold bilateralLaplace
    apply integral_congr_ae
    filter_upwards with x
    simp only [P, add_mul, Complex.exp_add]
    ring
  rw [hmod]
  intro hz
  exact hl ⟨((w + l).re, w.re), ⟨⟨w + l, hz, rfl⟩, hw⟩, by simp⟩

private theorem exists_smooth_bilateralLaplace_avoiding_lines {H : ℝ → ℂ}
    (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (hi : (∫ x, H x) ≠ 0)
    (S : Set ℝ) (hS : S.Countable) :
    ∃ P : ℝ → ℂ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ tsupport H ∧
      ∀ w : ℂ, w.re ∈ S → bilateralLaplace P w ≠ 0 := by
  obtain ⟨l, _, hl⟩ := exists_bilateralLaplace_modulation_avoiding_lines hs.continuous hc hi S hS
    (zero_lt_one : (0 : ℝ) < 1)
  exact ⟨fun x ↦ H x * Complex.exp ((l : ℂ) * x),
    hs.mul (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)),
    hc.mul_right, tsupport_mul_subset_left, hl⟩

private theorem bilateralLaplace_deriv_of_hasCompactSupport (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (w : ℂ) :
    bilateralLaplace (deriv H) w = -(w * bilateralLaplace H w) := by
  let E := fun x : ℝ ↦ Complex.exp (w * x)
  have hE (x : ℝ) : HasDerivAt E (w * E x) x := by
    convert (((hasDerivAt_id' (x : ℂ)).const_mul w).cexp).comp_ofReal using 1
    ring
  have hEc : Continuous E := continuous_iff_continuousAt.mpr fun x ↦ (hE x).continuousAt
  have hI : Integrable (fun x ↦ H x * E x) :=
    (hs.continuous.mul hEc).integrable_of_hasCompactSupport hc.mul_right
  have hI' : Integrable (fun x ↦ deriv H x * E x) :=
    ((hs.continuous_deriv (by simp)).mul hEc).integrable_of_hasCompactSupport hc.deriv.mul_right
  have hprod (x : ℝ) : HasDerivAt (fun y ↦ H y * E y)
      (deriv H x * E x + w * (H x * E x)) x := by
    convert ((hs.differentiable (by simp) x).hasDerivAt.mul (hE x)) using 1
    ring
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hprod (hI'.add (hI.const_mul w)) hI
  rw [integral_add hI' (hI.const_mul w), integral_const_mul] at hzero
  exact eq_neg_of_add_eq_zero_left hzero

/-- A constant-coefficient differential operator multiplies the bilateral Laplace transform by
the monic polynomial with roots in `s`. Its output is supported in the support of the input. -/
theorem exists_bilateralLaplace_mul_factors (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (s : Finset ℂ) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ tsupport H ∧
      ∀ w, bilateralLaplace G w = (∏ a ∈ s, (w - a)) * bilateralLaplace H w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨H, hs, hc, Subset.rfl, fun _ ↦ by simp⟩
  | insert a s ha ih =>
    obtain ⟨g, hgs, hgc, hsub, hgf⟩ := ih
    let G := fun x ↦ -deriv g x - a * g x
    have hGs : ContDiff ℝ ∞ G :=
      (contDiff_infty_iff_deriv.mp hgs).2.neg.sub (contDiff_const.mul hgs)
    have hoff (x : ℝ) (hx : x ∉ tsupport g) : G x = 0 := by
      simp only [G, deriv_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx,
        neg_zero, mul_zero, sub_zero]
    have hsupport : tsupport G ⊆ tsupport g :=
      closure_minimal (fun x hx ↦ by_contra fun hg ↦ hx (hoff x hg)) (isClosed_tsupport _)
    refine ⟨G, hGs, HasCompactSupport.intro hgc hoff, hsupport.trans hsub, fun w ↦ ?_⟩
    let E := fun x : ℝ ↦ Complex.exp (w * x)
    have he : Continuous E := by
      dsimp [E]
      fun_prop
    have hi : Integrable (fun x ↦ g x * E x) :=
      (hgs.continuous.mul he).integrable_of_hasCompactSupport hgc.mul_right
    have hd : Integrable (fun x ↦ deriv g x * E x) :=
      ((hgs.continuous_deriv (by simp)).mul he).integrable_of_hasCompactSupport hgc.deriv.mul_right
    have hcalc : bilateralLaplace G w = -bilateralLaplace (deriv g) w - a * bilateralLaplace g w := by
      change (∫ x, G x * E x) = -(∫ x, deriv g x * E x) - a * ∫ x, g x * E x
      calc
        _ = ∫ x, -(deriv g x * E x) - a * (g x * E x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp only [G]
          ring
        _ = _ := by
          rw [integral_sub (f := fun x ↦ -(deriv g x * E x)) hd.neg (hi.const_mul a),
            integral_neg, integral_const_mul]
    rw [hcalc, bilateralLaplace_deriv_of_hasCompactSupport g hgs hgc, hgf, Finset.prod_insert ha]
    ring

private theorem exists_bilateralLaplace_filtered_zeros {H : ℝ → ℂ} (hs : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (s : Finset ℂ) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ tsupport G ⊆ tsupport H ∧
      ∀ w, bilateralLaplace G w = 0 ↔ w ∈ s ∨ bilateralLaplace H w = 0 := by
  obtain ⟨G, hGs, hGc, hsub, hG⟩ := exists_bilateralLaplace_mul_factors H hs hc s
  refine ⟨G, hGs, hGc, hsub, fun w ↦ ?_⟩
  simp [hG, mul_eq_zero, Finset.prod_eq_zero_iff, sub_eq_zero]

/-- One smooth compact profile in any open interval achieves the prescribed transform zeros
on every line in a countable set of real parts. -/
theorem exists_bilateralLaplace_profile_on_countable_lines {a b : ℝ} (hab : a < b)
    (S : Set ℝ) (hS : S.Countable) (s : Finset ℂ) :
    ∃ H : ℝ → ℂ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioo a b ∧
      (∀ w ∈ s, bilateralLaplace H w = 0) ∧
      ∀ w : ℂ, w.re ∈ S → (bilateralLaplace H w = 0 ↔ w ∈ s) := by
  obtain ⟨B, hs, hc, hsub, hi⟩ := exists_bump_integral_ne_zero_in_interval hab
  obtain ⟨P, hPs, hPc, hp, hP⟩ := exists_smooth_bilateralLaplace_avoiding_lines hs hc hi S hS
  obtain ⟨H, hHs, hHc, hsub', hH⟩ := exists_bilateralLaplace_filtered_zeros hPs hPc s
  exact ⟨H, hHs, hHc, hsub'.trans (hp.trans hsub), fun w hw ↦ (hH w).2 (Or.inl hw),
    fun w hw ↦ by simp [hH w, hP w hw]⟩

/-- Two smooth profiles supported in a prescribed interval jointly control the entire plane.
On each vertical line one member has exactly the specified transform zeros at every height. -/
theorem exists_bilateralLaplace_pair_on_all_lines {a b : ℝ} (hab : a < b) (s : Finset ℂ) :
    ∃ H : Bool → ℝ → ℂ, (∀ j, ContDiff ℝ ∞ (H j) ∧ HasCompactSupport (H j) ∧
      tsupport (H j) ⊆ Ioo a b ∧ ∀ w ∈ s, bilateralLaplace (H j) w = 0) ∧
      ∀ r : ℝ, ∃ j, ∀ w : ℂ, w.re = r →
        (bilateralLaplace (H j) w = 0 ↔ w ∈ s) := by
  obtain ⟨B, hs, hc, hsub, hi⟩ := exists_bump_integral_ne_zero_in_interval hab
  let S := Complex.re '' {w | bilateralLaplace B w = 0}
  have hS : S.Countable := (countable_bilateralLaplace_zeros hs.continuous hc hi).image _
  obtain ⟨P, hPs, hPc, hp, hP⟩ := exists_smooth_bilateralLaplace_avoiding_lines hs hc hi S hS
  obtain ⟨B', hBs', hBc', hBsub, hB'⟩ := exists_bilateralLaplace_filtered_zeros hs hc s
  obtain ⟨P', hPs', hPc', hPsub, hP'⟩ := exists_bilateralLaplace_filtered_zeros hPs hPc s
  let H := fun j : Bool ↦ if j then P' else B'
  refine ⟨H, ?_, fun r ↦ ?_⟩
  · intro j
    cases j
    · exact ⟨hBs', hBc', hBsub.trans hsub, fun w hw ↦ (hB' w).2 (Or.inl hw)⟩
    · exact ⟨hPs', hPc', hPsub.trans (hp.trans hsub), fun w hw ↦ (hP' w).2 (Or.inl hw)⟩
  · by_cases hr : r ∈ S
    · refine ⟨true, fun w hw ↦ ?_⟩
      change bilateralLaplace P' w = 0 ↔ _
      simp [hP' w, hP w (hw ▸ hr)]
    · refine ⟨false, fun w hw ↦ ?_⟩
      change bilateralLaplace B' w = 0 ↔ _
      have hb : bilateralLaplace B w ≠ 0 := fun hz ↦ hr ⟨w, hz, hw⟩
      simp [hB' w, hb]

end RiemannMasullo
