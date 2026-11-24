module

public import RiemannMasullo.Research.TraceComparison.RationalTranslatedDiagonal
public import RiemannMasullo.Research.TraceComparison.RationalTranslatedPlaces
import RiemannMasullo.Research.StripNuclearity.RationalBoundedWindow
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumUniqueness

/-! # Growth of the translated rational trace and its visible zeta zeros -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Asymptotics ContDiff NNReal Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "logN(" x ")" => Real.log (((ideleClassNorm ℚ) (x : Cℚ)).val : ℝ)
local notation "physical(" g "," y "," x ")" => rationalCenteredLogProfile g (logN(x) - y)
local notation "wide(" φ "," hs "," U ")" =>
  centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ) < 1/2) hs U

private theorem shifted_zero_eventually_avoids (z : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ∉ range shiftedZetaZero := by
  obtain ⟨δ,hδ,hd⟩ := shiftedZetaZero_separated z
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ), self_mem_nhdsWithin] with u hu hn
  rintro ⟨ρ,rfl⟩
  exact (not_lt.mpr (hd ρ hn)) (by simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hu)

/-- Paper: Section 12.3, p. 514, and (12.5.1.4), p. 520. For a fixed rational radial
test on the positive log half-line, the wide diagonal of its translates is bounded by
O(exp(a y)) exactly when every ordinary zeta zero visible to its Mellin transform lies
in Re ρ ≤ 1/2 + a. The smoothing and Sobolev order may vary with y.
Deviation: The converse uses uniqueness of an absolutely convergent Laplace expansion. -/
theorem rational_translated_wide_diagonal_isBigO_iff (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0)
    (φ : ℝ → BruhatCompactSupport Cℚ) (hφ : ∀ y x, (φ y).val x = physical(g,y,x))
    (s : ℝ → ℝ) (hs : ∀ y, 3 ≤ s y) (U : ℝ → ℕ → Set Cℚ)
    (hU : ∀ y, IsDPrimeSequence μℚ (U y)) (hm : ∀ y n, MeasurableSet (U y n)) (a : ℝ) :
    ((fun y ↦ wide(φ y,hs y,U y)) =O[atTop] (fun y ↦ Real.exp (a*y))) ↔
      ∀ z : criticalStripZetaZeros, compactLogMellin g z.val ≠ 0 → z.val.re ≤ 1/2 + a := by
  let b (z : criticalStripZetaZeros) := Vℚ * (zetaZeroOrder z : ℂ) * compactLogMellin g z.val
  have hb : Summable b := by
    simpa only [b, mul_assoc] using (completedZeta_explicit_formula hg hc).2.2.1.of_norm.mul_left Vℚ
  have hshift (z : criticalStripZetaZeros) : (shiftedZetaZero z).re = z.val.re-1/2 := by simp [shiftedZetaZero]
  have heq : (fun y ↦ -wide(φ y,hs y,U y)) =ᶠ[atTop]
      (fun y : ℝ ↦ ∑' z, b z * Complex.exp (shiftedZetaZero z*y)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    have H := hasSum_translatedZeta_neg_diagonal g y (hzero _ (neg_nonpos.mpr hy)) (φ y) (hφ y)
      (by norm_num : (0:ℝ)<1/2) (hs y) (U y) (hU y) (hm y)
    rw [← H.tsum_eq]
    apply tsum_congr
    intro z
    have hz := abs_re_shiftedZetaZero_lt z
    rw [hshift] at hz
    rw [spectralStripMultiplicity_interior (abs_lt.mp hz)]
  have hM (z : criticalStripZetaZeros) : b z ≠ 0 ↔ compactLogMellin g z.val ≠ 0 := by
    have h₀ := mul_ne_zero rationalNormOneTamagawaVolume_ne_zero
      (Nat.cast_ne_zero.mpr (zetaZeroOrder_pos z).ne' : (zetaZeroOrder z : ℂ) ≠ 0)
    simp [b, h₀]
  have hh := expSum_isBigO_iff shiftedZetaZero b shiftedZetaZero_injective shifted_zero_eventually_avoids
    (fun z ↦ (le_abs_self _).trans (abs_re_shiftedZetaZero_lt z).le) hb a
  rw [← Asymptotics.isBigO_neg_left, Asymptotics.isBigO_congr heq (Filter.EventuallyEq.rfl), hh]
  simp only [hM, hshift, sub_le_iff_le_add, add_comm a]

/-- The published seven-eighths zero-free half-plane gives a genuine O(exp(3y/8))
bound on the actual translated global trace, with no restriction on height. -/
theorem rational_translated_wide_diagonal_isBigO_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0)
    (φ : ℝ → BruhatCompactSupport Cℚ) (hφ : ∀ y x, (φ y).val x = physical(g,y,x))
    (s : ℝ → ℝ) (hs : ∀ y, 3 ≤ s y) (U : ℝ → ℕ → Set Cℚ)
    (hU : ∀ y, IsDPrimeSequence μℚ (U y)) (hm : ∀ y n, MeasurableSet (U y n)) :
    (fun y ↦ wide(φ y,hs y,U y)) =O[atTop] (fun y ↦ Real.exp (3/8*y)) := by
  apply (rational_translated_wide_diagonal_isBigO_iff g hg hc hzero φ hφ s hs U hU hm _).mpr
  intro z _
  have h : z.val.re ≤ 7/8 := le_of_not_gt fun hh ↦ hn hh (mem_criticalStripZetaZeros.mp z.property).1
  linarith

end RiemannMasullo.StripNuclearity

