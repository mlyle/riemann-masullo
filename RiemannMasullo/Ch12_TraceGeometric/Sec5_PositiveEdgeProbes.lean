module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_Isolated
import all RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Compact positive probes for the width comparison in §12.5 -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽" => (continuousIdeleClassNorm F : C →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "M(" φ ", " χ ", " w ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C).val
    (ideleClassNormTwist (F := F) χ w)

/-- Lifting a smooth compact radial test with the inverse angular twist gives its
ordinary bilateral Laplace transform times the volume of the norm-one classes. -/
theorem exists_characterNormTest_laplace (χ : PontryaginDual C) (g : ℝ → ℂ)
    (hs : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport C,
      (∀ x, φ.val x = (χ⁻¹ x : ℂ) * g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ))) ∧
      ∀ w : ℂ, M(φ, χ, w) =
        (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * bilateralLaplace g w := by
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) χ⁻¹ g hs hc
  refine ⟨φ, hφ, fun w ↦ ?_⟩
  rw [characterNormTest_mellin g hs hc χ⁻¹ φ hφ χ w]
  have hone : χ * χ⁻¹ = 1 := mul_inv_cancel _
  rw [ite_eq_left (fun u ↦ by rw [hone]; rfl)]
  have hconst (u) : ((χ * χ⁻¹) (QuotientGroup.mk (canonicalIdeleNormSection F u) : C) : ℂ) = 1 := by
    rw [hone]; rfl
  have hi := grh_shift_integral g hs.continuous _ hconst 0 w
  simp only [sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hi
  rw [hi]
  rfl

/-- For each character and each real strip half-width, an actual compact Bruhat test has
Mellin transform with strictly positive real part at every ordinate on both centered edges. -/
theorem exists_hecke_positive_edge_probes (χ : PontryaginDual C) (b : ℝ) :
    ∃ φ : BruhatCompactSupport C, ∀ w : ℂ, |w.re| = |b| → 0 < (M(φ, χ, w)).re := by
  obtain ⟨K, -, -, -, -, hK⟩ := exists_compact_positive_laplace_edges
  let H := fun x : ℝ ↦ K x / Real.cosh (b*x)
  obtain ⟨hs, hc, -, hp⟩ := hK b
  let g := fun x : ℝ ↦ (H x : ℂ)
  have hgs : ContDiff ℝ (∞) g := Complex.ofRealCLM.contDiff.comp hs
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  obtain ⟨φ, -, hM⟩ := exists_characterNormTest_laplace χ g hgs hgc
  refine ⟨φ, fun w hw ↦ ?_⟩
  rw [hM, Complex.re_ofReal_mul]
  apply mul_pos
  · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Complex.ofReal_ne_zero.mp (grh_classVolume_ne_zero (F := F))).symm
  · have h := hp w.re hw w.im
    rw [Complex.re_add_im] at h
    exact h

namespace Isolated

local notation "Chars(" τ ")" => {χ : PontryaginDual C // ∀ t : ℝ≥0ˣ, χ ((τ) t) = 1}
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "Off(" z ")" => ((z).val.re - 1/2)
local notation "m(" χ "," z ")" => (ord(χ,(z).val)).toNat
local notation "Ext(" τ ", " α ")" => {p : Chars(τ) × ℂ // 0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re - 1/2|}

/-- The probes in the signed width comparison of Theorem 12.5.1.1 (pp. 519–520) can be
chosen unconditionally. The only remaining hypothesis compares the two actual signed sums. -/
theorem exists_positive_probe_traceFormula_exteriorZeros_of_widthComparison (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) {α s : ℝ} (hα : 0 < α) (hs : 1 < s) :
    ∃ probe : Chars(τ) → ℝ → BruhatCompactSupport C,
      (∀ (χ : Chars(τ)) (b : ℝ) (w : ℂ), |w.re| = |b| → 0 < (M(probe χ b, χ.val, w)).re) ∧
      ((∀ (χ : Chars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
          -(∑' z : Sites(χ.val), if |Off(z)| < b then (m(χ.val,z) : ℝ) *
            (M(probe χ b, χ.val, z.val - 1/2)).re else 0) ≤
          -(∑' z : Sites(χ.val), (spectralStripMultiplicity b s Off(z) m(χ.val,z) : ℝ) *
            (M(probe χ b, χ.val, z.val - 1/2)).re)) →
        ∀ φ : BruhatCompactSupport C, HasSum (fun p : Ext(τ, α) ↦
          ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ, p.val.1.val, p.val.2 - 1/2)) 0) := by
  choose probe hp using fun (χ : Chars(τ)) (b : ℝ) ↦ exists_hecke_positive_edge_probes χ.val b
  refine ⟨probe, hp, fun hcomp φ ↦ traceFormula_exteriorZeros_of_signedWidthComparison τ hτ hα hs
    probe ?_ hcomp φ⟩
  intro χ b hab _ z hz
  apply hp
  rw [abs_of_pos (hα.trans_le hab)]
  simpa only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] using hz

end Isolated
end RiemannMasullo
