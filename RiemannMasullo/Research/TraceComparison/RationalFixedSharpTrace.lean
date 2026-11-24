module

public import RiemannMasullo.Research.TraceComparison.RationalZetaStrip
public import RiemannMasullo.Research.TraceComparison.RationalDirichletStrip
import all RiemannMasullo.Research.StripNuclearity.RationalDiagonalDefect

/-! # Actual sharp S-local limits in a rational fixed strip -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology
open RiemannMasullo.External.Grh

namespace RiemannMasullo.StripNuclearity

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instNormOneSIdeleQuotientMeasurableSpaceSec1
  instSIdeleSecondCountableSec1

set_option quotPrecheck false
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Kℚ" => (ideleClassNorm ℚ).ker
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "Pr" => HeightOneSpectrum (𝓞 ℚ)
local notation "I(" S ")" => (SAdeleRing ℚ S)ˣ
local notation "Vℚ" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "vS(" S ")" => (((sLocalNormOneQuotientMeasure ℚ S) univ).toReal : ℂ)
local notation "N(" x ")" => ((((ideleClassNorm ℚ (x : Cℚ)).val : ℝ)) : ℂ)
local notation "poles(" φ ")" => ((∫ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x * N(x)^(-1/2:ℂ) ∂μℚ) +
  (∫ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x * N(x)^(1/2:ℂ) ∂μℚ))
local instance fixedSharpSIdeleT2 (S : Finset Pr) : T2Space I(S) := (sIdeleGroup_description ℚ S).2.1

/-- Convergence of the volume-adjusted sharp §12.4 masses for every admissible
finite set containing T, every compact S-local lift of the test, and both polar terms. -/
def RationalSharpTraceLimit (T : Finset Pr) (φ : BruhatCompactSupport Cℚ) (value : ℂ) : Prop :=
  ∀ S : Finset Pr, T ⊆ S → Subsingleton (CommRing.Pic ((S : Set Pr).integer ℚ)) →
    (∀ v : Pr, differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal → v ∈ S) →
    (∀ u : outsideIntegralIdeleUnits ℚ S, ∀ x : Cℚ, φ.val (QuotientGroup.mk u.val * x) = φ.val x) →
    ∀ B : BruhatCompactSupport I(S),
      (∀ x : I(S), HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ B.val (ξ.val * x))
        (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S x)))) →
      Tendsto (fun R : ℝ ↦ Vℚ / vS(S) * ∑' ξ : sProjectedDiagonal ℚ S, sLocalTraceSharpMass B ξ R
        - poles(φ)) atTop (𝓝 value)

private theorem rational_exists_sharp_limit_at_wide (τ : ℝ≥0ˣ →ₜ* Cℚ)
    (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport Cℚ) (hφ : ∀ x : Kℚ, φ.val x = 0) :
    ∃ T : Finset Pr, ∀ {s : ℝ} (hs : 3 ≤ s) (U : ℕ → Set Cℚ), IsDPrimeSequence μℚ U →
      (∀ n, MeasurableSet (U n)) → RationalSharpTraceLimit T φ
        (centeredStripGeometricDiagonalIntegral φ (by norm_num : (0:ℝ)<1/2) hs U) := by
  obtain ⟨T,hT⟩ := exists_finset_sharpMass_tendsto_diagonal_of_wide_or_inv_odd τ hτ φ hφ
  refine ⟨T, ?_⟩
  intro s hs U hU hm S hS hp hr ho B hB
  exact hT S hS hp hr ho B hB (α:=1/2) (by norm_num) hs U hU hm (Or.inl le_rfl)

/-- Paper: Section 12.3, p. 514, and (12.4.1.24), p. 518. For rational radial tests,
the sharp S-local trace converges to the actual global diagonal at every half-width
strictly greater than 3/8. The finite set may depend on the test.
Deviation: The input is the ordinary zeta seven-eighths theorem. -/
theorem rational_sharpMass_tendsto_of_zeta_seven_eighths
    (hn : ∀ {z : ℂ}, (7/8:ℝ) < z.re → riemannZeta z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (g : ℝ → ℂ) (h₀ : g 0 = 0) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Cℚ, φ.val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))) :
    ∃ T : Finset Pr, ∀ {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
      IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
      RationalSharpTraceLimit T φ (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U) := by
  obtain ⟨T,hT⟩ := rational_exists_sharp_limit_at_wide τ hτ φ (rational_vanishes_on_kernel g h₀ φ hφ)
  refine ⟨T, ?_⟩
  intro α s hα hs U hU hm
  rw [rational_radial_diagonal_eq_wide_of_retained_zeta g h₀ φ hφ (by linarith) hs _ U hU hm]
  · exact hT hs U hU hm
  · intro z
    have hz := rational_centered_zero_band_of_riemannZeta_nonvanishing (7/8) (fun _ hh _ ↦ hn hh) z
    exact spectralStripMultiplicity_interior (abs_lt.mp (by linarith : |z.val.re-1/2| < α)) _ _

/-- Paper: Section 12.3, p. 514, and (12.4.1.24), p. 518. The same fixed-width
sharp comparison holds for every admissible rational test, including all angular
characters, under the Dirichlet seven-eighths nonvanishing theorem.
Deviation: The zero exclusion comes from outside the manuscript. -/
theorem rational_sharpMass_tendsto_of_dirichlet_seven_eighths
    (hn : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ},
      (7/8:ℝ) < z.re → ¬ (χ = 1 ∧ z = 1) → DirichletCharacter.LFunction χ z ≠ 0)
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ)) (φ : BruhatCompactSupport Cℚ)
    (hφ : ∀ x : Kℚ, φ.val x = 0) :
    ∃ T : Finset Pr, ∀ {α s : ℝ} (hα : 3/8 < α) (hs : 3 ≤ s) (U : ℕ → Set Cℚ),
      IsDPrimeSequence μℚ U → (∀ n, MeasurableSet (U n)) →
      RationalSharpTraceLimit T φ (centeredStripGeometricDiagonalIntegral φ (show 0 < α by linarith) hs U) := by
  obtain ⟨T,hT⟩ := rational_exists_sharp_limit_at_wide τ hτ φ hφ
  refine ⟨T, ?_⟩
  intro α s hα hs U hU hm
  have hE := rational_isEmpty_exteriorZeros_of_dirichlet_band (by norm_num : (0:ℝ) ≤ 7/8) hn τ hτ
    (by linarith : 7/8-1/2 < α)
  rw [rational_diagonal_eq_wide_of_isEmpty_exterior τ hτ φ hφ (by linarith) hE hs hs U U hU hm hU hm]
  exact hT hs U hU hm

end RiemannMasullo.StripNuclearity

