module

public import RiemannMasullo.Research.TraceComparison.RationalAnnularLimits
public import RiemannMasullo.Research.StripNuclearity.RationalRealAnnihilator

/-! # Comparing the global strip diagonal with an actual rational S-local cutoff

On local-null tests in a prime-free interval the annular cutoff has zero
limit. Equality of that limit with the global integral therefore tests
exactly the missing arithmetic statement.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology
open RiemannMasullo.StripNuclearity
namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

set_option quotPrecheck false
local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "I₀" => (SAdeleRing ℚ S₀)ˣ
local notation "H₀" => sProjectedDiagonal ℚ S₀
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μF" => ideleClassTamagawaMeasure ℚ
local notation "μI" => sMultiplicativeTamagawaMeasure ℚ S₀
local notation "vF" => ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal
local notation "vS" => ((sLocalNormOneQuotientMeasure ℚ S₀) univ).toReal
local notation "radial(" φ "," g ")" =>
  ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x = rationalCenteredLogProfile g (Real.log (((ideleClassNorm ℚ) x).val : ℝ))
local notation "lifts(" B "," φ ")" => ∀ x : I₀, HasSum (fun ξ : H₀ ↦ (B : BruhatCompactSupport I₀).val (ξ.val*x))
  ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S₀ x)))
local notation "localTrace(" B "," D "," t ")" => (((vF / vS : ℝ) : ℂ) *
  sLocalTraceAnnularOrbitSum (B : BruhatCompactSupport I₀) D ((t:ℝ)*(t*t))⁻¹ t (t*t))
local notation "diagonal(" φ "," hα "," hs "," U ")" =>
  (∫ x : Cℚ, dSequenceKernelSmoothening μF U
    (globalStripGeometricKernel (F := ℚ) (1/2) (hα).le
      (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ
      (exists_numberField_projectiveKernel_comp_spectralProjection (F := ℚ) (le_of_lt hα)
        (lt_of_lt_of_le (b := (3 : ℝ)) Nat.one_lt_ofNat hs) φ)) (x,x) ∂μF)
local instance joinedCutoffT2 : T2Space I₀ := (sIdeleGroup_description ℚ S₀).2.1

/-- On the real-place annihilating family, the normalized actual annular
S-local trace tends to zero for every compact Bruhat lift. -/
theorem rational_annularTrace_realAnnihilator_tendsto_zero (f : ℝ → ℂ)
    (hf : ContDiff ℝ (∞) f) (hc : HasCompactSupport f) {a b : ℝ} (ha : 0 < a) (hI : tsupport f ⊆ Icc a b)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,boundedRealAnnihilator f))
    (B : BruhatCompactSupport I₀) (hB : lifts(B,φ)) (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI) :
    Tendsto (fun t : ℝ ↦ localTrace(B,D,t)) atTop (𝓝 0) := by
  obtain ⟨hd, -,hs⟩ := boundedRealAnnihilator_regularity f hf hc
  have h := (rational_annularTrace_two_limits_of_radial (boundedRealAnnihilator f) hd.continuous
    ha (hs.trans hI) φ hφ B hB D hD).2.const_mul (((vF/vS : ℝ) : ℂ))
  simpa only [boundedRealAnnihilator_realIntegral f hf hc ha hI, mul_zero] using h

/-- Paper: Section 12.3, p. 514, and the comparison used on p. 520. On a fixed
rational prime-free interval, agreement between the actual global geometric
diagonal and the limit of the actual S-local sharp annular kernel for all
positive half-widths and all real-place annihilating tests is equivalent to
ordinary RH. The sole arithmetic input is a sublinear dyadic count of the
omitted zeros at each width. All physical tests and S-unit lifts exist.
Deviation: Uses lower spatial radius t⁻³, upper spatial radius t and Fourier
radius t², with both polar terms zero on this family. -/
theorem rational_allWidths_annular_geometric_comparison_iff_riemannHypothesis
    {a b s : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < Real.log 2) (hs : 3 ≤ s)
    (hcount : ∀ α : ℝ, 0 < α → RationalOmittedZeroDyadicBound α s)
    (D : Set I₀) (hD : IsFundamentalDomain H₀ D μI)
    (U : ℕ → Set Cℚ) (hU : IsDPrimeSequence μF U) (hm : ∀ n, MeasurableSet (U n)) :
    (∀ α (hα : 0 < α) (f : ℝ → ℂ), ContDiff ℝ (∞) f → HasCompactSupport f → tsupport f ⊆ Icc a b →
      ∀ φ : BruhatCompactSupport Cℚ, radial(φ,boundedRealAnnihilator f) →
      ∀ B : BruhatCompactSupport I₀, lifts(B,φ) →
        Tendsto (fun t : ℝ ↦ localTrace(B,D,t)) atTop (𝓝 diagonal(φ,hα,hs,U))) ↔ RiemannHypothesis := by
  let := finite_rational_empty_sProjectedDiagonal
  have criterion := rational_allWidths_realAnnihilator_diagonal_zero_iff_riemannHypothesis_of_dyadicCount
    ha hab hb hs hcount U hU hm
  constructor
  · intro h
    apply criterion.mp
    intro α hα f hf hc hI φ hφ
    obtain ⟨hg,hgc,-⟩ := boundedRealAnnihilator_regularity f hf hc
    have hd : ContDiff ℝ (∞) (rationalCenteredLogProfile (boundedRealAnnihilator f)) :=
      (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const 2)).mul hg
    obtain ⟨B, -, hB⟩ := exists_sLocalTraceLift_radial_of_finite (F:=ℚ) (S:=S₀) _ hd hgc.mul_left φ hφ
    exact tendsto_nhds_unique (h α hα f hf hc hI φ hφ B hB)
      (rational_annularTrace_realAnnihilator_tendsto_zero f hf hc ha hI φ hφ B hB D hD)
  · intro rh α hα f hf hc hI φ hφ B hB
    have he : diagonal(φ,hα,hs,U) = 0 := criterion.mpr rh α hα f hf hc hI φ hφ
    rw [he]
    exact rational_annularTrace_realAnnihilator_tendsto_zero f hf hc ha hI φ hφ B hB D hD

end RiemannMasullo
