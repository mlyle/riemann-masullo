import RiemannMasullo.Ch01_Introduction.Sec4_TranslatedFirstPrimes
import RiemannMasullo.Ch01_Introduction.HeckePrimeSquareShell
import RiemannMasullo.Ch12_TraceGeometric.Sec5
noncomputable section
open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "normAt(" g ")" => (((ideleClassNorm F) (g : G)).val : ℝ)
local notation "normOneMass" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b
local notation "finiteTest" => ((w : V) → BruhatCompactSupport (w.adicCompletion F)ˣ)
local notation "moment(" H ", " s ")" => (∫ x : ℝ, (H : ℝ → ℂ) x * Complex.exp ((s : ℂ) * x))
private theorem joint_volume_pos : 0 < normOneMass := by
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.toReal_ofReal (by positivity)]
  positivity

theorem squareCorrected_localTerms_exp_bound (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) (hH : Continuous H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) :
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ∀ φ : BruhatCompactSupport G,
      (∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y)) → ∀ (A : archTest) (B : finiteTest),
      (∀ w t, (A w).val t = φ.val (archClass(w) t)) →
      (∀ w t, (B w).val t = φ.val (finiteClass(w) t)) →
      ‖firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1/2) +
        firstPrimeLocalTerms φ A B / (normOneMass : ℂ) + heckePrimeSquareShell ψ⁻¹ H y v‖ ≤ C * Real.exp (-y/6) := by
  obtain ⟨D, hD, harch⟩ := FirstPrimeArch.translated_archimedean_sum_bound ψ H hH hu huv hs
  obtain ⟨K, hK, hrem⟩ := heckeCompositeShell_sub_primeSquares_exp_bound
  have hc : HasCompactSupport H := HasCompactSupport.intro isCompact_Icc
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
  obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hc
  have hM₀ : 0 ≤ M := (norm_nonneg (H 0)).trans (hM 0)
  let Q := (Module.finrank ℚ F : ℝ) * M * K * Real.exp (v / 3 - u / 2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨‖moment(H, -1/2)‖ + D + Q, by positivity, fun y hy φ hφ A B hA hB ↦ ?_⟩
  have hV : (normOneMass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (joint_volume_pos (F := F)).ne'
  rw [firstPrime_localTerms_eq τ hτ ψ hψ H hu hs hy φ hφ A B hB, mul_div_cancel_left₀ _ hV]
  let S := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)
  have hrate : Real.exp (-(y/2)) ≤ Real.exp (-y/6) := Real.exp_le_exp.mpr (by linarith)
  have ha : ‖S‖ ≤ D * Real.exp (-y/6) :=
    (harch y hy φ hφ A hA).trans (mul_le_mul_of_nonneg_left hrate hD)
  have hq : ‖firstPrimeHigherPowers ψ⁻¹ H y v - heckePrimeSquareShell ψ⁻¹ H y v‖ ≤
      Q * Real.exp (-y/6) := hrem F ψ⁻¹ H hu huv hs hM₀ (fun x _ ↦ hM x) y hy
  have hp : ‖firstPrimePolarMoment ψ H y (-1/2)‖ ≤ ‖moment(H, -1/2)‖ * Real.exp (-y/6) := by
    by_cases h : ψ = 1
    · simp only [firstPrimePolarMoment, ite_eq_left h, norm_mul, Complex.norm_exp]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp
      linarith
    · rw [firstPrimePolarMoment, if_neg h, norm_zero]
      positivity
  calc
    _ = ‖firstPrimePolarMoment ψ H y (-1/2) - S -
        (firstPrimeHigherPowers ψ⁻¹ H y v - heckePrimeSquareShell ψ⁻¹ H y v)‖ := by
      congr 1
      dsimp only [S]
      ring
    _ ≤ ‖firstPrimePolarMoment ψ H y (-1/2)‖ + ‖S‖ +
        ‖firstPrimeHigherPowers ψ⁻¹ H y v - heckePrimeSquareShell ψ⁻¹ H y v‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
    _ ≤ _ := by simpa only [add_mul] using add_le_add (add_le_add hp ha) hq

#print axioms squareCorrected_localTerms_exp_bound
end RiemannMasullo
