module

public import RiemannMasullo.Ch02_AdelicTheta.Sec4
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Barrelled
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Weighted
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch09_HardySobolev.Sec1
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# S-local idelic zeta functions

Masullo, §3.3, pp. 128–141. The finset indexes the finite places, with all
archimedean places included. Holomorphy and meromorphy on quasi-character spaces
are expressed in complex norm-twist coordinates.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "modℂ[" m "," g "]" => (((m g : ℝ≥0) : ℝ) : ℂ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "rightHalf" => (Complex.re ⁻¹' Ioi (0 : ℝ))
local notation "criticalStrip" => (Complex.re ⁻¹' Ioo (0 : ℝ) 1)
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)

section Coordinates

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: §3.1.1, p. 119. A complex power of the positive module is
continuous and multiplicative. -/
theorem normPower_properties (m : G →* ℝ≥0ˣ) (hm : Continuous m) (s : ℂ) :
    (modℂ[m, (1 : G)]) ^ s = 1 ∧
    (∀ g h : G, (modℂ[m, g * h]) ^ s = (modℂ[m, g]) ^ s * (modℂ[m, h]) ^ s) ∧
    Continuous (fun g : G ↦ (modℂ[m, g]) ^ s) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro g h
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s
  · have hr : Continuous (fun g : G ↦ ((m g : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp hm)
    apply (Complex.continuous_ofReal.comp hr).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))

/-- Paper: §3.1.1, p. 119. A norm twist multiplies the quasi-character
by the given complex power of the module. -/
def quasiCharacterNormTwist (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (s : ℂ) : QuasiCharacter G :=
  let h := normPower_properties m hm s
  c * ⟨{ toFun := fun g ↦ (modℂ[m, g]) ^ s
         map_one' := h.1
         map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: §3.1.1, p. 119. Twisting with exponent one multiplies the
quasi-character by the module. -/
theorem quasiCharacterNormTwist_one (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    (c : QuasiCharacter G) (g : G) :
    quasiCharacterNormTwist m hm c 1 g = c g * modℂ[m, g] := by
  change c g * (modℂ[m, g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one]

end Coordinates

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist mₛ hmₛ ((circleToComplex).comp χ)
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "positive" => {c : Xₛ | ∃ (χ : PontryaginDual Jₛ) (s : ℂ),
  s ∈ rightHalf ∧ c = chartₛ(χ) s}
local notation "band[" m "," n "]" =>
  {g | (((m g : ℝ≥0) : ℝ)) ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}

local instance : MeasurableSpace Jₛ := borel _
local instance : MeasurableSpace J₁ := borel _
local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
local instance : MeasurableSpace Aₛ :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))

/-- The additive S-adeles are locally compact Hausdorff, with regular Haar
measure in their product Borel structure. -/
private theorem sAdele_fourierMeasure :
    let G := Multiplicative Aₛ
    let μ : Measure G := sAdditiveTamagawaMeasure F S
    T2Space G ∧ LocallyCompactSpace G ∧ BorelSpace G ∧ μ.IsHaarMeasure ∧ μ.Regular := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let G := Multiplicative Aₛ
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace Aₛ)
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space G := ‹T2Space Aₛ›
  let : SigmaCompactSpace Aₛ := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace G := ‹BorelSpace Aₛ›
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let hμ : (sAdditiveTamagawaMeasure F S).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace (sAdditiveTamagawaMeasure F S)
  exact ⟨inferInstanceAs (T2Space G), inferInstanceAs (LocallyCompactSpace G),
    inferInstanceAs (BorelSpace G), inferInstanceAs μ.IsHaarMeasure, inferInstanceAs μ.Regular⟩

/-- Paper: §3.3.1, p. 128. The Fourier integral formed with the standard
S-adelic character and additive Tamagawa measure preserves the test space. -/
theorem sAdeleSchwartzFourier_mem (f : ℬ(Aₛ)) :
    (fun y : Multiplicative Aₛ ↦ tamagawaFourier (sAdditiveTamagawaMeasure F S)
      (sAdeleStandardCharacter F S) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
        schwartzBruhatSubmodule (G := Multiplicative Aₛ) := by
  let G := Multiplicative Aₛ
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let : μ.Regular := hG.2.2.2.2
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  let g : schwartzBruhatSubmodule (PontryaginDual G) := fourier f
  have hEq (y : G) : tamagawaFourier (sAdditiveTamagawaMeasure F S)
      (sAdeleStandardCharacter F S) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd = g.val (e y) := by
    rw [tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]
      exact he y.toAdd x)]
    exact ((hfourier f).2 (e y)).symm
  rw [funext hEq]
  exact schwartzBruhat_mem_comp_equiv e g.property

/-- Paper: §3.3.1, p. 128. The S-adelic Fourier transform uses the product
additive Tamagawa measure and the standard S-adelic character. -/
def sAdeleSchwartzFourier (f : ℬ(Aₛ)) : ℬ(Aₛ) :=
  ⟨fun y ↦ tamagawaFourier (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S)
    (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd, sAdeleSchwartzFourier_mem f⟩

open Classical in
/-- Paper: Theorem 2.2.3.2, p. 82. Fourier transformation of an S-adelic test
inserted with the integer tail multiplies its local transform by the tail mass
on the inverse different and vanishes elsewhere. -/
theorem adeleSchwartzFourier_sAdeleSchwartzToGlobal :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (h : ℬ(Aₛ)) (y : AdeleRing (𝓞 F) F),
      adeleSchwartzFourier (sAdeleSchwartzToGlobal F S h) (Multiplicative.ofAdd y) =
        if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
          ‖y.2 v‖ ≤ (v.asIdeal.absNorm : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) then
          (c : ℝ) • sAdeleSchwartzFourier h (Multiplicative.ofAdd (adeleProjection F S y))
        else 0 := by
  classical
  obtain ⟨c, hc, _, hp, _⟩ := sAdeleProjection_dual_masses F S
  refine ⟨c, hc, fun h y ↦ ?_⟩
  let G := Multiplicative Aₛ
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let f := fun x : Aₛ ↦ h (Multiplicative.ofAdd x)
  let I := integralAdelesOutside F S
  let p := adeleProjection F S
  have he : (fun x ↦ sAdeleSchwartzToGlobal F S h (Multiplicative.ofAdd x)) =
      (I : Set (AdeleRing (𝓞 F) F)).indicator (f ∘ p) := by
    funext x
    rw [sAdeleSchwartzToGlobal_apply]
    have hi : x ∈ I ↔ ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F := by
      simp only [I, integralAdelesOutside, Subring.mem_iInf]
      rfl
    by_cases hx : x ∈ I
    · rw [ite_eq_left (hi.mp hx), indicator_of_mem hx]
      rfl
    · rw [ite_eq_right (hi.not.mp hx), indicator_of_notMem hx]
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  let ft := tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
  change ft (fun x ↦ sAdeleSchwartzToGlobal F S h (Multiplicative.ofAdd x)) y = _
  rw [he]
  have ht := congrFun (tamagawaFourier_sAdeleLift F S c hp f (SchwartzBruhat.integrable μ h)) y
  refine ht.trans ?_
  split
  · rename_i hy
    rw [indicator_of_mem (show y ∈ sAdeleTailDual F S from hy)]
    rfl
  · rename_i hy
    exact indicator_of_notMem (show y ∉ sAdeleTailDual F S from hy) _

/-- Paper: §3.3.1, p. 128. The Fourier transform at zero integrates the
test function against the additive Tamagawa measure. -/
theorem sAdeleSchwartzFourier_apply_zero (f : ℬ(Aₛ)) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) =
      ∫ x : Aₛ, f (Multiplicative.ofAdd x) ∂sAdditiveTamagawaMeasure F S := by
  have hp (p : ℕ) [Fact p.Prime] : padicStandardCharacter p 0 = 1 := by
    have key (n : ℕ) (a : ℤ_[p]) (ha : a = 0) :
        Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n)) = 1 := by
      subst ha
      simp
    unfold padicStandardCharacter
    exact key _ _ (Subtype.ext (mul_zero _))
  have hr : (0 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 0 := rfl
  have hf (v : HeightOneSpectrum (𝓞 ℚ)) : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 0 := rfl
  have h0 : adeleStandardCharacter F 0 = 1 := by
    simp [adeleStandardCharacter, ratAdeleStandardCharacter, hp, hr, hf]
  have hi (w : InfinitePlace F) : (0 : Aₛ).1 w = 0 := rfl
  have hS : sAdeleStandardCharacter F S 0 = 1 := by
    simp only [sAdeleStandardCharacter, finiteLocalStandardCharacter, hi, Pi.single_zero,
      Prod.snd_zero, Pi.zero_apply, RestrictedProduct.single_zero]
    exact (congrArg₂ (· * ·) (Finset.prod_eq_one fun _ _ ↦ h0)
      (Finset.prod_eq_one fun _ _ ↦ h0)).trans (one_mul 1)
  change tamagawaFourier _ _ _ (0 : Aₛ) = _
  simp [tamagawaFourier, hS]

/-- Integer-indicator insertion multiplies Fourier evaluation at zero by the
same nonzero additive tail mass for every local test. -/
theorem sAdeleSchwartzToGlobal_fourier_zero_scale :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : ℬ(Aₛ),
      adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd 0) =
        c * sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  classical
  obtain ⟨c, hc, -, hm, -⟩ := sAdeleProjection_dual_masses F S
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hc, fun f ↦ ?_⟩
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace Aₛ := inferInstanceAs
    (BorelSpace (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  let : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  let I := (integralAdelesOutside F S : Set (AdeleRing (𝓞 F) F))
  let z (y : Aₛ) := f (Multiplicative.ofAdd y)
  have hf : (fun x ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x)) =
      I.indicator (z ∘ adeleProjection F S) := by
    funext x
    have hI : x ∈ I ↔ ∀ v ∉ S, x.2 v ∈ v.adicCompletionIntegers F := by
      change x ∈ integralAdelesOutside F S ↔ _
      simp only [integralAdelesOutside, Subring.mem_iInf]
      rfl
    rw [sAdeleSchwartzToGlobal_apply, indicator_apply, hI]
    rfl
  rw [(adeleSchwartzFourier_apply_zero _).2, sAdeleSchwartzFourier_apply_zero, hf,
    integral_indicator (isOpen_integralAdelesOutside F S).measurableSet]
  have hZ : Continuous z := (schwartzBruhat_continuous f).comp continuous_ofAdd
  have he := integral_map (μ := (additiveTamagawaMeasure F).restrict I)
    hm.measurable.aemeasurable (f := z)
    (by rw [hm.map_eq]; exact hZ.aestronglyMeasurable)
  refine he.symm.trans ?_
  rw [hm.map_eq, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/-- Paper: Equation (3.3.1.1), p. 129. The S-local zeta integral weights
the restriction of the test function to the S-ideles by the quasi-character. -/
def sLocalIdelicZetaIntegral (f : ℬ(Aₛ)) (c : Xₛ) : ℂ :=
  ∫ g : Iₛ, f (Multiplicative.ofAdd g.val) * c (classOf g) ∂μₛ

section AbsoluteConvergence

open scoped Classical ENNReal Pointwise WithZero

private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance (w : InfinitePlace F) : BorelSpace w.Completionˣ := ⟨by
  change (borel w.Completion).comap Units.val = _
  rw [← borel_comap, ← (Units.isEmbedding_val₀ (G₀ := w.Completion)).eq_induced]⟩
private local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
private local instance measurableSpace_finiteAdicUnits (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
private local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩

/-- Each infinite coordinate is bounded by the mixed archimedean norm. -/
private theorem infinitePlace_norm_le_mixedNorm (x : InfiniteAdeleRing F) (w : InfinitePlace F) :
    ‖x w‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  apply Finset.le_sup'_of_le _ (Finset.mem_univ w)
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _).symm.le
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _).symm.le

omit [NumberField F] in
/-- A positive norm power at an infinite place becomes integrable against the multiplicative
Tamagawa measure after division by a sufficiently large power at infinity. -/
private theorem infiniteLocalTamagawa_integrable_norm_rpow (w : InfinitePlace F) {σ : ℝ}
    (hσ : 0 < σ) (k : ℕ) (hk : (w.mult : ℝ) * σ < k) :
    SigmaFinite (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
    Integrable (fun u : w.Completionˣ ↦ ‖u.val‖ ^ ((w.mult : ℝ) * σ) / (max 1 ‖u.val‖) ^ k)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  -- Convert the density-weighted integral to radial integration for additive Haar measure.
  let d := w.mult
  let ν := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : w.Completion) := (↑(‖x‖₊ ^ d) : ℝ≥0∞)⁻¹
  let U : Set w.Completion := {0}ᶜ
  have hU : U = range (Units.val : w.Completionˣ → w.Completion) := by
    ext x
    simpa [U] using (Units.exists_iff_ne_zero (p := (· = x))).symm
  have hmU : MeasurableSet U := (measurableSet_singleton (0 : w.Completion)).compl
  have he := (Units.isEmbedding_val₀ (G₀ := w.Completion)).measurableEmbedding (hU ▸ hmU)
  have hD : Measurable D := by dsimp [D]; fun_prop
  have hDf : ∀ᵐ x ∂ν.restrict U, D x < ⊤ := by
    refine (ae_restrict_iff' hmU).mpr (ae_of_all _ fun x hx ↦ ?_)
    have hp : 0 < ‖x‖₊ := NNReal.coe_pos.mp (norm_pos_iff.mpr hx)
    exact ENNReal.inv_lt_top.mpr (by dsimp [D]; positivity)
  have hRad (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
      [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
      [μ.IsAddHaarMeasure] (hd : Module.finrank ℝ E = d) :
      Integrable (fun x : E ↦ ‖x‖ ^ ((d : ℝ) * σ - d) / (max 1 ‖x‖) ^ k) μ := by
    refine (integrable_fun_norm_addHaar μ (f := fun r : ℝ ↦
      r ^ ((d : ℝ) * σ - d) / (max 1 r) ^ k)).mpr ?_
    have hd₀ : 0 < d := InfinitePlace.mult_pos (w := w)
    have heq (r : ℝ) (hr : 0 < r) :
        r ^ (Module.finrank ℝ E - 1) • (r ^ ((d : ℝ) * σ - d) / (max 1 r) ^ k) =
          r ^ ((d : ℝ) * σ - 1) / (max 1 r) ^ k := by
      rw [smul_eq_mul, ← mul_div_assoc, hd, ← Real.rpow_natCast, ← Real.rpow_add hr,
        Nat.cast_sub hd₀, Nat.cast_one]
      congr 2
      ring
    refine IntegrableOn.congr_fun ?_ (fun r hr ↦ (heq r hr).symm) measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    apply IntegrableOn.union
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ - 1)) (Ioc 0 1) :=
        ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr (by
          have hp := mul_pos (Nat.cast_pos.mpr hd₀) hσ
          linarith)).congr_set_ae Ioo_ae_eq_Ioc.symm
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioc
      simp [max_eq_left hr.2]
    · have hi : IntegrableOn (fun r : ℝ ↦ r ^ ((d : ℝ) * σ - 1 - k)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
      refine hi.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
      have hr' : 0 < r := zero_lt_one.trans hr
      rw [max_eq_right hr.le, ← Real.rpow_natCast, ← Real.rpow_sub hr']
  let f (x : w.Completion) := ‖x‖ ^ ((d : ℝ) * σ - d) / (max 1 ‖x‖) ^ k
  have hν : SigmaFinite ν ∧ Integrable f ν := by
    dsimp only [ν]
    by_cases hw : w.IsReal
    · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
      let e := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm
      have hme := e.toHomeomorph.measurableEmbedding
      have hnorm (x : ℝ) : ‖e.toHomeomorph x‖ = ‖x‖ :=
        e.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) x
      exact ⟨hme.sigmaFinite_map, hme.integrable_map_iff.mpr (by
        simpa only [f, Function.comp_def, hnorm] using hRad ℝ volume (by simp [d, hw.mult_eq_one]))⟩
    · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right hw]
      have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw').symm
      have hme := e.toHomeomorph.measurableEmbedding
      have hnorm (x : ℂ) : ‖e.toHomeomorph x‖ = ‖x‖ :=
        e.isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm) x
      rw [show (2 • (volume : Measure ℂ)) = (2 : ℝ≥0) • volume by
        rw [two_nsmul, ← one_add_one_eq_two, add_smul, one_smul]]
      change SigmaFinite (Measure.map e.toHomeomorph ((2 : ℝ≥0) • volume)) ∧
        Integrable f (Measure.map e.toHomeomorph ((2 : ℝ≥0) • volume))
      have hi : Integrable (f ∘ e.toHomeomorph) volume := by
        simpa only [f, Function.comp_def, hnorm] using
          hRad ℂ volume (by simp [Complex.finrank_real_complex, d, hw'.mult_eq_two])
      exact ⟨hme.sigmaFinite_map, hme.integrable_map_iff.mpr (hi.smul_measure_nnreal (c := 2))⟩
  let : SigmaFinite ν := hν.1
  have hmap : Measure.map Units.val (infiniteLocalMultiplicativeTamagawaMeasure F w) =
      (ν.restrict U).withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, he.map_comap, ← hU,
      restrict_withDensity hmU]
  refine ⟨SigmaFinite.of_map _ he.measurable.aemeasurable (hmap ▸
    (SigmaFinite.withDensity_of_ne_top (hDf.mono fun _ h ↦ h.ne))), ?_⟩
  change Integrable ((fun x : w.Completion ↦
    ‖x‖ ^ ((d : ℝ) * σ) / (max 1 ‖x‖) ^ k) ∘ Units.val) _
  rw [← he.integrable_map_iff, hmap, integrable_withDensity_iff hD hDf]
  refine hν.2.restrict.congr ((ae_restrict_iff' hmU).mpr (ae_of_all _ fun x hx ↦ ?_))
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  dsimp [f, D]
  rw [ENNReal.toReal_inv, ← ENNReal.coe_pow, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnNorm, div_mul_eq_mul_div,
    ← div_eq_mul_inv, Real.rpow_sub hx', Real.rpow_natCast]

/-- A positive norm power at a finite place is integrable against the multiplicative
Tamagawa measure on units with bounded norm. -/
private theorem finiteLocalTamagawa_integrable_norm_rpow (v : HeightOneSpectrum (𝓞 F)) {σ : ℝ}
    (hσ : 0 < σ) (R : ℝ) :
    SigmaFinite (finiteLocalMultiplicativeTamagawaMeasure F v) ∧
    Integrable ({u : (v.adicCompletion F)ˣ | ‖u.val‖ ≤ R}.indicator (fun u ↦ ‖u.val‖ ^ σ))
      (finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  let K := v.adicCompletion F
  let O := v.adicCompletionIntegers F
  let : ProperSpace K := properSpace_adicCompletion v
  let : LocallyCompactSpace Kˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let : SecondCountableTopology Kˣ :=
    (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let μ := Measure.haar (G := Kˣ)
  let U : Set Kˣ := O.units
  have hUc : IsCompact U := by
    let : CompactSpace O := compactSpace_adicCompletionIntegers v
    let : CompactSpace Oˣ := compactSpace_units_of_compactSpace O
    let ι := Units.map O.subtype.toMonoidHom
    have hι : Continuous ι := continuous_subtype_val.units_map _
    have hrange : range ι = U := by
      ext u
      exact ⟨by rintro ⟨a, rfl⟩; exact ⟨a.val.property, a.inv.property⟩,
        fun hu ↦ ⟨O.toSubmonoid.unitsEquivUnitsType ⟨u, hu⟩, Units.ext rfl⟩⟩
    rw [← hrange]
    exact isCompact_range hι
  have hUo : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hUi : (interior U).Nonempty := by
    rw [hUo.interior_eq]
    exact ⟨1, O.units.one_mem⟩
  have hmass : μ U ≠ 0 := ne_of_gt (μ.measure_pos_of_nonempty_interior hUi)
  have hscale : ∃ a : ℝ≥0, finiteLocalMultiplicativeTamagawaMeasure F v = a • μ := by
    -- The prescribed mass on integer units is finite, and Haar gives them positive mass.
    let a : ℝ≥0∞ := (ENNReal.ofReal (Real.sqrt ((v.asIdeal.absNorm : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ / μ U
    have hn : (0 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
    have hsqrt := Real.sqrt_pos_of_pos (pow_pos hn (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))
    have ha : a ≠ ⊤ := ENNReal.div_ne_top
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsqrt))) hmass
    refine ⟨a.toNNReal, ?_⟩
    change finiteLocalMultiplicativeTamagawaMeasure F v = (↑a.toNNReal : ℝ≥0∞) • μ
    rw [ENNReal.coe_toNNReal ha]
    rfl
  obtain ⟨a, ha⟩ := hscale
  rw [ha]
  refine ⟨SMul.sigmaFinite a, ?_⟩
  apply Integrable.smul_measure_nnreal
  -- Every shell is a translate of the compact group of integer units.
  let val : Valuation K ℤᵐ⁰ := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hp : ‖p.val‖ = q⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  obtain ⟨e, hep, heι⟩ := finitePlace_unitDecomposition v p hp
  let ι := Units.map O.subtype.toMonoidHom
  have hdecomp (u : Kˣ) : u = p ^ (e u).1.toAdd * ι (e u).2 := by
    apply e.injective
    rw [map_mul, map_zpow, hep, heι]
    refine Prod.ext ?_ (by simp)
    change (e u).1.toAdd = (e u).1.toAdd * 1 + 0
    simp
  have hU (u : Kˣ) (hu : u ∈ U) : ‖u.val‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)
  have hnorm (k : ℤ) (u : Kˣ) (hu : u ∈ U) : ‖(p ^ k * u).val‖ = q⁻¹ ^ k := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow, hp, hU u hu, mul_one]
  let r (k : ℤ) := q⁻¹ ^ k
  let shell (k : ℤ) := (fun u : Kˣ ↦ p ^ k * u) '' U
  have hshell (k : ℤ) : IsCompact (shell k) := hUc.image (continuous_const.mul continuous_id)
  have hm (k : ℤ) : μ (shell k) = μ U := measure_smul μ (p ^ k) U
  have hcover : {u : Kˣ | ‖u.val‖ ≤ R} ⊆ ⋃ k : {k : ℤ // r k ≤ R}, shell k.val := by
    intro u hu
    have hz : ι (e u).2 ∈ U := ⟨(e u).2.val.property, (e u).2.inv.property⟩
    have hk : r (e u).1.toAdd ≤ R := by
      change ‖u.val‖ ≤ R at hu
      rwa [hdecomp u, hnorm _ _ hz] at hu
    exact mem_iUnion.mpr ⟨⟨_, hk⟩, ⟨_, hz, (hdecomp u).symm⟩⟩
  have hR : MeasurableSet {u : Kˣ | ‖u.val‖ ≤ R} :=
    (isClosed_le (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
  rw [integrable_indicator_iff hR]
  let f (u : Kˣ) := ‖u.val‖ ^ σ
  have hf : Continuous f := (continuous_norm.comp Units.continuous_val).rpow_const
    (fun _ ↦ Or.inr hσ.le)
  refine (integrableOn_iUnion_of_summable_integral_norm
    (fun (k : {k : ℤ // r k ≤ R}) ↦ hf.continuousOn.integrableOn_compact (hshell k.val)) ?_).mono_set hcover
  have hseq : Summable ({k : ℤ | r k ≤ R}.indicator (fun k ↦ (q⁻¹ ^ k) ^ σ)) := by
    let G := {k : ℤ | r k ≤ R}.indicator (fun k ↦ (q⁻¹ ^ k) ^ σ)
    change Summable G
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine (summable_geometric_of_lt_one (r := q⁻¹ ^ σ) (by positivity)
        (Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hq) hσ)).of_nonneg_of_le ?_ ?_
      · intro n
        exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
      · intro n
        have heq : (q⁻¹ ^ σ) ^ n = (q⁻¹ ^ (n : ℤ)) ^ σ := by
          rw [← zpow_natCast, Real.rpow_zpow_comm (by positivity)]
        rw [heq]
        exact (Set.indicator_le_self' (s := {k : ℤ | r k ≤ R})
          (f := fun k ↦ (q⁻¹ ^ k) ^ σ) (fun _ _ ↦ by positivity)) n
    · obtain ⟨N, hN⟩ := eventually_atTop.mp
        ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop R)
      refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn ↦ ?_)
      have hlt : R < r (-(n : ℤ)) := by
        simpa [r, zpow_neg, inv_zpow] using hN n (by simpa using hn)
      exact Set.indicator_of_notMem (not_le.mpr hlt) _
  have hsub : Summable (fun (k : {k : ℤ // r k ≤ R}) ↦ r k.val ^ σ) := by
    refine (hseq.comp_injective Subtype.val_injective).congr ?_
    intro k
    exact Set.indicator_of_mem k.property _
  refine (hsub.mul_right (μ.real U)).congr fun k ↦ ?_
  have hEq : Set.EqOn (fun u : Kˣ ↦ ‖f u‖) (fun _ ↦ r k.val ^ σ) (shell k.val) := by
    rintro _ ⟨u, hu, rfl⟩
    change ‖‖(p ^ k.val * u).val‖ ^ σ‖ = r k.val ^ σ
    rw [hnorm _ _ hu, Real.norm_of_nonneg (by positivity)]
  rw [setIntegral_congr_fun (hshell _).measurableSet hEq, setIntegral_const]
  change r k.val ^ σ * (μ U).toReal = (μ (shell k.val)).toReal * r k.val ^ σ
  rw [hm, mul_comm]

/-- The modulus of a norm twist of a unitary character is the corresponding real norm power. -/
private theorem norm_sLocalNormTwist (χ : PontryaginDual Jₛ) (s : ℂ) (g : Iₛ) :
    ‖chartₛ(χ) s (classOf g)‖ =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ ((w.mult : ℝ) * s.re)) *
        ∏ v : S, ‖g.val.2 v‖ ^ s.re := by
  change ‖(χ (classOf g) : ℂ) * (modℂ[mₛ, classOf g]) ^ s‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hnorm : (((sIdeleNorm F S g : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖ := by
    simp [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_pow]
  rw [hnorm, Real.mul_rpow (by positivity) (by positivity)]
  have hprod {ι : Type _} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
      (∏ i, a i) ^ s.re = ∏ i, a i ^ s.re := by
    classical
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | insert i t hi ht =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (ha i) (Finset.prod_nonneg fun j _ ↦ ha j), ht]
  apply congrArg₂ (· * ·)
  · exact (hprod (fun w : InfinitePlace F ↦ ‖g.val.1 w‖ ^ w.mult)
      (fun w ↦ pow_nonneg (norm_nonneg (g.val.1 w)) w.mult)).trans
      (Finset.prod_congr rfl fun w _ ↦
        (Real.rpow_natCast_mul (norm_nonneg (g.val.1 w)) w.mult s.re).symm)
  · exact hprod (fun v : S ↦ ‖g.val.2 v‖) (fun v ↦ norm_nonneg (g.val.2 v))

/-- Paper: Theorem 3.3.1.1(1), p. 129. The S-idele integrand is absolutely
integrable on the positive half-plane. -/
theorem sLocalIdelicZetaIntegral_integrable (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val) * c (classOf g)) μₛ := by
  classical
  obtain ⟨χ, s, hs, rfl⟩ := hc
  have hσ : 0 < s.re := hs
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * s.re)
  have hw (w : InfinitePlace F) : (w.mult : ℝ) * s.re < k := by
    have hm : (w.mult : ℝ) ≤ 2 := by
      by_cases h : w.IsReal
      · simp [h.mult_eq_one]
      · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
    exact (mul_le_mul_of_nonneg_right hm hσ.le).trans_lt hk
  obtain ⟨C, hC, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound F S f
  have hR (v : S) : ∃ r : ℝ, ∀ x ∈ C, ‖x v‖ ≤ r :=
    hC.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose R hR using hR
  obtain ⟨B₀, hB₀, hb₀⟩ := hdecay 0
  obtain ⟨B₁, hB₁, hb₁⟩ := hdecay (∑ _w : InfinitePlace F, k)
  let B := max B₀ B₁
  have hBd (x : Aₛ) :
      ‖f (Multiplicative.ofAdd x)‖ * (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤ B := by
    let r := ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x.1‖
    have hprod : (∏ w : InfinitePlace F, (max 1 ‖x.1 w‖) ^ k) ≤
        (max 1 r) ^ (∑ _w : InfinitePlace F, k) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity)
        (fun w _ ↦ pow_le_pow_left₀ (by positivity)
          (max_le_max le_rfl (infinitePlace_norm_le_mixedNorm x.1 w)) _)
    refine (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)).trans ?_
    rcases le_total r 1 with hr | hr
    · simpa [max_eq_left hr, B] using (show ‖f (Multiplicative.ofAdd x)‖ ≤ max B₀ B₁ from
        (by simpa using hb₀ x : ‖f (Multiplicative.ofAdd x)‖ ≤ B₀).trans (le_max_left _ _))
    · rw [max_eq_right hr]
      exact (hb₁ x).trans (le_max_right _ _)
  -- The coordinate bounds give an integrable product majorant.
  let a (w : InfinitePlace F) (u : w.Completionˣ) :=
    ‖u.val‖ ^ ((w.mult : ℝ) * s.re) / (max 1 ‖u.val‖) ^ k
  let b (v : S) := {u : (v.val.adicCompletion F)ˣ | ‖u.val‖ ≤ R v}.indicator
    (fun u ↦ ‖u.val‖ ^ s.re)
  let μa := infiniteLocalMultiplicativeTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  have ha (w : InfinitePlace F) := infiniteLocalTamagawa_integrable_norm_rpow w hσ k (hw w)
  have hb (v : S) := finiteLocalTamagawa_integrable_norm_rpow v.val hσ (R v)
  let (w : InfinitePlace F) : SigmaFinite (μa w) := (ha w).1
  let (v : S) : SigmaFinite (μb v) := (hb v).1
  have hmajor := ((Integrable.fintype_prod_dep (fun w ↦ (ha w).2)).mul_prod
    (Integrable.fintype_prod_dep (fun v ↦ (hb v).2))).const_mul B
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let E := e.toHomeomorph.trans (eArch.toHomeomorph.prodCongr eS.toHomeomorph)
  have hE : Measurable E := by
    apply Measurable.prodMk
    · exact Measurable.of_eval fun w ↦ measurable_comap_iff.mpr
        ((measurable_pi_apply w).comp (measurable_fst.comp MeasurableSpace.le_map_comap))
    · apply Measurable.of_eval
      intro v
      have hborel : borel (v.val.adicCompletion F)ˣ =
          (borel (v.val.adicCompletion F)).comap Units.val := by
        rw [(Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)).eq_induced, borel_comap]
      change @Measurable Iₛ _ _ (borel _) _
      rw [hborel]
      exact measurable_comap_iff.mpr
        ((measurable_pi_apply v).comp (measurable_snd.comp MeasurableSpace.le_map_comap))
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)).secondCountableTopology
  let : BorelSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))
  let : BorelSpace Aₛ :=
    inferInstanceAs (BorelSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  have hE' : Measurable E.symm :=
    measurable_comap_iff.mpr
      ((Units.continuous_val : Continuous (Units.val : Iₛ → Aₛ)).comp E.symm.continuous).measurable
  let em : Iₛ ≃ᵐ _ := ⟨E.toEquiv, hE, hE'⟩
  have hmap : μₛ = ((Measure.pi μa).prod (Measure.pi μb)).map em.symm := rfl
  rw [hmap]
  apply em.symm.measurableEmbedding.integrable_map_iff.mpr
  refine hmajor.mono' ?_ (ae_of_all _ fun p ↦ ?_)
  · have hf : Continuous (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val)) :=
      (schwartzBruhat_continuous (G := Multiplicative Aₛ) f).comp
        (Units.continuous_val : Continuous (Units.val : Iₛ → Aₛ))
    have hc' : Continuous (fun g : Iₛ ↦ chartₛ(χ) s (classOf g)) :=
      (chartₛ(χ) s).continuous.comp continuous_quotient_mk'
    exact ((hf.mul hc').comp E.symm.continuous).aestronglyMeasurable
  · let g := em.symm p
    change ‖f (Multiplicative.ofAdd g.val) * chartₛ(χ) s (classOf g)‖ ≤
      B * ((∏ w, a w (p.1 w)) * ∏ v, b v (p.2 v))
    have h₁ (w : InfinitePlace F) : g.val.1 w = (p.1 w).val := rfl
    have h₂ (v : S) : g.val.2 v = (p.2 v).val := rfl
    rw [norm_mul, norm_sLocalNormTwist]
    simp_rw [h₁, h₂]
    by_cases hp : g.val.2 ∈ C
    · have hb' (v : S) : b v (p.2 v) = ‖(p.2 v).val‖ ^ s.re :=
        Set.indicator_of_mem (by simpa [← h₂ v] using hR v g.val.2 hp) _
      simp_rw [hb', a, Finset.prod_div_distrib]
      have hD : 0 < ∏ w : InfinitePlace F, (max 1 ‖(p.1 w).val‖) ^ k := by positivity
      rw [div_mul_eq_mul_div, ← mul_div_assoc, le_div_iff₀ hD]
      have h := hBd g.val
      simp_rw [h₁] at h
      calc
        _ = (‖f (Multiplicative.ofAdd g.val)‖ * ∏ w : InfinitePlace F,
              (max 1 ‖(p.1 w).val‖) ^ k) *
            ((∏ w : InfinitePlace F, ‖(p.1 w).val‖ ^ ((w.mult : ℝ) * s.re)) *
              ∏ v : S, ‖(p.2 v).val‖ ^ s.re) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)
    · rw [hsupport g.val hp, norm_zero, zero_mul]
      exact mul_nonneg (hB₀.trans (le_max_left _ _)) (mul_nonneg
        (Finset.prod_nonneg fun _ _ ↦ by dsimp [a]; positivity)
        (Finset.prod_nonneg fun v _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) _))

end AbsoluteConvergence

/-- Paper: Equation (3.3.1.1), p. 129. At the bare norm character the integrand
is the test function times the S-idelic norm. -/
theorem sLocalIdelicZetaIntegral_norm (f : ℬ(Aₛ)) :
    sLocalIdelicZetaIntegral f (chartₛ((1 : PontryaginDual Jₛ)) 1) =
      ∫ g : Iₛ, f (Multiplicative.ofAdd g.val) * modℂ[sIdeleNorm F S, g] ∂μₛ := by
  unfold sLocalIdelicZetaIntegral
  congr 1
  funext g
  congr 1
  change (((1 : PontryaginDual Jₛ) (classOf g) : Circle) : ℂ) *
    (modℂ[mₛ, classOf g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one, sIdeleQuotientNorm_mk, PontryaginDual.one_apply, Circle.coe_one, one_mul]

/-- Paper: Theorem 3.3.1.1(1) and Remark 3.3.1.2, p. 129. Closed norm-band
truncations of the zeta integral converge uniformly on compact subsets.
Deviation: The positive band widths are indexed by n + 1. -/
theorem sLocalIdelicZetaIntegral_tendstoUniformlyOn (f : ℬ(Aₛ))
    (K : Set Xₛ) (hK : IsCompact K) (hKpos : K ⊆ positive) :
    TendstoUniformlyOn (fun (n : ℕ) c ↦
      ∫ g in band[sIdeleNorm F S, n], f (Multiplicative.ofAdd g.val) * c (classOf g) ∂μₛ)
      (sLocalIdelicZetaIntegral f) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  have hne : ∃ x, mₛ x ≠ 1 := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨σ t, (hσ t).trans_ne ht⟩
  let abscissa := quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  have habs : Continuous abscissa :=
    continuous_quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne habs.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne habs.continuousOn
  let r (g : Iₛ) : ℝ := (sIdeleNorm F S g : ℝ≥0)
  have hr (g : Iₛ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hnorm {c : Xₛ} (hc : c ∈ K) (g : Iₛ) : ‖c (classOf g)‖ = r g ^ abscissa c := by
    obtain ⟨χ, s, -, rfl⟩ := hKpos hc
    have hs : abscissa (chartₛ(χ) s) = s.re :=
      quasiCharacterAbscissa_of_unitary_twist mₛ (isProperMap_sIdeleQuotientNorm F S) hne
        _ χ s (fun _ ↦ rfl)
    change ‖(χ (classOf g) : ℂ) * (modℂ[mₛ, classOf g]) ^ s‖ = _
    rw [hs, norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (hr g) s
  let integrand (c : Xₛ) (g : Iₛ) := f (Multiplicative.ofAdd g.val) * c (classOf g)
  have hint {c : Xₛ} (hc : c ∈ K) : Integrable (integrand c) μₛ :=
    sLocalIdelicZetaIntegral_integrable f c (hKpos hc)
  -- The two endpoint characters bound the integrands below and above norm one.
  let bound (g : Iₛ) := ‖integrand a g‖ + ‖integrand b g‖
  have hbound : Integrable bound μₛ := (hint ha).norm.add (hint hb).norm
  have hle {c : Xₛ} (hc : c ∈ K) (g : Iₛ) : ‖integrand c g‖ ≤ bound g := by
    have hweighted {d : Xₛ} (h : ‖c (classOf g)‖ ≤ ‖d (classOf g)‖) :
        ‖integrand c g‖ ≤ ‖integrand d g‖ := by
      dsimp only [integrand]
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
    by_cases hg : r g ≤ 1
    · refine (hweighted (d := a) ?_).trans (le_add_of_nonneg_right (norm_nonneg (integrand b g)))
      rw [hnorm hc, hnorm ha]
      exact Real.rpow_le_rpow_of_exponent_ge (hr g) hg (hmin hc)
    · refine (hweighted (d := b) ?_).trans (le_add_of_nonneg_left (norm_nonneg (integrand a g)))
      rw [hnorm hc, hnorm hb]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hg) (hmax hc)
  let B (n : ℕ) : Set Iₛ := band[sIdeleNorm F S, n]
  have hB (n : ℕ) : MeasurableSet (B n) := by
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    let : BorelSpace Iₛ := ⟨by
      change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace Aₛ) = _
      rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap,
        BorelSpace.measurable_eq (α := Aₛ)]⟩
    have hnorm_cont : Continuous (fun g : Iₛ ↦ mₛ (classOf g)) :=
      Continuous.comp hmₛ QuotientGroup.continuous_mk
    have hrcont : Continuous r :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp hnorm_cont)
    exact hrcont.measurable measurableSet_Icc
  have hBmono : Monotone B := by
    intro i j hij g hg
    have hij' : (i : ℝ) + 1 ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    exact ⟨((inv_le_inv₀ (by positivity) (by positivity)).mpr hij').trans hg.1,
      hg.2.trans hij'⟩
  have htail : (⋂ n, (B n)ᶜ) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro g hg
    obtain ⟨n, hn⟩ := exists_nat_gt (max (r g) (r g)⁻¹)
    have hn' : max (r g) (r g)⁻¹ ≤ (n : ℝ) + 1 :=
      hn.le.trans (le_add_of_nonneg_right zero_le_one)
    have hmem : g ∈ B n :=
      ⟨(inv_le_comm₀ (by positivity) (hr g)).2 ((le_max_right _ _).trans hn'),
        (le_max_left _ _).trans hn'⟩
    exact (mem_iInter.mp hg n) hmem
  have hlim : Tendsto (fun n ↦ ∫ g in (B n)ᶜ, bound g ∂μₛ) atTop (𝓝 0) := by
    simpa only [htail, setIntegral_empty] using
      (tendsto_setIntegral_of_antitone (μ := μₛ) (f := bound) (fun n ↦ (hB n).compl)
        (fun _ _ hij ↦ compl_subset_compl.mpr (hBmono hij)) ⟨0, hbound.integrableOn⟩)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn c hc
  change dist (∫ g, integrand c g ∂μₛ) (∫ g in B n, integrand c g ∂μₛ) < ε
  rw [dist_eq_norm, ← integral_add_compl (hB n) (hint hc), add_sub_cancel_left]
  calc
    ‖∫ g in (B n)ᶜ, integrand c g ∂μₛ‖ ≤ ∫ g in (B n)ᶜ, ‖integrand c g‖ ∂μₛ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g in (B n)ᶜ, bound g ∂μₛ :=
      setIntegral_mono_on (hint hc).norm.integrableOn hbound.integrableOn (hB n).compl
        (fun g _ ↦ hle hc g)
    _ < ε := hn

/-- A logarithm times a power with exponent in (σ/2, 3σ/2) is bounded by a multiple
of the sum of the σ/4-th and 7σ/4-th powers. -/
private theorem rpow_mul_abs_log_le_of_mem_Ioo {σ x r : ℝ} (hσ : 0 < σ)
    (hx : x ∈ Ioo (σ / 2) (3 * σ / 2)) (hr : 0 < r) :
    r ^ x * |Real.log r| ≤ 4 / σ * (r ^ (σ / 4) + r ^ (7 * σ / 4)) := by
  have hε : 0 < σ / 4 := by positivity
  rcases le_or_gt 1 r with h1 | h1
  · have hlog := Real.log_le_rpow_div hr.le hε
    have hpow : r ^ x ≤ r ^ (3 * σ / 2) := Real.rpow_le_rpow_of_exponent_le h1 hx.2.le
    rw [abs_of_nonneg (Real.log_nonneg h1)]
    calc r ^ x * Real.log r ≤ r ^ (3 * σ / 2) * (r ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg h1) (by positivity)
      _ = 4 / σ * r ^ (7 * σ / 4) := by
          rw [mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]
  · have hlog := Real.log_le_rpow_div (inv_pos.mpr hr).le hε
    have hpow : r ^ x ≤ r ^ (σ / 2) := Real.rpow_le_rpow_of_exponent_ge hr h1.le hx.1.le
    rw [abs_of_neg (Real.log_neg hr h1), ← Real.log_inv]
    calc r ^ x * Real.log r⁻¹ ≤ r ^ (σ / 2) * (r⁻¹ ^ (σ / 4) / (σ / 4)) :=
          mul_le_mul hpow hlog (Real.log_nonneg ((one_le_inv₀ hr).mpr h1.le)) (by positivity)
      _ = 4 / σ * r ^ (σ / 4) := by
          rw [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, mul_div_assoc', ← Real.rpow_add hr]
          field_simp
          ring_nf
      _ ≤ _ := by
          have : 0 ≤ r ^ (7 * σ / 4) := by positivity
          nlinarith [show 0 < 4 / σ by positivity]

/-- Paper: Theorem 3.3.1.1(1), p. 129. The zeta integral is holomorphic in
every norm-twist coordinate on the right half-plane. -/
theorem sLocalIdelicZetaIntegral_analyticOn (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZetaIntegral f (chartₛ(χ) s)) rightHalf := by
  have hopen : IsOpen (rightHalf : Set ℂ) := isOpen_Ioi.preimage Complex.continuous_re
  refine DifferentiableOn.analyticOnNhd (fun s hs ↦ ?_) hopen
  refine DifferentiableAt.differentiableWithinAt ?_
  have hσ : 0 < s.re := hs
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let : BorelSpace Aₛ := inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : BorelSpace Iₛ := ⟨by
    change MeasurableSpace.comap Units.val (inferInstance : MeasurableSpace Aₛ) = _
    rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap,
      BorelSpace.measurable_eq (α := Aₛ)]⟩
  let r (g : Iₛ) : ℝ := ((mₛ (classOf g) : ℝ≥0) : ℝ)
  have hr (g : Iₛ) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrcont : Continuous r :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (Continuous.comp hmₛ QuotientGroup.continuous_mk))
  let W (z : ℂ) (g : Iₛ) : ℂ := f (Multiplicative.ofAdd g.val) * chartₛ(χ) z (classOf g)
  let D (z : ℂ) (g : Iₛ) : ℂ := W z g * Complex.log (r g : ℂ)
  have hnormW (χ' : PontryaginDual Jₛ) (z : ℂ) (g : Iₛ) :
      ‖f (Multiplicative.ofAdd g.val) * chartₛ(χ') z (classOf g)‖ =
        ‖f (Multiplicative.ofAdd g.val)‖ * r g ^ z.re := by
    change ‖f (Multiplicative.ofAdd g.val) * ((χ' (classOf g) : ℂ) * (r g : ℂ) ^ z)‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hr g)]
  let V : Set ℂ := Complex.re ⁻¹' Ioo (s.re / 2) (3 * s.re / 2)
  have hV : V ∈ 𝓝 s := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
    (show s.re ∈ Ioo (s.re / 2) (3 * s.re / 2) from ⟨by linarith, by linarith⟩)
  have hint (χ' : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) :
      Integrable (fun g : Iₛ ↦ f (Multiplicative.ofAdd g.val) * chartₛ(χ') z (classOf g)) μₛ :=
    sLocalIdelicZetaIntegral_integrable f _ ⟨χ', z, hz, rfl⟩
  have hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (W z) μₛ :=
    Filter.mem_of_superset hV fun z hz ↦ (hint χ z (by
      have h := hz.1
      linarith)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D s) μₛ :=
    (hint χ s hσ).aestronglyMeasurable.mul (Complex.measurable_log.comp
      (Complex.continuous_ofReal.comp hrcont).measurable).aestronglyMeasurable
  let P (a : ℝ) (g : Iₛ) : ℂ :=
    f (Multiplicative.ofAdd g.val) * chartₛ((1 : PontryaginDual Jₛ)) (a : ℂ) (classOf g)
  have hPint (a : ℝ) (ha : 0 < a) : Integrable (P a) μₛ :=
    hint 1 (a : ℂ) (by simpa using ha)
  let bound (g : Iₛ) : ℝ := 4 / s.re * (‖P (s.re / 4) g‖ + ‖P (7 * s.re / 4) g‖)
  have hbound : Integrable bound μₛ :=
    ((hPint _ (by positivity)).norm.add (hPint _ (by positivity)).norm).const_mul _
  have hDbound : ∀ᵐ g ∂μₛ, ∀ z ∈ V, ‖D z g‖ ≤ bound g := Eventually.of_forall fun g z hz ↦ by
    have hlog : Complex.log (r g : ℂ) = (Real.log (r g) : ℂ) :=
      (Complex.ofReal_log (hr g).le).symm
    change ‖W z g * Complex.log (r g : ℂ)‖ ≤
      4 / s.re * (‖P (s.re / 4) g‖ + ‖P (7 * s.re / 4) g‖)
    rw [norm_mul, hnormW, hlog, Complex.norm_real, Real.norm_eq_abs, hnormW, hnormW,
      Complex.ofReal_re, Complex.ofReal_re, mul_assoc]
    calc ‖f (Multiplicative.ofAdd g.val)‖ * (r g ^ z.re * |Real.log (r g)|)
        ≤ ‖f (Multiplicative.ofAdd g.val)‖ *
          (4 / s.re * (r g ^ (s.re / 4) + r g ^ (7 * s.re / 4))) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le_of_mem_Ioo hσ hz (hr g))
            (norm_nonneg _)
      _ = _ := by ring
  have hdiff : ∀ᵐ g ∂μₛ, ∀ z ∈ V, HasDerivAt (fun w ↦ W w g) (D z g) z :=
    Eventually.of_forall fun g z _ ↦ by
      have hg : (r g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hr g).ne'
      change HasDerivAt (fun w : ℂ ↦ f (Multiplicative.ofAdd g.val) *
          ((χ (classOf g) : ℂ) * (r g : ℂ) ^ w))
        ((f (Multiplicative.ofAdd g.val) * ((χ (classOf g) : ℂ) * (r g : ℂ) ^ z)) *
          Complex.log (r g : ℂ)) z
      simpa only [id_eq, mul_assoc, mul_one] using
        (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul
          (χ (classOf g) : ℂ)).const_mul (f (Multiplicative.ofAdd g.val))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas (hint χ s hσ) hDmeas
    hDbound hbound hdiff).2.differentiableAt

section LocalFactors

variable {K : Type*} [Field K] [TopologicalSpace K] [MeasurableSpace Kˣ]

/-- Paper: Equation (3.3.1.7), p. 130. The local zeta integral integrates
the test function times the local quasi-character on the unit group. -/
def localIdelicZetaIntegral (μ : Measure Kˣ) (f : K → ℂ) (c : QuasiCharacter Kˣ) : ℂ :=
  ∫ g : Kˣ, f g.val * c g ∂μ

/-- Paper: Equation (3.3.2.1), p. 137. On an indicator of a set of finite
measure on which the character is trivial, the local zeta integral is its mass. -/
theorem localIdelicZetaIntegral_indicator (μ : Measure Kˣ) (c : QuasiCharacter Kˣ)
    (U : Set Kˣ) (hU : MeasurableSet U) (hfin : μ U ≠ ⊤) (hc : ∀ g ∈ U, c g = 1) :
    localIdelicZetaIntegral μ ((Units.val '' U).indicator (fun _ ↦ 1)) c = (μ U).toReal := by
  have h (g : Kˣ) : (Units.val '' U).indicator (fun _ ↦ (1 : ℂ)) g.val * c g =
      U.indicator (fun _ ↦ (1 : ℂ)) g := by
    by_cases hg : g ∈ U
    · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hg), Set.indicator_of_mem hg, hc g hg,
        one_mul]
    · rw [Set.indicator_of_notMem, Set.indicator_of_notMem hg, zero_mul]
      rintro ⟨x, hx, hxg⟩
      exact hg (Units.ext hxg ▸ hx)
  unfold localIdelicZetaIntegral
  simp_rw [h]
  rw [integral_indicator_const _ hU, measureReal_def, Complex.real_smul, mul_one]

variable [IsTopologicalGroup Kˣ]

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. A local Tate factor is meromorphic
in norm-twist coordinates and gives the local Fourier equation on the strip
of simultaneous absolute convergence. -/
def IsLocalTateFactor (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ)
    (fourier : (K → ℂ) → K → ℂ) (ρ : QuasiCharacter Kˣ → ℂ) : Prop :=
  (∀ χ : PontryaginDual Kˣ,
    MeromorphicNFOn (fun s ↦ ρ (quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s)) univ) ∧
  ∀ (f : ℬ(K)) (χ : PontryaginDual Kˣ) (s : ℂ), s ∈ criticalStrip →
    let c := quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s
    let test := fun x ↦ f (Multiplicative.ofAdd x)
    localIdelicZetaIntegral μ test c =
      ρ c * localIdelicZetaIntegral μ (fourier test) (dualQuasiCharacter m hm c)

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. A nonzero transformed zeta integral
on the strip determines the correcting factor by a ratio. -/
theorem IsLocalTateFactor.eq_div {m : Kˣ →* ℝ≥0ˣ} {hm : Continuous m} {μ : Measure Kˣ}
    {fourier : (K → ℂ) → K → ℂ} {ρ : QuasiCharacter Kˣ → ℂ}
    (hρ : IsLocalTateFactor m hm μ fourier ρ) (f : ℬ(K)) (χ : PontryaginDual Kˣ)
    (s : ℂ) (hs : s ∈ criticalStrip) :
    let c := quasiCharacterNormTwist m hm ((circleToComplex).comp χ) s
    let test := fun x ↦ f (Multiplicative.ofAdd x)
    let Zdual := localIdelicZetaIntegral μ (fourier test) (dualQuasiCharacter m hm c)
    Zdual ≠ 0 → ρ c = localIdelicZetaIntegral μ test c / Zdual := by
  intro c test Zdual hZ
  rw [hρ.2 f χ s hs, mul_div_cancel_right₀ _ hZ]

end LocalFactors

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "infiniteNorm(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "finiteNorm(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)

local instance (v : Primes) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

local notation "infiniteFourier(" w ")" => tamagawaFourier (infiniteLocalAdditiveTamagawaMeasure F w)
  (fun x ↦ adeleStandardCharacter F (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "finiteFourier(" v ")" => tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v)
  (finiteLocalStandardCharacter F v)

/-- Paper: Equation (3.3.1.3), p. 129. The normalized archimedean module is continuous. -/
theorem continuous_infiniteLocalModule (w : InfinitePlace F) :
    Continuous (infiniteNorm(w)) := by
  change Continuous (fun x : w.Completionˣ ↦
    Units.map nnNormHom.toMonoidHom x ^ InfinitePlace.mult w)
  exact (continuous_nnNorm.units_map _).pow _

/-- Paper: Equation (3.3.1.3), p. 129. The normalized finite-place module is continuous. -/
theorem continuous_finiteLocalModule (v : Primes) :
    Continuous (finiteNorm(v)) := by
  exact continuous_nnNorm.units_map _

omit [NumberField F] in
/-- Paper: Definition A.3.2.2(1), p. 560. The archimedean local multiplicative Tamagawa
measure `dx / |x|ᵥ` is a Haar measure on the local unit group. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (w : InfinitePlace F) :
    (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let := infiniteLocalAdditiveTamagawaMeasure_haar F w
  unfold infiniteLocalMultiplicativeTamagawaMeasure
  apply isHaarMeasure_comap_units_withDensity
  intro a ha
  by_cases h : w.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    let e := (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm
    have he : Measurable e := (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous.measurable
    rw [map_mul_left_map_ringEquiv e he volume _ real_map_mul_left_volume a ha, h.mult_eq_one]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal h).norm_map_of_map_zero (map_zero _) a
    rw [hn]
  · have h' := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex h').symm
    have he : Measurable e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex h').symm.continuous.measurable
    have hscale (b : ℂ) (hb : b ≠ 0) : ((2 : ℕ) • (volume : Measure ℂ)).map (b * ·) =
        (((‖b‖₊ ^ 2 : ℝ≥0) : ENNReal))⁻¹ • ((2 : ℕ) • (volume : Measure ℂ)) := by
      rw [Measure.map_smul, complex_map_mul_left_volume b hb, ← Nat.cast_smul_eq_nsmul ENNReal,
        ← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, smul_smul, mul_comm]
      exact (measurable_const_mul b).aemeasurable
    rw [map_mul_left_map_ringEquiv e he _ _ hscale a ha, h'.mult_eq_two]
    have hn : ‖e.symm a‖₊ = ‖a‖₊ := by
      ext
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a
    rw [hn]

/-- A meromorphic identity on the open critical strip holds off a discrete
set in the whole complex plane. -/
private theorem sLocal_meromorphic_identity {a b : ℂ → ℂ} (ha : Meromorphic a) (hb : Meromorphic b)
    (h : EqOn a b criticalStrip) : a =ᶠ[codiscrete ℂ] b := by
  let Δ := a - b
  have hΔ : MeromorphicOn Δ univ := fun x _ ↦ (ha x).sub (hb x)
  have h₀ : meromorphicOrderAt Δ (1 / 2) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have ho : IsOpen criticalStrip := isOpen_Ioo.preimage Complex.continuous_re
    have hm : (1 / 2 : ℂ) ∈ criticalStrip := by
      change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
      norm_num
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hm)] with z hz using sub_eq_zero.mpr (h hz)
  apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.2
  intro x
  exact (meromorphicOrderAt_eq_top_iff.mp (hΔ.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ x) h₀)).mono fun z hz ↦ sub_eq_zero.mp hz

section FactorPatching

local notation "leftHalf" => (Complex.re ⁻¹' Iio (1 : ℝ))

/-- Two quotients with equal cross-products agree if their numerators are
both nonzero, including the zero value assigned at a pole. -/
private theorem div_eq_div_of_nonzero_numerators {a b c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : a * d = c * b) : a / b = c / d := by
  apply inv_injective
  rw [inv_div, inv_div]
  exact (div_eq_div_iff ha hc).2 (by simpa only [mul_comm] using h.symm)

/-- Patch local zeta quotients in each norm chart. On the right use tests
with compactly supported Fourier transform, and on the left use compactly
supported tests. Cross multiplication extends from the common strip by the
identity theorem. A nonzero numerator at a pole enforces normal form. -/
private theorem localFactor_patch {X I T : Type*} (J : I → ℂ → X) (σ : X → ℝ)
    (hσ : ∀ i z, σ (J i z) = z.re) (hcov : ∀ x, ∃ i z, J i z = x)
    (N D : T → X → ℂ) (P Q : T → Prop)
    (hP : ∀ x, ∃ p, P p ∧ N p x ≠ 0) (hQ : ∀ x, ∃ q, Q q ∧ D q x ≠ 0)
    (hN : ∀ t i, AnalyticOnNhd ℂ (N t ∘ J i) rightHalf)
    (hD : ∀ t i, AnalyticOnNhd ℂ (D t ∘ J i) leftHalf)
    (hNL : ∀ t, P t → ∀ i, AnalyticOnNhd ℂ (N t ∘ J i) leftHalf)
    (hDR : ∀ t, Q t → ∀ i, AnalyticOnNhd ℂ (D t ∘ J i) rightHalf)
    (he : ∀ i z, z ∈ criticalStrip → ∀ t u, N t (J i z) * D u (J i z) = N u (J i z) * D t (J i z)) :
    let E (R : X → ℂ) := (∀ i, MeromorphicNFOn (R ∘ J i) univ) ∧
      ∀ i z, z ∈ criticalStrip → ∀ t, N t (J i z) = R (J i z) * D t (J i z)
    (∃! R, E R) ∧ ∀ R, E R → ∀ i, AnalyticOnNhd ℂ (R ∘ J i) rightHalf := by
  intro E
  classical
  choose p hp hpn using hP
  choose q hq hqd using hQ
  let ratio (t : T) (x : X) := N t x / D t x
  let R (x : X) := if 0 < σ x then ratio (q x) x else ratio (p x) x
  have hmid : (1 / 2 : ℂ) ∈ criticalStrip := by
    change 0 < (1 / 2 : ℂ).re ∧ (1 / 2 : ℂ).re < 1
    norm_num
  have ho : ∀ᶠ w in 𝓝 (1 / 2 : ℂ), w ∈ criticalStrip := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hmid
  have cross (U : Set ℂ) (hU : IsPreconnected U) (hmidU : (1 / 2 : ℂ) ∈ U) (i : I) (t u : T)
      (nt : AnalyticOnNhd ℂ (N t ∘ J i) U) (nu : AnalyticOnNhd ℂ (N u ∘ J i) U)
      (dt : AnalyticOnNhd ℂ (D t ∘ J i) U) (du : AnalyticOnNhd ℂ (D u ∘ J i) U) :
      ∀ z ∈ U, N t (J i z) * D u (J i z) = N u (J i z) * D t (J i z) := by
    exact fun _ hz ↦ (nt.mul du).eqOn_of_preconnected_of_eventuallyEq (nu.mul dt) hU hmidU
      (ho.mono fun z hz ↦ he i z hz t u) hz
  have onRight (i : I) (z : ℂ) (hz : z ∈ rightHalf) (t : T)
      (ht : Q t) (hne : D t (J i z) ≠ 0) : R (J i z) = ratio t (J i z) := by
    let x := J i z
    rw [show R x = ratio (q x) x from ite_eq_left (by change 0 < σ (J i z); rw [hσ]; exact hz)]
    exact (div_eq_div_iff (hqd x) hne).mpr (cross _ (convex_halfSpace_re_gt 0).isPreconnected hmid.1
      i (q x) t (hN _ _) (hN _ _) (hDR _ (hq x) _) (hDR _ ht _) z hz)
  have onLeft (i : I) (z : ℂ) (hz : z ∈ leftHalf) (t : T)
      (ht : P t) (hne : N t (J i z) ≠ 0) : R (J i z) = ratio t (J i z) := by
    let x := J i z
    by_cases hr : 0 < σ x
    · rw [show R x = ratio (q x) x from ite_eq_left hr]
      have h := he i z ⟨by simpa only [x, hσ] using hr, hz⟩ (q x) t
      exact (div_eq_div_iff (hqd x) (right_ne_zero_of_mul (h.trans_ne (mul_ne_zero hne (hqd x))))).mpr h
    · rw [show R x = ratio (p x) x from ite_eq_right hr]
      exact div_eq_div_of_nonzero_numerators (hpn x) hne
        (cross _ (convex_halfSpace_re_lt 1).isPreconnected hmid.2 i (p x) t
          (hNL _ (hp x) _) (hNL _ ht _) (hD _ _) (hD _ _) z hz)
  have hreg (i : I) (z : ℂ) (hz : z ∈ rightHalf) : AnalyticAt ℂ (R ∘ J i) z := by
    let x := J i z
    let t := q x
    have hd := hDR t (hq x) i z hz
    have hne : (D t ∘ J i) z ≠ 0 := hqd x
    have heq : R ∘ J i =ᶠ[𝓝 z] (N t ∘ J i) / (D t ∘ J i) := by
      filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hz,
        hd.continuousAt.eventually_ne hne] with w hw hs using onRight i w hw t (hq x) hs
    exact ((hN t i z hz).div hd hne).congr heq.symm
  have hnf (i : I) : MeromorphicNFOn (R ∘ J i) univ := by
    intro z _
    let x := J i z
    by_cases hz : z ∈ rightHalf
    · exact (hreg i z hz).meromorphicNFAt
    · have hl : z ∈ leftHalf := lt_of_le_of_lt (le_of_not_gt hz) zero_lt_one
      let t := p x
      have hn := hNL t (hp x) i z hl
      have hne : (N t ∘ J i) z ≠ 0 := hpn x
      have heq : R ∘ J i =ᶠ[𝓝 z] (N t ∘ J i) / (D t ∘ J i) := by
        filter_upwards [(isOpen_Iio.preimage Complex.continuous_re).mem_nhds hl,
          hn.continuousAt.eventually_ne hne] with w hw hs using onLeft i w hw t (hp x) hs
      exact (meromorphicNFAt_congr heq).2 (MeromorphicNFOn.div hn (hD t i z hl).meromorphicNFAt (Or.inr hne))
  have hfe (i : I) (z : ℂ) (hz : z ∈ criticalStrip) (t : T) : N t (J i z) = R (J i z) * D t (J i z) := by
    let x := J i z
    rw [onRight i z hz.1 (q x) (hq x) (hqd x)]
    change N t x = N (q x) x / D (q x) x * D t x
    field_simp [hqd x]
    exact he i z hz t (q x)
  have hu : ∀ R', E R' → R' = R := by
    rintro R' ⟨hnf', hfe'⟩
    funext x
    obtain ⟨i, z, rfl⟩ := hcov x
    have heq := sLocal_meromorphic_identity (meromorphicOn_univ.mp (hnf' i).meromorphicOn)
      (meromorphicOn_univ.mp (hnf i).meromorphicOn) (fun w hw ↦
        mul_right_cancel₀ (hqd (J i w)) ((hfe' i w hw (q _)).symm.trans (hfe i w hw (q _))))
    exact ((hnf' i (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hnf i (mem_univ z)) |>.mp
      (heq.filter_mono (nhdsNE_le_codiscrete z))).eq_of_nhds
  exact ⟨⟨R, ⟨hnf, hfe⟩, hu⟩, fun R' hR ↦ hu R' hR ▸ hreg⟩

end FactorPatching

section LocalRegularity

variable {K : Type*} [NormedField K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "chart[" m "," hm "," χ "]" => quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- Absolute convergence for the real powers in an open interval gives
holomorphy of every unitary Mellin twist on the corresponding strip. -/
private theorem localZeta_analytic {μ : Measure Kˣ} (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m)
    (f : ℬ(K)) (χ : PontryaginDual Kˣ) {U : Set ℝ} (hU : IsOpen U)
    (hI : ∀ a ∈ U, Integrable (fun u : Kˣ ↦ ‖f (Multiplicative.ofAdd u.val)‖ *
      (((m u : ℝ≥0) : ℝ) ^ a)) μ) :
    AnalyticOnNhd ℂ (fun z ↦ localIdelicZetaIntegral μ test(f) (chart[m, hm, χ] z)) (Complex.re ⁻¹' U) := by
  let r (u : Kˣ) : ℝ := (m u : ℝ≥0)
  let t (u : Kˣ) := f (Multiplicative.ofAdd u.val) * (χ u : ℂ)
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp hm)
  have ht : Continuous t := ((schwartzBruhat_continuous f).comp
    (continuous_ofAdd.comp Units.continuous_val)).mul (continuous_subtype_val.comp χ.continuous)
  have he (z : ℂ) : localIdelicZetaIntegral μ test(f) (chart[m, hm, χ] z) =
      ∫ u, t u * (r u : ℂ) ^ z ∂μ := integral_congr_ae (.of_forall fun u ↦ (mul_assoc _ _ _).symm)
  simp_rw [he]
  apply analyticOnNhd_integral_mul_cpow μ _ _ ht.measurable hr.measurable
    (fun u ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) hU
  intro a ha
  simpa only [t, norm_mul, Circle.norm_coe, mul_one] using hI a ha

/-- Duality in a norm chart reflects the exponent in one. -/
private theorem dualQuasiCharacter_normTwist {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (m : G →* ℝ≥0ˣ) (hm : Continuous m) (χ : PontryaginDual G) (s : ℂ) :
    dualQuasiCharacter m hm (chart[m, hm, χ] s) = chart[m, hm, χ⁻¹] (1 - s) := by
  ext1 g
  have hp : 0 < ((m g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change modℂ[m, g] * (chart[m, hm, χ] s) g⁻¹ = ((χ⁻¹ g : Circle) : ℂ) * modℂ[m, g] ^ (1 - s)
  rw [map_inv]
  change _ * ((χ g : ℂ) * modℂ[m, g] ^ s)⁻¹ = (χ g : ℂ)⁻¹ * _
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hp.ne'), Complex.cpow_one, mul_inv_rev, div_eq_mul_inv]
  ring

/-- Tests supported near one can detect any continuous local quasi-character
with an integral over a compact subset of the units. -/
private theorem localZeta_exists_nonzero_compact [ProperSpace K]
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (c : QuasiCharacter Kˣ)
    (hb : ∀ U ∈ 𝓝 (1 : K), ∃ (g : ℬ(K)) (a : K → ℝ),
      (∀ x, g (Multiplicative.ofAdd x) = (a x : ℂ)) ∧
      (∀ x, 0 ≤ a x) ∧ a 1 = 1 ∧ Function.support a ⊆ U) :
    ∃ g : ℬ(K), HasCompactSupport (fun u : Kˣ ↦ g (Multiplicative.ofAdd u.val)) ∧
      localIdelicZetaIntegral μ test(g) c ≠ 0 := by
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  obtain ⟨C, hC, hK, hU⟩ := exists_mem_nhds_isCompact_mapsTo (continuous_id (X := Kˣ))
    ((Complex.continuous_re.comp c.continuous).continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show 0 < (c 1).re by simp)))
  have hC' : Units.val '' C ∈ 𝓝 (1 : K) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).image_mem_nhds.mpr hC
  obtain ⟨g, a, ha, hna, h1, hsub⟩ := hb _ hC'
  let t (u : Kˣ) := g (Multiplicative.ofAdd u.val)
  have htc : Continuous t := (schwartzBruhat_continuous g).comp (continuous_ofAdd.comp Units.continuous_val)
  have hmem (u : Kˣ) (h : a u.val ≠ 0) : u ∈ C :=
    Units.val_injective.mem_set_image.mp (hsub h)
  have ht : HasCompactSupport t := HasCompactSupport.intro hK fun u hu ↦
    (ha u.val).trans (by rw [not_ne_iff.mp (mt (hmem u) hu), Complex.ofReal_zero])
  refine ⟨g, ht, ?_⟩
  let G (u : Kˣ) := t u * c u
  have hG : Continuous G := htc.mul c.continuous
  have hI : Integrable G μ := hG.integrable_of_hasCompactSupport ht.mul_right
  have hpos (u : Kˣ) : 0 ≤ (G u).re := by
    change 0 ≤ (g (Multiplicative.ofAdd u.val) * c u).re
    rw [ha]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    by_cases h : a u.val = 0
    · simp [h]
    · exact mul_nonneg (hna _) (hU (hmem u h)).le
  have hG₁ : (G 1).re ≠ 0 := by simp [G, t, ha, h1]
  have hp := integral_pos_of_integrable_nonneg_ne_zero (Complex.continuous_re.comp hG) hI.re hpos hG₁
  intro hz
  exact hp.ne' ((integral_re hI).trans (congrArg Complex.re hz))

end LocalRegularity

section FourierModel

variable {K : Type*} [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))

/-- A perfect local multiplication pairing transports the Fourier isomorphism
on the dual back to the original field, for any normalization of additive Haar. -/
private theorem localFourier_model (ν : Measure K) [ν.IsAddHaarMeasure]
    (e : Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K))
    (ψ : K → Circle) (he : ∀ x y : K, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = ψ (x * y)) :
    ∃ T : ℬ(K) → ℬ(K), Surjective T ∧ ∀ f : ℬ(K),
      Integrable test(f) ν ∧ tamagawaFourier ν ψ test(f) = test(T f) := by
  let G := Multiplicative K
  let μ : Measure G := ν
  let : T2Space G := inferInstanceAs (T2Space K)
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace K)
  let : BorelSpace G := inferInstanceAs (BorelSpace K)
  let hμ := ‹ν.IsAddHaarMeasure›
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hμ.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hμ.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hμ.map_add_left_eq_self x.toAdd }
  let : μ.Regular := addHaar_regular_of_sigmaCompactSpace ν
  refine (schwartzBruhat_fourier_equiv μ).elim fun A hA ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e).elim fun P hP ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e.symm).elim fun Q hQ ↦ ?_
  have hsur : Surjective P := by
    intro g
    refine ⟨Q g, Subtype.ext (funext fun x ↦ ?_)⟩
    change P (Q g) x = g x
    exact (hP (Q g) x).trans ((hQ g (e x)).trans (congrArg g (e.symm_apply_apply x)))
  let T (f : ℬ(K)) : ℬ(K) := P (A f)
  refine ⟨T, hsur.comp A.surjective, ?_⟩
  intro f
  refine ⟨(hA f).1, funext fun x ↦ ?_⟩
  exact (tamagawaFourier_eq_lcaFourier ν ψ test(f) x _ (fun y ↦ (he x y).trans (congrArg ψ (mul_comm x y)))).trans
      (((hA f).2 _).symm.trans (hP (A f) _).symm)

end FourierModel

section ChartCover

variable {K : Type*} [NormedField K] [ProperSpace K]
local notation "chart[" m "," hm "," χ "]" => quasiCharacterNormTwist m hm ((circleToComplex).comp χ)

/-- Factor a quasi-character into its unitary part and the positive real
power determined by its abscissa. -/
private theorem localChart_cover (m : Kˣ →* ℝ≥0ˣ) (hm : IsProperMap m) (hn : ∃ u, m u ≠ 1)
    (c : QuasiCharacter Kˣ) : ∃ χ : PontryaginDual Kˣ, ∃ s : ℂ, chart[m, hm.continuous, χ] s = c := by
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let a := quasiCharacterAbscissa m hm hn c
  let d := quasiCharacterNormTwist m hm.continuous c (-(a : ℂ))
  have hnorm (u : Kˣ) : ‖d u‖ = 1 := by
    change ‖c u * modℂ[m, u] ^ (-(a : ℂ))‖ = 1
    have hp : 0 < ((m u : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa m hm hn c u, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [Complex.neg_re, Complex.ofReal_re, ← Real.rpow_add hp, a, add_neg_cancel, Real.rpow_zero]
  let χ : PontryaginDual Kˣ :=
    { toFun := fun u ↦ ⟨d u, mem_sphere_zero_iff_norm.mpr (hnorm u)⟩
      map_one' := Subtype.ext d.map_one
      map_mul' := fun u v ↦ Subtype.ext (d.map_mul u v)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), ContinuousMonoidHom.ext fun u ↦ ?_⟩
  change (c u * modℂ[m, u] ^ (-(a : ℂ))) * modℂ[m, u] ^ (a : ℂ) = c u
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m u).ne_zero)),
    neg_add_cancel, Complex.cpow_zero, mul_one]

end ChartCover

section LocalPairing

open scoped ENNReal

variable {K : Type*} [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]

/-- For a fixed dilation, the additive Fourier kernel is symmetric. Apply
Mathlib's bilinear Fourier pairing to the form (x,y) ↦ txy. -/
private theorem local_fourier_pair (ν : Measure K) [SigmaFinite ν]
    (ψ : Multiplicative K →ₜ* Circle) (f g : K → ℂ) (hf : Integrable f ν) (hg : Integrable g ν) (t : K) :
    (∫ x, f x * tamagawaFourier ν (ψ ∘ Multiplicative.ofAdd) g (x * t) ∂ν) =
      ∫ x, g x * tamagawaFourier ν (ψ ∘ Multiplicative.ofAdd) f (x * t) ∂ν := by
  let a : AddChar K Circle := AddChar.toMonoidHomEquiv.symm ψ.toMonoidHom
  let L := t • LinearMap.mul K K
  have hL : Continuous fun p : K × K ↦ L p.1 p.2 :=
    continuous_const.mul (continuous_fst.mul continuous_snd)
  have hflip : L.flip = L := LinearMap.ext₂ fun x y ↦ congrArg (t * ·) (mul_comm y x)
  have hid (h : K → ℂ) (y : K) : VectorFourier.fourierIntegral a ν L h y =
      tamagawaFourier ν (ψ ∘ Multiplicative.ofAdd) h (y * t) := by
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    change (a (-(t * (x * y))) : Circle) • h x = _
    rw [AddChar.map_neg_eq_inv]
    change ((a (t * (x * y)))⁻¹ : Circle) * h x = h x * star (ψ (Multiplicative.ofAdd (x * (y * t))) : ℂ)
    rw [Circle.coe_inv_eq_conj, mul_comm, show t * (x * y) = x * (y * t) by ring]
    rfl
  have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := L)
    (show Continuous a from ψ.continuous) hL hg hf
  rw [hflip] at he
  simpa only [hid, smul_eq_mul, mul_comm] using he

variable [MeasurableSpace Kˣ] [BorelSpace Kˣ]

/-- Multiplying the multiplicative measure by the local module recovers a
constant multiple of the additive measure. The omitted zero has measure zero. -/
private theorem local_integral_module (ν : Measure K) [NullSingletonClass ν] (μ : Measure Kˣ)
    (d : K → ℝ≥0) (hd : Measurable d) (hn : ∀ u : Kˣ, d u.val ≠ 0)
    (k : ℝ≥0∞) (hμ : μ = k • (ν.withDensity (fun x ↦ (d x : ℝ≥0∞)⁻¹)).comap Units.val)
    (f : K → ℂ) :
    (∫ u : Kˣ, f u.val * ((d u.val : ℝ) : ℂ) ∂μ) = k.toReal • ∫ x, f x ∂ν := by
  let v := (Units.val : Kˣ → K)
  let h := fun x : K ↦ f x * ((d x : ℝ) : ℂ)
  have he : MeasurableEmbedding v := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hv : range v = {0}ᶜ := by
    ext x
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  rw [hμ, integral_smul_measure]
  congr 1
  change (∫ u : Kˣ, h (v u) ∂_) = _
  rw [← he.integral_map, he.map_comap, hv, restrict_withDensity (measurableSet_singleton 0).compl,
    restrict_compl_singleton]
  have hfin : ∀ᵐ x ∂ν, (d x : ℝ≥0∞)⁻¹ < ⊤ := by
    filter_upwards [ν.ae_ne 0] with x hx using
      ENNReal.inv_lt_top.mpr (by exact_mod_cast (pos_iff_ne_zero.mpr (hn (Units.mk0 x hx)) : 0 < d x))
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x ↦ (d x : ℝ≥0∞)⁻¹) hd.coe_nnreal_ennreal.inv hfin]
  refine integral_congr_ae ?_
  filter_upwards [ν.ae_ne 0] with x hx
  have hn' : ((d x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (hn (Units.mk0 x hx)))
  simp only [h, ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul, Complex.ofReal_inv]
  field_simp [hn']

end LocalPairing

section TateCorrelation

variable {K : Type*} [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ]

omit [BorelSpace K] in
/-- The integral of the multiplicative correlation is the product of the two
zeta integrals. In the correlation the characters cancel to the local module,
turning its inner integral into an additive integral. -/
private theorem localZeta_correlation (ν : Measure K) (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (b : ℝ)
    (hμ : ∀ h : K → ℂ, (∫ u : Kˣ, h u.val * modℂ[m, u] ∂μ) = b • ∫ x, h x ∂ν)
    (c : QuasiCharacter Kˣ) (f g : K → ℂ)
    (hi : Integrable (fun u : Kˣ ↦ f u.val * c u) μ)
    (hj : Integrable (fun u : Kˣ ↦ g u.val * dualQuasiCharacter m hm c u) μ) :
    localIdelicZetaIntegral μ f c * localIdelicZetaIntegral μ g (dualQuasiCharacter m hm c) =
      ∫ t : Kˣ, (b • ∫ x, f x * g (x * t.val) ∂ν) * dualQuasiCharacter m hm c t ∂μ := by
  let d := dualQuasiCharacter m hm c
  let A (u : Kˣ) := f u.val * c u
  let B (u : Kˣ) := g u.val * d u
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : μ.Regular := inferInstance
  have hc (u : Kˣ) : c u * d u = modℂ[m, u] := by
    change c u * (modℂ[m, u] * c u⁻¹) = _
    rw [map_inv, mul_left_comm, mul_inv_cancel₀ ((Group.isUnit u).map c).ne_zero, mul_one]
  have hconv := integral_lcaConvolution μ (f := fun u ↦ A u⁻¹) (g := B) hi.comp_inv hj
  rw [integral_inv_eq_self] at hconv
  refine hconv.symm.trans (integral_congr_ae (.of_forall fun t ↦ ?_))
  change (∫ u : Kˣ, A u⁻¹ * B (u⁻¹ * t) ∂μ) = _
  rw [integral_inv_eq_self (fun u ↦ A u * B (u * t)) μ]
  change _ = (b • ∫ x, f x * g (x * t.val) ∂ν) * d t
  rw [← hμ (fun x ↦ f x * g (x * t.val)), ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun u ↦ ?_)
  change (f u.val * c u) * (g (u.val * t.val) * d (u * t)) = (f u.val * g (u.val * t.val) * modℂ[m, u]) * d t
  rw [map_mul, ← hc]
  ring

end TateCorrelation

section LocalExistence

variable {K : Type*} [NormedField K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace Kˣ] [BorelSpace Kˣ]
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "chart[" m "," hm "," χ "]" => quasiCharacterNormTwist m hm ((circleToComplex).comp χ)
local notation "leftHalf" => (Complex.re ⁻¹' Iio (1 : ℝ))

omit [ProperSpace K] [MeasurableSpace K] [BorelSpace K] in
/-- Compact support inside the unit group gives absolute convergence for
every real exponent, including negative exponents. -/
private theorem localWeight_compact (m : Kˣ →* ℝ≥0ˣ) (hm : Continuous m) (μ : Measure Kˣ)
    [IsFiniteMeasureOnCompacts μ] (g : ℬ(K))
    (hcg : HasCompactSupport (fun u : Kˣ ↦ g (Multiplicative.ofAdd u.val))) (a : ℝ) :
    Integrable (fun u : Kˣ ↦ ‖g (Multiplicative.ofAdd u.val)‖ * ((m u : ℝ≥0) : ℝ) ^ a) μ := by
  have h₁ : Continuous fun u : Kˣ ↦ ‖g (Multiplicative.ofAdd u.val)‖ :=
    ((schwartzBruhat_continuous g).comp (continuous_ofAdd.comp Units.continuous_val)).norm
  have h₂ : Continuous fun u : Kˣ ↦ ((m u : ℝ≥0) : ℝ) ^ a :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hm)).rpow_const
      (fun u ↦ Or.inl (NNReal.coe_ne_zero.mpr (m u).ne_zero))
  exact (h₁.mul h₂).integrable_of_hasCompactSupport hcg.norm.mul_right

/-- Tate's symmetric pairing determines the factor on the strip. Tests
supported in the unit group and inverse transforms of such tests continue
it to the two half-planes, with uniqueness on every unitary chart. -/
private theorem localTate_existsUnique (m : Kˣ →* ℝ≥0ˣ) (hm : IsProperMap m) (hn : ∃ u, m u ≠ 1)
    (μ : Measure Kˣ) [μ.IsHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure]
    (b : ℝ) (hμ : ∀ h : K → ℂ, (∫ u : Kˣ, h u.val * modℂ[m, u] ∂μ) = b • ∫ x, h x ∂ν)
    (ψ : K → Circle) (e : Multiplicative K ≃ₜ* PontryaginDual (Multiplicative K))
    (he : ∀ x y : K, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = ψ (x * y))
    (hi : ∀ (f : ℬ(K)) (a : ℝ), 0 < a →
      Integrable (fun u : Kˣ ↦ ‖f (Multiplicative.ofAdd u.val)‖ * ((m u : ℝ≥0) : ℝ) ^ a) μ)
    (hb : ∀ U ∈ 𝓝 (1 : K), ∃ (g : ℬ(K)) (a : K → ℝ),
      (∀ x, g (Multiplicative.ofAdd x) = (a x : ℂ)) ∧
      (∀ x, 0 ≤ a x) ∧ a 1 = 1 ∧ Function.support a ⊆ U) :
    let E := IsLocalTateFactor m hm.continuous μ (tamagawaFourier ν ψ)
    (∃! ρ, E ρ) ∧ ∀ ρ, E ρ → ∀ χ, AnalyticOnNhd ℂ (fun z ↦ ρ (chart[m, hm.continuous, χ] z)) rightHalf := by
  intro spec
  let J (χ : PontryaginDual Kˣ) (z : ℂ) := chart[m, hm.continuous, χ] z
  let d := dualQuasiCharacter m hm.continuous
  refine (localFourier_model ν e ψ he).elim fun T hT ↦ ?_
  have hF (f : ℬ(K)) : tamagawaFourier ν ψ test(f) = test(T f) := (hT.2 f).2
  let N (f : ℬ(K)) (c : QuasiCharacter Kˣ) := localIdelicZetaIntegral μ test(f) c
  let D (f : ℬ(K)) (c : QuasiCharacter Kˣ) := N (T f) (d c)
  let P (f : ℬ(K)) := HasCompactSupport (fun u : Kˣ ↦ f (Multiplicative.ofAdd u.val))
  have hN (f : ℬ(K)) (χ : PontryaginDual Kˣ) : AnalyticOnNhd ℂ (N f ∘ J χ) rightHalf :=
    localZeta_analytic m hm.continuous f χ isOpen_Ioi (hi f)
  have hE (f : ℬ(K)) (hf : P f) (χ : PontryaginDual Kˣ) :
      AnalyticOnNhd ℂ (N f ∘ J χ) (Complex.re ⁻¹' (univ : Set ℝ)) :=
    localZeta_analytic m hm.continuous f χ isOpen_univ (fun a _ ↦ localWeight_compact m hm.continuous μ f hf a)
  have hD (f : ℬ(K)) (χ : PontryaginDual Kˣ) (z : ℂ) : D f (J χ z) = N (T f) (J χ⁻¹ (1 - z)) :=
    congrArg (N (T f)) (dualQuasiCharacter_normTwist m hm.continuous χ z)
  have hiJ (f : ℬ(K)) (χ : PontryaginDual Kˣ) (z : ℂ) (hz : z ∈ rightHalf) :
      Integrable (fun u : Kˣ ↦ f (Multiplicative.ofAdd u.val) * J χ z u) μ := by
    have hc := ((schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)).mul
      (J χ z).continuous
    refine (hi f z.re hz).mono' hc.aestronglyMeasurable (.of_forall fun u ↦ ?_)
    change ‖f (Multiplicative.ofAdd u.val) * ((χ u : ℂ) * modℂ[m, u] ^ z)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hstrip (χ : PontryaginDual Kˣ) (z : ℂ) (hz : z ∈ criticalStrip) (f g : ℬ(K)) :
      N f (J χ z) * D g (J χ z) = N g (J χ z) * D f (J χ z) := by
    have hdual := dualQuasiCharacter_normTwist m hm.continuous χ z
    have hz' : 1 - z ∈ rightHalf := by
      change 0 < (1 - z).re
      simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hz.2
    have hcorr (f g : ℬ(K)) := localZeta_correlation ν μ m hm.continuous b hμ (J χ z)
      test(f) test(T g) (hiJ f χ z hz.1) (hdual ▸ hiJ (T g) χ⁻¹ (1 - z) hz')
    refine (hcorr f g).trans ((integral_congr_ae (.of_forall fun t ↦ ?_)).trans (hcorr g f).symm)
    congr 2
    let a := e (Multiplicative.ofAdd (1 : K))
    have hψ : a ∘ Multiplicative.ofAdd = ψ := funext fun x ↦ (he 1 x).trans (congrArg ψ (one_mul x))
    have h := local_fourier_pair ν a test(f) test(g) (hT.2 f).1 (hT.2 g).1 t.val
    have heq (g : ℬ(K)) (y : K) :
        tamagawaFourier ν (a ∘ Multiplicative.ofAdd) test(g) y = T g (Multiplicative.ofAdd y) :=
      (congrArg (fun φ ↦ tamagawaFourier ν φ test(g) y) hψ).trans (congrFun (hF g) y)
    have hI (f g : ℬ(K)) :
        (∫ x : K, f (Multiplicative.ofAdd x) * tamagawaFourier ν (a ∘ Multiplicative.ofAdd)
          test(g) (x * t.val) ∂ν) = ∫ x : K, f (Multiplicative.ofAdd x) * T g (Multiplicative.ofAdd (x * t.val)) ∂ν :=
      integral_congr_ae (.of_forall fun x ↦ congrArg (f (Multiplicative.ofAdd x) * ·) (heq g (x * t.val)))
    exact (hI f g).symm.trans (h.trans (hI g f))
  let E (R : QuasiCharacter Kˣ → ℂ) := (∀ χ, MeromorphicNFOn (R ∘ J χ) univ) ∧
    ∀ χ z, z ∈ criticalStrip → ∀ f, N f (J χ z) = R (J χ z) * D f (J χ z)
  have hR : (∃! R, E R) ∧ ∀ R, E R → ∀ χ, AnalyticOnNhd ℂ (R ∘ J χ) rightHalf := by
    refine localFactor_patch J (quasiCharacterAbscissa m hm hn)
      (fun χ z ↦ quasiCharacterAbscissa_of_unitary_twist m hm hn _ χ z (fun _ ↦ rfl))
      (localChart_cover m hm hn) N D P (P ∘ T) (fun c ↦ localZeta_exists_nonzero_compact μ c hb) ?_
      hN ?_ (fun f hf χ z _ ↦ hE f hf χ z (mem_univ _)) ?_ hstrip
    · intro c
      obtain ⟨g, hg, hn⟩ := localZeta_exists_nonzero_compact μ (d c) hb
      obtain ⟨f, rfl⟩ := hT.1 g
      exact ⟨f, hg, hn⟩
    · intro f χ
      change AnalyticOnNhd ℂ (fun z ↦ D f (J χ z)) leftHalf
      simp_rw [hD]
      intro z hz
      exact (hN (T f) χ⁻¹ _ (show 0 < (1 - z).re by simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hz)).comp
        (analyticAt_const.sub analyticAt_id)
    · intro f hf χ
      change AnalyticOnNhd ℂ (fun z ↦ D f (J χ z)) rightHalf
      simp_rw [hD]
      exact fun z _ ↦ (hE (T f) hf χ⁻¹ _ (mem_univ _)).comp (analyticAt_const.sub analyticAt_id)
  have iff_spec (R : QuasiCharacter Kˣ → ℂ) : E R ↔ IsLocalTateFactor m hm.continuous μ (tamagawaFourier ν ψ) R := by
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, fun f χ z hz ↦ by simpa only [hF] using h' χ z hz f⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun χ z hz f ↦ by simpa only [hF] using h' f χ z hz⟩
  obtain ⟨⟨R, h, hu⟩, hr⟩ := hR
  exact ⟨⟨R, (iff_spec R).mp h, fun R' hR' ↦ hu R' ((iff_spec R').mpr hR')⟩,
    fun R' hR' ↦ hr R' ((iff_spec R').mpr hR')⟩

end LocalExistence

section LocalApplications

open scoped ENNReal

/-- A positive power of the norm is nontrivial and changes additive measure
to multiplicative measure by the prescribed density. -/
private theorem localTate_normData {K : Type*} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableSpace Kˣ] [BorelSpace Kˣ]
    (ν : Measure K) [ν.IsAddHaarMeasure] (μ : Measure Kˣ) (k : ℝ≥0∞) (n : ℕ) (hn : n ≠ 0)
    (hμ : μ = k • (ν.withDensity (fun x ↦ (↑(‖x‖₊ ^ n) : ℝ≥0∞)⁻¹)).comap Units.val) :
    let m : Kˣ →* ℝ≥0ˣ := (Units.map nnNormHom.toMonoidHom) ^ n
    (∃ u, m u ≠ 1) ∧ ∀ f : K → ℂ, (∫ u : Kˣ, f u.val * modℂ[m, u] ∂μ) = k.toReal • ∫ x, f x ∂ν := by
  intro m
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_nnNorm K
  let u := Units.mk0 x (nnNorm_ne_zero_iff.mp (zero_lt_one.trans hx).ne')
  refine ⟨⟨u, fun h ↦ (one_lt_pow₀ hx hn).ne' (congrArg (Units.val : ℝ≥0ˣ → ℝ≥0) h)⟩, ?_⟩
  exact local_integral_module ν μ (fun x ↦ ‖x‖₊ ^ n) (continuous_nnNorm.pow _).measurable
    (fun u ↦ pow_ne_zero _ (nnNorm_ne_zero_iff.mpr u.ne_zero)) k hμ

end LocalApplications

omit [NumberField F] in
/-- Real and complex completions admit isometric additive Euclidean coordinates. -/
private theorem infiniteLocal_euclidean (w : InfinitePlace F) :
    ∃ n, ∃ e : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n)),
      Isometry (fun x : w.Completion ↦ (e (Multiplicative.ofAdd x)).toAdd) := by
  have h {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (a : w.Completion ≃+ V) (ha : Isometry a) :
      ∃ n, ∃ e : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n)),
        Isometry (fun x : w.Completion ↦ (e (Multiplicative.ofAdd x)).toAdd) := by
    let b := (stdOrthonormalBasis ℝ V).repr
    let t := a.trans b.toLinearEquiv.toAddEquiv
    have ht : Isometry t := b.isometry.comp ha
    let E : w.Completion ≃ᵢ EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := ⟨t.toEquiv, ht⟩
    let e : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
      { toMulEquiv := t.toMultiplicative
        continuous_toFun := ht.continuous
        continuous_invFun := E.symm.continuous }
    exact ⟨_, e, ht⟩
  by_cases hw : w.IsReal
  · exact h (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toAddEquiv
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).isometry
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    exact h (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).toAddEquiv
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).isometry

omit [NumberField F] in
/-- Local smooth bumps in Euclidean coordinates provide real Schwartz tests. -/
private theorem infiniteLocal_smallTest (w : InfinitePlace F) (U : Set w.Completion) (hU : U ∈ 𝓝 1) :
    ∃ (g : ℬ(w.Completion)) (a : w.Completion → ℝ), (∀ x, g (Multiplicative.ofAdd x) = (a x : ℂ)) ∧
      (∀ x, 0 ≤ a x) ∧ a 1 = 1 ∧ Function.support a ⊆ U := by
  obtain ⟨n, e, _⟩ := infiniteLocal_euclidean w
  let V := EuclideanSpace ℝ (Fin n)
  let E : w.Completion ≃ₜ V := e.toHomeomorph
  obtain ⟨a, hs, hc, hd, hn, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (E.symm.continuous.continuousAt.preimage_mem_nhds (show U ∈ 𝓝 (E.symm (E 1)) by simpa using hU))
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) := inferInstanceAs (LocallyCompactSpace w.Completion)
  let g (x : Multiplicative w.Completion) : ℂ := a (E x.toAdd)
  have hg : g ∈ schwartzBruhatSubmodule (Multiplicative w.Completion) :=
    (mem_schwartzBruhatSubmodule_euclidean_iff e g).2
      ⟨(hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd), fun _ ↦ rfl⟩
  refine ⟨⟨g, hg⟩, fun x ↦ a (E x), fun _ ↦ rfl, fun _ ↦ (hn (mem_range_self _)).1, h1, ?_⟩
  intro x hx
  have h := hs (subset_tsupport a hx)
  change E.symm (E x) ∈ U at h
  simpa using h

/-- The Euclidean Schwartz seminorms dominate the local Mellin weight at infinity. -/
private theorem infiniteLocal_weight_integrable (w : InfinitePlace F) (f : ℬ(w.Completion))
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : w.Completionˣ ↦ ‖f (Multiplicative.ofAdd u.val)‖ *
      ((infiniteNorm(w) u : ℝ≥0) : ℝ) ^ a) (infiniteLocalMultiplicativeTamagawaMeasure F w) := by
  obtain ⟨n, e, he⟩ := infiniteLocal_euclidean w
  let : T2Space (Multiplicative w.Completion) := inferInstanceAs (T2Space w.Completion)
  let : LocallyCompactSpace (Multiplicative w.Completion) := inferInstanceAs (LocallyCompactSpace w.Completion)
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  obtain ⟨g, hg⟩ := (mem_schwartzBruhatSubmodule_euclidean_iff e _).1 f.property
  obtain ⟨k, hk⟩ := exists_nat_gt (w.mult * a)
  let B := max (SchwartzMap.seminorm ℝ 0 0 g) (SchwartzMap.seminorm ℝ k 0 g)
  have hB (x : w.Completion) : ‖f (Multiplicative.ofAdd x)‖ * (max 1 ‖x‖) ^ k ≤ B := by
    rw [← hg]
    rcases le_total ‖x‖ 1 with h | h
    · rw [max_eq_left h, one_pow, mul_one]
      exact (g.norm_le_seminorm ℝ _).trans (le_max_left _ _)
    · rw [max_eq_right h, mul_comm]
      have hn : ‖(e (Multiplicative.ofAdd x)).toAdd‖ = ‖x‖ :=
        he.norm_map_of_map_zero (e.map_one) x
      rw [← hn]
      exact (g.norm_pow_mul_le_seminorm ℝ k _).trans (le_max_right _ _)
  have hI := (infiniteLocalTamagawa_integrable_norm_rpow w ha k hk).2
  refine (hI.const_mul B).mono' ?_ (.of_forall fun u ↦ ?_)
  · have h₁ := ((schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)).norm
    have h₂ := (NNReal.continuous_coe.comp (Units.continuous_val.comp (continuous_infiniteLocalModule w))).rpow_const
      (fun u ↦ Or.inl (NNReal.coe_ne_zero.mpr (infiniteNorm(w) u).ne_zero)) (p := a)
    exact (h₁.mul h₂).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))]
    have hn : ((infiniteNorm(w) u : ℝ≥0) : ℝ) = ‖u.val‖ ^ w.mult := by
      simp [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
    rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← mul_div_assoc]
    rw [le_div_iff₀ (by positivity), mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (by positivity)

open scoped Classical in
/-- The restriction of the global perfect pairing to an archimedean
summand is nontrivial, hence perfect over the completion field. -/
private theorem infiniteLocal_pair (w : InfinitePlace F) :
    ∃ e : Multiplicative w.Completion ≃ₜ* PontryaginDual (Multiplicative w.Completion),
      ∀ x y : w.Completion, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) =
        adeleStandardCharacter F (Pi.single w (x * y), 0) := by
  classical
  let a := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion := LipschitzWith.properSpace a.isClosedEmbedding.isProperMap a.lipschitzWith
  let j : w.Completion →+ 𝔸[F] :=
    (AddMonoidHom.inl _ _).comp (AddMonoidHom.single _ w)
  have hj : Continuous j := (continuous_single w).prodMk continuous_const
  obtain ⟨ψ, hψ⟩ := exists_adeleCharacterHom F
  let d := ψ.comp (⟨j.toMultiplicative, hj⟩ : Multiplicative w.Completion →ₜ* Multiplicative 𝔸[F])
  have hd (x : w.Completion) : d (Multiplicative.ofAdd x) = adeleStandardCharacter F (j x) := hψ _
  obtain ⟨E, hE, -⟩ := additiveTamagawaMeasure_selfDual F
  have hmul (y : 𝔸[F]) : j 1 * y = j (y.1 w) := by
    refine Prod.ext (funext fun v ↦ ?_) (zero_mul _)
    change Pi.single w (1 : w.Completion) v * y.1 v = Pi.single w (y.1 w) v
    by_cases hv : v = w
    · subst v; simp
    · simp [Pi.single_eq_of_ne hv]
  have hnt : ∃ x, d (Multiplicative.ofAdd x) ≠ 1 := by
    by_contra! h
    have he : E (Multiplicative.ofAdd (j 1)) = 1 := PontryaginDual.ext fun y ↦
      (hE (j 1) y.toAdd).trans ((congrArg _ (hmul y.toAdd)).trans ((hd _).symm.trans (h _)))
    have hz : j 1 = 0 := E.injective (he.trans E.map_one.symm)
    have := congrArg (fun y : 𝔸[F] ↦ y.1 w) hz
    change Pi.single w (1 : w.Completion) w = 0 at this
    exact one_ne_zero ((Pi.single_eq_same _ _).symm.trans this)
  exact (exists_pontryaginDualEquiv_of_normedField d hnt).elim fun e he ↦
    ⟨e, fun x y ↦ (he x y).trans (hd _)⟩

/-- Paper: Equation (3.3.1.3), p. 129. The local Tate factor exists uniquely
and is holomorphic at positive abscissa, as in Proposition 3.3.1.5(3), p. 132. -/
private theorem infiniteLocalTateFactor_properties (w : InfinitePlace F) :
    let E := IsLocalTateFactor (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) (infiniteFourier(w))
    (∃! ρ, E ρ) ∧ ∀ ρ, E ρ → ∀ χ : PontryaginDual w.Completionˣ,
      AnalyticOnNhd ℂ (fun z ↦ ρ (quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
        ((circleToComplex).comp χ) z)) rightHalf := by
  dsimp only
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion := LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  let : NontriviallyNormedField w.Completion := ⟨⟨2, by
    rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num⟩⟩
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let := infiniteLocalAdditiveTamagawaMeasure_haar F w
  let := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  obtain ⟨hn, hμ⟩ := localTate_normData (infiniteLocalAdditiveTamagawaMeasure F w)
    (infiniteLocalMultiplicativeTamagawaMeasure F w) 1 w.mult w.mult_ne_zero (by rw [one_smul]; rfl)
  refine (infiniteLocal_pair w).elim fun e he ↦ ?_
  exact localTate_existsUnique _ (isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero) hn _ _ _ hμ _ e he
    (infiniteLocal_weight_integrable w) (infiniteLocal_smallTest w)

/-- Paper: Equation (3.3.1.3), p. 129. Tate's local equation characterizes
a unique archimedean factor in normal form. -/
theorem infiniteLocalTateFactor_existsUnique (w : InfinitePlace F) :
    ∃! ρ, IsLocalTateFactor (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) (infiniteFourier(w)) ρ := by
  exact (infiniteLocalTateFactor_properties w).1

/-- Paper: Definition A.3.2.2(2), p. 560. The finite local multiplicative Tamagawa
measure is a Haar measure on the local unit group. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (v : Primes) :
    (finiteLocalMultiplicativeTamagawaMeasure F v).IsHaarMeasure := by
  let : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : LocallyCompactSpace (v.adicCompletion F)ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  let U : Set (v.adicCompletion F)ˣ := (v.adicCompletionIntegers F).units
  have hO : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hK : IsCompact U := by
    have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  have hmass := hO.measure_pos μ ⟨1, (v.adicCompletionIntegers F).units.one_mem⟩
  have hnorm : 0 < (v.asIdeal.absNorm : ℝ) :=
    Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hsqrt := Real.sqrt_pos_of_pos (pow_pos hnorm
    (multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))))
  unfold finiteLocalMultiplicativeTamagawaMeasure
  exact Measure.IsHaarMeasure.smul μ
    (ENNReal.div_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      hK.measure_ne_top (μ := μ)⟩)
    (ENNReal.div_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hsqrt).ne') hmass.ne')

/-- At a finite place, a compact open ball about one is a Schwartz test. -/
private theorem finiteLocal_smallTest (v : Primes) (U : Set (v.adicCompletion F)) (hU : U ∈ 𝓝 1) :
    ∃ (g : ℬ(v.adicCompletion F)) (a : v.adicCompletion F → ℝ),
      (∀ x, g (Multiplicative.ofAdd x) = (a x : ℂ)) ∧
      (∀ x, 0 ≤ a x) ∧ a 1 = 1 ∧ Function.support a ⊆ U := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  let B := Metric.closedBall (1 : v.adicCompletion F) (ε / 2)
  have hB : IsClopen B := IsUltrametricDist.isClopen_closedBall _ (half_pos hε).ne'
  let b := B.indicator (1 : v.adicCompletion F → ℂ)
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v b).2
    ⟨(LocallyConstant.charFn ℂ hB).isLocallyConstant, HasCompactSupport.intro
      (isCompact_closedBall _ _) (fun _ hx ↦ indicator_of_notMem hx _)⟩
  refine ⟨g, B.indicator (fun _ ↦ 1), fun x ↦ (hg x).trans ?_, fun _ ↦ indicator_nonneg (by simp) _,
    indicator_of_mem (Metric.mem_closedBall_self (half_pos hε).le) _, ?_⟩
  · by_cases hx : x ∈ B <;> simp [b, hx]
  · intro x hx
    exact hsub ((mem_of_indicator_ne_zero hx).trans_lt (half_lt_self hε))

/-- The finite-place Schwartz test has compact support and is bounded there. -/
private theorem finiteLocal_weight_integrable (v : Primes) (f : ℬ(v.adicCompletion F))
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : (v.adicCompletion F)ˣ ↦ ‖f (Multiplicative.ofAdd u.val)‖ *
      ((finiteNorm(v) u : ℝ≥0) : ℝ) ^ a) (finiteLocalMultiplicativeTamagawaMeasure F v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let t (x : v.adicCompletion F) := f (Multiplicative.ofAdd x)
  have hc := ((mem_finitePlaceSchwartz_iff F v t).1 ⟨f, fun _ ↦ rfl⟩).2
  have ht : Continuous t := (schwartzBruhat_continuous f).comp continuous_ofAdd
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn continuous_norm.continuousOn
  obtain ⟨B, hB⟩ := ht.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hI := (finiteLocalTamagawa_integrable_norm_rpow v ha R).2
  refine (hI.const_mul (max B 0)).mono' ?_ (.of_forall fun u ↦ ?_)
  · have hpow := (continuous_norm.comp (Units.continuous_val (M := v.adicCompletion F))).rpow_const
      (fun u ↦ Or.inl (norm_ne_zero_iff.mpr u.ne_zero)) (p := a)
    exact ((ht.norm.comp Units.continuous_val).mul hpow).aestronglyMeasurable
  · change ‖‖t u.val‖ * ‖u.val‖ ^ a‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases h : t u.val = 0
    · rw [h, norm_zero, zero_mul]
      exact mul_nonneg (le_max_right _ _) (indicator_nonneg (fun _ _ ↦ by positivity) _)
    · rw [indicator_of_mem (show ‖u.val‖ ≤ R by simpa using hR _ (subset_tsupport _ h))]
      exact mul_le_mul_of_nonneg_right ((hB (mem_range_self _)).trans (le_max_left _ _)) (by positivity)

open scoped WithZero in
/-- Paper: Equation (3.3.1.3), p. 129. The local Tate factor exists uniquely
and is holomorphic at positive abscissa, as in Proposition 3.3.1.5(3), p. 132. -/
private theorem finiteLocalTateFactor_properties (v : Primes) :
    let E := IsLocalTateFactor (finiteNorm(v)) (continuous_finiteLocalModule v)
      (finiteLocalMultiplicativeTamagawaMeasure F v) (finiteFourier(v))
    (∃! ρ, E ρ) ∧ ∀ ρ, E ρ → ∀ χ : PontryaginDual (v.adicCompletion F)ˣ,
      AnalyticOnNhd ℂ (fun z ↦ ρ (quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v)
        ((circleToComplex).comp χ) z)) rightHalf := by
  dsimp only
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let val : Valuation K ℤᵐ⁰ := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  let : NontriviallyNormedField K := ⟨⟨π.val⁻¹, by
    rw [norm_inv, norm_uniformizer_adicCompletion v _ hπ, inv_inv]
    exact hq⟩⟩
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  obtain ⟨hn, hμ⟩ := localTate_normData (finiteLocalAdditiveTamagawaMeasure F v)
    (finiteLocalMultiplicativeTamagawaMeasure F v) (v.asIdeal.absNorm / (v.asIdeal.absNorm - 1)) 1 one_ne_zero
    (by simpa only [pow_one] using finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity F v)
  have hp := isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero
  simp only [pow_one] at hn hμ hp
  refine (finiteLocalAdditiveTamagawaMeasure_selfDual F v).elim fun e he ↦ ?_
  exact localTate_existsUnique _ hp hn _ _ _ hμ _ e he.1 (finiteLocal_weight_integrable v) (finiteLocal_smallTest v)

/-- Paper: Equation (3.3.1.3), p. 129. Tate's local equation characterizes
a unique finite-place factor in normal form. -/
theorem finiteLocalTateFactor_existsUnique (v : Primes) :
    ∃! ρ, IsLocalTateFactor (finiteNorm(v)) (continuous_finiteLocalModule v)
      (finiteLocalMultiplicativeTamagawaMeasure F v) (finiteFourier(v)) ρ := by
  exact (finiteLocalTateFactor_properties v).1

/-- Paper: Equation (3.3.1.3), p. 129. The archimedean Tate factor uses the
standard local Fourier transform.
Deviation: The local functional equation fixes the Fourier sign convention. -/
def infiniteLocalTateFactor (w : InfinitePlace F) : QuasiCharacter w.Completionˣ → ℂ :=
  (infiniteLocalTateFactor_existsUnique w).exists.choose

/-- Paper: Equation (3.3.1.3), p. 129. The finite Tate factor uses the
standard local Fourier transform.
Deviation: The local functional equation fixes the Haar and Fourier conventions. -/
def finiteLocalTateFactor (v : Primes) : QuasiCharacter (v.adicCompletion F)ˣ → ℂ :=
  (finiteLocalTateFactor_existsUnique v).exists.choose

/-- Paper: Equation (3.3.2.11), p. 139. The archimedean factor satisfies
Tate's equation for the specified Fourier transform. -/
theorem infiniteLocalTateFactor_spec (w : InfinitePlace F) :
    IsLocalTateFactor (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      (infiniteLocalMultiplicativeTamagawaMeasure F w) (infiniteFourier(w))
      (infiniteLocalTateFactor w) :=
  (infiniteLocalTateFactor_existsUnique w).exists.choose_spec

/-- Paper: Equation (3.3.2.11), p. 139. The finite-place factor satisfies
Tate's equation for the specified Fourier transform. -/
theorem finiteLocalTateFactor_spec (v : Primes) :
    IsLocalTateFactor (finiteNorm(v)) (continuous_finiteLocalModule v)
      (finiteLocalMultiplicativeTamagawaMeasure F v) (finiteFourier(v))
      (finiteLocalTateFactor v) :=
  (finiteLocalTateFactor_existsUnique v).exists.choose_spec

local notation "eProd" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "eArch" => ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
local notation "eFin" => ContinuousMulEquiv.piUnits (M := fun v : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "archAt(" w ")" => fun x ↦
  classOf ((eProd).symm ((eArch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1))
local notation "finAt(" v ")" => fun x ↦
  classOf ((eProd).symm (1, (eFin).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at an archimedean
place and taking its class is continuous and multiplicative. -/
theorem sLocalInfiniteInsertion_properties (w : InfinitePlace F) :
    let i : w.Completionˣ → Jₛ := archAt(w)
    i 1 = 1 ∧ (∀ x y, i (x * y) = i x * i y) ∧ Continuous i := by
  classical
  let A (v : InfinitePlace F) := v.Completionˣ
  let q : Iₛ →* Jₛ := QuotientGroup.mk' _
  let i := (q.comp (eProd).symm.toMonoidHom).comp
    ((MonoidHom.inl _ _).comp ((eArch).symm.toMonoidHom.comp (MonoidHom.mulSingle A w)))
  refine ⟨i.map_one, i.map_mul, ?_⟩
  exact QuotientGroup.continuous_mk.comp ((eProd).symm.continuous.comp
    (((eArch).symm.continuous.comp (continuous_mulSingle (A := A) w)).prodMk continuous_const))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at an archimedean
place restricts an S-local quasi-character to that place. -/
def sLocalInfiniteRestriction (w : InfinitePlace F) (c : Xₛ) : QuasiCharacter w.Completionˣ :=
  let h := sLocalInfiniteInsertion_properties (S := S) w
  c.comp ⟨{ toFun := archAt(w), map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a unit at a finite
place and taking its class is continuous and multiplicative. -/
theorem sLocalFiniteInsertion_properties (v : S) :
    let i : (v.val.adicCompletion F)ˣ → Jₛ := finAt(v)
    i 1 = 1 ∧ (∀ x y, i (x * y) = i x * i y) ∧ Continuous i := by
  classical
  let : DecidableEq S := Classical.decEq _
  let B (w : S) := (w.val.adicCompletion F)ˣ
  let q : Iₛ →* Jₛ := QuotientGroup.mk' _
  let i := (q.comp (eProd).symm.toMonoidHom).comp
    ((MonoidHom.inr _ _).comp ((eFin).symm.toMonoidHom.comp (MonoidHom.mulSingle B v)))
  refine ⟨i.map_one, i.map_mul, ?_⟩
  exact QuotientGroup.continuous_mk.comp ((eProd).symm.continuous.comp
    (continuous_const.prodMk ((eFin).symm.continuous.comp (continuous_mulSingle (A := B) v))))

/-- Paper: Equation (3.3.1.3), p. 129. Inserting a local unit at a finite
place restricts an S-local quasi-character to that place. -/
def sLocalFiniteRestriction (v : S) (c : Xₛ) : QuasiCharacter (v.val.adicCompletion F)ˣ :=
  let h := sLocalFiniteInsertion_properties v
  c.comp ⟨{ toFun := finAt(v), map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of a norm twist of the trivial
S-local character to an archimedean place is the same power of the normalized local module. -/
theorem sLocalInfiniteRestriction_normTwist (w : InfinitePlace F) (s : ℂ) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ((1 : PontryaginDual Jₛ)) s) g =
      (modℂ[infiniteNorm(w), g]) ^ s := by
  change (((1 : PontryaginDual Jₛ) (archAt(w) g) : Circle) : ℂ) *
    (modℂ[mₛ, archAt(w) g]) ^ s = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, sIdeleQuotientNorm_mk]
  congr 2
  let x : Iₛ := (eProd).symm ((eArch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w g), 1)
  let ev : (Iₛ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval x))
  change ev (sIdeleNorm F S) = _
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  change (∏ w' : InfinitePlace F,
      ‖(((@Pi.mulSingle (InfinitePlace F) (fun u ↦ u.Completionˣ) _ (Classical.decEq _) w g) w' :
        w'.Completionˣ) : w'.Completion)‖ ^
        w'.mult) * ∏ v : S, ‖((1 : (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F)‖ = _
  classical
  rw [Finset.prod_eq_single w (fun w' _ hw' ↦ by rw [Pi.mulSingle_eq_of_ne hw', Units.val_one,
      norm_one, one_pow]) (fun h ↦ absurd (Finset.mem_univ w) h), Pi.mulSingle_eq_same]
  simp

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of the S-idelic norm character
to an archimedean place is the normalized local module. -/
theorem sLocalInfiniteRestriction_norm (w : InfinitePlace F) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ((1 : PontryaginDual Jₛ)) 1) g =
      modℂ[infiniteNorm(w), g] := by
  rw [sLocalInfiniteRestriction_normTwist, Complex.cpow_one]

/-- Paper: Equation (3.3.1.3), p. 129. Restriction of the S-idelic norm character
to a finite place is the normalized local module. -/
theorem sLocalFiniteRestriction_norm (v : S) (g : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (chartₛ((1 : PontryaginDual Jₛ)) 1) g =
      modℂ[finiteNorm(v.val), g] := by
  change (((1 : PontryaginDual Jₛ) (finAt(v) g) : Circle) : ℂ) *
    (modℂ[mₛ, finAt(v) g]) ^ (1 : ℂ) = _
  rw [Complex.cpow_one, PontryaginDual.one_apply, Circle.coe_one, one_mul, sIdeleQuotientNorm_mk]
  congr 1
  let x : Iₛ := (eProd).symm (1, (eFin).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v g))
  let ev : (Iₛ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval x))
  change ev (sIdeleNorm F S) = _
  simp only [sIdeleNorm, map_mul, map_prod, map_pow]
  change (∏ w : InfinitePlace F,
      ‖((1 : w.Completionˣ) : w.Completion)‖ ^ w.mult) * ∏ v' : S,
      ‖(((@Pi.mulSingle S (fun u ↦ (u.val.adicCompletion F)ˣ) _ (Classical.decEq _) v g) v' :
        (v'.val.adicCompletion F)ˣ) :
        v'.val.adicCompletion F)‖ = _
  let : DecidableEq S := Classical.decEq _
  rw [Finset.prod_eq_single v (fun v' _ hv' ↦ by rw [Pi.mulSingle_eq_of_ne hv', Units.val_one,
      norm_one]) (fun h ↦ absurd (Finset.mem_univ v) h), Pi.mulSingle_eq_same]
  simp

/-- Paper: Equation (3.3.1.3), p. 129. The S-local correcting factor multiplies
the local Tate factors on the restricted quasi-characters. -/
def sLocalRhoFactor (c : Xₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalTateFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalTateFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.3), p. 129. With no finite places in S, the correcting
factor is the archimedean product. -/
theorem sLocalRhoFactor_archimedean (c : QuasiCharacter (SIdeleQuotient F ∅)) :
    sLocalRhoFactor c =
      ∏ w : InfinitePlace F, infiniteLocalTateFactor w (sLocalInfiniteRestriction w c) := by
  rw [sLocalRhoFactor, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]

/-- Restricting a unitary chart gives a unitary chart with the same exponent at an archimedean place. -/
private theorem sLocalInfinite_chart (χ : PontryaginDual Jₛ) (w : InfinitePlace F) :
    ∃ η : PontryaginDual w.Completionˣ, ∀ s : ℂ, sLocalInfiniteRestriction w (chartₛ(χ) s) =
      quasiCharacterNormTwist infiniteNorm(w) (continuous_infiniteLocalModule w) ((circleToComplex).comp η) s := by
  let h := sLocalInfiniteInsertion_properties (S := S) w
  let i : w.Completionˣ →ₜ* Jₛ := ⟨⟨⟨archAt(w), h.1⟩, h.2.1⟩, h.2.2⟩
  refine ⟨χ.comp i, fun s ↦ ?_⟩
  ext1 g
  change (χ (i g) : ℂ) * (modℂ[mₛ, i g]) ^ s = (χ (i g) : ℂ) * _ ^ s
  have hm := sLocalInfiniteRestriction_norm (S := S) w g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using
    congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ s) hm

/-- Restricting a unitary chart gives a unitary chart with the same exponent at a finite place. -/
private theorem sLocalFinite_chart (χ : PontryaginDual Jₛ) (v : S) :
    ∃ η : PontryaginDual (v.val.adicCompletion F)ˣ, ∀ s : ℂ, sLocalFiniteRestriction v (chartₛ(χ) s) =
      quasiCharacterNormTwist finiteNorm(v.val) (continuous_finiteLocalModule v.val) ((circleToComplex).comp η) s := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ := ⟨⟨⟨finAt(v), h.1⟩, h.2.1⟩, h.2.2⟩
  refine ⟨χ.comp i, fun s ↦ ?_⟩
  ext1 g
  change (χ (i g) : ℂ) * (modℂ[mₛ, i g]) ^ s = (χ (i g) : ℂ) * _ ^ s
  have hm := sLocalFiniteRestriction_norm v g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using
    congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ s) hm

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. The correcting factor is meromorphic
in each norm-twist coordinate. -/
theorem sLocalRhoFactor_meromorphic (χ : PontryaginDual Jₛ) :
    Meromorphic (fun s ↦ sLocalRhoFactor (chartₛ(χ) s)) := by
  have ha (w : InfinitePlace F) :
      Meromorphic (fun s ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (chartₛ(χ) s))) := by
    obtain ⟨η, he⟩ := sLocalInfinite_chart χ w
    simp_rw [he]
    exact meromorphicOn_univ.mp ((infiniteLocalTateFactor_spec w).1 η).meromorphicOn
  have hb (v : S) :
      Meromorphic (fun s ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) s))) := by
    obtain ⟨η, he⟩ := sLocalFinite_chart χ v
    simp_rw [he]
    exact meromorphicOn_univ.mp ((finiteLocalTateFactor_spec v.val).1 η).meromorphicOn
  intro z
  exact (MeromorphicAt.fun_prod (fun w _ ↦ ha w z)).mul
    (MeromorphicAt.fun_prod (fun v _ ↦ hb v z))

/-- The product σ-algebra on the S-adeles is the Borel σ-algebra. -/
theorem sAdeleRing_borelSpace : BorelSpace Aₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  exact inferInstanceAs (BorelSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))

/-- The σ-algebra on the S-ideles pulled back from the S-adeles is their Borel σ-algebra,
because the S-ideles carry the subspace topology. -/
theorem sIdeleGroup_borelSpace : BorelSpace Iₛ := by
  have := sAdeleRing_borelSpace (F := F) (S := S)
  refine ⟨?_⟩
  rw [(sIdeleGroup_description F S).1.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
  rfl

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa measure is a
Haar measure on the S-ideles. -/
theorem sMultiplicativeTamagawaMeasure_isHaarMeasure : (μₛ).IsHaarMeasure := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := by
    refine ⟨?_⟩
    rw [Units.isEmbedding_val₀.eq_induced, borel_comap, ← BorelSpace.measurable_eq]
    rfl
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) w
  let (v : S) := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v.val
  have := sIdeleGroup_borelSpace (F := F) (S := S)
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eInf := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let E := (ContinuousMulEquiv.mk' (eInf.symm.toHomeomorph.prodCongr eS.symm.toHomeomorph)
    (fun x y ↦ Prod.ext (map_mul eInf.symm x.1 y.1) (map_mul eS.symm x.2 y.2))).trans e.symm
  change (Measure.map E _).IsHaarMeasure
  have h1 : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  have h2 : (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val)).IsHaarMeasure :=
    Measure.pi.isHaarMeasure _
  have h3 : ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val))).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure _ _
  exact E.isHaarMeasure_map _

/-- Dualizing a norm twist inverts its unitary part and reflects its exponent. -/
private theorem sLocal_dual_normTwist (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) :=
  dualQuasiCharacter_normTwist mₛ hmₛ χ s

/-- The zeroth archimedean decay estimate bounds a Schwartz test everywhere. -/
private theorem sLocalSchwartz_bound (f : ℬ(Aₛ)) : ∃ B : ℝ, ∀ x : Aₛ, ‖f (Multiplicative.ofAdd x)‖ ≤ B := by
  obtain ⟨_, _, _, h⟩ := sAdeleSchwartz_exists_decay_bound F S f
  obtain ⟨B, _, hB⟩ := h 0
  exact ⟨B, fun x ↦ by simpa only [pow_zero, mul_one] using hB x⟩

/-- Paper: Lemma 3.3.1.3, p. 130. At each quasi-character of positive
abscissa, zeta integration is a continuous linear functional in the test function. -/
theorem sLocalIdelicZetaIntegral_tempered (c : Xₛ) (hc : c ∈ positive) :
    ∃ Z : ℬ(Aₛ) →L[ℂ] ℂ, ∀ f : ℬ(Aₛ), Z f = sLocalIdelicZetaIntegral f c := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let : BarrelledSpace ℂ ℬ(Aₛ) := (sAdeleSchwartz_montel F S).1
  let : ContinuousSMul ℂ ℬ(Aₛ) := (schwartzBruhat_stageWithSeminorms (Multiplicative Aₛ)).continuousSMul
  let v (g : Iₛ) : ℬ(Aₛ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd g.val)).comp (schwartzBruhatSubmodule _).subtype
  let w (g : Iₛ) := c (classOf g)
  have hv (g : Iₛ) : Continuous (fun f ↦ ‖v g f‖) :=
    schwartzBruhat_evalNorm_continuous (G := Multiplicative Aₛ) (Multiplicative.ofAdd g.val)
  have ev (g : Iₛ) (f : ℬ(Aₛ)) : v g f = f (Multiplicative.ofAdd g.val) := rfl
  clear_value v
  have hb (f : ℬ(Aₛ)) : ∃ B : ℝ, ∀ g : Iₛ, ‖v g f‖ ≤ B := by
    refine (sLocalSchwartz_bound (F := F) (S := S) f).elim fun B hB ↦ ?_
    exact ⟨B, fun g ↦ (congrArg norm (ev g f)).trans_le (hB g.val)⟩
  have hw : Continuous w := c.continuous.comp QuotientGroup.continuous_mk
  have hi (f : ℬ(Aₛ)) : Integrable (fun g ↦ v g f * w g) μₛ :=
    (sLocalIdelicZetaIntegral_integrable f c hc).congr (.of_forall fun g ↦ congrArg (· * w g) (ev g f).symm)
  refine (exists_continuousLinearMap_integral_mul (E := ℬ(Aₛ)) μₛ v hv hb w hw hi).elim fun Z hZ ↦ ?_
  exact ⟨Z, fun f ↦ (hZ f).trans (integral_congr_ae (.of_forall fun g ↦ congrArg (· * w g) (ev g f)))⟩

/-- The product formula also applies when the local coordinates of a Schwartz test
are given as ordinary functions. -/
private theorem sLocal_zeta_prod (c : Xₛ) (hc : c ∈ positive)
    (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → w.Completion → ℂ)
    (fFin : (v : S) → v.val.adicCompletion F → ℂ)
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, fArch w (x.1 w)) *
        ∏ v : S, fFin v (x.2 v)) :
    sLocalIdelicZetaIntegral f c =
      (∏ w : InfinitePlace F, localIdelicZetaIntegral
        (infiniteLocalMultiplicativeTamagawaMeasure F w) (fArch w)
        (sLocalInfiniteRestriction w c)) *
      ∏ v : S, localIdelicZetaIntegral
        (finiteLocalMultiplicativeTamagawaMeasure F v.val) (fFin v)
        (sLocalFiniteRestriction v c) := by
  classical
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := ⟨by
    change (borel w.Completion).comap Units.val = _
    rw [← borel_comap, ← (Units.isEmbedding_val₀ (G₀ := w.Completion)).eq_induced]⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.val.adicCompletion F)).secondCountableTopology
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let μa := infiniteLocalMultiplicativeTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  let (w : InfinitePlace F) : SigmaFinite (μa w) :=
    (infiniteLocalTamagawa_integrable_norm_rpow w (σ := 1) zero_lt_one (w.mult + 1) (by simp)).1
  let (v : S) : SigmaFinite (μb v) :=
    (finiteLocalTamagawa_integrable_norm_rpow v.val (σ := 1) zero_lt_one 1).1
  let E := (eProd).toHomeomorph.trans ((eArch).toHomeomorph.prodCongr (eFin).toHomeomorph)
  let φ (g : Iₛ) := f (Multiplicative.ofAdd g.val) * c (classOf g)
  let A (w : InfinitePlace F) (u : w.Completionˣ) :=
    fArch w u.val * sLocalInfiniteRestriction w c u
  let B (v : S) (u : (v.val.adicCompletion F)ˣ) :=
    fFin v u.val * sLocalFiniteRestriction v c u
  have hχ (a : (w : InfinitePlace F) → w.Completionˣ) (b : (v : S) → (v.val.adicCompletion F)ˣ) :
      c (classOf (E.symm (a, b))) = (∏ w, sLocalInfiniteRestriction w c (a w)) *
        ∏ v, sLocalFiniteRestriction v c (b v) := by
    obtain ⟨A, B, hA, hB, h⟩ := sIdeleQuotientCharacter_eq_prod_restrictions F S c
    have he (u : (w : InfinitePlace F) → w.Completionˣ) (v : (j : S) → (j.val.adicCompletion F)ˣ) :
        (eProd) (E.symm (u, v)) = ((eArch).symm u, (eFin).symm v) :=
      (eProd).apply_symm_apply _
    have h' := h (E.symm (a, b))
    rw [he, (eArch).apply_symm_apply, (eFin).apply_symm_apply] at h'
    have hf (v : S) (y : (v.val.adicCompletion F)ˣ) : B v y = sLocalFiniteRestriction v c y := by
      refine (hB v y).trans ?_
      apply congrArg (fun u ↦ c (classOf ((eProd).symm (1, (eFin).symm u))))
      congr 1
      exact Subsingleton.elim _ _
    exact h'.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ hA w _)
      (Finset.prod_congr rfl fun v _ ↦ hf v _))
  have hφ (a b) : φ (E.symm (a, b)) = (∏ w, A w (a w)) * ∏ v, B v (b v) := by
    dsimp only [φ]
    rw [hf, hχ]
    change ((∏ w, fArch w (a w).val) *
      ∏ v, fFin v (b v).val) * _ = _
    simp only [A, B, Finset.prod_mul_distrib]
    ring
  change (∫ g, φ g ∂(((Measure.pi μa).prod (Measure.pi μb)).map E.symm)) =
    (∏ w, ∫ u, A w u ∂μa w) * ∏ v, ∫ u, B v u ∂μb v
  have hi : Integrable φ μₛ := sLocalIdelicZetaIntegral_integrable f c hc
  exact (integral_map (φ := E.symm) E.symm.measurable.aemeasurable hi.aestronglyMeasurable).trans (by
    change (∫ p, φ (E.symm (p.1, p.2)) ∂((Measure.pi μa).prod (Measure.pi μb))) = _
    simp_rw [hφ]
    exact (integral_prod_mul (μ := Measure.pi μa) (ν := Measure.pi μb)
      (fun a ↦ ∏ w, A w (a w)) (fun b ↦ ∏ v, B v (b v))).trans
      (congrArg₂ (· * ·) (integral_fintype_prod_eq_prod A) (integral_fintype_prod_eq_prod B)))

/-- Paper: Remark 3.3.1.4, p. 131. On a pure tensor the S-local zeta
functional is the product of the local zeta functionals.
Deviation: Pointwise factorization specifies the pure tensors. -/
theorem sLocalIdelicZetaIntegral_pureTensor (c : Xₛ) (hc : c ∈ positive)
    (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
    (fFin : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) :
    sLocalIdelicZetaIntegral f c =
      (∏ w : InfinitePlace F, localIdelicZetaIntegral
        (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ fArch w (Multiplicative.ofAdd x))
        (sLocalInfiniteRestriction w c)) *
      ∏ v : S, localIdelicZetaIntegral
        (finiteLocalMultiplicativeTamagawaMeasure F v.val) (fun x ↦ fFin v (Multiplicative.ofAdd x))
        (sLocalFiniteRestriction v c) := by
  exact sLocal_zeta_prod c hc f (fun w x ↦ fArch w (Multiplicative.ofAdd x))
    (fun v x ↦ fFin v (Multiplicative.ofAdd x)) hf

-- Vanishing on a determining family of tests forces a continuous functional to vanish.
local notation "Determines(" G ", " P ")" =>
  ∀ L : SchwartzBruhat G →L[ℂ] ℂ, (∀ f : SchwartzBruhat G, P f → L f = 0) → ∀ f, L f = 0

section

open scoped TensorProduct
open UniformSpace
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- A separately continuous form that vanishes on determining pairs vanishes on
the algebraic tensor product. -/
private theorem schwartzTestsDetermine_tensor {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    {P : SchwartzBruhat G → Prop} {Q : SchwartzBruhat H → Prop}
    (hP : Determines(G, P)) (hQ : Determines(H, Q))
    (M : InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H) →L[ℂ] ℂ)
    (hm : ∀ f g, P f → Q g → M (f ⊗ₜ[ℂ] g) = 0) :
    ∀ t, M t = 0 := by
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat H) := schwartzBruhat_t2
  have hb := (continuous_inductiveTensor_iff (E := SchwartzBruhat G) (F := SchwartzBruhat H)
    M.toLinearMap).mp M.continuous
  let b := TensorProduct.mk ℂ (SchwartzBruhat G) (SchwartzBruhat H)
  have hright (f : SchwartzBruhat G) (hf : P f) (g : SchwartzBruhat H) : M (b f g) = 0 :=
    hQ (⟨M.toLinearMap.comp (b f), hb.1 f⟩) (fun g hg ↦ hm f g hf hg) g
  have hleft (f : SchwartzBruhat G) (g : SchwartzBruhat H) : M (b f g) = 0 :=
    hP (⟨M.toLinearMap.comp (b.flip g), hb.2 g⟩) (fun f hf ↦ hright f hf g) f
  let T : SchwartzBruhat G ⊗[ℂ] SchwartzBruhat H →ₗ[ℂ] ℂ := M.toLinearMap
  have hz : T = 0 := TensorProduct.ext' hleft
  exact fun t ↦ LinearMap.congr_fun hz t

/-- The Schwartz kernel theorem carries determining families on the two
factors to products of tests. -/
private theorem schwartzTestsDetermine_prod {G H T : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    [LocallyCompactSpace H] [SecondCountableTopology H]
    [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T] [LocallyCompactSpace T]
    (e : T ≃ₜ* G × H) {P : SchwartzBruhat G → Prop} {Q : SchwartzBruhat H → Prop}
    {R : SchwartzBruhat T → Prop} (hP : Determines(G, P)) (hQ : Determines(H, Q))
    (hR : ∀ f g h, P f → Q g → (∀ x : T, h x = f (e x).1 * g (e x).2) → R h) :
    Determines(T, R) := by
  intro L hL h
  let V := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)
  refine (schwartzBruhat_kernel_equiv (G := G) (H := H)).elim fun k hk ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e).elim fun pull hpull ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e.symm).elim fun push hpush ↦ ?_
  have hsur : Surjective pull := fun f ↦ ⟨push f, Subtype.ext (funext fun x ↦ by
    change pull (push f) x = f x
    rw [hpull, hpush, e.symm_apply_apply])⟩
  let : ContinuousSMul ℂ V := (withGeneratingSeminorms_spec _ _).continuousSMul
  let j : V →L[ℂ] Completion V := Completion.toComplL
  let J : Completion V →L[ℂ] ℂ := (L.comp pull).comp k.toContinuousLinearMap
  let M : V →L[ℂ] ℂ := J.comp j
  have hJ (u : Completion V) : J u = L (pull (k u)) := by
    simp only [J, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  have hM (t : V) : M t = J (t : Completion V) := by
    simp only [M, j, ContinuousLinearMap.comp_apply, Completion.coe_toComplL]
  clear_value M J
  have hpure (f : SchwartzBruhat G) (g : SchwartzBruhat H) (hf : P f) (hg : Q g) :
      M (f ⊗ₜ[ℂ] g) = 0 := by
    let t : V := f ⊗ₜ[ℂ] g
    change M t = 0
    let v : Completion V := Completion.coe' t
    have ht : M t = J v := by with_reducible exact hM t
    have hprod (x : G) (y : H) : k v (x, y) = f x * g y := by
      with_reducible exact hk f g x y
    have ha (x : T) : pull (k v) x = f (e x).1 * g (e x).2 := by
      refine (hpull (k v) x).trans ?_
      exact hprod (e x).1 (e x).2
    have hzero := hL (pull (k v)) (hR f g (pull (k v)) hf hg ha)
    with_reducible exact ht.trans ((hJ v).trans hzero)
  have hz := schwartzTestsDetermine_tensor (G := G) (H := H) hP hQ M hpure
  have hT (u : Completion V) : J u = 0 :=
    Completion.ext' J.continuous continuous_const (fun t ↦ (hM t).symm.trans (hz t)) u
  refine (hsur h).elim fun a ha ↦ ?_
  refine (k.surjective a).elim fun u hu ↦ ?_
  exact (congrArg L ha.symm).trans ((congrArg (fun v ↦ L (pull v)) hu.symm).trans ((hJ u).symm.trans (hT u)))

/-- Pure tests on a finite product determine its continuous functionals.
Split off one coordinate and apply the binary kernel theorem inductively. -/
private theorem schwartzTestsDetermine_pi {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)] :
    Determines((∀ i, G i), fun h : SchwartzBruhat (∀ i, G i) ↦
      ∃ f : (i : ι) → SchwartzBruhat (G i), ∀ x, h x = ∏ i, f i (x i)) := by
  classical
  by_cases hn : Nonempty ι
  · let i := hn.some
    let e : ((j : ι) → G j) ≃ₜ* G i × ((j : {j // j ≠ i}) → G j) :=
      ContinuousMulEquiv.mk' (Homeomorph.piSplitAt i G) (fun _ _ ↦ rfl)
    refine schwartzTestsDetermine_prod e (P := fun _ ↦ True) (fun L h f ↦ h f trivial)
      (schwartzTestsDetermine_pi (fun j : {j // j ≠ i} ↦ G j.val)) ?_
    rintro f _ h _ ⟨g, hg⟩ hh
    let a (j : ι) : SchwartzBruhat (G j) := if h : j = i then h ▸ f else g ⟨j, h⟩
    refine ⟨a, fun x ↦ ?_⟩
    rw [hh, hg, ← Fintype.prod_subtype_mul_prod_subtype (· = i)]
    congr 1
    · simp [a]; rfl
    · exact Finset.prod_congr rfl fun j _ ↦ by simp [a, j.property]; rfl
  · let : IsEmpty ι := not_nonempty_iff.mp hn
    intro L h f
    by_cases hz : f 1 = 0
    · have h0 : f = 0 := Subtype.ext (funext fun x ↦ (congrArg f (Subsingleton.elim x 1)).trans hz)
      rw [h0, map_zero]
    · have h1 := h ((f 1)⁻¹ • f) ⟨isEmptyElim, fun x ↦ by
        change (f 1)⁻¹ * f x = _
        simp [Subsingleton.elim x 1, hz]⟩
      simpa [map_smul, hz] using h1
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (p := fun j ↦ j ≠ i) (x := i) (by simp)

end

/-- Paper: Remark 3.3.1.4, p. 131. The zeta functional is determined among
continuous linear functionals by its product formula on pure tensors.
Deviation: The completed tensor functional is characterized by its continuous
extension property on the S-adelic test space itself. -/
theorem sLocalIdelicZetaIntegral_eq_of_pureTensor (c : Xₛ) (hc : c ∈ positive)
    (Z : ℬ(Aₛ) →L[ℂ] ℂ)
    (hZ : ∀ (f : ℬ(Aₛ)) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
      (fFin : (v : S) → ℬ(v.val.adicCompletion F)),
      (∀ x : Aₛ, f (Multiplicative.ofAdd x) =
        (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
          ∏ v : S, fFin v (Multiplicative.ofAdd (x.2 v))) →
      Z f = sLocalIdelicZetaIntegral f c) (f : ℬ(Aₛ)) :
    Z f = sLocalIdelicZetaIntegral f c := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let H (v : S) := Multiplicative (v.val.adicCompletion F)
  let T := Multiplicative Aₛ
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := inferInstanceAs (LocallyCompactSpace w.Completion)
  let (v : S) : LocallyCompactSpace (H v) := inferInstanceAs (LocallyCompactSpace (v.val.adicCompletion F))
  let : T2Space T := inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace T := inferInstanceAs (LocallyCompactSpace Aₛ)
  let e : T ≃ₜ* ((w : InfinitePlace F) → G w) × ((v : S) → H v) :=
    ContinuousMulEquiv.mk' (Homeomorph.refl _) (fun _ _ ↦ rfl)
  refine (sLocalIdelicZetaIntegral_tempered (F := F) (S := S) c hc).elim fun L hL ↦ ?_
  have hD : Determines(T, fun h : SchwartzBruhat T ↦ (Z - L) h = 0) :=
    schwartzTestsDetermine_prod e (schwartzTestsDetermine_pi G) (schwartzTestsDetermine_pi H) (R := fun h ↦ (Z - L) h = 0) (by
      rintro _ _ h ⟨a, ha⟩ ⟨b, hb⟩ hprod
      exact sub_eq_zero.mpr ((hZ h a b fun x ↦ (hprod _).trans (congrArg₂ (· * ·) (ha _) (hb _))).trans
        (hL h).symm))
  exact (sub_eq_zero.mp (hD (Z - L) (fun _ h ↦ h) f)).trans (hL f)

/-- Fourier transformation of a product test separates over the additive
Tamagawa product measure. -/
private theorem sLocal_fourier_prod (f : ℬ(Aₛ))
    (a : (w : InfinitePlace F) → w.Completion → ℂ) (b : (v : S) → v.val.adicCompletion F → ℂ)
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) = (∏ w, a w (x.1 w)) * ∏ v, b v (x.2 v))
    (y : Aₛ) : sAdeleSchwartzFourier f (Multiplicative.ofAdd y) =
      (∏ w, infiniteFourier(w) (a w) (y.1 w)) * ∏ v, finiteFourier(v.val) (b v) (y.2 v) := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let A (w : InfinitePlace F) (x : w.Completion) :=
    a w x * star (adeleStandardCharacter F (Pi.single w (x * y.1 w), 0) : ℂ)
  let B (v : S) (x : v.val.adicCompletion F) :=
    b v x * star (finiteLocalStandardCharacter F v.val (x * y.2 v) : ℂ)
  let μa := infiniteLocalAdditiveTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val
  let (w : InfinitePlace F) : SigmaFinite (μa w) :=
    inferInstanceAs (SigmaFinite (infiniteLocalAdditiveTamagawaMeasure F w))
  let (v : S) : SigmaFinite (μb v) :=
    inferInstanceAs (SigmaFinite (finiteLocalAdditiveTamagawaMeasure F v.val))
  have he (x : Aₛ) : f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F S (x * y) : ℂ) =
      (∏ w, A w (x.1 w)) * ∏ v, B v (x.2 v) := by
    rw [hf]
    let α (w : InfinitePlace F) := adeleStandardCharacter F (Pi.single w (x.1 w * y.1 w), 0)
    let β (v : S) := finiteLocalStandardCharacter F v.val (x.2 v * y.2 v)
    let C := (starRingEnd ℂ).toMonoidHom.comp Circle.coeHom
    change _ * C ((∏ w, α w) * ∏ v, β v) =
      (∏ w, a w (x.1 w) * C (α w)) * ∏ v, b v (x.2 v) * C (β v)
    rw [map_mul, map_prod, map_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  change (∫ x : Aₛ, f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F S (x * y) : ℂ)
    ∂(Measure.pi μa).prod (Measure.pi μb)) = (∏ w, ∫ x, A w x ∂μa w) * ∏ v, ∫ x, B v x ∂μb v
  simp_rw [he]
  exact (integral_prod_mul (μ := Measure.pi μa) (ν := Measure.pi μb)
    (fun p ↦ ∏ w, A w (p w)) (fun p ↦ ∏ v, B v (p v))).trans
    (congrArg₂ (· * ·) (integral_fintype_prod_eq_prod A) (integral_fintype_prod_eq_prod B))

/-- A local Fourier equation applies to restrictions along a module-preserving
insertion. Restriction commutes both with the norm twist and with duality. -/
private theorem sLocal_restrict_tate_equation {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace Kˣ] [IsTopologicalGroup Kˣ] {m : Kˣ →* ℝ≥0ˣ} {hm : Continuous m}
    {μ : Measure Kˣ} {fourier : (K → ℂ) → K → ℂ} {ρ : QuasiCharacter Kˣ → ℂ}
    (hρ : IsLocalTateFactor m hm μ fourier ρ) (i : Kˣ →ₜ* Jₛ)
    (hi : ∀ g, modℂ[mₛ, i g] = modℂ[m, g]) (f : ℬ(K)) (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s ∈ criticalStrip) :
    let c := chartₛ(χ) s
    let test := fun x ↦ f (Multiplicative.ofAdd x)
    localIdelicZetaIntegral μ test (c.comp i) = ρ (c.comp i) *
      localIdelicZetaIntegral μ (fourier test) ((dualQuasiCharacter mₛ hmₛ c).comp i) := by
  let c := chartₛ(χ) s
  let d := quasiCharacterNormTwist m hm ((circleToComplex).comp (χ.comp i)) s
  have hc : d = c.comp i := by
    ext1 g
    exact congrArg (fun x : ℂ ↦ (χ (i g) : ℂ) * x ^ s) (hi g).symm
  have hd : dualQuasiCharacter m hm d = (dualQuasiCharacter mₛ hmₛ c).comp i := by
    ext1 g
    change modℂ[m, g] * d g⁻¹ = modℂ[mₛ, i g] * c (i g)⁻¹
    rw [hi, hc]
    change _ * c (i g⁻¹) = _
    rw [map_inv]
  dsimp only
  have h := hρ.2 f (χ.comp i) s hs
  change localIdelicZetaIntegral μ _ d = ρ d * localIdelicZetaIntegral μ _ (dualQuasiCharacter m hm d) at h
  rwa [hd, hc] at h

/-- Multiply the local Tate equations for the coordinates of a pure test. -/
private theorem sLocal_functionalEquation_of_tensor (χ : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ criticalStrip)
    (f : ℬ(Aₛ)) (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) = (∏ w, a w (Multiplicative.ofAdd (x.1 w))) *
      ∏ v, b v (Multiplicative.ofAdd (x.2 v))) :
    let c := chartₛ(χ) s
    sLocalIdelicZetaIntegral f c = sLocalRhoFactor c *
      sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) (dualQuasiCharacter mₛ hmₛ c) := by
  let c := chartₛ(χ) s
  let d := dualQuasiCharacter mₛ hmₛ c
  have hc : c ∈ positive := ⟨χ, s, hs.1, rfl⟩
  have hd : d ∈ positive :=
    ⟨χ⁻¹, 1 - s, by simpa only [mem_preimage, mem_Ioi, Complex.sub_re, Complex.one_re] using sub_pos.mpr hs.2,
      sLocal_dual_normTwist χ s⟩
  let A (w : InfinitePlace F) (x : w.Completion) := a w (Multiplicative.ofAdd x)
  let B (v : S) (x : v.val.adicCompletion F) := b v (Multiplicative.ofAdd x)
  let A' (w : InfinitePlace F) := infiniteFourier(w) (A w)
  let B' (v : S) := finiteFourier(v.val) (B v)
  let μa := infiniteLocalMultiplicativeTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  have ha (w : InfinitePlace F) :
      localIdelicZetaIntegral (μa w) (A w) (sLocalInfiniteRestriction w c) =
        infiniteLocalTateFactor w (sLocalInfiniteRestriction w c) *
        localIdelicZetaIntegral (μa w) (A' w) (sLocalInfiniteRestriction w d) := by
    let h := sLocalInfiniteInsertion_properties (S := S) w
    let i : w.Completionˣ →ₜ* Jₛ := ⟨⟨⟨archAt(w), h.1⟩, h.2.1⟩, h.2.2⟩
    apply sLocal_restrict_tate_equation (infiniteLocalTateFactor_spec w) i _ (a w) χ s hs
    intro g
    have hm := sLocalInfiniteRestriction_norm (S := S) w g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using hm
  have hb (v : S) :
      localIdelicZetaIntegral (μb v) (B v) (sLocalFiniteRestriction v c) =
        finiteLocalTateFactor v.val (sLocalFiniteRestriction v c) *
        localIdelicZetaIntegral (μb v) (B' v) (sLocalFiniteRestriction v d) := by
    let h := sLocalFiniteInsertion_properties v
    let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ := ⟨⟨⟨finAt(v), h.1⟩, h.2.1⟩, h.2.2⟩
    apply sLocal_restrict_tate_equation (finiteLocalTateFactor_spec v.val) i _ (b v) χ s hs
    intro g
    have hm := sLocalFiniteRestriction_norm v g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using hm
  change sLocalIdelicZetaIntegral f c = sLocalRhoFactor c * sLocalIdelicZetaIntegral _ d
  rw [sLocal_zeta_prod c hc f A B hf, sLocal_zeta_prod d hd _ A' B' (sLocal_fourier_prod f A B hf)]
  change ((∏ w, localIdelicZetaIntegral (μa w) (A w) _) * ∏ v, localIdelicZetaIntegral (μb v) (B v) _) = _
  simp_rw [ha, hb]
  simp only [sLocalRhoFactor, Finset.prod_mul_distrib]
  ring

/-- Self-duality carries the continuous Fourier map on the Pontryagin dual
back to the S-adelic Schwartz space. -/
theorem sLocal_fourier_continuousLinear :
    ∃ T : ℬ(Aₛ) →L[ℂ] ℬ(Aₛ), ∀ f, T f = sAdeleSchwartzFourier f := by
  let G := Multiplicative Aₛ
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let : μ.Regular := hG.2.2.2.2
  refine (sAdditiveTamagawaMeasure_selfDual F S).elim fun e he ↦ ?_
  refine (schwartzBruhat_fourier_equiv μ).elim fun fourier hfourier ↦ ?_
  refine (exists_schwartzBruhat_comp_equivCLM e).elim fun P hP ↦ ?_
  refine ⟨P.comp fourier.toContinuousLinearMap, fun f ↦ Subtype.ext (funext fun y ↦ ?_)⟩
  change P (fourier f) y = tamagawaFourier _ _ _ y.toAdd
  exact (hP _ y).trans (((hfourier f).2 (e y)).trans
    (tamagawaFourier_eq_lcaFourier _ _ _ _ (e y) (fun x ↦ by
      rw [mul_comm x y.toAdd]; exact he.1 y.toAdd x)).symm)

/-- Paper: Theorem 3.3.1.1(1)(a), p. 129. The zeta integral satisfies the
Fourier equation on the strip where both integrals converge. -/
theorem sLocalIdelicZetaIntegral_functionalEquation (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s ∈ criticalStrip) :
    let c := chartₛ(χ) s
    sLocalIdelicZetaIntegral f c =
      sLocalRhoFactor c * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f)
        (dualQuasiCharacter mₛ hmₛ c) := by
  let c := chartₛ(χ) s
  let d := dualQuasiCharacter mₛ hmₛ c
  have hc : c ∈ positive := ⟨χ, s, hs.1, rfl⟩
  have hd : d ∈ positive :=
    ⟨χ⁻¹, 1 - s, by simpa only [mem_preimage, mem_Ioi, Complex.sub_re, Complex.one_re] using sub_pos.mpr hs.2,
      sLocal_dual_normTwist χ s⟩
  refine (sLocalIdelicZetaIntegral_tempered d hd).elim fun Z hZ ↦ ?_
  refine (sLocal_fourier_continuousLinear (F := F) (S := S)).elim fun T hT ↦ ?_
  let L := sLocalRhoFactor c • (Z.comp T)
  have hL (f : ℬ(Aₛ)) : L f = sLocalRhoFactor c * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) d :=
    congrArg (sLocalRhoFactor c * ·) ((hZ (T f)).trans (congrArg (fun g ↦ sLocalIdelicZetaIntegral g d) (hT f)))
  exact (sLocalIdelicZetaIntegral_eq_of_pureTensor c hc L (fun g a b h ↦
    (hL g).trans (sLocal_functionalEquation_of_tensor χ s hs g a b h).symm) f).symm.trans (hL f)

/-- The S-idelic module takes a value other than one. -/
private theorem sIdeleQuotientNorm_ne_one' : ∃ x, mₛ x ≠ 1 := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  exact ⟨σ t, (hσ t).trans_ne ht⟩

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa of a norm twist of a unitary
character of J_S is the real part of the exponent. -/
private theorem sLocal_abscissa_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    quasiCharacterAbscissa mₛ (isProperMap_sIdeleQuotientNorm F S) sIdeleQuotientNorm_ne_one'
      (chartₛ(χ) s) = s.re :=
  quasiCharacterAbscissa_of_unitary_twist mₛ (isProperMap_sIdeleQuotientNorm F S) _ _ χ s
    (fun _ ↦ rfl)

/-- Paper: §3.1.1, p. 119. If two norm-twist charts pass through the same
quasi-character, adding the same increment to both coordinates gives the same
quasi-character again. -/
private theorem sLocal_chart_add_of_eq {χ χ' : PontryaginDual Jₛ} {s s' : ℂ}
    (h : chartₛ(χ) s = chartₛ(χ') s') (z : ℂ) :
    chartₛ(χ) (s + z) = chartₛ(χ') (s' + z) := by
  ext1 g
  have hg := DFunLike.congr_fun h g
  have hn : (modℂ[mₛ, g]) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change (χ g : ℂ) * (modℂ[mₛ, g]) ^ s = (χ' g : ℂ) * (modℂ[mₛ, g]) ^ s' at hg
  change (χ g : ℂ) * (modℂ[mₛ, g]) ^ (s + z) = (χ' g : ℂ) * (modℂ[mₛ, g]) ^ (s' + z)
  rw [Complex.cpow_add _ _ hn, Complex.cpow_add _ _ hn, ← mul_assoc, ← mul_assoc, hg]

/-- Paper: Equation (3.1.1.4), p. 119. Duality in the norm-twist coordinate
takes the inverse unitary character and reflects the exponent. -/
private theorem sLocal_dual_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) := by
  ext1 g
  let N : ℂ := modℂ[mₛ, g]
  have hN : N ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  change N * chartₛ(χ) s g⁻¹ = chartₛ(χ⁻¹) (1 - s) g
  rw [map_inv]
  change N * ((χ g : ℂ) * N ^ s)⁻¹ = ((χ⁻¹ g : Circle) : ℂ) * N ^ (1 - s)
  rw [show ((χ⁻¹ g : Circle) : ℂ) = (χ g : ℂ)⁻¹ from Circle.coe_inv (χ g), mul_inv_rev, Complex.cpow_sub 1 s hN,
    Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem sLocal_eq_of_meromorphicNFOn {G H : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hH : MeromorphicNFOn H univ)
    (h : ∀ z : ℂ, 0 < z.re → G z = H z) (s : ℂ) : G s = H s := by
  have hAt : meromorphicOrderAt (G - H) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hAt
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
    hNear).eq_of_nhds

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. Chart continuations of the zeta integral
agree wherever two norm-twist charts pass through the same quasi-character. -/
private theorem sLocalIdelicZetaIntegral_chartContinuation_eq (f : ℬ(Aₛ))
    {χ χ' : PontryaginDual Jₛ} {G G' : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hG' : MeromorphicNFOn G' univ)
    (hGeq : ∀ s : ℂ, 0 < s.re → G s = sLocalIdelicZetaIntegral f (chartₛ(χ) s))
    (hG'eq : ∀ s : ℂ, 0 < s.re → G' s = sLocalIdelicZetaIntegral f (chartₛ(χ') s))
    {s s' : ℂ} (h : chartₛ(χ) s = chartₛ(χ') s') : G s = G' s' := by
  let d := s' - s
  have hRe : s.re = s'.re := by
    rw [← sLocal_abscissa_chart χ s, h, sLocal_abscissa_chart]
  have htw (z : ℂ) : chartₛ(χ') (z + d) = chartₛ(χ) z := by
    have := (sLocal_chart_add_of_eq h (z - s)).symm
    rwa [add_sub_cancel, show s' + (z - s) = z + d by ring] at this
  have hH : MeromorphicNFOn (fun z ↦ G' (z + d)) univ := fun z _ ↦
    (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := G')).mpr (hG' (mem_univ _))
  have hs := sLocal_eq_of_meromorphicNFOn hG hH (fun z hz ↦ by
    have hzd : 0 < (z + d).re := by
      simpa only [d, Complex.add_re, Complex.sub_re, hRe, sub_self, add_zero] using hz
    rw [hGeq z hz, hG'eq _ hzd, htw]) s
  rw [hs]
  change G' (s + (s' - s)) = G' s'
  rw [add_sub_cancel]

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. In each norm-twist coordinate, the zeta integral
on the right half-plane and the correcting factor times the dual zeta integral on the
half-plane left of one glue to a function with a normal-form meromorphic continuation. -/
private theorem sLocalIdelicZetaIntegral_exists_chartContinuation (f : ℬ(Aₛ))
    (χ : PontryaginDual Jₛ) :
    ∃ G : ℂ → ℂ, MeromorphicNFOn G univ ∧
      ∀ s : ℂ, 0 < s.re → G s = sLocalIdelicZetaIntegral f (chartₛ(χ) s) := by
  classical
  let Z (s : ℂ) := sLocalIdelicZetaIntegral f (chartₛ(χ) s)
  let W (s : ℂ) := sLocalRhoFactor (chartₛ(χ) s) *
    sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) (chartₛ(χ⁻¹) (1 - s))
  let M (s : ℂ) := if 0 < s.re then Z s else W s
  have hZ := sLocalIdelicZetaIntegral_analyticOn f χ
  have hZd := sLocalIdelicZetaIntegral_analyticOn (sAdeleSchwartzFourier f) χ⁻¹
  have hρ := sLocalRhoFactor_meromorphic χ
  have hRight : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLeft : IsOpen {s : ℂ | s.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hMZ (s : ℂ) (hs : 0 < s.re) : M =ᶠ[𝓝 s] Z :=
    Filter.mem_of_superset (hRight.mem_nhds hs) fun z hz ↦ if_pos hz
  have hMW (s : ℂ) (hs : s.re < 1) : M =ᶠ[𝓝 s] W := by
    refine Filter.mem_of_superset (hLeft.mem_nhds hs) fun z hz ↦ ?_
    by_cases h0 : 0 < z.re
    · change (if 0 < z.re then Z z else W z) = W z
      rw [if_pos h0]
      have hfe := sLocalIdelicZetaIntegral_functionalEquation f χ z ⟨h0, hz⟩
      simp only at hfe
      rw [sLocal_dual_chart] at hfe
      exact hfe
    · change (if 0 < z.re then Z z else W z) = W z
      rw [if_neg h0]
  have hZan (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ Z s := hZ s hs
  have hWmer (s : ℂ) (hs : s.re < 1) : MeromorphicAt W s := by
    have h1 : (1 - s) ∈ rightHalf := by
      change 0 < (1 - s).re
      rw [Complex.sub_re, Complex.one_re]
      linarith
    have hA : AnalyticAt ℂ (fun z : ℂ ↦ sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f)
        (chartₛ(χ⁻¹) (1 - z))) s :=
      (hZd (1 - s) h1).comp (by fun_prop)
    exact (hρ s).mul hA.meromorphicAt
  have hM : MeromorphicOn M univ := by
    intro s _
    by_cases hs : 0 < s.re
    · exact (hZan s hs).meromorphicAt.congr
        ((hMZ s hs).symm.filter_mono nhdsWithin_le_nhds)
    · have hs' : s.re < 1 := by linarith [not_lt.mp hs]
      exact (hWmer s hs').congr ((hMW s hs').symm.filter_mono nhdsWithin_le_nhds)
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn M univ, fun s hs ↦ ?_⟩
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr ((hZan s hs).congr (hMZ s hs).symm).meromorphicNFAt]
  exact if_pos hs

/-- Paper: Equation (3.1.1.2), p. 119. Every quasi-character of J_S is a norm twist of a
unitary character, with real exponent its abscissa. -/
private theorem sLocal_exists_chart (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), c = chartₛ(χ) s := by
  have : IsClosed ((sProjectedDiagonal F S) :
        Set Iₛ) := by
    let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
    let d := p.comp (integralAdeleDiagonal F S)
    obtain ⟨hd, hc, _⟩ := sAdele_additive_quotient F S
    rw [sProjectedDiagonal, MonoidHom.map_range]
    exact isClosed_range_unitsMap d.toMonoidHom hd hc
  have : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have hp := isProperMap_sIdeleQuotientNorm F S
  let a := quasiCharacterAbscissa mₛ hp sIdeleQuotientNorm_ne_one' c
  have hnorm := norm_quasiCharacter_eq_rpow_abscissa mₛ hp sIdeleQuotientNorm_ne_one' c
  let q : Xₛ := c * chartₛ((1 : PontryaginDual Jₛ)) (-(a : ℂ))
  have hmod (g : Jₛ) : 0 < ((mₛ g : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hq (g : Jₛ) : ‖q g‖ = 1 := by
    change ‖c g * ((((1 : PontryaginDual Jₛ) g : Circle) : ℂ) * (modℂ[mₛ, g]) ^ (-(a : ℂ)))‖ = 1
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, hnorm,
      Complex.norm_cpow_eq_rpow_re_of_pos (hmod g), Complex.neg_re, Complex.ofReal_re,
      ← Real.rpow_add (hmod g), add_neg_cancel, Real.rpow_zero]
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨q g, mem_sphere_zero_iff_norm.mpr (hq g)⟩
      map_one' := Circle.ext (map_one q)
      map_mul' := fun g h ↦ Circle.ext (map_mul q g h)
      continuous_toFun := q.continuous.subtype_mk _ }
  refine ⟨χ, a, ?_⟩
  ext1 g
  have hn : (modℂ[mₛ, g]) ≠ 0 := Complex.ofReal_ne_zero.mpr (hmod g).ne'
  change c g = (c g * ((((1 : PontryaginDual Jₛ) g : Circle) : ℂ) *
    (modℂ[mₛ, g]) ^ (-(a : ℂ)))) * (modℂ[mₛ, g]) ^ (a : ℂ)
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, mul_assoc, ← Complex.cpow_add _ _ hn,
    neg_add_cancel, Complex.cpow_zero, mul_one]

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The zeta integral has a unique
meromorphic continuation in normal form on each norm-twist coordinate. -/
theorem sLocalIdelicZetaIntegral_exists_continuation (f : ℬ(Aₛ)) :
    ∃! Z : Xₛ → ℂ, (∀ χ : PontryaginDual Jₛ,
      MeromorphicNFOn (fun s ↦ Z (chartₛ(χ) s)) univ) ∧
      EqOn Z (sLocalIdelicZetaIntegral f) positive := by
  classical
  choose G hGNF hGeq using sLocalIdelicZetaIntegral_exists_chartContinuation f
  choose χc sc hc using sLocal_exists_chart (F := F) (S := S)
  let Z : Xₛ → ℂ := fun c ↦ G (χc c) (sc c)
  have hZ (χ : PontryaginDual Jₛ) (s : ℂ) : Z (chartₛ(χ) s) = G χ s :=
    sLocalIdelicZetaIntegral_chartContinuation_eq f (hGNF _) (hGNF χ) (hGeq _) (hGeq χ)
      (hc (chartₛ(χ) s)).symm
  refine ⟨Z, ⟨fun χ ↦ ?_, fun c hc' ↦ ?_⟩, fun Z' ⟨hZ'NF, hZ'eq⟩ ↦ funext fun c ↦ ?_⟩
  · simpa only [hZ] using hGNF χ
  · obtain ⟨χ, s, hs, rfl⟩ := hc'
    exact (hZ χ s).trans (hGeq χ s hs)
  · rw [hc c, hZ]
    refine sLocal_eq_of_meromorphicNFOn (hZ'NF (χc c)) (hGNF (χc c)) (fun z hz ↦ ?_) (sc c)
    exact (hZ'eq ⟨χc c, z, hz, rfl⟩).trans (hGeq _ z hz).symm

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The S-local Z-function is the
meromorphic continuation of the zeta integral. -/
def sLocalIdelicZFunction (f : ℬ(Aₛ)) : Xₛ → ℂ :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. On the half-plane of convergence,
the continuation agrees with the defining integral. -/
theorem sLocalIdelicZFunction_eq_integral (f : ℬ(Aₛ)) :
    EqOn (sLocalIdelicZFunction f) (sLocalIdelicZetaIntegral f) positive :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose_spec.2

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. The S-local Z-function is
meromorphic in normal form in each norm-twist coordinate. -/
theorem sLocalIdelicZFunction_meromorphic (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    MeromorphicNFOn (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ :=
  (sLocalIdelicZetaIntegral_exists_continuation f).exists.choose_spec.1 χ

/-- Paper: Theorem 3.3.1.1(1)(b), p. 129. Every pole of the Z-function
lies at a pole of the correcting factor and has at most its pole order. -/
theorem sLocalIdelicZFunction_poles (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) :
    min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) s) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) s := by
  let Z (g : ℬ(Aₛ)) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction g (chartₛ(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chartₛ(χ) z)
  let D (z : ℂ) := Z (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)
  have hZ (g : ℬ(Aₛ)) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z g η) z :=
    ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hZa (g : ℬ(Aₛ)) (η : PontryaginDual Jₛ) : AnalyticOnNhd ℂ (Z g η) rightHalf :=
    (sLocalIdelicZetaIntegral_analyticOn g η).congr (isOpen_Ioi.preimage Complex.continuous_re)
      (fun z hz ↦ (sLocalIdelicZFunction_eq_integral g ⟨η, z, hz, rfl⟩).symm)
  by_cases hs : 0 < s.re
  · exact (min_le_left _ _).trans ((hZa f χ s hs).meromorphicOrderAt_nonneg)
  have hD : AnalyticAt ℂ D s :=
    (hZa _ _ (1 - s) (show 0 < (1 - s).re by simp; linarith)).comp (analyticAt_const.sub analyticAt_id)
  have hR := sLocalRhoFactor_meromorphic χ
  have hEq : Z f χ =ᶠ[codiscrete ℂ] R * D := by
    apply sLocal_meromorphic_identity (hZ f χ) (fun z ↦ (hR z).mul
      ((hZ _ _ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id)))
    intro z hz
    change Z f χ z = R z * D z
    have hd : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
    dsimp only [Z, D, R]
    rw [sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩,
      sLocalIdelicZFunction_eq_integral _ ⟨χ⁻¹, 1 - z, hd, rfl⟩]
    exact (sLocalIdelicZetaIntegral_functionalEquation f χ z hz).trans
      (congrArg (fun c ↦ R z * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) c)
        (sLocal_dual_normTwist χ z))
  have heq := hEq.filter_mono (nhdsNE_le_codiscrete s)
  change min 0 (meromorphicOrderAt R s) ≤ meromorphicOrderAt (Z f χ) s
  rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_mul (hR s) hD.meromorphicAt]
  exact (min_le_right _ _).trans (le_add_of_nonneg_right hD.meromorphicOrderAt_nonneg)

local notation "diagₛ" => sProjectedDiagonal F S

/-- Paper: Equation (3.1.2.1), p. 120. The projected diagonal S-units are closed in the
S-ideles. -/
theorem isClosed_sProjectedDiagonal : IsClosed (diagₛ : Set Iₛ) := by
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  let d := p.comp (integralAdeleDiagonal F S)
  obtain ⟨hd, hc, _⟩ := sAdele_additive_quotient F S
  rw [sProjectedDiagonal, MonoidHom.map_range]
  exact isClosed_range_unitsMap d.toMonoidHom hd hc

/-- Paper: Equation (3.1.2.1), p. 120. The projected diagonal S-units are discrete, since
they lie in the discrete diagonal S-integers. -/
theorem discreteTopology_sProjectedDiagonal : DiscreteTopology (diagₛ : Subgroup Iₛ) := by
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  let d := p.comp (integralAdeleDiagonal F S)
  obtain ⟨hd, -, hdisc, _⟩ := sAdele_additive_quotient F S
  let : DiscreteTopology (Set.range d) := isDiscrete_iff_discreteTopology.mp hdisc
  let f : (diagₛ : Subgroup Iₛ) → Set.range d := fun x ↦ ⟨x.val.val, by
    obtain ⟨_, ⟨u, rfl⟩, hx⟩ := x.prop
    exact ⟨u.val, by rw [← hx]; rfl⟩⟩
  exact .of_continuous_injective (f := f)
    (continuous_induced_rng.2 (Units.continuous_val.comp continuous_subtype_val))
    (fun x y h ↦ Subtype.ext (Units.ext (congrArg Subtype.val h)))

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa measure is
regular. -/
theorem sMultiplicativeTamagawaMeasure_regular : (μₛ).Regular := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hind := (sIdeleGroup_description F S).1
  have hemb : Topology.IsEmbedding (Units.val : Iₛ → Aₛ) := ⟨hind, Units.val_injective⟩
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : TopologicalSpace.MetrizableSpace Aₛ := inferInstanceAs (TopologicalSpace.MetrizableSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := hind.secondCountableTopology
  let : TopologicalSpace.MetrizableSpace Iₛ := hemb.metrizableSpace
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  infer_instance

/-- Paper: Theorem 3.3.1.1(2), p. 129. Weil's formula with counting measure
on the diagonal S-units determines the quotient Tamagawa measure. -/
theorem sLocalQuotientTamagawaMeasure_existsUnique :
    ∃! ν : Measure Jₛ, IsWeilQuotientMeasure _ μₛ Measure.count ν := by
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let := sMultiplicativeTamagawaMeasure_regular (F := F) (S := S)
  let : DiscreteTopology (diagₛ : Subgroup Iₛ) := discreteTopology_sProjectedDiagonal
  let : (Measure.count : Measure (diagₛ : Subgroup Iₛ)).IsHaarMeasure :=
    count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure (diagₛ : Subgroup Iₛ)).Regular :=
    count_regular_of_discreteTopology
  exact weilQuotientMeasure_existsUnique _ isClosed_sProjectedDiagonal μₛ Measure.count

/-- Paper: Equation (3.3.1.4), p. 129. The measure on the S-idele quotient
is Weil's quotient measure for the product measure and counting measure.
Deviation: The quotient here is J as specified in §3.3.1 and §3.1.2. -/
def sLocalQuotientTamagawaMeasure (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (SIdeleQuotient F S) :=
  (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).exists.choose

local notation "μJ" => sLocalQuotientTamagawaMeasure F S

/-- Paper: Theorem 3.3.1.1(2), p. 129. The quotient measure satisfies the
Weil normalization for integrals against the product measure on the S-ideles. -/
theorem sLocalQuotientTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure _ μₛ Measure.count μJ :=
  (sLocalQuotientTamagawaMeasure_existsUnique (F := F) (S := S)).exists.choose_spec

/-- Paper: Equation (3.3.1.4), p. 129. The theta Mellin integral weights
the S-local theta function by the quasi-character on the S-idele quotient. -/
def sLocalThetaMellinIntegral (f : ℬ(Aₛ)) (c : Xₛ) : ℂ :=
  ∫ g : Jₛ, sLocalAdelicThetaOnClasses F S f g * c g ∂μJ

/-- Unfold the weighted theta sum by applying Weil's formula to the integrable
zeta integrand. Counting the projected diagonal counts each S-unit once. -/
private theorem sLocalThetaMellin_unfold (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Jₛ ↦ sLocalAdelicThetaOnClasses F S f g * c g) μJ ∧
      sLocalThetaMellinIntegral f c = sLocalIdelicZetaIntegral f c := by
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let := sMultiplicativeTamagawaMeasure_regular (F := F) (S := S)
  let H : Subgroup Iₛ := diagₛ
  let : DiscreteTopology H := discreteTopology_sProjectedDiagonal
  let : (Measure.count : Measure H).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let U := (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ
  let d : U →* Iₛ := (Units.map ((adeleProjection F S).comp
    (integralAdelesOutside F S).subtype).toMonoidHom).comp
      (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  have hd : Injective d := fun _ _ h ↦ Units.ext ((sAdele_additive_quotient F S).1
    (congrArg Units.val h))
  have hr : d.range = H := by change _ = Subgroup.map _ _; rw [MonoidHom.map_range]
  let e : U ≃ H := (MonoidHom.ofInjective hd).toEquiv.trans (MulEquiv.subgroupCongr hr).toEquiv
  have he (u : U) : (e u : Iₛ) = d u := rfl
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable U := Units.val_injective.countable
  let : Countable H := e.surjective.countable
  let φ (g : Iₛ) := f (Multiplicative.ofAdd g.val) * c (classOf g)
  have hW := weilQuotientIntegral_L1 H isClosed_sProjectedDiagonal μₛ Measure.count μJ
    sLocalQuotientTamagawaMeasure_isWeil (sLocalIdelicZetaIntegral_integrable f c hc)
  have hfibre (q : Jₛ) : lcaCosetIntegral H Measure.count φ q =
      sLocalAdelicThetaOnClasses F S f q * c q := by
    let x : Iₛ := q.out
    have hx : classOf x = q := QuotientGroup.out_eq' q
    have hclass (h : H) : classOf (x * (h : Iₛ)) = q :=
      (QuotientGroup.mk_mul_of_mem x h.property).trans hx
    have hsum : Summable (fun u : U ↦ ‖f (Multiplicative.ofAdd (d u * x).val)‖) :=
      (sLocalAdelicTheta_summableUniformlyOn_norm F S f {x} isCompact_singleton).summable rfl
    change (∫ h : H, f (Multiplicative.ofAdd (x * (h : Iₛ)).val) * c (classOf (x * (h : Iₛ)))
      ∂Measure.count) = _
    simp_rw [hclass]
    rw [integral_mul_const]
    congr 1
    have hI : Integrable (fun h : H ↦ f (Multiplicative.ofAdd (x * (h : Iₛ)).val)) Measure.count := by
      apply integrable_count_iff.mpr
      rw [← e.summable_iff]
      simpa only [comp_def, he, mul_comm x] using hsum
    have hθ : sLocalAdelicThetaOnClasses F S f q = ∑' u : U, f (Multiplicative.ofAdd (d u * x).val) :=
      (congrArg (sLocalAdelicThetaOnClasses F S f) hx.symm).trans
        ((sLocalAdelicThetaOnClasses_mk F S f x).trans (sLocalAdelicTheta_apply F S f x))
    let term (h : H) := (Measure.count : Measure H).real {h} • f (Multiplicative.ofAdd (x * (h : Iₛ)).val)
    refine (integral_countable hI).trans ((e.tsum_eq term).symm.trans (Eq.trans ?_ hθ.symm))
    exact tsum_congr fun u ↦ by simp only [term, he, count_real_singleton, one_smul, mul_comm x]
  rw [show lcaCosetIntegral H Measure.count φ = _ from funext hfibre] at hW
  exact ⟨hW.2.1, hW.2.2.symm⟩

/-- Paper: Theorem 3.3.1.1(2)–(3), p. 129. The theta Mellin integral
unfolds to the zeta integral on the positive half-plane. -/
theorem sLocalThetaMellinIntegral_eq_zeta (f : ℬ(Aₛ)) :
    EqOn (sLocalThetaMellinIntegral f) (sLocalIdelicZetaIntegral f) positive := by
  intro c hc
  exact (sLocalThetaMellin_unfold f c hc).2

/-- Paper: Theorem 3.3.1.1(2), p. 129. The theta Mellin integrand is
absolutely integrable on the positive half-plane. -/
theorem sLocalThetaMellinIntegral_integrable (f : ℬ(Aₛ)) (c : Xₛ) (hc : c ∈ positive) :
    Integrable (fun g : Jₛ ↦ sLocalAdelicThetaOnClasses F S f g * c g) μJ := by
  exact (sLocalThetaMellin_unfold f c hc).1

/-- Paper: Theorem 3.3.1.1(2) and Remark 3.3.1.2, p. 129. The theta Mellin
integral converges uniformly on compact subsets under norm-band truncation.
Deviation: The positive band widths are indexed by n + 1. -/
theorem sLocalThetaMellinIntegral_tendstoUniformlyOn (f : ℬ(Aₛ))
    (K : Set Xₛ) (hK : IsCompact K) (hKpos : K ⊆ positive) :
    TendstoUniformlyOn (fun (n : ℕ) c ↦
      ∫ g in band[mₛ, n], sLocalAdelicThetaOnClasses F S f g * c g ∂μJ)
      (sLocalThetaMellinIntegral f) atTop K := by
  have hne : ∃ x, mₛ x ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let σ : Xₛ → ℝ := quasiCharacterAbscissa (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hσ := continuous_quasiCharacterAbscissa (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S) hne
  refine tendstoUniformlyOn_mellinBands μJ (fun g : Jₛ ↦ ((mₛ g : ℝ≥0) : ℝ))
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _))
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hmₛ)).measurable)
    (fun g ↦ ‖sLocalAdelicThetaOnClasses F S f g‖) (fun _ ↦ norm_nonneg _) σ
    (fun c g ↦ sLocalAdelicThetaOnClasses F S f g * c g) K hK hσ.continuousOn
    (fun c hc ↦ sLocalThetaMellinIntegral_integrable f c (hKpos hc)) ?_
  intro c hc g
  obtain ⟨χ, s, -, rfl⟩ := hKpos hc
  have hs : σ (chartₛ(χ) s) = s.re :=
    quasiCharacterAbscissa_of_unitary_twist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S) hne _ χ s (fun _ ↦ rfl)
  rw [norm_mul, hs]
  congr 1
  change ‖(χ g : ℂ) * (modℂ[mₛ, g]) ^ s‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul]
  exact Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _

/-- Paper: Theorem 3.3.1.1(2), p. 129. The theta Mellin integral is
holomorphic on the positive half-plane in each norm-twist coordinate. -/
theorem sLocalThetaMellinIntegral_analyticOn (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalThetaMellinIntegral f (chartₛ(χ) s)) rightHalf := by
  exact AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re)
    (sLocalIdelicZetaIntegral_analyticOn f χ)
    (fun s hs ↦ (sLocalThetaMellinIntegral_eq_zeta f ⟨χ, s, hs, rfl⟩).symm)

local notation "normProduct(" τ ")" =>
  (fun x : J₁ × ℝ≥0ˣ ↦ (x.1 : Jₛ) * classOf (τ x.2))

/-- Paper: Theorem 3.3.1.1(3), p. 129. The product of Haar measure on
the norm-one group with dt/t transports to the quotient Tamagawa measure. -/
theorem sLocalNormOneQuotientMeasure_existsUnique :
    ∃! ν : Measure J₁, ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) →
        (ν.prod positiveRealHaar).map (normProduct(τ)) = μJ := by
  -- Topology and measurability of the S-ideles and their quotient.
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hind := (sIdeleGroup_description F S).1
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := hind.secondCountableTopology
  let : T2Space Iₛ := (sIdeleGroup_description F S).2.1
  let : LocallyCompactSpace Iₛ := (sIdeleGroup_description F S).2.2.1
  have : IsClosed (diagₛ : Set Iₛ) := isClosed_sProjectedDiagonal
  have : BorelSpace Jₛ := ⟨rfl⟩
  have : BorelSpace J₁ := ⟨rfl⟩
  have hmc : Continuous mₛ := hmₛ
  have : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hμJ := sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)
  have : (μJ).IsHaarMeasure := hμJ.1
  -- Probability Haar measure on the compact norm-one group.
  let ν₀ : Measure J₁ := Measure.haarMeasure ⊤
  have hν₀ : ν₀ univ = 1 := Measure.haarMeasure_self
  -- A norm section through one infinite place.
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ₀ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩
  have hτ₀ : RightInverse τ₀ (sIdeleNorm F S) := by
    intro t
    let A := integralAdelesOutside F S
    have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
      simp only [A, integralAdelesOutside, Subring.mem_iInf]
      intro v _
      exact (v.adicCompletionIntegers F).one_mem
    have ht : s t ∈ A.toSubmonoid.units :=
      ⟨hmem t, by
        change ((s t)⁻¹).val ∈ A
        rw [← map_inv]
        exact hmem t⁻¹⟩
    let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
    exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)
  -- For each section, multiplication identifies the product with the quotient.
  have hnorm (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (t : ℝ≥0ˣ) :
      mₛ (classOf (τ t)) = t := (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  let E (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : (J₁ × ℝ≥0ˣ) ≃ₜ* Jₛ :=
    { toFun := normProduct(τ)
      invFun := fun y ↦ (⟨y * (classOf (τ (mₛ y)))⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnorm τ hτ, mul_inv_cancel]⟩, mₛ y)
      left_inv := fun x ↦ by
        have hk : mₛ (x.1 : Jₛ) = 1 := x.1.property
        have hx : mₛ ((x.1 : Jₛ) * classOf (τ x.2)) = x.2 := by
          rw [map_mul, hk, one_mul, hnorm τ hτ]
        refine Prod.ext (Subtype.ext ?_) hx
        change (x.1 : Jₛ) * classOf (τ x.2) *
          (classOf (τ (mₛ ((x.1 : Jₛ) * classOf (τ x.2)))))⁻¹ = x.1
        rw [hx, mul_inv_cancel_right]
      right_inv := fun y ↦ by simp
      map_mul' := fun x y ↦ by
        change ((x.1 * y.1 : J₁) : Jₛ) * classOf (τ (x.2 * y.2)) =
          ((x.1 : Jₛ) * classOf (τ x.2)) * ((y.1 : Jₛ) * classOf (τ y.2))
        rw [map_mul, QuotientGroup.mk_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _
      continuous_toFun := by
        have : Continuous (classOf) := QuotientGroup.continuous_mk
        fun_prop
      continuous_invFun := by
        have : Continuous (classOf) := QuotientGroup.continuous_mk
        refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hmc
        exact continuous_id.mul ((this.comp (τ.continuous.comp hmc)).inv) }
  let M (τ : ℝ≥0ˣ →ₜ* Iₛ) : Measure Jₛ := (ν₀.prod positiveRealHaar).map (normProduct(τ))
  have hMH (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : (M τ).IsHaarMeasure :=
    (E τ hτ).isHaarMeasure_map (ν₀.prod positiveRealHaar)
  -- The band of norms between one and e has mass one for each of these measures.
  let T : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hTm : MeasurableSet T :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRT : positiveRealHaar T = 1 := by
    let T₀ : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT₀ : ((T₀.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T₀ (by rw [hT₀]; exact Real.one_le_exp zero_le_one)
    rw [hT₀, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set Jₛ := mₛ ⁻¹' T
  have hBm : MeasurableSet B := hmc.measurable hTm
  have hMB (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) : M τ B = 1 := by
    have hφ : Continuous (normProduct(τ)) := (E τ hτ).continuous
    rw [Measure.map_apply hφ.measurable hBm]
    have hpre : normProduct(τ) ⁻¹' B = univ ×ˢ T := by
      ext ⟨k, t⟩
      have hk : mₛ (k : Jₛ) = 1 := k.property
      change mₛ ((k : Jₛ) * classOf (τ t)) ∈ T ↔ _
      rw [map_mul, hk, one_mul, hnorm τ hτ]
      simp
    rw [hpre, Measure.prod_prod, hν₀, one_mul, hPRT]
  -- Every such measure is the same multiple of the quotient Tamagawa measure.
  have hscale (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
      μJ = μJ B • M τ := by
    have := hMH τ hτ
    have h := Measure.isMulLeftInvariant_eq_smul μJ (M τ)
    have hB := congrArg (fun ν : Measure Jₛ ↦ ν B) h
    simp only [smul_apply, ENNReal.smul_def, smul_eq_mul, hMB τ hτ, mul_one] at hB
    rw [hB, ← ENNReal.smul_def]
    exact h
  have hTcpt : IsCompact T := by
    let h := Nonneg.unitsHomeomorphPos ℝ
    have hK : IsCompact {y : {x : ℝ // 0 < x} | y.val ∈ Icc 1 (Real.exp 1)} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1) using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by linarith [hx.1]⟩, hx, rfl⟩
    have hTeq : T = h ⁻¹' {y | y.val ∈ Icc 1 (Real.exp 1)} := rfl
    rw [hTeq, ← h.image_symm]
    exact hK.image h.symm.continuous
  have hBtop : μJ B ≠ ⊤ :=
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage hTcpt).measure_lt_top.ne
  have hB0 : μJ B ≠ 0 := by
    intro h
    have h' := hscale τ₀ hτ₀
    rw [h, zero_smul] at h'
    exact NeZero.ne μJ h'
  have hmap (c : ENNReal) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) :
      ((c • ν₀).prod positiveRealHaar).map (normProduct(τ)) = c • M τ := by
    have hφ : Continuous (normProduct(τ)) := (E τ hτ).continuous
    rw [Measure.prod_smul_left, Measure.map_smul _ hφ.aemeasurable]
  refine ⟨μJ B • ν₀, ⟨Measure.IsHaarMeasure.smul _ hB0 hBtop, Measure.Regular.smul hBtop,
    fun τ hτ ↦ (hmap _ τ hτ).trans (hscale τ hτ).symm⟩, ?_⟩
  rintro ν' ⟨hν'H, hν'R, hν'⟩
  have : SecondCountableTopology J₁ := TopologicalSpace.Subtype.secondCountableTopology _
  have h := Measure.isMulLeftInvariant_eq_smul ν' ν₀
  have hm' := hν' τ₀ hτ₀
  rw [h, ENNReal.smul_def, hmap _ τ₀ hτ₀] at hm'
  have hd := congrArg (fun ν : Measure Jₛ ↦ ν B) hm'
  simp only [smul_apply, hMB τ₀ hτ₀, smul_eq_mul, mul_one] at hd
  rw [h, ENNReal.smul_def, hd]

/-- Paper: Theorem 3.3.1.1(3), p. 129. Normalize Haar measure on the
norm-one S-idele quotient by splitting the quotient measure against dt/t. -/
def sLocalNormOneQuotientMeasure (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (sIdeleQuotientNorm F S).ker :=
  (sLocalNormOneQuotientMeasure_existsUnique (F := F) (S := S)).exists.choose

local notation "μJ₁" => sLocalNormOneQuotientMeasure F S

/-- Paper: Theorem 3.3.1.1(3), p. 129. Multiplication using any norm
section pushes the product with dt/t to the quotient Tamagawa measure. -/
theorem sLocalNormOneQuotientMeasure_normProduct :
    (μJ₁).IsHaarMeasure ∧ ∀ τ : ℝ≥0ˣ →ₜ* Iₛ, RightInverse τ (sIdeleNorm F S) →
      ((μJ₁).prod positiveRealHaar).map (normProduct(τ)) = μJ :=
  have h := (sLocalNormOneQuotientMeasure_existsUnique (F := F) (S := S)).exists.choose_spec
  ⟨h.1, h.2.2⟩

section Homogeneous

local instance : Measure.IsHaarMeasure μJ₁ :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

local notation "ωOf(" χ ")" => (χ : PontryaginDual Jₛ).comp
  (⟨Subgroup.subtype (mₛ).ker, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ)
local notation "radial[" τ "," f "," χ "," s "]" => (fun t : ℝ≥0ˣ ↦
  sLocalHomogeneousAdelicTheta F S μJ₁ (ωOf(χ)) f (classOf (τ t)) * chartₛ(χ) s (classOf (τ t)))

/-- Paper: Equation (3.3.1.5), p. 129. The radial Mellin integral is the
dt/t integral of the homogeneous theta term times the section's character. -/
def sLocalRadialMellinIntegral (τ : ℝ≥0ˣ →ₜ* Iₛ) (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) : ℂ :=
  ∫ t : ℝ≥0ˣ, radial[τ, f, χ, s] t ∂positiveRealHaar

/-- Paper: Theorem 3.3.1.1(3), p. 129. On the positive half-plane the
radial integral agrees with the quotient theta Mellin integral. -/
theorem sLocalRadialMellinIntegral_eq_theta
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ rightHalf) :
    sLocalRadialMellinIntegral τ f χ s = sLocalThetaMellinIntegral f (chartₛ(χ) s) := by
  let c := chartₛ(χ) s
  let G (g : Jₛ) := sLocalAdelicThetaOnClasses F S f g * c g
  have hG : Integrable G μJ := sLocalThetaMellinIntegral_integrable f c ⟨χ, s, hs, rfl⟩
  have hmap := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  rw [← hmap] at hG
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : e x = Units.mk0 (Real.exp x).toNNReal (by positivity) := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  let : SigmaFinite positiveRealHaar := by
    unfold positiveRealHaar
    rw [← funext he]
    exact e.toMeasurableEquiv.sigmaFinite_map
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology Jₛ := inferInstance
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have hm : Measurable (normProduct(τ)) :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul
      ((QuotientGroup.continuous_mk.comp τ.continuous).measurable.comp measurable_snd)
  have hprod := hG.comp_aemeasurable hm.aemeasurable
  change (∫ t, radial[τ, f, χ, s] t ∂positiveRealHaar) = ∫ g, G g ∂μJ
  refine (congrArg (fun μ ↦ ∫ g, G g ∂μ) hmap).symm.trans ?_ |>.symm
  refine (integral_map hm.aemeasurable hG.aestronglyMeasurable).trans ?_
  refine (integral_prod_symm _ hprod).trans ?_
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  change (∫ h : J₁, G (h.val * classOf (τ t)) ∂μJ₁) = radial[τ, f, χ, s] t
  simp only [sLocalHomogeneousAdelicTheta, IsLinearMap.mk'_apply, ContinuousMap.coe_mk]
  rw [← integral_mul_const]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  have hker : c h.val = (χ h.val : ℂ) := by
    change (χ h.val : ℂ) * modℂ[mₛ, h.val] ^ s = (χ h.val : ℂ)
    rw [MonoidHom.mem_ker.mp h.property]
    simp
  change sLocalAdelicThetaOnClasses F S f (h.val * classOf (τ t)) *
      c (h.val * classOf (τ t)) =
    (sLocalAdelicThetaOnClasses F S f (classOf (τ t) * h.val) * (χ h.val : ℂ)) *
      c (classOf (τ t))
  rw [map_mul c, hker, mul_assoc, mul_comm h.val]

/-- Paper: Theorem 3.3.1.1(3), p. 129. The radial Mellin integrand is
absolutely integrable for each positive abscissa. -/
theorem sLocalRadialMellinIntegral_integrable
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ rightHalf) :
    Integrable (radial[τ, f, χ, s]) positiveRealHaar := by
  let c := chartₛ(χ) s
  let G (g : Jₛ) := sLocalAdelicThetaOnClasses F S f g * c g
  have hG : Integrable G μJ := sLocalThetaMellinIntegral_integrable f c ⟨χ, s, hs, rfl⟩
  rw [← (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ] at hG
  let : BorelSpace Jₛ := ⟨rfl⟩
  let : BorelSpace J₁ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let e : ℝ ≃ₜ ℝ≥0ˣ :=
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : e x = Units.mk0 (Real.exp x).toNNReal (by positivity) := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  let : SigmaFinite positiveRealHaar := by
    unfold positiveRealHaar
    rw [← funext he]
    exact e.toMeasurableEquiv.sigmaFinite_map
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : SecondCountableTopology Jₛ := inferInstance
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage isCompact_singleton)
  have hm : Measurable (normProduct(τ)) :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul
      ((QuotientGroup.continuous_mk.comp τ.continuous).measurable.comp measurable_snd)
  have hprod := hG.comp_aemeasurable hm.aemeasurable
  refine hprod.integral_prod_right.congr (.of_forall fun t ↦ ?_)
  change (∫ h : J₁, G (h.val * classOf (τ t)) ∂μJ₁) = radial[τ, f, χ, s] t
  simp only [sLocalHomogeneousAdelicTheta, IsLinearMap.mk'_apply, ContinuousMap.coe_mk]
  rw [← integral_mul_const]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  have hker : c h.val = (χ h.val : ℂ) := by
    change (χ h.val : ℂ) * modℂ[mₛ, h.val] ^ s = (χ h.val : ℂ)
    rw [MonoidHom.mem_ker.mp h.property]
    simp
  change sLocalAdelicThetaOnClasses F S f (h.val * classOf (τ t)) *
      c (h.val * classOf (τ t)) =
    (sLocalAdelicThetaOnClasses F S f (classOf (τ t) * h.val) * (χ h.val : ℂ)) *
      c (classOf (τ t))
  rw [map_mul c, hker, mul_assoc, mul_comm h.val]

/-- Paper: Theorem 3.3.1.1(3) and Remark 3.3.1.2, p. 129. The radial integral
truncated to closed norm bands converges uniformly on compact subsets of each
positive component.
Deviation: The compact sets are taken in a fixed norm-twist component. -/
theorem sLocalRadialMellinIntegral_tendstoUniformlyOn
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (K : Set ℂ) (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) s ↦
      ∫ t in band[MonoidHom.id ℝ≥0ˣ, n], radial[τ, f, χ, s] t ∂positiveRealHaar)
      (sLocalRadialMellinIntegral (F := F) (S := S) τ f χ) atTop K := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let r (t : ℝ≥0ˣ) : ℝ := t.val
  let A (t : ℝ≥0ˣ) : ℂ := sLocalHomogeneousAdelicTheta F S μJ₁ (ωOf(χ)) f (classOf (τ t))
  let C (s : ℂ) (t : ℝ≥0ˣ) : ℂ := chartₛ(χ) s (classOf (τ t))
  let H (s : ℂ) (t : ℝ≥0ˣ) : ℂ := A t * C s t
  have hr (t : ℝ≥0ˣ) : 0 < r t := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hm : Measurable r := (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hI (s : ℂ) (hs : s ∈ K) : Integrable (H s) positiveRealHaar :=
    sLocalRadialMellinIntegral_integrable (F := F) (S := S) τ hτ f χ s (hKpos hs)
  have hC (s : ℂ) (t : ℝ≥0ˣ) : ‖C s t‖ = r t ^ s.re := by
    change ‖(χ (classOf (τ t)) : ℂ) * (modℂ[mₛ, classOf (τ t)]) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk F S (τ t), hτ t]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (hr t) s
  have hN (s : ℂ) (_ : s ∈ K) (t : ℝ≥0ˣ) : ‖H s t‖ = ‖A t‖ * r t ^ s.re :=
    (norm_mul (A t) (C s t)).trans (congrArg (‖A t‖ * ·) (hC s t))
  exact tendstoUniformlyOn_mellinBands positiveRealHaar r hr hm (fun t ↦ ‖A t‖)
    (fun t ↦ norm_nonneg (A t)) Complex.re H K hK Complex.continuous_re.continuousOn hI hN

/-- Paper: Theorem 3.3.1.1(3), p. 129. The radial Mellin integral is
holomorphic on each positive norm-twist half-plane. -/
theorem sLocalRadialMellinIntegral_analyticOn
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (sLocalRadialMellinIntegral (F := F) (S := S) τ f χ) rightHalf := by
  exact AnalyticOnNhd.congr (isOpen_Ioi.preimage Complex.continuous_re)
    (sLocalThetaMellinIntegral_analyticOn f χ)
    (fun s hs ↦ (sLocalRadialMellinIntegral_eq_theta τ hτ f χ s hs).symm)

end Homogeneous

/-! ## The correcting factor -/

/-- A real test localized near the unit has a zeta integral with positive real
part. The archimedean test is a smooth bump and the finite tests are indicators
of compact open balls. -/
theorem sLocal_exists_real_test (c : Xₛ) (hc : c ∈ positive) :
    ∃ f : ℬ(Aₛ), (∀ x, star (f x) = f x) ∧ sLocalIdelicZetaIntegral f c ≠ 0 := by
  classical
  let χ (g : Iₛ) := c (classOf g)
  have hχ : Continuous χ := c.continuous.comp QuotientGroup.continuous_mk
  have h1 : χ 1 = 1 := by change c ((QuotientGroup.mk' _) 1) = 1; simp
  have hpos : {g | 0 < (χ g).re} ∈ 𝓝 (1 : Iₛ) :=
    (Complex.continuous_re.comp hχ).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simp [h1]))
  rw [(sIdeleGroup_description F S).1.nhds_eq_comap] at hpos
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hpos
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hU
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  obtain ⟨a, haV, hac, had, ha₀, ha₁⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((continuous_mixedCoordinates (F := F)).2.continuousAt.preimage_mem_nhds
      (show V ∈ 𝓝 (m.symm (m 1)) by simpa using hV))
  let A (x : InfiniteAdeleRing F) : ℂ := (a (m x) : ℂ)
  have hA : A ∘ Multiplicative.toAdd ∈ schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) :=
    (mem_archimedeanSchwartzBruhat_iff (F := F) A).2
      ⟨(hac.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp had), fun _ ↦ rfl⟩
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  let B (v : S) := Metric.closedBall (1 : v.val.adicCompletion F) (ε / 2)
  have hB (v : S) : IsClopen (B v) := IsUltrametricDist.isClopen_closedBall _ (half_pos hε).ne'
  let b (v : S) := (B v).indicator (1 : v.val.adicCompletion F → ℂ)
  have hb (v : S) := (mem_finitePlaceSchwartz_iff F v.val (b v)).2
    ⟨(LocallyConstant.charFn ℂ (hB v)).isLocallyConstant, HasCompactSupport.intro
      (isCompact_closedBall (1 : v.val.adicCompletion F) (ε / 2))
      (fun _ hx ↦ indicator_of_notMem hx _)⟩
  choose t ht using hb
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let f := e (TensorProduct.tmul ℂ (⟨_, hA⟩ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (PiTensorProduct.tprod ℂ t))
  have hf (x : Aₛ) : f (Multiplicative.ofAdd x) = A x.1 * ∏ v, b v (x.2 v) := by
    exact (he _ t x).trans (congrArg (A x.1 * ·) (Finset.prod_congr rfl fun v _ ↦ ht v _))
  have heval (x : Aₛ) : f (Multiplicative.ofAdd x) =
      if ∀ v, x.2 v ∈ B v then A x.1 else 0 := by
    rw [hf]
    split_ifs with hx
    · simp [b, hx]
    · obtain ⟨v, hv⟩ := not_forall.mp hx
      rw [Finset.prod_eq_zero (Finset.mem_univ v) (indicator_of_notMem hv _), mul_zero]
  have hf₁ : f (Multiplicative.ofAdd (1 : Aₛ)) = 1 := by
    rw [heval, ite_eq_left (by intro v; exact Metric.mem_closedBall_self (half_pos hε).le)]
    change (a (m 1) : ℂ) = 1
    exact_mod_cast ha₁
  refine ⟨f, fun x ↦ ?_, ?_⟩
  · rw [show f x = _ from heval x.toAdd]
    split_ifs <;> simp [A]
  · let G (g : Iₛ) := f (Multiplicative.ofAdd g.val) * χ g
    have hG : Integrable G μₛ := sLocalIdelicZetaIntegral_integrable f c hc
    have hcnt : Continuous G := ((schwartzBruhat_continuous f).comp
      (Units.continuous_val : Continuous (Units.val : Iₛ → Aₛ))).mul hχ
    have hnonneg (g : Iₛ) : 0 ≤ (G g).re := by
      dsimp only [G]
      rw [heval]
      split_ifs with hg
      · by_cases h : a (m g.val.1) = 0
        · simp [A, h]
        have hxV := haV (subset_tsupport _ h)
        change m.symm (m g.val.1) ∈ V at hxV
        rw [m.symm_apply_apply] at hxV
        have hxW := hεW ((dist_pi_lt_iff hε).mpr (fun v ↦ (hg v).trans_lt (half_lt_self hε)))
        have hx : 0 < (χ g).re := hsub (hVW ⟨hxV, hxW⟩)
        simpa [A, Complex.mul_re] using mul_nonneg (ha₀ (mem_range_self _)).1 hx.le
      · simp
    let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
    have hval : (G 1).re ≠ 0 := by simp [G, h1, hf₁]
    have hp := integral_pos_of_integrable_nonneg_ne_zero (Complex.continuous_re.comp hcnt)
      hG.re hnonneg hval
    intro hz
    change (∫ g, G g ∂μₛ) = 0 at hz
    exact hp.ne' ((integral_re hG).trans (congrArg Complex.re hz))

/-- Minus one is a diagonal S-unit. -/
private theorem sLocal_classOf_neg_one : classOf (-1 : Iₛ) = 1 := by
  refine (sIdeleQuotient_mk_eq_one F S _).2 ⟨-1, ?_⟩
  apply Units.ext
  simp

/-- Plancherel inversion for the self-dual S-adelic measure identifies the
second Fourier transform of a Schwartz test with reflection. -/
theorem sLocal_fourier_inversion (f : ℬ(Aₛ)) (y : Aₛ) :
    sAdeleSchwartzFourier (sAdeleSchwartzFourier f) (Multiplicative.ofAdd y) =
      f (Multiplicative.ofAdd (-y)) := by
  let G := Multiplicative Aₛ
  let μ : Measure G := sAdditiveTamagawaMeasure F S
  have hG := sAdele_fourierMeasure (F := F) (S := S)
  let : T2Space G := hG.1
  let : LocallyCompactSpace G := hG.2.1
  let : BorelSpace G := hG.2.2.1
  let : μ.IsHaarMeasure := hG.2.2.2.1
  let : μ.Regular := hG.2.2.2.2
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he, hν⟩ := sAdditiveTamagawaMeasure_selfDual F S
  let ν : Measure (PontryaginDual G) := μ.map e
  obtain ⟨fourier, hfourier⟩ := schwartzBruhat_fourier_equiv μ
  let g : SchwartzBruhat G := f
  let H : PontryaginDual G → ℂ := lcaFourier μ g
  have h1 : Integrable (g : G → ℂ) μ := (hfourier g).1
  have h2 := schwartzBruhat_memLp_two_of_integrable g h1
  have hFT (x : G) : sAdeleSchwartzFourier f x = H (e x) :=
    tamagawaFourier_eq_lcaFourier _ _ _ _ (e x) (fun a ↦ by rw [mul_comm a x.toAdd]; exact he x.toAdd a)
  have hH : Integrable H ν := by
    apply (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff).2
    exact ((hfourier (sAdeleSchwartzFourier f)).1).congr (.of_forall hFT)
  obtain ⟨u, hu, hformula⟩ := lcaInverseFourier_zeroAtInfty μ ν hν
    (h2.toLp g) H hH ((lcaFourier_unitary μ ν hν).exists.choose_spec _ h1 h2)
  have heq : (u : G → ℂ) = g := Measure.eq_of_ae_eq (hu.trans h2.coeFn_toLp)
    u.continuous (schwartzBruhat_continuous g)
  let a : G := Multiplicative.ofAdd (-y)
  have hi := hformula a
  rw [show u a = g a from congrFun heq a] at hi
  refine Eq.trans ?_ hi.symm
  change (∫ x : G, sAdeleSchwartzFourier f x * star (sAdeleStandardCharacter F S (x.toAdd * y) : ℂ) ∂μ) =
    ∫ χ : PontryaginDual G, H χ * (χ a : ℂ) ∂(μ.map e)
  refine Eq.trans ?_ (e.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map
    (μ := μ) (fun χ : PontryaginDual G ↦ H χ * (χ a : ℂ))).symm
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  change sAdeleSchwartzFourier f x * star (sAdeleStandardCharacter F S (x.toAdd * y) : ℂ) =
    H (e x) * (e x (Multiplicative.ofAdd (-y)) : ℂ)
  rw [hFT]
  congr 1
  rw [ofAdd_neg, map_inv, Circle.coe_inv_eq_conj]
  exact congrArg (fun u : Circle ↦ star (u : ℂ)) (he x.toAdd y).symm

/-- Paper: Proposition 3.3.1.5(1), p. 132. The product of the factors for
dual quasi-characters is the value of the quasi-character at minus one.
Deviation: Equality is in the codiscrete filter of each norm-twist coordinate. -/
theorem sLocalRhoFactor_mul_dual (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalRhoFactor c * sLocalRhoFactor (dualQuasiCharacter mₛ hmₛ c) =
        c (classOf (-1 : Iₛ)) := by
  let R (η : PontryaginDual Jₛ) (z : ℂ) := sLocalRhoFactor (chartₛ(η) z)
  let A (z : ℂ) := R χ z * R χ⁻¹ (1 - z)
  have hm : Meromorphic A := fun z ↦ (sLocalRhoFactor_meromorphic χ z).mul
    ((sLocalRhoFactor_meromorphic χ⁻¹ (1 - z)).comp_analyticAt (analyticAt_const.sub analyticAt_id))
  have heq : A =ᶠ[codiscrete ℂ] (fun _ ↦ 1) := by
    apply sLocal_meromorphic_identity hm (fun _ ↦ analyticAt_const.meromorphicAt)
    intro z hz
    obtain ⟨f, -, hf⟩ := sLocal_exists_real_test (chartₛ(χ) z) ⟨χ, z, hz.1, rfl⟩
    let g := sAdeleSchwartzFourier f
    let Z (f : ℬ(Aₛ)) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZetaIntegral f (chartₛ(η) z)
    have fe (f : ℬ(Aₛ)) (η : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ criticalStrip) :
        Z f η s = R η s * Z (sAdeleSchwartzFourier f) η⁻¹ (1 - s) := by
      exact (sLocalIdelicZetaIntegral_functionalEquation f η s hs).trans
        (congrArg (fun c ↦ R η s * sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) c)
          (sLocal_dual_normTwist η s))
    have hz' : 1 - z ∈ criticalStrip := by
      change 0 < (1 - z).re ∧ (1 - z).re < 1
      simp only [Complex.sub_re, Complex.one_re]
      constructor <;> linarith [hz.1, hz.2]
    have h₂ := fe g χ⁻¹ (1 - z) hz'
    simp only [sub_sub_cancel, inv_inv] at h₂
    have hdouble : Z (sAdeleSchwartzFourier g) χ z = Z f χ z := by
      let : BorelSpace Iₛ := sIdeleGroup_borelSpace
      let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
      let φ (x : Iₛ) := f (Multiplicative.ofAdd x.val) * chartₛ(χ) z (classOf x)
      refine Eq.trans ?_ (integral_mul_left_eq_self (μ := μₛ) φ (-1 : Iₛ))
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      change sAdeleSchwartzFourier g (Multiplicative.ofAdd x.val) * chartₛ(χ) z (classOf x) =
        f (Multiplicative.ofAdd ((-1 : Iₛ) * x).val) * chartₛ(χ) z (classOf ((-1 : Iₛ) * x))
      rw [sLocal_fourier_inversion f, QuotientGroup.mk_mul, sLocal_classOf_neg_one, one_mul,
        Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul]
    have h : Z f χ z = A z * Z f χ z := calc
      _ = R χ z * Z g χ⁻¹ (1 - z) := fe f χ z hz
      _ = R χ z * (R χ⁻¹ (1 - z) * Z f χ z) :=
        congrArg (R χ z * ·) (h₂.trans (congrArg (R χ⁻¹ (1 - z) * ·) hdouble))
      _ = _ := (mul_assoc _ _ _).symm
    exact mul_right_cancel₀ hf (h.symm.trans (one_mul _).symm)
  filter_upwards [heq] with z hz
  dsimp only
  rw [sLocal_dual_normTwist, sLocal_classOf_neg_one, map_one]
  exact hz

/-- Conjugating a chart inverts its unitary part and conjugates its exponent. -/
private theorem sLocal_chart_conj (χ : PontryaginDual Jₛ) (s : ℂ) (x : Jₛ) :
    chartₛ(χ⁻¹) (star s) x = star (chartₛ(χ) s x) := by
  let r : ℝ := (mₛ x : ℝ≥0)
  have hr : 0 ≤ r := (mₛ x).val.coe_nonneg
  change ((χ x)⁻¹ : Circle) * (r : ℂ) ^ (star s) = star ((χ x : ℂ) * (r : ℂ) ^ s)
  rw [star_mul', Circle.coe_inv_eq_conj]
  have h := Complex.cpow_conj (r : ℂ) s (by rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm)
  simpa [Complex.star_def] using congrArg ((star (χ x : ℂ)) * ·) h

/-- For a real test the Fourier transform at the opposite argument is the
conjugate of its value at the original argument. -/
private theorem sLocal_fourier_neg_of_real (f : ℬ(Aₛ)) (hf : ∀ x, star (f x) = f x) (y : Aₛ) :
    sAdeleSchwartzFourier f (Multiplicative.ofAdd (-y)) =
      star (sAdeleSchwartzFourier f (Multiplicative.ofAdd y)) := by
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  change (∫ x : Aₛ, f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F S (x * -y) : ℂ)
    ∂sAdditiveTamagawaMeasure F S) = star (∫ x : Aₛ, f (Multiplicative.ofAdd x) *
      star (sAdeleStandardCharacter F S (x * y) : ℂ) ∂sAdditiveTamagawaMeasure F S)
  rw [Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  have hp : sAdeleStandardCharacter F S (x * -y) = (sAdeleStandardCharacter F S (x * y))⁻¹ := by
    rw [← he x (-y), ← he x y, ofAdd_neg, map_inv]
  change f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F S (x * -y) : ℂ) =
    star (f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter F S (x * y) : ℂ))
  simp only [hp, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul', star_star, hf]

/-- Schwartz zeta integrals conjugate under conjugating a chart whenever
the integrand test conjugates by an idele translation of trivial class. -/
private theorem sLocal_zeta_conj (g : ℬ(Aₛ)) (u : Iₛ) (hu : classOf u = 1)
    (hg : ∀ x : Iₛ, g (Multiplicative.ofAdd (u * x).val) = star (g (Multiplicative.ofAdd x.val)))
    (χ : PontryaginDual Jₛ) (s : ℂ) :
    sLocalIdelicZetaIntegral g (chartₛ(χ⁻¹) (star s)) =
      star (sLocalIdelicZetaIntegral g (chartₛ(χ) s)) := by
  let : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  let φ (x : Iₛ) := g (Multiplicative.ofAdd x.val) * chartₛ(χ⁻¹) (star s) (classOf x)
  change (∫ x, φ x ∂μₛ) = star (∫ x : Iₛ, g (Multiplicative.ofAdd x.val) * chartₛ(χ) s (classOf x) ∂μₛ)
  rw [← integral_mul_left_eq_self φ u, Complex.star_def, ← integral_conj]
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  dsimp only [φ]
  rw [hg, QuotientGroup.mk_mul, hu, one_mul, sLocal_chart_conj]
  exact (star_mul' _ _).symm

/-- Paper: Proposition 3.3.1.5(1), p. 132. Conjugating the quasi-character
conjugates its factor and multiplies by the character at minus one.
Deviation: The conjugate character uses the inverse unitary base and the
conjugate exponent. Equality holds off a discrete set of exponents. -/
theorem sLocalRhoFactor_conj (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      sLocalRhoFactor (chartₛ(χ⁻¹) (star s)) =
        chartₛ(χ) s (classOf (-1 : Iₛ)) * star (sLocalRhoFactor (chartₛ(χ) s)) := by
  let R (η : PontryaginDual Jₛ) (z : ℂ) := sLocalRhoFactor (chartₛ(η) z)
  let A (z : ℂ) := star (R χ⁻¹ (star z))
  have hA : Meromorphic A := by
    intro z
    obtain ⟨n, hn⟩ := sLocalRhoFactor_meromorphic χ⁻¹ (star z)
    refine ⟨n, ?_⟩
    let G (w : ℂ) := (w - star z) ^ n * R χ⁻¹ w
    have hg : AnalyticAt ℂ G (star z) := hn
    have hr : AnalyticAt ℂ (fun w ↦ star (G (star w))) z := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [continuousAt_star (x := z) (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with w hw
      exact differentiableAt_conj_conj_iff.mpr hw
    simpa only [G, A, star_mul', star_pow, star_sub, star_star, smul_eq_mul] using hr
  have heq : A =ᶠ[codiscrete ℂ] R χ := by
    apply sLocal_meromorphic_identity hA (sLocalRhoFactor_meromorphic χ)
    intro z hz
    obtain ⟨f, hf, hn⟩ := sLocal_exists_real_test (chartₛ(χ) z) ⟨χ, z, hz.1, rfl⟩
    let g := sAdeleSchwartzFourier f
    let N := sLocalIdelicZetaIntegral f (chartₛ(χ) z)
    let D := sLocalIdelicZetaIntegral g (chartₛ(χ⁻¹) (1 - z))
    have hfe (η : PontryaginDual Jₛ) (s : ℂ) (hs : s ∈ criticalStrip) :
        sLocalIdelicZetaIntegral f (chartₛ(η) s) = R η s *
          sLocalIdelicZetaIntegral g (chartₛ(η⁻¹) (1 - s)) := by
      rw [sLocalIdelicZetaIntegral_functionalEquation f η s hs, sLocal_dual_normTwist]
    have h₁ : N = R χ z * D := hfe χ z hz
    have hz' : star z ∈ criticalStrip := by simpa only [mem_preimage, Complex.star_def, Complex.conj_re] using hz
    have h₂ := hfe χ⁻¹ (star z) hz'
    have hf' (x : Iₛ) : f (Multiplicative.ofAdd ((1 : Iₛ) * x).val) = star (f (Multiplicative.ofAdd x.val)) := by
      rw [one_mul, hf]
    have hg' (x : Iₛ) : g (Multiplicative.ofAdd ((-1 : Iₛ) * x).val) = star (g (Multiplicative.ofAdd x.val)) := by
      simpa only [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul] using sLocal_fourier_neg_of_real f hf x.val
    have left := sLocal_zeta_conj f 1 (by simp) hf' χ z
    have right := sLocal_zeta_conj g (-1) sLocal_classOf_neg_one hg' χ⁻¹ (1 - z)
    have hs : 1 - star z = star (1 - z) := by simp
    have hD : sLocalIdelicZetaIntegral g (chartₛ(χ⁻¹⁻¹) (1 - star z)) = star D :=
      (congrArg (fun t : ℂ ↦ sLocalIdelicZetaIntegral g (chartₛ(χ⁻¹⁻¹) t)) hs).trans right
    have hEq : star N = R χ⁻¹ (star z) * star D :=
      left.symm.trans (h₂.trans (congrArg (R χ⁻¹ (star z) * ·) hD))
    have h₂' : N = A z * D := by
      simpa only [star_mul', star_star] using congrArg star hEq
    exact mul_right_cancel₀ (right_ne_zero_of_mul fun h ↦ hn (h₁.trans h)) (h₂'.symm.trans h₁)
  filter_upwards [heq] with z hz
  rw [sLocal_classOf_neg_one, map_one, one_mul]
  exact (star_star _).symm.trans (congrArg star hz)

/-- Holomorphy of the local Tate factors passes to their finite product. -/
private theorem sLocalRhoFactor_analyticOn (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) rightHalf := by
  unfold sLocalRhoFactor
  apply AnalyticOnNhd.mul
  · apply Finset.analyticOnNhd_fun_prod
    intro w _
    obtain ⟨η, he⟩ := sLocalInfinite_chart χ w
    simp_rw [he]
    exact (infiniteLocalTateFactor_properties w).2 _ (infiniteLocalTateFactor_spec w) η
  · apply Finset.analyticOnNhd_fun_prod
    intro v _
    obtain ⟨η, he⟩ := sLocalFinite_chart χ v
    simp_rw [he]
    exact (finiteLocalTateFactor_properties v.val).2 _ (finiteLocalTateFactor_spec v.val) η

/-- Paper: Proposition 3.3.1.5(2), p. 132. On the critical line the correcting
factor is regular. -/
theorem sLocalRhoFactor_analyticAt_criticalLine (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s.re = 1 / 2) :
    AnalyticAt ℂ (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) s := by
  apply sLocalRhoFactor_analyticOn χ s
  change 0 < s.re
  rw [hs]
  norm_num

/-- Paper: Proposition 3.3.1.5(2), p. 132. On the critical line the correcting
factor has modulus one. -/
theorem sLocalRhoFactor_norm_criticalLine (χ : PontryaginDual Jₛ)
    (s : ℂ) (hs : s.re = 1 / 2) :
    ‖sLocalRhoFactor (chartₛ(χ) s)‖ = 1 := by
  let R (z : ℂ) := sLocalRhoFactor (chartₛ(χ) z)
  let D (z : ℂ) := sLocalRhoFactor (chartₛ(χ⁻¹) z)
  have hreflect : 1 - s = star s := by
    apply Complex.ext <;> norm_num [Complex.sub_re, hs]
  have hR : ContinuousAt R s := (sLocalRhoFactor_analyticAt_criticalLine χ s hs).continuousAt
  have hD : ContinuousAt D (star s) :=
    (sLocalRhoFactor_analyticAt_criticalLine χ⁻¹ (star s) (by simpa using hs)).continuousAt
  have hunit (z : ℂ) : ‖chartₛ(χ) z (classOf (-1 : Iₛ))‖ = 1 := by
    rw [sLocal_classOf_neg_one, map_one, norm_one]
  have hmul : (fun z ↦ ‖R z‖ * ‖D (1 - z)‖) =ᶠ[𝓝[≠] s] fun _ ↦ (1 : ℝ) := by
    filter_upwards [(sLocalRhoFactor_mul_dual χ).filter_mono (nhdsNE_le_codiscrete s)] with z hz
    rw [← hunit z, ← hz, norm_mul, sLocal_dual_normTwist χ z]
  have hconj : (fun z ↦ ‖D (star z)‖) =ᶠ[𝓝[≠] s] fun z ↦ ‖R z‖ := by
    filter_upwards [(sLocalRhoFactor_conj χ).filter_mono (nhdsNE_le_codiscrete s)] with z hz
    change ‖sLocalRhoFactor _‖ = _
    rw [hz, norm_mul, hunit, one_mul, norm_star]
  have hD' : ContinuousAt D (1 - s) := hreflect ▸ hD
  have hm := tendsto_nhds_unique_of_eventuallyEq
    ((hR.norm.mul (hD'.comp (continuousAt_const.sub continuousAt_id)).norm).continuousWithinAt
      (s := {s}ᶜ)) tendsto_const_nhds hmul
  have hc := tendsto_nhds_unique_of_eventuallyEq
    ((hD.comp continuousAt_star).norm.continuousWithinAt (s := {s}ᶜ))
    (hR.norm.continuousWithinAt (s := {s}ᶜ)) hconj
  change ‖R s‖ * ‖D (1 - s)‖ = 1 at hm
  change ‖D (star s)‖ = ‖R s‖ at hc
  rw [hreflect, hc] at hm
  change ‖R s‖ = 1
  nlinarith [norm_nonneg (R s)]

/-- Paper: Proposition 3.3.1.5(3), p. 132. Every complex derivative of the
correcting factor is holomorphic on the positive half-plane. -/
theorem sLocalRhoFactor_iteratedDeriv_analyticOn (χ : PontryaginDual Jₛ) (k : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z))) rightHalf := by
  rw [iteratedDeriv_eq_iterate]
  apply AnalyticOnNhd.iterated_deriv _ k
  exact sLocalRhoFactor_analyticOn χ

-- TODO(paper-gap): The bound (3.3.1.11) omits the archimedean degrees when
-- multiplying local factors. For F = ℚ(i), no finite places, and k = 0, the
-- trivial chart at Re(s) = 1 has growth of order |Im(s)|, rather than |Im(s)|^1/2.

-- This pass ends before the definition of the partial Euler product (3.3.1.25), p. 134.

end RiemannMasullo
