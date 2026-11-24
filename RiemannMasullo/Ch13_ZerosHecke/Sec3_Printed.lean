module

public import RiemannMasullo.Ch13_ZerosHecke.Sec3
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Printed claims about the capped critical-line trace

The codimension and trace identity in Theorem 13.3.1.1 are distinct claims.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "D[" F "]" => BruhatCompactSupport C[F]

/-- Paper: Theorem 13.3.1.1, p. 522. The common test subspace for all the
character jets in (13.3.1.2) is claimed to have codimension `[F : ℚ]`. -/
def Printed.criticalTraceTestCodimension : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    Module.rank ℂ (D[F] ⧸ criticalTraceTestSubmodule τ) = (Module.finrank ℚ F : Cardinal)

/-- Paper: Theorem 13.3.1.1, p. 522. Take `F = ℚ`, the section with positive real
component and finite components one, and identify the norm-one classes with
`ℤ̂ˣ`. Let `ω` be the nontrivial character of `(ℤ/4ℤ)ˣ`, pulled back along the
projection from `ℤ̂ˣ`. For a smooth compactly supported bump `b` with integral
one, the tests `b(log t)` and `b(log t) · conj (ω(k))` on `(t,k)` have, respectively,
moment pairs `(1,0)` and `(0,1)` for the trivial character and `ω`, by Haar
orthogonality. The common kernel therefore has codimension at least two. -/
theorem Printed.criticalTraceTestCodimension_false : ¬ Printed.criticalTraceTestCodimension :=
  by
  intro h
  let q : (AdeleRing (𝓞 ℚ) ℚ)ˣ →ₜ* C[ℚ] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C[ℚ] := q.comp
    ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  have hrank := criticalTraceTestSubmodule_rat_codimension_ge_two τ hτ
  rw [h ℚ τ hτ, Module.finrank_self] at hrank
  norm_num at hrank

local notation "ord[" F "](" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "mellinAt[" F "](" φ ", " χ ", " s ")" =>
  (∫ g : C[F], (φ : D[F]).val g * ideleClassNormTwist (F := F) χ s g ∂ideleClassTamagawaMeasure F)

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The capped
critical-line sum and the printed polar and local terms are claimed to converge
to the same continuous linear functional on the space satisfying (13.3.1.2). -/
def Printed.criticalTraceFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    let A := criticalTraceTestSubmodule (F := F) τ
    let zeros := {z : {χ : PontryaginDual C[F] // ∀ t, χ (τ t) = 1} × ℂ //
      0 < ord[F](z.1.val, z.2) ∧ z.2.re = 1 / 2}
    ∃ L : A →L[ℂ] ℂ, ∀ φ : A,
      HasSum (fun z : zeros ↦
        (criticalTraceMultiplicity (F := F) z.val.1.val z.val.2 z.property.1 : ℂ) *
          mellinAt[F](φ.val, z.val.1.val, z.val.2 - 1 / 2)) (L φ) ∧
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        HasSum (fun v : HeightOneSpectrum (𝓞 F) ↦ (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
          finiteConnesWeilPrincipalValue (F := F) v 1 (b v))
          (mellinAt[F](φ.val, 1, -1 / 2) + mellinAt[F](φ.val, 1, 1 / 2) -
            (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ)

private theorem criticalTraceFormula_false_schwartz {F : Type} [Field F] [NumberField F]
    (φ : D[F]) : φ.val ∈ schwartzBruhatSubmodule C[F] := by
  obtain ⟨m, _, h, hsur⟩ := exists_ideleClassModulation F
  rw [← modulatedExponentialDecaySubmodule_singleton_zero m]
  exact bruhatCompactSupport_le_modulatedExponentialDecay m {0} h hsur φ.property

private theorem criticalTraceFormula_false_translate {F : Type} [Field F] [NumberField F]
    (φ : D[F]) (a : C[F]) : ∃ ψ : D[F], ∀ g, ψ.val g = φ.val (a⁻¹ * g) := by
  let f : SchwartzBruhat C[F] := ⟨φ.val, criticalTraceFormula_false_schwartz φ⟩
  let v := schwartzBruhatTranslate a f
  exact ⟨⟨v.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth v),
    φ.property.2.comp_homeomorph (Homeomorph.mulLeft a⁻¹)⟩, fun _ ↦ rfl⟩

/-- Translation acts on each Mellin evaluation by the value of its character. -/
private theorem criticalTraceFormula_false_mellin_translate {F : Type} [Field F] [NumberField F]
    (φ ψ : D[F]) (a : C[F]) (ha : ∀ g, ψ.val g = φ.val (a⁻¹ * g))
    (χ : PontryaginDual C[F]) (s : ℂ) :
    mellinAt[F](ψ, χ, s) = ideleClassNormTwist χ s a * mellinAt[F](φ, χ, s) := by
  let ξ := ideleClassNormTwist χ s
  rw [← integral_const_mul]
  refine (integral_mul_left_eq_self (μ := ideleClassTamagawaMeasure F)
    (fun g ↦ ψ.val g * ξ g) a).symm.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
  change ψ.val (a * g) * ξ (a * g) = ξ a * (φ.val g * ξ g)
  rw [ha, inv_mul_cancel_left, map_mul, mul_left_comm]

/-- A translation multiplies each critical-line Mellin evaluation by a unit complex number. -/
private theorem criticalTraceFormula_false_mellin_norm {F : Type} [Field F] [NumberField F]
    (φ ψ : D[F]) (a : C[F]) (ha : ∀ g, ψ.val g = φ.val (a⁻¹ * g))
    (χ : PontryaginDual C[F]) (s : ℂ) (hs : s.re = 1 / 2) :
    ‖mellinAt[F](ψ, χ, s - 1 / 2)‖ = ‖mellinAt[F](φ, χ, s - 1 / 2)‖ := by
  let ξ := ideleClassNormTwist χ (s - 1 / 2)
  have hn : ‖ξ a‖ = 1 := by
    change ‖(χ a : ℂ) * (((ideleClassNorm F a).val : ℝ) : ℂ) ^ (s - 1 / 2)‖ = 1
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    norm_num [Complex.sub_re, hs]
  rw [criticalTraceFormula_false_mellin_translate φ ψ a ha, norm_mul, hn, one_mul]

local notation "lineZeros[" F "](" τ ")" =>
  {z : {χ : PontryaginDual C[F] // ∀ t, χ (τ t) = 1} × ℂ //
    0 < ord[F](z.1.val, z.2) ∧ z.2.re = 1 / 2}
local notation "term[" F "](" φ ", " z ")" =>
  ((criticalTraceMultiplicity (F := F) (z).val.1.val (z).val.2 (z).property.1 : ℂ) *
    mellinAt[F](φ, (z).val.1.val, (z).val.2 - 1 / 2))

/-- The bound for the critical-line sum depends only on the initial test. -/
private theorem criticalTraceFormula_false_spectral_bound {F : Type} [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C[F]) (φ : D[F]) :
    ∃ B : ℝ, ∀ (a : C[F]) (ψ : D[F]), (∀ g, ψ.val g = φ.val (a⁻¹ * g)) →
      ∀ {T : ℂ}, HasSum (fun z : lineZeros[F](τ) ↦ term[F](ψ, z)) T → ‖T‖ ≤ B := by
  let bound (z : lineZeros[F](τ)) := ‖term[F](φ, z)‖
  refine ⟨∑' z, bound z, fun a ψ ha T hT ↦ ?_⟩
  have he (z : lineZeros[F](τ)) : ‖term[F](ψ, z)‖ = bound z := by
    dsimp only [bound]
    rw [norm_mul, norm_mul, criticalTraceFormula_false_mellin_norm φ ψ a ha _ _ z.property.2]
  rw [← hT.tsum_eq]
  exact (norm_tsum_le_tsum_norm hT.summable.norm).trans_eq (tsum_congr he)

local notation "logNorm[" F "](" g ")" =>
  ((Real.log (((ideleClassNorm F g).val : ℝ))) : ℂ)
local notation "moment[" F "](" φ ", " χ ", " k ")" =>
  (∫ x : C[F], (φ : D[F]).val x * (χ x : ℂ) * logNorm[F](x) ^ (k : ℕ)
    ∂ideleClassTamagawaMeasure F)

private theorem criticalTraceFormula_false_log_mul {F : Type} [Field F] [NumberField F]
    (a b : C[F]) : logNorm[F](a * b) = logNorm[F](a) + logNorm[F](b) := by
  rw [map_mul]
  change ((Real.log ((((ideleClassNorm F a).val : ℝ)) * (((ideleClassNorm F b).val : ℝ))) : ℝ) : ℂ) = _
  rw [Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', Complex.ofReal_add]

/-- Under translation in the kernel of a unitary character, its zeroth moment
is constant and its first log moment is affine in the translating log norm. -/
private theorem criticalTraceFormula_false_translate_moments {F : Type} [Field F] [NumberField F]
    (φ ψ : D[F]) (a : C[F]) (ha : ∀ g, ψ.val g = φ.val (a⁻¹ * g))
    (χ : PontryaginDual C[F]) (hχ : χ a = 1) :
    moment[F](ψ, χ, 0) = moment[F](φ, χ, 0) ∧
    moment[F](ψ, χ, 1) = logNorm[F](a) * moment[F](φ, χ, 0) + moment[F](φ, χ, 1) := by
  let μ := ideleClassTamagawaMeasure F
  let f (x : C[F]) := φ.val x * (χ x : ℂ)
  let l (x : C[F]) := logNorm[F](x)
  have hbase (x : C[F]) : ψ.val (a * x) * (χ (a * x) : ℂ) = f x := by
    rw [ha, inv_mul_cancel_left, map_mul, hχ, one_mul]
  have hc : Continuous f := (schwartzBruhat_continuous
    (⟨φ.val, criticalTraceFormula_false_schwartz φ⟩ : SchwartzBruhat C[F])).mul
    (continuous_subtype_val.comp χ.continuous)
  have hs : HasCompactSupport f := φ.property.2.mul_right
  have hl : Continuous l := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
      fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  simp only [pow_zero, mul_one, pow_one]
  constructor
  · refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ ψ.val x * (χ x : ℂ)) a).symm.trans ?_
    exact integral_congr_ae (.of_forall hbase)
  · refine (integral_mul_left_eq_self (μ := μ) (fun x ↦ ψ.val x * (χ x : ℂ) * l x) a).symm.trans ?_
    have hsplit (x) : ψ.val (a * x) * (χ (a * x) : ℂ) * l (a * x) =
        l a * f x + f x * l x := by
      rw [hbase, show l (a * x) = l a + l x from criticalTraceFormula_false_log_mul a x]
      ring
    refine (integral_congr_ae (.of_forall hsplit)).trans ?_
    have h₀ : Integrable (fun x ↦ l a * f x) μ := (hc.integrable_of_hasCompactSupport hs).const_mul _
    have h₁ : Integrable (fun x ↦ f x * l x) μ := (hc.mul hl).integrable_of_hasCompactSupport hs.mul_right
    exact (integral_add h₀ h₁).trans (congrArg (· + ∫ x, f x * l x ∂μ) (integral_const_mul _ _))

private theorem criticalTraceFormula_false_jet {F : Type} [Field F] [NumberField F]
    (φ : D[F]) (χ : PontryaginDual C[F]) (k : ℕ) :
    (criticalTraceMoment_isLinearMap χ k).mk' _ φ = moment[F](φ, χ, k) := by
  change (∫ x, φ.val x * spectralZeroJet χ 0 0 k x ∂ideleClassTamagawaMeasure F) = _
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  change φ.val x * (ideleClassNormTwist χ _ x * logNorm[F](x) ^ k) = _
  have hc : ideleClassNormTwist χ (((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) x = (χ x : ℂ) := by
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    change (χ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  rw [hc]
  exact (mul_assoc _ _ _).symm

local notation "diffTest(" τ ", " t ", " q ", " η ", " x ")" =>
  (η).val ((τ (t * q ^ 2))⁻¹ * x) - 2 * (η).val ((τ (t * q))⁻¹ * x) + (η).val ((τ t)⁻¹ * x)

/-- Second differences along the norm section kill both the constant and the linear
log moments of every section-trivial character in degree two. -/
private theorem criticalTraceFormula_false_differences {F : Type} [Field F] [NumberField F]
    (hd : Module.finrank ℚ F ≤ 2) (τ : ℝ≥0ˣ →ₜ* C[F]) (q : ℝ≥0ˣ) (η : D[F]) :
    ∃ φ : ℝ≥0ˣ → criticalTraceTestSubmodule τ,
      ∀ t x, (φ t).val.val x = diffTest(τ, t, q, η, x) := by
  choose T hT using fun t ↦ criticalTraceFormula_false_translate η (τ t)
  let f (t : ℝ≥0ˣ) : D[F] := T (t * q ^ 2) - (2 : ℂ) • T (t * q) + T t
  have hmem (t) : f t ∈ criticalTraceTestSubmodule τ := by
    refine (Submodule.mem_iInf _).mpr fun χ ↦ (Submodule.mem_iInf _).mpr fun k ↦ ?_
    let M (i : ℕ) := (criticalTraceMoment_isLinearMap (F := F) χ.val i).mk' _
    change M k.val (T (t * q ^ 2) - (2 : ℂ) • T (t * q) + T t) = 0
    rw [map_add, map_sub, map_smul]
    have hj (i r) : M i (T r) = moment[F](T r, χ.val, i) :=
      criticalTraceFormula_false_jet _ _ _
    simp only [hj, smul_eq_mul]
    have h r := criticalTraceFormula_false_translate_moments η (T r) (τ r) (hT r) χ.val (χ.property r)
    have hk := k.isLt
    rcases (show k.val = 0 ∨ k.val = 1 by omega) with hk | hk
    · rw [hk, (h _).1, (h _).1, (h _).1]
      ring
    · have hlog a b : logNorm[F](τ (a * b)) = logNorm[F](τ a) + logNorm[F](τ b) := by
        exact (congrArg (fun x ↦ logNorm[F](x)) (map_mul τ a b)).trans
          (criticalTraceFormula_false_log_mul _ _)
      rw [hk, (h _).2, (h _).2, (h _).2, sq, hlog, hlog, hlog]
      ring
  refine ⟨fun t ↦ ⟨f t, hmem t⟩, fun t x ↦ ?_⟩
  change (T (t * q ^ 2)).val x - 2 * (T (t * q)).val x + (T t).val x = _
  rw [hT, hT, hT]

local notation "Gauss" => CyclotomicField 4 ℚ
local notation "gaussianPole(" φ ", " s ")" =>
  (∫ g : C[Gauss], (φ : D[Gauss]).val g * ideleClassNormTwist (1 : PontryaginDual C[Gauss]) s g
    ∂ideleClassTamagawaMeasure Gauss)
local notation "step₄" => (Units.mk0 (4 : ℝ≥0) (by norm_num))
local notation "finiteData[" F "]" =>
  ((v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "localSum[" F "](" a ", " b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑' v : HeightOneSpectrum (𝓞 F), (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v 1 (b v))

/-- Paper: Definition A.3.2.1, p. 560. The norm-one Gaussian idele classes have
Tamagawa volume π/4. The discriminant is −4, the class number and regulator
are one, and there are four roots of unity. -/
private theorem criticalTraceFormula_false_gaussian_volume :
    (normOneIdeleClassTamagawaMeasure Gauss univ).toReal = Real.pi / 4 := by
  have hK : IsCyclotomicExtension {4} ℚ Gauss := CyclotomicField.isCyclotomicExtension 4 ℚ
  have : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ Gauss := hK
  have hdisc : NumberField.discr Gauss = -4 := by
    simpa using IsCyclotomicExtension.Rat.discr_prime_pow_succ 2 1 Gauss
  have hreal : InfinitePlace.nrRealPlaces Gauss = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) _ (by decide)
  have hcomplex : InfinitePlace.nrComplexPlaces Gauss = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4)]
    decide
  have hclass : NumberField.classNumber Gauss = 1 := by
    apply NumberField.classNumber_eq_one_iff.mpr
    apply NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    rw [hdisc, IsCyclotomicExtension.Rat.finrank 4 Gauss, hcomplex]
    norm_num [show Nat.totient 4 = 2 by decide, Nat.factorial]
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
  have htorsion : NumberField.Units.torsionOrder Gauss = 4 := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 4)]
    decide
  have hreg : NumberField.Units.regulator Gauss = 1 := by
    have hc : Fintype.card (InfinitePlace Gauss) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hreal, hcomplex]
    have hall := Fintype.card_le_one_iff.mp hc.le
    classical
    rw [NumberField.Units.regulator_eq_det', Matrix.det_eq_one_of_card_eq_zero
      (Fintype.card_eq_zero_iff.mpr ⟨fun w ↦ w.2 (hall _ _)⟩), abs_one]
  rw [normOneIdeleClassTamagawaMeasure_volume, hdisc, hreal, hcomplex, hclass, htorsion, hreg]
  norm_num [show Real.sqrt 4 = 2 from
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi / 4)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

attribute [local instance] instInfiniteCompletionMeasurableSec4b in
private theorem criticalTraceFormula_false_complex_bound_integrable {F : Type} [Field F]
    [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex) :
    Integrable (fun x : w.Completion ↦ ((1 + ‖x‖) ^ 3)⁻¹)
      (infiniteLocalAdditiveTamagawaMeasure F w) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : infiniteLocalAdditiveTamagawaMeasure F w = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hn (z : ℂ) : ‖m z‖ = ‖z‖ := by
    change ‖j.symm z‖ = ‖z‖
    rw [← dist_zero_right, ← dist_zero_right z, ← j.symm.dist_eq z 0,
      show j.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm]
  have hi : Integrable (fun z : ℂ ↦ ((1 + ‖z‖) ^ 3)⁻¹) volume := by
    have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := 3) (by norm_num)
    refine h.congr (.of_forall fun z ↦ ?_)
    change (1 + ‖z‖) ^ (-(3 : ℝ)) = _
    rw [Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hμ, integrable_map_equiv]
  simp only [Function.comp_def, hn, two_smul]
  exact hi.add_measure hi

/-- Uniform pointwise bound for the complex finite-part kernel away from the identity. -/
private theorem criticalTraceFormula_false_kernel_bound {r y M v : ℝ}
    (hM : 0 ≤ M) (hv : v ≤ M) (hy : 3 < y)
    (h₁ : y ≤ 1 + r) (h₂ : r ≤ 1 + y) :
    v / y / r ^ 2 ≤ 8 * M * ((1 + r) ^ 3)⁻¹ := by
  have hr' : 0 < r := by linarith
  have hy' : 0 < y := by linarith
  have h3 : (1 + r) ^ 3 ≤ 8 * (y * r ^ 2) := calc
    _ = (1 + r) * ((1 + r) * (1 + r)) := by ring
    _ ≤ (2 * y) * ((2 * r) * (2 * r)) :=
      mul_le_mul (by linarith) (mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = _ := by ring
  rw [← div_eq_mul_inv, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  exact (mul_le_mul_of_nonneg_right hv (by positivity)).trans (by
    calc M * (1 + r) ^ 3 ≤ M * (8 * (y * r ^ 2)) := mul_le_mul_of_nonneg_left h3 hM
         _ = _ := by ring)

attribute [local instance] instInfiniteCompletionMeasurableSec4b in
private theorem criticalTraceFormula_false_complex_bound {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, ∀ f : BruhatCompactSupport w.Completionˣ,
      (∀ u, ‖f.val u‖ ≤ M) → (∀ u : w.Completionˣ, ‖u.val‖ ≤ 3 → f.val u = 0) →
      ‖infiniteConnesWeilPrincipalValue w f‖ ≤ C := by
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let bound (x : w.Completion) : ℝ := 8 * M * ((1 + ‖x‖) ^ 3)⁻¹
  have hint : Integrable bound μ := (criticalTraceFormula_false_complex_bound_integrable w hw).const_mul _
  let c : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  refine ⟨(∫ x, bound x ∂μ) / ‖c‖, fun f hf hzero ↦ ?_⟩
  let A := (exists_infiniteWeilTestMap w).choose f
  let h (x : w.Completion) := A (Multiplicative.ofAdd x)
  let kernel (x : w.Completion) := h x / ((‖x‖ ^ 2 : ℝ) : ℂ)
  let ext := Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ 0)
  have hA (x : w.Completion) : h x = ext (1 + x) / (‖1 + x‖ : ℂ) := by
    have hx := (exists_infiniteWeilTestMap w).choose_spec f x
    change A (Multiplicative.ofAdd x) = ext (1 + x) / (‖1 + x‖ : ℂ)
    change A (Multiplicative.ofAdd x) = ext (1 + x) / (Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ) at hx
    rw [hw.mult_eq_two, Real.sqrt_sq (norm_nonneg _)] at hx
    exact hx
  have hext (x : w.Completion) (hx : x ≠ 0) :
      ext x = f.val (Units.mk0 x hx) := Units.val_injective.extend_apply _ _ (Units.mk0 x hx)
  have hext0 : ext 0 = 0 := by
    exact Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ u.ne_zero hu)
  have hsmall (x : w.Completion) (hx : ‖1 + x‖ ≤ 3) : h x = 0 := by
    rw [hA]
    by_cases h : 1 + x = 0
    · rw [h, hext0, zero_div]
    · rw [hext _ h, hzero _ hx, zero_div]
  have h0 : h 0 = 0 := hsmall 0 (by simp)
  have hk (x : w.Completion) : ‖kernel x‖ ≤ bound x := by
    by_cases hsmall' : ‖1 + x‖ ≤ 3
    · simp only [kernel, hsmall x hsmall', zero_div, norm_zero]
      dsimp only [bound]; positivity
    have hy : 3 < ‖1 + x‖ := lt_of_not_ge hsmall'
    have hne : 1 + x ≠ 0 := norm_ne_zero_iff.mp (by linarith)
    simp only [kernel, hA, hext _ hne, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), abs_of_nonneg (sq_nonneg ‖x‖)]
    refine criticalTraceFormula_false_kernel_bound hM (hf _) hy ?_ ?_
    · simpa using norm_add_le (1 : w.Completion) x
    · simpa only [add_sub_cancel_left, norm_one, add_comm (1 : ℝ)] using norm_sub_le (1 + x) (1 : w.Completion)
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec A).2
  have hL := (complexLogFourier_finitePart w hw A).2.2
  change infiniteConnesWeilPrincipalValue w f = _ at hT
  change Filter.Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2}, kernel x ∂μ) +
    c * h 0 * (Real.log ε : ℂ)) _ (nhds (-c * (_ + _ * h 0))) at hL
  simp only [h0, mul_zero, zero_mul, add_zero] at hL
  have he : (∫ x, kernel x ∂μ) = c * infiniteConnesWeilPrincipalValue w f := by
    rw [hT, mul_neg, ← neg_mul]
    refine tendsto_nhds_unique ?_ hL
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hr : ‖x‖ ^ 2 < ε := lt_of_not_ge hx
    have h1 : ‖1 + x‖ ≤ 3 := by
      have := norm_add_le (1 : w.Completion) x
      rw [norm_one] at this
      have hlt : ‖x‖ < 1 := by
        by_contra! hn
        nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hn]
      linarith
    simp [kernel, hsmall x h1]
  apply (le_div_iff₀ (norm_pos_iff.mpr hc)).mpr
  rw [mul_comm, ← norm_mul, ← he]
  exact norm_integral_le_of_norm_le hint (.of_forall hk)

/-- For any compact test, the rescaled complex contribution vanishes under the
translations of norm 4ⁿ. Eventually its local test vanishes on the ball of radius three. -/
private theorem criticalTraceFormula_false_complex_tendsto {F : Type} [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F)) (φ : D[F])
    (w : InfinitePlace F) (hw : w.IsComplex) (a : ℕ → BruhatCompactSupport w.Completionˣ)
    (ha : ∀ n u, (a n).val u =
      φ.val ((τ (step₄ ^ n))⁻¹ * IdeleClassGroup.ofCompletion (𝓞 F) F w u)) :
    Filter.Tendsto (fun n ↦ (2 : ℂ)⁻¹ ^ n * infiniteConnesWeilPrincipalValue w (a n))
      Filter.atTop (nhds 0) := by
  let ν (g : C[F]) : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hν : Continuous ν := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  let K := insert (1 : C[F]) (tsupport φ.val)
  have hK : IsCompact K := φ.property.2.insert 1
  obtain ⟨lo, _, hlo⟩ := hK.exists_isMinOn (insert_nonempty _ _) hν.continuousOn
  obtain ⟨hi, _, hhi⟩ := hK.exists_isMaxOn (insert_nonempty _ _) hc.norm.continuousOn
  have hM (g) : ‖φ.val g‖ ≤ ‖φ.val hi‖ := by
    by_cases h : φ.val g = 0
    · simp [h]
    · exact isMaxOn_iff.mp hhi g (Or.inr (subset_tsupport _ (mem_support.mpr h)))
  have hm : 0 < ν lo := NNReal.coe_pos.mpr (Units.zero_lt _)
  obtain ⟨C, hC⟩ := criticalTraceFormula_false_complex_bound w hw (norm_nonneg (φ.val hi))
  have h₄ : Filter.Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hr : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  apply squeeze_zero_norm' (a := fun n ↦ (2 : ℝ)⁻¹ ^ n * C) _ (by simpa using hr.mul_const C)
  filter_upwards [(h₄.atTop_mul_const hm).eventually_gt_atTop 9] with n hn
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_ofNat]
  refine mul_le_mul_of_nonneg_left (hC _ (fun u ↦ (ha n u) ▸ hM _) fun u hu ↦ ?_) (by positivity)
  rw [ha]
  by_contra hne
  let g := (τ (step₄ ^ n))⁻¹ * IdeleClassGroup.ofCompletion (𝓞 F) F w u
  have hg : ν lo ≤ ν g := isMinOn_iff.mp hlo g (Or.inr (subset_tsupport _ (mem_support.mpr hne)))
  have hνg : ν g = (‖u.val‖ ^ 2) / (4 : ℝ) ^ n := by
    dsimp only [ν, g]
    rw [map_mul, map_inv, hτ, ideleClassNorm_ofCompletion, hw.mult_eq_two]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.coe_map,
      NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, Units.val_mk0, div_eq_inv_mul]
    rfl
  rw [hνg, le_div_iff₀ (by positivity)] at hg
  have hu' : ‖u.val‖ ^ 2 ≤ 9 := by nlinarith [mul_self_le_mul_self (norm_nonneg u.val) hu]
  change 9 < 4 ^ n * ν lo at hn
  linarith [mul_comm (ν lo) ((4 : ℝ) ^ n)]

local notation "splitShells(" f ", " n ")" =>
  ((2 : ℂ) * ((∑' k : ℕ, (ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) k : ℂ) *
    f ((k : ℝ) / (4 : ℝ) ^ (n : ℕ))) / (4 : ℂ) ^ (n : ℕ)))

open ArithmeticFunction.vonMangoldt in
open scoped ContDiff in
/-- The unramified Gaussian shell weights have mean one. The residue class
one modulo four has von Mangoldt density one half, and its multiplicity is two. -/
private theorem criticalTraceFormula_false_smoothed_shells
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    Filter.Tendsto (fun n : ℕ ↦ splitShells(f, n)) Filter.atTop (nhds (∫ y in Ioi 0, f y)) := by
  let a : ZMod 4 := 1
  have ha : IsUnit a := isUnit_one
  have h := WienerIkehara.tendsto_sum_div_smooth (f := residueClass a)
    (A := ((Nat.totient 4 : ℕ) : ℝ)⁻¹) (C := Real.log 4 + 4) (G := LFunctionResidueClassAux a)
    (fun N ↦ (Finset.sum_le_sum fun i _ ↦ residueClass_le a i).trans (Chebyshev.sum_range_vonMangoldt_le N))
    (continuousOn_LFunctionResidueClassAux a)
    (fun s hs ↦ by rw [eqOn_LFunctionResidueClassAux ha hs]; push_cast; ring)
    (residueClass_nonneg a) hf hc hpos
  have h₄ : Filter.Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h' := (h.comp h₄).const_mul (2 : ℂ)
  simpa [Function.comp_def, a, show Nat.totient 4 = 2 by decide, ← mul_assoc] using h'

local notation "ν(" x ")" => (((ideleClassNorm Gauss x).val : ℝ))
local notation "radial(" w ", " x ")" => ((Real.sqrt ν(x) : ℂ) * w ν(x))

/-- A compact positive-axis profile gives a smooth radial test with its square-root
norm factor. Its positive polar moment is the volume times the integral of the profile. -/
private theorem criticalTraceFormula_false_radial (w : ℝ → ℂ) (hw : ContDiff ℝ ∞ w)
    (hs : HasCompactSupport w) (hpos : tsupport w ⊆ Ioi 0) :
    ∃ φ : D[Gauss], (∀ x, φ.val x = radial(w, x)) ∧
      gaussianPole(φ, 1 / 2) = (((normOneIdeleClassTamagawaMeasure Gauss univ).toReal : ℝ) : ℂ) *
        ∫ y in Ioi 0, w y := by
  let H (x : ℝ) : ℂ := ((Real.exp (x / 2) : ℝ) : ℂ) * w (Real.exp x)
  have hH : ContDiff ℝ ∞ H := (Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_id.div_const 2))).mul (hw.comp Real.contDiff_exp)
  have hS : HasCompactSupport (w ∘ Real.exp) := by
    apply HasCompactSupport.intro (hs.image_of_continuousOn (Real.continuousOn_log.mono
      (fun x hx ↦ (mem_Ioi.mp (hpos hx)).ne')))
    intro x hx
    change w (Real.exp x) = 0
    exact image_eq_zero_of_notMem_tsupport fun h ↦ hx ⟨_, h, Real.log_exp _⟩
  obtain ⟨φ, hφ⟩ := exists_normTest (F := Gauss) H hH (hS.mul_left : HasCompactSupport H)
  have hroot (x : ℝ) (hx : 0 < x) : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  refine ⟨φ, fun x ↦ ?_, ?_⟩
  · rw [hφ]
    have hx : 0 < ν(x) := NNReal.coe_pos.mpr (Units.zero_lt _)
    simp only [H, hroot _ hx, Real.exp_log hx]
  · have hm := normTest_mellin H hH.continuous φ hφ (1 : PontryaginDual C[Gauss]) (1 / 2)
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ,
      PontryaginDual.one_apply, implies_true, ite_true, Circle.coe_one, mul_one] at hm
    refine hm.trans (congrArg (_ * ·) ?_)
    have hi := grh_shift_integral H hH.continuous (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 (1 / 2)
    simp only [sub_zero, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hi
    refine hi.trans ((integral_congr_ae (.of_forall fun x ↦ ?_)).trans (integral_comp_exp w))
    change ((Real.exp (x / 2) : ℝ) : ℂ) * w (Real.exp x) * Complex.exp (1 / 2 * x) = _
    rw [show (1 / 2 : ℂ) * x = ((x / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
      Algebra.smul_def]
    change _ = ((Real.exp x : ℝ) : ℂ) * w (Real.exp x)
    rw [mul_right_comm, ← Complex.ofReal_mul, ← Real.exp_add, add_halves]

/-- A second difference of a single compact bump produces a profile of nonzero
integral. Its supports lie in [1,48], well away from the singular local shell. -/
private theorem criticalTraceFormula_false_radial_difference (τ : ℝ≥0ˣ →ₜ* C[Gauss])
    (hτ : RightInverse τ (ideleClassNorm Gauss)) :
    ∃ (η φ : D[Gauss]) (w : ℝ → ℂ), (∀ x, φ.val x = diffTest(τ, 1, step₄, η, x)) ∧
      (∀ x, φ.val x = radial(w, x)) ∧ ContDiff ℝ ∞ w ∧
      HasCompactSupport w ∧ tsupport w ⊆ Icc 1 48 ∧ (∫ y in Ioi 0, w y) ≠ 0 ∧
      gaussianPole(φ, 1 / 2) =
        (((normOneIdeleClassTamagawaMeasure Gauss univ).toReal : ℝ) : ℂ) * ∫ y in Ioi 0, w y := by
  let β : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let B (x : ℝ) : ℂ := (β x : ℂ)
  let w (x : ℝ) : ℂ := (1 / 4) * B ((1 / 16) * x) - B ((1 / 4) * x) + B x
  have hB : ContDiff ℝ ∞ B := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hS : HasCompactSupport B := β.hasCompactSupport.comp_left Complex.ofReal_zero
  have hzero (x : ℝ) (hx : x < 1 ∨ 3 < x) : B x = 0 := by
    apply Complex.ofReal_eq_zero.mpr
    apply β.zero_of_le_dist
    rw [Real.dist_eq]
    change 1 ≤ |x - 2|
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hSB : tsupport B ⊆ Icc 1 3 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    exact hx (hzero x (by simpa only [mem_Icc, not_and_or, not_le] using h))
  have hBW : tsupport w ⊆ Icc 1 48 := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra h
    have hc : x < 1 ∨ 48 < x := by simpa only [mem_Icc, not_and_or, not_le] using h
    have h₁ : B (1 / 16 * x) = 0 := hzero _ (hc.imp (by intro; linarith) (by intro; linarith))
    have h₂ : B (1 / 4 * x) = 0 := hzero _ (hc.imp (by intro; linarith) (by intro; linarith))
    have h₃ : B x = 0 := hzero _ (hc.imp id (by intro; linarith))
    exact hx (by simp only [w, h₁, h₂, h₃, mul_zero, sub_zero, add_zero])
  have hW : ContDiff ℝ ∞ w :=
    ((contDiff_const.mul (hB.comp (contDiff_const.mul contDiff_id))).sub
      (hB.comp (contDiff_const.mul contDiff_id))).add hB
  have hWS : HasCompactSupport w := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hBW
  have hWP : tsupport w ⊆ Ioi 0 := fun x hx ↦ lt_of_lt_of_le zero_lt_one (hBW hx).1
  obtain ⟨η, hη, _⟩ := criticalTraceFormula_false_radial B hB hS
    (fun x hx ↦ lt_of_lt_of_le zero_lt_one (hSB hx).1)
  obtain ⟨φ, hφ, hP⟩ := criticalTraceFormula_false_radial w hW hWS hWP
  refine ⟨η, φ, w, fun x ↦ ?_, hφ, hW, hWS, hBW, ?_, hP⟩
  · have hnorm (t : ℝ≥0ˣ) : ν((τ t)⁻¹ * x) = ν(x) / (t.val : ℝ) := by
      rw [map_mul, map_inv, hτ, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul,
        NNReal.coe_inv, div_eq_inv_mul]
    have hx : 0 ≤ ν(x) := NNReal.coe_nonneg _
    simp only [hφ, hη, hnorm, one_mul, Units.val_pow_eq_pow_val, NNReal.coe_pow,
      Units.val_mk0, NNReal.coe_ofNat, Units.val_one, NNReal.coe_one, div_one]
    have h₄ : Real.sqrt (4 : ℝ) = 2 := (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
    have h₁₆ : Real.sqrt (16 : ℝ) = 4 := (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
    norm_num [w, Real.sqrt_div hx, h₄, h₁₆, div_eq_inv_mul]
    ring
  · have hI : ∫ y in Ioi (0 : ℝ), w y = ∫ y, w y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hWP h)
    let D (a : ℝ) (x : ℝ) := B (a * x)
    have hD (a : ℝ) (ha : a ≠ 0) : Integrable (D a) := by
      have hcont : Continuous (D a) := hB.continuous.comp (continuous_const.mul continuous_id)
      have hcompact : HasCompactSupport (D a) := hS.comp_smul (c := a) ha
      exact hcont.integrable_of_hasCompactSupport hcompact
    have hset : (∫ y, w y) = ∫ y, B y := by
      change (∫ y, (1 / 4 : ℂ) * D (1 / 16) y - D (1 / 4) y + B y) = _
      have h₁ := (hD (1 / 16) (by norm_num)).const_mul (1 / 4 : ℂ)
      have h₂ := hD (1 / 4) (by norm_num)
      rw [integral_add (f := fun y ↦ (1 / 4 : ℂ) * D (1 / 16) y - D (1 / 4) y)
        (h₁.sub h₂) (hB.continuous.integrable_of_hasCompactSupport hS),
        integral_sub h₁ h₂, integral_const_mul]
      simp only [D, Measure.integral_comp_mul_left]
      norm_num [Algebra.smul_def]
      ring
    rw [hI, hset, show (∫ y, B y) = ((∫ y, β y : ℝ) : ℂ) from integral_ofReal]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (β.integral_pos (μ := volume)))

attribute [local instance] instFiniteCompletionUnitsMeasurableSec4b instFiniteCompletionMeasurableSec4b

local notation "mass(" F ", " v ")" =>
  (((finiteLocalMultiplicativeTamagawaMeasure F v (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℝ) : ℂ)

/-- All multiplicative shells are translates of the integer units, and hence have equal mass. -/
private theorem criticalTraceFormula_false_shell_measure {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
    finiteLocalMultiplicativeTamagawaMeasure F v {u : (v.adicCompletion F)ˣ | ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ k} =
      finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units := by
  classical
  let K := v.adicCompletion F
  let q : ℝ := v.asIdeal.absNorm
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U := (v.adicCompletionIntegers F).units
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let a : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹ ^ k
  have hq : 0 < q := by dsimp [q]; exact_mod_cast (Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm v))
  have ha : ‖a.val‖ = q ^ k := by
    rw [show a.val = ((π : K)⁻¹) ^ k by rfl, norm_pow, norm_inv, norm_uniformizer_adicCompletion v _ hπ, inv_inv]
  have hU (u : Kˣ) : u ∈ U ↔ ‖u.val‖ = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.trans
      Valued.toNormedField.norm_eq_one_iff.symm
  let S := {u : Kˣ | ‖u.val‖ = q ^ k}
  have he : (fun u : Kˣ ↦ a * u) ⁻¹' S = (U : Set Kˣ) := by
    ext u
    change ‖(a * u).val‖ = q ^ k ↔ u ∈ U
    rw [Units.val_mul, norm_mul, ha, hU]
    exact ⟨fun h ↦ mul_left_cancel₀ (pow_ne_zero k hq.ne') (h.trans (mul_one _).symm),
      fun h ↦ by rw [h, mul_one]⟩
  exact (measure_preimage_mul μ a S).symm.trans (congrArg μ he)

/-- Norms on a completion at a finite place are integral powers of the residue cardinality.
A copy of the private lemma of the same name in `AppA_AlgebraicNT/Sec3.lean`. -/
private theorem norm_adicCompletion_eq_zpow (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {z : v.adicCompletion F} (hz : z ≠ 0) :
    ‖z‖ = (v.asIdeal.absNorm : ℝ) ^ (WithZero.log (Valued.v z)) := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ((Valuation.ne_zero_iff _).mpr hz)]
  push_cast
  rfl

private theorem criticalTraceFormula_false_exists_shell {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) (hu : 1 < ‖u.val‖) :
    ∃ k : ℕ, ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ (k + 1) := by
  let j : ℤ := WithZero.log (Valued.v u.val)
  have hn : ‖u.val‖ = (v.asIdeal.absNorm : ℝ) ^ j := norm_adicCompletion_eq_zpow F v u.ne_zero
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hj : 0 < j := (zpow_lt_zpow_iff_right₀ hq).mp (by simpa [← hn] using hu)
  refine ⟨j.toNat - 1, hn.trans ?_⟩
  rw [← zpow_natCast]
  congr 1
  omega

/-- Integration of a radial compact cutoff supported on norms above one is a
finite sum over the positive powers of the residue cardinality. -/
private theorem criticalTraceFormula_false_radial_shells {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (w : ℝ → ℂ) (hs : HasCompactSupport w)
    (hlo : ∀ y ≤ 1, w y = 0) :
    (∫ u : (v.adicCompletion F)ˣ, w ‖u.val‖ ∂finiteLocalMultiplicativeTamagawaMeasure F v) =
      mass(F, v) * ∑' k : ℕ, w ((v.asIdeal.absNorm : ℝ) ^ (k + 1)) := by
  classical
  let K := v.adicCompletion F
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨R, hR⟩ := hs.bddAbove
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt R hq
  have hout (k : ℕ) (hk : N ≤ k) : w (q ^ (k + 1)) = 0 := by
    exact image_eq_zero_of_notMem_tsupport fun h ↦
      ((hN.trans_le (pow_le_pow_right₀ hq.le (by omega : N ≤ k + 1))).not_ge (hR h))
  let B (k : ℕ) (u : Kˣ) : ℂ := if ‖u.val‖ = q ^ (k + 1) then w (q ^ (k + 1)) else 0
  have he (u : Kˣ) : w ‖u.val‖ = ∑ k ∈ Finset.range N, B k u := by
    by_cases hu : 1 < ‖u.val‖
    · obtain ⟨j, hj⟩ := criticalTraceFormula_false_exists_shell v u hu
      change ‖u.val‖ = q ^ (j + 1) at hj
      have hne (k : ℕ) (hk : k ≠ j) : ‖u.val‖ ≠ q ^ (k + 1) := fun h ↦
        hk (by have := (pow_right_injective₀ (zero_lt_one.trans hq) hq.ne') (h.symm.trans hj); omega)
      rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [B, hne k hk])
        (fun h ↦ by simp [B, hj, hout j (by simpa using h)]), hj]
      simp [B, hj]
    · rw [hlo _ (le_of_not_gt hu)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      have hne : ‖u.val‖ ≠ q ^ (k + 1) := fun h ↦ hu (h ▸ one_lt_pow₀ hq (Nat.succ_ne_zero k))
      simp [B, hne]
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let S (k : ℕ) := {u : Kˣ | ‖u.val‖ = q ^ (k + 1)}
  have hm (k) : MeasurableSet (S k) := (isClosed_eq (continuous_norm.comp Units.continuous_val)
    continuous_const).measurableSet
  have hfin (k) : μ (S k) ≠ ⊤ := by
    rw [show μ (S k) = _ from criticalTraceFormula_false_shell_measure v (k + 1)]
    exact (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr
      (compactSpace_adicCompletionIntegers v (K := F)))).measure_lt_top.ne
  have hB (k : ℕ) : Integrable (B k) μ := by
    change Integrable ((S k).indicator (fun _ ↦ w (q ^ (k + 1)))) μ
    exact (integrable_indicator_iff (hm k)).mpr (integrableOn_const (hfin k))
  rw [show (fun u : Kˣ ↦ w ‖u.val‖) = fun u ↦ ∑ k ∈ Finset.range N, B k u from funext he,
    integral_finsetSum _ fun k _ ↦ hB k,
    tsum_eq_sum (s := Finset.range N) (fun k hk ↦ hout k (by simpa using hk)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (∫ u, (S k).indicator (fun _ ↦ _) u ∂μ) = _
  rw [integral_indicator (hm k), setIntegral_const, Complex.real_smul, measureReal_def,
    show μ (S k) = _ from criticalTraceFormula_false_shell_measure v (k + 1)]

/-- Away from the singular shell, the square-root norm in the test cancels the
denominator of the finite principal value. -/
private theorem criticalTraceFormula_false_finite_pv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (w : ℝ → ℂ) (hs : HasCompactSupport w)
    (hpos : tsupport w ⊆ Icc 1 48) (n : ℕ) (hn : n ≠ 0) (b : BruhatCompactSupport (v.adicCompletion F)ˣ)
    (hb : ∀ u : (v.adicCompletion F)ˣ, b.val u =
      (Real.sqrt (‖u.val‖ / (4 : ℝ) ^ n) : ℂ) * w (‖u.val‖ / (4 : ℝ) ^ n)) :
    finiteConnesWeilPrincipalValue v 1 b = (2 : ℂ)⁻¹ ^ n * (mass(F, v) *
      ∑' k : ℕ, w ((v.asIdeal.absNorm : ℝ) ^ (k + 1) / (4 : ℝ) ^ n)) := by
  let K := v.adicCompletion F
  let T := (4 : ℝ) ^ n
  let f (y : ℝ) := w (y / T)
  have hT : 1 < T := one_lt_pow₀ (by norm_num : (1 : ℝ) < 4) hn
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hs' : HasCompactSupport f := by simpa [f, div_eq_inv_mul] using hs.comp_smul (c := T⁻¹) (inv_ne_zero hTpos.ne')
  have hlo (y : ℝ) (hy : y ≤ 1) : f y = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := w) fun h ↦
      ((div_lt_one hTpos).mpr (hy.trans_lt hT)).not_ge (hpos h).1
  have hzero : b.val 1 = 0 := by
    rw [hb, Units.val_one, norm_one, show w (1 / (4 : ℝ) ^ n) = 0 from hlo 1 le_rfl, mul_zero]
  have hp := (finiteConnesWeilPrincipalValue_of_apply_one_zero v b hzero).2
  have hroot : Real.sqrt T = (2 : ℝ) ^ n := by
    rw [show T = ((2 : ℝ) ^ n) ^ 2 by dsimp [T]; rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      Real.sqrt_sq (by positivity)]
  rw [hp, ← criticalTraceFormula_false_radial_shells v f hs' hlo, ← integral_const_mul]
  apply integral_congr_ae (.of_forall fun u ↦ ?_)
  by_cases hu : 1 < ‖u.val‖
  · have hsub : ‖1 - u.val‖ = ‖u.val‖ := by
      rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by simpa using hu.ne : ‖(1 : K)‖ ≠ ‖-u.val‖), norm_neg, norm_one, max_eq_right hu.le]
    rw [hb, hsub, Real.sqrt_div (norm_nonneg _), hroot]
    have hsq : (Real.sqrt ‖u.val‖ : ℂ) ^ 2 = (‖u.val‖ : ℂ) := by
      exact_mod_cast Real.sq_sqrt (norm_nonneg u.val)
    change _ = (2 : ℂ)⁻¹ ^ n * w _
    push_cast
    rw [inv_pow]
    field_simp [show (‖u.val‖ : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero)]
    linear_combination w (‖u.val‖ / (4 : ℝ) ^ n) * hsq
  · rw [hb, show w (‖u.val‖ / (4 : ℝ) ^ n) = 0 from hlo _ (le_of_not_gt hu)]
    simp [f, hlo _ (le_of_not_gt hu)]
/-- The fiber above an odd rational prime has total logarithmic weight twice the prime
logarithm exactly when the rational power is one modulo four. -/
private theorem criticalTraceFormula_false_odd_shell (p k : ℕ) (hp : p.Prime) (hodd : ¬ p ∣ 4) :
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    (∑' Q : P.primesOver (𝓞 Gauss),
      if Q.val.inertiaDeg ℤ ∣ k then Real.log (Q.val.absNorm : ℝ) else 0) =
      if (p : ZMod 4) ^ k = 1 then 2 * Real.log p else 0 := by
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP0 : P ≠ ⊥ := by simpa [P] using hp.ne_zero
  have : P.IsPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).2
    (Int.prime_iff_natAbs_prime.mpr (by simpa using hp))
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  let : Fintype (P.primesOver (𝓞 Gauss)) := (IsDedekindDomain.primesOver_finite P (𝓞 Gauss)).fintype
  let f := orderOf (p : ZMod 4)
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclotomicExtension {4} ℚ Gauss := CyclotomicField.isCyclotomicExtension 4 ℚ
  have hf (Q : P.primesOver (𝓞 Gauss)) : Q.val.inertiaDeg ℤ = f := by
    have := Q.property.1
    have := Q.property.2
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p Gauss Q.val hodd
  have he (Q : P.primesOver (𝓞 Gauss)) : Q.val.ramificationIdx ℤ = 1 := by
    have := Q.property.1
    have := Q.property.2
    exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p Gauss Q.val hodd
  have hcard : Fintype.card (P.primesOver (𝓞 Gauss)) * f = 2 := by
    have h := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 Gauss)
    simpa only [he, hf, one_mul, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      RingOfIntegers.rank, IsCyclotomicExtension.Rat.finrank 4 Gauss,
      show Nat.totient 4 = 2 by decide] using h
  have hlog (Q : P.primesOver (𝓞 Gauss)) : Real.log (Q.val.absNorm : ℝ) = f * Real.log p := by
    have := Q.property.1
    have := Q.property.2
    have hn : Q.val.absNorm = p ^ f := by
      rw [← Ideal.absNorm_pow_inertiaDeg P Q.val, hf Q]
      simp [P]
    rw [hn, Nat.cast_pow, Real.log_pow]
  change (∑' Q : P.primesOver (𝓞 Gauss), _) = _
  rw [tsum_fintype]
  by_cases h : f ∣ k
  · simp only [hf, h, ite_true, hlog, orderOf_dvd_iff_pow_eq_one.mp h,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, hcard]
    norm_num
  · have hn : (p : ZMod 4) ^ k ≠ 1 := fun hk ↦ h (orderOf_dvd_iff_pow_eq_one.mpr hk)
    simp [hf, h, hn]

local notation "oddShellWeight(" m ")" =>
  (if IsPrimePow (m : ℕ) ∧ (m : ℕ).minFac ≠ 2 then
    ∑' Q : (Ideal.span {((m : ℕ).minFac : ℤ)}).primesOver (𝓞 Gauss),
      if Q.val.inertiaDeg ℤ ∣ (m : ℕ).factorization (m : ℕ).minFac
        then Real.log (Q.val.absNorm : ℝ) else 0
  else (0 : ℝ))

/-- The weights of all unramified prime-ideal powers over a rational integer are
twice the rational von Mangoldt weight in the class one modulo four. -/
private theorem criticalTraceFormula_false_odd_weight (m : ℕ) :
    oddShellWeight(m) = 2 * ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 4) m := by
  classical
  simp only [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply, mem_ofPred_eq,
    ArithmeticFunction.vonMangoldt_apply]
  by_cases hm : IsPrimePow m
  · have hp : m.minFac.Prime := Nat.minFac_prime hm.ne_one
    by_cases htwo : m.minFac = 2
    · have hdiv : 2 ∣ m := htwo ▸ Nat.minFac_dvd m
      have hmod : (m : ZMod 4) ≠ 1 := by
        obtain ⟨d, rfl⟩ := hdiv
        intro h
        have h' := (ZMod.natCast_eq_natCast_iff' (2 * d) 1 4).mp (by simpa using h)
        omega
      simp [htwo, hmod]
    · have hodd : ¬ m.minFac ∣ 4 := fun h ↦ htwo
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show m.minFac ∣ 2 ^ 2 by simpa using h)))
      rw [ite_eq_left (And.intro hm htwo), ite_eq_left hm]
      rw [criticalTraceFormula_false_odd_shell _ _ hp hodd]
      have he : (m.minFac : ZMod 4) ^ m.factorization m.minFac = (m : ZMod 4) := by
        exact_mod_cast congrArg (fun x : ℕ ↦ (x : ZMod 4)) hm.minFac_pow_factorization_eq
      rw [he]
      split_ifs <;> ring
  · simp [hm]

/-- Any fixed prime contributes a vanishing error after normalization.
Only linearly many powers can occur below the translated support. -/
private theorem criticalTraceFormula_false_prime_powers (q : ℝ) (hq : 2 ≤ q) (w : ℝ → ℂ) (hw : Continuous w)
    (hs : HasCompactSupport w) :
    Filter.Tendsto (fun n : ℕ ↦
      (∑' k : ℕ, w (q ^ (k + 1) / (4 : ℝ) ^ n)) / (4 : ℂ) ^ n)
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨R, hR⟩ := hs.bddAbove
  obtain ⟨K, hK⟩ := exists_nat_gt R
  have hKR : R < (2 : ℝ) ^ K := hK.trans_le (by exact_mod_cast Nat.lt_two_pow_self.le)
  obtain ⟨M, _, hM⟩ := (hs.insert 0).exists_isMaxOn (insert_nonempty _ _) hw.norm.continuousOn
  have hb x : ‖w x‖ ≤ ‖w M‖ := by
    by_cases hx : w x = 0
    · simp [hx]
    · exact isMaxOn_iff.mp hM x (Or.inr (subset_tsupport _ (mem_support.mpr hx)))
  have htr (n k : ℕ) (hk : 2 * n + K ≤ k) :
      w (q ^ (k + 1) / (4 : ℝ) ^ n) = 0 := by
    by_contra! h
    have hr := hR (subset_tsupport _ (mem_support.mpr h))
    have hpow : (2 : ℝ) ^ K * (4 : ℝ) ^ n ≤ 2 ^ (k + 1) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact (not_lt_of_ge hr) (hKR.trans_le ((le_div_iff₀ (by positivity)).mpr
      (hpow.trans (pow_le_pow_left₀ (by norm_num) hq _))))
  have hnr := tendsto_self_mul_const_pow_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (4 : ℝ)⁻¹) (by norm_num) (by norm_num)
  have hlim := (((hnr.const_mul 2).add (hr.const_mul (K : ℝ))).mul_const ‖w M‖)
  simp only [mul_zero, add_zero, zero_mul] at hlim
  refine squeeze_zero_norm (a := fun n : ℕ ↦ (2 * n + K : ℕ) * ‖w M‖ / (4 : ℝ) ^ n) ?_ ?_
  · intro n
    rw [tsum_eq_sum (s := Finset.range (2 * n + K)) (fun k hk ↦ htr n k (by simpa using hk)),
      norm_div, norm_pow, Complex.norm_ofNat]
    gcongr
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ ↦ hb _).trans_eq (by simp))
  · refine hlim.congr fun n ↦ ?_
    push_cast
    rw [inv_pow, div_eq_mul_inv]
    ring

local notation "powers(" v ", " w ", " n ")" =>
  (∑' k : ℕ, w (((Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℕ) : ℝ) ^ (k + 1) / (4 : ℝ) ^ (n : ℕ)))

section
open scoped Classical

local notation "Vg" => HeightOneSpectrum (𝓞 Gauss)
local notation "qv(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "occurs(" v ", " m ")" => (∃ k : ℕ, qv(v) ^ (k + 1) = (m : ℕ))

private theorem criticalTraceFormula_false_norm_prime (v : Vg) :
    IsPrimePow qv(v) ∧ (qv(v).minFac : 𝓞 Gauss) ∈ v.asIdeal := by
  obtain ⟨p, k, hk, hmem, hp, he⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  rw [he, hp.pow_minFac hk.ne']
  exact ⟨⟨p, k, hp.prime, hk, rfl⟩, hmem⟩

private theorem criticalTraceFormula_false_fiber_weight (m : ℕ) :
    (∑' v : Vg, if qv(v).minFac ≠ 2 ∧ occurs(v, m) then Real.log (qv(v) : ℝ) else 0) =
      oddShellWeight(m) := by
  classical
  have hh (v : Vg) (h : occurs(v, m)) : IsPrimePow m ∧ m.minFac = qv(v).minFac := by
    obtain ⟨k, rfl⟩ := h
    exact ⟨(isPrimePow_pow_iff (Nat.succ_ne_zero k)).mpr (criticalTraceFormula_false_norm_prime v).1,
      Nat.pow_minFac (Nat.succ_ne_zero k)⟩
  by_cases good : IsPrimePow m ∧ m.minFac ≠ 2
  · rw [ite_eq_left good]
    let p := m.minFac
    let e := m.factorization p
    let P : Ideal ℤ := Ideal.span {(p : ℤ)}
    have hp : p.Prime := Nat.minFac_prime good.1.ne_one
    have hP0 : P ≠ ⊥ := by simpa [P] using hp.ne_zero
    have : P.IsPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero)).2
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hp))
    have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    have hpowe : p ^ e = m := good.1.minFac_pow_factorization_eq
    have he : 0 < e := by
      by_contra! h
      exact good.1.ne_one (by rw [← hpowe, Nat.eq_zero_of_le_zero h, pow_zero])
    let I := {v : Vg | v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 Gauss)) P}
    let E : I ≃ P.primesOver (𝓞 Gauss) := HeightOneSpectrum.equivPrimesOver _ hP0
    let a (v : Vg) : ℝ := if qv(v).minFac ≠ 2 ∧ occurs(v, m) then Real.log (qv(v) : ℝ) else 0
    have hsupp : support a ⊆ I := by
      intro v hv
      have hv' : qv(v).minFac ≠ 2 ∧ occurs(v, m) := by
        by_contra h
        exact hv (ite_eq_right h)
      have hmem : (p : 𝓞 Gauss) ∈ v.asIdeal := by
        change (m.minFac : 𝓞 Gauss) ∈ v.asIdeal
        rw [(hh v hv'.2).2]
        exact (criticalTraceFormula_false_norm_prime v).2
      change v.asIdeal ∣ Ideal.map (algebraMap ℤ (𝓞 Gauss)) P
      rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      simpa [P] using hmem
    change (∑' v, a v) = _
    rw [← tsum_subtype_eq_of_support_subset hsupp, ← E.tsum_eq]
    apply tsum_congr
    intro V
    let v : Vg := V.val
    let Q := E V
    have hQ : Q.val = v.asIdeal := rfl
    have : Q.val.IsPrime := Q.property.1
    have : Q.val.LiesOver P := Q.property.2
    let f := Q.val.inertiaDeg ℤ
    have hnorm : qv(v) = p ^ f := by
      rw [← hQ, ← Ideal.absNorm_pow_inertiaDeg P Q.val]
      simp [P, f]
    have hf : 0 < f := by
      by_contra! h
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      rw [hnorm, Nat.eq_zero_of_le_zero h, pow_zero] at this
      omega
    have hiff : occurs(v, m) ↔ f ∣ e := by
      constructor
      · rintro ⟨k, hk⟩
        rw [hnorm, ← pow_mul, ← hpowe] at hk
        exact ⟨_, (Nat.pow_right_injective hp.two_le hk).symm⟩
      · rintro ⟨d, hd⟩
        have hdpos : d ≠ 0 := by intro h; simp [h] at hd; omega
        exact ⟨d - 1, by rw [hnorm, ← pow_mul, show d - 1 + 1 = d by omega, ← hd, hpowe]⟩
    have hpmin : qv(v).minFac ≠ 2 := by rw [hnorm, hp.pow_minFac hf.ne']; exact good.2
    change (if qv(v).minFac ≠ 2 ∧ occurs(v, m) then _ else _) =
      if f ∣ e then Real.log (Q.val.absNorm : ℝ) else 0
    by_cases hx : f ∣ e
    · rw [ite_eq_left ⟨hpmin, hiff.mpr hx⟩, ite_eq_left hx, hQ]
    · rw [ite_eq_right (fun h ↦ hx (hiff.mp h.2)), ite_eq_right hx]
  · rw [ite_eq_right good]
    calc _ = ∑' _ : Vg, (0 : ℝ) := by
           apply tsum_congr
           intro v
           exact ite_eq_right (fun h ↦ good ⟨(hh v h.2).1, fun he ↦ h.1 ((hh v h.2).2.symm.trans he)⟩)
         _ = 0 := tsum_zero

/-- Regroup a finite profile on positive powers by the resulting rational integer. -/
private theorem criticalTraceFormula_false_group_norms (W : ℕ → ℂ)
    (hW : (support W).Finite) (A : Vg → ℂ) :
    (∑' v : Vg, A v * ∑' k : ℕ, W (qv(v) ^ (k + 1))) =
    ∑' m : ℕ, (∑' v : Vg, if occurs(v, m) then A v else 0) * W m := by
  classical
  let T := hW.toFinset
  have hT (m : ℕ) (hm : m ∉ T) : W m = 0 := by
    contrapose! hm
    exact hW.mem_toFinset.mpr hm
  let B (m : ℕ) (v : Vg) : ℂ := if occurs(v, m) then A v else 0
  have hsupp (m) : (support (B m)).Finite := by
    apply (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 Gauss) m).subset
    intro v hv
    have he : occurs(v, m) := by by_contra! h; exact hv (ite_eq_right (by simpa only [not_exists] using h))
    obtain ⟨k, rfl⟩ := he
    exact Nat.le_self_pow (by omega) _
  have hp (v : Vg) : A v * (∑' k : ℕ, W (qv(v) ^ (k + 1))) =
      ∑ m ∈ T, B m v * W m := by
    let g (k : ℕ) := qv(v) ^ (k + 1)
    have hi : Injective g := fun k l h ↦ by
      have := Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) h
      omega
    let f (m : ℕ) : ℂ := if occurs(v, m) then W m else 0
    have hzero : support f ⊆ range g := by
      intro m hm
      by_contra h
      exact hm (ite_eq_right h)
    have hre : (∑' k : ℕ, W (qv(v) ^ (k + 1))) = ∑' m : ℕ, f m := by
      rw [← hi.tsum_eq hzero]
      apply tsum_congr
      intro k
      exact (ite_eq_left (show occurs(v, g k) from ⟨k, rfl⟩)).symm
    rw [hre, tsum_eq_sum (s := T) (fun m hm ↦ by simp only [f, hT m hm, ite_self]), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    by_cases h : occurs(v, m) <;> simp only [f, B, h, ite_true, ite_false, zero_mul, mul_zero]
  rw [tsum_congr hp, Summable.tsum_finsetSum (fun m _ ↦ (summable_of_hasFiniteSupport (hsupp m)).mul_right (W m)),
    tsum_eq_sum (s := T) (fun m hm ↦ by rw [hT m hm, mul_zero])]
  exact Finset.sum_congr rfl fun m _ ↦ tsum_mul_right

/-- Paper: Theorem 13.3.1.1, (13.3.1.5), p. 522. Regroup the powers of the
Gaussian prime ideals by their rational norms. The finitely many exceptional
places account for the different and the prime above two. -/
theorem criticalTraceFormula_gaussian_prime_power_regroup (w : ℝ → ℂ) (hs : HasCompactSupport w) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 Gauss))) (c : HeightOneSpectrum (𝓞 Gauss) → ℂ), ∀ n : ℕ,
      (∑' v : HeightOneSpectrum (𝓞 Gauss), (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
        (mass(Gauss, v) * powers(v, w, n))) =
        (∑' m : ℕ, ((oddShellWeight(m) : ℝ) : ℂ) * w ((m : ℝ) / (4 : ℝ) ^ n)) +
        ∑ v ∈ S, c v * powers(v, w, n) := by
  classical
  let L (v : Vg) : ℂ := ↑(Real.log (qv(v) : ℝ))
  let A (v : Vg) : ℂ := if qv(v).minFac ≠ 2 then L v else 0
  let c (v : Vg) : ℂ := L v * mass(Gauss, v) - A v
  have hmass : {v : Vg | mass(Gauss, v) ≠ 1}.Finite := by
    refine (finiteLocalTamagawaMass_finite Gauss).subset fun v hv h ↦ hv ?_
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, h, ENNReal.toReal_one, Complex.ofReal_one]
  have htwo : {v : Vg | qv(v).minFac = 2}.Finite := by
    have h := (Ring.HasFiniteQuotients.finite_setOfPred_mem (2 : 𝓞 Gauss) (by norm_num)).preimage
      (HeightOneSpectrum.asIdeal_injective (R := 𝓞 Gauss)).injOn
    refine h.subset fun v hv ↦ ?_
    have hmem := (criticalTraceFormula_false_norm_prime v).2
    change qv(v).minFac = 2 at hv
    rw [hv, Nat.cast_ofNat] at hmem
    exact hmem
  have hc : (support c).Finite := by
    apply (hmass.union htwo).subset
    intro v hv
    by_contra h
    have hM : mass(Gauss, v) = 1 := not_ne_iff.mp fun hM ↦ h (Or.inl hM)
    have hq : qv(v).minFac ≠ 2 := fun hq ↦ h (Or.inr hq)
    exact hv (by simp only [c, A, ite_eq_left hq, hM, mul_one, sub_self])
  refine ⟨hc.toFinset, c, fun n ↦ ?_⟩
  let W (m : ℕ) := w ((m : ℝ) / (4 : ℝ) ^ n)
  obtain ⟨R, hR⟩ := hs.bddAbove
  obtain ⟨M, hM⟩ := exists_nat_gt (R * (4 : ℝ) ^ n)
  have hcut (m : ℕ) (hm : M ≤ m) : W m = 0 := by
    exact image_eq_zero_of_notMem_tsupport (f := w) fun h ↦ (hM.trans_le (by exact_mod_cast hm)).not_ge
      ((div_le_iff₀ (by positivity)).mp (hR h))
  have hW : (support W).Finite := (Finset.range M).finite_toSet.subset fun m hm ↦
    Finset.mem_range.mpr (lt_of_not_ge fun h ↦ hm (hcut m h))
  let Z (v : Vg) := ∑' k : ℕ, W (qv(v) ^ (k + 1))
  have hZ (v : Vg) : Z v = powers(v, w, n) := by simp only [Z, W, Nat.cast_pow]
  have hZs : (support Z).Finite := by
    refine (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 Gauss) M).subset fun v hv ↦ ?_
    by_contra h
    have hz (k : ℕ) := hcut (qv(v) ^ (k + 1))
      ((le_of_not_ge h).trans (Nat.le_self_pow (Nat.succ_ne_zero _) _))
    exact hv (by simp only [Z, hz, tsum_zero])
  have hAZ : Summable (fun v ↦ A v * Z v) := summable_of_hasFiniteSupport
    (hZs.subset (support_mul_subset_right ..))
  have hCZ : Summable (fun v ↦ c v * Z v) := summable_of_hasFiniteSupport
    (hc.subset (support_mul_subset_left ..))
  have hcoeff (m) : (∑' v : Vg, if occurs(v, m) then A v else 0) = ((oddShellWeight(m) : ℝ) : ℂ) := by
    rw [← criticalTraceFormula_false_fiber_weight, Complex.ofReal_tsum]
    apply tsum_congr
    intro v
    by_cases h : occurs(v, m)
    · rw [ite_eq_left h]
      by_cases hq : qv(v).minFac ≠ 2
      · rw [ite_eq_left ⟨hq, h⟩]; exact ite_eq_left hq
      · rw [ite_eq_right (fun h' ↦ hq h'.1), Complex.ofReal_zero]; exact ite_eq_right hq
    · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h h'.2), Complex.ofReal_zero]
  have hregular : (∑' v : Vg, A v * Z v) =
      ∑' m : ℕ, ((oddShellWeight(m) : ℝ) : ℂ) * W m := by
    rw [show (∑' v : Vg, A v * Z v) = _ from criticalTraceFormula_false_group_norms W hW A]
    simp only [hcoeff]
  have hcorr : (∑' v : Vg, c v * Z v) = ∑ v ∈ hc.toFinset, c v * powers(v, w, n) := by
    rw [tsum_eq_sum (s := hc.toFinset) (fun v h ↦ mul_eq_zero_of_left
      (notMem_support.mp (fun hv ↦ h (hc.mem_toFinset.mpr hv))) _)]
    exact Finset.sum_congr rfl fun v _ ↦ congrArg (c v * ·) (hZ v)
  rw [← hregular, ← hcorr, ← hAZ.tsum_add hCZ]
  apply tsum_congr
  intro v
  rw [← hZ]
  change L v * (_ * _) = A v * _ + (L v * _ - A v) * _
  ring

end

open scoped ContDiff in
/-- Paper: Theorem 13.3.1.1, (13.3.1.4)–(13.3.1.5), p. 522. Over the Gaussian
field, compare the normalized finite-place terms of a translated second difference with
the rational von Mangoldt weights on prime powers congruent to one modulo four.
The cutoff has integral equal to the positive polar moment divided by the class volume.
A translated radial bump supplies the cutoff. The exceptional local unit masses
and the prime above two contribute a vanishing normalized error. -/
theorem criticalTraceFormula_gaussian_shell_comparison (τ : ℝ≥0ˣ →ₜ* C[Gauss])
    (_hτ : RightInverse τ (ideleClassNorm Gauss)) :
    ∃ (η φ : D[Gauss]) (weight : ℝ → ℂ), (∀ x, φ.val x = diffTest(τ, 1, step₄, η, x)) ∧
      gaussianPole(φ, 1 / 2) ≠ 0 ∧ ContDiff ℝ ∞ weight ∧ HasCompactSupport weight ∧
      tsupport weight ⊆ Ioi 0 ∧ (∫ y in Ioi 0, weight y) =
        gaussianPole(φ, 1 / 2) / (((normOneIdeleClassTamagawaMeasure Gauss univ).toReal : ℝ) : ℂ) ∧
      ∀ (b : ℕ → finiteData[Gauss]),
        (∀ n v u, ((b n) v).val u =
          φ.val ((τ (step₄ ^ n))⁻¹ * IdeleClassGroup.ofAdicCompletion (𝓞 Gauss) Gauss v u)) →
        Filter.Tendsto (fun n ↦ (2 : ℂ)⁻¹ ^ n *
          (∑' v : HeightOneSpectrum (𝓞 Gauss), (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
            finiteConnesWeilPrincipalValue v 1 (b n v)) -
          splitShells(weight, n)) Filter.atTop (nhds 0) := by
  obtain ⟨η, φ, w, hd, hφ, hw, hc, hpos, hI, hP⟩ := criticalTraceFormula_false_radial_difference τ _hτ
  let V : ℂ := (((normOneIdeleClassTamagawaMeasure Gauss univ).toReal : ℝ) : ℂ)
  have hV : V ≠ 0 := by
    dsimp [V]
    rw [criticalTraceFormula_false_gaussian_volume]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  refine ⟨η, φ, w, hd, hP ▸ mul_ne_zero hV hI, hw, hc, fun y hy ↦
    lt_of_lt_of_le zero_lt_one (hpos hy).1, ?_, fun b hb ↦ ?_⟩
  · rw [hP, mul_div_cancel_left₀ _ hV]
  obtain ⟨S, c, hsum⟩ := criticalTraceFormula_gaussian_prime_power_regroup w hc
  have hlim (v : HeightOneSpectrum (𝓞 Gauss)) :=
    (criticalTraceFormula_false_prime_powers (v.asIdeal.absNorm : ℝ)
        (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v) w hw.continuous hc).const_mul (c v)
  have ht := tendsto_finsetSum S (fun v _ ↦ hlim v)
  simp only [mul_zero, Finset.sum_const_zero] at ht
  refine Filter.Tendsto.congr' ?_ ht
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hp (v : HeightOneSpectrum (𝓞 Gauss)) := criticalTraceFormula_false_finite_pv v w hc hpos n hn.ne' (b n v) (by
    intro u
    rw [hb, hφ]
    have hnorm : ν((τ (step₄ ^ n))⁻¹ * IdeleClassGroup.ofAdicCompletion (𝓞 Gauss) Gauss v u) =
        ‖u.val‖ / (4 : ℝ) ^ n := by
      rw [map_mul, map_inv, _hτ, ideleClassNorm_ofAdicCompletion]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, Units.val_mk0, div_eq_inv_mul]
      rfl
    rw [hnorm])
  have hl : (2 : ℂ)⁻¹ ^ n * (∑' v : HeightOneSpectrum (𝓞 Gauss),
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 (b n v)) =
        (∑' v : HeightOneSpectrum (𝓞 Gauss), (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
        (mass(Gauss, v) * powers(v, w, n))) / (4 : ℂ) ^ n := by
    rw [← tsum_mul_left, ← tsum_div_const]
    apply tsum_congr
    intro v
    rw [hp v]
    rw [show (4 : ℂ) ^ n = ((2 : ℂ) ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num, inv_pow]
    ring
  have hr : (∑' m : ℕ, ((oddShellWeight(m) : ℝ) : ℂ) * w ((m : ℝ) / (4 : ℝ) ^ n)) / (4 : ℂ) ^ n = splitShells(w, n) := by
    rw [← mul_div_assoc, ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro m
    rw [criticalTraceFormula_false_odd_weight, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc]
  rw [hl, hsum, add_div, hr, add_sub_cancel_left, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  exact (mul_div_assoc ..).symm


private theorem criticalTraceFormula_false_polar {F : Type} [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
    (φ ψ : D[F]) (n : ℕ) (ht : ∀ g, ψ.val g = φ.val ((τ (step₄ ^ n))⁻¹ * g)) :
    mellinAt[F](ψ, 1, -1 / 2) = (2 : ℂ)⁻¹ ^ n * mellinAt[F](φ, 1, -1 / 2) ∧
    mellinAt[F](ψ, 1, 1 / 2) = (2 : ℂ) ^ n * mellinAt[F](φ, 1, 1 / 2) := by
  have hfour : (4 : ℂ) ^ (1 / 2 : ℂ) = 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_ofNat 4, ← Complex.ofReal_cpow (by norm_num : 0 ≤ (4 : ℝ)),
      ← Real.sqrt_eq_rpow, show Real.sqrt 4 = 2 from
        (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)]
    norm_num
  have he (s : ℂ) : mellinAt[F](ψ, 1, s) =
      ((4 : ℂ) ^ s) ^ n * mellinAt[F](φ, 1, s) := by
    let ξ := ideleClassNormTwist (F := F) 1 s
    have hξ : ξ (τ step₄) = (4 : ℂ) ^ s := by
      change (1 : ℂ) * (((ideleClassNorm F (τ step₄)).val : ℝ) : ℂ) ^ s = _
      rw [one_mul, hτ]
      rfl
    have hn : ξ (τ (step₄ ^ n)) = ((4 : ℂ) ^ s) ^ n := by rw [map_pow, map_pow, hξ]
    exact (criticalTraceFormula_false_mellin_translate φ ψ _ ht 1 s).trans
      (congrArg (· * mellinAt[F](φ, 1, s)) hn)
  constructor
  · simpa only [neg_div, Complex.cpow_neg, hfour] using he (-1 / 2)
  · simpa only [hfour] using he (1 / 2)

/-- After division by `2ⁿ`, the negative pole and any bounded spectral sum vanish. -/
private theorem criticalTraceFormula_false_limit (P N : ℂ) (L G : ℕ → ℂ) (B : ℝ)
    (hB : ∀ n, ‖L n‖ ≤ B)
    (hG : ∀ n, G n = (2 : ℂ)⁻¹ ^ n * N + 2 ^ n * P - L n) :
    Filter.Tendsto (fun n ↦ (2 : ℂ)⁻¹ ^ n * G n) Filter.atTop (nhds P) := by
  have hr : Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hc : Filter.Tendsto (fun n : ℕ ↦ (2 : ℂ)⁻¹ ^ n) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num [norm_inv])
  have hL : Filter.Tendsto (fun n ↦ (2 : ℂ)⁻¹ ^ n * L n) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun n ↦ (2 : ℝ)⁻¹ ^ n * B)
    · intro n
      rw [norm_mul, norm_pow, norm_inv]
      simp only [Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left (hB n) (by positivity)
    · simpa using hr.mul_const B
  have hlim := (((hc.mul hc).mul_const N).add (tendsto_const_nhds (x := P))).sub hL
  simp only [zero_mul, zero_add, sub_zero] at hlim
  refine hlim.congr fun n ↦ ?_
  have hcancel : (2 : ℂ)⁻¹ ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [hG, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hcancel, one_mul]

private theorem criticalTraceFormula_false_gaussian_degree : Module.finrank ℚ Gauss ≤ 2 := by
  have : IsCyclotomicExtension {4} ℚ Gauss := CyclotomicField.isCyclotomicExtension 4 ℚ
  rw [IsCyclotomicExtension.Rat.finrank 4 Gauss]
  decide

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. Take
`F = ℚ(i)` and the test `φ_X(g) = f(log |g|_F − X)`, where `f = b''` and
`b(u) = exp(−1 / (u(1 − u)))` for `0 < u < 1`, extended by zero. Both radial
moments vanish by integration by parts, and all nontrivial norm-one characters
vanish by orthogonality. On the critical line translation multiplies each
Mellin value by a phase, so absolute convergence bounds the capped zero sum
uniformly in `X`. Write `J = ∫ f(u) exp(u/2) du > 0`. The polar sum is
`(π/4) J exp(X/2) + O(exp(−X/2))` by the norm-one Tamagawa volume. The
archimedean term is `O(exp(−X/2))`. On each finite shell of norm `qᵐ > 1`, the
term in (13.3.1.5) before the minus sign is `log(q) · q^(−m/2) · f(m log q − X)`
times the integer-unit mass. That mass is one off the prime above two, whose
contribution is `O(exp(−X/2))`. The prime ideal theorem and partial summation
give `J exp(X/2) + o(exp(X/2))` for the finite sum. Thus the printed right side
grows in magnitude like `(1 − π/4) J exp(X/2)` for large `X`. -/
theorem Printed.criticalTraceFormula_false : ¬ Printed.criticalTraceFormula := by
  intro printed
  let projection : (AdeleRing (𝓞 Gauss) Gauss)ˣ →ₜ* C[Gauss] :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C[Gauss] := projection.comp
    ⟨canonicalIdeleNormSection Gauss, canonicalIdeleNormSection_continuous Gauss⟩
  have hτ : RightInverse τ (ideleClassNorm Gauss) := canonicalIdeleNormSection_rightInverse Gauss
  obtain ⟨η, φ, weight, hφ, hP, hsmooth, hc, hpos, hI, hlocal⟩ :=
    criticalTraceFormula_gaussian_shell_comparison τ hτ
  obtain ⟨ψ, hψ⟩ := criticalTraceFormula_false_differences
    criticalTraceFormula_false_gaussian_degree τ step₄ η
  have ht (n : ℕ) (g : C[Gauss]) :
      (ψ (step₄ ^ n)).val.val g = φ.val ((τ (step₄ ^ n))⁻¹ * g) := by
    rw [hψ, hφ]
    simp only [one_mul, map_mul, mul_inv_rev, mul_assoc, map_one, inv_one]
  obtain ⟨L, hL⟩ := printed Gauss τ hτ
  let values (n : ℕ) := L (ψ (step₄ ^ n))
  obtain ⟨B, hb⟩ := criticalTraceFormula_false_spectral_bound τ φ
  have hB (n) : ‖values n‖ ≤ B := hb _ _ (ht n) ((hL _).1)
  choose a b ha hb' hsum using fun n : ℕ ↦ (hL (ψ (step₄ ^ n))).2
  let G (n : ℕ) := localSum[Gauss](a n, b n)
  let P := gaussianPole(φ, 1 / 2)
  let N := gaussianPole(φ, -1 / 2)
  have hG (n) : G n = (2 : ℂ)⁻¹ ^ n * N + 2 ^ n * P - values n := by
    have he := (hsum n).tsum_eq
    have hp := criticalTraceFormula_false_polar τ hτ φ (ψ (step₄ ^ n)).val n (ht n)
    dsimp only [G]
    rw [he, hp.1, hp.2]
    change _ + (_ + _ - _ - _) = _
    dsimp only [values, N, P]
    ring
  have h₁ := criticalTraceFormula_false_limit P N values G B hB hG
  have hdiff := hlocal b (fun n v u ↦ (hb' n v u).trans (ht n _))
  have hfinite := hdiff.add (criticalTraceFormula_false_smoothed_shells weight hsmooth hc hpos)
  simp only [sub_add_cancel, zero_add, hI] at hfinite
  have hcx : ∀ w : InfinitePlace Gauss, w.IsComplex := by
    have : IsCyclotomicExtension {4} ℚ Gauss := CyclotomicField.isCyclotomicExtension 4 ℚ
    exact (IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Gauss (by decide)).isComplex
  have harch (w : InfinitePlace Gauss) :=
    criticalTraceFormula_false_complex_tendsto τ hτ φ w (hcx w) (fun n ↦ a n w)
      (fun n u ↦ (ha n w u).trans (ht n _))
  have h₂ := (tendsto_finsetSum Finset.univ (fun w _ ↦ harch w)).add hfinite
  simp only [Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← mul_add] at h₂
  have he : P = P / (((Real.pi / 4 : ℝ)) : ℂ) := by
    rw [← criticalTraceFormula_false_gaussian_volume]
    exact tendsto_nhds_unique h₁ h₂
  have hV : (((Real.pi / 4 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hcoeff : (((Real.pi / 4 : ℝ)) : ℂ) = 1 :=
    mul_left_cancel₀ hP (((eq_div_iff hV).mp he).trans (mul_one P).symm)
  have hreal : Real.pi / 4 = 1 := Complex.ofReal_injective (hcoeff.trans Complex.ofReal_one.symm)
  linarith [Real.pi_lt_four]

end RiemannMasullo
