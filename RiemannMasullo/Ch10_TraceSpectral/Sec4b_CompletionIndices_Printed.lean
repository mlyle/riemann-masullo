module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
import RiemannMasullo.External.HardyCriticalLine.CriticalLineZeroInfinitude
import RiemannMasullo.External.HardyCriticalLine.LowerIntegralBound
import RiemannMasullo.External.HardyCriticalLine.UpperIntegralBound
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas

import all RiemannMasullo.Ch03_IdelicZeta.Sec2

/-!
# Printed completion and indexing claims in §10.4.3

The corresponding quotient and kernel declarations are in `Sec4b.lean`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 3

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "C₁[" F "]" => (ideleClassNorm F).ker
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "μ[" F "]" => ideleClassTamagawaMeasure F
local notation "logNorm[" F "]" => (logIdeleClassNorm F)
local notation "E[" F ", " ω "]" =>
  ↥(modulatedDecayIsotype m[F] univ (mem_univ (0 : ℝ)) ω)
local notation "W[" F ", " s "]" =>
  CompactIntervalSobolev μ[F] logNorm[F] 0 0 s
local notation "θ(" ω ", " f ")" => (homogeneousAdelicTheta ω (f).val : _ → ℂ)
local notation "thetaClosure(" F ", " ω ", " a ", " s ")" =>
  closure {v : W[F, s] | ∃ f : adelePolarSubspace F,
    (v : C[F] → ℂ) =ᵐ[μ[F]] modulationWeight m[F] a (θ(ω, f))}

/-- Paper: Diagram (10.4.3.2), p. 465. As printed: bare norm completion
induces the lower right quotient arrow. On representatives, an untwisted
polar-free theta function completes to a vector in the closure of the
twisted theta image. The diagram note in `Sec4b.lean` inserts the twist
before completion (ERRATA F193). -/
def Printed.spectralLineCompletion_descends : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual C₁[F]) (a s : ℝ), 0 ≤ s →
    ∀ (u : E[F, ω]) (v : W[F, s]),
      (v : C[F] → ℂ) =ᵐ[μ[F]] u.val.val →
      (∃ f : adelePolarSubspace F, u.val.val = θ(ω, f)) →
      v ∈ thetaClosure(F, ω, a, s)

section CompletionCounterexample

local notation "C" => C[ℚ]
local notation "K" => C₁[ℚ]
local notation "m" => m[ℚ]
local notation "μC" => μ[ℚ]
local notation "μ₁" => normOneIdeleClassTamagawaMeasure ℚ
local notation "B" => SchwartzBruhat (Multiplicative (AdeleRing (𝓞 ℚ) ℚ))
local notation "c(" z ")" => ideleClassNormTwist (1 : PontryaginDual C) z
local notation "θ₁(" f ")" => (homogeneousAdelicTheta (1 : PontryaginDual K) f : C → ℂ)
local notation "ΛG" => gaussianCompletedHeckeL (1 : PontryaginDual C)
local notation "ΛC" => continuedCompletedHeckeL (1 : PontryaginDual C)

-- This is the norm-section argument used in the injectivity of the trivial twist
-- chart in Chapter 3, §2.
private theorem ratUnitaryTwist_injective : Injective
    (ideleClassNormTwist (1 : PontryaginDual C)) := by
  intro z w he
  let τ (u : ℝ≥0ˣ) : C := QuotientGroup.mk (canonicalIdeleNormSection ℚ u)
  have hτ (u : ℝ≥0ˣ) : ideleClassNorm ℚ (τ u) = u :=
    canonicalIdeleNormSection_rightInverse ℚ u
  let d := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 z
  refine (existsUnique_complexPower d).unique (fun _ ↦ one_mul _) fun u ↦ ?_
  have h := DFunLike.congr_fun he (τ u)
  change 1 * (((ideleClassNorm ℚ (τ u)).val : ℝ) : ℂ) ^ z =
    1 * (((ideleClassNorm ℚ (τ u)).val : ℝ) : ℂ) ^ w at h
  rw [hτ, one_mul, one_mul] at h
  exact (one_mul _).trans h

private theorem ratUnitaryTwist_regular {z : ℂ} (hz : z ≠ 0) (hz₁ : z ≠ 1) :
    c(z) ≠ 1 ∧ c(z) ≠ c(1) := by
  refine ⟨fun h ↦ hz (ratUnitaryTwist_injective (h.trans ?_)),
    fun h ↦ hz₁ (ratUnitaryTwist_injective h)⟩
  ext g
  change (1 : ℂ) = 1 * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ (0 : ℂ)
  simp

private theorem gaussianRat_eq_continued : ΛG = ΛC := by
  funext z
  have hG := globalIdelicZFunction_meromorphic (adelicStandardGaussian (1 : PontryaginDual C)) 1
  have hC := (continuedCompletedHeckeL_spec (1 : PontryaginDual C)).1
  have he := meromorphicContinuation_eventuallyEq hG.meromorphicOn hC.meromorphicOn (fun s hs ↦ by
    change ΛG s = ΛC s
    rw [gaussianCompletedHeckeL_eq_completedHeckeL (1 : PontryaginDual C) s hs,
      (continuedCompletedHeckeL_spec (1 : PontryaginDual C)).2 ⟨s, hs⟩]
    norm_num [NumberField.discr_rat]) z
  exact (((hG (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hC (mem_univ z))).mp he).eq_of_nhds

private theorem gaussianRat_nonzero_imag (t : ℝ) (ht : 0 < t) :
    ΛG ((t : ℂ) * Complex.I) ≠ 0 := by
  let w := (t : ℂ) * Complex.I
  let z := 1 - w
  have hz : z.re = 1 := by simp [z, w, Complex.mul_re]
  have hzne : z ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [z, w, Complex.mul_im] at him
    linarith
  have hz₀ : z ≠ 0 := fun h ↦ by simp [h] at hz
  let hC := continuedCompletedHeckeL_spec (1 : PontryaginDual C)
  have hau : AnalyticAt ℂ ΛG z :=
    (globalIdelicZFunction_poles (adelicStandardGaussian (1 : PontryaginDual C)) 1).1
      z (ratUnitaryTwist_regular hz₀ hzne)
  have hzN : ΛC z ≠ 0 := by
    intro hzero
    have ha : AnalyticAt ℂ ΛC z := gaussianRat_eq_continued ▸ hau
    have htO : 0 < meromorphicOrderAt ΛC z := by
      rw [ha.meromorphicOrderAt_eq]
      have hne := ha.analyticOrderAt_ne_zero.mpr hzero
      cases horder : analyticOrderAt ΛC z using ENat.recTopCoe with
      | top => simp
      | coe n => simpa [horder, Nat.pos_iff_ne_zero] using hne
    have hbad := completedHeckeL_continuation_zeros (1 : PontryaginDual C) ΛC hC.1 hC.2
      (hz ▸ zero_lt_one) htO
    exact (lt_irrefl (1 : ℝ)) (hz ▸ hbad)
  have hdual : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), ΛC s =
      completedHeckeL ((1 : PontryaginDual C)⁻¹) s := by
    simpa only [inv_one] using hC.2
  obtain ⟨ε, -, -, hfun⟩ := completedHeckeL_continuation_functionalEquation
    (1 : PontryaginDual C) ΛC ΛC hC.1 hC.2 hC.1 hdual
  rw [gaussianRat_eq_continued]
  intro hzero
  have hzero' : ΛC w = 0 := hzero
  exact hzN ((hfun w).trans (by rw [hzero', mul_zero]))

private theorem fourierZero_translate (u : IdeleGroup (𝓞 ℚ) ℚ) (f : B) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd 0) =
      (((ideleNorm ℚ u).val : ℝ) : ℂ) * adeleSchwartzFourier f (Multiplicative.ofAdd 0) := by
  let q := (adelicThetaLinearMap ℚ).ker.mkQL
  let ρ := (existsUnique_globalThetaAction (F := ℚ)).exists.choose
  have hρ : ρ (QuotientGroup.mk u : C) (q f) = q (schwartzBruhatUnitTranslate u f) :=
    (existsUnique_globalThetaAction (F := ℚ)).exists.choose_spec.2 u f
  have h := globalThetaPolarValues_snd_translate (F := ℚ) (QuotientGroup.mk u) (q f)
  rw [hρ, globalThetaPolarValues_mk, globalThetaPolarValues_mk] at h
  exact h

private theorem exists_polar_eval_ne_zero (t : ℝ) (ht : 0 < t) :
    ∃ f : adelePolarSubspace ℚ, globalIdelicZFunction f.val c((t : ℂ) * Complex.I) ≠ 0 := by
  let z := (t : ℂ) * Complex.I
  have hz : z ≠ 0 := by simp [z, ht.ne']
  have hz₁ : z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at this
  have hreg := ratUnitaryTwist_regular hz hz₁
  obtain ⟨D, -, hD, hfac⟩ := adelicEigendistribution_normalized (1 : PontryaginDual C)
  let G : B := adelicStandardGaussian (1 : PontryaginDual C)
  have hd := (hD z (D z)).1 rfl
  have hnon : c(z) ≠ 1 := hreg.1
  obtain ⟨g, hg⟩ : ∃ g : C, c(z) g ≠ 1 := by
    by_contra! h
    exact hnon (ContinuousMonoidHom.ext h)
  have hqsurj : Surjective (QuotientGroup.mk : IdeleGroup (𝓞 ℚ) ℚ → C) := QuotientGroup.mk_surjective
  obtain ⟨u, rfl⟩ := hqsurj g
  let r : ℂ := (((ideleNorm ℚ u).val : ℝ) : ℂ)
  let q := c(z) (QuotientGroup.mk u)
  have hq : q ≠ 1 := hg
  have hqr : q ≠ r := by
    intro h
    have hnorm : ‖q‖ = 1 := by
      rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm ℚ)
        (isProperMap_ideleClassNorm ℚ) (ideleClassNorm_ne_one (F := ℚ))]
      rw [quasiCharacterAbscissa_ideleClassNormTwist]
      simp [z, Complex.mul_re]
    have hr : (ideleNorm ℚ u).val = 1 := by
      rw [h] at hnorm
      change ‖((((ideleNorm ℚ u).val : ℝ≥0) : ℝ) : ℂ)‖ = 1 at hnorm
      rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)] at hnorm
      exact_mod_cast hnorm
    apply hq
    simpa [r, hr] using h
  let A := schwartzBruhatUnitTranslate u
  let d := A G - G
  let f := A d - r • d
  have hd₀ : d (Multiplicative.ofAdd 0) = 0 := by
    change A G (Multiplicative.ofAdd 0) - G (Multiplicative.ofAdd 0) = 0
    rw [schwartzBruhatUnitTranslate_apply, mul_zero, sub_self]
  have hf : f ∈ adelePolarSubspace ℚ := by
    apply (mem_adelePolarSubspace f).2
    refine ⟨?_, ?_⟩
    · change A d (Multiplicative.ofAdd 0) - r * d (Multiplicative.ofAdd 0) = 0
      rw [schwartzBruhatUnitTranslate_apply, mul_zero, hd₀, mul_zero, sub_self]
    · change (adelePolarValues f).2 = 0
      rw [show f = A d - r • d from rfl, map_sub, map_smul]
      change adeleSchwartzFourier (A d) (Multiplicative.ofAdd 0) -
        r * adeleSchwartzFourier d (Multiplicative.ofAdd 0) = 0
      rw [fourierZero_translate, sub_self]
  have htrans (k : B) : D z (A k) = q * D z k := hd.1 u k
  have hval : D z d = q - 1 := by
    change D z (A G - G) = _
    rw [map_sub, htrans, show D z G = 1 from hd.2, mul_one]
  have hval' : D z f = (q - r) * (q - 1) := by
    change D z (A d - r • d) = _
    rw [map_sub, map_smul, htrans, hval, smul_eq_mul, sub_mul]
  refine ⟨⟨f, hf⟩, ?_⟩
  change globalIdelicZFunction f c(z) ≠ 0
  rw [hfac z hreg.1 hreg.2 f, hval']
  exact mul_ne_zero (gaussianRat_nonzero_imag t ht)
    (mul_ne_zero (sub_ne_zero.mpr hqr) (sub_ne_zero.mpr hq))

local notation "E₀" => E[ℚ, (1 : PontryaginDual K)]
local notation "U" => ModulatedExponentialDecay m univ
local notation "hm" =>
  (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation m)
local notation "hsurj" => (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.2.2.2.1

/-- Lift the compact average to the decay space, as in the periodization proof
in Chapter 4, §5. -/
private theorem exists_ratHomogeneousTheta_decay (f : adelePolarSubspace ℚ) :
    ∃ u : E₀, u.val.val = θ₁(f.val) := by
  let : (μ₁).IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let : (μ₁).Regular := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.2.1
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  let : LocallyCompactSpace K :=
    (isCompact_iff_compactSpace.mpr ‹CompactSpace K›).isClosed.locallyCompactSpace
  let ψ : U := ⟨adelicTheta f.val, adelicTheta_mem_modulatedExponentialDecay_of_polar f.val f.property⟩
  obtain ⟨ρ, hρ, -⟩ := exists_modulatedExponentialDecay_translationAction m univ hm hsurj
    ordConnected_univ univ_nonempty
  let ω : PontryaginDual K := 1
  obtain ⟨A, hA, -⟩ := existsUnique_modulatedExponentialDecay_isotypicProjector m univ hm hsurj
    ordConnected_univ univ_nonempty μ₁ ρ hρ ω
  let zero : (Set.univ : Set ℝ) := ⟨0, mem_univ _⟩
  let v : U := (A ψ).val
  have htw (g : U) (x : C) : modulatedExponentialDecayTwist m univ zero g x = g.val x :=
    congrFun (modulationWeight_zero m g.val) x
  have hval (x : C) : v.val x = ((μ₁).real univ)⁻¹ • θ₁(f.val) x := by
    have he := congrArg (fun g : SchwartzBruhat C ↦ g x) (hA ψ zero)
    rw [htw] at he
    refine he.trans ((schwartzBruhatIsotypicProjector_apply m hm μ₁ ω
      (modulatedExponentialDecayTwist m univ zero ψ) x).2.trans ?_)
    congr 1
    change (∫ k : K, star (ω k : ℂ) *
      modulatedExponentialDecayTwist m univ zero ψ (k.val⁻¹ * x) ∂μ₁) = _
    simp only [htw, ω, PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul]
    have hev (k : K) : ψ.val (k.val⁻¹ * x) = adelicTheta f.val ((k⁻¹ : K).val * x) := rfl
    rw [integral_congr_ae (.of_forall hev)]
    have hInv := integral_inv_eq_self (fun k : K ↦ adelicTheta f.val (k.val * x)) μ₁
    rw [hInv]
    unfold homogeneousAdelicTheta
    simp only [ContinuousMap.coe_mk, PontryaginDual.one_apply, Circle.coe_one, mul_one]
  have hmass := (measureReal_univ_pos (μ := μ₁)).ne'
  let v' : U := ((μ₁).real univ : ℂ) • v
  have hrep : v'.val = θ₁(f.val) := by
    funext x
    change ((μ₁).real univ : ℂ) * v.val x = _
    rw [hval, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hmass), one_mul]
  refine ⟨⟨v', (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mpr ?_⟩, hrep⟩
  intro k x
  rw [hrep]
  exact homogeneousAdelicTheta_homogeneous ω f.val k x

/-- The unnormalized norm-one average multiplies a Mellin integral in the trivial
component by the mass of the compact norm-one group. -/
private theorem ratHomogeneousTheta_mellin (f : adelePolarSubspace ℚ) (z : ℂ) :
    (∫ g, θ₁(f.val) g * c(z) g ∂μC) =
      ((μ₁).real univ : ℂ) * globalIdelicZFunction f.val c(z) := by
  let : (μC).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let : (μ₁).IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  obtain ⟨hf₀, hfF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  let v : C → ℂ := fun g ↦ adelicTheta f.val g * c(z) g
  have hv : Integrable v μC := globalThetaMellinIntegral_integrable_of_vanishing f.val hf₀ hfF c(z)
  have hcv : Continuous v := (adelicTheta f.val).continuous.mul (c(z)).continuous
  have hc (k : K) : c(z) k.val = 1 := by
    change 1 * (((ideleClassNorm ℚ k.val).val : ℝ) : ℂ) ^ z = 1
    rw [show ideleClassNorm ℚ k.val = 1 from k.property]
    simp
  have hnorm (k : K) : Integrable (fun g : C ↦ v (k.val * g)) μC :=
    (measurePreserving_mul_left μC k.val).integrable_comp_of_integrable hv
  have hprod : Integrable (fun p : K × C ↦ v (p.1.val * p.2)) ((μ₁).prod μC) := by
    apply (integrable_prod_iff (hcv.comp ((continuous_subtype_val.comp continuous_fst).mul
      continuous_snd)).aestronglyMeasurable).mpr
    refine ⟨.of_forall hnorm, ?_⟩
    have hin (k : K) : (∫ g : C, ‖v (k.val * g)‖ ∂μC) = ∫ g, ‖v g‖ ∂μC :=
      integral_mul_left_eq_self (μ := μC) (fun g ↦ ‖v g‖) k.val
    exact (integrable_const _).congr (.of_forall fun k ↦ (hin k).symm)
  have haverage (g : C) : θ₁(f.val) g * c(z) g = ∫ k : K, v (k.val * g) ∂μ₁ := by
    unfold homogeneousAdelicTheta
    rw [ContinuousMap.coe_mk, ← integral_mul_const]
    refine integral_congr_ae (.of_forall fun k ↦ ?_)
    simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one, one_mul, v, map_mul, hc]
  simp_rw [haverage]
  rw [← integral_integral_swap hprod]
  simp_rw [integral_mul_left_eq_self (μ := μC) v]
  rw [integral_const, Complex.real_smul]
  exact congrArg (((μ₁).real univ : ℂ) * ·)
    (congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf₀ hfF) c(z))

private theorem exists_ratLineRepresentative (u : E₀) :
    ∃ v : W[ℚ, 2], (v : C → ℂ) =ᵐ[μC] u.val.val := by
  let action := exists_modulatedExponentialDecay_translationAction m univ hm hsurj
    ordConnected_univ univ_nonempty
  let ω : PontryaginDual K := 1
  let S := actionIsotype (action.choose.comp (ideleClassNorm ℚ).ker.subtype) ω
  have hu : u.val ∈ S := by
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Subtype.ext
    funext x
    exact (action.choose_spec.1 k.val u.val x).trans
      ((mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mp u.property k x)
  let φ : S := ⟨u.val, hu⟩
  obtain ⟨i, hi, -⟩ := existsUnique_spectralLineTestCompletion (F := ℚ) 0
    (show (0 : ℝ) ≤ 2 by norm_num) ω
  exact ⟨(i φ).val, (hi.1 φ).trans (.of_eq (modulationWeight_zero m u.val.val))⟩

local notation "shift(" a ", " t ")" => (((a : ℝ) : ℂ) + (t : ℂ) * Complex.I)

private theorem ratNormTwist_modulationWeight (a : ℝ) (z : ℂ) (v : C → ℂ) (g : C) :
    modulationWeight m a v g * c(z) g = v g * c((a : ℂ) + z) g := by
  let x : ℝ := (ideleClassNorm ℚ g).val
  have hx : 0 < x := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))
  change ((x ^ a : ℝ) : ℂ) * v g * (1 * (x : ℂ) ^ z) =
    v g * (1 * (x : ℂ) ^ ((a : ℂ) + z))
  rw [Complex.ofReal_cpow hx.le, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  ring

private theorem exists_ratLineEvaluation (a t : ℝ)
    (hz : 0 < meromorphicOrderAt ΛC (shift(a, t))) :
    ∃ L₂ : StrongDual ℂ W[ℚ, 2], ∀ v : W[ℚ, 2],
      L₂ v = ∫ g, v g * c((t : ℂ) * Complex.I) g ∂μC := by
  let χ : PontryaginDual K → PontryaginDual C := fun _ ↦ 1
  let z := shift(a, t)
  obtain ⟨hL, hR⟩ := continuedCompletedHeckeL_spec (1 : PontryaginDual C)
  have ho₂ : meromorphicOrderAt ΛC 2 = 0 := by
    apply (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
    rw [show ΛC 2 = completedHeckeL (1 : PontryaginDual C) ⟨2, by norm_num⟩ from hR ⟨2, by norm_num⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos _ (by norm_num))
      (finiteHeckeL_ne_zero_of_one_lt_re _ _)
  have hf := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ z) (by rw [ho₂]; simp)
  have hp : 0 < (meromorphicOrderAt ΛC z).untop₀ := by
    apply WithTop.coe_lt_coe.mp
    rwa [WithTop.coe_untop₀_of_ne_top hf]
  have hn : 0 < (meromorphicOrderAt ΛC z).untop₀.toNat := by omega
  let j : SpectralLineJetIndex χ a 2 := ⟨(1, t, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    exact ⟨hn, by norm_num⟩⟩
  obtain ⟨L₂, hL₂, -⟩ := spectralLineJet_functional χ (by norm_num : (1 : ℝ) < 2) j
  refine ⟨L₂, fun v ↦ ?_⟩
  simpa only [j, χ, spectralZeroJet, pow_zero, mul_one, Complex.ofReal_zero, zero_add] using (hL₂ v).2

private theorem spectralLineCompletion_descends_false_of_zero (t : ℝ) (ht : 0 < t)
    (hz : 0 < meromorphicOrderAt ΛC (shift((1 / 2 : ℝ), t))) :
    ¬ Printed.spectralLineCompletion_descends := by
  intro hdesc
  let a : ℝ := 1 / 2
  let z := (t : ℂ) * Complex.I
  have hregular := ratUnitaryTwist_regular
    (z := shift(a, t)) (by
      intro h
      have := congrArg Complex.re h
      norm_num [a, Complex.mul_re] at this)
    (by
      intro h
      have := congrArg Complex.re h
      norm_num [a, Complex.mul_re] at this)
  obtain ⟨L₂, hL₂⟩ := exists_ratLineEvaluation a t hz
  obtain ⟨f, hf⟩ := exists_polar_eval_ne_zero t ht
  obtain ⟨u, hu⟩ := exists_ratHomogeneousTheta_decay f
  obtain ⟨v, hv⟩ := exists_ratLineRepresentative u
  have hvL : L₂ v ≠ 0 := by
    rw [hL₂ v]
    have he : (∫ g, v g * c(z) g ∂μC) = ∫ g, θ₁(f.val) g * c(z) g ∂μC :=
      integral_congr_ae ((hv.trans (.of_eq hu)).mono fun g hg ↦ congrArg (· * c(z) g) hg)
    rw [he, ratHomogeneousTheta_mellin]
    let : (μ₁).IsHaarMeasure :=
      (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
    let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ₁)).ne') hf
  have hG : ΛG (shift(a, t)) = 0 := by
    rw [gaussianRat_eq_continued]
    by_contra hn
    have ho := ((continuedCompletedHeckeL_spec (1 : PontryaginDual C)).1
      (mem_univ (shift(a, t)))).meromorphicOrderAt_eq_zero_iff.mpr hn
    exact (lt_irrefl 0) (ho ▸ hz)
  obtain ⟨D, -, -, hD⟩ := adelicEigendistribution_normalized (1 : PontryaginDual C)
  have hsubset : {w : W[ℚ, 2] | ∃ f' : adelePolarSubspace ℚ,
      (w : C → ℂ) =ᵐ[μC] modulationWeight m a (θ₁(f'.val))} ⊆ {w | L₂ w = 0} := by
    rintro w ⟨f', hw⟩
    change L₂ w = 0
    rw [hL₂ w]
    have he : (∫ g, w g * c(z) g ∂μC) =
        ∫ g, θ₁(f'.val) g * c(shift(a, t)) g ∂μC := by
      apply integral_congr_ae
      filter_upwards [hw] with g hg
      rw [hg]
      exact ratNormTwist_modulationWeight a z _ _
    rw [he, ratHomogeneousTheta_mellin, hD _ hregular.1 hregular.2 f'.val, hG, zero_mul, mul_zero]
  exact hvL (closure_minimal hsubset (isClosed_eq L₂.continuous continuous_const)
    (hdesc ℚ 1 a 2 (by norm_num) u v hv ⟨f, hu⟩))

/-- The positive ordinate is supplied by Thomas Lince's vendored Hardy first-zero
certificate. Chapter 13 compares the finite trivial Hecke L-function with Riemann zeta,
and its archimedean factor is nonvanishing on this half-plane. -/
private theorem exists_ratLinePositiveZero :
    ∃ t : ℝ, 0 < t ∧ 0 < meromorphicOrderAt ΛC (shift((1 / 2 : ℝ), t)) := by
  obtain ⟨t, ht, hzeta⟩ := HardyFirstZero.first_zero_on_line
  refine ⟨t, by linarith [ht.1], ?_⟩
  let z := shift((1 / 2 : ℝ), t)
  have hz : z ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z, Complex.mul_re] at this
  have ha := analyticOn_riemannZeta _ hz
  have hmer : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C)
    hmer (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by norm_num [z, Complex.mul_re])
  have hz₀ : riemannZeta z = 0 := by simpa [z] using hzeta
  change 0 < meromorphicOrderAt ΛC z
  rw [← he, ha.meromorphicOrderAt_eq]
  have hne := ha.analyticOrderAt_ne_zero.mpr hz₀
  cases ho : analyticOrderAt riemannZeta z using ENat.recTopCoe with
  | top => simp
  | coe k => simpa [ho, Nat.pos_iff_ne_zero] using hne

/-- Paper: Diagram (10.4.3.2), p. 465. Over `ℚ` in the trivial isotype, take
a positive critical-line zeta ordinate. Two norm translations of the standard
adelic Gaussian cancel its polar values while preserving a nonzero Mellin value
at the corresponding frequency on the imaginary axis. The Mellin functional is
continuous in the Sobolev norm of degree two. It vanishes on the twisted theta
closure by the forward factorization at the critical-line zero. -/
theorem Printed.spectralLineCompletion_descends_false :
    ¬ Printed.spectralLineCompletion_descends := by
  obtain ⟨t, ht, hz⟩ := exists_ratLinePositiveZero
  exact spectralLineCompletion_descends_false_of_zero t ht hz

/-- Paper: Diagram (10.4.3.2), p. 465. As printed: the lower right arrow
induced by bare completion is injective. On representatives, if the
completed vector belongs to the twisted theta closure, the source
representative is already an untwisted polar-free theta function.
The diagram note in `Sec4b.lean` identifies the needed closure condition.
`spectralLineKernel_orthogonalLift` uses the completed quotient (ERRATA F194). -/
def Printed.spectralLineCompletion_quotientInjective : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ω : PontryaginDual C₁[F]) (a s : ℝ), 0 ≤ s →
    ∀ (u : E[F, ω]) (v : W[F, s]),
      (v : C[F] → ℂ) =ᵐ[μ[F]] u.val.val →
      v ∈ thetaClosure(F, ω, a, s) →
      ∃ f : adelePolarSubspace F, u.val.val = θ(ω, f)

/-- Real norm weights preserve the two-sided decay space and the trivial
norm-one isotype. -/
private theorem ratLineCompletion_weightedTest (a : ℝ) (u : E₀) :
    ∃ u' : E₀, u'.val.val = modulationWeight m a u.val.val := by
  have hJ : (fun b : ℝ ↦ b - a) '' univ = univ :=
    image_univ_of_surjective fun b ↦ ⟨b + a, add_sub_cancel_right b a⟩
  obtain ⟨e, he⟩ : ∃ e : U ≃L[ℂ] U, ∀ f, (e f).val = modulationWeight m a f.val := by
    exact (congrArg (fun J : Set ℝ ↦ ∃ e : U ≃L[ℂ] ModulatedExponentialDecay m J,
      ∀ f, (e f).val = modulationWeight m a f.val) hJ).mp
      (modulatedExponentialDecay_shift_equiv m univ hm hsurj ordConnected_univ univ_nonempty a)
  refine ⟨⟨e u.val, (mem_modulatedDecayIsotype_iff m 1 univ (mem_univ _) _).mpr ?_⟩, he _⟩
  intro k x
  have hk : ideleClassNorm ℚ k.val = 1 := k.property
  have hn : ideleClassNorm ℚ (k.val⁻¹ * x) = ideleClassNorm ℚ x := by
    rw [map_mul, map_inv, hk, inv_one, one_mul]
  have hu := (mem_modulatedDecayIsotype_iff m 1 univ (mem_univ _) _).mp u.property k x
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul] at hu ⊢
  rw [he]
  change (↑((((ideleClassNorm ℚ (k.val⁻¹ * x)).val : ℝ) ^ a)) : ℂ) *
      u.val.val (k.val⁻¹ * x) =
    (↑((((ideleClassNorm ℚ x).val : ℝ) ^ a)) : ℂ) * u.val.val x
  rw [hn, hu]

/-- Paper: Diagram (10.4.3.2), p. 465. Over the rationals in the trivial
isotype, twist the same polar-free theta used in the descent counterexample
by the exponent `-1/2`. Its completed vector is a twisted generator. Its
Mellin value at the certified critical-line zero is the nonzero imaginary-axis
value of the untwisted test, so it cannot itself be an untwisted theta. -/
theorem Printed.spectralLineCompletion_quotientInjective_false :
    ¬ Printed.spectralLineCompletion_quotientInjective := by
  intro hinj
  obtain ⟨t, ht, hz⟩ := exists_ratLinePositiveZero
  let a : ℝ := -1 / 2
  let z := shift((1 / 2 : ℝ), t)
  obtain ⟨f, hf⟩ := exists_polar_eval_ne_zero t ht
  obtain ⟨u, hu⟩ := exists_ratHomogeneousTheta_decay f
  obtain ⟨u', hu'⟩ := ratLineCompletion_weightedTest a u
  have hrep : u'.val.val = modulationWeight m a (θ₁(f.val)) := hu'.trans (congrArg _ hu)
  obtain ⟨v, hv⟩ := exists_ratLineRepresentative u'
  obtain ⟨g, hg⟩ := hinj ℚ 1 a 2 (by norm_num) u' v hv
    (subset_closure ⟨f, hv.trans (.of_eq hrep)⟩)
  have hshift : (a : ℂ) + z = (t : ℂ) * Complex.I := by
    simp [a, z, Complex.ofReal_div]
    ring
  have hregular := ratUnitaryTwist_regular (z := z)
    (fun h ↦ by
      have he := congrArg Complex.re h
      norm_num [z, Complex.mul_re] at he)
    (fun h ↦ by
      have he := congrArg Complex.re h
      norm_num [z, Complex.mul_re] at he)
  have hG : ΛG z = 0 := by
    rw [gaussianRat_eq_continued]
    by_contra h
    have hL := (continuedCompletedHeckeL_spec (1 : PontryaginDual C)).1 (mem_univ z)
    have ho := hL.meromorphicOrderAt_eq_zero_iff.mpr h
    exact (lt_irrefl 0) (ho ▸ hz)
  have he : (∫ x, θ₁(g.val) x * c(z) x ∂μC) =
      ∫ x, θ₁(f.val) x * c((t : ℂ) * Complex.I) x ∂μC := by
    simp only [← hg, hrep]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by
      simpa only [hshift] using ratNormTwist_modulationWeight a z (θ₁(f.val)) x
  rw [ratHomogeneousTheta_mellin, ratHomogeneousTheta_mellin] at he
  obtain ⟨D, -, -, hD⟩ := adelicEigendistribution_normalized (1 : PontryaginDual C)
  rw [hD _ hregular.1 hregular.2 g.val, hG, zero_mul, mul_zero] at he
  let : (μ₁).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let : CompactSpace K := (ideleClassGroup_finiteness ℚ).2.1
  exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ₁)).ne') hf) he.symm

end CompletionCounterexample

local notation "zeroOrder(" χ ", " a ", " t ")" =>
  meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + (t : ℂ) * Complex.I)
local notation "lineZeros(" χ ", " a ")" =>
  {t : ℝ // 0 < zeroOrder(χ, a, t)}
local notation "lineJetIndices(" χ ", " ω ", " t ", " a ", " s ")" =>
  {i : ℕ × ℕ × ℕ // i.2.2 <
    min (zeroOrder((χ) ((ω) i.1), a, ((t) i.1 i.2.1).val)).untop₀.toNat
      ⌊(s - 1) / 2 + 1⌋₊}

/-- Paper: Theorem 10.4.3.1, enumeration clause (2), p. 466. As printed:
each base character has an enumeration indexed by all nonnegative integers
of its zero ordinates on the line of real part a, ordered by absolute value.
The zero indexing of `spectralLineQuotientKernel_tendsto` allows finite
and empty rows (ERRATA F197). -/
def Printed.spectralLineZeroEnumeration : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a : ℝ), 0 < a →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]),
      IsSpectralBasepointChoice χ → ∀ ω,
        ∃ t : ℕ ≃ lineZeros(χ ω, a), Monotone (fun j ↦ |(t j).val|)

/-- Paper: Theorem 10.4.3.1, enumeration clause (2), p. 466. For `F = ℚ`
choose the trivial extension of the trivial norm-one character and set
`a = 2`. The completed zeta function has no zeros on this line, so the
enumeration cannot give a value even at index zero. -/
theorem Printed.spectralLineZeroEnumeration_false :
    ¬ Printed.spectralLineZeroEnumeration := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let ω : PontryaginDual C₁[ℚ] := 1
  obtain ⟨e, _⟩ := hall ℚ 2 (by norm_num) χ hχ ω
  let t := e 0
  let z : ℂ := 2 + (t.val : ℂ) * Complex.I
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  have ht : 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) z := t.property
  exact (not_lt_of_ge horder.le) ht

/-- Paper: Theorem 10.4.3.5, enumeration clauses (2)–(3), p. 472. As printed:
the ordered enumeration of strip zero pairs has an entry for every natural
number. The indexing in `spectralStripQuotientKernel_tendsto` uses just
the existing strip zeros (ERRATA F197).
Deviation: Clause (2) omits the offset range. Read it on the domain of
(10.4.3.38) in clause (3), the boundary and interior of the strip. -/
def Printed.spectralStripZeroEnumeration : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α : ℝ), 0 < a → 0 ≤ α →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]),
      IsSpectralBasepointChoice χ → ∀ ω,
        ∃ z : ℕ ≃ {p : ℝ × ℝ // p.2 ∈ Icc (-α) α ∧ 0 < zeroOrder(χ ω, a + p.2, p.1)},
          Monotone (fun j ↦ |(z j).val.1|)

/-- Paper: Theorem 10.4.3.5, enumeration clauses (2)–(3), p. 472. For
`F = ℚ` and the trivial basepoint take `a = 2` and `α = 0`.
Formula (10.4.3.38) forces the offset at index zero to be zero, so this
entry would be a completed zeta zero on the zero-free line of real part 2. -/
theorem Printed.spectralStripZeroEnumeration_false :
    ¬ Printed.spectralStripZeroEnumeration := by
  intro hall
  apply Printed.spectralLineZeroEnumeration_false
  intro F _ _ a ha χ hχ ω
  obtain ⟨z, hz⟩ := hall F a 0 ha le_rfl χ hχ ω
  let Z := {p : ℝ × ℝ // p.2 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < zeroOrder(χ ω, a + p.2, p.1)}
  have hzero (p : Z) : p.val.2 = 0 := by simpa using p.property.1
  let e : Z ≃ lineZeros(χ ω, a) :=
    { toFun := fun p ↦ ⟨p.val.1, by simpa only [hzero p, Complex.ofReal_zero, add_zero] using p.property.2⟩
      invFun := fun t ↦ ⟨(t.val, 0), by simp, by simpa only [Complex.ofReal_zero, add_zero] using t.property⟩
      left_inv := fun p ↦ Subtype.ext (Prod.ext rfl (hzero p).symm)
      right_inv := fun _ ↦ rfl }
  exact ⟨z.trans e, hz⟩

/-- Paper: Theorem 10.4.3.1(2), pp. 467–468. As printed: for a sequence in
the jet index set (10.4.3.11), escaping to the point of the one-point
compactification of the discrete index set is equivalent to both zero
coordinates tending to infinity. The rectangles in
`spectralKernelRectangle` already have the product order on their
endpoints (ERRATA F198). -/
def Printed.spectralLineJet_cofinite_iff_coordinates : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → 1 < s →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]), IsSpectralBasepointChoice χ →
      ∀ (ω : ℕ ≃ PontryaginDual C₁[F])
        (t : ∀ k : ℕ, ℕ ≃ lineZeros(χ (ω k), a)),
        (∀ k, Monotone (fun j ↦ |(t k j).val|)) →
        ∀ i : ℕ → lineJetIndices(χ, ω, t, a, s),
          Tendsto i atTop cofinite ↔
            Tendsto (fun n ↦ ((i n).val.1, (i n).val.2.1)) atTop atTop

section CofiniteCoordinates

open IsDedekindDomain

local notation "K[" F "]" => (ideleClassNorm F).ker
local notation "point(" a ", " t ")" => (((a : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I)
local notation "ord(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "Z(" χ ", " a ")" => {t : ℝ // 0 < ord(χ, point(a, t))}
local notation "J(" χ ", " ω ", " t ", " a ", " s ")" =>
  {i : ℕ × ℕ × ℕ // i.2.2 < min (ord((χ) ((ω) i.1), point(a, ((t) i.1 i.2.1).val))).untop₀.toNat
    ⌊(s - 1) / 2 + 1⌋₊}

private theorem positiveOrder {F : Type} [Field F] [NumberField F] (χ : PontryaginDual C[F])
    {z : ℂ} (hz : 0 < ord(χ, z)) : 0 < (ord(χ, z)).untop₀ := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have htwo : ord(χ, (2 : ℂ)) ≠ ⊤ := by
    intro h
    have hp : 0 < ord(χ, (2 : ℂ)) := h ▸ WithTop.coe_lt_top (0 : ℤ)
    have hb := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at hb
  have hne := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z) htwo
  apply WithTop.coe_lt_coe.mp
  rwa [WithTop.coe_untop₀_of_ne_top hne]

private theorem enumeration_contradicts (F : Type) [Field F] [NumberField F] (a : ℝ) (ha : 0 < a)
    (χ : PontryaginDual K[F] → PontryaginDual C[F]) (hχ : IsSpectralBasepointChoice χ)
    (ω : ℕ ≃ PontryaginDual K[F]) (t : ∀ k, ℕ ≃ Z(χ (ω k), a))
    (ht : ∀ k, Monotone (fun j ↦ |(t k j).val|)) :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates := by
  intro hall
  let i (n : ℕ) : J(χ, ω, t, a, (4 : ℝ)) := ⟨(0,n,0), lt_min
    (by have h := positiveOrder (χ (ω 0)) (t 0 n).property; dsimp; omega)
    (Nat.floor_pos.mpr (by norm_num))⟩
  have hi : Injective i := fun _ _ h ↦ congrArg (fun j ↦ j.val.2.1) h
  have hc : Tendsto i atTop cofinite := Nat.cofinite_eq_atTop ▸ hi.tendsto_cofinite
  have hp := (hall F a 4 ha (by norm_num) χ hχ ω t ht i).mp hc
  obtain ⟨n, hn⟩ := (hp.eventually_ge_atTop (1, 0)).exists
  exact Nat.not_succ_le_zero 0 hn.1

private theorem bounded_zeros {F : Type} [Field F] [NumberField F] (χ : PontryaginDual C[F])
    (a b : ℝ) : {t : Z(χ, a) | |t.val| ≤ b}.Finite := by
  let p (t : ℝ) := point(a, t)
  let K := p '' Icc (-b) b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop : Continuous p)
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL χ) K
  have hf := D.finiteSupport hK
  let f (t : Z(χ, a)) := p t.val
  have hi : Injective f := by
    intro x y h
    apply Subtype.ext
    simpa [f, p] using congrArg Complex.im h
  apply (hf.preimage hi.injOn).subset
  intro t ht
  change D (p t.val) ≠ 0
  have hM : MeromorphicOn (continuedCompletedHeckeL χ) K :=
    fun z _ ↦ (continuedCompletedHeckeL_spec χ).1.meromorphicOn z (mem_univ _)
  have hmem : p t.val ∈ K := ⟨t.val, abs_le.mp ht, rfl⟩
  change MeromorphicOn.divisor _ K (p t.val) ≠ 0
  rw [MeromorphicOn.divisor_apply hM hmem]
  exact (positiveOrder _ t.property).ne'

private theorem enumerate_zeros {F : Type} [Field F] [NumberField F] (χ : PontryaginDual C[F])
    (a : ℝ) [Infinite Z(χ, a)] : ∃ t : ℕ ≃ Z(χ, a), Monotone (fun j ↦ |(t j).val|) := by
  classical
  let key (x : Z(χ, a)) := toLex (|x.val|, x.val)
  let pred (x : Z(χ, a)) := {y | key y < key x}
  have hp (x) : (pred x).Finite := (bounded_zeros χ a |x.val|).subset
    fun y hy ↦ Prod.Lex.monotone_fst (key y) (key x) (le_of_lt hy)
  let rank (x : Z(χ, a)) := (pred x).ncard
  have hlt {x y} (h : key x < key y) : rank x < rank y := by
    refine Set.ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨fun _ hz ↦ lt_trans hz h, ?_⟩) (hp y)
    intro he
    have : x ∈ pred x := he ▸ (show x ∈ pred y from h)
    exact (lt_irrefl (key x)) this
  have hinj : Injective rank := by
    intro x y h
    rcases lt_trichotomy (key x) (key y) with hxy | he | hyx
    · exact False.elim ((hlt hxy).ne h)
    · exact Subtype.ext (congrArg (fun k ↦ (ofLex k).2) he)
    · exact False.elim ((hlt hyx).ne h.symm)
  let e := Equiv.ofInjective rank hinj
  let : Infinite (range rank) := Infinite.of_injective e e.injective
  let o := Nat.Subtype.orderIsoOfNat (range rank)
  let t := o.toEquiv.trans e.symm
  refine ⟨t, fun i j hij ↦ ?_⟩
  have hr (i) : rank (t i) = (o i).val := congrArg Subtype.val (e.apply_symm_apply (o i))
  by_contra! h
  have hji := hlt (x := t j) (y := t i) (Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))
  rw [hr, hr] at hji
  exact (not_lt_of_ge (o.monotone hij)) hji

-- Distinct primes give distinct norm-one classes by inserting -1 at one prime.
private theorem rat_normOne_infinite : Infinite K[ℚ] := by
  classical
  let V := HeightOneSpectrum (𝓞 ℚ)
  let : Infinite V := Infinite.of_injective
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  let g (v : V) := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)
  let i (v : V) : K[ℚ] := ⟨QuotientGroup.mk (g v), by
    change ideleClassNorm ℚ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1)) = 1
    rw [ideleClassNorm_ofAdicCompletion]
    apply Units.ext
    change ‖(-1 : v.adicCompletion ℚ)‖₊ = 1
    simp⟩
  refine Infinite.of_injective i fun v w h ↦ ?_
  by_contra hvw
  have hm : (QuotientGroup.mk (g v) : C[ℚ]) = QuotientGroup.mk (g w) := congrArg Subtype.val h
  obtain ⟨a, ha⟩ := QuotientGroup.eq.mp hm
  have hq := congrArg (fun x : IdeleGroup (𝓞 ℚ) ℚ ↦ x.val.1 Rat.infinitePlace) ha
  change algebraMap ℚ Rat.infinitePlace.Completion a.val =
    (g v)⁻¹.val.1 Rat.infinitePlace * 1 at hq
  have he (v : V) : (g v)⁻¹ = g v := by
    change (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (-1))⁻¹ = _
    rw [← map_inv]
    simp [g]
  rw [he] at hq
  change algebraMap ℚ Rat.infinitePlace.Completion a.val = 1 * 1 at hq
  have ha1 : a = 1 := Units.ext ((algebraMap ℚ Rat.infinitePlace.Completion).injective
    (hq.trans ((one_mul _).trans (map_one _).symm)))
  rw [ha1, map_one, eq_comm, inv_mul_eq_one] at ha
  have hc := congrArg (fun d : IdeleGroup (𝓞 ℚ) ℚ ↦ d.val.2 v) ha
  change Pi.mulSingle (M := fun u : V ↦ u.adicCompletion ℚ) v (-1) v =
    Pi.mulSingle (M := fun u : V ↦ u.adicCompletion ℚ) w (-1) v at hc
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hvw] at hc
  have hrat : (-1 : ℚ) = 1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective (by
    simpa only [map_neg, map_one] using hc)
  norm_num at hrat

private theorem rat_character_enumeration : Nonempty (ℕ ≃ PontryaginDual K[ℚ]) := by
  let : CompactSpace K[ℚ] := (ideleClassGroup_finiteness ℚ).2.1
  have : SecondCountableTopology K[ℚ] := TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace K[ℚ] := (isCompact_iff_compactSpace.mpr ‹CompactSpace K[ℚ]›).isClosed.locallyCompactSpace
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual K[ℚ]) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K[ℚ] Circle).secondCountableTopology
  have : Countable (PontryaginDual K[ℚ]) := countable_of_Lindelof_of_discrete
  have : Infinite (PontryaginDual K[ℚ]) := by
    apply Infinite.of_not_fintype
    intro _
    obtain ⟨e, _⟩ := pontryaginDual_bidual (G := K[ℚ])
    have : Infinite K[ℚ] := rat_normOne_infinite
    have := Finite.of_injective e e.injective
    exact _root_.not_finite K[ℚ]
  exact nonempty_equiv_of_countable

private theorem counterexample_of_infinite_rows
    (χ : PontryaginDual K[ℚ] → PontryaginDual C[ℚ]) (hχ : IsSpectralBasepointChoice χ)
    (hinf : ∀ η, Infinite Z(χ η, (1 / 2 : ℝ))) :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates := by
  obtain ⟨ω⟩ := rat_character_enumeration
  have enum (k : ℕ) : ∃ t : ℕ ≃ Z(χ (ω k), (1 / 2 : ℝ)), Monotone (fun j ↦ |(t j).val|) := by
    let := hinf (ω k)
    exact enumerate_zeros _ _
  choose t ht using enum
  exact enumeration_contradicts ℚ _ (by norm_num) χ hχ ω t ht

-- The only analytic input below is stated for Mathlib Dirichlet characters.
-- Classification of the normalized rational rows is already in RationalExteriorZeros.
private theorem counterexample_of_primitive_dirichlet_zeros
    (hInf : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      {t : ℝ | χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0}.Infinite) :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates := by
  let q : (AdeleRing (𝓞 ℚ) ℚ)ˣ →ₜ* C[ℚ] := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  let n : C[ℚ] →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let p := ContinuousMonoidHom.id C[ℚ] / τ.comp n
  have hp (x : C[ℚ]) : p x ∈ K[ℚ] := by
    change ideleClassNorm ℚ (x / τ (ideleClassNorm ℚ x)) = 1
    rw [map_div, hτ, div_self']
  let r : C[ℚ] →ₜ* K[ℚ] := ⟨p.toMonoidHom.codRestrict _ hp, p.continuous.subtype_mk _⟩
  let χ (η : PontryaginDual K[ℚ]) := η.comp r
  apply counterexample_of_infinite_rows χ
  · intro η
    ext g : 1
    apply congrArg η
    apply Subtype.ext
    change g.val / τ (ideleClassNorm ℚ g.val) = g.val
    rw [show ideleClassNorm ℚ g.val = 1 from g.property, map_one, div_one]
  intro η
  have hnorm (t) : χ η (τ t) = 1 := by
    change η (r (τ t)) = 1
    rw [show r (τ t) = 1 from Subtype.ext (by
      change τ t / τ (ideleClassNorm ℚ (τ t)) = 1
      rw [hτ, div_self']), map_one]
  obtain ⟨N, hN, ψ, hprim, hL⟩ := exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ (χ η) hnorm
  let S := {t : ℝ | 0 < ord(χ η, point((1 / 2 : ℝ), t))}
  apply Set.Infinite.to_subtype (s := S)
  apply (hInf N ψ hprim).mono
  intro t ht
  let z := point((1 / 2 : ℝ), t)
  have hr : z.re = 1 / 2 := by simp [z]
  have h1 : z ≠ 1 := fun he ↦ by norm_num [he] at hr
  have hd : DifferentiableOn ℂ ψ.LFunction {1}ᶜ := fun w hw ↦
    (DirichletCharacter.differentiableAt_LFunction ψ w (.inl hw)).differentiableWithinAt
  have ha := hd.analyticAt (isOpen_compl_singleton.mem_nhds h1)
  have hzero : ψ.LFunction z = 0 := by
    simpa [z] using ht
  have hz := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg fun h ↦
    ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm hzero
  change 0 < ord(χ η, z)
  rw [← meromorphicOrderAt_finiteHeckeL_continuation (χ η) (meromorphic_dirichletLFunction ψ)
    (fun w ↦ (DirichletCharacter.LFunction_eq_LSeries ψ w.property).trans (hL w w.property).symm)
    (show 0 < z.re by rw [hr]; norm_num)]
  exact hz

end CofiniteCoordinates

/-- Classical input, not a statement of the paper. Every primitive Dirichlet character, the
character of conductor one included, has infinitely many zeros on the critical line: there
are infinitely many real `t` with `L(1/2 + it, χ) = 0`. For conductor one this is Hardy's
theorem of 1914 on the Riemann zeta function; for Dirichlet characters the refutation below
cites Bauer, Corollary 1. Stated as a proposition, so that what is proved from it takes it as a
hypothesis by name. -/
def PrimitiveDirichletLInfiniteCriticalZeros : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    {t : ℝ | χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0}.Infinite

/-- Paper: Theorem 10.4.3.1(2), pp. 467–468. The printed claim fails if every primitive
Dirichlet character has infinitely many zeros on the critical line
(`PrimitiveDirichletLInfiniteCriticalZeros`). Over ℚ take `a = 1/2` and `s = 4`. Use the
Dirichlet characters for the basepoints and put the trivial character first. Every row then
has infinitely many critical-line ordinates, finitely many in each bounded interval, so each
admits an absolute-value enumeration. The zeroth jets `(0,j,0)` escape each finite set while
their first coordinate is constant. -/
theorem Printed.spectralLineJet_cofinite_iff_coordinates_false_of_criticalZeros
    (h : PrimitiveDirichletLInfiniteCriticalZeros) :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates :=
  counterexample_of_primitive_dirichlet_zeros h

open Complex in
/-- For conductor one the Dirichlet L-function is the ordinary Riemann zeta function. -/
private theorem primitiveDirichletL_infinite_criticalZeros_modOne (χ : DirichletCharacter ℂ 1) :
    {t : ℝ | χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * I) = 0}.Infinite := by
  simp only [DirichletCharacter.LFunction_modOne_eq]
  refine HardyCriticalLine.positiveHardyZeroHeights_infinite.mono fun t ht ↦ ?_
  exact (HardyCriticalLine.hardyFunctionReal_eq_zero_iff t).mp ht.2

open scoped ComplexConjugate in
open Complex in
/-- Conjugation of Dirichlet coefficients carries the character to its inverse. The identity theorem
extends the conjugation formula from absolute convergence to the punctured plane. -/
private theorem primitiveDirichletL_infinite_criticalZeros_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z : ℂ) (hz : z ≠ 1) : conj (χ.LFunction (conj z)) = χ⁻¹.LFunction z := by
  have hf : AnalyticOnNhd ℂ (fun w ↦ conj (χ.LFunction (conj w))) {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun w hw ↦ (differentiableAt_conj_conj_iff.mpr <| χ.differentiableAt_LFunction _ <|
        Or.inl ((map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hw)).differentiableWithinAt)
      isOpen_compl_singleton
  have hg : AnalyticOnNhd ℂ χ⁻¹.LFunction {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun w hw ↦ (χ⁻¹.differentiableAt_LFunction _ (.inl hw)).differentiableWithinAt)
      isOpen_compl_singleton
  have hc (w : ℂ) (hw : 1 < w.re) : conj (χ.LFunction (conj w)) = χ⁻¹.LFunction w := by
    rw [χ.LFunction_eq_LSeries (by simpa using hw), χ⁻¹.LFunction_eq_LSeries hw]
    unfold LSeries
    rw [conj_tsum]
    refine tsum_congr fun n ↦ ?_
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    exact congrArg (fun a : ℂ ↦ a / (n : ℂ) ^ w) (MulChar.star_apply' χ (n : ZMod N))
  have hn : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt (g := Complex.re) (continuous_const (y := (1 : ℝ))) continuous_re).mem_nhds (by norm_num)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by simp : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
    (eventuallyEq_of_mem hn fun w hw ↦ hc w hw) hz

open scoped ComplexConjugate in
open Complex in
/-- Conjugation preserves the parity-dependent real Gamma factor. -/
private theorem primitiveDirichletL_infinite_criticalZeros_gamma_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z : ℂ) :
    χ⁻¹.gammaFactor (conj z) = conj (χ.gammaFactor z) := by
  rcases χ.even_or_odd with h | h
  · have h' : χ⁻¹.Even := by
      change χ⁻¹ (-1) = 1
      rw [← MulChar.star_apply', h, star_one]
    rw [h.gammaFactor_def, h'.gammaFactor_def, Gammaℝ_conj]
  · have h' : χ⁻¹.Odd := by
      change χ⁻¹ (-1) = -1
      rw [← MulChar.star_apply', h, star_neg, star_one]
    rw [h.gammaFactor_def, h'.gammaFactor_def, ← Gammaℝ_conj, map_add, map_one]

open Complex in
/-- The Gamma factor is nonzero in the right half-plane. -/
private theorem primitiveDirichletL_infinite_criticalZeros_gamma_ne {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

open Complex in
/-- Recover the completed L-function from its finite and archimedean factors. -/
private theorem primitiveDirichletL_infinite_criticalZeros_completion {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    χ.completedLFunction s = χ.gammaFactor s * χ.LFunction s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [χ.LFunction_eq_completed_div_gammaFactor _ (.inl h0)]
  field_simp [primitiveDirichletL_infinite_criticalZeros_gamma_ne χ hs]

open scoped ComplexConjugate in
open Complex in
/-- On the critical line the primitive functional equation relates each value to its conjugate. -/
private theorem primitiveDirichletL_infinite_criticalZeros_fe {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (t : ℝ) :
    let s := (1 / 2 : ℂ) + t * I
    χ.completedLFunction s = (N : ℂ) ^ (-(t : ℂ) * I) * χ.rootNumber * conj (χ.completedLFunction s) := by
  intro s
  have hre : s.re = 1 / 2 := by norm_num [s, Complex.add_re, Complex.mul_re]
  have hne : s ≠ 1 := by intro h; norm_num [h] at hre
  have hfe := hχ.completedLFunction_one_sub (1 - s)
  have hc : 1 - s = conj s := by
    dsimp only [s]
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have hh : 1 - s - 1 / 2 = - (t : ℂ) * I := by dsimp [s]; ring
  rw [sub_sub_cancel, hh, hc] at hfe
  refine hfe.trans ?_
  apply congrArg (fun w : ℂ ↦ (N : ℂ) ^ (-(t : ℂ) * I) * χ.rootNumber * w)
  rw [primitiveDirichletL_infinite_criticalZeros_completion _ (by rw [conj_re, hre]; norm_num),
      primitiveDirichletL_infinite_criticalZeros_completion _ (by rw [hre]; norm_num), map_mul, primitiveDirichletL_infinite_criticalZeros_gamma_conj]
  apply congrArg (fun w : ℂ ↦ conj (χ.gammaFactor s) * w)
  simpa using (primitiveDirichletL_infinite_criticalZeros_conj χ (conj s) ((map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hne)).symm

open scoped ComplexConjugate in
open Complex in
/-- Removing the root-number phase and half of the conductor twist gives a real value. -/
private theorem primitiveDirichletL_infinite_criticalZeros_phase {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (t : ℝ) :
    let s := (1 / 2 : ℂ) + t * I
    let θ := (t * Real.log N - χ.rootNumber.arg) / 2
    let H := exp ((θ : ℂ) * I) * χ.completedLFunction s
    conj H = H := by
  intro s θ H
  have heps : exp ((χ.rootNumber.arg : ℂ) * I) = χ.rootNumber := by
    simpa only [DirichletCharacter.norm_rootNumber hχ, ofReal_one, one_mul] using
      norm_mul_exp_arg_mul_I χ.rootNumber
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hlog : log (N : ℂ) = ((Real.log N : ℝ) : ℂ) := by
    rw [ofReal_log (Nat.cast_nonneg N), ofReal_natCast]
  have hfac : exp (((θ : ℂ)) * I) * ((N : ℂ) ^ (-(t : ℂ) * I) * χ.rootNumber) =
      conj (exp ((θ : ℂ) * I)) := by
    rw [cpow_def_of_ne_zero hN, hlog, ← heps, ← exp_add, ← exp_add, ← exp_conj, map_mul,
      conj_ofReal, conj_I]
    congr 1
    dsimp only [θ]
    push_cast
    ring
  change conj (exp ((θ : ℂ) * I) * χ.completedLFunction s) =
    exp ((θ : ℂ) * I) * χ.completedLFunction s
  rw [map_mul, ← hfac, mul_assoc]
  exact congrArg (fun w : ℂ ↦ exp ((θ : ℂ) * I) * w) (primitiveDirichletL_infinite_criticalZeros_fe hχ t).symm

open Complex in
/-- Normalizing a nonzero complex number near one changes its distance from one by at most a factor two. -/
private theorem primitiveDirichletL_infinite_criticalZeros_unit_sub_one {z : ℂ} (hz : z ≠ 0) :
    ‖z / (‖z‖ : ℂ) - 1‖ ≤ 2 * ‖z - 1‖ := by
  have hn : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have h : z / (‖z‖ : ℂ) - z = (z / (‖z‖ : ℂ)) * ((1 - ‖z‖ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have he : ‖z / (‖z‖ : ℂ) - z‖ ≤ ‖z - 1‖ := by
    rw [h, norm_mul, norm_div, norm_real, Real.norm_eq_abs, abs_norm,
      div_self (norm_ne_zero_iff.mpr hz), one_mul, norm_real, Real.norm_eq_abs, abs_sub_comm]
    simpa only [norm_one] using abs_norm_sub_norm_le z (1 : ℂ)
  simpa [two_mul] using (norm_sub_le_norm_sub_add_norm_sub (z / (‖z‖ : ℂ)) z 1).trans (add_le_add he le_rfl)

open scoped ComplexConjugate in
open Complex in
/-- At height `t` the odd Gamma phase differs from the even one rotated by `π / 4` by at most
`2 exp (−πt)`. The reflection formula reduces the comparison to normalizing `1 + i exp (−πt)`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_gamma_shift (t : ℝ) :
    let s := (1 / 2 : ℂ) + (t : ℂ) * I
    let u (z : ℂ) := z / (‖z‖ : ℂ)
    ‖u (Gammaℝ (s + 1)) - exp (((Real.pi / 4 : ℝ) : ℂ) * I) * u (Gammaℝ s)‖ ≤
      2 * Real.exp (-Real.pi * t) := by
  intro s u
  let q := Real.exp (-Real.pi * t)
  let θ := ((Real.pi / 4 : ℝ) : ℂ) * I
  let y := Real.pi * t / 2
  have hs : 1 - s = conj s := by
    dsimp only [s]
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have hc : cos (Real.pi * s / 2) =
      ((Real.exp y / 2 : ℝ) : ℂ) * exp (-θ) * (1 + I * (q : ℂ)) := by
    have h1 : ((Real.pi : ℂ) * s / 2) * I = -(y : ℂ) + θ := by
      dsimp [s, y, θ]
      push_cast
      ring_nf
      simp [I_sq]
      ring
    have h2 : -((Real.pi : ℂ) * s / 2) * I = (y : ℂ) - θ := by
      rw [neg_mul, h1]; ring
    have hrot : exp (2 * θ) = I := by
      rw [show 2 * θ = (Real.pi / 2 : ℂ) * I by dsimp [θ]; push_cast; ring, exp_pi_div_two_mul_I]
    have hq : ((q : ℝ) : ℂ) = exp (-2 * (y : ℂ)) := by
      dsimp only [q, y]; rw [ofReal_exp]; congr 1; push_cast; ring
    rw [cos, h1, h2]
    rw [hq, ← hrot]
    rw [ofReal_div (Real.exp y) 2, ofReal_ofNat, ofReal_exp y]
    have ha : exp (-↑y + θ) = exp (y : ℂ) * exp (-θ) * (exp (2 * θ) * exp (-2 * (y : ℂ))) := by
      simp only [← exp_add]
      congr 1
      ring
    have hb : exp (↑y - θ) = exp (y : ℂ) * exp (-θ) := by rw [sub_eq_add_neg, exp_add]
    rw [ha, hb]
    ring
  have hmul (a b : ℂ) : u (a * b) = u a * u b := by
    dsimp only [u]
    rw [norm_mul, ofReal_mul]
    exact div_mul_div_comm .. |>.symm
  have hnorm (z : ℂ) (hz : z ≠ 0) : ‖u z‖ = 1 := by
    dsimp only [u]; rw [norm_div, norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hz)]
  have hconj (z : ℂ) : u (conj z) = conj (u z) := by
    simp [u]
  have hinv (z : ℂ) : u z⁻¹ = (u z)⁻¹ := by
    simp [u, div_eq_mul_inv, mul_comm]
  have hg : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num [s, add_re, mul_re])
  have hq0 : (1 + I * (q : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hθ : ‖exp θ‖ = 1 := norm_exp_ofReal_mul_I _
  have hθn : ‖exp (-θ)‖ = 1 := by rw [exp_neg, norm_inv, hθ, inv_one]
  have huθ : u (exp (-θ)) = (exp θ)⁻¹ := by rw [show u (exp (-θ)) = exp (-θ) / (‖exp (-θ)‖ : ℂ) by rfl, hθn, ofReal_one, div_one, exp_neg]
  have hpos : 0 < Real.exp y / 2 := by positivity
  have hscale : u ((Real.exp y / 2 : ℝ) : ℂ) = 1 := by simp [u]
  have hreflect := congrArg u (Gammaℝ_one_sub_mul_Gammaℝ_one_add s)
  rw [hs, Gammaℝ_conj, add_comm (1 : ℂ) s, hmul, hconj, ← inv_eq_conj (hnorm _ hg), hc,
    hinv, hmul, hmul, hscale, one_mul, huθ, mul_inv_rev, inv_inv] at hreflect
  have hgo : u (Gammaℝ (s + 1)) = exp θ * u (Gammaℝ s) * conj (u (1 + I * (q : ℂ))) := by
    rw [← inv_eq_conj (hnorm _ hq0)]
    have hgu : u (Gammaℝ s) ≠ 0 := div_ne_zero hg (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hg))
    calc _ = u (Gammaℝ s) * ((u (Gammaℝ s))⁻¹ * u (Gammaℝ (s + 1))) := by field_simp
         _ = _ := by rw [hreflect]; ring
  rw [hgo, ← mul_sub_one, norm_mul, norm_mul, hθ, hnorm _ hg, one_mul, one_mul,
    show conj (u (1 + I * (q : ℂ))) - 1 = conj (u (1 + I * (q : ℂ)) - 1) by simp,
    norm_conj]
  calc _ ≤ 2 * ‖(1 + I * (q : ℂ)) - 1‖ := primitiveDirichletL_infinite_criticalZeros_unit_sub_one hq0
       _ = _ := by rw [add_sub_cancel_left, norm_mul, norm_I, one_mul, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

open Complex in
/-- The archimedean factor is continuous at all points of the critical line. -/
private theorem primitiveDirichletL_infinite_criticalZeros_gamma_cont {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Continuous (fun t ↦ χ.gammaFactor (HardyCriticalLine.criticalLinePoint t)) := by
  have hg (z : ℂ) (hz : 0 < z.re) : ContinuousAt Gammaℝ z := by
    have h := (differentiable_Gammaℝ_inv z).continuousAt.inv₀ (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
    simpa only [Pi.inv_def, inv_inv] using h
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs : 0 < (HardyCriticalLine.criticalLinePoint t).re := by
    norm_num [HardyCriticalLine.criticalLinePoint, add_re, mul_re]
  rcases χ.even_or_odd with h | h
  · simp_rw [h.gammaFactor_def]
    exact (hg _ hs).comp HardyCriticalLine.continuous_criticalLinePoint.continuousAt
  · simp_rw [h.gammaFactor_def]
    have hr : 0 < (HardyCriticalLine.criticalLinePoint t + 1).re := by
      rw [add_re, one_re]; linarith
    have hfun : ContinuousAt (fun u : ℝ ↦ HardyCriticalLine.criticalLinePoint u + (1 : ℂ)) t := by
      exact HardyCriticalLine.continuous_criticalLinePoint.continuousAt.add_const _
    exact (hg _ hr).comp (f := fun u : ℝ ↦ HardyCriticalLine.criticalLinePoint u + (1 : ℂ)) hfun

open Complex in
/-- A fixed unit and the same Stirling phase approximate the archimedean factor of either parity. -/
private theorem primitiveDirichletL_infinite_criticalZeros_gamma_asymptotic {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∃ b : ℂ, ‖b‖ = 1 ∧ ∀ t : ℝ, 1 ≤ t →
      let s := HardyCriticalLine.criticalLinePoint t
      ‖χ.gammaFactor s / (‖χ.gammaFactor s‖ : ℂ) -
        b * exp (I * (HardyCriticalLine.criticalLineStirlingPhase t : ℂ))‖ ≤ 3 / t := by
  let point := HardyCriticalLine.criticalLinePoint
  let u (z : ℂ) := z / (‖z‖ : ℂ)
  let W (t : ℝ) := exp (I * (HardyCriticalLine.criticalLineStirlingPhase t : ℂ))
  have heven (t : ℝ) (ht : 1 ≤ t) :
      ‖u (Gammaℝ (point t)) - W t‖ ≤ 11 / (16 * t) := by
    simpa only [point, HardyCriticalLine.criticalLinePoint, W, u, mul_comm I (t : ℂ)] using
      HardyCriticalLine.norm_criticalLineGammaR_unit_sub_exp_stirlingPhase_le ht
  rcases χ.even_or_odd with h | h
  · refine ⟨1, norm_one, fun t ht ↦ ?_⟩
    dsimp only
    rw [h.gammaFactor_def, one_mul]
    exact (heven t ht).trans (by apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr; linarith)
  · let b := exp (((Real.pi / 4 : ℝ) : ℂ) * I)
    have hbn : ‖b‖ = 1 := norm_exp_ofReal_mul_I _
    refine ⟨b, hbn, fun t ht ↦ ?_⟩
    dsimp only
    rw [h.gammaFactor_def]
    have hs := primitiveDirichletL_infinite_criticalZeros_gamma_shift t
    have hq : Real.exp (-Real.pi * t) ≤ 1 / t := by
      rw [neg_mul, Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos _) (by positivity)]
      have e := Real.add_one_le_exp (Real.pi * t)
      nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (show 0 ≤ t by linarith)]
    calc
      _ ≤ ‖u (Gammaℝ (point t + 1)) - b * u (Gammaℝ (point t))‖ +
          ‖b * u (Gammaℝ (point t)) - b * W t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖u (Gammaℝ (point t + 1)) - b * u (Gammaℝ (point t))‖ + ‖u (Gammaℝ (point t)) - W t‖ := by rw [← mul_sub, norm_mul, hbn, one_mul]
      _ ≤ 2 * (1 / t) + 11 / (16 * t) := add_le_add (hs.trans (by gcongr)) (heven t ht)
      _ ≤ 3 / t := by field_simp; linarith

open scoped ComplexConjugate in
open Complex in
/-- Construct a continuous real Hardy function with the same absolute value as `L` on the line.
Its phase differs from a fixed unit times the conductor-shifted Stirling phase by `O(1/t)`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_real_approx {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    ∃ H : ℝ → ℝ, Continuous H ∧
      (∀ t, |H t| = ‖χ.LFunction (HardyCriticalLine.criticalLinePoint t)‖) ∧
      ∃ b : ℂ, ‖b‖ = 1 ∧ ∀ t : ℝ, 1 ≤ t →
        ‖(H t : ℂ) - b * exp (I * ((HardyCriticalLine.criticalLineStirlingPhase t + (Real.log N / 2) * t : ℝ) : ℂ)) *
          χ.LFunction (HardyCriticalLine.criticalLinePoint t)‖ ≤
          (3 / t) * ‖χ.LFunction (HardyCriticalLine.criticalLinePoint t)‖ := by
  let s := HardyCriticalLine.criticalLinePoint
  let θ (t : ℝ) := (t * Real.log N - χ.rootNumber.arg) / 2
  let r (t : ℝ) := exp ((θ t : ℂ) * I)
  let g (t : ℝ) := χ.gammaFactor (s t)
  let L (t : ℝ) := χ.LFunction (s t)
  let Z (t : ℝ) := r t * (g t / (‖g t‖ : ℂ)) * L t
  have hs (t : ℝ) : (s t).re = 1 / 2 := by norm_num [s, HardyCriticalLine.criticalLinePoint, add_re, mul_re]
  have hn (t : ℝ) : g t ≠ 0 := primitiveDirichletL_infinite_criticalZeros_gamma_ne χ (by rw [hs]; norm_num)
  have hnorm (t : ℝ) : ‖r t‖ = 1 := norm_exp_ofReal_mul_I _
  have hreal (t : ℝ) : ((Z t).re : ℂ) = Z t := by
    apply conj_eq_iff_re.mp
    have hp := primitiveDirichletL_infinite_criticalZeros_phase hχ t
    change conj (r t * χ.completedLFunction (s t)) = r t * χ.completedLFunction (s t) at hp
    rw [primitiveDirichletL_infinite_criticalZeros_completion χ (by rw [hs]; norm_num)] at hp
    have he : Z t = (r t * (g t * L t)) / (‖g t‖ : ℂ) := by dsimp only [Z]; ring
    rw [he, map_div₀, conj_ofReal, hp]
  have hrc : Continuous r := by unfold r θ; fun_prop
  have hgc : Continuous g := primitiveDirichletL_infinite_criticalZeros_gamma_cont χ
  have hLc : Continuous L := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : s t ≠ 1 := by intro h; have e := hs t; norm_num [h] at e
    exact (χ.differentiableAt_LFunction _ (.inl hne)).continuousAt.comp
      HardyCriticalLine.continuous_criticalLinePoint.continuousAt
  have hZ : Continuous Z := (hrc.mul (hgc.div (continuous_ofReal.comp hgc.norm) (fun t ↦ ofReal_ne_zero.mpr <| norm_ne_zero_iff.mpr (hn t)))).mul hLc
  refine ⟨(fun t ↦ (Z t).re), continuous_re.comp hZ, fun t ↦ ?_, ?_⟩
  · change |(Z t).re| = ‖L t‖
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hreal, show Z t = _ from rfl, norm_mul, norm_mul, norm_div, hnorm,
      norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr (hn _)), one_mul, one_mul]
  · obtain ⟨b, hb, he⟩ := primitiveDirichletL_infinite_criticalZeros_gamma_asymptotic χ
    let a := exp (((-χ.rootNumber.arg / 2 : ℝ) : ℂ) * I)
    have han : ‖a‖=1 := norm_exp_ofReal_mul_I _
    refine ⟨a * b, by rw [norm_mul, han, hb, one_mul], fun t ht ↦ ?_⟩
    have heq : a * b * exp (I * ((HardyCriticalLine.criticalLineStirlingPhase t + (Real.log N / 2) * t : ℝ) : ℂ)) =
        r t * (b * exp (I * (HardyCriticalLine.criticalLineStirlingPhase t : ℂ))) := by
      dsimp [a, r, θ]
      rw [mul_right_comm, ← exp_add, mul_comm b, ← mul_assoc, ← exp_add]
      congr 2
      push_cast
      ring
    rw [hreal, heq]
    change ‖r t * (g t / (‖g t‖ : ℂ)) * L t - (r t * (b * _)) * L t‖ ≤ _
    rw [← sub_mul, ← mul_sub, norm_mul, norm_mul, hnorm, one_mul]
    exact mul_le_mul_of_nonneg_right (he t ht) (norm_nonneg _)

open Complex in
/-- On writing `u = x^(−d)`, the derivative of `u^(s/d)` on `0 < u ≤ 1` is bounded by `‖s‖/d`.
This bounds differences of Dirichlet powers by a telescoping real majorant. -/
private theorem primitiveDirichletL_infinite_criticalZeros_power_variation {s : ℂ} {d a b : ℝ}
    (hd : 0 < d) (hs : d ≤ s.re) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(a : ℂ) ^ (-s) - (b : ℂ) ^ (-s)‖ ≤
      (‖s‖ / d) * (a ^ (-d) - b ^ (-d)) := by
  let r := s / (d : ℂ)
  have hr : 1 ≤ r.re := by
    simpa [r, le_div_iff₀ hd] using hs
  have hr0 : r ≠ 0 := by intro h; norm_num [h] at hr
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hbp : 0 < b := hap.trans_le hab
  have hrepr {x : ℝ} (hx : 0 < x) : ((x ^ (-d) : ℝ) : ℂ) ^ r = (x : ℂ) ^ (-s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne'),
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ← ofReal_log (Real.rpow_nonneg hx.le _),
      Real.log_rpow hx, ← ofReal_log hx.le]
    congr 1
    dsimp only [r]
    push_cast
    field_simp [ofReal_ne_zero.mpr hd.ne']
  have hlow : 0 < b ^ (-d) := Real.rpow_pos_of_pos hbp _
  have h10 : a ^ (-d) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha (neg_nonpos.mpr hd.le)
  have hba : b ^ (-d) ≤ a ^ (-d) := Real.rpow_le_rpow_of_nonpos hap hab (neg_nonpos.mpr hd.le)
  have hdiff (x : ℝ) (hx : x ∈ Icc (b ^ (-d)) (a ^ (-d))) :=
    (hasDerivAt_ofReal_cpow_const (hlow.trans_le hx.1).ne' hr0).hasDerivWithinAt (s := Icc (b ^ (-d)) (a ^ (-d)))
  have hbnd (x : ℝ) (hx : x ∈ Ico (b ^ (-d)) (a ^ (-d))) :
      ‖r * (x : ℂ) ^ (r - 1)‖ ≤ ‖s‖ / d := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (hlow.trans_le hx.1)]
    calc _ ≤ ‖r‖ * 1 := by
            gcongr
            apply Real.rpow_le_one
            · exact (hlow.trans_le hx.1).le
            · exact hx.2.le.trans h10
            · simpa using sub_nonneg.mpr hr
         _ = _ := by simp [r, Real.norm_of_nonneg hd.le]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hdiff hbnd (a ^ (-d)) ⟨hba, le_rfl⟩
  simpa only [hrepr hap, hrepr hbp] using h

open Complex Finset in
/-- Each full period of a nonprincipal character sums to zero, and the remaining partial sum has norm
at most its modulus. -/
private theorem primitiveDirichletL_infinite_criticalZeros_character_partial {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∀ n : ℕ, ‖∑ i ∈ range n, χ ((i : ZMod N) + 1)‖ ≤ N := by
  let S (n : ℕ) := ∑ i ∈ range n, χ ((i : ZMod N) + 1)
  have htotal : S N = 0 := by
    rw [show S N = ∑ i : Fin N, χ (((i : ℕ) : ZMod N) + 1) from (Fin.sum_univ_eq_sum_range _ _).symm]
    have he (i : Fin N) : ((i : ℕ) : ZMod N) = ZMod.finEquiv N i := by
      cases N with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ n =>
        exact ZMod.natCast_zmod_val (n := n + 1) i
    simp_rw [he]
    calc _ = ∑ a : ZMod N, χ (a + 1) := (ZMod.finEquiv N).toEquiv.sum_comp (fun a ↦ χ (a + 1))
         _ = ∑ a : ZMod N, χ a := Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) χ
         _ = 0 := χ.sum_eq_zero_of_ne_one hχ
  have hperiod : Function.Periodic S N := by
    intro n
    induction n with
    | zero => simpa [S] using htotal
    | succ n ih =>
      rw [Nat.succ_add, show S (n + N).succ = S (n + N) + χ ((((n + N : ℕ) : ZMod N)) + 1) from sum_range_succ ..,
        show S n.succ = S n + χ ((n : ZMod N) + 1) from sum_range_succ .., ih]
      simp
  intro n
  have hmod : S n = S (n % N) := by
    have h := hperiod.nsmul (n / N) (n % N)
    simpa [nsmul_eq_mul, Nat.mul_comm (n / N), Nat.mod_add_div] using h
  change ‖S n‖ ≤ N
  rw [hmod]
  calc ‖S (n % N)‖ ≤ ∑ i ∈ range (n % N), ‖χ ((i : ZMod N) + 1)‖ := norm_sum_le ..
       _ ≤ ∑ _i ∈ range (n % N), (1 : ℝ) := sum_le_sum fun i _ ↦ χ.norm_le_one _
       _ ≤ N := by simp; exact_mod_cast (Nat.mod_lt n (NeZero.pos N)).le

open Complex Finset in
/-- The tail of the telescoping majorant starting at index `k` equals `(k+1)^(−d)`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_variation_sum {d : ℝ} (hd : 0 < d) (k : ℕ) :
    HasSum (fun i : ℕ ↦ ((i + k + 1 : ℕ) : ℝ) ^ (-d) - ((i + 1 + k + 1 : ℕ) : ℝ) ^ (-d))
      (((k + 1 : ℕ) : ℝ) ^ (-d)) := by
  let v (i : ℕ) := ((i + k + 1 : ℕ) : ℝ) ^ (-d)
  have hv : Tendsto v atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop hd).comp <|
      tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp (tendsto_add_atTop_nat k))
  have hm (i : ℕ) : v (i + 1) ≤ v i := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega) (neg_nonpos.mpr hd.le)
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun i ↦ sub_nonneg.mpr (hm i)) _).mpr
  have ht : Tendsto (fun n ↦ v 0 - v n) atTop (𝓝 (v 0)) := by simpa using tendsto_const_nhds.sub hv
  convert! ht using 1
  · funext n
    exact Finset.sum_range_sub' v n
  · simp [v]

open Complex Finset in
/-- A nonprincipal Dirichlet L-function on `σ > 0` differs from its first `n` terms by at most
`N(1 + ‖s‖/σ)(n+1)^(−σ)`. Summation by parts gives a locally normally convergent continuation. -/
private theorem primitiveDirichletL_infinite_criticalZeros_truncate {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖χ.LFunction s - ∑ i ∈ range n, χ ((i : ZMod N) + 1) * ((i + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      N * (1 + ‖s‖ / s.re) * ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
  classical
  let P (k : ℕ) := ∑ i ∈ range k, χ ((i : ZMod N) + 1)
  let w (z : ℂ) (i : ℕ) := ((i + 1 : ℕ) : ℂ) ^ (-z)
  let v (d : ℝ) (i : ℕ) := ((i + 1 : ℕ) : ℝ) ^ (-d)
  let D (i : ℕ) (z : ℂ) := P (i + 1) * (w z i - w z (i + 1))
  let F (z : ℂ) := ∑' i, D i z
  have hP (k : ℕ) : ‖P k‖ ≤ N := primitiveDirichletL_infinite_criticalZeros_character_partial χ hχ k
  have hpos (d : ℝ) (i : ℕ) : 0 < v d i := Real.rpow_pos_of_pos (by positivity) _
  have hm {d : ℝ} (hd : 0 < d) (i : ℕ) : 0 ≤ v d i - v d (i + 1) := by
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega) (neg_nonpos.mpr hd.le)
  have hv {d : ℝ} (hd : 0 < d) (k : ℕ) :
      HasSum (fun i : ℕ ↦ v d (i + k) - v d (i + k + 1)) (v d k) := by
    simpa only [v, add_right_comm] using primitiveDirichletL_infinite_criticalZeros_variation_sum hd k
  have hb {d b : ℝ} {z : ℂ} (hd : 0 < d) (hz : d ≤ z.re) (hb : ‖z‖ ≤ b) (i : ℕ) :
      ‖D i z‖ ≤ (N * (b / d)) * (v d i - v d (i + 1)) := by
    have h := primitiveDirichletL_infinite_criticalZeros_power_variation (s := z) (a := ((i + 1 : ℕ) : ℝ)) (b := ((i + 1 + 1 : ℕ) : ℝ))
      hd hz (by norm_cast; omega) (by norm_cast; omega)
    have h' : ‖w z i - w z (i + 1)‖ ≤ (‖z‖ / d) * (v d i - v d (i + 1)) := by simpa only [w, v, ofReal_natCast] using h
    calc ‖D i z‖ = ‖P (i + 1)‖ * ‖w z i - w z (i + 1)‖ := norm_mul ..
         _ ≤ (N : ℝ) * ((b / d) * (v d i - v d (i + 1))) := mul_le_mul (hP _) (h'.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb hd.le) (hm hd i))) (norm_nonneg _) (Nat.cast_nonneg _)
         _ = _ := by ring
  have hsum {z : ℂ} (hz : 0 < z.re) : Summable (fun i ↦ D i z) := by
    refine Summable.of_norm_bounded (g := fun i ↦ _ * (v z.re i - v z.re (i + 1))) ?_ (hb hz le_rfl le_rfl)
    simpa using ((hv hz 0).summable.mul_left (N * (‖z‖ / z.re)))
  have hfinite (z : ℂ) (k : ℕ) :
      ∑ i ∈ range k, χ ((i : ZMod N) + 1) * w z i = (∑ i ∈ range k, D i z) + P k * w z k := by
    induction k with
    | zero => simp [P]
    | succ k ih =>
      rw [sum_range_succ, sum_range_succ, ih]
      simp only [D, show P (k + 1) = P k + χ ((k : ZMod N) + 1) from sum_range_succ ..]
      ring
  have hlarge (z : ℂ) (hz : 1 < z.re) : χ.LFunction z = F z := by
    have hL : HasSum (fun n : ℕ ↦ LSeries.term (fun n ↦ χ (n : ZMod N)) z n) (χ.LFunction z) := by
      rw [χ.LFunction_eq_LSeries hz]; exact (χ.LSeriesSummable_of_one_lt_re hz).hasSum
    have hL' : HasSum (fun i : ℕ ↦ χ ((i : ZMod N) + 1) * w z i) (χ.LFunction z) := by
      have h := (hasSum_nat_add_iff' 1).mpr hL
      convert! h using 1
      · funext i
        dsimp only [w]
        rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero i), div_eq_mul_inv, cpow_neg]
        simp only [Nat.cast_succ]
      · simp
    have hbd : Tendsto (fun k ↦ P k * w z k) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      have ht : Tendsto (fun k : ℕ ↦ v z.re k) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (zero_lt_one.trans hz)).comp <|
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
      apply squeeze_zero (fun _ ↦ norm_nonneg _) ?_ (by simpa using ht.const_mul (N : ℝ))
      intro k
      rw [norm_mul]
      apply mul_le_mul (hP _) _ (norm_nonneg _) (Nat.cast_nonneg _)
      have hp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      simpa [v, w, neg_re] using (norm_cpow_eq_rpow_re_of_pos hp (-z)).le
    apply tendsto_nhds_unique hL'.tendsto_sum_nat
    simp_rw [hfinite]
    simpa [F] using ((hsum (zero_lt_one.trans hz)).hasSum.tendsto_sum_nat.add hbd)
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
    intro z hz
    let d := z.re / 2
    let B := ‖z‖ + 1
    let U := {w : ℂ | d < w.re} ∩ {w : ℂ | ‖w‖ < B}
    have hd : 0 < d := half_pos hz
    have hop : IsOpen U := (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
    have hzU : z ∈ U := ⟨show z.re / 2 < z.re from half_lt_self (show 0 < z.re from hz), show ‖z‖ < ‖z‖ + 1 by linarith⟩
    have hF' : DifferentiableOn ℂ F U := by
      refine differentiableOn_tsum_of_summable_norm (u := fun i ↦ N * (B / d) * (v d i - v d (i + 1))) ?_ ?_ hop ?_
      · simpa using ((hv hd 0).summable.mul_left (N * (B / d)))
      · intro i
        have ha (k : ℕ) : Differentiable ℂ (fun z ↦ w z k) := by
          dsimp only [w]
          exact differentiable_neg.const_cpow (.inl (by exact_mod_cast Nat.succ_ne_zero k))
        exact (((ha i).sub (ha (i + 1))).const_mul (P (i + 1))).differentiableOn
      · intro i w hw
        exact hb hd hw.1.le hw.2.le i
    exact ((hF' z hzU).differentiableAt (hop.mem_nhds hzU)).differentiableWithinAt
  have hFχ : AnalyticOnNhd ℂ χ.LFunction {z : ℂ | 0 < z.re} :=
    (χ.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have hagree : χ.LFunction s = F s := by
    have hconn : IsPreconnected {z : ℂ | 0 < z.re} := convex_halfSpace_re_gt 0 |>.isPreconnected
    have h2 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt (continuous_const (y := (1 : ℝ))) continuous_re).mem_nhds (by norm_num)
    exact hFχ.eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hU) hconn
      (by norm_num : (2 : ℂ) ∈ {w : ℂ | 0 < w.re}) (eventuallyEq_of_mem h2 fun w hw ↦ hlarge w hw) hs
  change ‖χ.LFunction s - ∑ i ∈ range n, χ ((i : ZMod N) + 1) * w s i‖ ≤ _
  rw [hagree, hfinite, show F s = (∑ i ∈ range n, D i s) + ∑' i, D (i + n) s from ((hsum hs).sum_add_tsum_nat_add n).symm]
  have htail : ‖∑' i, D (i + n) s‖ ≤ (N * (‖s‖ / s.re)) * v s.re n := by
    exact tsum_of_norm_bounded ((hv hs n).mul_left (N * (‖s‖ / s.re))) (fun i ↦ hb hs le_rfl le_rfl (i + n))
  have hpn : ‖P n * w s n‖ ≤ N * v s.re n := by
    rw [norm_mul]
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    refine mul_le_mul (hP _) ?_ (norm_nonneg _) (Nat.cast_nonneg _)
    simpa [v, w] using (norm_cpow_eq_rpow_re_of_pos hp (-s)).le
  rw [add_sub_add_left_eq_sub]
  exact (norm_sub_le _ _).trans ((add_le_add htail hpn).trans_eq (by dsimp [v]; ring))

open Finset in
/-- Reindex a finite sum over the positive integers. -/
private theorem primitiveDirichletL_infinite_criticalZeros_sum_shift {E : Type*} [AddCommMonoid E] (f : ℕ → E) (m : ℕ) :
    ∑ i ∈ range m, f (i + 1) = ∑ n ∈ Finset.Icc 1 m, f n := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]

open Complex Finset HardyCriticalLine in
/-- Split a weighted sum at an integer threshold and sum the majorants `C/√n` on both parts. -/
private theorem primitiveDirichletL_infinite_criticalZeros_split_sum (z : ℕ → ℂ) (X D : ℕ) {C E : ℝ} (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hall : ∀ n ∈ Finset.Icc 1 X, ‖z n‖ ≤ C * (1 / Real.sqrt n))
    (hhi : ∀ n ∈ Finset.Icc 1 X, D < n → ‖z n‖ ≤ E * (1 / Real.sqrt n)) :
    ‖∑ n ∈ Finset.Icc 1 X, z n‖ ≤ 2 * C * Real.sqrt D + 2 * E * Real.sqrt X := by
  classical
  let L := (Finset.Icc 1 X).filter fun n ↦ n ≤ D
  let H := (Finset.Icc 1 X).filter fun n ↦ ¬n ≤ D
  have hsub : L ⊆ Finset.Icc 1 D := by
    intro n hn
    obtain ⟨hm, hD⟩ := mem_filter.mp hn
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hD⟩
  have hs (A : Finset ℕ) (B : ℕ) {J : ℝ} (hJ : 0 ≤ J) (hp : A ⊆ Finset.Icc 1 B)
      (hb : ∀ n ∈ A, ‖z n‖ ≤ J * (1 / Real.sqrt n)) :
      ‖∑ n ∈ A, z n‖ ≤ 2 * J * Real.sqrt B := by
    calc ‖∑ n ∈ A, z n‖ ≤ ∑ n ∈ A, ‖z n‖ := norm_sum_le ..
         _ ≤ ∑ n ∈ A, J * (1 / Real.sqrt n) := sum_le_sum hb
         _ = J * ∑ n ∈ A, 1 / Real.sqrt n := (mul_sum ..).symm
         _ ≤ J * (2 * Real.sqrt B) := by
             apply mul_le_mul_of_nonneg_left _ hJ
             exact (sum_le_sum_of_subset_of_nonneg hp fun n _ _ ↦ by positivity).trans
               (sum_Icc_one_div_sqrt_le_two_mul_sqrt B)
         _ = _ := by ring
  have hl := hs L D hC hsub (fun n hn ↦ hall n (mem_filter.mp hn).1)
  have hh := hs H X hE (filter_subset ..) (fun n hn ↦ hhi n (mem_filter.mp hn).1 (lt_of_not_ge (mem_filter.mp hn).2))
  rw [← sum_filter_add_sum_filter_not (Finset.Icc 1 X) (fun n ↦ n ≤ D)]
  exact (norm_add_le _ _).trans (add_le_add hl hh)

open Complex Finset HardyCriticalLine in
/-- An unphased Dirichlet monomial with `log n ≥ K > 0` has dyadic integral bounded by `4/(K√n)`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_raw_mode {n : ℕ} (hn : 0 < n) {K T : ℝ}
    (hK : 0 < K) (hT : 0 < T) (hnK : K ≤ Real.log n) :
    ‖∫ t in T..2 * T, (n : ℂ) ^ (-criticalLinePoint t)‖ ≤ (4 / K) * (1 / Real.sqrt n) := by
  let F (t : ℝ) := -t * Real.log n
  have hd (t : ℝ) : HasDerivAt F (-Real.log n) t := by
    simpa [F] using ((hasDerivAt_id t).neg.mul_const (Real.log n))
  have he := norm_integral_firstDerivativeOscillation_le_four_div_c1 (F := F)
    (F' := fun _ ↦ -Real.log n) (a := T) (b := 2 * T) (by linarith) hK
    (fun t _ ↦ hd t) continuousOn_const monotoneOn_const
    (fun _ _ ↦ by simpa [abs_of_pos (hK.trans_le hnK)] using hnK)
  have hlog : log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by rw [ofReal_log (Nat.cast_nonneg n), ofReal_natCast]
  have hm (t : ℝ) : (n : ℂ) ^ (-criticalLinePoint t) =
      ((1 / Real.sqrt n : ℝ) : ℂ) * firstDerivativeOscillation F t := by
    rw [cpow_neg_criticalLinePoint_eq_mode hn, cpow_neg_criticalLinePoint_zero hn, hlog]
    dsimp only [firstDerivativeOscillation, F]
    congr 2
    push_cast
    ring
  simp_rw [hm]
  rw [intervalIntegral.integral_const_mul, norm_mul, norm_real, Real.norm_of_nonneg (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right he (by positivity)

open Complex Finset HardyCriticalLine in
/-- After inserting the shifted Stirling phase, a Dirichlet monomial has the usual Hardy oscillation
with a linear term. Its fixed unit factor drops out of the norm. -/
private theorem primitiveDirichletL_infinite_criticalZeros_phased_mode (c : ℝ) {n : ℕ} (hn : 0 < n) {T : ℝ} (hT : 0 < T) :
    ‖∫ t in T..2 * T, exp (I * ((criticalLineStirlingPhase t + c * t : ℝ) : ℂ)) *
      (n : ℂ) ^ (-criticalLinePoint t)‖ =
      (1 / Real.sqrt n) * ‖∫ t in T..2 * T, firstDerivativeOscillation (fun u ↦ hardyOscillatoryPhase n u + c * u) t‖ := by
  have hab : T ≤ 2 * T := by linarith
  have heq : (∫ t in T..2 * T, exp (I * ((criticalLineStirlingPhase t + c * t : ℝ) : ℂ)) *
      (n : ℂ) ^ (-criticalLinePoint t)) =
      ∫ t in T..2 * T, (((1 / Real.sqrt n : ℝ) : ℂ) * exp (-I * (Real.pi / 8))) *
        firstDerivativeOscillation (fun u ↦ hardyOscillatoryPhase n u + c * u) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : 0 < t := hT.trans_le ((uIcc_of_le hab ▸ ht : t ∈ Icc T (2 * T)).1)
    push_cast
    rw [mul_add, exp_add, mul_right_comm, exp_stirlingPhase_mul_cpow_eq_hardyOscillatoryMode hn ht']
    dsimp only [firstDerivativeOscillation]
    push_cast
    rw [mul_add, exp_add]
    ring
  rw [heq, intervalIntegral.integral_const_mul, norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)]
  have h : ‖exp (-I * (Real.pi / 8))‖ = 1 := by rw [norm_exp]; norm_num
  rw [h, mul_one]

open Complex Finset HardyCriticalLine in
/-- The shifted Hardy modes retain curvature `1/(2t)`; beyond `B√T` their slopes have magnitude
at least `K`. The two derivative estimates control both ranges on `[T,2T]`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_modes (c K : ℝ) (hK : 0 < K) :
    ∃ B : ℝ, 0 < B ∧ ∀ {n : ℕ}, 0 < n → ∀ {T : ℝ}, 0 < T →
      let F (t : ℝ) := hardyOscillatoryPhase n t + c * t
      ‖∫ t in T..2 * T, firstDerivativeOscillation F t‖ ≤ 20 * Real.sqrt T ∧
        (B * Real.sqrt T ≤ n → ‖∫ t in T..2 * T, firstDerivativeOscillation F t‖ ≤ 4 / K) := by
  let B := Real.exp (c + K)
  have hB : 0 < B := Real.exp_pos _
  refine ⟨B, hB, ?_⟩
  intro n hn T hT F
  let G (t : ℝ) := hardyOscillatoryPhaseDeriv n t + c
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hab : T ≤ 2 * T := by linarith
  have hp (t : ℝ) (ht : t ∈ uIcc T (2 * T)) : 0 < t := hT.trans_le ((uIcc_of_le hab ▸ ht : t ∈ Icc T (2 * T)).1)
  have hd (t : ℝ) (ht : t ∈ uIcc T (2 * T)) : HasDerivAt F (G t) t := by
    simpa [F, G, Pi.add_def] using (hasDerivAt_hardyOscillatoryPhase hn (hp t ht)).add ((hasDerivAt_id t).const_mul c)
  have hd' (t : ℝ) (ht : t ∈ uIcc T (2 * T)) : HasDerivAt G (1 / (2 * t)) t :=
    (hasDerivAt_hardyOscillatoryPhaseDeriv hn (hp t ht)).add_const _
  have hmono : MonotoneOn G (uIcc T (2 * T)) := fun x hx y hy hxy ↦
    add_le_add (monotoneOn_hardyOscillatoryPhaseDeriv hn (hp x hx) (hp y hy) hxy) le_rfl
  constructor
  · refine (norm_integral_firstDerivativeOscillation_le_ten_div_sqrt
      (r := 1 / (4 * T)) hab (by positivity) hd hd' hmono ?_).trans_eq ?_
    · intro t ht
      have htpos := hp t ht
      rw [uIcc_of_le hab] at ht
      rw [abs_of_pos (by positivity)]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      linarith [ht.2]
    · rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by norm_num)]
      rw [show Real.sqrt 4 = 2 by exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)]
      field_simp [Real.sqrt_pos.mpr hT]
      ring
  · intro hbn
    apply norm_integral_firstDerivativeOscillation_le_four_div_c1 hab hK hd
      (fun t ht ↦ (hd' t ht).continuousAt.continuousWithinAt) hmono
    intro t ht
    have htpos := hp t ht
    rw [uIcc_of_le hab] at ht
    have hsq : B ^ 2 * T ≤ (n : ℝ) ^ 2 := by
      have h := (sq_le_sq₀ (mul_nonneg hB.le (Real.sqrt_nonneg _)) hn'.le).mpr hbn
      rwa [mul_pow, Real.sq_sqrt hT.le] at h
    have hratio : t / (2 * Real.pi * (n : ℝ) ^ 2) ≤ 1 / B ^ 2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      calc t * B ^ 2 ≤ (2 * T) * B ^ 2 := by gcongr; exact ht.2
           _ = 2 * (B ^ 2 * T) := by ring
           _ ≤ 2 * (n : ℝ) ^ 2 := by gcongr
           _ ≤ 1 * (2 * Real.pi * (n : ℝ) ^ 2) := by nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sq_nonneg (n : ℝ))]
    have hl := Real.log_le_log (by positivity : 0 < t / (2 * Real.pi * (n : ℝ) ^ 2)) hratio
    rw [one_div, Real.log_inv, Real.log_pow, show Real.log B = c + K from Real.log_exp _] at hl
    have hg : G t ≤ -K := by dsimp [G, hardyOscillatoryPhaseDeriv]; norm_num at hl; linarith
    rw [abs_of_neg (hg.trans_lt (neg_lt_zero.mpr hK))]
    linarith

open Complex Finset HardyCriticalLine in
/-- At `T = k⁴` the unphased mean of a Dirichlet polynomial with first coefficient one contains
the main term `T`. Its error and the entire phased mean are at most `40Dk³ + (8/K)√m`. -/
private theorem primitiveDirichletL_infinite_criticalZeros_polynomial_means (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (ha1 : a 1 = 1)
    (c K : ℝ) (hK : 0 < K) :
    ∃ D : ℕ, 0 < D ∧ ∀ (k m : ℕ), 0 < k → 0 < m →
      let T : ℝ := (k : ℝ) ^ 4
      let P (t : ℝ) := ∑ n ∈ Finset.Icc 1 m, a n * (n : ℂ) ^ (-criticalLinePoint t)
      let E (t : ℝ) := exp (I * ((criticalLineStirlingPhase t + c * t : ℝ) : ℂ))
      let R := 40 * (D : ℝ) * (k : ℝ) ^ 3 + (8 / K) * Real.sqrt m
      ‖(∫ t in T..2 * T, P t) - (T : ℂ)‖ ≤ R ∧ ‖∫ t in T..2 * T, E t * P t‖ ≤ R := by
  obtain ⟨B, hB, hmode⟩ := primitiveDirichletL_infinite_criticalZeros_modes c K hK
  obtain ⟨D, hD⟩ := exists_nat_gt (max 1 (max B (Real.exp K)))
  have hD1 : 1 < (D : ℝ) := (le_max_left ..).trans_lt hD
  have hDB : B ≤ (D : ℝ) := (le_max_left ..).trans ((le_max_right ..).trans hD.le)
  have hDK : Real.exp K ≤ D := (le_max_right ..).trans ((le_max_right ..).trans hD.le)
  refine ⟨D, by exact_mod_cast (zero_lt_one.trans hD1), ?_⟩
  intro k m hk hm T P E R
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hT : 0 < T := by dsimp [T]; positivity
  have hab : T ≤ 2 * T := by linarith
  have hroot : Real.sqrt T = (k : ℝ) ^ 2 := by
    change Real.sqrt ((k : ℝ) ^ 4) = _
    rw [show (k : ℝ) ^ 4 = ((k : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg _)]
  let l := (D * k) ^ 2
  have hl : Real.sqrt l = (D : ℝ) * k := by dsimp [l]; push_cast; rw [Real.sqrt_sq (by positivity)]
  have hsplit {n : ℕ} (hn : l < n) : B * Real.sqrt T ≤ n ∧ K ≤ Real.log n := by
    have hln : ((D : ℝ) * k) ^ 2 < n := by exact_mod_cast hn
    have hD2 : (D : ℝ) ≤ (D : ℝ) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hD1.le) (Nat.cast_nonneg D)]
    have h1 : 1 ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
    have h2 : (D : ℝ) ^ 2 * (k : ℝ) ^ 2 ≤ n := by simpa only [mul_pow] using hln.le
    refine ⟨by rw [hroot]; exact (mul_le_mul_of_nonneg_right (hDB.trans hD2) (sq_nonneg _)).trans h2, ?_⟩
    have hn0 : 0 < (n : ℝ) := (Real.exp_pos K).trans_le (hDK.trans (hD2.trans ((le_mul_of_one_le_right (sq_nonneg _) h1).trans h2)))
    exact (Real.le_log_iff_exp_le hn0).mpr (hDK.trans (hD2.trans ((le_mul_of_one_le_right (sq_nonneg _) h1).trans h2)))
  let w (n : ℕ) (t : ℝ) := (n : ℂ) ^ (-criticalLinePoint t)
  have hint (n : ℕ) (hn : 0 < n) : IntervalIntegrable (w n) volume T (2 * T) := (continuous_cpow_neg_criticalLinePoint hn).intervalIntegrable ..
  have hintE (n : ℕ) (hn : 0 < n) : IntervalIntegrable (fun t ↦ E t * w n t) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos : 0 < t := hT.trans_le ((uIcc_of_le hab ▸ ht : t ∈ Icc T (2 * T)).1)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul _ (continuous_cpow_neg_criticalLinePoint hn).continuousAt
    dsimp only [E, criticalLineStirlingPhase]
    fun_prop (disch := positivity)
  have hlimit (z : ℕ → ℂ)
      (hal : ∀ n ∈ Finset.Icc 1 m, ‖z n‖ ≤ (20 * Real.sqrt T) * (1 / Real.sqrt n))
      (hhi : ∀ n ∈ Finset.Icc 1 m, l < n → ‖z n‖ ≤ (4 / K) * (1 / Real.sqrt n)) :
      ‖∑ n ∈ Finset.Icc 1 m, z n‖ ≤ R := by
    apply (primitiveDirichletL_infinite_criticalZeros_split_sum z m l (by positivity) (by positivity) hal hhi).trans_eq
    dsimp only [R]
    rw [hl, hroot]
    ring
  constructor
  · let z (n : ℕ) := a n * (∫ t in T..2 * T, w n t) - (if n = 1 then (T : ℂ) else 0)
    have hsum : (∫ t in T..2 * T, P t) - (T : ℂ) = ∑ n ∈ Finset.Icc 1 m, z n := by
      dsimp only [z, P]
      rw [intervalIntegral.integral_finsetSum (fun n hn ↦ (hint n (mem_Icc.mp hn).1).const_mul _), sum_sub_distrib]
      simp_rw [intervalIntegral.integral_const_mul]
      simp [Nat.ne_of_gt hm]
    rw [hsum]
    have h1 : z 1 = 0 := by
      dsimp [z, w]; simp [ha1, Algebra.smul_def]; ring
    have hne {n : ℕ} (hn : n ≠ 1) : ‖z n‖ ≤ ‖∫ t in T..2 * T, w n t‖ := by
      simpa [z, hn, norm_mul] using mul_le_mul_of_nonneg_right (ha n) (norm_nonneg (∫ t in T..2 * T, w n t))
    refine hlimit z ?_ ?_
    · intro n hn
      by_cases he : n = 1
      · subst n; rw [h1, norm_zero]; positivity
      · have hpos := (mem_Icc.mp hn).1
        refine (hne he).trans ((norm_integral_cpow_neg_criticalLinePoint_le (show 2 ≤ n by omega) T).trans ?_)
        rw [hroot, div_eq_mul_one_div]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
    · intro n hn hnl
      have hpos := (mem_Icc.mp hn).1
      by_cases he : n = 1
      · subst n; rw [h1, norm_zero]; positivity
      · exact (hne he).trans (primitiveDirichletL_infinite_criticalZeros_raw_mode hpos hK hT (hsplit hnl).2)
  · let z (n : ℕ) := a n * ∫ t in T..2 * T, E t * w n t
    have hsum : (∫ t in T..2 * T, E t * P t) = ∑ n ∈ Finset.Icc 1 m, z n := by
      change (∫ t in T..2 * T, E t * ∑ n ∈ Finset.Icc 1 m, a n * w n t) = _
      simp only [mul_sum]
      simp_rw [show ∀ (n : ℕ) (t : ℝ), E t * (a n * w n t) = a n * (E t * w n t) by intros; ring]
      rw [intervalIntegral.integral_finsetSum (fun n hn ↦ (hintE n (mem_Icc.mp hn).1).const_mul _)]
      simp only [z, intervalIntegral.integral_const_mul]
    rw [hsum]
    have hz {n : ℕ} (hn : 0 < n) :
        ‖z n‖ ≤ (1 / Real.sqrt n) * ‖∫ t in T..2 * T, firstDerivativeOscillation (fun u ↦ hardyOscillatoryPhase n u + c * u) t‖ := by
      rw [← primitiveDirichletL_infinite_criticalZeros_phased_mode c hn hT, show z n = a n * _ from rfl, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ha n)
    refine hlimit z ?_ ?_
    · intro n hn
      have hp := (mem_Icc.mp hn).1
      simpa only [mul_comm (20 * Real.sqrt T)] using (hz hp).trans (mul_le_mul_of_nonneg_left (hmode hp hT).1 (by positivity))
    · intro n hn hnl
      have hp := (mem_Icc.mp hn).1
      simpa only [mul_comm (4 / K)] using (hz hp).trans (mul_le_mul_of_nonneg_left ((hmode hp hT).2 (hsplit hnl).1) (by positivity))

open Complex Finset HardyCriticalLine in
/-- On `[T,2T]` with `T = k⁴`, a cutoff of size `(AT)²` gives uniform error at most `1/16`.
The shorter cutoff `T` gives a pointwise bound of order `√T` for the L-function. -/
private theorem primitiveDirichletL_infinite_criticalZeros_window_approx {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∃ A : ℕ, 0 < A ∧ ∀ k : ℕ, 0 < k →
      let T : ℝ := (k : ℝ) ^ 4
      let m := (A * k ^ 4) ^ 2
      let P (t : ℝ) := ∑ n ∈ Finset.Icc 1 m, χ (n : ZMod N) * (n : ℂ) ^ (-criticalLinePoint t)
      ∀ t ∈ Icc T (2 * T), ‖χ.LFunction (criticalLinePoint t) - P t‖ ≤ 1 / 16 ∧
        ‖χ.LFunction (criticalLinePoint t)‖ ≤ (2 + 7 * (N : ℝ)) * (k : ℝ) ^ 2 := by
  let A := 128 * (N + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro k hk T m P t ht
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hT1 : 1 ≤ T := one_le_pow₀ hk1
  have htp : 0 ≤ t := (zero_le_one.trans hT1).trans ht.1
  have hs : (criticalLinePoint t).re = 1 / 2 := by norm_num [criticalLinePoint, add_re, mul_re]
  have hsn : ‖criticalLinePoint t‖ ≤ 3 * T := by
    dsimp only [criticalLinePoint]
    apply (norm_add_le _ _).trans
    rw [norm_div, norm_one, norm_ofNat, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg htp]
    linarith [ht.2]
  let Q (m' : ℕ) := ∑ n ∈ Finset.Icc 1 m', χ (n : ZMod N) * (n : ℂ) ^ (-criticalLinePoint t)
  have hcut (j : ℕ) (hj : 0 < j) :
      ‖χ.LFunction (criticalLinePoint t) - Q (j ^ 2)‖ ≤ 7 * N * T / j := by
    have h := primitiveDirichletL_infinite_criticalZeros_truncate χ hχ (s := criticalLinePoint t) (by rw [hs]; norm_num) (j ^ 2)
    have hq : (∑ i ∈ range (j ^ 2), χ ((i : ZMod N) + 1) * ((i + 1 : ℕ) : ℂ) ^ (-criticalLinePoint t)) = Q (j ^ 2) := by
      simpa [Q] using primitiveDirichletL_infinite_criticalZeros_sum_shift (fun n : ℕ ↦ χ (n : ZMod N) * (n : ℂ) ^ (-criticalLinePoint t)) (j ^ 2)
    rw [hq, hs, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow] at h
    have hj' : 0 < (j : ℝ) := by exact_mod_cast hj
    have hr : (j : ℝ) ≤ Real.sqrt ((j ^ 2 + 1 : ℕ) : ℝ) := by
      apply (Real.le_sqrt (Nat.cast_nonneg _) (by positivity)).mpr
      push_cast
      linarith
    calc _ ≤ N * (1 + ‖criticalLinePoint t‖/(1 / 2)) * (Real.sqrt ((j ^ 2 + 1 : ℕ) : ℝ))⁻¹ := h
         _ ≤ N * (7 * T) * (j : ℝ)⁻¹ := by
           apply mul_le_mul _ ((inv_le_inv₀ (hj'.trans_le hr) hj').mpr hr) (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by positivity)
           apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
           linarith
         _ = _ := by ring
  have hqnorm (j : ℕ) : ‖Q j‖ ≤ 2 * Real.sqrt j := by
    refine (norm_sum_le _ _).trans ((sum_le_sum (g := fun n : ℕ ↦ 1 / Real.sqrt n) ?_).trans (sum_Icc_one_div_sqrt_le_two_mul_sqrt j))
    intro n hn
    rw [norm_mul, norm_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hn).1]
    exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  constructor
  · refine (hcut (A * k ^ 4) (by positivity)).trans ?_
    dsimp only [T, A]
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (pow_nonneg (Nat.cast_nonneg (α := ℝ) k) 4)]
  · have hkroot : Real.sqrt ((k ^ 2) ^ 2 : ℕ) = (k : ℝ) ^ 2 := by push_cast; rw [Real.sqrt_sq (sq_nonneg _)]
    have h := (norm_sub_norm_le (χ.LFunction (criticalLinePoint t)) (Q ((k ^ 2) ^ 2))).trans (hcut (k ^ 2) (by positivity))
    have hp := hqnorm ((k ^ 2) ^ 2)
    rw [hkroot] at hp
    have hdiv : 7 * (N : ℝ) * T / ((k ^ 2 : ℕ) : ℝ) = 7 * N * (k : ℝ) ^ 2 := by
      dsimp only [T]; push_cast; field_simp [show (k : ℝ) ≠ 0 by positivity]
    rw [hdiv] at h
    linarith

open Complex in
/-- Integrating a uniform error bound over a dyadic interval costs its length. -/
private theorem primitiveDirichletL_infinite_criticalZeros_integral_error {f g : ℝ → ℂ} {T B : ℝ} (hT : 0 < T)
    (hf : IntervalIntegrable f volume T (2 * T)) (hg : IntervalIntegrable g volume T (2 * T))
    (h : ∀ t ∈ Icc T (2 * T), ‖f t - g t‖ ≤ B) :
    ‖(∫ t in T..2 * T, f t) - ∫ t in T..2 * T, g t‖ ≤ B * T := by
  rw [← intervalIntegral.integral_sub hf hg]
  have hab : T ≤ 2 * T := by linarith
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := B) (fun t ht ↦ ?_)).trans_eq
  · rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    ring
  · rw [uIoc_of_le hab] at ht
    exact h t ⟨ht.1.le, ht.2⟩

open Complex Finset HardyCriticalLine in
/-- If the Hardy function had finitely many zeros it would have constant sign on a sufficiently
late dyadic interval. Its small signed mean would then dominate the large unphased mean. -/
private theorem primitiveDirichletL_infinite_criticalZeros_nonprincipal {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    {t : ℝ | χ.LFunction ((1 / 2 : ℂ) + (t : ℂ) * I) = 0}.Infinite := by
  obtain ⟨H, hH, hnormH, b, hb, hphase⟩ := primitiveDirichletL_infinite_criticalZeros_real_approx hχ
  obtain ⟨A, hA, hcut⟩ := primitiveDirichletL_infinite_criticalZeros_window_approx χ hχ1
  let c := Real.log N / 2
  let K := 256 * (A : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨D, hD, hmeans⟩ := primitiveDirichletL_infinite_criticalZeros_polynomial_means (fun n : ℕ ↦ χ (n : ZMod N))
    (fun n ↦ χ.norm_le_one _) (by simp) c K hK
  by_contra hnot
  obtain ⟨R, hR⟩ := (Set.not_infinite.mp hnot).bddAbove
  obtain ⟨k, hbig⟩ := exists_nat_gt (max R (max (1280 * (D : ℝ)) (48 * (2 + 7 * (N : ℝ)))))
  have hkR : R < (k : ℝ) := (le_max_left ..).trans_lt hbig
  have hkD : 1280 * (D : ℝ) ≤ k := (le_max_left ..).trans ((le_max_right ..).trans hbig.le)
  have hkN : 48 * (2 + 7 * (N : ℝ)) ≤ k := (le_max_right ..).trans ((le_max_right ..).trans hbig.le)
  have hk1 : 1 ≤ (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hk : 0 < k := by exact_mod_cast hk1
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (Nat.cast_nonneg k)]
  let T : ℝ := (k : ℝ) ^ 4
  let m := (A * k ^ 4) ^ 2
  have hm : 0 < m := by dsimp [m]; positivity
  have hT1 : 1 ≤ T := one_le_pow₀ hk1
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hab : T ≤ 2 * T := by linarith
  have hkT : (k : ℝ) ≤ T := by dsimp [T]; simpa using pow_le_pow_right₀ hk1 (by norm_num : 1 ≤ 4)
  let L (t : ℝ) := χ.LFunction (criticalLinePoint t)
  let P (t : ℝ) := ∑ n ∈ Finset.Icc 1 m, χ (n : ZMod N) * (n : ℂ) ^ (-criticalLinePoint t)
  let E (t : ℝ) := exp (I * ((criticalLineStirlingPhase t + c * t : ℝ) : ℂ))
  have hEn (t : ℝ) : ‖E t‖ = 1 := by dsimp only [E]; rw [mul_comm]; exact norm_exp_ofReal_mul_I _
  have hiL : Continuous L := (χ.differentiable_LFunction hχ1).continuous.comp continuous_criticalLinePoint
  have hiP : Continuous P := continuous_finsetSum _ fun n hn ↦ (continuous_cpow_neg_criticalLinePoint (mem_Icc.mp hn).1).const_mul _
  have hiEP : IntervalIntegrable (fun t ↦ b * (E t * P t)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have htpos : 0 < t := hT.trans_le ((uIcc_of_le hab ▸ ht : t ∈ Icc T (2 * T)).1)
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.const_mul
    apply ContinuousAt.mul _ hiP.continuousAt
    dsimp only [E, criticalLineStirlingPhase]
    fun_prop (disch := positivity)
  have hcut' (t : ℝ) (ht : t ∈ Icc T (2 * T)) :
      ‖L t - P t‖ ≤ 1 / 16 ∧ ‖L t‖ ≤ (2 + 7 * (N : ℝ)) * (k : ℝ) ^ 2 := hcut k hk t ht
  have hsigned (t : ℝ) (ht : t ∈ Icc T (2 * T)) : ‖(H t : ℂ) - b * (E t * P t)‖ ≤ 1 / 8 := by
    have htp := hT.trans_le ht.1
    have he := hphase t (hT1.trans ht.1)
    have hc := hcut' t ht
    have hfrac : (3 / t) * (2 + 7 * (N : ℝ)) * (k : ℝ) ^ 2 ≤ 1 / 16 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (div_le_iff₀ htp).mpr
      have hsq := mul_le_mul_of_nonneg_right (hkN.trans hk2) (sq_nonneg (k : ℝ))
      have htt : (k : ℝ) ^ 4 ≤ t := ht.1
      nlinarith [htt]
    have he' : ‖(H t : ℂ) - b * E t * L t‖ ≤ 1 / 16 := by
      exact he.trans ((mul_le_mul_of_nonneg_left hc.2 (by positivity)).trans (by linarith [hfrac]))
    have hdiff : ‖b * E t * L t - b * (E t * P t)‖ ≤ 1 / 16 := by
      rw [← mul_assoc b, ← mul_sub, norm_mul, norm_mul, hb, hEn, one_mul, one_mul]
      exact hc.1
    linarith [norm_sub_le_norm_sub_add_norm_sub (H t : ℂ) (b * E t * L t) (b * (E t * P t))]
  have herrL := primitiveDirichletL_infinite_criticalZeros_integral_error hT (hiL.intervalIntegrable ..) (hiP.intervalIntegrable ..)
    (fun t ht ↦ (hcut' t ht).1)
  have herrH := primitiveDirichletL_infinite_criticalZeros_integral_error hT ((continuous_ofReal.comp hH).intervalIntegrable ..) hiEP hsigned
  have hmn := hmeans k m hk hm
  have hsmall : 40 * (D : ℝ) * (k : ℝ) ^ 3 + (8 / K) * Real.sqrt m ≤ T / 16 := by
    have hms : Real.sqrt m = (A : ℝ) * T := by dsimp [m,T]; push_cast; rw [Real.sqrt_sq (by positivity)]
    have hK' : (8 / K) * Real.sqrt m = T / 32 := by rw [hms]; dsimp [K]; field_simp; ring
    rw [hK']
    have hp := mul_le_mul_of_nonneg_right hkD (pow_nonneg (Nat.cast_nonneg k) 3)
    dsimp [T]
    nlinarith
  have hraw : ‖(∫ t in T..2 * T, P t) - (T : ℂ)‖ ≤ T / 16 := hmn.1.trans hsmall
  have hphis : ‖∫ t in T..2 * T, b * (E t * P t)‖ ≤ T / 16 := by
    rw [intervalIntegral.integral_const_mul, norm_mul, hb, one_mul]
    exact hmn.2.trans hsmall
  have hno (t : ℝ) (ht : t ∈ Icc T (2 * T)) : H t ≠ 0 := by
    intro he
    have h := hnormH t
    rw [he, abs_zero, eq_comm, norm_eq_zero] at h
    have hb' : t ≤ R := hR (show t ∈ {u : ℝ | χ.LFunction ((1 / 2 : ℂ) + (u : ℂ) * I) = 0} from h)
    linarith [ht.1]
  have habs := abs_integral_eq_integral_abs_of_constant_sign hab
    (nonnegative_or_nonpositive_on_Icc_of_continuous_ne_zero hH hab hno)
  have hcomp : ‖∫ t in T..2 * T, L t‖ ≤ ‖∫ t in T..2 * T, (H t : ℂ)‖ := by
    rw [intervalIntegral.integral_ofReal, norm_real, Real.norm_eq_abs, habs]
    simpa only [hnormH] using (intervalIntegral.norm_integral_le_integral_norm (f := L) hab)
  have h1 := norm_sub_norm_le (T : ℂ) (∫ t in T..2 * T, P t)
  rw [norm_sub_rev, norm_real, Real.norm_of_nonneg hT.le] at h1
  have h2 := norm_sub_norm_le (∫ t in T..2 * T, P t) (∫ t in T..2 * T, L t)
  rw [norm_sub_rev] at h2
  have h3 := norm_sub_norm_le (∫ t in T..2 * T, (H t : ℂ)) (∫ t in T..2 * T, b * (E t * P t))
  linarith only [h1.trans hraw, h2.trans herrL, h3.trans herrH, hcomp, hphis, hT]

/-- Classical input: every primitive Dirichlet character has infinitely many zeros on the
critical line (Hardy 1914 for the Riemann zeta function; Bauer, Corollary 1, for Dirichlet
characters). This classical theorem supplies the arithmetic input for the refutation of
Theorem 10.4.3.1(2) as printed. -/
theorem primitiveDirichletL_infinite_criticalZeros : PrimitiveDirichletLInfiniteCriticalZeros := by
  intro N _ χ hχ
  by_cases hN : N = 1
  · subst N
    exact primitiveDirichletL_infinite_criticalZeros_modOne χ
  · apply primitiveDirichletL_infinite_criticalZeros_nonprincipal hχ
    intro he
    have hc : 1 = N := by simpa only [DirichletCharacter.IsPrimitive, he,
      DirichletCharacter.conductor_one] using hχ
    exact hN hc.symm

/-- Paper: Theorem 10.4.3.1(2), pp. 467–468. Over ℚ take `a = 1/2` and
`s = 4`. Use the Dirichlet characters for the basepoints and put the
trivial character first. Every primitive Dirichlet row has infinitely many
critical-line ordinates (Bauer, Corollary 1), finitely many in each bounded
interval, so each admits an absolute-value enumeration. The zeroth jets
`(0,j,0)` escape each finite set while their first coordinate is constant.
The proof is `Printed.spectralLineJet_cofinite_iff_coordinates_false_of_criticalZeros` applied to
the classical theorem `primitiveDirichletL_infinite_criticalZeros`. -/
theorem Printed.spectralLineJet_cofinite_iff_coordinates_false :
    ¬ Printed.spectralLineJet_cofinite_iff_coordinates :=
  Printed.spectralLineJet_cofinite_iff_coordinates_false_of_criticalZeros
    primitiveDirichletL_infinite_criticalZeros

/-- Paper: (10.4.3.21), p. 469. As printed: a finite rectangle has image
given by the finite sum over an initial segment of the lexicographic jet
order. This records the finiteness of the stated summation domain for every
endpoint. The kernel `spectralKernelRectangle` sums over the two coordinate
bounds (ERRATA F198). -/
def Printed.spectralLineJet_lexInitialSegment_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → 1 < s →
    ∀ (χ : PontryaginDual C₁[F] → PontryaginDual C[F]), IsSpectralBasepointChoice χ →
      ∀ (ω : ℕ ≃ PontryaginDual C₁[F])
        (t : ∀ k : ℕ, ℕ ≃ lineZeros(χ (ω k), a)),
        (∀ k, Monotone (fun j ↦ |(t k j).val|)) →
        ∀ i₀ : lineJetIndices(χ, ω, t, a, s),
          {i : lineJetIndices(χ, ω, t, a, s) | i = i₀ ∨
            Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) i.val i₀.val}.Finite

/-- Paper: (10.4.3.21), p. 469. Over ℚ take `a = 1/2`, `s = 4` and
the enumeration of Dirichlet rows with the trivial character first.
The lexicographic initial segment through `(1,0,0)` includes every
zeroth jet `(0,j,0)` of the trivial row. -/
theorem Printed.spectralLineJet_lexInitialSegment_finite_false :
    ¬ Printed.spectralLineJet_lexInitialSegment_finite := by
  classical
  intro hfin
  apply Printed.spectralLineJet_cofinite_iff_coordinates_false
  intro F _ _ a s ha hs χ hχ ω t ht i
  let J := lineJetIndices(χ, ω, t, a, s)
  have hcut : 0 < ⌊(s - 1) / 2 + 1⌋₊ := Nat.floor_pos.mpr (by linarith)
  have ordpos (k n : ℕ) : 0 < (zeroOrder(χ (ω k), a, ((t k) n).val)).untop₀.toNat := by
    let z : ℂ := (a : ℂ) + (((t k) n).val : ℂ) * Complex.I
    let L := continuedCompletedHeckeL (χ (ω k))
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec (χ (ω k))
    have htwo : meromorphicOrderAt L 2 ≠ ⊤ := by
      intro h
      have hp : 0 < meromorphicOrderAt L 2 := h ▸ WithTop.coe_lt_top (0 : ℤ)
      have hb := completedHeckeL_continuation_zeros (χ (ω k)) _ hL heq
        (by norm_num : 0 < (2 : ℂ).re) hp
      norm_num at hb
    have hne : meromorphicOrderAt L z ≠ ⊤ := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ _) (mem_univ z) htwo
    have hp : 0 < meromorphicOrderAt L z := ((t k) n).property
    rw [← WithTop.coe_untop₀_of_ne_top hne] at hp
    have hint : 0 < (meromorphicOrderAt L z).untop₀ := WithTop.coe_lt_coe.mp hp
    change 0 < (meromorphicOrderAt L z).untop₀.toNat
    omega
  let j (k n : ℕ) : J := ⟨(k, n, 0), lt_min (ordpos k n) hcut⟩
  have hinj : Injective (j 0) := fun m n he ↦ congrArg (fun v : J ↦ v.val.2.1) he
  have hf := hfin F a s ha hs χ hχ ω t ht (j 1 0)
  apply False.elim
  apply (Set.infinite_range_of_injective hinj)
  apply hf.subset
  rintro _ ⟨n, rfl⟩
  exact Or.inr (Prod.Lex.left _ _ (Nat.zero_lt_succ 0))

end RiemannMasullo
