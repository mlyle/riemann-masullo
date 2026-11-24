module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic

/-! # §11.2: the printed intersection of principal-value kernels -/

@[expose] public noncomputable section

open Function Filter Topology IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (logIdeleClassNorm F)

/-- Paper: Proof of Proposition 11.2.0.1(2), p. 485. As printed: On each norm-one
isotype the range of the completed 0-line principal value is the common kernel
of the Mellin evaluations and derivatives through order |S₀| − 1 at every zero
of the reciprocal partial Euler product. `OrbitalJetIndex` uses the individual
multiplicities and `globalThetaSobolevPrincipalValue_range_closure` compares
closures. See ERRATA F163. -/
def Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual C𝔽(F)) (s : ℝ) (hs : 0 ≤ s), 2 * (S₀.card : ℝ) ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let hI := le_rfl (a := (0 : ℝ))
    let W := CompactIntervalSobolev μ logNorm(F) 0 0 s
    let H := globalThetaSobolev F 0 hI hs
    let P := globalThetaSobolevPrincipalValue F S₀ 0 hs
    let K := (ideleClassNorm F).ker
    let ω := χ.comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* C𝔽(F))
    let Wω := actionIsotype ((hardySobolevTranslation μ m𝔽(F) 0 0 s hI hs).comp K.subtype) ω
    ∀ u : Wω,
      (∃ f : H, (f : W) ∈ Wω ∧ (P f : W) = u.val) ↔
        ∀ (ε : ℂ), reciprocalPartialHeckeEulerProduct χ S₀ ε = 0 →
          ∀ j : ℕ, j < S₀.card →
            (∫ g, u.val g * ideleClassNormTwist χ ε g * (logNorm(F) g : ℂ) ^ j ∂μ) = 0

section
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => C𝔽(F)
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "ωOf(" χ ")" => (χ : PontryaginDual C𝔽).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μ₁" => normOneIdeleClassTamagawaMeasure F

private theorem classMellin_log_exp_bound (x s t : ℝ) (ht : s - 1 < t ∧ t < s + 1) :
    Real.exp (x * t) * |x| ≤ Real.exp (x * (s - 2)) + Real.exp (x * (s + 2)) := by
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  by_cases h : 0 ≤ x
  · apply le_add_of_nonneg_of_le (Real.exp_pos _).le
    rw [Real.exp_le_exp, abs_of_nonneg h]
    nlinarith [mul_nonneg h (sub_nonneg.mpr ht.2.le)]
  · apply le_add_of_le_of_nonneg _ (Real.exp_pos _).le
    rw [Real.exp_le_exp, abs_of_nonpos (le_of_not_ge h)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) (sub_nonneg.mpr ht.1.le)]

private theorem classMellin_hasDerivAt (χ : PontryaginDual C𝔽) (f : C𝔽 → ℂ)
    (hint : ∀ w : ℂ, Integrable (fun g ↦ f g * ideleClassNormTwist χ w g) μ𝔽)
    (z : ℂ) :
    HasDerivAt (fun w ↦ ∫ g, f g * ideleClassNormTwist χ w g ∂μ𝔽)
      (∫ g, f g * ideleClassNormTwist χ z g * (logNorm(F) g : ℂ) ∂μ𝔽) z := by
  let N (g : C𝔽) : ℝ := (ideleClassNorm F g).val
  let l (g : C𝔽) := Real.log (N g)
  let A (w : ℂ) (g : C𝔽) := f g * ideleClassNormTwist χ w g
  let B (w : ℂ) (g : C𝔽) := A w g * (l g : ℂ)
  have hN (g : C𝔽) : 0 < N g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hA (w : ℂ) (g : C𝔽) : ‖A w g‖ = ‖f g‖ * Real.exp (l g * w.re) := by
    change ‖f g * ((χ g : ℂ) * (N g : ℂ) ^ w)‖ = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN g),
      Real.rpow_def_of_pos (hN g)]
  let U := Complex.re ⁻¹' Ioo (z.re - 1) (z.re + 1)
  have hU : U ∈ 𝓝 z := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds ⟨by linarith, by linarith⟩
  let D (g : C𝔽) := ‖A (z - 2) g‖ + ‖A (z + 2) g‖
  have hD : Integrable D μ𝔽 := (hint (z - 2)).norm.add (hint (z + 2)).norm
  have hb (g : C𝔽) (w : ℂ) (hw : w ∈ U) : ‖B w g‖ ≤ D g := by
    change ‖A w g * (l g : ℂ)‖ ≤ ‖A (z - 2) g‖ + ‖A (z + 2) g‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hA, hA, hA, ← mul_add, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa using classMellin_log_exp_bound (l g) z.re w.re hw
  have hl : Continuous l := (NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log (fun g ↦ (hN g).ne')
  have hd (g : C𝔽) (w : ℂ) : HasDerivAt (fun v ↦ A v g) (B w g) w := by
    have hp := (Complex.hasStrictDerivAt_const_cpow (y := w) (Or.inl (Complex.ofReal_ne_zero.mpr (hN g).ne'))).hasDerivAt
    change HasDerivAt (fun v : ℂ ↦ f g * ((χ g : ℂ) * (N g : ℂ) ^ v))
      ((f g * ((χ g : ℂ) * (N g : ℂ) ^ w)) * (Real.log (N g) : ℂ)) w
    simpa only [← Complex.ofReal_log (hN g).le, mul_assoc] using (hp.const_mul (χ g : ℂ)).const_mul (f g)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (.of_forall fun w ↦ (hint w).aestronglyMeasurable) (hint z)
    ((hint z).aestronglyMeasurable.mul (Complex.continuous_ofReal.comp hl).aestronglyMeasurable)
    (.of_forall hb) hD (.of_forall fun g w _ ↦ hd g w)).2

private theorem polarClassMellin_integral (χ : PontryaginDual C𝔽) (z : ℂ) (f : ℬ₀) :
    Integrable (fun g ↦ homogeneousAdelicTheta (ωOf(χ)) f.val g * ideleClassNormTwist χ z g) μ𝔽 ∧
      (∫ g, homogeneousAdelicTheta (ωOf(χ)) f.val g * ideleClassNormTwist χ z g ∂μ𝔽) =
        ((μ₁ univ).toReal : ℂ) * globalIdelicZFunction f.val (ideleClassNormTwist χ z) := by
  let ν := normOneIdeleClassTamagawaMeasure F
  let μ := ideleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let ω : PontryaginDual C₁ := ωOf(χ)
  let c := ideleClassNormTwist χ z
  let W (g : C𝔽) := adelicTheta f.val g * c g
  let A (g : C𝔽) := homogeneousAdelicTheta ω f.val g * c g
  let Φ (p : C𝔽 × C₁) := W (p.2.val * p.1)
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  have hi : Integrable W μ :=
    globalThetaMellinIntegral_integrable_of_vanishing f.val hf.1 hf.2 c
  have hP : AEStronglyMeasurable Φ (μ.prod ν) := by
    apply Continuous.aestronglyMeasurable
    have hmul : Continuous (fun p : C𝔽 × C₁ ↦ p.2.val * p.1) := by fun_prop
    exact ((adelicTheta f.val).continuous.mul c.continuous).comp hmul
  have hp : Integrable Φ (μ.prod ν) := by
    apply (integrable_prod_iff' hP).mpr
    constructor
    · filter_upwards with u
      change Integrable (fun g ↦ W (u.val * g)) μ
      have hm : Measure.map (fun g : C𝔽 ↦ u.val * g) μ = μ := map_mul_left_eq_self μ u.val
      have hw : AEStronglyMeasurable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by
        rw [hm]; exact hi.aestronglyMeasurable
      have hi' : Integrable W (Measure.map (fun g : C𝔽 ↦ u.val * g) μ) := by rw [hm]; exact hi
      have hmul : Continuous (fun g : C𝔽 ↦ u.val * g) := by fun_prop
      have h := (integrable_map_measure hw hmul.measurable.aemeasurable).mp hi'
      exact h
    · have he : (fun u : C₁ ↦ ∫ g, ‖Φ (g,u)‖ ∂μ) = fun _ ↦ ∫ g, ‖W g‖ ∂μ := by
        funext u
        change (∫ g, ‖W (u.val * g)‖ ∂μ) = _
        exact integral_mul_left_eq_self (fun g ↦ ‖W g‖) u.val
      rw [he]
      exact integrable_const _
  have ha (g : C𝔽) : (∫ u, Φ (g,u) ∂ν) = A g := by
    have hu (u : C₁) : c u.val = (ω u : ℂ) := by
      change (χ u.val : ℂ) * (((ideleClassNorm F u.val : ℝ≥0) : ℝ) : ℂ) ^ z = _
      simp only [MonoidHom.mem_ker.mp u.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
      rfl
    change (∫ u, adelicTheta f.val (u.val * g) * c (u.val * g) ∂ν) = _
    simp_rw [map_mul c, hu, ← mul_assoc, integral_mul_const]
    rfl
  refine ⟨hp.integral_prod_left.congr (Filter.Eventually.of_forall ha), ?_⟩
  change (∫ g, A g ∂μ) = ((ν univ).toReal : ℂ) * globalIdelicZFunction f c
  rw [← integral_congr_ae (Filter.Eventually.of_forall ha), ← integral_prod Φ hp, integral_prod_symm Φ hp]
  have he (u : C₁) : (∫ g, Φ (g,u) ∂μ) = ∫ g, W g ∂μ := integral_mul_left_eq_self W u.val
  simp_rw [he, integral_const]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  exact congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f.val hf.1 hf.2) c

/-- On a polar test the principal-value multiplier identity extends across every
point, since both sides are continuous. -/
private theorem polarClassMellin_pvMultiplier (χ : PontryaginDual C𝔽) (T : Finset V)
    (f : ℬ₀) (z : ℂ) :
    globalIdelicZFunction (adelePrincipalValue F T f.val) (ideleClassNormTwist χ z) =
      reciprocalPartialHeckeEulerProduct χ T z * globalIdelicZFunction f.val (ideleClassNormTwist χ z) := by
  have h₁ := (globalIdelicZFunction_entire_of_vanishing _
    (adelePrincipalValue_mem_polarSubspace T f) χ).continuous.continuousAt (x := z)
  have h₂ := (globalIdelicZFunction_entire_of_vanishing _ f.property χ).continuous.continuousAt (x := z)
  have hfactor (v : V) : Differentiable ℂ (fun w ↦ (finiteHeckeEulerFactor χ v w)⁻¹) := by
    unfold finiteHeckeEulerFactor
    split_ifs
    · simp_rw [inv_inv]
      have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
      exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_neg.const_cpow (Or.inl hq)))
    · simp_rw [inv_one]
      exact differentiable_const _
  have hprod : Continuous (reciprocalPartialHeckeEulerProduct χ T) := by
    unfold reciprocalPartialHeckeEulerProduct
    exact (Differentiable.fun_finsetProd (𝕜 := ℂ) fun v _ ↦ hfactor v).continuous
  exact ((h₁.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ((hprod.continuousAt (x := z)).mul h₂)).mp
    ((globalPrincipalValueConverse_mellin T χ f.val).filter_mono (nhdsNE_le_codiscrete z))).eq_of_nhds

private theorem polarClassMellin_hasDerivAt (χ : PontryaginDual C𝔽) (z : ℂ) (f : ℬ₀) :
    HasDerivAt (fun w ↦ ∫ g, homogeneousAdelicTheta (ωOf(χ)) f.val g *
      ideleClassNormTwist χ w g ∂μ𝔽) (∫ g, homogeneousAdelicTheta (ωOf(χ)) f.val g *
      ideleClassNormTwist χ z g * (logNorm(F) g : ℂ) ∂μ𝔽) z :=
  classMellin_hasDerivAt χ _ (fun w ↦ (polarClassMellin_integral χ w f).1) z

private theorem polarClassMellin_firstMoment_ne_zero (χ : PontryaginDual C𝔽) (T : Finset V)
    (f : ℬ₀) (z d : ℂ) (hz : reciprocalPartialHeckeEulerProduct χ T z = 0)
    (hd : HasDerivAt (reciprocalPartialHeckeEulerProduct χ T) d z) (hd0 : d ≠ 0)
    (hf : globalIdelicZFunction f.val (ideleClassNormTwist χ z) ≠ 0) :
    (∫ g, homogeneousAdelicTheta (ωOf(χ)) (adelePrincipalValue F T f.val) g *
      ideleClassNormTwist χ z g * (logNorm(F) g : ℂ) ∂μ𝔽) ≠ 0 := by
  let h : ℬ₀ := ⟨_, adelePrincipalValue_mem_polarSubspace T f⟩
  let E := reciprocalPartialHeckeEulerProduct χ T
  let Z (w : ℂ) := globalIdelicZFunction f.val (ideleClassNormTwist χ w)
  let m : ℂ := ((μ₁ univ).toReal : ℂ)
  have hm : m ≠ 0 := by
    let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
    let : (μ₁).IsHaarMeasure :=
      (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
    exact Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'
  have hEq : (fun w ↦ ∫ g, homogeneousAdelicTheta (ωOf(χ)) h.val g *
      ideleClassNormTwist χ w g ∂μ𝔽) = fun w ↦ m * (E w * Z w) := by
    funext w
    rw [(polarClassMellin_integral χ w h).2, polarClassMellin_pvMultiplier χ T f w]
  have hn := polarClassMellin_hasDerivAt χ z h
  rw [hEq] at hn
  have hZ : Differentiable ℂ Z := globalIdelicZFunction_entire_of_vanishing _ f.property χ
  have hE : HasDerivAt E d z := hd
  have hval := hn.unique ((hE.mul (hZ z).hasDerivAt).const_mul m)
  change E z = 0 at hz
  rw [hz, zero_mul, add_zero] at hval
  exact hval ▸ mul_ne_zero hm (mul_ne_zero hd0 hf)

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "norm𝔽" => fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)

/-- Different exponents give different global norm twists of a fixed character. -/
private theorem pvKernel_chart_injective (χ : PontryaginDual C𝔽) :
    Injective (ideleClassNormTwist χ) := by
  intro s t h
  let w := quasiCharacterNormTwist (MonoidHom.id ℝ≥0ˣ) continuous_id 1 s
  have hw (u : ℝ≥0ˣ) : w u = ((u.val : ℝ) : ℂ) ^ s := one_mul _
  apply (existsUnique_complexPower w).unique hw
  intro u
  let g : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hg : ideleClassNorm F g = u := canonicalIdeleNormSection_rightInverse F u
  have he := DFunLike.congr_fun h g
  change (χ g : ℂ) * (norm𝔽 g : ℂ) ^ s = (χ g : ℂ) * (norm𝔽 g : ℂ) ^ t at he
  rw [show norm𝔽 g = (u.val : ℝ) from congrArg (fun x : ℝ≥0ˣ ↦ (x.val : ℝ)) hg] at he
  exact (hw u).trans (mul_left_cancel₀ (Circle.coe_ne_zero _) he)

/-- Unit translation preserves evaluation at zero and scales Fourier evaluation by the norm. -/
private theorem pvKernel_translatePolar
    (u : IdeleGroup (𝓞 F) F)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    adelePolarValues (F := F) (schwartzBruhatUnitTranslate u f) =
      ((adelePolarValues (F := F) f).1,
        (((ideleNorm F u).val : ℝ) : ℂ) * (adelePolarValues (F := F) f).2) := by
  apply Prod.ext
  · change f (Multiplicative.ofAdd (u.inv * 0)) = f (Multiplicative.ofAdd 0)
    rw [mul_zero]
  · have h := globalThetaPolarValues_snd_translate (F := F) (QuotientGroup.mk u)
      (Submodule.Quotient.mk f)
    rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u f] at h
    exact h

/-- Reflection across the critical strip gives a test nonzero at any nontrivial unitary
character. Two translation differences annihilate evaluation at zero and Fourier evaluation
at zero while preserving nonvanishing of the Mellin value. -/
private theorem pvKernel_polarNonzero (χ : PontryaginDual C𝔽) (z : ℂ) (hz : z.re = 0)
    (hc : ideleClassNormTwist χ z ≠ 1) :
    ∃ f : adelePolarSubspace F, globalIdelicZFunction f.val (ideleClassNormTwist χ z) ≠ 0 := by
  let c := ideleClassNormTwist χ z
  have h₁ : ideleClassNormTwist (1 : PontryaginDual C𝔽) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hDual (η : PontryaginDual C𝔽) (s : ℂ) :
      dualQuasiCharacter (G := C𝔽) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous
        (ideleClassNormTwist η s) = ideleClassNormTwist η⁻¹ (1 - s) := by
    ext1 g
    let N : ℂ := (((ideleClassNorm F g).val : ℝ) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (ideleClassNorm F g).ne_zero)
    change N * ideleClassNormTwist η s g⁻¹ = ideleClassNormTwist η⁻¹ (1 - s) g
    rw [map_inv]
    change N * ((η g : ℂ) * N ^ s)⁻¹ = (η g : ℂ)⁻¹ * N ^ (1 - s)
    rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
    ac_rfl
  have hr : (1 - z).re = 1 := by simp [hz]
  have hreg₁ : ideleClassNormTwist χ⁻¹ (1 - z) ≠ 1 := by
    intro e
    have h := quasiCharacterAbscissa_ideleClassNormTwist χ⁻¹ (1 - z)
    rw [e, ← h₁, quasiCharacterAbscissa_ideleClassNormTwist, hr] at h
    norm_num at h
  have hreg₂ : ideleClassNormTwist χ⁻¹ (1 - z) ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
    intro e
    have h := congrArg (fun c : HeckeCharacter (𝓞 F) F ↦
      dualQuasiCharacter (G := C𝔽) (ideleClassNorm F) (isProperMap_ideleClassNorm F).continuous c) e
    rw [hDual, hDual,
      inv_inv, inv_one, sub_sub_cancel, sub_self, h₁] at h
    exact hc h
  obtain ⟨g, hg⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ⁻¹
  let L (s : ℂ) := globalIdelicZFunction g (ideleClassNormTwist χ⁻¹ s)
  have hL : MeromorphicNFOn L univ := globalIdelicZFunction_meromorphic g χ⁻¹
  have hn : L (1 - z) ≠ 0 := by
    intro he
    have han : AnalyticAt ℂ L (1 - z) := (globalIdelicZFunction_poles g χ⁻¹).1 _ ⟨hreg₁, hreg₂⟩
    have hpos : 0 < meromorphicOrderAt L (1 - z) :=
      lt_of_le_of_ne han.meromorphicOrderAt_nonneg
        (fun h ↦ ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp h.symm) he)
    have hlt := completedHeckeL_continuation_zeros χ⁻¹ L hL (fun s ↦ by
      change globalIdelicZFunction _ _ = _
      rw [globalIdelicZFunction_eq_integral, hg s]
      change 1 < quasiCharacterAbscissa _ _ _ _
      rw [quasiCharacterAbscissa_ideleClassNormTwist]
      exact s.2) (by rw [hr]; norm_num) hpos
    linarith
  let E := adeleSchwartzFourier g
  have hE : globalIdelicZFunction E c ≠ 0 := by
    change globalIdelicZFunction g (ideleClassNormTwist χ⁻¹ (1 - z)) ≠ 0 at hn
    rwa [globalIdelicZFunction_functionalEquation, hDual,
      inv_inv, sub_sub_cancel] at hn
  have hcn : c ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽) 1 := by
    intro e
    have h := quasiCharacterAbscissa_ideleClassNormTwist χ z
    change ideleClassNormTwist χ z = _ at e
    rw [e, quasiCharacterAbscissa_ideleClassNormTwist, hz] at h
    norm_num at h
  have hreg : 0 ≤ globalIdelicOrderBound c := by
    rw [globalIdelicOrderBound, ite_eq_right (not_or.mpr ⟨hc, hcn⟩)]
  let Z : SchwartzBruhat (Multiplicative 𝔸[F]) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ (globalIdelicMellin (F := F) f).val ⟨c, hreg⟩
      map_add' := by intro f g; rw [map_add]; rfl
      map_smul' := by intro a g; rw [map_smul]; rfl }
  have hZT (t : I𝔽) (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
      Z (schwartzBruhatUnitTranslate t f) = c (QuotientGroup.mk t) * Z f :=
    globalIdelicMellin_unitTranslate t f ⟨c, hreg⟩
  have hZE : Z E ≠ 0 := hE
  let r : NNRealˣ := Units.mk0 2 (by norm_num)
  let u := canonicalIdeleNormSection F r
  have hn' : (((ideleNorm F u).val : ℝ) : ℂ) = 2 := by
    rw [canonicalIdeleNormSection_rightInverse F r]
    rfl
  have hcu : c (QuotientGroup.mk u) ≠ 2 := by
    intro h
    have hnrm (q : C𝔽) : ‖c q‖ = 1 := by
      change ‖(χ q : ℂ) * (((ideleClassNorm F q : NNReal) : ℝ) : ℂ) ^ z‖ = 1
      rw [norm_mul, Circle.norm_coe,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)), hz]
      simp
    have hb := hnrm (QuotientGroup.mk u)
    rw [h] at hb
    norm_num at hb
  obtain ⟨q, hq⟩ : ∃ q : C𝔽, c q ≠ 1 := by
    by_contra! h
    exact hc (ContinuousMonoidHom.ext fun q ↦ h q)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  let d := schwartzBruhatUnitTranslate u E - (2 : ℂ) • E
  let f := schwartzBruhatUnitTranslate v d - d
  have hp : f ∈ adelePolarSubspace F := by
    change adelePolarValues (F := F) f = 0
    dsimp only [f, d]
    rw [map_sub, pvKernel_translatePolar, map_sub, map_smul, pvKernel_translatePolar, hn']
    apply Prod.ext <;> simp
  refine ⟨⟨f, hp⟩, ?_⟩
  change Z f ≠ 0
  have he : Z f = (c (QuotientGroup.mk v) - 1) * (c (QuotientGroup.mk u) - 2) * Z E := by
    dsimp only [f, d]
    rw [map_sub, hZT, map_sub, hZT, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hq) (sub_ne_zero.mpr hcu)) hZE

private theorem polarClassMellin_commutes
    {G E : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    {μ : Measure G} {ρ : G →* (E →L[ℂ] E)} {χ : PontryaginDual G} {A : E →L[ℂ] E}
    (hA : IsPettisIsotypicAverageOn μ univ ρ χ A) (P : E →L[ℂ] E)
    (hP : ∀ g y, P (ρ g y) = ρ g (P y)) (x : E) : P (A x) = A (P x) := by
  have h : HasPettisIntegral (.positive (μ.restrict univ))
      (fun g ↦ P (star (χ g : ℂ) • ρ g x)) (P (A x)) := by
    obtain ⟨hi, he⟩ := hA x
    refine ⟨fun φ ↦ hi (φ.comp P), LinearMap.ext fun φ ↦ ?_⟩
    exact LinearMap.congr_fun he (φ.comp P)
  simp only [map_smul, hP] at h
  exact h.unique (hA (P x))

private theorem polarClassMellin_isotypeRange (S : Finset V) (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) :
    let W := CompactIntervalSobolev μ𝔽 logNorm(F) 0 0 s
    let H := globalThetaSobolev F 0 (le_refl (0 : ℝ)) hs
    let Wω := actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽(F) 0 0 s le_rfl hs).comp
      (ideleClassNorm F).ker.subtype) ω
    let P := globalThetaSobolevPrincipalValue F S 0 hs
    ∃ u : H, (u : W) ∈ Wω ∧ ((P u).val : W) ∈ Wω ∧
      ((P u).val : C𝔽 → ℂ) =ᵐ[μ𝔽] homogeneousAdelicTheta ω (adelePrincipalValue F S f.val) := by
  intro W H Wω P
  let R := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose
  let R₁ := R.comp (ideleClassNorm F).ker.subtype
  let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω).exists.choose
  let j := globalThetaSobolevInclusion F 0 (le_refl (0 : ℝ)) hs
  let t (b : ℬ₀) : H := j (Submodule.Quotient.mk b)
  let B (x : H) : H := (A x).val
  have hc (x : H) : P (B x) = B (P x) :=
    polarClassMellin_commutes
      (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω).exists.choose_spec.1
      P (fun k y ↦ globalThetaSobolevPrincipalValue_equivariant S 0 hs k y) x
  have hb (x : H) : (B x : W) ∈ Wω := by
    rw [mem_actionIsotype]
    intro k
    have hR := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose_spec.1
    exact (hR k.val (B x)).symm.trans (congrArg Subtype.val ((mem_actionIsotype _ ω _).mp (A x).property k))
  let f' : ℬ₀ := ⟨_, adelePrincipalValue_mem_polarSubspace S f⟩
  have ht : P (t f) = t f' := globalThetaSobolevPrincipalValue_apply S 0 hs f
  refine ⟨B (t f), hb _, ?_, ?_⟩
  · rw [hc]
    exact hb _
  · rw [hc, ht]
    obtain ⟨i, -, -, hi⟩ := exists_globalHomogeneousThetaSobolevInclusion
      (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω
    let q : globalPolarFreeThetaSubmodule (F := F) ω :=
      ⟨Submodule.Quotient.mk f'.val, ⟨f'.val, f'.property, rfl⟩⟩
    obtain ⟨h₁, h₂⟩ := hi f' q rfl
    change ((A (t f')).val.val : C𝔽 → ℂ) =ᵐ[μ𝔽] _
    change i q = A (t f') at h₁
    have heq : ((A (t f')).val.val : C𝔽 → ℂ) = ((i q).val.val : C𝔽 → ℂ) :=
      congrArg (fun x : actionIsotype R₁ ω ↦ (x.val.val : C𝔽 → ℂ)) h₁.symm
    exact (Filter.EventuallyEq.of_eq heq).trans
      (h₂.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽(F) _)))

end

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))

/-- The Euler denominator at a rational prime for the trivial character. -/
private theorem pvKernel_rat_factor (v : Vℚ) :
    (fun z ↦ (finiteHeckeEulerFactor χ₀ v z)⁻¹) =
      fun z ↦ 1 - Complex.exp (-(Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * z) := by
  have h1 : ideleClassNormTwist χ₀ 0 = 1 := by
    ext g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hu : (ideleClassNormTwist χ₀ 0).IsUnramifiedAt v := by
    rw [h1, HeckeCharacter.isUnramifiedAt_iff]
    intro x
    simp
  have hπ := (Valued.v : Valuation (v.adicCompletion ℚ)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
  funext z
  rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv, h1]
  simp [HeckeCharacter.localValue, hπ.ne_zero, Complex.cpow_def_of_ne_zero hq,
    Complex.natCast_log]

/-- At the frequency 2πi/log 2 the denominator at 2 vanishes simply while that
at 3 is nonzero, since log 3 lies strictly between log 2 and twice log 2. -/
private theorem pvKernel_rat_simple_zero :
    ∃ (S : Finset Vℚ) (z : ℂ), S.card = 2 ∧ z.re = 0 ∧ ideleClassNormTwist χ₀ z ≠ 1 ∧
      reciprocalPartialHeckeEulerProduct χ₀ S z = 0 ∧
      ∃ d, HasDerivAt (reciprocalPartialHeckeEulerProduct χ₀ S) d z ∧ d ≠ 0 := by
  classical
  let place (p : ℕ) (hp : p.Prime) : Vℚ :=
    let h := RatRingOfIntegers.prime_natCast_iff.mpr hp
    ⟨Ideal.span {(p : 𝓞 ℚ)}, (Ideal.span_singleton_prime h.ne_zero).mpr h,
      fun e ↦ h.ne_zero (Ideal.span_singleton_eq_bot.mp e)⟩
  let v := place 2 Nat.prime_two
  let w := place 3 Nat.prime_three
  have hv : v.asIdeal.absNorm = 2 := RatRingOfIntegers.absNorm_span_natCast 2
  have hw : w.asIdeal.absNorm = 3 := RatRingOfIntegers.absNorm_span_natCast 3
  have hvw : v ≠ w := by
    intro e
    rw [e, hw] at hv
    contradiction
  let S : Finset Vℚ := {v,w}
  let t : ℝ := 2 * Real.pi / Real.log 2
  let z := (t : ℂ) * Complex.I
  let d (q : ℝ) (s : ℂ) := 1 - Complex.exp (-(Real.log q : ℂ) * s)
  have he : reciprocalPartialHeckeEulerProduct χ₀ S = fun s ↦ d 2 s * d 3 s := by
    funext s
    rw [reciprocalPartialHeckeEulerProduct, Finset.prod_pair hvw, congrFun (pvKernel_rat_factor v) s,
      congrFun (pvKernel_rat_factor w) s, hv, hw]
    norm_num [d]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := div_pos Real.two_pi_pos hlog
  have hscale : t * Real.log 2 = 2 * Real.pi := div_mul_cancel₀ _ hlog.ne'
  have h₂ : d 2 z = 0 := by
    apply sub_eq_zero.mpr
    symm
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-1, ?_⟩
    have h : (t : ℂ) * (Real.log 2 : ℝ) = 2 * (Real.pi : ℂ) := by exact_mod_cast hscale
    simp only [Int.cast_neg, Int.cast_one]
    change -(Real.log 2 : ℂ) * ((t : ℂ) * Complex.I) = (-1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
    linear_combination -Complex.I * h
  have h₃ : d 3 z ≠ 0 := by
    intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp h).symm
    have hi := congrArg Complex.im hn
    simp [z, Complex.mul_im, Complex.mul_re, Complex.log_re] at hi
    have hlo : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    have hhi : Real.log 3 < 2 * Real.log 2 := by
      calc
        Real.log 3 < Real.log ((2 : ℝ) ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have ha := mul_lt_mul_of_pos_left hlo ht
    have hb := mul_lt_mul_of_pos_left hhi ht
    by_cases hneg : n ≤ -2
    · have hn' : (n : ℝ) ≤ -2 := by exact_mod_cast hneg
      nlinarith only [hi, hb, hscale, mul_nonneg (show 0 ≤ -(n : ℝ) - 2 by linarith) Real.pi_pos.le]
    · have hn' : (-1 : ℝ) ≤ n := by exact_mod_cast (show -1 ≤ n by omega)
      nlinarith only [hi, ha, hscale, mul_nonneg (show 0 ≤ (n : ℝ) + 1 by linarith) Real.pi_pos.le]
  have hd (q : ℝ) : HasDerivAt (d q) (-(Complex.exp (-(Real.log q : ℂ) * z) * (-(Real.log q : ℂ) * 1))) z :=
    (((hasDerivAt_id z).const_mul (-(Real.log q : ℂ))).cexp).const_sub 1
  refine ⟨S, z, Finset.card_pair hvw, by simp [z], ?_, ?_, ?_⟩
  · intro h
    have h1 : ideleClassNormTwist χ₀ 0 = 1 := by
      ext g
      change (1 : ℂ) * _ ^ (0 : ℂ) = 1
      simp
    have he := congrArg Complex.im (pvKernel_chart_injective χ₀ (h.trans h1.symm))
    simp [z, ht.ne'] at he
  · simp only [he, h₂, zero_mul]
  · rw [he]
    refine ⟨_, (hd 2).fun_mul (hd 3), ?_⟩
    rw [h₂, zero_mul, add_zero]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero _)
      (mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlog.ne')) one_ne_zero))) h₃

/-- Paper: Proof of Proposition 11.2.0.1(2), p. 485.
At the simple zero of the rational two-prime Euler product, a first logarithmic
moment can be nonzero on the principal-value image. -/
theorem Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels_false :
    ¬ Printed.globalThetaSobolevPrincipalValue_range_eq_jetKernels := by
  intro h
  obtain ⟨S, z, hc, hzre, htwist, hz, d, hd, hd₀⟩ := pvKernel_rat_simple_zero
  obtain ⟨f, hf⟩ := pvKernel_polarNonzero χ₀ z hzre htwist
  let hs : 0 ≤ (4 : ℝ) := by norm_num
  let K := (ideleClassNorm ℚ).ker
  let ω := (χ₀).comp (⟨K.subtype, continuous_subtype_val⟩ : K →ₜ* C𝔽(ℚ))
  obtain ⟨u, hu, hPu, hrep⟩ := polarClassMellin_isotypeRange S 4 hs ω f
  have hcard : 2 * (S.card : ℝ) ≤ 4 := by norm_num [hc]
  have h₁ : (1 : ℕ) < S.card := by simp [hc]
  have hzero := (h ℚ S χ₀ 4 hs hcard ⟨_, hPu⟩).mp ⟨u, hu, rfl⟩ z hz 1 h₁
  apply polarClassMellin_firstMoment_ne_zero χ₀ S f z d hz hd hd₀ hf
  refine (integral_congr_ae ?_).trans (by simpa only [pow_one] using hzero)
  filter_upwards [hrep] with g hg
  rw [hg]

end RiemannMasullo
