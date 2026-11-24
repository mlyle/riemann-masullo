module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Basic
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Exponential system on monogenic quotients

Masullo, §4.4, pp. 188–197. We use the left translation convention
`f (g⁻¹ * x)` and the Fourier convention of §D.1.1.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal NNReal TensorProduct

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G)

local notation "K" => m.toMonoidHom.ker
local notation "L" => Real.log ((m γ).val : ℝ)
local notation "Γ" => Subgroup.zpowers γ
local notation "Q" => G ⧸ Γ
local notation "S" => SchwartzBruhat Q
local notation "E" => ModulatedExponentialDecay m (Set.univ : Set ℝ)
local notation "logModule" x => Real.log ((m x).val : ℝ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

/-! ## 4.4.1 Mellin transform in split coordinates -/

-- TODO(paper-gap): Page 189 calls S_I(G) locally compact and identifies its
-- topology with the projective twist topology for arbitrary I.
-- TODO(paper-gap): The compact Fourier factor in (4.4.1.2) is a function on Ĝ¹.
-- The displayed codomain uses G¹, and the next formula evaluates M at c(τ(t)g).

section Mellin

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (hm : IsModulation m) (hms : Surjective m)
variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (χ : PontryaginDual G)

local notation "D" => ModulatedExponentialDecay m I
local notation "P" => PositiveRealExponentialDecay I
local notation "B" => SchwartzBergman I
local notation "M" => positiveRealFourierMellin I hOpen hInt hne
local notation "twist[" s "]" => quasiCharacterNormTwist m.toMonoidHom m.continuous
  ((circleToComplex).comp χ) s
local notation "phase[" b "]" => (b : ℂ) * Complex.I
local notation "avg⟦" f ", " t "⟧" => (∫ k : K, (χ k.val : ℂ) * (f).val (k.val * τ t) ∂μ₁)

include hOpen hInt hne hms hτ hμ in
/-- Paper: Equations (4.4.1.1) and (4.4.1.4), pp. 189–190. In the chart of a unitary
character, the group Mellin integral splits into the compact character integral
and a positive-real integral. Both the inner and outer integrals converge. -/
theorem modulatedMellin_split (f : D) (s : ℂ) (hs : s.re ∈ I) :
    (∀ t : ℝ≥0ˣ, Integrable (fun k : K ↦ (χ k.val : ℂ) * f.val (k.val * τ t)) μ₁) ∧
    Integrable (fun t : ℝ≥0ˣ ↦ ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg⟦f, t⟧)
      positiveRealHaar ∧
    modulatedFourierMellin m I hm μ f.val (twist[s]) =
      ∫ t : ℝ≥0ˣ, ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg⟦f, t⟧ ∂positiveRealHaar := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let r (g : G) : ℝ := (m g).val
  have hr (g : G) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hrc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  -- The real twist controls the norm of the complex Mellin integrand.
  let w := modulatedExponentialDecayTwist m I ⟨s.re, hs⟩ f
  have hw (g : G) : w g = ((r g ^ s.re : ℝ) : ℂ) * f.val g := rfl
  have hf : Continuous f.val := by
    have hc := Complex.continuous_ofReal.comp
      (hrc.rpow_const (p := s.re) (fun g ↦ Or.inl (hr g).ne'))
    have hne (g : G) : ((r g ^ s.re : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hr g) _).ne'
    refine ((schwartzBruhat_continuous w).div hc hne).congr fun g ↦ ?_
    change w g / ((r g ^ s.re : ℝ) : ℂ) = f.val g
    rw [hw, mul_div_cancel_left₀ _ (hne g)]
  let H (g : G) := f.val g * (twist[s]) g
  have hc : Continuous H := hf.mul (twist[s]).continuous
  have hint : Integrable H μ := by
    apply (schwartzBruhat_integrable μ w).norm.mono' hc.aestronglyMeasurable
    filter_upwards with g
    change ‖f.val g * ((χ g : ℂ) * (r g : ℂ) ^ s)‖ ≤ ‖w g‖
    rw [hw, norm_mul, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (hr g), norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (hr g) _), mul_comm]
  let φ (p : K × ℝ≥0ˣ) := p.1.val * τ p.2
  have hφ : Continuous φ :=
    (continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd)
  have hprod : Integrable (H ∘ φ) (μ₁.prod positiveRealHaar) := by
    rw [hμ] at hint
    exact hint.comp_measurable hφ.measurable
  -- The modulus is t along each compact fiber, so its complex power factors out.
  have hfiber (t : ℝ≥0ˣ) : (∫ k : K, (H ∘ φ) (k, t) ∂μ₁) =
      ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg⟦f, t⟧ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun k ↦ ?_)
    change f.val (k.val * τ t) * ((χ (k.val * τ t) : ℂ) *
      (((m (k.val * τ t)).val : ℝ) : ℂ) ^ s) = _
    rw [map_mul χ, Circle.coe_mul, map_mul m, show m k.val = 1 from k.property,
      hτ t, one_mul]
    ring
  have hstrip : twist[s] ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I := by
    change quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 (twist[s]) ∈ I
    rwa [quasiCharacterAbscissa_of_unitary_twist m.toMonoidHom hm.1 hm.2 _ χ s (fun _ ↦ rfl)]
  refine ⟨fun t ↦ ?_, hprod.integral_prod_right.congr (.of_forall hfiber), ?_⟩
  · have hcontinuous : Continuous (fun k : K ↦ (χ k.val : ℂ) * f.val (k.val * τ t)) :=
      (continuous_subtype_val.comp (χ.continuous.comp continuous_subtype_val)).mul
        (hf.comp (continuous_subtype_val.mul continuous_const))
    exact hcontinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · rw [modulatedFourierMellin, indicator_of_mem hstrip]
    change (∫ g, H g ∂μ) = _
    rw [hμ, integral_map hφ.measurable.aemeasurable hc.aestronglyMeasurable]
    exact (integral_prod_symm (H ∘ φ) hprod).trans (integral_congr_ae (.of_forall hfiber))

include hms hτ in
private theorem splitCharacter_mem_relativeVerticalStrip (c : QuasiCharacter G)
    (ω : PontryaginDual K) (s : ℂ) (hs : s.re ∈ I)
    (hc : ∀ (k : K) (t : ℝ≥0ˣ),
      c (k.val * τ t) = (ω k : ℂ) * ((t.val : ℝ) : ℂ) ^ s) :
    c ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I := by
  let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  have ht : (t.val : ℝ) = 2 := by norm_num [t]
  obtain ⟨g, hg⟩ := hms t
  have hz : c (τ (m g)) = (((m g).val : ℝ) : ℂ) ^ s := by simpa using hc 1 (m g)
  have hn := norm_quasiCharacter_eq_rpow_abscissa m.toMonoidHom hm.1 hm.2 c (τ (m g))
  change ‖c (τ (m g))‖ = ((m (τ (m g))).val : ℝ) ^ _ at hn
  rw [hz, hτ, hg, ht, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)] at hn
  change quasiCharacterAbscissa _ _ _ c ∈ I
  rwa [← (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp hn]

include hOpen hInt hne hms hτ hμ in
/-- Paper: Equation (4.4.1.2), p. 190. The Mellin transform identifies the decay
space with the completed inductive tensor of the compact dual's Schwartz–Bruhat
space and the scalar Schwartz–Bergman space, evaluated in split coordinates.
Deviation: The compact Fourier factor is indexed by characters of the norm-one
group, as in Theorem D.3.3.13. Its Haar measure can have arbitrary positive mass. -/
theorem modulatedMellin_tensor_equiv :
    let U := InductiveTensor (SchwartzBruhat (PontryaginDual K)) B
    ∃ (F : D ≃L[ℂ] Completion U) (j : Completion U →L[ℂ] (PontryaginDual K → B)),
      Injective j ∧
      (∀ (v : SchwartzBruhat (PontryaginDual K)) (H : B) ω,
        j (Completion.coe' (α := U) (v ⊗ₜ[ℂ] H)) ω = v ω • H) ∧
      ∀ (f : D) (c : QuasiCharacter G) (ω : PontryaginDual K) (s : ℂ), s.re ∈ I →
        (∀ (k : K) (t : ℝ≥0ˣ),
          c (k.val * τ t) = (ω k : ℂ) * ((t.val : ℝ) : ℂ) ^ s) →
        modulatedFourierMellin m I hm μ f.val c = (j (F f) ω).val s := by
  classical
  intro U
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let mass : ℝ≥0 := (μ₁ univ).toNNReal
  have hm0 : mass ≠ 0 := by
    exact (ENNReal.toNNReal_pos (NeZero.ne (μ₁ univ)) (measure_ne_top _ _)).ne'
  have hmass : (mass : ℝ≥0∞) = μ₁ univ := ENNReal.coe_toNNReal (measure_ne_top _ _)
  let ν₁ : Measure K := mass⁻¹ • μ₁
  let ν : Measure G := mass⁻¹ • μ
  let : ν₁.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hm0)
  let : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (inv_ne_zero hm0)
  have hprob : ν₁ univ = 1 := by
    change (mass⁻¹ : ℝ≥0) • μ₁ univ = 1
    rw [← hmass, ← ENNReal.coe_smul, smul_eq_mul, inv_mul_cancel₀ hm0, ENNReal.coe_one]
  have hν : ν = (ν₁.prod positiveRealHaar).map (fun z : K × ℝ≥0ˣ ↦ z.1.val * τ z.2) := by
    have hcont : Continuous (fun z : K × ℝ≥0ˣ ↦ z.1.val * τ z.2) :=
      (continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd)
    rw [show ν₁ = mass⁻¹ • μ₁ from rfl, Measure.prod_smul_left,
      Measure.map_smul _ hcont.measurable.aemeasurable, ← hμ]
  refine (modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ).elim fun e he ↦ ?_
  let tensor := modulatedFourierMellin_tensor m I hm hInt hne τ hτ ν hOpen ν₁ hprob hν e he
  refine tensor.elim fun _ hf ↦ ?_
  refine hf.elim fun F hF ↦ ?_
  refine hF.elim fun j hj ↦ ?_
  have hinj := hj.2.2.1
  have hpure := hj.2.2.2.1
  have hcoord := hj.2.2.2.2
  let c₀ : ℂ := (mass : ℝ)
  have hc₀ : c₀ ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hm0)
  let scale : D ≃L[ℂ] D := {
    LinearEquiv.smulOfNeZero ℂ D c₀ hc₀ with
    continuous_toFun := continuous_const_smul _
    continuous_invFun := continuous_const_smul _ }
  with_reducible_and_instances refine ⟨scale.trans (e.symm.trans F), j, hinj, hpure, ?_⟩
  intro f c ω s hs hc
  have hstrip := splitCharacter_mem_relativeVerticalStrip m hm hms I τ hτ c ω s hs hc
  have hco := hcoord (e.symm (scale f)) ⟨c,hstrip⟩ ω ⟨s,hs⟩ hc
  let obs (v : D) := modulatedFourierMellin m I hm ν v.val c
  have hv := congrArg obs (e.apply_symm_apply (scale f))
  simp only [ContinuousLinearEquiv.trans_apply]
  dsimp only [obs] at hv
  have hintegral : modulatedFourierMellin m I hm μ f.val c =
      modulatedFourierMellin m I hm ν (scale f).val c := by
    simp only [modulatedFourierMellin, indicator_of_mem hstrip]
    change (∫ g, f.val g * c g ∂μ) = ∫ g, (c₀ * f.val g) * c g ∂(mass⁻¹ • μ)
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_smul_nnreal_measure]
    change _ = ((mass : ℝ) : ℂ) * ((((mass⁻¹ : ℝ≥0) : ℝ) : ℂ) * _)
    rw [← mul_assoc, ← Complex.ofReal_mul, ← NNReal.coe_mul, mul_inv_cancel₀ hm0]
    simp
  exact hintegral.trans (hv.symm.trans hco)

/-- Paper: Discussion 4.4.1.1, p. 191. A unitary character has a unique real
frequency along the fixed positive-real section. -/
theorem existsUnique_modulatedMellinSectionFrequency :
    ∃! b : ℝ, ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ)) := by
  have key (b : ℝ) (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ ((b : ℂ) * Complex.I) =
      (Circle.exp (b * Real.log (t.val : ℝ)) : ℂ) := by
    have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ← Complex.ofReal_log ht.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  obtain ⟨z, ⟨hre, hz⟩, huniq⟩ := existsUnique_unitaryComplexPower
    ((circleToComplex).comp (ContinuousMonoidHom.comp χ τ)) (fun t ↦ Circle.norm_coe _)
  have hzb : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  refine ⟨z.im, fun t ↦ Circle.ext ?_, fun b hb ↦ ?_⟩
  · rw [← key, ← hzb]
    exact hz t
  · have h := huniq ((b : ℂ) * Complex.I) ⟨by simp, fun t ↦ ?_⟩
    · rw [← h]
      simp
    · rw [key, ← hb t]
      rfl

set_option linter.unusedSectionVars false in
include hm hInt hne hτ in
/-- Evaluation of the unnormalized compact average is a continuous functional on
the decay space. Evaluate one real twist after applying the compact projector. -/
private theorem compactAverage_functional (t : ℝ≥0ˣ) :
    ∃ R : D →L[ℂ] ℂ, ∀ f, R f = avg⟦f, t⟧ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let ω : PontryaginDual K := χ.comp ⟨Subgroup.subtype K, continuous_subtype_val⟩
  let a : I := ⟨hne.choose, hne.choose_spec⟩
  let W : D →L[ℂ] SchwartzBruhat G := ⟨modulatedExponentialDecayTwist m I a,
    (continuous_apply a).comp (modulatedExponentialDecay_twists_continuous m I hm hInt hne τ hτ)⟩
  let T := schwartzBruhatIsotypicProjector m hm μ₁ ω
  let w : ℂ := (((t.val : ℝ) ^ (a : ℝ) : ℝ) : ℂ)
  have hw : w ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr t.zero_lt) _).ne'
  let mass : ℂ := μ₁.real univ
  have hmass : mass ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'
  refine ⟨(mass * w⁻¹) • ((schwartzBruhatEvalCLM (τ t)).comp (T.comp W)), fun f ↦ ?_⟩
  let g (k : K) := star (ω k : ℂ) * W f (k.val⁻¹ * τ t)
  have hval (k : K) : g k⁻¹ = w * ((χ k.val : ℂ) * f.val (k.val * τ t)) := by
    have hω : (ω k⁻¹ : ℂ) = star (χ k.val : ℂ) := by
      change (χ (k.val⁻¹) : ℂ) = _
      rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
    have hx : (k⁻¹).val⁻¹ * τ t = k.val * τ t := congrArg (· * τ t) (inv_inv k.val)
    have hmod : m (k.val * τ t) = t :=
      (map_mul m _ _).trans ((congrArg₂ (· * ·) (show m k.val = 1 from k.property) (hτ t)).trans (one_mul t))
    have ht : W f ((k⁻¹).val⁻¹ * τ t) = w * f.val (k.val * τ t) := calc
      _ = W f (k.val * τ t) := congrArg (W f).val hx
      _ = _ := (modulatedExponentialDecayTwist_apply m I a f _).trans
        (congrArg (fun u : ℝ≥0ˣ ↦ (((u.val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * f.val (k.val * τ t)) hmod)
    exact (congrArg₂ (· * ·) ((congrArg star hω).trans (star_star _)) ht).trans (mul_left_comm _ _ _)
  have hint : (∫ k, g k ∂μ₁) = w * avg⟦f, t⟧ := calc
    _ = ∫ k, g k⁻¹ ∂μ₁ := (integral_inv_eq_self g μ₁).symm
    _ = _ := (integral_congr_ae (.of_forall hval)).trans (integral_const_mul _ _)
  have hP := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω (W f) (τ t)).2
  have scalar (x : ℂ) : (μ₁.real univ)⁻¹ • x = mass⁻¹ * x := by
    rw [Complex.real_smul, Complex.ofReal_inv]
  have hP' : T (W f) (τ t) = mass⁻¹ * (w * avg⟦f, t⟧) :=
    hP.trans ((scalar _).trans (congrArg (mass⁻¹ * ·) hint))
  have cancel (x : ℂ) : mass * w⁻¹ * (mass⁻¹ * (w * x)) = x := by
    calc
      _ = (mass * mass⁻¹) * (w⁻¹ * w) * x := by ac_rfl
      _ = x := by rw [mul_inv_cancel₀ hmass, inv_mul_cancel₀ hw, one_mul, one_mul]
  change (mass * w⁻¹) * T (W f) (τ t) = _
  with_reducible_and_instances
    exact (congrArg ((mass * w⁻¹) * ·) hP').trans (cancel _)

/-- Contracting a completed tensor product by a normalized functional is a split
surjection. A vector where the functional takes value one gives a continuous section. -/
private theorem exists_split_tensor_restriction {U V W ι : Type*}
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [PolynormableSpace ℂ U] [T2Space U]
    [AddCommGroup V] [Module ℂ V] [UniformSpace V] [IsUniformAddGroup V]
    [PolynormableSpace ℂ V] [T2Space V] [ContinuousSMul ℂ V] [CompleteSpace V]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (φ : U →L[ℂ] ℂ) (ev : ι → V →L[ℂ] ℂ) (res : ι → W →L[ℂ] ℂ)
    (e : Completion (InductiveTensor U V) ≃L[ℂ] W)
    (h : ∀ u v i, res i (e (Completion.coe' (α := InductiveTensor U V) (u ⊗ₜ[ℂ] v))) =
      φ u * ev i v) (u : U) (hu : φ u = 1)
    (hext : ∀ p q : V, (∀ i, ev i p = ev i q) → p = q) :
    ∃ (A : W →L[ℂ] V) (J : V →L[ℂ] W), (∀ p, A (J p) = p) ∧
      ∀ w i, ev i (A w) = res i w := by
  obtain ⟨A, hA⟩ := exists_tensor_restriction φ ev res e h
  let Z := InductiveTensor U V
  let j : V →L[ℂ] Z :=
    ⟨TensorProduct.mk ℂ U V u, ((continuous_inductiveTensor_iff (LinearMap.id : Z →ₗ[ℂ] Z)).1 continuous_id).1 u⟩
  let emb : Z →L[ℂ] Completion Z := Completion.toComplL
  let J := e.toContinuousLinearMap.comp (emb.comp j)
  refine ⟨A, J, fun p ↦ hext _ _ fun i ↦ ?_, hA⟩
  calc
    ev i (A (J p)) = res i (J p) := hA _ _
    _ = φ u * ev i p := h u p i
    _ = ev i p := by rw [hu, one_mul]

/-- A logarithmic profile is determined by its values on positive-real units. -/
private theorem scalarProfile_ext_log {p q : P}
    (h : ∀ t : ℝ≥0ˣ, p.val (Real.log (t.val : ℝ)) = q.val (Real.log (t.val : ℝ))) : p = q := by
  apply Subtype.ext
  funext x
  let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have ht : Real.log (t.val : ℝ) = x := by
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  exact (congrArg p.val ht.symm).trans ((h t).trans (congrArg q.val ht))

set_option linter.unusedSectionVars false in
include hm hInt hne hτ in
/-- Contract the split decay tensor with the compact character integral. A pure tensor
with normalized conjugate character in its first factor splits this contraction. -/
private theorem compactAverage_split :
    ∃ (A : D →L[ℂ] P) (J : P →L[ℂ] D), (∀ p, A (J p) = p) ∧
      ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧ := by
  let SK := SchwartzBruhat K
  let U := InductiveTensor SK P
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have : T2Space SK := schwartzBruhat_t2
  have : T2Space P := (positiveRealExponentialDecay_isEmbedding I hne).t2Space
  have : CompleteSpace P := positiveRealExponentialDecay_complete I hne
  let ω : PontryaginDual K := χ.comp ⟨Subgroup.subtype K, continuous_subtype_val⟩
  let FT := (schwartzBruhat_fourier_equiv (G := K) μ₁).choose
  let φ : SK →L[ℂ] ℂ := (schwartzBruhatEvalCLM ω⁻¹).comp FT.toContinuousLinearMap
  have hφ (u : SK) : φ u = ∫ k : K, (χ k.val : ℂ) * u k ∂μ₁ := by
    change FT u ω⁻¹ = _
    refine ((schwartzBruhat_fourier_equiv (G := K) μ₁).choose_spec u).2 ω⁻¹ |>.trans ?_
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro k
    change u k * star (((ω k)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, mul_comm]
    rfl
  let idM := ContinuousMonoidHom.id ℝ≥0ˣ
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let d := (identityModulationExponentialDecay_equiv I hInt hne).choose
  let ev₀ (t : ℝ≥0ˣ) : ModulatedExponentialDecay idM I →L[ℂ] ℂ :=
    ⟨(LinearMap.proj t).comp (modulatedExponentialDecaySubmodule idM I).subtype,
      continuous_modulatedExponentialDecay_eval idM I hne t⟩
  let ev (t : ℝ≥0ˣ) := (ev₀ t).comp d.toContinuousLinearMap
  have hev (t : ℝ≥0ˣ) (p : P) : ev t p = p.val (Real.log (t.val : ℝ)) :=
    (identityModulationExponentialDecay_equiv I hInt hne).choose_spec p t
  let R (t : ℝ≥0ˣ) := (compactAverage_functional m hm I hInt hne τ hτ μ₁ χ t).choose
  have hR (t : ℝ≥0ˣ) (f : D) : R t f = avg⟦f, t⟧ :=
    (compactAverage_functional m hm I hInt hne τ hτ μ₁ χ t).choose_spec f
  have hB := modulatedExponentialDecay_tensor_equiv m I hm hInt hne τ hτ
  let B₀ := hB.choose
  have hpure (f : D) (t : ℝ≥0ˣ) (u : SK) (v : P)
      (hf : ∀ k : K, f.val (k.val * τ t) = u k * v.val (Real.log (t.val : ℝ))) :
      R t f = φ u * ev t v := by
    calc
      R t f = avg⟦f, t⟧ := hR t f
      _ = ∫ k : K, ((χ k.val : ℂ) * u k) * v.val (Real.log (t.val : ℝ)) ∂μ₁ :=
        integral_congr_ae (.of_forall fun k ↦ (congrArg ((χ k.val : ℂ) * ·) (hf k)).trans (mul_assoc _ _ _).symm)
      _ = (∫ k : K, (χ k.val : ℂ) * u k ∂μ₁) * v.val (Real.log (t.val : ℝ)) := integral_mul_const _ _
      _ = φ u * ev t v := congrArg₂ (· * ·) (hφ u).symm (hev _ _).symm
  let u₁ := (compact_schwartzBruhat_one (H := K)).choose
  have hU := schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹
  let u : SK := ((μ₁.real univ : ℂ)⁻¹) • hU.choose u₁
  have hu (k : K) : (χ k.val : ℂ) * u k = (μ₁.real univ : ℂ)⁻¹ := by
    change (ω k : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * hU.choose u₁ k) = _
    have hc : hU.choose u₁ k = (ω⁻¹ k : ℂ) :=
      (hU.choose_spec u₁ k).trans ((congrArg ((ω⁻¹ k : ℂ) * ·)
        ((compact_schwartzBruhat_one (H := K)).choose_spec k)).trans (mul_one _))
    have hw : (ω k : ℂ) * (ω⁻¹ k : ℂ) = 1 :=
      (Circle.coe_mul _ _).symm.trans (congrArg ((↑) : Circle → ℂ) (mul_inv_cancel (ω k)))
    calc
      _ = (ω k : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * (ω⁻¹ k : ℂ)) := congrArg (fun y : ℂ ↦ (ω k : ℂ) * (_ * y)) hc
      _ = (μ₁.real univ : ℂ)⁻¹ * ((ω k : ℂ) * (ω⁻¹ k : ℂ)) := mul_left_comm _ _ _
      _ = _ := (congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) hw).trans (mul_one _)
  have hm₁ : (μ₁.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne'
  have hφu : φ u = 1 := (hφ u).trans ((integral_congr_ae (.of_forall hu)).trans
    ((integral_const _).trans (Complex.real_smul.trans (mul_inv_cancel₀ hm₁))))
  have hext (p q : P) (h : ∀ t, ev t p = ev t q) : p = q := by
    apply scalarProfile_ext_log I
    intro t
    exact (hev t p).symm.trans ((h t).trans (hev t q))
  have hsplit : ∃ (A : D →L[ℂ] P) (J : P →L[ℂ] D), (∀ p, A (J p) = p) ∧
      ∀ f t, ev t (A f) = R t f := by
    with_reducible_and_instances
      apply exists_split_tensor_restriction (U := SK) (V := P) (W := D) (ι := ℝ≥0ˣ) φ ev R B₀ _ u hφu hext
    intro u v t
    let f : D := B₀ (Completion.coe' (α := U) (u ⊗ₜ[ℂ] v))
    have he (k : K) : f.val (k.val * τ t) = u k * v.val (Real.log (t.val : ℝ)) := by
      with_reducible_and_instances exact hB.choose_spec u v k t
    with_reducible_and_instances change R t f = φ u * ev t v
    with_reducible_and_instances exact hpure f t u v he
  obtain ⟨A, J, hJ, hA⟩ := hsplit
  exact ⟨A, J, hJ, fun f t ↦ (hev t (A f)).symm.trans ((hA f t).trans (hR t f))⟩

include hInt hne in
/-- Multiplying a scalar profile by a unitary character of the positive reals is a
continuous linear automorphism. The inverse multiplies by the inverse character. -/
private theorem scalarProfile_unitary (η : PontryaginDual ℝ≥0ˣ) :
    ∃ U : P ≃L[ℂ] P, ∀ p (t : ℝ≥0ˣ),
      (U p).val (Real.log (t.val : ℝ)) = (η t : ℂ) * p.val (Real.log (t.val : ℝ)) := by
  let idM := ContinuousMonoidHom.id ℝ≥0ˣ
  have hid : IsModulation idM := ⟨isProperMap_id, ⟨(Units.mk0 2 (by norm_num) : ℝ≥0ˣ), by
    intro h
    have hn := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    norm_num [idM] at hn⟩⟩
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hM := modulatedExponentialDecay_mul_unitaryCharacter idM I hid surjective_id hInt hne
  let F := (hM η).choose
  let J := (hM η⁻¹).choose
  have hF := (hM η).choose_spec
  have hJ := (hM η⁻¹).choose_spec
  have hm₁ (t : ℝ≥0ˣ) : (η⁻¹ t : ℂ) = (η t : ℂ)⁻¹ := Circle.coe_inv _
  have inv₁ (p) : J (F p) = p := by
    apply Subtype.ext
    funext t
    calc
      _ = (η⁻¹ t : ℂ) * ((η t : ℂ) * p.val t) := (hJ (F p) t).trans (congrArg ((η⁻¹ t : ℂ) * ·) (hF p t))
      _ = _ := (congrArg (fun z : ℂ ↦ z * ((η t : ℂ) * p.val t)) (hm₁ t)).trans (inv_mul_cancel_left₀ (Circle.coe_ne_zero _) _)
  have inv₂ (p) : F (J p) = p := by
    apply Subtype.ext
    funext t
    calc
      _ = (η t : ℂ) * ((η⁻¹ t : ℂ) * p.val t) := (hF (J p) t).trans (congrArg ((η t : ℂ) * ·) (hJ p t))
      _ = _ := (congrArg (fun z : ℂ ↦ (η t : ℂ) * (z * p.val t)) (hm₁ t)).trans (mul_inv_cancel_left₀ (Circle.coe_ne_zero _) _)
  let V := ContinuousLinearEquiv.equivOfInverse F J inv₁ inv₂
  let d := (identityModulationExponentialDecay_equiv I hInt hne).choose
  have hd := (identityModulationExponentialDecay_equiv I hInt hne).choose_spec
  let U := (d.trans V).trans d.symm
  refine ⟨U, fun p t ↦ ?_⟩
  have hh : d (U p) = F (d p) := d.apply_symm_apply _
  exact (hd (U p) t).symm.trans ((congrArg (fun z : ModulatedExponentialDecay idM I ↦ z.val t) hh).trans
    ((hF (d p) t).trans (congrArg ((η t : ℂ) * ·) (hd p t))))

include hOpen hInt hne in
/-- Express the scalar Mellin transform using the exponential pushforward of Lebesgue
measure, with the same positive-real Haar measure as in the split group integral. -/
private theorem scalarProfile_mellin_haar (p : P) (s : ℂ) (hs : s.re ∈ I) :
    (M p).val s = ∫ t : ℝ≥0ˣ, ((t.val : ℝ) : ℂ) ^ s * p.val (Real.log (t.val : ℝ)) ∂positiveRealHaar := by
  let ex : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hval (x : ℝ) : ((ex x).val : ℝ) = Real.exp x := rfl
  have heq : positiveRealHaar = Measure.map ex volume := by
    unfold positiveRealHaar
    congr 1
    funext x
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).trans (hval x).symm
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  rw [positiveRealFourierMellin_apply I hOpen hInt hne p s hs, mellin_fromLog_eq_integral_exp,
    heq, ex.measurableEmbedding.integral_map]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change Complex.exp (s * x) * p.val x = (((ex x).val : ℝ) : ℂ) ^ s * p.val (Real.log ((ex x).val : ℝ))
  rw [hval x, Real.log_exp, Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm s]

/-- Conjugating the inverse profile shift by the scalar transform undoes the forward
shift on transformed profiles. -/
private theorem conjugate_profile_shift_apply {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (F : X ≃L[ℂ] Y) (U : X ≃L[ℂ] X) (x : X) :
    ((F.symm.trans U.symm).trans F) (F (U x)) = F x := by
  change F (U.symm (F.symm (F (U x)))) = F x
  rw [F.symm_apply_apply, U.symm_apply_apply]

set_option linter.unusedSectionVars false in
include hms hτ hμ in
/-- The scalar Mellin transform of the character-twisted profile is the group Mellin
integral, and conjugating the inverse twist translates the spectral variable. -/
private theorem compactAverage_mellin_maps (b : ℝ)
    (hb : ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ)))
    (A : D →L[ℂ] P) (hA : ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧)
    (U : P ≃L[ℂ] P) (hU : ∀ (p : P) (t : ℝ≥0ˣ),
      (U p).val (Real.log (t.val : ℝ)) = (χ (τ t) : ℂ) * p.val (Real.log (t.val : ℝ))) :
    ∃ (F : D →L[ℂ] B) (T : B ≃L[ℂ] B),
      (∀ f s, s.re ∈ I → (F f).val s = modulatedFourierMellin m I hm μ f.val (twist[s])) ∧
      (∀ H s, s.re ∈ I → (T H).val s = H.val (s - phase[b])) ∧
      ∀ f, T (F f) = M (A f) := by
  let η : PontryaginDual ℝ≥0ˣ := χ.comp τ
  have hη (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ phase[b] = (η t : ℂ) := by
    have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr t.zero_lt
    change ((t.val : ℝ) : ℂ) ^ phase[b] = (χ (τ t) : ℂ)
    rw [hb, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ← Complex.ofReal_log ht.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hshift (p : P) (s : ℂ) (hs : s.re ∈ I) :
      (M (U p)).val s = (M p).val (s + phase[b]) := by
    have hs' : (s + phase[b]).re ∈ I := by simpa using hs
    rw [scalarProfile_mellin_haar I hOpen hInt hne _ _ hs,
      scalarProfile_mellin_haar I hOpen hInt hne _ _ hs']
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    change ((t.val : ℝ) : ℂ) ^ s * (U p).val (Real.log (t.val : ℝ)) =
      ((t.val : ℝ) : ℂ) ^ (s + phase[b]) * p.val (Real.log (t.val : ℝ))
    have h₀ : ((t.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero)
    rw [hU p t, Complex.cpow_add _ _ h₀, hη, mul_assoc]
    rfl
  let F : D →L[ℂ] B := (M).toContinuousLinearMap.comp (U.toContinuousLinearMap.comp A)
  let T : B ≃L[ℂ] B := ((M).symm.trans U.symm).trans M
  have hF (f : D) (s : ℂ) (hs : s.re ∈ I) : (F f).val s = modulatedFourierMellin m I hm μ f.val (twist[s]) := by
    change (M (U (A f))).val s = _
    refine (scalarProfile_mellin_haar I hOpen hInt hne _ _ hs).trans ?_
    refine Eq.trans ?_ (modulatedMellin_split m hm hms I hOpen hInt hne τ hτ μ₁ μ hμ χ f s hs).2.2.symm
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    change ((t.val : ℝ) : ℂ) ^ s * (U (A f)).val (Real.log (t.val : ℝ)) = _
    exact (congrArg (((t.val : ℝ) : ℂ) ^ s * ·)
      ((hU (A f) t).trans (congrArg ((η t : ℂ) * ·) (hA f t)))).trans (mul_assoc _ _ _).symm
  have hT (H : B) (s : ℂ) (hs : s.re ∈ I) : (T H).val s = H.val (s - phase[b]) := by
    let p := U.symm ((M).symm H)
    have hs' : (s - phase[b]).re ∈ I := by simpa using hs
    have h := hshift p (s - phase[b]) hs'
    have hH : M (U p) = H := (congrArg M (U.apply_symm_apply ((M).symm H))).trans ((M).apply_symm_apply H)
    change (M p).val s = _
    exact (congrArg (M p).val (sub_add_cancel s phase[b]).symm).trans
      (h.symm.trans (congrArg (fun q : B ↦ q.val (s - phase[b])) hH))
  have hdiagram (f : D) : T (F f) = M (A f) :=
    conjugate_profile_shift_apply M U (A f)
  with_reducible_and_instances exact ⟨F, T, hF, hT, hdiagram⟩

/-- A split average and a compatible pair of transforms induce the diagram on the
kernel quotient. -/
private theorem exists_diagram_of_split_average {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (M₀ : Y → Z) (pA : (X →L[ℂ] Y) → Prop) (pF : (X →L[ℂ] Z) → Prop)
    (pT : (Z ≃L[ℂ] Z) → Prop)
    (h₁ : ∃ (A : X →L[ℂ] Y) (J : Y →L[ℂ] X), (∀ y, A (J y) = y) ∧ pA A)
    (h₂ : ∀ A, pA A → ∃ (F : X →L[ℂ] Z) (T : Z ≃L[ℂ] Z),
      pF F ∧ pT T ∧ ∀ x, T (F x) = M₀ (A x)) :
    ∃ (A : X →L[ℂ] Y) (F : X →L[ℂ] Z) (T : Z ≃L[ℂ] Z) (e : (X ⧸ A.ker) ≃L[ℂ] Y),
      pA A ∧ pF F ∧ pT T ∧ (∀ x, e (A.ker.mkQ x) = A x) ∧
      (∀ x, T (F x) = M₀ (e (A.ker.mkQ x))) := by
  obtain ⟨A, J, hJ, hA⟩ := h₁
  obtain ⟨F, T, hF, hT, hcomm⟩ := h₂ A hA
  obtain ⟨e, he⟩ := exists_ker_quotientEquiv_of_rightInverse A J hJ
  exact ⟨A, F, T, e, hA, hF, hT, he, fun x ↦ (hcomm x).trans (congrArg M₀ (he x).symm)⟩

-- TODO(paper-gap): The bottom arrow in (4.4.1.3) evaluates the scalar Mellin
-- transform at s. The displayed integral on p. 191 evaluates it at s + i x₀.
-- Item (3) also uses the idele class notation C_F¹ for the general group G¹.

set_option linter.unusedSectionVars false in
include hms hτ hμ in
/-- Paper: Discussion 4.4.1.1, pp. 190–191. The compact average followed by
restriction to the section identifies its kernel quotient with the scalar decay
space. The group transform on this character component agrees, after translation
of its argument by minus the section frequency times i, with the scalar Mellin
transform of that profile.
Deviation: The bottom arrow uses the unshifted scalar Mellin transform specified
by the diagram. The isotypic quotient is represented by the kernel of the
section profile of the unnormalized average. -/
theorem modulatedMellin_isotypicDiagram (b : ℝ)
    (hb : ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ))) :
    ∃ (A : D →L[ℂ] P) (F : D →L[ℂ] B) (T : B ≃L[ℂ] B)
      (e : (D ⧸ A.ker) ≃L[ℂ] P),
      (∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧) ∧
      (∀ f s, s.re ∈ I → (F f).val s = modulatedFourierMellin m I hm μ f.val (twist[s])) ∧
      (∀ H s, s.re ∈ I → (T H).val s = H.val (s - phase[b])) ∧
      (∀ f, e (A.ker.mkQ f) = A f) ∧
      (∀ f, T (F f) = M (e (A.ker.mkQ f))) := by
  let pA (A : D →L[ℂ] P) := ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧
  let pF (F : D →L[ℂ] B) := ∀ f (s : ℂ), s.re ∈ I →
    (F f).val s = modulatedFourierMellin m I hm μ f.val (twist[s])
  let pT (T : B ≃L[ℂ] B) := ∀ H (s : ℂ), s.re ∈ I → (T H).val s = H.val (s - phase[b])
  with_reducible_and_instances
    apply exists_diagram_of_split_average (X := D) (Y := P) (Z := B) M pA pF pT
  · exact compactAverage_split m hm I hInt hne τ hτ μ₁ χ
  · intro A hA
    let η : PontryaginDual ℝ≥0ˣ := χ.comp τ
    have hw := scalarProfile_unitary I hInt hne η
    have hη (t : ℝ≥0ˣ) : (η t : ℂ) = (χ (τ t) : ℂ) := rfl
    have hw' (p : P) (t : ℝ≥0ˣ) : (hw.choose p).val (Real.log (t.val : ℝ)) =
        (χ (τ t) : ℂ) * p.val (Real.log (t.val : ℝ)) :=
      (hw.choose_spec p t).trans (congrArg (· * p.val (Real.log (t.val : ℝ))) (hη t))
    with_reducible_and_instances
      exact compactAverage_mellin_maps m hm hms I hOpen hInt hne τ hτ μ₁ μ hμ χ b hb
        A hA hw.choose hw'

include hOpen hInt hne hms in
/-- Paper: Discussion 4.4.1.1(1–2), p. 191. Translation by the inverse generator
acts on the group Mellin transform by the value of the twisted character there. -/
theorem modulatedMellin_translate (f : D) (s : ℂ) (hs : s.re ∈ I) :
    let f' : D := ⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩
    modulatedFourierMellin m I hm μ f'.val (twist[s]) =
      (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) *
        modulatedFourierMellin m I hm μ f.val (twist[s]) := by
  intro f'
  have hmem : twist[s] ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I := by
    change quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 (twist[s]) ∈ I
    rw [quasiCharacterAbscissa_of_unitary_twist m.toMonoidHom hm.1 hm.2 _ χ s (fun _ ↦ rfl)]
    exact hs
  have hval : (twist[s]) γ⁻¹ = (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) := by
    change (χ γ⁻¹ : ℂ) * (((m γ⁻¹).val : ℝ) : ℂ) ^ s = _
    rw [map_inv m γ, Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _), Complex.cpow_neg]
  exact (modulatedFourierMellin_equivariant m I hm hInt hne μ hOpen hms γ⁻¹ f ⟨_, hmem⟩).trans
    (congrArg (· * modulatedFourierMellin m I hm μ f.val (twist[s])) hval)

include hτ in
/-- Paper: Discussion 4.4.1.1(3), p. 191. Compact averaging sends translation by
the inverse generator to dilation of the positive-real profile by its module,
weighted by the character of the inverse generator's compact component. -/
theorem modulatedMellin_average_translate (f : D) (t : ℝ≥0ˣ) :
    (∫ k : K, (χ k.val : ℂ) * f.val (γ * (k.val * τ t)) ∂μ₁) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * avg⟦f, m γ * t⟧ := by
  have hk₀ : γ * (τ (m γ))⁻¹ ∈ K := by
    change m (γ * (τ (m γ))⁻¹) = 1
    rw [map_mul, map_inv m (τ (m γ)), hτ (m γ), mul_inv_cancel]
  obtain ⟨k₀, hk₀v⟩ : ∃ k₀ : K, k₀.val = γ * (τ (m γ))⁻¹ := ⟨⟨_, hk₀⟩, rfl⟩
  have hpt (k : K) : (χ k.val : ℂ) * f.val (γ * (k.val * τ t)) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) *
        ((χ (k₀ * k).val : ℂ) * f.val ((k₀ * k).val * τ (m γ * t))) := by
    have h1 : γ * (k.val * τ t) = (k₀ * k).val * τ (m γ * t) := by
      rw [Subgroup.coe_mul, hk₀v, map_mul τ, mul_assoc γ, mul_assoc γ, mul_comm _ k.val,
        mul_assoc k.val, inv_mul_cancel_left]
    have h2 : k.val = τ (m γ) * γ⁻¹ * (k₀ * k).val := by
      rw [Subgroup.coe_mul, hk₀v, mul_assoc γ, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_left]
    rw [h1, ← mul_assoc, ← Circle.coe_mul, ← map_mul, ← h2]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self
    (fun k : K ↦ (χ k.val : ℂ) * f.val (k.val * τ (m γ * t))) k₀

set_option linter.unusedSectionVars false in
include hτ in
private theorem compactAverage_translate_mem_ker (A : D →L[ℂ] P)
    (hA : ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧)
    (ρ : G →* (D →L[ℂ] D)) (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x))
    (g : G) (f : D) (hf : f ∈ A.ker) : ρ g f ∈ A.ker := by
  change A (ρ g f) = 0
  apply Subtype.ext
  funext x
  change (A (ρ g f)).val x = 0
  let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have ht : Real.log (t.val : ℝ) = x := by
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  have hzero (u : ℝ≥0ˣ) : avg⟦f, u⟧ = 0 :=
    (hA f u).symm.trans (congrArg (fun p : P ↦ p.val (Real.log (u.val : ℝ)))
      (show A f = 0 from hf))
  calc
    (A (ρ g f)).val x = avg⟦ρ g f, t⟧ :=
      (congrArg (A (ρ g f)).val ht.symm).trans (hA _ _)
    _ = ∫ k : K, (χ k.val : ℂ) * f.val (g⁻¹ * (k.val * τ t)) ∂μ₁ :=
      integral_congr_ae (.of_forall fun k ↦ congrArg ((χ k.val : ℂ) * ·) (hρ _ _ _))
    _ = _ := (modulatedMellin_average_translate m g⁻¹ I τ hτ μ₁ χ f t).trans
      ((congrArg (fun c : ℂ ↦ (χ (τ (m g⁻¹) * (g⁻¹)⁻¹) : ℂ) * c)
        (hzero (m g⁻¹ * t))).trans (mul_zero _))

set_option linter.unusedSectionVars false in
include hτ in
/-- Paper: Discussion 4.4.1.1(3), p. 191. The cyclic translation action descends
continuously to the isotypic quotient, realized as the quotient by the kernel
of the compact average in section coordinates. -/
theorem modulatedMellin_isotype_quotient_action (hγ : 1 < (m γ).val)
    (A : D →L[ℂ] P)
    (hA : ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧)
    (ρ : G →* (D →L[ℂ] D)) (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x)) :
    let V := D ⧸ A.ker
    ∃ r : (Γ) →* (V →L[ℂ] V),
      (∀ (g : (Γ)) (f : D), r g (A.ker.mkQ f) = A.ker.mkQ (ρ g.val f)) ∧
      Continuous (fun z : (Γ) × V ↦ r z.1 z.2) := by
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  with_reducible_and_instances
    exact exists_ker_quotientAction (U := G) (X := D) (Y := P) Γ A ρ
      (fun g f hf ↦ compactAverage_translate_mem_ker m I τ hτ μ₁ χ A hA ρ hρ g.val f hf)

include hOpen hInt hne in
/-- Paper: Discussion 4.4.1.1(4), p. 191. The scalar Mellin transform takes the
dilation and compact character factor of the section profile to multiplication
by the corresponding complex power and character value. -/
theorem modulatedMellin_profile_translate (p p' : P)
    (hp : ∀ x : ℝ, p'.val x = (χ (τ (m γ) * γ⁻¹) : ℂ) * p.val (L + x))
    (s : ℂ) (hs : s.re ∈ I) :
    (M p').val s =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) * (M p).val s := by
  have ha : 0 < ((m γ).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m γ))
  rw [positiveRealFourierMellin_apply I hOpen hInt hne p' s hs,
    positiveRealFourierMellin_apply I hOpen hInt hne p s hs, mul_assoc,
    ← smul_eq_mul (a := (((m γ).val : ℝ) : ℂ) ^ (-s)),
    ← mellin_comp_mul_left (fun u ↦ p.val (Real.log u)) s ha, ← smul_eq_mul,
    ← mellin_const_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  simp only [hp, Real.log_mul ha.ne' (mem_Ioi.mp ht).ne', smul_eq_mul]

/-- Paper: Discussion 4.4.1.1(5), p. 191. Translating the group multiplier in the
spectral variable gives the compact character times the scalar multiplier. -/
theorem modulatedMellin_shift_multiplier (b : ℝ)
    (hb : ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ))) (s : ℂ) :
    (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s + phase[b]) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) := by
  have hx : 0 < ((m γ).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m γ))
  have hx' : (((m γ).val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have key : (((m γ).val : ℝ) : ℂ) ^ phase[b] = (χ (τ (m γ)) : ℂ) := by
    rw [hb, Complex.cpow_def_of_ne_zero hx', ← Complex.ofReal_log hx.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [map_mul, Circle.coe_mul, Complex.cpow_add _ _ hx', key]
  ring

end Mellin

/-! ## 4.4.2 Periodization and the exponential system -/

section Periodization

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)

local notation "per[" f ", " x "]" => ∑' n : ℤ, (f).val (γ ^ n * x)

/-- Counting measure on the infinite cyclic subgroup turns its coset integral into the orbit sum. -/
private theorem cyclicOrbitSum_mem (hγ : 1 < (m γ).val) (f : SchwartzBruhat G) :
    (fun z : Q ↦ ∑' n : ℤ, f (γ ^ n * z.out)) ∈ schwartzBruhatSubmodule Q := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let pow (n : ℤ) : Γ := ⟨γ ^ n, Subgroup.zpow_mem_zpowers _ _⟩
  have hinj : Injective pow := by
    intro n k h
    have hv := congrArg (fun g : Γ ↦ (m g.val).val) h
    change (m (γ ^ n)).val = (m (γ ^ k)).val at hv
    simp only [map_zpow, Units.val_zpow_eq_zpow_val] at hv
    exact (zpow_right_strictMono₀ hγ).injective hv
  let e : ℤ ≃ Γ := Equiv.ofBijective pow ⟨hinj, fun g ↦ by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    exact ⟨n, Subtype.ext hn⟩⟩
  have H := lcaCosetIntegral_mem_schwartzBruhat Γ Measure.count
    Subgroup.isClosed_of_discreteTopology f
  convert H.2 using 1
  funext z
  rw [lcaCosetIntegral, integral_countable (H.1 z.out), ← e.tsum_eq]
  apply tsum_congr
  intro n
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact congrArg f.val (mul_comm (γ ^ n) z.out)

include hm hms hγ in
/-- Paper: Definition 4.4.2.1, pp. 191–192. The orbit sum at a representative
belongs to the Schwartz–Bruhat space of the quotient. -/
theorem modulatedPeriodization_mem (f : E) :
    (fun z : Q ↦ per[f, z.out]) ∈ schwartzBruhatSubmodule Q := by
  have hf := modulationWeight_mem_schwartzBruhat m univ ⟨0, mem_univ 0⟩ f
  rw [modulationWeight_zero] at hf
  exact cyclicOrbitSum_mem m γ hγ ⟨f.val, hf⟩

/-- Paper: Definition 4.4.2.1, pp. 191–192. Periodization sums a two-sided
exponentially decaying function over the integer translates of a quotient point. -/
def modulatedPeriodization (f : E) : S :=
  ⟨fun z ↦ per[f, z.out], modulatedPeriodization_mem m γ hm hms hγ f⟩

/-- A function in the Schwartz–Bruhat submodule is bounded. -/
private theorem schwartzBruhatSubmodule_exists_norm_le {H : Type*} [CommGroup H]
    [TopologicalSpace H] {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  let P (g : H → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C
  have hzero : P 0 := ⟨0, fun x ↦ by simp⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x ↦ (norm_add_le (g x) (h x)).trans (add_le_add (hC x) (hD x))⟩
  refine Submodule.iSup_induction (motive := P) _ hg (fun a g hg ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ hg (fun e g hg ↦ ?_) hzero hadd
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  have hb (z) : ‖s z‖ ≤ (elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono (s.property.2 (0, 0, 0, 0)).ne hz
  refine ⟨(elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · simp

/-- A two-sided sequence with geometric decay in both directions is summable. -/
private theorem summable_of_zpow_bounds (u : ℤ → ℂ) (c ρ C₁ C₂ : ℝ) (hc : 1 < c)
    (h1 : ∀ n, ‖u n‖ ≤ C₁ * (c ^ n * ρ)⁻¹) (h2 : ∀ n, ‖u n‖ ≤ C₂ * (c ^ n * ρ)) :
    Summable u := by
  have hg : Summable fun n : ℕ ↦ c⁻¹ ^ n :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hc.le))
      (inv_lt_one_of_one_lt₀ hc)
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_norm_bounded (hg.mul_left (C₁ * ρ⁻¹)) fun n ↦ (h1 n).trans_eq ?_
    change C₁ * (c ^ (n : ℤ) * ρ)⁻¹ = C₁ * ρ⁻¹ * c⁻¹ ^ n
    rw [zpow_natCast, inv_pow]
    ring
  · refine Summable.of_norm_bounded (hg.mul_left (C₂ * ρ)) fun n ↦ (h2 (-n)).trans_eq ?_
    change C₂ * (c ^ (-(n : ℤ)) * ρ) = C₂ * ρ * c⁻¹ ^ n
    rw [zpow_neg, zpow_natCast, inv_pow]
    ring

/-- A two-sided decay function is dominated by the module and by its inverse. -/
private theorem modulatedExponentialDecay_exists_weight_bounds (f : E) :
    ∃ C₁ C₂ : ℝ, ∀ y : G, ‖f.val y‖ ≤ C₁ * ((m y).val : ℝ)⁻¹ ∧
      ‖f.val y‖ ≤ C₂ * ((m y).val : ℝ) := by
  obtain ⟨C₁, h1⟩ := schwartzBruhatSubmodule_exists_norm_le
    (Submodule.mem_comap.mp ((Submodule.mem_iInf _).mp f.property ⟨1, mem_univ 1⟩))
  obtain ⟨C₂, h2⟩ := schwartzBruhatSubmodule_exists_norm_le
    (Submodule.mem_comap.mp ((Submodule.mem_iInf _).mp f.property ⟨-1, mem_univ (-1)⟩))
  refine ⟨C₁, C₂, fun y ↦ ?_⟩
  have hy : 0 < ((m y).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m y))
  have e1 : ‖((((m y).val : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) * f.val y‖ ≤ C₁ := h1 y
  have e2 : ‖((((m y).val : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ) * f.val y‖ ≤ C₂ := h2 y
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _),
    Real.rpow_one] at e1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _),
    Real.rpow_neg_one] at e2
  refine ⟨?_, ((inv_mul_le_iff₀ hy).mp e2).trans_eq (mul_comm _ _)⟩
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hy).mpr ((mul_comm _ _).trans_le e1)

/-- The module of a point of the orbit of the generator. -/
private theorem modulation_zpow_mul (n : ℤ) (z : G) :
    ((m (γ ^ n * z)).val : ℝ) = ((m γ).val : ℝ) ^ n * ((m z).val : ℝ) := by
  rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
    NNReal.coe_zpow]

/-- The periodization at the class of a point is the orbit sum at that point. -/
private theorem modulatedPeriodization_apply_mk (f : E) (x : G) :
    modulatedPeriodization m γ hm hms hγ f (QuotientGroup.mk x) =
      ∑' n : ℤ, f.val (γ ^ n * x) := by
  obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul Γ x
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have e' : (QuotientGroup.mk x : Q).out = γ ^ j * x := e.trans (mul_comm _ _)
  change ∑' n : ℤ, f.val (γ ^ n * (QuotientGroup.mk x : Q).out) = _
  rw [e', ← (Equiv.addRight j).tsum_eq (fun n : ℤ ↦ f.val (γ ^ n * x))]
  refine tsum_congr fun n ↦ ?_
  change f.val (γ ^ n * (γ ^ j * x)) = f.val (γ ^ (n + j) * x)
  rw [zpow_add, mul_assoc]

/-- The orbit series of a two-sided decay function is summable. -/
private theorem modulatedPeriodization_summable (hc : 1 < (m γ).val) (f : E) (x : G) :
    Summable fun n : ℤ ↦ f.val (γ ^ n * x) := by
  obtain ⟨C₁, C₂, hb⟩ := modulatedExponentialDecay_exists_weight_bounds m f
  refine summable_of_zpow_bounds _ ((m γ).val : ℝ) ((m x).val : ℝ) C₁ C₂
    (by exact_mod_cast hc) (fun n ↦ ?_) (fun n ↦ ?_)
  · rw [← modulation_zpow_mul m γ]
    exact (hb _).1
  · rw [← modulation_zpow_mul m γ]
    exact (hb _).2
/-- Paper: Definition 4.4.2.1, p. 192. At every lift of a quotient point the
orbit series converges to the specified periodization. -/
theorem modulatedPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x))
      (modulatedPeriodization m γ hm hms hγ f (QuotientGroup.mk x)) := by
  rw [modulatedPeriodization_apply_mk m γ hm hms hγ f x]
  exact (modulatedPeriodization_summable m γ hγ f x).hasSum
variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "weightedOrbit⟦" f ", " n ", " x "⟧" =>
  ∫ k : K, (χ k.val : ℂ) * (f).val (γ ^ n * (k.val * x)) ∂μ₁

omit [MeasurableSpace G] [BorelSpace G] in
/-- Unitary modulation is translation of the Fourier transform on the dual group. -/
private theorem unitary_mul_mem (η : PontryaginDual G) (f : SchwartzBruhat G) :
    (fun x ↦ (η x : ℂ) * f x) ∈ schwartzBruhatSubmodule G := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  obtain ⟨F, hF⟩ := schwartzBruhat_fourier_equiv (G := G) μ
  let u := F.symm (schwartzBruhatTranslate η (F f))
  let g (x : G) := (η x : ℂ) * f x
  have hη : Continuous (fun x ↦ (η x : ℂ)) := continuous_subtype_val.comp η.continuous
  have hg : Integrable g μ := by
    simpa only [g, mul_comm] using
      (hF f).1.mul_bdd (c := 1) hη.aestronglyMeasurable (.of_forall fun x ↦ by simp)
  have htransform (ψ : PontryaginDual G) : lcaFourier μ u ψ = lcaFourier μ g ψ := by
    rw [← (hF u).2, show F u = _ from F.apply_symm_apply _]
    change F f (η⁻¹ * ψ) = _
    rw [(hF f).2]
    apply integral_congr_ae
    refine .of_forall fun x ↦ ?_
    change f x * star (((η x)⁻¹ * ψ x : Circle) : ℂ) = g x * star (ψ x : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
    dsimp only [g]
    ring
  have hzero (ψ : PontryaginDual G) : lcaFourier μ (u.val - g) ψ = 0 := by
    change (∫ x, (u x - g x) * star (ψ x : ℂ) ∂μ) = 0
    simp_rw [sub_mul]
    rw [integral_sub (integrable_fourierIntegrand μ (hF u).1 ψ)
      (integrable_fourierIntegrand μ hg ψ)]
    exact sub_eq_zero.mpr (htransform ψ)
  have hae : u.val =ᵐ[μ] g := (ae_eq_zero_of_lcaFourier_eq_zero μ ((hF u).1.sub hg)
    hzero).mono fun _ hx ↦ sub_eq_zero.mp hx
  have heq : u.val = g := ((schwartzBruhat_continuous u).ae_eq_iff_eq μ
    (hη.mul (schwartzBruhat_continuous f))).mp hae
  change g ∈ schwartzBruhatSubmodule G
  rw [← heq]
  exact u.property

include hm hms hγ in
/-- Paper: Definition 4.4.2.1, pp. 191–192. The character-weighted orbit
sum at a representative belongs to the Schwartz–Bruhat space of the quotient. -/
theorem modulatedIsotypicPeriodization_mem (f : E) :
    (fun z : Q ↦ ∑' n : ℤ, weightedOrbit⟦f, n, z.out⟧) ∈ schwartzBruhatSubmodule Q := by
  have hf := modulationWeight_mem_schwartzBruhat m univ ⟨0, mem_univ 0⟩ f
  rw [modulationWeight_zero] at hf
  let g : SchwartzBruhat G := ⟨_, unitary_mul_mem χ ⟨f.val, hf⟩⟩
  have hK : IsCompact (K : Set G) := hm.1.isCompact_preimage (isCompact_singleton (x := 1))
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : μ₁.Regular := haar_regular_of_compactSpace μ₁
  let p := schwartzBruhatCosetIntegral K μ₁ hK.isClosed g
  let u : SchwartzBruhat G := ⟨_, schwartzBruhatSubmodule_compactQuotient_pullback_mem
    K hK p.property⟩
  let v : SchwartzBruhat G := ⟨_, unitary_mul_mem χ⁻¹ u⟩
  have hv (y : G) : v y = ∫ k : K, (χ k.val : ℂ) * f.val (k.val * y) ∂μ₁ := by
    change ((χ y)⁻¹ : Circle) * (p (QuotientGroup.mk y) : ℂ) = _
    rw [show p (QuotientGroup.mk y) = _ from schwartzBruhatCosetIntegral_mk K μ₁ hK.isClosed g y,
      ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun k ↦ ?_)
    change _ * ((χ (y * k.val) : ℂ) * f.val (y * k.val)) = _
    rw [map_mul, Circle.coe_mul, ← mul_assoc, ← mul_assoc, ← Circle.coe_mul,
      inv_mul_cancel, Circle.coe_one, one_mul, mul_comm y]
  convert cyclicOrbitSum_mem m γ hγ v using 1
  funext z
  apply tsum_congr
  intro n
  rw [hv]
  exact integral_congr_ae (.of_forall fun k ↦ by dsimp only; rw [mul_left_comm (γ ^ n)])

/-- Paper: Definition 4.4.2.1 and Remark 4.4.2.2, pp. 191–192. Homogeneous
periodization sums the unnormalized compact character averages over the orbit.
The formula weights the translate by the character evaluated at the translating
element and uses only the restriction of the character to the compact group. -/
def modulatedIsotypicPeriodization (f : E) : S :=
  ⟨fun z ↦ ∑' n : ℤ, weightedOrbit⟦f, n, z.out⟧,
    modulatedIsotypicPeriodization_mem m γ hm hms hγ μ₁ χ f⟩

include hm in
/-- Paper: Definition 4.4.2.1, p. 192. For every lift and every integer
translate the compact average is integrable. -/
theorem modulatedIsotypicPeriodization_integrable (f : E) (n : ℤ) (x : G) :
    Integrable (fun k : K ↦ (χ k.val : ℂ) * f.val (γ ^ n * (k.val * x))) μ₁ := by
  have hmem : f.val ∈ schwartzBruhatSubmodule G := by
    have h := (Submodule.mem_iInf _).mp f.property ⟨0, mem_univ 0⟩
    rwa [Submodule.mem_comap, modulationWeight_zero] at h
  have hf : Continuous f.val := schwartzBruhat_continuous (G := G) ⟨f.val, hmem⟩
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hcont : Continuous (fun k : K ↦ (χ k.val : ℂ) * f.val (γ ^ n * (k.val * x))) :=
    (continuous_subtype_val.comp ((map_continuous χ).comp continuous_subtype_val)).mul
      (hf.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The homogeneous periodization at the class of a point is the sum of the compact
averages over the orbit of that point. -/
private theorem modulatedIsotypicPeriodization_apply_mk (f : E) (x : G) :
    modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f (QuotientGroup.mk x) =
      ∑' n : ℤ, weightedOrbit⟦f, n, x⟧ := by
  obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul Γ x
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have e' : (QuotientGroup.mk x : Q).out = γ ^ j * x := e.trans (mul_comm _ _)
  change ∑' n : ℤ, weightedOrbit⟦f, n, (QuotientGroup.mk x : Q).out⟧ = _
  rw [e', ← (Equiv.addRight j).tsum_eq (fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧)]
  refine tsum_congr fun n ↦ integral_congr_ae (.of_forall fun k ↦ ?_)
  change (χ k.val : ℂ) * f.val (γ ^ n * (k.val * (γ ^ j * x))) =
    (χ k.val : ℂ) * f.val (γ ^ (n + j) * (k.val * x))
  rw [zpow_add, mul_assoc, mul_left_comm (γ ^ j)]

/-- The series of the compact averages over an orbit is summable. -/
private theorem modulatedIsotypicPeriodization_summable (hprop : IsModulation m)
    (hc : 1 < (m γ).val) (f : E) (x : G) :
    Summable fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧ := by
  obtain ⟨C₁, C₂, hb⟩ := modulatedExponentialDecay_exists_weight_bounds m f
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp (hprop.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hk (k : K) : ((m (k.val * x)).val : ℝ) = ((m x).val : ℝ) := by
    rw [map_mul m, show m k.val = 1 from MonoidHom.mem_ker.mp k.property, one_mul]
  have hbd (D : ℝ) (n : ℤ) (h : ∀ k : K, ‖f.val (γ ^ n * (k.val * x))‖ ≤ D) :
      ‖weightedOrbit⟦f, n, x⟧‖ ≤ D * μ₁.real univ :=
    norm_integral_le_of_norm_le_const (.of_forall fun k ↦ by
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact h k)
  refine summable_of_zpow_bounds _ ((m γ).val : ℝ) ((m x).val : ℝ) (C₁ * μ₁.real univ)
    (C₂ * μ₁.real univ) (by exact_mod_cast hc) (fun n ↦ ?_) (fun n ↦ ?_)
  · refine (hbd (C₁ * (((m γ).val : ℝ) ^ n * ((m x).val : ℝ))⁻¹) n fun k ↦ ?_).trans_eq
      (by ring)
    rw [← hk k, ← modulation_zpow_mul m γ]
    exact (hb _).1
  · refine (hbd (C₂ * (((m γ).val : ℝ) ^ n * ((m x).val : ℝ))) n fun k ↦ ?_).trans_eq
      (by ring)
    rw [← hk k, ← modulation_zpow_mul m γ]
    exact (hb _).2
/-- Paper: Definition 4.4.2.1, p. 192. At every lift the orbit series of the
compact averages converges to the homogeneous periodization. -/
theorem modulatedIsotypicPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧)
      (modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f (QuotientGroup.mk x)) := by
  rw [modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f x]
  exact (modulatedIsotypicPeriodization_summable m γ μ₁ χ hm hγ f x).hasSum
/-- Paper: Definition 4.4.2.1, p. 192. Left translation by a norm-one element
multiplies the homogeneous periodization by the character evaluated there. -/
theorem modulatedIsotypicPeriodization_homogeneous (f : E) (k : K) (z : Q) :
    let F := modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f
    F (QuotientGroup.mk k.val⁻¹ * z) = (χ k.val : ℂ) * F z := by
  intro F
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : F (QuotientGroup.mk (k.val⁻¹ * x)) = ∑' n : ℤ, weightedOrbit⟦f, n, k.val⁻¹ * x⟧ :=
    modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f _
  have h2 : F (QuotientGroup.mk x) = ∑' n : ℤ, weightedOrbit⟦f, n, x⟧ :=
    modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f x
  rw [← QuotientGroup.mk_mul, h1, h2, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [← integral_const_mul, ← integral_mul_right_eq_self (μ := μ₁) _ k]
  refine integral_congr_ae (.of_forall fun k' ↦ ?_)
  change (χ (k' * k).val : ℂ) * f.val (γ ^ n * ((k' * k).val * (k.val⁻¹ * x))) =
    (χ k.val : ℂ) * ((χ k'.val : ℂ) * f.val (γ ^ n * (k'.val * x)))
  rw [Subgroup.coe_mul, map_mul χ, Circle.coe_mul, mul_assoc k'.val, mul_inv_cancel_left]
  ring
-- TODO(later): needs §4.5.1.1 for convergence in the Schwartz–Bruhat topology
-- and the continuous, open and surjective periodization maps there.

end Periodization

section CyclicCharacters

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)

local notation "J" => PontryaginDual K × ℤ
local notation "expValue[" j ", " x "]" =>
  (χ (j).1 x)⁻¹ * Circle.exp ((t₀ (j).1 - 2 * Real.pi * ((j).2 : ℝ) / L) * logModule x)

-- TODO(paper-gap): Situation 4.4.2.3 calls γ a real number and leaves the
-- restriction equation in (4) unfinished. Here γ is an element of G and
-- the lift restricts to ω.

/-- Paper: Situation 4.4.2.3(4–5), p. 192. Each norm-one character admits a lift
with its section frequency and its phase at the generator.
Deviation: The restriction equation missing from (4) is stated as in Lemma 4.4.2.5. -/
theorem exists_modulatedCyclicCharacter_lifts (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (hγ : 1 < (m γ).val) :
    ∃ (χ : PontryaginDual K → PontryaginDual G) (b t₀ : PontryaginDual K → ℝ),
      (∀ ω (k : K), χ ω k.val = ω k) ∧
      (∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = Circle.exp (b ω * Real.log (t.val : ℝ))) ∧
      (∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ ω * L) = χ ω γ) := by
  have hmem (x : G) : x * (τ (m x))⁻¹ ∈ K := by
    change m (x * (τ (m x))⁻¹) = 1
    rw [map_mul, map_inv, hτ (m x), mul_inv_cancel]
  let p : G →ₜ* K :=
    { toFun := fun x ↦ ⟨x * (τ (m x))⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y ↦ Subtype.ext (by
        change x * y * (τ (m (x * y)))⁻¹ = x * (τ (m x))⁻¹ * (y * (τ (m y))⁻¹)
        rw [map_mul, map_mul, mul_inv, mul_mul_mul_comm])
      continuous_toFun :=
        (continuous_id.mul (τ.continuous.comp m.continuous).inv).subtype_mk hmem }
  let χ : PontryaginDual K → PontryaginDual G := fun ω ↦ ContinuousMonoidHom.comp ω p
  have hphase (ω : PontryaginDual K) :
      ∃ t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ ω γ :=
    (existsUnique_modulatedCharacterPhase m γ hγ (χ ω)).exists
  choose t₀ ht₀ using hphase
  refine ⟨χ, fun _ ↦ 0, t₀, fun ω k ↦ ?_, fun ω t ↦ ?_, ht₀⟩
  · have hk : p k.val = k := Subtype.ext (by
      change k.val * (τ (m k.val))⁻¹ = k.val
      rw [show m k.val = 1 from k.property, map_one, inv_one, mul_one])
    change ω (p k.val) = ω k
    rw [hk]
  · have ht : p (τ t) = 1 := Subtype.ext (by
      change τ t * (τ (m (τ t)))⁻¹ = 1
      rw [hτ t, mul_inv_cancel])
    change ω (p (τ t)) = _
    rw [ht]
    simp

include hm hms hχ in
/-- Paper: Remark 4.4.2.4, p. 192. With the chosen lifts, the norm twists
parametrize all continuous quasi-characters, one complex coordinate per
norm-one character. The unitary characters correspond to the imaginary axis. -/
theorem modulatedCyclicQuasiCharacter_coordinates :
    ∃ e : (PontryaginDual K × ℂ) ≃ₜ QuasiCharacter G,
      (∀ p, e p = quasiCharacterNormTwist m.toMonoidHom m.continuous
        ((circleToComplex).comp (χ p.1)) p.2) ∧
      ∀ p, (∀ x : G, ‖e p x‖ = 1) ↔ p.2.re = 0 := by
  obtain ⟨τ, hτ⟩ := exists_section_of_surjective hm.1 hms
  have : CompactSpace K := isCompact_iff_compactSpace.mp (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  obtain ⟨d, hd⟩ := quasiCharacterParametrization_of_split m.toMonoidHom m.continuous τ hτ
  let c (ω : PontryaginDual K) := (circleToComplex).comp (χ ω)
  let b (ω : PontryaginDual K) := (d (c ω)).1
  let shear : (PontryaginDual K × ℂ) ≃ₜ (ℂ × PontryaginDual K) :=
    { toFun := fun p ↦ (b p.1 + p.2, p.1)
      invFun := fun p ↦ (p.2, p.1 - b p.2)
      left_inv := fun _ ↦ Prod.ext rfl (by dsimp only; abel)
      right_inv := fun _ ↦ Prod.ext (by dsimp only; abel) rfl
      continuous_toFun := ((continuous_of_discreteTopology (f := b)).comp
        continuous_fst |>.add continuous_snd).prodMk continuous_fst
      continuous_invFun := continuous_snd.prodMk (continuous_fst.sub
        ((continuous_of_discreteTopology (f := b)).comp continuous_snd)) }
  let e := shear.trans d.symm
  have he (p : PontryaginDual K × ℂ) : e p =
      quasiCharacterNormTwist m.toMonoidHom m.continuous (c p.1) p.2 := by
    let v := quasiCharacterNormTwist m.toMonoidHom m.continuous (c p.1) p.2
    apply d.injective
    change d (d.symm (shear p)) = d v
    rw [d.apply_symm_apply]
    apply Prod.ext
    · obtain ⟨s, -, hs⟩ := existsUnique_complexPower (v.comp τ)
      apply (hs _ _).trans (hs _ _).symm
      · intro t
        change c p.1 (τ t) * (((m (τ t)).val : ℝ) : ℂ) ^ p.2 =
          ((t.val : ℝ) : ℂ) ^ (b p.1 + p.2)
        rw [hτ t, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
          (NNReal.coe_ne_zero.mpr t.ne_zero)), (hd (c p.1)).1 t]
      · exact (hd v).1
    · apply PontryaginDual.ext
      intro k
      apply Circle.ext
      rw [(hd v).2]
      change (p.1 k : ℂ) = (χ p.1 k.val : ℂ) * (((m k.val).val : ℝ) : ℂ) ^ p.2
      rw [show m k.val = 1 from k.property, hχ]
      simp
  refine ⟨e, he, fun p ↦ ?_⟩
  have hn (x : G) : ‖e p x‖ = ((m x).val : ℝ) ^ p.2.re := by
    rw [he]
    change ‖(χ p.1 x : ℂ) * (((m x).val : ℝ) : ℂ) ^ p.2‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  constructor
  · intro h
    let t := Units.mk0 (2 : ℝ≥0) (by norm_num)
    obtain ⟨x, hx⟩ := hms t
    have H := (hn x).symm.trans (h x)
    rw [hx] at H
    exact (Real.rpow_right_inj (x := 2) (by norm_num) (by norm_num)).mp
      (H.trans (Real.rpow_zero _).symm)
  · intro h x
    rw [hn, h, Real.rpow_zero]

/-- Paper: Lemma 4.4.2.5, p. 193. The cyclic subgroup is closed, so its
quotient is Hausdorff. -/
theorem modulatedCyclicSubgroup_closed (hγ : 1 < (m γ).val) :
    IsClosed (Γ : Set G) := by
  have := modulated_zpowers_discrete m γ hγ
  exact Subgroup.isClosed_of_discreteTopology

/-- Paper: Lemma 4.4.2.5, p. 193. The quotient by the cyclic subgroup is compact. -/
theorem modulatedCyclicQuotient_compact (hm : IsModulation m) (hγ : 1 < (m γ).val) :
    CompactSpace Q := by
  have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m x))
  have hproper : IsProperMap (fun x : G ↦ Real.log ((m x).val : ℝ)) := by
    let e : ℝ≥0ˣ ≃ₜ ℝ :=
      (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
    have he : (e ∘ m) = fun x : G ↦ Real.log ((m x).val : ℝ) :=
      funext fun g ↦ (Real.log_of_pos (hpos g)).symm
    exact he ▸ e.isProperMap.comp hm.1
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have hC := hproper.isCompact_preimage (isCompact_Icc (a := (0 : ℝ)) (b := L))
  have himg :
      ((↑) : G → Q) '' ((fun x : G ↦ Real.log ((m x).val : ℝ)) ⁻¹' Icc 0 L) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := (le_div_iff₀ hL).mp (Int.floor_le (Real.log ((m x).val : ℝ) / L))
    have h2 := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (Real.log ((m x).val : ℝ) / L))
    generalize ⌊Real.log ((m x).val : ℝ) / L⌋ = n at h1 h2
    rw [add_one_mul] at h2
    refine ⟨γ ^ (-n) * x, ?_, ?_⟩
    · have hlog : Real.log ((m (γ ^ (-n) * x)).val : ℝ) =
          Real.log ((m x).val : ℝ) - n * L := by
        rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
          NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos γ).ne') (hpos x).ne',
          Real.log_zpow]
        push_cast
        ring
      change Real.log ((m (γ ^ (-n) * x)).val : ℝ) ∈ Icc 0 L
      rw [hlog]
      constructor <;> linarith
    · rw [QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ _), one_mul]
  rw [← isCompact_univ_iff, ← himg]
  exact hC.image QuotientGroup.continuous_mk

include ht₀ hγ in
/-- Paper: Lemma 4.4.2.5, p. 193. The exponential formula is a continuous
unitary homomorphism on the quotient. -/
theorem modulatedCyclicCharacter_properties (j : J) :
    let u : G → Circle := fun x ↦ expValue[j, x]
    u 1 = 1 ∧ (∀ x y, u (x * y) = u x * u y) ∧ Continuous u ∧
      (∀ x : (Γ), u x.val = 1) := by
  intro u
  have hpos (x : G) : ((m x).val : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hL : L ≠ 0 := (Real.log_pos (by exact_mod_cast hγ)).ne'
  have hone : u 1 = 1 := by simp [u]
  have hmul (x y : G) : u (x * y) = u x * u y := by
    simp only [u, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos x) (hpos y), mul_add,
      Circle.exp_add, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have hcont : Continuous u := by
    have hlog : Continuous fun x : G ↦ logModule x :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log hpos
    exact (map_continuous (χ j.1)).inv.mul
      (Circle.exp.continuous.comp (continuous_const.mul hlog))
  have hgen : u γ = 1 := by
    have harg : (t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L) * L =
        t₀ j.1 * L - 2 * Real.pi * (j.2 : ℝ) := by
      rw [sub_mul, div_mul_cancel₀ _ hL]
    change (χ j.1 γ)⁻¹ * Circle.exp ((t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L) * L) = 1
    rw [harg, Circle.exp_sub, (ht₀ j.1).2, Circle.exp_two_pi_mul_int, div_one, inv_mul_cancel]
  refine ⟨hone, hmul, hcont, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  let U : G →* Circle := { toFun := u, map_one' := hone, map_mul' := hmul }
  have hU (y : G) : U y = u y := rfl
  change u (γ ^ k) = 1
  rw [← hU, map_zpow, hU, hgen, one_zpow]

/-- Paper: Equation (4.4.2.4), p. 193. The lattice character is the inverse of
the chosen lift multiplied by the indicated phase and integer frequency. -/
def modulatedCyclicCharacter (j : J) : PontryaginDual Q :=
  let h := modulatedCyclicCharacter_properties m γ hγ χ t₀ ht₀ j
  let u : G →* Circle :=
    { toFun := fun x ↦ expValue[j, x]
      map_one' := h.1
      map_mul' := h.2.1 }
  let v := QuotientGroup.lift Γ u (fun {x} hx ↦ h.2.2.2 ⟨x, hx⟩)
  ⟨v, (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr h.2.2.1⟩

/-- Paper: Equation (4.4.2.4), p. 193. The quotient character takes its
prescribed value at every representative. -/
theorem modulatedCyclicCharacter_mk (j : J) (x : G) :
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk x) = expValue[j, x] := by
  simp only [modulatedCyclicCharacter]
  rfl

-- TODO(paper-gap): The proof on p. 193 chooses t₁ in an interval open at zero.
-- For the trivial lift this forces t₀ = -t₁ to be the excluded upper endpoint.

include hm hms hχ in
/-- Paper: Lemma 4.4.2.5, p. 193. Pulling the quotient characters back along the
quotient map gives exactly the annihilator, with one pair per character. -/
theorem modulatedCyclicCharacter_annihilator :
    let q : G →ₜ* Q := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
    ∃ e : J ≃ lcaAnnihilator Γ,
      ∀ j, (e j).val = PontryaginDual.map q (modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j) := by
  intro q
  obtain ⟨a, ha⟩ := modulatedCharacter_zpowers_annihilator m hm hms γ hγ χ hχ t₀ ht₀
  refine ⟨a.trans (Equiv.inv _), fun j ↦ PontryaginDual.ext fun x ↦ ?_⟩
  change ((a j).val x)⁻¹ = modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk x)
  rw [modulatedCyclicCharacter_mk, ha j.1 j.2 x, mul_inv, ← Circle.exp_neg, ← neg_mul, neg_sub]

include hm hγ in
/-- Paper: Lemma 4.4.2.5, p. 193. The annihilator carries the discrete topology
induced by the dual of the original group. -/
theorem modulatedCyclicAnnihilator_discrete :
    DiscreteTopology (lcaAnnihilator Γ) := by
  have := modulatedCyclicQuotient_compact m γ hm hγ
  obtain ⟨d, -⟩ := lcaQuotientDual_equiv_annihilator Γ (modulatedCyclicSubgroup_closed m γ hγ)
  exact d.toHomeomorph.discreteTopology_iff.mp inferInstance

end CyclicCharacters

section DiscreteStages
open Filter
open scoped ContDiff


variable {H : Type*} [CommGroup H] [TopologicalSpace H] [DiscreteTopology H]

/-- On a discrete group the trivial subgroup is good, since the dual is compact. -/
private theorem discrete_bot_good : IsBruhatGoodSubgroup (⊥ : Subgroup H) := by
  have hc : IsCompact ((⊥ : Subgroup H) : Set H) := isCompact_singleton
  have : CompactSpace (lcaAnnihilator (⊥ : Subgroup H)) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ (isOpen_discrete _))
  exact ⟨hc.isClosed, isOpen_lcaAnnihilator _ hc, isCompactlyGeneratedGroup_of_compact⟩

/-- A discrete elementary group has no Euclidean or torus coordinates. -/
private theorem discrete_presentation_dims (e : ElementaryLCAPresentation H) :
    e.realDim = 0 ∧ e.torusDim = 0 := by
  have : DiscreteTopology (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    e.equiv.symm.toHomeomorph.isEmbedding.discreteTopology
  let R := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  have hR : Continuous (fun x : R ↦ (x, (0 : T), (0 : Fin e.latticeRank → ℤ), (0 : e.finiteFactor))) :=
    continuous_id.prodMk continuous_const
  have hT : Continuous (fun t : T ↦ ((0 : R), t, (0 : Fin e.latticeRank → ℤ), (0 : e.finiteFactor))) :=
    continuous_const.prodMk (continuous_id.prodMk continuous_const)
  constructor
  · by_contra h
    have : NeZero e.realDim := ⟨h⟩
    obtain ⟨x, hx⟩ := exists_ne (0 : R)
    exact hx (congrArg Prod.fst (hR.isConst_of_preconnectedSpace x 0))
  · by_contra h
    have : NeZero e.torusDim := ⟨h⟩
    obtain ⟨t, ht⟩ := exists_ne (0 : T)
    exact ht (congrArg (fun z ↦ z.2.1) (hT.isConst_of_preconnectedSpace t 0))

/-- Domination in absolute value on a discrete elementary stage controls every defining
seminorm, since all its weights are lattice monomials. -/
private theorem discrete_elementary_solid {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (hm : m = 0) (hn : n = 0)
    (s : ElementarySchwartz m n r F) (f : ElementaryLieGroup m n r F → ℂ)
    (hf : ∀ z, ‖f z‖ ≤ ‖s z‖) :
    ∃ t : ElementarySchwartz m n r F, t.val = f ∧
      ∀ i, elementarySchwartzSeminorm i t ≤ elementarySchwartzSeminorm i s := by
  subst m n
  have hb (i : ElementarySchwartzIndex 0 0 r) :
      elementarySchwartzBound f i ≤ elementarySchwartzBound s.val i := by
    obtain ⟨α, β, γ, δ⟩ := i
    obtain rfl : β = 0 := Subsingleton.elim _ _
    obtain rfl : γ = 0 := Subsingleton.elim _ _
    simp only [elementarySchwartzBound, elementaryPartial_zero, Finset.univ_eq_empty,
      Finset.prod_empty, one_mul, nnNorm_mul]
    gcongr with xt a b
    exact hf _
  have hs (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)) := by
    have h (xt : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) : xt = 0 := Subsingleton.elim _ _
    rw [show (fun xt ↦ f (elementaryCover xt a b)) = fun _ ↦ f (elementaryCover 0 a b) from
      funext fun xt ↦ congrArg (fun y ↦ f (elementaryCover y a b)) (h xt)]
    exact contDiff_const
  refine ⟨⟨f, hs, fun i ↦ (hb i).trans_lt (s.property.2 i)⟩, rfl, fun i ↦ ?_⟩
  exact ENNReal.toReal_mono (s.property.2 i).ne (hb i)

/-- On a stage with trivial kernel an arbitrary subset cuts out an elementary stage
function, with the same bounds as the original one. -/
private theorem discrete_stage_cutoff (b : BruhatStructuralPair H)
    (e : ElementaryLCAPresentation b.quotient) (s : SchwartzBruhatStage e)
    (θ : b.quotient →* H) (hθ : ∀ x : b.val.1, θ (QuotientGroup.mk x) = x)
    (U : Set H) :
    ∃ t : SchwartzBruhatStage e, (∀ i, elementarySchwartzSeminorm i t ≤ elementarySchwartzSeminorm i s) ∧
      schwartzBruhatStageRealization b e t = U.indicator (schwartzBruhatStageRealization b e s) := by
  classical
  let Z := {z | θ (e.equiv.symm (Multiplicative.ofAdd z)) ∈ U}
  have : DiscreteTopology b.quotient := QuotientGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  have hh := discrete_presentation_dims (H := b.quotient) e
  have ht := discrete_elementary_solid hh.1 hh.2 s (Z.indicator s.val) (fun z ↦ by
    by_cases hz : z ∈ Z <;> simp [hz])
  refine ⟨ht.choose, ht.choose_spec.2, funext fun x ↦ ?_⟩
  by_cases hx : x ∈ b.val.1
  · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk (⟨x, hx⟩ : b.val.1)))
    have hy : y ∈ Z ↔ x ∈ U := by
      change θ (e.equiv.symm (e.equiv _)) ∈ U ↔ _
      rw [e.equiv.symm_apply_apply, hθ]
    have hreal (u : SchwartzBruhatStage e) : schwartzBruhatStageRealization b e u x = u y :=
      (schwartzBruhatStageRealization_apply b e u x).trans (dite_eq_left hx)
    have hval := (hreal ht.choose).trans (congrFun ht.choose_spec.1 y)
    by_cases hu : x ∈ U
    · exact hval.trans ((indicator_of_mem (hy.mpr hu) _).trans
        ((hreal s).symm.trans (indicator_of_mem hu _).symm))
    · exact hval.trans ((indicator_of_notMem (hu ∘ hy.mp) _).trans (indicator_of_notMem hu _).symm)
  · have hreal (u : SchwartzBruhatStage e) : schwartzBruhatStageRealization b e u x = 0 :=
      (schwartzBruhatStageRealization_apply b e u x).trans (dite_eq_right hx)
    by_cases hu : x ∈ U
    · exact (hreal ht.choose).trans ((hreal s).symm.trans (indicator_of_mem hu _).symm)
    · exact (hreal ht.choose).trans (indicator_of_notMem hu _).symm

/-- All truncations of a discrete Schwartz–Bruhat function belong to one compact set. -/
private theorem discrete_cutoffs_compact (f : SchwartzBruhat H) :
    ∃ C : Set (SchwartzBruhat H), IsCompact C ∧
      ∀ U : Set H, ∃ u ∈ C, u.val = U.indicator f.val := by
  classical
  obtain ⟨a, d, v, hv⟩ := (mem_schwartzBruhatSubmodule_iff _).mp f.property
  let b : BruhatStructuralPair H := ⟨(a.val.1, OrderDual.toDual ⊥),
    a.property.1, a.property.2.1, discrete_bot_good, bot_le⟩
  let e := b.elementary.some
  have hj := schwartzBruhatStage_transition (a := a) (b := b)
    (show a ≤ b from ⟨le_rfl, (bot_le : (⊥ : Subgroup H) ≤ OrderDual.ofDual a.val.2)⟩) d e
  let s := hj.choose v
  have hs : schwartzBruhatStageRealization b e s = f.val := (hj.choose_spec.1 v).trans hv
  let C : Set (SchwartzBruhatStage e) := {t | ∀ i, elementarySchwartzSeminorm i t ≤
    elementarySchwartzSeminorm i s}
  have hbd : Bornology.IsVonNBounded ℂ C :=
    elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bounded.mpr fun i ↦
      ⟨_, lt_add_of_le_of_pos (apply_nonneg (elementarySchwartzSeminorm i) s) zero_lt_one,
        fun t ht ↦ lt_add_of_le_of_pos (ht i) zero_lt_one⟩
  let : ContinuousSMul ℂ (SchwartzBruhatStage e) := elementarySchwartz_withSeminorms.continuousSMul
  have : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  have hc := elementarySchwartz_isCompact_of_isClosed_isVonNBounded isClosed_closure hbd.closure
  let inc : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat H := schwartzBruhatStageInclusion b e
  refine ⟨inc '' closure C, hc.image (continuous_schwartzBruhatStageInclusion b e), fun U ↦ ?_⟩
  let θ : b.quotient →* H := QuotientGroup.lift _ b.val.1.subtype (fun _ hx ↦ Subgroup.mem_bot.mp hx)
  have ht := discrete_stage_cutoff b e s θ (fun _ ↦ rfl) U
  exact ⟨inc ht.choose, ⟨ht.choose, subset_closure ht.choose_spec.1, rfl⟩,
    ht.choose_spec.2.trans (congrArg U.indicator hs)⟩

/-- In a discrete Bruhat space, pointwise truncation along any enumeration converges
in the Bruhat topology, by compactness of the family and continuity of evaluation. -/
private theorem discrete_cutoffs_tendsto (f : SchwartzBruhat H) (σ : ℕ ≃ H)
    (u : ℕ → SchwartzBruhat H)
    (hu : ∀ n x, u n x = if σ.symm x < n then f x else 0) : Tendsto u atTop (𝓝 f) := by
  classical
  obtain ⟨C, hc, hU⟩ := discrete_cutoffs_compact f
  apply hc.tendsto_nhds_of_unique_mapClusterPt
  · apply Eventually.of_forall
    intro n
    obtain ⟨v, hv, hv'⟩ := hU {x | σ.symm x < n}
    have h : u n = v := by
      apply Subtype.ext
      funext x
      rw [hu, hv']
      by_cases hz : σ.symm x < n <;> simp [hz]
    exact h ▸ hv
  · intro g _ h
    apply Subtype.ext
    funext x
    have hclosed : IsClosed {v : SchwartzBruhat H | v x = f x} :=
      isClosed_eq (continuous_schwartzBruhat_eval x) continuous_const
    exact hclosed.mem_of_mapClusterPt h ((eventually_gt_atTop (σ.symm x)).mono fun n hn ↦
      (hu n x).trans (ite_eq_left hn))

open Classical in
private theorem sum_weighted_delta {T : Type*} (σ : ℕ ≃ T) (u : T → ℂ) (c : ℂ) (hc : c ≠ 0)
    (n : ℕ) (z : T) :
    (∑ i ∈ Finset.range n, (c⁻¹ * u (σ i)) * (if σ i = z then c else 0)) =
      if σ.symm z < n then u z else 0 := by
  classical
  simp only [mul_ite, mul_zero]
  by_cases hz : σ.symm z < n
  · rw [ite_eq_left hz, Finset.sum_eq_single (σ.symm z)]
    · simp [hc, mul_comm]
    · intro k _ hk
      exact ite_eq_right (fun h ↦ hk (σ.eq_symm_apply.mpr h))
    · simp [hz]
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (fun h ↦ hz ((σ.eq_symm_apply.mpr h) ▸ Finset.mem_range.mp hk))

open Classical in
/-- Transport the coordinate expansions from the discrete Fourier side. The factor
in the transform of a character cancels the reciprocal in its coefficient. -/
private theorem basis_of_discrete_fourier {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (F : X ≃L[ℂ] SchwartzBruhat H) (σ : ℕ ≃ H) (c : ℂ) (hc : c ≠ 0)
    (x : ℕ → X) (a : ℕ → StrongDual ℂ X)
    (hx : ∀ n z, F (x n) z = if σ n = z then c else 0)
    (ha : ∀ n v, a n v = c⁻¹ * F v (σ n)) : IsSchauderBasis x a := by
  classical
  constructor
  · intro i j
    change a i (x j) = _
    rw [ha, hx]
    by_cases h : i = j
    · simp [h, hc]
    · simp [h, Ne.symm h]
  · intro v
    change HasSum (fun n ↦ a n v • x n) v (SummationFilter.conditional ℕ)
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    apply F.toHomeomorph.isInducing.tendsto_nhds_iff.mpr
    apply discrete_cutoffs_tendsto (F v) σ
    intro n z
    change F (∑ i ∈ Finset.range n, a i v • x i) z = _
    let ev := schwartzBruhatEvalCLM z
    change ev (F (∑ i ∈ Finset.range n, a i v • x i)) = _
    simp only [map_sum, map_smul, smul_eq_mul]
    change (∑ i ∈ Finset.range n, a i v * F (x i) z) = _
    simp only [ha, hx]
    exact sum_weighted_delta σ (F v).val c hc n z

end DiscreteStages

section DiscreteEstimates

open scoped ContDiff

open Classical in
/-- The point mass in a discrete elementary chart has, for each defining seminorm,
a bound given by the corresponding monomial at its lattice coordinate. -/
private theorem discrete_elementary_delta {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (hm : m = 0) (hn : n = 0)
    (y : ElementaryLieGroup m n r F) :
    ∃ t : ElementarySchwartz m n r F, (∀ z, t z = (Pi.single (M := fun _ ↦ ℂ) y 1) z) ∧
      ∀ i, elementarySchwartzSeminorm i t ≤ ∏ k, |(y.2.2.1 k : ℝ)| ^ i.2.2.2 k := by
  classical
  subst m n
  let f : ElementaryLieGroup 0 0 r F → ℂ := Pi.single y 1
  let w (δ : Fin r → ℕ) := ∏ k, ‖(y.2.2.1 k : ℂ)‖₊ ^ δ k
  have hb (i : ElementarySchwartzIndex 0 0 r) :
      elementarySchwartzBound f i ≤ (w i.2.2.2 : ℝ≥0∞) := by
    obtain ⟨α, β, γ, δ⟩ := i
    obtain rfl : β = 0 := Subsingleton.elim _ _
    obtain rfl : γ = 0 := Subsingleton.elim _ _
    simp only [elementarySchwartzBound, elementaryPartial_zero, Finset.univ_eq_empty,
      Finset.prod_empty, one_mul, iSup_le_iff]
    intro xt a b
    by_cases h : elementaryCover xt a b = y
    · have ha : a = y.2.2.1 := congrArg (fun z : ElementaryLieGroup 0 0 r F ↦ z.2.2.1) h
      rw [h, show f y = 1 from Pi.single_eq_same y _, mul_one, ha]
      simp [w]
    · rw [show f (elementaryCover xt a b) = 0 from Pi.single_eq_of_ne h _, mul_zero, nnNorm_zero]
      exact zero_le
  have hs (a : Fin r → ℤ) (b : F) : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)) := by
    have h (xt : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) : xt = 0 := Subsingleton.elim _ _
    rw [show (fun xt ↦ f (elementaryCover xt a b)) = fun _ ↦ f (elementaryCover 0 a b) from
      funext fun xt ↦ congrArg (fun z ↦ f (elementaryCover z a b)) (h xt)]
    exact contDiff_const
  refine ⟨⟨f, hs, fun i ↦ (hb i).trans_lt ENNReal.coe_lt_top⟩, fun _ ↦ rfl, fun i ↦ ?_⟩
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top (hb i)).trans_eq (by
    simp [w, ← Int.norm_cast_real, Real.norm_eq_abs])

/-- A lattice monomial grows polynomially on an affine integral line. -/
private theorem affine_monomial_bound {r : ℕ} (a b : Fin r → ℤ) (δ : Fin r → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ,
      (∏ k, |((a k + n * b k : ℤ) : ℝ)| ^ δ k) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  let M (k : Fin r) : ℝ := |(a k : ℝ)| + |(b k : ℝ)|
  refine ⟨∏ k, M k ^ δ k, Finset.prod_nonneg fun k _ ↦ pow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) _, ∑ k, δ k, fun n ↦ ?_⟩
  have h (k : Fin r) : |((a k + n * b k : ℤ) : ℝ)| ≤ M k * (1 + |(n : ℝ)|) := by
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    dsimp only [M]
    nlinarith [abs_nonneg (b k : ℝ), mul_nonneg (abs_nonneg (a k : ℝ)) (abs_nonneg (n : ℝ))]
  calc
    _ ≤ ∏ k, (M k * (1 + |(n : ℝ)|)) ^ δ k :=
      Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦ pow_le_pow_left₀ (abs_nonneg _) (h k) _
    _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Take one polynomial bound for a finite family of weights. -/
private theorem finite_polynomial_bound {ι : Type*} (t : Finset ι) (w : ι → ℤ → ℝ)
    (hw : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, w i n ≤ C * (1 + |(n : ℝ)|) ^ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ i ∈ t, ∀ n : ℤ, w i n ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | insert i t _ ih =>
    obtain ⟨C, hC, d, h⟩ := ih
    obtain ⟨B, hB, e, k⟩ := hw i
    refine ⟨max B C, hB.trans (le_max_left _ _), max e d, fun j hj n ↦ ?_⟩
    have hOne : 1 ≤ 1 + |(n : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
    have hone : 0 ≤ 1 + |(n : ℝ)| := zero_le_one.trans hOne
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (k n).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hOne (le_max_left _ _))
        (pow_nonneg hone _) (hB.trans (le_max_left _ _)))
    · exact (h j hj n).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hOne (le_max_right _ _))
        (pow_nonneg hone _) (hC.trans (le_max_right _ _)))

/-- A continuous seminorm of a family of elementary functions is bounded polynomially
if the defining seminorms each have such a bound. -/
private theorem elementary_family_polynomial_bound {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F] (t : ℤ → ElementarySchwartz m n r F)
    (h : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ k : ℤ,
      elementarySchwartzSeminorm i (t k) ≤ C * (1 + |(k : ℝ)|) ^ d)
    (p : Seminorm ℂ (ElementarySchwartz m n r F)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ k : ℤ, p (t k) ≤ C * (1 + |(k : ℝ)|) ^ d := by
  obtain ⟨I, c, -, hc⟩ := Seminorm.bound_of_continuous elementarySchwartz_withSeminorms p hp
  obtain ⟨C, hC, d, hB⟩ := finite_polynomial_bound I (fun i k ↦ elementarySchwartzSeminorm i (t k)) h
  refine ⟨c * C, mul_nonneg c.coe_nonneg hC, d, fun k ↦ ?_⟩
  calc
    _ ≤ (c : ℝ) * I.sup elementarySchwartzSeminorm (t k) := hc _
    _ ≤ (c : ℝ) * (C * (1 + |(k : ℝ)|) ^ d) := mul_le_mul_of_nonneg_left
      (Seminorm.finset_sup_apply_le (mul_nonneg hC (by positivity)) (fun i hi ↦ hB i hi k)) c.coe_nonneg
    _ = _ := (mul_assoc _ _ _).symm

private theorem polynomial_bound_of_le (f g : ℤ → ℝ) (h : ∀ n, f n ≤ g n)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, g n ≤ C * (1 + |(n : ℝ)|) ^ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, f n ≤ C * (1 + |(n : ℝ)|) ^ d := by
  obtain ⟨C, hC, d, hd⟩ := hb
  exact ⟨C, hC, d, fun n ↦ (h n).trans (hd n)⟩

open Classical in
/-- Every affine cyclic family of point masses on a discrete group is contained in a
single elementary stage, with polynomial growth for each continuous seminorm. -/
private theorem discrete_pointMass_polynomial {H : Type*} [CommGroup H] [TopologicalSpace H]
    [DiscreteTopology H] (u v : H) (f : ℤ → SchwartzBruhat H)
    (hf : ∀ n z, f n z = if z = u * v ^ n then 1 else 0)
    (p : Seminorm ℂ (SchwartzBruhat H)) (hp : Continuous p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, p (f n) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  have hJ₀ := exists_openCompactlyGeneratedSubgroup_contains ((isCompact_singleton (x := v)).insert u)
  let J := hJ₀.choose
  have hJ := hJ₀.choose_spec
  let b : BruhatStructuralPair H := ⟨(J.val, OrderDual.toDual ⊥),
    J.property.1, J.property.2, discrete_bot_good, bot_le⟩
  let x : b.val.1 := ⟨u, hJ (mem_insert _ _)⟩
  let y : b.val.1 := ⟨v, hJ (mem_insert_of_mem _ (mem_singleton _))⟩
  let e := b.elementary.some
  let chart : b.val.1 →* Multiplicative (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  let θ : b.quotient →* H := QuotientGroup.lift _ b.val.1.subtype (fun _ hx ↦ Subgroup.mem_bot.mp hx)
  have hinj : Injective chart := fun a c h ↦ Subtype.ext (congrArg θ (e.equiv.injective h))
  let z (n : ℤ) := (chart (x * y ^ n)).toAdd
  have : DiscreteTopology b.quotient := QuotientGroup.discreteTopology_iff.mpr (isOpen_discrete _)
  have hh := discrete_presentation_dims (H := b.quotient) e
  let t (n : ℤ) := (discrete_elementary_delta hh.1 hh.2 (z n)).choose
  have ht (n : ℤ) := (discrete_elementary_delta hh.1 hh.2 (z n)).choose_spec
  let inc : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat H := schwartzBruhatStageInclusion b e
  have heq (n : ℤ) : inc (t n) = f n := by
    apply Subtype.ext
    funext k
    change schwartzBruhatStageRealization b e (t n) k = f n k
    rw [hf, schwartzBruhatStageRealization_apply]
    by_cases hk : k ∈ b.val.1
    · rw [dite_eq_left hk]
      let l : b.val.1 := ⟨k, hk⟩
      change t n (chart l).toAdd = _
      rw [(ht n).1]
      by_cases he : k = u * v ^ n
      · have hl : l = x * y ^ n := Subtype.ext he
        rw [ite_eq_left he, hl]
        exact Pi.single_eq_same _ _
      · rw [ite_eq_right he]
        apply Pi.single_eq_of_ne
        intro h
        exact he (congrArg Subtype.val (hinj h))
    · rw [dite_eq_right hk, ite_eq_right]
      rintro rfl
      exact hk (x * y ^ n).property
  let A := (chart x).toAdd.2.2.1
  let B := (chart y).toAdd.2.2.1
  have hcoord (n : ℤ) (k : Fin e.latticeRank) : (z n).2.2.1 k = A k + n * B k := by
    simp only [z, map_mul, map_zpow]
    change A k + n • B k = _
    simp only [zsmul_eq_mul, Int.cast_id]
  have hpoly (i : ElementarySchwartzIndex e.realDim e.torusDim e.latticeRank) :
      ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, elementarySchwartzSeminorm i (t n) ≤ C * (1 + |(n : ℝ)|) ^ d := by
    refine polynomial_bound_of_le _ _ ?_ (affine_monomial_bound A B i.2.2.2)
    intro n
    exact ((ht n).2 i).trans_eq (Finset.prod_congr rfl (fun k _ ↦
      congrArg (fun a : ℤ ↦ |(a : ℝ)| ^ i.2.2.2 k) (hcoord n k)))
  exact polynomial_bound_of_le _ _ (fun n ↦ (congrArg p (heq n)).symm.le)
    (elementary_family_polynomial_bound t hpoly (p.comp inc) (hp.comp (continuous_schwartzBruhatStageInclusion b e)))
end DiscreteEstimates

open Classical in
/-- The Fourier transform of a compact group character is the point mass at that
character, with height equal to the Haar mass of the group. -/
private theorem fourier_character {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A)
    [μ.IsHaarMeasure] (η ψ : PontryaginDual A) :
    lcaFourier μ (fun x ↦ (η x : ℂ)) ψ = if η = ψ then (μ.real univ : ℂ) else 0 := by
  classical
  by_cases h : η = ψ
  · subst ψ
    simp only [ite_true]
    have hunit (x : A) : (η x : ℂ) * star (η x : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
      simp
    unfold lcaFourier
    calc
      _ = ∫ _ : A, (1 : ℂ) ∂μ := integral_congr_ae (.of_forall hunit)
      _ = _ := by simp [Measure.real]
  · rw [ite_eq_right h]
    obtain ⟨g, hg⟩ : ∃ g, η g ≠ ψ g := by
      by_contra! e
      exact h (PontryaginDual.ext e)
    let c := lcaFourier μ (fun x ↦ (η x : ℂ)) ψ
    have hc : (η g : ℂ) * c = (ψ g : ℂ) * c := calc
      _ = lcaFourier μ (fun x ↦ (η (g * x) : ℂ)) ψ := by
        simp only [lcaFourier, c, map_mul, Circle.coe_mul, mul_assoc, integral_const_mul]
      _ = _ := lcaFourier_translate μ (fun x ↦ (η x : ℂ)) g ψ
    exact (mul_eq_mul_right_iff.mp hc).resolve_left (fun hh ↦ hg (Circle.ext hh))

open Filter in
/-- In a barrelled nuclear space the partial sums of a Schauder basis are equicontinuous
by Banach–Steinhaus, and the nuclear basis criterion gives absoluteness. -/
private theorem absolute_of_barrelled_nuclear {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [BarrelledSpace ℂ X] {x : ℕ → X} {a : ℕ → StrongDual ℂ X}
    (hN : IsNuclearTVS.{0} X) (hb : IsSchauderBasis x a) : SchauderBasis.IsAbsolute x a := by
  have := hN.1
  have := hN.2.1
  let : ContinuousSMul ℂ X := PolynormableSpace.continuousSMul ℂ X
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hconv (z : X) : Tendsto (fun k ↦ SchauderBasis.partialProjection x a k z) atTop (𝓝 z) := by
    have hsum := hb.2 z
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hsum
    simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, SchauderBasis.partialProjection,
      ← Nat.range_succ_eq_Iic, sum_apply, ContinuousLinearMap.smulRight_apply]
      using hsum.comp (tendsto_add_atTop_nat 1)
  exact SchauderBasis.isAbsolute_of_isNuclearTVS hN hb
    ((PolynormableSpace.banach_steinhaus (𝓕 := SchauderBasis.partialProjection x a)
      (fun z ↦ (hconv z).isVonNBounded_range ℂ)).equicontinuous 0)

/-- Reflexivity identifies the coordinates of the dual basis with evaluation. -/
private theorem dual_schwartzBruhat_basis {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    {x : ℕ → SchwartzBruhat H} {a : ℕ → StrongDual ℂ (SchwartzBruhat H)}
    (hb : IsSchauderBasis x a) (ha : SchauderBasis.IsAbsolute x a) :
    let eval := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x n)
    IsSchauderBasis a eval ∧ SchauderBasis.IsAbsolute a eval := by
  let X := SchwartzBruhat H
  have : T2Space X := schwartzBruhat_t2
  have : BarrelledSpace ℂ X := schwartzBruhat_barrelled
  let d := (schwartzBruhat_reflexive (G := H)).choose
  have hd := (schwartzBruhat_reflexive (G := H)).choose_spec
  have href : IsHomeomorph (ContinuousLinearMap.applyₗ («E» := X) ℂ (RingHom.id ℂ)) := by
    convert d.toHomeomorph.isHomeomorph using 1
    exact funext fun u ↦ ContinuousLinearMap.ext fun l ↦ (hd u l).symm
  have h := SchauderBasis.isShrinking_of_isAbsolute («E» := X) schwartzBruhat_complete href hb ha
  have : BarrelledSpace ℂ (StrongDual ℂ X) := schwartzBruhat_strongDual_barrelled
  exact ⟨h, absolute_of_barrelled_nuclear schwartzBruhat_strongDual_nuclear h⟩

/-- On the infinite cyclic group the maximal elementary stage is the integer lattice. -/
theorem integer_schwartz_sequence :
    ∃ A : RapidDecaySequence 1 ≃L[ℂ] SchwartzBruhat (Multiplicative ℤ),
      ∀ s (k : ℤ), A s (Multiplicative.ofAdd k) = s (fun _ ↦ k) := by
  let H := Multiplicative ℤ
  let E₀ := ElementaryLieGroup 0 0 1 PUnit
  let c : H ≃ₜ* Multiplicative E₀ :=
    { toFun := fun n ↦ Multiplicative.ofAdd (0, 0, fun _ ↦ n.toAdd, 0)
      invFun := fun x ↦ Multiplicative.ofAdd (x.toAdd.2.2.1 0)
      left_inv := fun _ ↦ rfl
      right_inv := fun x ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext _ (Subsingleton.elim _ _)
        exact funext fun i ↦ congrArg x.toAdd.2.2.1 (Subsingleton.elim 0 i)
      map_mul' := fun _ _ ↦ by
        apply Multiplicative.toAdd.injective
        apply Prod.ext (Subsingleton.elim _ _)
        apply Prod.ext (Subsingleton.elim _ _)
        exact Prod.ext rfl (Subsingleton.elim _ _)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let p : ElementaryLCAPresentation H := ⟨0, 0, 1, PUnit, c⟩
  have hG := (lca_elementary_iff (G := H)).mpr ⟨p⟩
  let top : (⊤ : Subgroup H) ≃ₜ* H := ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let a : BruhatStructuralPair H := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hG.1,
    isBruhatGoodSubgroup_bot_iff.mpr hG.2, bot_le⟩
  let q : a.quotient ≃* H :=
    QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype top.symm (fun _ ↦ rfl)
  let q' : a.quotient ≃ₜ* H :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_subtype_val
      continuous_invFun := QuotientGroup.continuous_mk.comp top.symm.continuous }
  let e : ElementaryLCAPresentation a.quotient := ⟨0, 0, 1, PUnit, q'.trans c⟩
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat H := schwartzBruhatStageInclusion a e
  have hJ := schwartzBruhatStage_isEmbedding a e
  have hs := schwartzBruhat_maxStage_surjective a (fun b ↦
    (show b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup H) ≤ OrderDual.ofDual b.val.2 from ⟨le_top, bot_le⟩)) e
  let B := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective J ⟨hJ.injective, hs⟩)
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hs⟩)
  have hR := rapidDecaySequence_equiv_elementarySchwartz (r := 1)
  refine ⟨hR.choose.trans B, fun s n ↦ ?_⟩
  change schwartzBruhatStageRealization a e (hR.choose s) (Multiplicative.ofAdd n) = _
  rw [schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top _)]
  exact hR.choose_spec s _

/-- Sampling a Schwartz function on an affine lattice and retaining any subset of
the samples gives a Schwartz–Bruhat function on the infinite cyclic group. -/
theorem schwartzBruhat_of_affine_integer_samples (f : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : a ≠ 0)
    (p : ℤ → Prop) [DecidablePred p] :
    ∃ v : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ,
      v (Multiplicative.ofAdd n) = if p n then f (a * n + b) else 0 := by
  let g : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfAntilipschitz ℂ
    (g := fun t : ℝ ↦ a*t+b) (by fun_prop)
    ((isometry_add_right b).antilipschitzWith.comp (antilipschitzWith_mul_left ha)) f
  let s (i : Fin 1 → ℤ) := if p (i 0) then g (i 0) else 0
  have hs : s ∈ rapidDecaySequenceSubmodule 1 := by
    intro j
    let w (x : ℝ) := ((1 + x^2 : ℝ) : ℂ) ^ j
    have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
    let H := SchwartzMap.smulLeftCLM ℂ w g
    have hH (x : ℝ) : ‖H x‖ = (1 + x^2)^j * ‖g x‖ := by
      change ‖(SchwartzMap.smulLeftCLM ℂ w g) x‖ = _
      rw [SchwartzMap.smulLeftCLM_apply hw, norm_smul]
      dsimp only [w]
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ 1 + x^2)]
    have hsum : Summable (fun n : ℤ ↦ ‖H (n : ℝ)‖) := by
      apply summable_of_isBigO (Real.summable_abs_int_rpow (b := 2) (by norm_num))
      obtain ⟨C, hC⟩ := ((H.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite).bound
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [hC] with n hn
      simpa only [comp_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hn
    have hmajor := hsum.mul_left ((2 : ℝ)^j)
    have hsmall : Summable (fun n : ℤ ↦ (1 + |(n : ℝ)|)^j * ‖s (fun _ ↦ n)‖) := by
      apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ hmajor
      intro n
      change _ ≤ 2^j * ‖H (n : ℝ)‖
      rw [hH, ← mul_assoc, ← mul_pow]
      apply mul_le_mul
      · apply pow_le_pow_left₀ (by positivity)
        nlinarith [sq_abs (n : ℝ), sq_nonneg (|(n : ℝ)| - 1)]
      · by_cases hn : p n <;> simp [s, hn]
      · positivity
      · positivity
    have hbound : rapidDecaySequenceBound j s =
        ∑' n : ℤ, ENNReal.ofReal ((1 + |(n : ℝ)|)^j * ‖s (fun _ ↦ n)‖) := by
      unfold rapidDecaySequenceBound
      rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
      apply tsum_congr
      intro n
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ofReal_norm,
        ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one]
      congr 2
      congr 1
      change ‖(WithLp.toLp 2 (fun _ : Fin 1 ↦ (n : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ₑ = _
      rw [← ofReal_norm, EuclideanSpace.norm_eq]
      simp [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
    rw [hbound, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsmall]
    exact ENNReal.ofReal_lt_top
  obtain ⟨A, hA⟩ := integer_schwartz_sequence
  exact ⟨A ⟨s,hs⟩, fun n ↦ hA ⟨s,hs⟩ n⟩

/-- A polynomially bounded scalar sequence multiplies every Schwartz sequence on the
infinite cyclic group. The weight of order j is controlled by that of order j + d. -/
private theorem integer_schwartz_multiplier (w : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (d : ℕ)
    (hw : ∀ k : ℤ, ‖w k‖ ≤ C * (1 + |(k : ℝ)|) ^ d) (v : SchwartzBruhat (Multiplicative ℤ)) :
    (fun k : Multiplicative ℤ ↦ w k.toAdd * v k) ∈ schwartzBruhatSubmodule (Multiplicative ℤ) := by
  have hA := integer_schwartz_sequence
  let s := hA.choose.symm v
  let f (a : Fin 1 → ℤ) := w (a 0) * s a
  let M : ℝ≥0 := ⟨C, hC⟩
  let N (a : Fin 1 → ℤ) := ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin 1))‖₊
  have hw' (a : Fin 1 → ℤ) : ‖w (a 0)‖₊ ≤ M * (1 + N a) ^ d := by
    change ‖w (a 0)‖ ≤ C * (1 + (N a : ℝ)) ^ d
    have hN : |(a 0 : ℝ)| ≤ (N a : ℝ) :=
      (Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ (a i : ℝ))) 0)
    exact (hw _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add_right hN 1) _) hC)
  have hf (j : ℕ) : rapidDecaySequenceBound j f < ⊤ := by
    calc
      _ ≤ ∑' a, (M : ℝ≥0∞) * ((1 + (N a : ℝ≥0∞)) ^ (j + d) * (‖s a‖₊ : ℝ≥0∞)) := by
        apply tsum_le_tsum
        intro a
        change (1 + (N a : ℝ≥0∞)) ^ j * (‖w (a 0) * s a‖₊ : ℝ≥0∞) ≤
          (M : ℝ≥0∞) * ((1 + (N a : ℝ≥0∞)) ^ (j + d) * (‖s a‖₊ : ℝ≥0∞))
        rw [nnNorm_mul, ENNReal.coe_mul, pow_add]
        have h := ENNReal.coe_le_coe.mpr (hw' a)
        push_cast at h
        calc
          _ ≤ (1 + (N a : ℝ≥0∞)) ^ j * (((M : ℝ≥0∞) * (1 + N a) ^ d) * ‖s a‖₊) := by gcongr
          _ = _ := by ac_rfl
      _ = (M : ℝ≥0∞) * rapidDecaySequenceBound (j + d) s.val := ENNReal.tsum_mul_left
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (s.property _)
  let u := hA.choose (⟨f, hf⟩ : RapidDecaySequence 1)
  have he (k : Multiplicative ℤ) : u k = w k.toAdd * v k := by
    have h := hA.choose_spec (⟨f, hf⟩ : RapidDecaySequence 1) k.toAdd
    exact h.trans (congrArg (w k.toAdd * ·) ((hA.choose_spec s k.toAdd).symm.trans
      (congrArg (fun z : SchwartzBruhat (Multiplicative ℤ) ↦ z k) (hA.choose.apply_symm_apply v))))
  exact (funext he) ▸ u.property

section ExponentialSystem

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)

local notation "J" => PontryaginDual K × ℤ
local notation "ξ" => modulatedCyclicCharacter m γ hγ χ t₀ ht₀

include hm in
/-- Paper: Lemma 4.4.2.6(1), p. 193. The cyclic quotient character, viewed
as a complex-valued function, belongs to the Schwartz–Bruhat space. -/
theorem modulatedCyclicExponential_mem (j : J) :
    (fun z : Q ↦ (ξ j z : ℂ)) ∈ schwartzBruhatSubmodule Q := by
  have : CompactSpace Q := modulatedCyclicQuotient_compact m γ hm hγ
  have : T1Space Q := QuotientGroup.t1Space_iff.mpr (modulatedCyclicSubgroup_closed m γ hγ)
  obtain ⟨c, hc⟩ := compact_schwartzBruhat_one (H := Q)
  simpa only [hc, mul_one] using unitary_mul_mem (ξ j) c

/-- Paper: Equation (4.4.2.5), p. 193. The exponential basis vector is the
complex-valued cyclic quotient character. -/
def modulatedCyclicExponential (j : J) : S :=
  ⟨fun z ↦ (ξ j z : ℂ), modulatedCyclicExponential_mem m γ hm hγ χ t₀ ht₀ j⟩

local notation "e" => modulatedCyclicExponential m γ hm hγ χ t₀ ht₀

/-- Paper: Equation (4.4.2.5), p. 193. In split coordinates the exponential
has the conjugate compact character and the shifted integer frequency. -/
theorem modulatedCyclicExponential_split (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (b : PontryaginDual K → ℝ)
    (hb : ∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = Circle.exp (b ω * Real.log (t.val : ℝ)))
    (j : J) (t : ℝ≥0ˣ) (k : K) (hk : χ j.1 k.val = j.1 k) :
    e j (QuotientGroup.mk (τ t * k.val)) =
      star (j.1 k : ℂ) *
        (Circle.exp ((t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L - b j.1) *
          Real.log (t.val : ℝ)) : ℂ) := by
  have hlog : (logModule (τ t * k.val)) = Real.log (t.val : ℝ) := by
    rw [map_mul, hτ t, show m k.val = 1 from k.2, mul_one]
  change ((modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk (τ t * k.val)) :
    Circle) : ℂ) = _
  rw [modulatedCyclicCharacter_mk, hlog, map_mul, hb, hk, sub_mul _ (b j.1), Circle.exp_sub,
    Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  congr 1
  simp only [mul_inv, div_eq_mul_inv]
  ac_rfl

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [hHaar₁ : μ₁.IsHaarMeasure]

local instance instMeasurableSpaceCyclicQuotientSec4 : MeasurableSpace Q := borel _
local instance instBorelSpaceCyclicQuotientSec4 : BorelSpace Q := ⟨rfl⟩
variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [hHaar : ν.IsHaarMeasure]

local notation "coeff⟦" j "⟧" => (fun f : S ↦ (L * μ₁.real univ)⁻¹ * lcaFourier ν f (ξ j))

/-- A linear functional on the Schwartz–Bruhat space that is bounded by a multiple of the
supremum norm is continuous, because the supremum norm is a continuous seminorm on every
elementary stage. -/
private theorem schwartzBruhat_continuous_of_sup_bound {A : Type*} [CommGroup A]
    [TopologicalSpace A] (Λ : SchwartzBruhat A →ₗ[ℂ] ℂ) (C : ℝ≥0)
    (hΛ : ∀ (f : SchwartzBruhat A) (M : ℝ), (∀ x, ‖f x‖ ≤ M) → ‖Λ f‖ ≤ C * M) :
    Continuous Λ := by
  classical
  let p := (normSeminorm ℂ ℂ).comp Λ
  have hp : ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b s) := by
    intro b s
    let q := (normSeminorm ℂ ℂ).comp (Λ.comp (schwartzBruhatStageInclusion b s))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage s) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    have hpt (f : SchwartzBruhatStage s) (x : A) :
        ‖schwartzBruhatStageRealization b s f x‖ ≤ p₀ f := by
      let := s.finiteGroup
      have he := schwartzBruhatStageRealization_apply b s f x
      by_cases hx : x ∈ b.val.1
      · rw [dite_eq_left hx] at he
        rw [he]
        let y := Multiplicative.toAdd (s.equiv (QuotientGroup.mk ⟨x, hx⟩))
        change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
          (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
            (elementarySchwartzBound_zero f.val).symm
        exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
      · rw [dite_eq_right hx] at he
        exact ((congrArg norm he).trans (norm_zero : ‖(0 : ℂ)‖ = 0)).le.trans
          (apply_nonneg p₀ f)
    have hC : Continuous (C • p₀) := hp₀.const_smul C
    exact Seminorm.continuous_of_le hC fun f ↦
      hΛ (schwartzBruhatStageInclusion b s f) (p₀ f) (hpt f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion b s)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp Λ fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

include hm hHaar₁ hHaar in
/-- Paper: Equation (4.4.2.6), p. 193. With Haar measure on the compact quotient,
the Fourier coefficient formula is linear and continuous in the test function. -/
theorem modulatedCyclicFourierCoeff_linearContinuous (j : J) :
    IsLinearMap ℂ (coeff⟦j⟧) ∧ Continuous (coeff⟦j⟧) := by
  classical
  have := modulatedCyclicQuotient_compact m γ hm hγ
  have hξ : Continuous (fun z : Q ↦ ((ξ j z : Circle) : ℂ)) :=
    continuous_subtype_val.comp (ξ j).continuous
  have hint (f : S) : Integrable (fun z ↦ f z * star ((ξ j z : Circle) : ℂ)) ν :=
    ((schwartzBruhat_continuous f).mul hξ.star).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlin : IsLinearMap ℂ (coeff⟦j⟧) := by
    refine ⟨fun f g ↦ ?_, fun c f ↦ ?_⟩
    · change _ * (∫ z, (f z + g z) * star ((ξ j z : Circle) : ℂ) ∂ν) =
        _ * (∫ z, f z * star ((ξ j z : Circle) : ℂ) ∂ν) +
          _ * ∫ z, g z * star ((ξ j z : Circle) : ℂ) ∂ν
      simp_rw [add_mul]
      rw [integral_add (hint f) (hint g), mul_add]
    · change _ * (∫ z, (c * f z) * star ((ξ j z : Circle) : ℂ) ∂ν) =
        c * (_ * ∫ z, f z * star ((ξ j z : Circle) : ℂ) ∂ν)
      simp_rw [mul_assoc c]
      rw [integral_const_mul, mul_left_comm]
  refine ⟨hlin, ?_⟩
  let C : ℝ≥0 := ⟨‖(((L * μ₁.real univ)⁻¹ : ℝ) : ℂ)‖ * ν.real univ, by positivity⟩
  refine schwartzBruhat_continuous_of_sup_bound (IsLinearMap.mk' _ hlin) C fun f M hM ↦ ?_
  change ‖(((L * μ₁.real univ)⁻¹ : ℝ) : ℂ) * ∫ z, f z * star ((ξ j z : Circle) : ℂ) ∂ν‖ ≤
    ‖(((L * μ₁.real univ)⁻¹ : ℝ) : ℂ)‖ * ν.real univ * M
  rw [norm_mul, mul_assoc, mul_comm (ν.real univ)]
  refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const
    (.of_forall fun z ↦ ?_)) (norm_nonneg _)
  rw [norm_mul, norm_star, Circle.norm_coe, mul_one]
  exact hM z
-- TODO(paper-gap): The exponent in (4.4.2.6) uses log γ, which is undefined
-- for a general group element. The conjugate of (4.4.2.5) uses log|γ|_G.

/-- Paper: Equation (4.4.2.6), p. 193. The coordinate functional integrates
against the conjugate of the exponential and divides by the quotient volume.
Deviation: The denominator inside the printed exponent is read as the logarithm
of the module, in accordance with (4.4.2.5).
Deviation: The page integrates against the Haar measure of the quotient that the measure
of the group and the counting measure of the cyclic subgroup determine, whose total mass
is the divisor used here. In this definition the measure on the quotient is any Haar
measure, so the functional is the printed coefficient only when that measure has this
mass; the basis theorems assume that it does. -/
def modulatedCyclicFourierCoeff (j : J) : StrongDual ℂ S :=
  let h := modulatedCyclicFourierCoeff_linearContinuous m γ hm hγ χ t₀ ht₀ μ₁ ν j
  ⟨IsLinearMap.mk' (coeff⟦j⟧) h.1, h.2⟩

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν

/-- Paper: Equation (4.4.2.6), p. 193. The coefficient integrates the
Schwartz–Bruhat function against the conjugate exponential with the stated normalization. -/
theorem modulatedCyclicFourierCoeff_apply (j : J) (f : S) :
    Integrable (fun z ↦ f z * star (e j z)) ν ∧
    a j f = (L * μ₁.real univ)⁻¹ * ∫ z, f z * star (e j z) ∂ν := by
  have := modulatedCyclicQuotient_compact m γ hm hγ
  refine ⟨?_, rfl⟩
  have hξ : Continuous (fun z : Q ↦ ((ξ j z : Circle) : ℂ)) :=
    continuous_subtype_val.comp (ξ j).continuous
  exact ((schwartzBruhat_continuous f).mul hξ.star).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable [SecondCountableTopology G]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G)
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

include hm hγ hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. The Weil quotient measure has total mass
equal to the product of the logarithmic period and the volume of the norm-one group. -/
theorem modulatedCyclicQuotient_measure_univ :
    ν univ = ENNReal.ofReal L * μ₁ univ := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  have hΓ : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  have : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hφ : Continuous fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2 := by fun_prop
  -- The measure `μ` is a Haar measure: a multiple of the canonical one.
  let μ₀ : Measure K := Measure.haarMeasure ⊤
  have hcan := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₀ Measure.haarMeasure_self
  have : (canonicalModulatedHaar m hm).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hscale := Measure.isMulLeftInvariant_eq_smul μ₁ μ₀
  set c := Measure.haarScalarFactor μ₁ μ₀
  have hc : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [ENNReal.coe_eq_zero] at h
    rw [h, zero_smul] at hscale
    exact NeZero.ne μ₁ hscale
  have hprod : μ₁.prod positiveRealHaar = c • μ₀.prod positiveRealHaar := by
    rw [← Measure.prod_smul_left, ← hscale]
  have hμc : μ = (c : ℝ≥0∞) • canonicalModulatedHaar m hm := by
    rw [hμ, hprod, Measure.map_smul _ hφ.aemeasurable, hcan, ENNReal.smul_def]
  have : μ.IsHaarMeasure := hμc ▸ Measure.IsHaarMeasure.smul _ hc ENNReal.coe_ne_top
  have : μ.Regular := by
    let μH : Measure G := Measure.haarMeasure (Classical.arbitrary _)
    rw [Measure.isMulLeftInvariant_eq_smul μ μH]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  -- A Borel fundamental domain for the cyclic subgroup.
  let ℓ : G → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  have hpos (x : G) : (0 : ℝ) < (m x).val := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hℓ (x : G) (k : ℤ) : ℓ (x * γ ^ k) = ℓ x + k * L := by
    simp only [ℓ, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (hpos x).ne' (zpow_pos (hpos γ) k).ne', Real.log_zpow]
  let Δ : Set G := {x | ((m x).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)}
  have hmemΔ (x : G) : x ∈ Δ ↔ ℓ x ∈ Ico 0 L := by
    change ((m x).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ) ↔ _
    simp only [mem_Ico, ℓ, Real.log_nonneg_iff (hpos x), Real.log_lt_log_iff (hpos x) (hpos γ)]
  have hcontm : Continuous fun x : G ↦ ((m x).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hΔ : MeasurableSet Δ := hcontm.measurable measurableSet_Ico
  have hbij : Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : Q)) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp hxy)
      have hyx : y = x * γ ^ k := by rw [hk, mul_inv_cancel_left]
      have hx' := (hmemΔ x).mp hx
      have hy' := (hmemΔ y).mp hy
      rw [hyx, hℓ] at hy'
      have h1 : (k : ℝ) < 1 := by
        by_contra h
        nlinarith [hx'.1, hy'.2]
      have h2 : (-1 : ℝ) < k := by
        by_contra h
        nlinarith [hx'.2, hy'.1]
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast h1
        have : -1 < k := by exact_mod_cast h2
        omega
      exact Subtype.ext (show x = y by rw [hyx, hk0, zpow_zero, mul_one])
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      let k : ℤ := -⌊ℓ x / L⌋
      refine ⟨⟨x * γ ^ k, (hmemΔ _).mpr ?_⟩, ?_⟩
      · rw [hℓ]
        have hf := Int.floor_le (ℓ x / L)
        have hf' := Int.lt_floor_add_one (ℓ x / L)
        rw [le_div_iff₀ hL] at hf
        rw [div_lt_iff₀ hL] at hf'
        constructor
        · simp only [k, Int.cast_neg]; nlinarith
        · simp only [k, Int.cast_neg]; nlinarith
      · exact QuotientGroup.mk_mul_of_mem x (Subgroup.zpow_mem_zpowers γ k)
  -- The mass of the fundamental domain.
  have hPR : positiveRealHaar {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} =
      ENNReal.ofReal L := by
    let ex (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
    have he : Measurable ex :=
      measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
    have hset : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} :=
      measurableSet_Ico.preimage
        (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
    change (volume.map ex) _ = _
    rw [Measure.map_apply he hset]
    have hpre : ex ⁻¹' {t | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} = Ico 0 L := by
      ext x
      change (1 ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) < _) ↔ _
      rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.one_le_exp_iff,
        ← Real.lt_log_iff_exp_lt (hpos γ)]
      rfl
    rw [hpre, Real.volume_Ico, sub_zero]
  have hμΔ : μ Δ = μ₁ univ * ENNReal.ofReal L := by
    rw [hμ, Measure.map_apply hφ.measurable hΔ]
    have hpre : (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) ⁻¹' Δ =
        univ ×ˢ {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} := by
      ext ⟨k, t⟩
      have hk : m (k : G) = 1 := k.property
      change ((m ((k : G) * τ t)).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ) ↔ _
      rw [map_mul, hk, one_mul, hτ t]
      simp
    rw [hpre, Measure.prod_prod, hPR]
  -- Weil's formula for the constant function one.
  have hΔfin : μ Δ ≠ ∞ := by
    rw [hμΔ]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hint : Integrable (fun _ : Q ↦ (1 : ℂ)) ν := by
    rw [weilFundamentalDomain_integrable_iff Γ hΓ μ hΔ hbij ν hν]
    exact (integrable_indicator_iff hΔ).mpr (integrableOn_const hΔfin)
  have heq := weilFundamentalDomain_integral Γ hΓ μ hΔ hbij ν hν hint
  have hνfin : ν univ ≠ ∞ := by
    have := (integrable_const_iff.mp hint).resolve_left one_ne_zero
    exact measure_ne_top ν univ
  simp only [integral_const, measureReal_restrict_apply_univ, Complex.real_smul, mul_one,
    Complex.ofReal_inj] at heq
  have hreal : ν.real univ = μ.real Δ := heq
  rw [← ENNReal.ofReal_toReal hνfin, ← measureReal_def, hreal, measureReal_def,
    ENNReal.ofReal_toReal hΔfin, hμΔ, mul_comm]

set_option linter.unusedSectionVars false in
include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6(1), p. 193. Every enumeration of the full character
index gives an absolute Schauder basis, with the Fourier coefficients as coordinates. -/
theorem modulatedCyclicExponential_absoluteBasis :
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, IsSchauderBasis (e ∘ σ) (a ∘ σ) ∧
        SchauderBasis.IsAbsolute (e ∘ σ) (a ∘ σ) := by
  classical
  have hc := modulatedCyclicSubgroup_closed m γ hγ
  have : T1Space Q := QuotientGroup.t1Space_iff.mpr hc
  have : CompactSpace Q := modulatedCyclicQuotient_compact m γ hm hγ
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have : SecondCountableTopology Circle := inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  have : SecondCountableTopology (PontryaginDual K) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap K Circle).secondCountableTopology
  have : Countable (PontryaginDual K) := countable_of_Lindelof_of_discrete
  refine ⟨nonempty_equiv_of_countable, fun σ ↦ ?_⟩
  have hi := modulatedCyclicCharacter_annihilator m γ hm hms hγ χ hχ t₀ ht₀
  have hd := lcaQuotientDual_equiv_annihilator Γ hc
  let θ := (σ.trans hi.choose).trans hd.choose.symm.toEquiv
  have hθ (n : ℕ) : θ n = ξ (σ n) := by
    apply hd.choose.injective
    change hd.choose (hd.choose.symm _) = _
    rw [hd.choose.apply_symm_apply]
    apply Subtype.ext
    exact PontryaginDual.ext fun x ↦
      (DFunLike.congr_fun (hi.choose_spec (σ n)) x).trans (hd.choose_spec (ξ (σ n)) x).symm
  have hmass : ν.real univ = L * μ₁.real univ := by
    rw [Measure.real, modulatedCyclicQuotient_measure_univ m γ hm hγ μ₁ ν τ hτ μ hμ hν,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.log_pos (by exact_mod_cast hγ)).le]
    rfl
  have : ν.Regular := haar_regular_of_compactSpace ν
  let F := (schwartzBruhat_fourier_equiv (G := Q) ν).choose
  have hF := (schwartzBruhat_fourier_equiv (G := Q) ν).choose_spec
  have hchar (j : J) (z : PontryaginDual Q) : F (e j) z = if ξ j = z then (ν.real univ : ℂ) else 0 :=
    ((hF (e j)).2 z).trans (fourier_character ν (ξ j) z)
  have hscalar : (((L * μ₁.real univ)⁻¹ : ℝ) : ℂ) = (ν.real univ : ℂ)⁻¹ :=
    (Complex.ofReal_inv _).trans (congrArg (fun r : ℝ ↦ (r : ℂ)⁻¹) hmass.symm)
  have hcoeff (j : J) (f : S) : a j f = (ν.real univ : ℂ)⁻¹ * F f (ξ j) :=
    congrArg₂ (· * ·) hscalar ((hF f).2 (ξ j)).symm
  have hx (n : ℕ) (z : PontryaginDual Q) : F ((e ∘ σ) n) z = if θ n = z then (ν.real univ : ℂ) else 0 :=
    (hchar (σ n) z).trans (congrArg (fun t ↦ if t = z then (ν.real univ : ℂ) else 0) (hθ n).symm)
  have ha (n : ℕ) (f : S) : (a ∘ σ) n f = (ν.real univ : ℂ)⁻¹ * F f (θ n) :=
    (hcoeff (σ n) f).trans (congrArg (fun t ↦ (ν.real univ : ℂ)⁻¹ * F f t) (hθ n).symm)
  have hb : IsSchauderBasis (e ∘ σ) (a ∘ σ) := by
    with_reducible_and_instances
      exact basis_of_discrete_fourier (H := PontryaginDual Q) (X := S) F θ (ν.real univ)
        (Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne') (e ∘ σ) (a ∘ σ) hx ha
  have : BarrelledSpace ℂ S := schwartzBruhat_barrelled
  exact ⟨hb, absolute_of_barrelled_nuclear schwartzBruhat_nuclear hb⟩

include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6, p. 197. The coefficient functionals in any such
enumeration form an absolute Schauder basis of the strong dual. Its coordinate
functionals are evaluations at the original exponentials. -/
theorem modulatedCyclicFourierCoeff_absoluteBasis (σ : ℕ ≃ J) :
    let eval : ℕ → StrongDual ℂ (StrongDual ℂ S) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e (σ n))
    IsSchauderBasis (a ∘ σ) eval ∧ SchauderBasis.IsAbsolute (a ∘ σ) eval := by
  have : T1Space Q := QuotientGroup.t1Space_iff.mpr (modulatedCyclicSubgroup_closed m γ hγ)
  have h := (modulatedCyclicExponential_absoluteBasis m γ hm hms hγ χ hχ t₀ ht₀ μ₁ ν
    τ hτ μ hμ hν).2 σ
  exact dual_schwartzBruhat_basis h.1 h.2

-- TODO(paper-gap): In (4.4.2.10) the Fourier transform must be evaluated
-- at the basis character itself with the displayed Fourier convention.

include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6(2a), p. 194. A unique Schwartz–Bruhat function on
the annihilator assigns each basis character its coordinate coefficient. -/
theorem modulatedCyclicFourierCoeff_schwartz (f : S) :
    let q : G →ₜ* Q := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
    ∃! v : SchwartzBruhat (lcaAnnihilator Γ), ∀ j : J,
      ∀ η : lcaAnnihilator Γ, η.val = PontryaginDual.map q (ξ j) → v η = a j f := by
  intro q
  have hc := modulatedCyclicSubgroup_closed m γ hγ
  have : T1Space Q := QuotientGroup.t1Space_iff.mpr hc
  have : CompactSpace Q := modulatedCyclicQuotient_compact m γ hm hγ
  have : ν.Regular := hν.2.1
  let d := (lcaQuotientDual_equiv_annihilator Γ hc).choose
  have hd := (lcaQuotientDual_equiv_annihilator Γ hc).choose_spec
  have : DiscreteTopology (lcaAnnihilator Γ) := modulatedCyclicAnnihilator_discrete m γ hm hγ
  let T := (schwartzBruhat_congr d).choose
  have hT := (schwartzBruhat_congr d).choose_spec
  let F := (schwartzBruhat_fourier_equiv (G := Q) ν).choose
  have hF := (schwartzBruhat_fourier_equiv (G := Q) ν).choose_spec
  let v := (((L * μ₁.real univ)⁻¹ : ℝ) : ℂ) • T (F f)
  have hv (j : J) (η : lcaAnnihilator Γ) (hη : η.val = PontryaginDual.map q (ξ j)) :
      v η = a j f := by
    have h : d (ξ j) = η := Subtype.ext (PontryaginDual.ext fun x ↦
      (hd (ξ j) x).trans (DFunLike.congr_fun hη.symm x))
    rw [← h]
    change _ * T (F f) (d (ξ j)) = _ * lcaFourier ν f (ξ j)
    rw [hT, (hF f).2]
  refine ⟨v, hv, fun w hw ↦ Subtype.ext (funext fun η ↦ ?_)⟩
  obtain ⟨idx, hi⟩ := modulatedCyclicCharacter_annihilator m γ hm hms hγ χ hχ t₀ ht₀
  obtain ⟨j, rfl⟩ := idx.surjective η
  exact (hw j _ (hi j)).trans (hv j _ (hi j)).symm

/-- In one compact character component, successive integer frequencies differ
by powers of a single quotient character. -/
private theorem cyclic_character_line (ω : PontryaginDual K) :
    ∀ n : ℤ, ξ (ω, n) = ξ (ω, 0) * ((ξ (ω, 0))⁻¹ * ξ (ω, 1)) ^ n := by
  intro n
  apply PontryaginDual.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | _ x =>
    let A := (χ ω x)⁻¹ * Circle.exp (t₀ ω * (logModule x))
    let step := -(2 * Real.pi / L) * (logModule x)
    have h (k : ℤ) : ξ (ω, k) (QuotientGroup.mk x) = A * Circle.exp step ^ k := by
      have ha : (t₀ ω - 2 * Real.pi * (k : ℝ) / L) * (logModule x) =
          t₀ ω * (logModule x) + k • step := by
        dsimp only [step]
        rw [zsmul_eq_mul]
        ring
      rw [modulatedCyclicCharacter_mk]
      change (χ ω x)⁻¹ * Circle.exp ((t₀ ω - 2 * Real.pi * (k : ℝ) / L) * (logModule x)) = _
      rw [ha, Circle.exp_add, Circle.exp_zsmul]
      exact (mul_assoc _ _ _).symm
    let ev : PontryaginDual Q →* Circle :=
      { toFun := fun δ ↦ δ (QuotientGroup.mk x)
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    change ev (ξ (ω, n)) = ev (_ * _ ^ n)
    rw [map_mul ev, map_zpow ev, map_mul ev, map_inv ev]
    change ξ (ω, n) (QuotientGroup.mk x) = ξ (ω, 0) (QuotientGroup.mk x) *
      ((ξ (ω, 0) (QuotientGroup.mk x))⁻¹ * ξ (ω, 1) (QuotientGroup.mk x)) ^ n
    simp only [h, zpow_zero, mul_one, zpow_one, inv_mul_cancel_left]

/-- Paper: Remark 4.4.2.9, p. 194. At a fixed compact character the values of a
continuous seminorm on the cyclic exponentials have polynomial growth.
Deviation: The polynomial bound is expressed with a nonnegative constant and
a power of one plus the absolute frequency. -/
theorem modulatedCyclicExponential_seminorm_polynomialGrowth
    (p : Seminorm ℂ S) (hp : Continuous p) (ω : PontryaginDual K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, p (e (ω, n)) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  have : T1Space Q := QuotientGroup.t1Space_iff.mpr (modulatedCyclicSubgroup_closed m γ hγ)
  have : CompactSpace Q := modulatedCyclicQuotient_compact m γ hm hγ
  let μ₀ : Measure Q := Measure.haarMeasure ⊤
  have hμ₀ : μ₀ univ = 1 := Measure.haarMeasure_self
  have h₁ : (μ₀.real univ : ℂ) = 1 := by simp [Measure.real, hμ₀]
  let F := (schwartzBruhat_fourier_equiv (G := Q) μ₀).choose
  have hF := (schwartzBruhat_fourier_equiv (G := Q) μ₀).choose_spec
  let A := ξ (ω, 0)
  let B₁ := A⁻¹ * ξ (ω, 1)
  let f (n : ℤ) := F (e (ω, n))
  have hf (n : ℤ) (z : PontryaginDual Q) : f n z = if z = A * B₁ ^ n then 1 else 0 := by
    have ht := ((hF (e (ω, n))).2 z).trans (fourier_character μ₀ (ξ (ω, n)) z)
    have hn := cyclic_character_line m γ hγ χ t₀ ht₀ ω n
    have he : ξ (ω, n) = A * B₁ ^ n := hn
    exact ht.trans (by rw [he, h₁, (eq_comm : A * B₁ ^ n = z ↔ z = A * B₁ ^ n)])
  have hb := discrete_pointMass_polynomial A B₁ f hf (p.comp F.symm.toLinearEquiv.toLinearMap)
    (hp.comp F.symm.continuous)
  exact polynomial_bound_of_le _ _ (fun n ↦ (congrArg p (F.symm_apply_apply (e (ω, n)))).symm.le) hb

/-- Paper: Lemma 4.4.2.6(2b), p. 194. For a fixed compact character, the seminorm
values of the exponential vectors multiply every Schwartz sequence into another
Schwartz sequence. The integers are written multiplicatively in the Bruhat space. -/
theorem modulatedCyclicExponential_seminorm_multiplier
    (p : Seminorm ℂ S) (hp : Continuous p) (ω : PontryaginDual K)
    (v : SchwartzBruhat (Multiplicative ℤ)) :
    (fun n : Multiplicative ℤ ↦ (p (e (ω, n.toAdd)) : ℂ) * v n) ∈
      schwartzBruhatSubmodule (Multiplicative ℤ) := by
  have h := modulatedCyclicExponential_seminorm_polynomialGrowth m γ hm hγ χ t₀ ht₀ p hp ω
  let C := h.choose
  let d := h.choose_spec.2.choose
  have hd := h.choose_spec.2.choose_spec
  let w (n : ℤ) : ℂ := (p (e (ω, n)) : ℂ)
  have hw (n : ℤ) : ‖w n‖ ≤ C * (1 + |(n : ℝ)|) ^ d :=
    (Complex.norm_of_nonneg (apply_nonneg p _)).le.trans (hd n)
  with_reducible_and_instances
    exact integer_schwartz_multiplier w C h.choose_spec.1 d hw v

include hm hγ hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Dividing the quotient Haar measure by its
specified total mass gives the probability Haar measure. -/
theorem modulatedCyclicQuotient_probabilityHaar :
    IsProbabilityMeasure ((ENNReal.ofReal L * μ₁ univ)⁻¹ • ν) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have h0 : ENNReal.ofReal L * μ₁ univ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hL).ne' (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ₁))
  have htop : ENNReal.ofReal L * μ₁ univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ₁ univ)
  constructor
  rw [smul_apply, smul_eq_mul,
    modulatedCyclicQuotient_measure_univ m γ hm hγ μ₁ ν τ hτ μ hμ hν,
    ENNReal.inv_mul_cancel h0 htop]

include hms hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Normalizing the norm-one Haar measure to
mass one gives the same Weil quotient measure as dividing by that mass
after taking the quotient. -/
theorem modulatedCyclicQuotient_canonicalHaar :
    IsWeilQuotientMeasure Γ (canonicalModulatedHaar m hm) Measure.count ((μ₁ univ)⁻¹ • ν) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hφ : Continuous fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2 := by fun_prop
  -- The canonical measure is `μ` divided by the mass of the norm-one group.
  let μ₀ : Measure K := Measure.haarMeasure ⊤
  have hμ₀ : μ₀ univ = 1 := Measure.haarMeasure_self
  have hcan := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₀ hμ₀
  have hscale := Measure.isMulLeftInvariant_eq_smul μ₁ μ₀
  set c := Measure.haarScalarFactor μ₁ μ₀
  have hc : μ₁ univ = c := by
    conv_lhs => rw [hscale]
    rw [smul_apply, hμ₀, ENNReal.smul_def, smul_eq_mul, mul_one]
  have h0 : μ₁ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne μ₁)
  have htop : μ₁ univ ≠ ∞ := measure_ne_top μ₁ univ
  have hprod : μ₁.prod positiveRealHaar = c • μ₀.prod positiveRealHaar := by
    rw [← Measure.prod_smul_left, ← hscale]
  have hμc : μ = μ₁ univ • canonicalModulatedHaar m hm := by
    rw [hμ, hprod, Measure.map_smul _ hφ.aemeasurable, hcan, ENNReal.smul_def, hc]
  have hcanμ : canonicalModulatedHaar m hm = (μ₁ univ)⁻¹ • μ := by
    rw [hμc, smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]
  -- Rescale both sides of Weil's formula.
  obtain ⟨hνH, hνR, hW⟩ := hν
  refine ⟨Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr h0), Measure.Regular.smul (ENNReal.inv_ne_top.mpr h0),
    fun f hf ↦ ?_⟩
  rw [hcanμ, integral_smul_measure, integral_smul_measure, hW f hf]

-- TODO(paper-gap): Remark 4.4.2.8 gives no transport map for the topology of
-- the multiplier space. Its algebraic membership is used in Lemma 4.4.2.6(2b).
-- Its seminorm example on the positive reals also uses a function outside S(ℝ>0).

/-- Paper: Remark 4.4.2.9, p. 194. Multiplication by a unitary character
preserves the Schwartz–Bruhat space of the original group. -/
theorem pontryaginDual_mul_schwartzBruhat (η : PontryaginDual G) (f : SchwartzBruhat G) :
    (fun x ↦ (η x : ℂ) * f x) ∈ schwartzBruhatSubmodule G := by
  -- The Fourier transform turns multiplication by `η` into translation on the dual group.
  let μ : Measure G := Measure.haar
  have : μ.IsHaarMeasure := inferInstanceAs ((Measure.haar (G := G)).IsHaarMeasure)
  have : μ.Regular := inferInstanceAs ((Measure.haar (G := G)).Regular)
  obtain ⟨F, hF⟩ := schwartzBruhat_fourier_equiv (G := G) μ
  obtain ⟨Φ, hΦ, hinj, -⟩ := lcaFourier_L1 (G := G) μ
  let v : SchwartzBruhat G := F.symm (schwartzBruhatTranslate η (F f))
  let u : G → ℂ := v
  let g (y : G) := (η y : ℂ) * f y
  have hη : Continuous (fun y : G ↦ (η y : ℂ)) := continuous_subtype_val.comp η.continuous
  have hg : Integrable g μ := by
    simpa only [g, mul_comm] using
      (hF f).1.mul_bdd (c := 1) hη.aestronglyMeasurable (.of_forall fun y ↦ by simp)
  have hu : Integrable u μ := (hF v).1
  have htransform (χ : PontryaginDual G) : lcaFourier μ u χ = lcaFourier μ g χ := by
    rw [← (hF v).2 χ]
    have hv : F v = schwartzBruhatTranslate η (F f) := F.apply_symm_apply _
    rw [hv]
    change F f (η⁻¹ * χ) = _
    rw [(hF f).2]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y ↦ by
      change f y * star (((η y)⁻¹ * χ y : Circle) : ℂ) = g y * star (χ y : ℂ)
      rw [Circle.coe_mul, Circle.coe_inv_eq_conj, ← Complex.star_def, star_mul, star_star]
      dsimp only [g]
      ring
  have hcoe (w : G → ℂ) (hw : Integrable w μ) (χ : PontryaginDual G) :
      Φ (hw.toL1 w) χ = lcaFourier μ w χ := by
    rw [hΦ]
    exact integral_congr_ae (hw.coeFn_toL1.mono fun y hy ↦ congrArg (· * star (χ y : ℂ)) hy)
  have hL1 : hu.toL1 u = hg.toL1 g :=
    hinj (ZeroAtInftyContinuousMap.ext fun χ ↦ by rw [hcoe, hcoe, htransform])
  have hae : u =ᵐ[μ] g := (Integrable.toL1_eq_toL1_iff u g hu hg).mp hL1
  have heq : u = g := ((schwartzBruhat_continuous v).ae_eq_iff_eq μ
    (hη.mul (schwartzBruhat_continuous f))).mp hae
  exact (congrArg (· ∈ schwartzBruhatSubmodule G) heq).mp v.property

-- TODO(paper-gap): The proof on p. 195 asserts that the coefficients vanish
-- on the annihilator of the stage subgroup. They vanish off that annihilator.
-- TODO(paper-gap): For (4.4.2.8), a finite-set exhaustion must eventually
-- contain each fixed character. A union equal to the index set is insufficient.
-- TODO(paper-gap): On p. 196 the directional derivative symbol is zero at
-- the trivial character. Multiplication by it cannot be an automorphism.

end ExponentialSystem

end RiemannMasullo
