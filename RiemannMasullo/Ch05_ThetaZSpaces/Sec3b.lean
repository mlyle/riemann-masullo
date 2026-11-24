module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a

import RiemannMasullo.Ch02_AdelicTheta.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.External.TauCeti.Analysis.Complex.Pompeiu.Basic
import RiemannMasullo.ForMathlib.Analysis.Complex.PeriodicStrip
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace

/-! # Extensions by zero and holomorphic S-idelic zeta functions

Masullo, §5.3.3–5.3.4, pp. 249–265.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions FourierTransform NNReal NumberField.AdeleRing SchwartzMap TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

section PuncturedLine

-- TODO(paper-gap): The logarithmic argument substitution leaves the exponent interval I fixed.

/-- Paper: Example 5.3.3.1, p. 249.
Logarithmic coordinates give a linear homeomorphism between the weighted spaces on
the real line and the positive multiplicative reals.
Deviation: The exponents are unchanged under the logarithmic change of the argument. -/
theorem positiveRealExponentialDecay_log_equiv (I : Set ℝ) (hI : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ)) :=
  identityModulationExponentialDecay_equiv I hI hne

local notation "normPower(" K ", " d ")" =>
  (Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ)

/-- Paper: Proposition 5.3.3.2, p. 249.
Natural powers of the norm on the multiplicative group are continuous as
maps to the positive reals. -/
theorem continuous_archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) :
    Continuous (normPower(K, d)) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun x : Kˣ ↦ (‖(x : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val).pow d
  have h2 : Continuous fun x : Kˣ ↦ (‖((x⁻¹ : Kˣ) : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val |>.comp continuous_inv).pow d
  refine ⟨?_, ?_⟩
  · convert h1 using 2 with x
    simp
  · convert h2 using 2 with x
    simp [map_inv₀]

/-- Paper: Proposition 5.3.3.2, p. 249.
The real multiplicative group uses the norm, and the complex multiplicative group
uses the squared norm. -/
def archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) : Kˣ →ₜ* ℝ≥0ˣ :=
  ⟨normPower(K, d), continuous_archimedeanUnitModulation K d⟩

/-- Paper: Proposition 5.3.3.2, p. 249.
At a nonzero argument the module evaluates to the indicated power of its norm. -/
theorem archimedeanUnitModulation_apply (K : Type*) [NormedField K] (d : ℕ) (u : Kˣ) :
    ((archimedeanUnitModulation K d u).val : ℝ) = ‖(u : K)‖ ^ d := by
  show (((((Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ) u) : ℝ≥0ˣ).val : ℝ≥0) : ℝ) = _
  rw [MonoidHom.pow_apply]
  simp [nnNormHom]

local notation "𝓔(" K ", " d ", " I ")" => ModulatedExponentialDecay (archimedeanUnitModulation K d) I
local notation "punctured(" K ")" => (⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ : Opens K)
local notation "𝒟₀(" K ")" => 𝓓(punctured(K), ℂ)
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))
local notation "complexCoordinate(" conjugate ")" =>
  (fun z : ℂ ↦ if conjugate then star z else z)
local notation "wirtinger(" conjugate ")" =>
  (if conjugate then wirtingerConjDeriv else wirtingerDeriv)

/-- Radial logarithm and angle give a cylinder, whose vector cover is the ordinary
complex exponential with angular period one. -/
private theorem complexSchwartz_restrict_chart :
    ∃ e : ℂˣ ≃ₜ* Multiplicative (ElementaryLieGroup 1 1 0 PUnit.{1}),
      ∀ (t : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) a b,
        (e.symm (Multiplicative.ofAdd (elementaryCover t a b))).val =
          Complex.exp ((t.1 0 : ℂ) + ((2 * Real.pi * t.2 0 : ℝ) : ℂ) * Complex.I) := by
  let X := ElementaryLieGroup 1 1 0 PUnit.{1}
  let A := AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)
  let phase (u : ℂˣ) : Circle := ⟨u.val / (‖u.val‖ : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    simp [u.ne_zero]⟩
  let z (x : X) : ℂ := (Real.exp (x.1 0) : ℂ) * (A (x.2.1 0) : ℂ)
  have hz (x : X) : ‖z x‖ = Real.exp (x.1 0) := by simp [z]
  let Z (x : X) := Units.mk0 (z x) (norm_pos_iff.mp ((Real.exp_pos _).trans_eq (hz x).symm))
  let L (u : ℂˣ) : X := (WithLp.toLp 2 (fun _ ↦ Real.log ‖u.val‖), fun _ ↦ A.symm (phase u), 0, 0)
  have hcont : Continuous phase := by
    apply Continuous.subtype_mk
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      (fun u ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))
  let e : Multiplicative X ≃ₜ* ℂˣ :=
    { toFun := fun x ↦ Z x.toAdd
      invFun := fun u ↦ Multiplicative.ofAdd (L u)
      left_inv := fun x ↦ by
        change L (Z x.toAdd) = x.toAdd
        refine Prod.ext ?_ (Prod.ext ?_ (Subsingleton.elim _ _))
        · ext j
          have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          change Real.log ‖z _‖ = _
          rw [hz, Real.log_exp]
        · funext j
          have hj : j = 0 := Subsingleton.elim _ _
          subst hj
          apply A.injective
          rw [show (L (Z x.toAdd)).2.1 0 = A.symm (phase (Z x.toAdd)) from rfl, A.apply_symm_apply]
          apply Subtype.ext
          change z x.toAdd / (‖z x.toAdd‖ : ℂ) = _
          rw [hz]
          exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
      right_inv := fun u ↦ by
        apply Units.ext
        change (Real.exp (Real.log ‖u.val‖) : ℂ) * (A (A.symm (phase u)) : ℂ) = u.val
        rw [Real.exp_log (norm_pos_iff.mpr u.ne_zero), A.apply_symm_apply]
        exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))
      map_mul' := fun x y ↦ by
        apply Units.ext
        change (Real.exp (x.toAdd.1 0 + y.toAdd.1 0) : ℂ) *
          (A (x.toAdd.2.1 0 + y.toAdd.2.1 0) : ℂ) = z x.toAdd * z y.toAdd
        simp only [z, A, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_add, Circle.coe_mul,
          Real.exp_add, Complex.ofReal_mul]
        ring
      continuous_toFun := by
        apply Units.isEmbedding_val₀.continuous_iff.mpr
        change Continuous z
        exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
          ((PiLp.continuous_apply 2 _ 0).comp continuous_fst))).mul (continuous_subtype_val.comp
          (A.continuous.comp ((continuous_apply 0).comp (continuous_fst.comp continuous_snd))))
      continuous_invFun := by
        change Continuous L
        refine Continuous.prodMk ?_ ((continuous_pi fun _ ↦ A.symm.continuous.comp hcont).prodMk continuous_const)
        exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ ↦
          Units.continuous_val.norm.log (fun u ↦ norm_ne_zero_iff.mpr u.ne_zero)) }
  refine ⟨e.symm, fun t a b ↦ ?_⟩
  change (Real.exp (t.1 0) : ℂ) * (A (t.2 0 : AddCircle (1 : ℝ)) : ℂ) = _
  simp [A, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, Circle.coe_exp,
    Complex.exp_add, Complex.ofReal_exp]

/-- A family on an elementary group with no lattice factor is Schwartz if it is smooth
on the cover, absorbs its directional derivatives, and has bounded polynomial weights. -/
private theorem archimedean_profile_mem {m n : ℕ} {F U : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (P : U → ElementaryLieGroup m n 0 F → ℂ)
    (hs : ∀ u a b, ContDiff ℝ (∞) (fun t ↦ P u (elementaryCover t a b)))
    (hd : ∀ u v, ∃ u', ∀ t a b, fderiv ℝ (fun t ↦ P u (elementaryCover t a b)) t v =
      P u' (elementaryCover t a b))
    (hb : ∀ u (α : Fin m → ℕ), ∃ C : ℝ≥0, ∀ t a b,
      ‖(∏ k, (t.1 k : ℂ) ^ α k) * P u (elementaryCover t a b)‖ ≤ C)
    (u : U) : P u ∈ elementarySchwartzSubmodule m n 0 F := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  have jets (l : List X) : ∃ u', ∀ t a b,
      iteratedFDeriv ℝ l.length (fun t ↦ P u (elementaryCover t a b)) t l.get =
        P u' (elementaryCover t a b) := by
    induction l with
    | nil => exact ⟨u, by simp⟩
    | cons v l ih =>
      obtain ⟨u', hu'⟩ := ih
      obtain ⟨u'', hu''⟩ := hd u' v
      refine ⟨u'', fun t a b ↦ ?_⟩
      refine (((hs u a b).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top l.length)
        t).iteratedFDeriv_succ_apply_left' (m := (v :: l).get)).trans ?_
      exact (congrArg (fun g : X → ℂ ↦ fderiv ℝ g t v) (funext fun t ↦ hu' t a b)).trans (hu'' t a b)
  refine ⟨hs u, fun ⟨α, β, γ, δ⟩ ↦ ?_⟩
  let l : List X := (List.ofFn (fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))).flatten ++
    (List.ofFn (fun j : Fin n ↦ List.replicate (γ j) (0, EuclideanSpace.single j 1))).flatten
  obtain ⟨u', hu'⟩ := jets l
  obtain ⟨C, hC⟩ := hb u' α
  refine lt_of_le_of_lt (b := (C : ENNReal)) (iSup_le fun t ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.coe_lt_top
  apply ENNReal.coe_le_coe.mpr
  change ‖((∏ k, (t.1 k : ℂ) ^ α k) * ∏ k, (a k : ℂ) ^ δ k) *
    iteratedFDeriv ℝ l.length (fun t ↦ P u (elementaryCover t a b)) t l.get‖ ≤ (C : ℝ)
  simpa only [Finset.univ_eq_empty (α := Fin 0), Finset.prod_empty, mul_one, hu'] using
    (show ‖(∏ k, (t.1 k : ℂ) ^ α k) * P u' (elementaryCover t a b)‖ ≤ C from hC t a b)

/-- A positive exponential absorbs powers of the logarithm at the puncture. On the
other end of the cylinder an ordinary Schwartz seminorm absorbs both weights. -/
private theorem complexSchwartz_restrict_radial_bound (b : ℝ) (hb : 0 < b) (k : ℕ)
    (f : 𝓢(ℂ, ℂ)) : ∃ C : ℝ≥0, ∀ t : ℝ, ∀ z : ℂ, ‖z‖ = Real.exp t →
      |t| ^ k * Real.exp (b * t) * ‖f z‖ ≤ C := by
  let A := (k.factorial : ℝ) / b ^ k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ k ≤ A * Real.exp (b * x) := by
    have h := (div_le_iff₀ (show 0 < (k.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb.le hx) k)
    dsimp [A]
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hb k)]
    simpa only [mul_pow, mul_comm] using h
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * b)
  let B := SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ N 0 f
  have hB : 0 ≤ B := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  refine ⟨⟨A * B, mul_nonneg hA hB⟩, fun t z hz ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_right (hpow |t| (abs_nonneg _)) (Real.exp_pos (b*t)).le
  rw [mul_assoc, ← Real.exp_add] at h
  refine (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hA
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    have he : Real.exp (b*t+b*t) ≤ Real.exp t ^ N := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hN ht]
    rw [← hz] at he
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans
      ((SchwartzMap.norm_pow_mul_le_seminorm ℝ f N z).trans (le_add_of_nonneg_left (apply_nonneg _ _)))
  · rw [abs_of_nonpos (le_of_not_ge ht), mul_neg, neg_add_cancel, Real.exp_zero, one_mul]
    exact (SchwartzMap.norm_le_seminorm ℝ f z).trans (le_add_of_nonneg_right (apply_nonneg _ _))

/-- On the cylinder the weighted Euler derivatives of a restricted test are again
weighted restrictions. Each derivative is a linear vector field on the additive plane. -/
private theorem complexSchwartz_restrict_weighted (b : ℝ) (hb : 0 < b) :
    ∃ T : 𝓢(ℂ, ℂ) →L[ℂ] SchwartzBruhat ℂˣ, ∀ f (u : ℂˣ),
      T f u = (Real.exp (b * Real.log ‖u.val‖) : ℂ) * f u.val := by
  obtain ⟨e, he⟩ := complexSchwartz_restrict_chart
  let d : ElementaryLCAPresentation ℂˣ := ⟨1, 1, 0, PUnit.{1}, e⟩
  obtain ⟨J, hJ⟩ := elementarySchwartz_equiv_schwartzBruhat d
  let V := EuclideanSpace ℝ (Fin 1)
  let X := V × V
  let r : X →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.fst ℝ V V)
  let s : X →L[ℝ] ℝ := (2 * Real.pi) • (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ V V)
  let L : X →L[ℝ] ℂ := Complex.ofRealCLM.comp r + Complex.I • Complex.ofRealCLM.comp s
  let B : X →L[ℝ] ℂ := Complex.ofRealCLM.comp (b • r)
  let profile (f : 𝓢(ℂ, ℂ)) (t : X) := Complex.exp (B t) * f (Complex.exp (L t))
  let P (f : 𝓢(ℂ, ℂ)) (y : ElementaryLieGroup 1 1 0 PUnit.{1}) :=
    let u := e.symm (Multiplicative.ofAdd y)
    (Real.exp (b * Real.log ‖u.val‖) : ℂ) * f u.val
  have hL (t : X) : L t = (t.1 0 : ℂ) + ((2 * Real.pi * t.2 0 : ℝ) : ℂ) * Complex.I := by
    change _ + Complex.I * _ = _
    rw [mul_comm Complex.I]
    rfl
  have hre (t : X) : (L t).re = t.1 0 := by rw [hL]; simp
  have hp (f : 𝓢(ℂ, ℂ)) (a b') : (fun t ↦ P f (elementaryCover t a b')) = profile f := by
    funext t
    dsimp only [P, profile]
    rw [he, ← hL, Complex.norm_exp, hre, Real.log_exp]
    exact congrArg (· * _) (Complex.ofReal_exp _)
  have hmem (f : 𝓢(ℂ, ℂ)) : P f ∈ elementarySchwartzSubmodule 1 1 0 PUnit.{1} := by
    apply archimedean_profile_mem P _ _ _ f
    · intro f a b'
      rw [hp]
      exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp B.contDiff).mul
        (f.smooth'.comp ((Complex.contDiff_exp (𝕜 := ℝ)).comp L.contDiff))
    · intro f v
      let l : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) (L v)
      let T : 𝓢(ℂ, ℂ) := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ))
        l.hasTemperateGrowth (SchwartzMap.fderivCLM ℝ ℂ ℂ f)
      refine ⟨T + B v • f, fun t a b' ↦ ?_⟩
      rw [hp, congrFun (hp _ a b') t]
      have dExp (K : X →L[ℝ] ℂ) := (((Complex.hasDerivAt_exp (K t)).hasFDerivAt.restrictScalars ℝ).comp t
        K.hasFDerivAt)
      have h := ((dExp B).mul (f.differentiableAt.hasFDerivAt.comp t (dExp L))).fderiv
      change fderiv ℝ (fun t ↦ Complex.exp (B t) * f (Complex.exp (L t))) t v = _
      refine (congrArg (fun A : X →L[ℝ] ℂ ↦ A v) h).trans ?_
      change _ = Complex.exp (B t) * (fderiv ℝ (f : ℂ → ℂ) (Complex.exp (L t)) (L v * Complex.exp (L t)) +
        B v * f (Complex.exp (L t)))
      simp [smul_eq_mul]
      ring
    · intro f α
      obtain ⟨C, hC⟩ := complexSchwartz_restrict_radial_bound b hb (α 0) f
      refine ⟨C, fun t a b' ↦ ?_⟩
      rw [congrFun (hp f a b') t]
      simpa [profile, Fintype.prod_unique, norm_mul, Complex.norm_exp, B, r, show (ContinuousLinearMap.fst ℝ V V) t = t.1 by rfl, ← mul_assoc] using
        hC (t.1 0) (Complex.exp (L t)) (by rw [Complex.norm_exp, hre])
  let A : 𝓢(ℂ, ℂ) →ₗ[ℂ] ElementarySchwartz 1 1 0 PUnit.{1} :=
    { toFun := fun f ↦ ⟨P f, hmem f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ mul_left_comm _ _ _) }
  have : CompleteSpace 𝓢(ℂ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℂ, ℂ)).IsCountablyGenerated := by rw [uniformity_eq_comap_nhds_zero]; infer_instance
  have : BaireSpace 𝓢(ℂ, ℂ) := BaireSpace.of_completelyPseudoMetrizable
  have hc : Continuous A := by
    apply continuous_toElementarySchwartz_of_eval
    intro y
    let u := e.symm (Multiplicative.ofAdd y)
    exact ⟨(Real.exp (b * Real.log ‖u.val‖) : ℂ) • TemperedDistribution.delta u.val, fun _ ↦ rfl⟩
  refine ⟨J.toContinuousLinearMap.comp ⟨A, hc⟩, fun f u ↦ ?_⟩
  change J (A f) u = _
  rw [hJ]
  change P f (e u).toAdd = _
  exact congrArg (fun u : ℂˣ ↦ (Real.exp (b * Real.log ‖u.val‖) : ℂ) * f u.val) (e.symm_apply_apply u)

/-- Paper: §5.3.3, p. 249.
Restriction of an additive complex Schwartz function to the units gives a continuous
linear injection into the space with all positive squared-norm weights. -/
theorem complexSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℂ, ℂ) →L[ℂ] 𝓔(ℂ, 2, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℂ, ℂ)) (u : ℂˣ), (R f).val u = f u.val := by
  let G := ℂˣ
  let X := 𝓢(ℂ, ℂ)
  let m := archimedeanUnitModulation ℂ 2
  let I : Set ℝ := Ioi 0
  have hk : IsBruhatGoodSubgroup (⊥ : Subgroup G) := by
    let d := (stdOrthonormalBasis ℝ ℂ).repr
    exact isBruhatGoodSubgroup_bot_iff.mpr ⟨_, ⟨(d.toHomeomorph.isOpenEmbedding.comp
      (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩
  let k : {k : Subgroup G // IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)} :=
    ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, hk.2.2⟩
  let e : G ⧸ k.val ≃ₜ* G := QuotientGroup.quotientBot.toContinuousMulEquiv fun _ ↦
    (QuotientGroup.isQuotientMap_mk k.val).isOpen_preimage.symm
  let P := schwartzBruhatPullbackEquiv e
  let N : X →ₗ[ℂ] ((G ⧸ k.val) → ℂ) :=
    { toFun := fun f q ↦ f (e q).val, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let m' := quotientModulation m k.val k.property.1
  have htw (a : I) : ∃ T : X →L[ℂ] SchwartzBruhat (G ⧸ k.val), ∀ f,
      (T f).val = modulationWeight m' a (N f) := by
    obtain ⟨T, hT⟩ := complexSchwartz_restrict_weighted (2 * a.val) (by have := a.property; exact mul_pos (by norm_num) this)
    refine ⟨P.toContinuousLinearMap.comp T, fun f ↦ funext fun q ↦ ?_⟩
    induction q using QuotientGroup.induction_on with
    | _ u =>
      change T f u = ((((m' (QuotientGroup.mk u)).val : ℝ) ^ a.val : ℝ) : ℂ) * f u.val
      rw [hT, quotientModulation_apply, archimedeanUnitModulation_apply]
      rw [Real.rpow_def_of_pos (pow_pos (norm_pos_iff.mpr u.ne_zero) 2), Real.log_pow]
      congr 3
      ring
  let R : X →ₗ[ℂ] ModulatedExponentialDecayStage m I k :=
    N.codRestrict (modulatedExponentialDecaySubmodule m' I) fun f ↦
      (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr (by
        rw [← (htw a).choose_spec f]; exact ((htw a).choose f).property)
  have hc : Continuous R := (modulatedExponentialDecayStage_twists_isInducing m I k).continuous_iff.mpr
    (continuous_pi fun a ↦ (htw a).choose.continuous.congr fun f ↦ Subtype.ext ((htw a).choose_spec f))
  let J : ModulatedExponentialDecayStage m I k →ₗ[ℂ] ModulatedExponentialDecay m I :=
    modulatedExponentialDecayStageInclusion m I k
  have hJ : Continuous J := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp J
    fun p ↦ p.property k
  refine ⟨⟨J.comp R, hJ.comp hc⟩, fun f g h ↦ ?_, fun _ _ ↦ rfl⟩
  apply DFunLike.coe_injective
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) f.continuous g.continuous
  intro z hz
  exact congrArg (fun a : ModulatedExponentialDecay m I ↦ a.val (Units.mk0 z hz)) h

open scoped Manifold in
private theorem puncturedTest_mul_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (a : E → ℂ) (ha : ContDiff ℝ (∞) a)
    (ha₀ : ∀ x ≠ 0, a x ≠ 0) :
    ∃ M : 𝒟₀(E) ≃L[ℂ] 𝒟₀(E), ∀ f x, M f x = a x * f x := by
  let Ω := punctured(E)
  have mulSmooth (b : E → ℂ) (hb : ContDiffOn ℝ (∞) b Ω) (f : E → ℂ)
      (hf : ContDiff ℝ (∞) f) (hs : ∀ x ∉ Ω, ∀ᶠ y in 𝓝 x, f y = 0) :
      ContDiff ℝ (∞) (fun x ↦ b x * f x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · exact ((hb x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).mul hf.contDiffAt
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hs x hx] with y hy
      simp [hy]
  have mulCLM (b : E → ℂ) (hb : ContDiffOn ℝ (∞) b Ω) :
      ∃ T : 𝓓(Ω, ℂ) →L[ℂ] 𝓓(Ω, ℂ), ∀ f x, T f x = b x * f x := by
    have zeroLocally (f : 𝓓(Ω, ℂ)) (x : E) (hx : x ∉ Ω) : ∀ᶠ y in 𝓝 x, f y = 0 := by
      have hxf : x ∉ tsupport f := fun h ↦ hx (f.tsupport_subset h)
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxf] with y hy
      exact notMem_support.mp fun h ↦ hy (subset_closure h)
    let F (f : 𝓓(Ω, ℂ)) : 𝓓(Ω, ℂ) :=
      ⟨fun x ↦ b x * f x, mulSmooth b hb f f.contDiff (zeroLocally f),
        f.hasCompactSupport.mono (support_mul_subset_right b f),
        tsupport_mul_subset_right.trans f.tsupport_subset⟩
    refine ⟨TestFunction.mkCLM ℂ F ?_ ?_ ?_, fun _ _ ↦ rfl⟩
    · intro f g
      ext x
      exact mul_add _ _ _
    · intro c f
      ext x
      exact mul_left_comm _ _ _
    · intro K hK
      -- On each fixed support stage, replace the multiplier by a globally smooth one.
      obtain ⟨χ, hχ₀, hχ₁, _⟩ :=
        exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E)) Ω.isOpen.isClosed_compl
          K.isCompact.isClosed (disjoint_left.mpr (fun _ hx hy ↦ hx (hK hy))) (n := (⊤ : ℕ∞))
      have hχ : ContDiff ℝ (∞) (fun x ↦ (χ x : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp χ.contMDiff)
      have h : ContDiff ℝ (∞) (fun x ↦ b x * (χ x : ℂ)) :=
        mulSmooth b hb _ hχ fun x hx ↦ by
          filter_upwards [hχ₀.filter_mono (nhds_le_nhdsSet hx)] with y hy
          simp [hy]
      let L := ContDiffMapSupportedIn.bilinLeftCLM (K := K) (ContinuousLinearMap.mul ℂ ℂ) h
      refine ((TestFunction.continuous_ofSupportedIn hK).comp L.continuous).congr ?_
      intro f
      ext x
      change (f x) * (b x * (χ x : ℂ)) = b x * f x
      by_cases hx : x ∈ K
      · have he := hχ₁.self_of_nhdsSet x hx
        simp [he, mul_comm]
      · have hf := notMem_support.mp (fun hh ↦ hx (f.tsupport_subset (subset_closure hh)))
        simp [hf]
  obtain ⟨M, hM⟩ := mulCLM a ha.contDiffOn
  obtain ⟨N, hN⟩ := mulCLM (fun x ↦ (a x)⁻¹) (ha.contDiffOn.inv ha₀)
  have hcomp (f : 𝓓(Ω, ℂ)) (x : E) :
      N (M f) x = f x ∧ M (N f) x = f x := by
    rw [hN, hM, hM, hN]
    by_cases hx : x = 0
    · have hf : f x = 0 :=
        notMem_support.mp (fun h ↦ (f.tsupport_subset (subset_closure h)) (by simp [hx]))
      simp [hf]
    · simp [ha₀ x hx]
  let e : 𝓓(Ω, ℂ) ≃ₗ[ℂ] 𝓓(Ω, ℂ) :=
    { M.toLinearMap with
      invFun := N
      left_inv := fun f ↦ TestFunction.ext (fun x ↦ (hcomp f x).1)
      right_inv := fun f ↦ TestFunction.ext (fun x ↦ (hcomp f x).2) }
  exact ⟨⟨e, M.continuous, N.continuous⟩, hM⟩

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is a linear homeomorphism on compactly supported
smooth tests on the punctured real line. -/
theorem realCoordinate_mul_puncturedTest :
    ∃ M : 𝒟₀(ℝ) ≃L[ℂ] 𝒟₀(ℝ), ∀ f x, M f x = (x : ℂ) * f x := by
  exact puncturedTest_mul_equiv (fun x : ℝ ↦ (x : ℂ)) Complex.ofRealCLM.contDiff
    (fun x hx ↦ by exact_mod_cast hx)

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by either complex coordinate, z or its conjugate, is a linear homeomorphism
on compactly supported smooth tests on the punctured complex plane. -/
theorem complexCoordinate_mul_puncturedTest (conjugate : Bool) :
    ∃ M : 𝒟₀(ℂ) ≃L[ℂ] 𝒟₀(ℂ), ∀ f z, M f z = complexCoordinate(conjugate) z * f z := by
  cases conjugate
  · exact puncturedTest_mul_equiv (id : ℂ → ℂ) contDiff_id (fun _ hx ↦ hx)
  · exact puncturedTest_mul_equiv (star : ℂ → ℂ) Complex.conjCLE.contDiff (fun z hz ↦ by simpa using hz)

private theorem realCoordinate_mul_exponentialDecay_good : IsBruhatGoodSubgroup (⊥ : Subgroup ℝˣ) := by
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  exact isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨(e.symm.toHomeomorph.isOpenEmbedding.comp
    (Units.isOpenEmbedding_val (R := ℝ))).singletonChartedSpace⟩⟩

/-- The positive units give a Bruhat stage. They lie in every open stage subgroup,
while their intersection with each compact stage kernel is trivial. -/
private theorem realCoordinate_mul_exponentialDecay_posStage :
    ∃ a : BruhatStructuralPair ℝˣ, a.val.1 = Units.posSubgroup ℝ ∧
      OrderDual.ofDual a.val.2 = ⊥ ∧ ∀ b : BruhatStructuralPair ℝˣ,
        a.val.1 ≤ b.val.1 ∧ ∀ x ∈ a.val.1, x ∈ OrderDual.ofDual b.val.2 → x = 1 := by
  let P := Units.posSubgroup ℝ
  have hP : IsOpen (P : Set ℝˣ) := isOpen_Ioi.preimage Units.continuous_val
  have hPc : PreconnectedSpace P := by
    apply isPreconnected_iff_preconnectedSpace.mp
    apply Units.isOpenEmbedding_val.isInducing.isPreconnected_image.mp
    have he : Units.val '' (P : Set ℝˣ) = Ioi (0 : ℝ) := by
      ext x
      exact ⟨fun ⟨u, hu, he⟩ ↦ he ▸ hu, fun hx ↦ ⟨Units.mk0 x (ne_of_gt hx), hx, rfl⟩⟩
    rw [he]
    exact isPreconnected_Ioi
  let : LocallyCompactSpace P := hP.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup P := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : P)
    have ho : IsOpen (Subgroup.closure U : Set P) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, ho⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  refine ⟨⟨(P, OrderDual.toDual ⊥), hP, hgen, realCoordinate_mul_exponentialDecay_good, bot_le⟩,
    rfl, rfl, fun b ↦ ⟨?_, ?_⟩⟩
  · have h := (OpenSubgroup.isClopen ⟨b.val.1, b.property.1⟩).preimage
      (continuous_subtype_val (p := fun x ↦ x ∈ P))
    have hu := h.eq_univ ⟨1, b.val.1.one_mem⟩
    intro x hx
    exact (Set.eq_univ_iff_forall.mp hu) (⟨x, hx⟩ : P)
  · intro x hx hk
    let m := archimedeanUnitModulation ℝ 1
    have hm : m x = 1 := compactSubgroup_le_modulation_ker m _
      (isCompact_of_isBruhatGoodSubgroup_aux _ b.property.2.2.1) hk
    have he := archimedeanUnitModulation_apply ℝ 1 x
    change ((m x).val : ℝ) = _ at he
    rw [hm, pow_one, Real.norm_eq_abs, abs_of_pos (show 0 < x.val from hx)] at he
    exact Units.ext he.symm

/-- Restrict an arbitrary stage to the positive component and realize the result
in the positive stage, extending by zero on the other component. -/
private theorem realCoordinate_mul_exponentialDecay_restrictStage
    (a b : BruhatStructuralPair ℝˣ) (ha : OrderDual.ofDual a.val.2 = ⊥)
    (hab : a.val.1 ≤ b.val.1)
    (hk : ∀ x ∈ a.val.1, x ∈ OrderDual.ofDual b.val.2 → x = 1)
    (e : ElementaryLCAPresentation a.quotient) (d : ElementaryLCAPresentation b.quotient) :
    ∃ R : SchwartzBruhatStage d →L[ℂ] SchwartzBruhatStage e,
      ∀ f x, schwartzBruhatStageRealization a e (R f) x =
        (a.val.1 : Set ℝˣ).indicator (schwartzBruhatStageRealization b d f) x := by
  classical
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let _ := d.finiteGroup
  let _ := d.finiteTopology
  let _ := d.finiteDiscrete
  let _ := d.finiteFintype
  let inc := Subgroup.inclusion hab
  let p := MonoidHom.toAdditive ((d.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)).comp inc)
  let q := MonoidHom.toAdditive (e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _))
  have hqker (x : a.val.1) (hx : (QuotientGroup.mk x : a.quotient) = 1) : x = 1 := by
    apply Subtype.ext
    change x.val = 1
    simpa only [ha, Subgroup.mem_bot] using (a.quotient_mk_eq_one x).mp hx
  have hqi : Injective q := by
    apply (AddMonoidHom.ker_eq_bot_iff _).mp
    refine le_antisymm (fun x hx ↦ ?_) bot_le
    change Additive.toMul x = 1
    apply hqker
    exact e.equiv.injective ((show e.equiv _ = 1 from hx).trans (map_one _).symm)
  have hqs : Surjective q := fun y ↦ (e.equiv.surjective (Multiplicative.ofAdd y)).elim
    fun t ht ↦ (QuotientGroup.mk_surjective t).elim fun x hx ↦ ⟨Additive.ofMul x, (congrArg e.equiv hx).trans ht⟩
  let v := Equiv.ofBijective q ⟨hqi, hqs⟩
  have hker : p.ker ≤ q.ker := by
    intro x hx
    have he := d.equiv.injective ((show d.equiv (QuotientGroup.mk (inc (Additive.toMul x))) = 1 from hx).trans
      (map_one _).symm)
    have h1 := hk _ (Additive.toMul x).property ((b.quotient_mk_eq_one _).mp he)
    have hx0 : x = 0 := congrArg Additive.ofMul (Subtype.ext h1)
    rw [hx0]
    exact q.ker.zero_mem
  let T : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhatStage e :=
    { toFun := fun f ↦ ⟨fun y ↦ f (p (v.symm y)), by
        apply elementarySchwartz_of_common_pullback p _ _ q _ _ hqs hker f
        · intro x
          exact congrArg (fun z ↦ f (p z)) (v.symm_apply_apply x).symm
        · exact d.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
            (show Continuous inc from continuous_subtype_val.subtype_mk _))
        · exact d.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe.comp
            (a.property.1.isOpenMap_inclusion hab))
        · exact e.equiv.continuous.comp (QuotientGroup.continuous_mk
            (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
        · exact e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
            (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let X := SchwartzBruhatStage d
  let : BarrelledSpace ℂ X := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  let : ContinuousSMul ℂ X := elementarySchwartz_withSeminorms.continuousSMul
  have hT : Continuous T := by
    apply continuous_toElementarySchwartz_of_eval T
    intro y
    exact elementarySchwartz_eval_continuousLinear (p (v.symm y))
  refine ⟨⟨T, hT⟩, fun f x ↦ ?_⟩
  by_cases hx : x ∈ a.val.1
  · exact ((schwartzBruhatStageRealization_apply a e (T f) x).trans (dite_eq_left hx)).trans <|
      (congrArg (fun z ↦ f (p z)) (v.symm_apply_apply (Additive.ofMul (⟨x, hx⟩ : a.val.1)))).trans <|
      (((schwartzBruhatStageRealization_apply b d f x).trans (dite_eq_left (hab hx))).symm.trans
        (Set.indicator_of_mem hx _).symm)
  · exact ((schwartzBruhatStageRealization_apply a e (T f) x).trans (dite_eq_right hx)).trans
      (Set.indicator_of_notMem hx _).symm

/-- Twice the projection onto the positive component minus the identity multiplies
Schwartz–Bruhat functions by the sign. -/
private theorem realCoordinate_mul_exponentialDecay_sign :
    ∃ S : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f (x : ℝˣ), S f x = (if 0 < x.val then (1 : ℂ) else -1) * f x := by
  classical
  let a := realCoordinate_mul_exponentialDecay_posStage.choose
  have has := realCoordinate_mul_exponentialDecay_posStage.choose_spec
  have ha : a.val.1 = Units.posSubgroup ℝ := has.1
  let e := a.elementary.some
  let H := (a.val.1 : Set ℝˣ)
  let L : (ℝˣ → ℂ) →ₗ[ℂ] (ℝˣ → ℂ) :=
    { toFun := H.indicator
      map_add' := H.indicator_add'
      map_smul' := fun c f ↦ H.indicator_smul (fun _ ↦ c) f }
  have hstage (b : BruhatStructuralPair ℝˣ) (d : ElementaryLCAPresentation b.quotient) :=
    realCoordinate_mul_exponentialDecay_restrictStage a b has.2.1 (has.2.2 b).1 (has.2.2 b).2 e d
  have hmem : schwartzBruhatSubmodule ℝˣ ≤ (schwartzBruhatSubmodule ℝˣ).comap L := by
    refine iSup_le fun b ↦ iSup_le fun d ↦ ?_
    rintro _ ⟨f, rfl⟩
    let R := (hstage b d).choose
    have hr := funext ((hstage b d).choose_spec f)
    change H.indicator _ ∈ schwartzBruhatSubmodule ℝˣ
    exact hr ▸ (schwartzBruhatStageInclusion a e (R f)).property
  let P : SchwartzBruhat ℝˣ →ₗ[ℂ] SchwartzBruhat ℝˣ :=
    (L.comp (schwartzBruhatSubmodule ℝˣ).subtype).codRestrict _ (fun f ↦ hmem f.property)
  have hc : Continuous P := by
    have gen := withGeneratingSeminorms_spec (schwartzBruhatSubmodule ℝˣ)
      (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule ℝˣ) //
        ∀ b d, Continuous (p ∘ schwartzBruhatStageInclusion b d)} → _)
    refine gen.continuous_of_continuous_comp P fun p ↦ gen.continuous_seminorm ⟨p.val.comp P, ?_⟩
    intro b d
    let R := (hstage b d).choose
    exact ((p.property a e).comp R.continuous).congr fun f ↦
      congrArg p.val (Subtype.ext (funext ((hstage b d).choose_spec f)))
  let A : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ := ⟨P, hc⟩
  refine ⟨A + A - ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
  change H.indicator f.val x + H.indicator f.val x - f.val x = _
  have hx : x ∈ H ↔ 0 < x.val := by
    change x ∈ a.val.1 ↔ _
    rw [ha, Units.mem_posSubgroup]
  by_cases h : 0 < x.val
  · rw [Set.indicator_of_mem (hx.mpr h), ite_eq_left h, one_mul, add_sub_cancel_right]
  · rw [Set.indicator_of_notMem (mt hx.mp h), ite_eq_right h, zero_add, zero_sub, neg_one_mul]

private theorem realCoordinate_mul_exponentialDecay_weight (b : ℝ) (x : ℝˣ) :
    (if 0 < x.val then (1 : ℂ) else -1) * (↑(‖x.val‖ ^ (b + 1)) : ℂ) =
      (↑(‖x.val‖ ^ b) : ℂ) * (x.val : ℂ) := by
  rw [Real.rpow_add (norm_pos_iff.mpr x.ne_zero), Real.rpow_one, Complex.ofReal_mul]
  by_cases hx : 0 < x.val
  · rw [ite_eq_left hx, one_mul, Real.norm_eq_abs, abs_of_pos hx]
  · rw [ite_eq_right hx, Real.norm_eq_abs, abs_of_nonpos (le_of_not_gt hx), Complex.ofReal_neg]
    ring

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuous for decay on a closed upper half-line. -/
theorem realCoordinate_mul_exponentialDecay (a : ℝ) :
    ∃ M : 𝓔(ℝ, 1, Ici a) →L[ℂ] 𝓔(ℝ, 1, Ici a),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by
  let m := archimedeanUnitModulation ℝ 1
  let I := Ici a
  let E := ModulatedExponentialDecay m I
  -- Use the stage for the trivial compact subgroup, so the output loses no sign information.
  let k : {k : Subgroup ℝˣ // IsCompact (k : Set ℝˣ) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)} :=
    ⟨⊥, by simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : ℝˣ)),
      realCoordinate_mul_exponentialDecay_good.2.2⟩
  let v : (ℝˣ ⧸ k.val) ≃ₜ* ℝˣ :=
    { QuotientGroup.quotientBot with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_id
      continuous_invFun := QuotientGroup.continuous_mk }
  let n := quotientModulation m k.val k.property.1
  have pull := exists_schwartzBruhat_pullback (A := ℝˣ ⧸ k.val) (B := ℝˣ) v
  let S := realCoordinate_mul_exponentialDecay_sign.choose
  let coord (x : ℝˣ ⧸ k.val) : ℂ := (v x).val
  let L : E →ₗ[ℂ] ((ℝˣ ⧸ k.val) → ℂ) := (LinearMap.mulLeft ℂ coord).comp
    ((LinearMap.funLeft ℂ ℂ v).comp (modulatedExponentialDecaySubmodule m I).subtype)
  let next (b : I) : I := ⟨b + 1, le_trans b.property (le_add_of_nonneg_right zero_le_one)⟩
  let W (b : I) : E →L[ℂ] SchwartzBruhat (ℝˣ ⧸ k.val) := pull.choose.comp <| S.comp
    ⟨modulatedExponentialDecayTwist m I (next b), continuous_decay_twist m I (next b)⟩
  -- The b-twist of x f is the sign times the (b+1)-twist of f.
  have hw (b : I) (f : E) : (W b f).val = modulationWeight n b (L f) := by
    funext y
    refine QuotientGroup.induction_on y fun x ↦ ?_
    refine (pull.choose_spec (S (modulatedExponentialDecayTwist m I (next b) f)) _).trans ?_
    refine (realCoordinate_mul_exponentialDecay_sign.choose_spec
      (modulatedExponentialDecayTwist m I (next b) f) x).trans ?_
    change (if 0 < x.val then (1 : ℂ) else -1) *
      (((((m x).val : ℝ) ^ ((b : ℝ) + 1) : ℝ) : ℂ) * f.val x) =
      ((((m x).val : ℝ) ^ (b : ℝ) : ℝ) : ℂ) * ((x.val : ℂ) * f.val x)
    rw [show ((m x).val : ℝ) = ‖x.val‖ by simpa only [pow_one] using archimedeanUnitModulation_apply ℝ 1 x,
      ← mul_assoc, realCoordinate_mul_exponentialDecay_weight, mul_assoc]
  let T : E →ₗ[ℂ] ModulatedExponentialDecayStage m I k := L.codRestrict _ (fun f ↦
    (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr ((hw b f) ▸ (W b f).property))
  have hT : Continuous T := by
    apply (modulatedExponentialDecayStage_twists_isInducing m I k).continuous_iff.mpr
    exact continuous_pi fun b ↦ (W b).continuous.congr fun f ↦ Subtype.ext (hw b f)
  let j : ModulatedExponentialDecayStage m I k →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp j (fun p ↦ p.property k)
  exact ⟨(⟨j, hj⟩ : _ →L[ℂ] E).comp ⟨T, hT⟩, fun _ _ ↦ rfl⟩

/-- The real absolute value on the units is a surjective modulation. -/
private theorem realCoordinate_mul_allExponentialDecay_modulation
    [SecondCountableTopology ℝˣ] :
    IsModulation (archimedeanUnitModulation ℝ 1) ∧ Surjective (archimedeanUnitModulation ℝ 1) := by
  refine ⟨⟨isProperMap_units_nnNorm_pow (K := ℝ) 1 one_ne_zero, ⟨Units.mk0 2 two_ne_zero, ?_⟩⟩, ?_⟩
  · intro h
    have h2 := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [archimedeanUnitModulation_apply, Units.val_mk0, pow_one, Units.val_one,
      NNReal.coe_one] at h2
    norm_num at h2
  · intro t
    have ht : ((t.val : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr t.ne_zero
    refine ⟨Units.mk0 _ ht, Units.ext (NNReal.eq ?_)⟩
    rw [archimedeanUnitModulation_apply, Units.val_mk0, pow_one, Real.norm_eq_abs,
      abs_of_nonneg (NNReal.coe_nonneg _)]

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuously invertible for decay at all exponents. -/
theorem realCoordinate_mul_allExponentialDecay :
    ∃ M : 𝓔(ℝ, 1, univ) ≃L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by
  letI : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm := realCoordinate_mul_allExponentialDecay_modulation.1
  have hms := realCoordinate_mul_allExponentialDecay_modulation.2
  let c : QuasiCharacter ℝˣ :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (Units.coeHom ℝ),
      Complex.continuous_ofReal.comp Units.continuous_val⟩
  exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms c

/-- The squared complex absolute value on the units is a surjective modulation. -/
private theorem complexCoordinate_mul_allExponentialDecay_modulation
    [SecondCountableTopology ℂˣ] :
    IsModulation (archimedeanUnitModulation ℂ 2) ∧ Surjective (archimedeanUnitModulation ℂ 2) := by
  refine ⟨⟨isProperMap_units_nnNorm_pow (K := ℂ) 2 two_ne_zero, ⟨Units.mk0 2 two_ne_zero, ?_⟩⟩, ?_⟩
  · intro h
    have h2 := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [archimedeanUnitModulation_apply, Units.val_mk0, Units.val_one,
      NNReal.coe_one, Complex.norm_ofNat] at h2
    norm_num at h2
  · intro t
    have ht : ((Real.sqrt ((t.val : ℝ≥0) : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (NNReal.coe_pos.mpr (Units.zero_lt t)))
    refine ⟨Units.mk0 _ ht, Units.ext (NNReal.eq ?_)⟩
    rw [archimedeanUnitModulation_apply, Units.val_mk0, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt (NNReal.coe_nonneg _)]

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuous for decay on a closed upper half-line. -/
theorem complexCoordinate_mul_exponentialDecay (conjugate : Bool) (a : ℝ) :
    ∃ M : 𝓔(ℂ, 2, Ici a) →L[ℂ] 𝓔(ℂ, 2, Ici a),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by
  let _ : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let m := archimedeanUnitModulation ℂ 2
  obtain ⟨hm, hms⟩ := complexCoordinate_mul_allExponentialDecay_modulation
  let d : QuasiCharacter ℂˣ := if conjugate then
    ⟨(starRingEnd ℂ).toMonoidHom.comp (Units.coeHom ℂ), Complex.continuous_conj.comp Units.continuous_val⟩
    else ⟨Units.coeHom ℂ, Units.continuous_val⟩
  have hd (g : ℂˣ) : d g = complexCoordinate(conjugate) g.val := by cases conjugate <;> rfl
  have hnorm (g : ℂˣ) : ‖d g‖ = ‖g.val‖ := by rw [hd]; cases conjugate <;> simp
  have hn (g : ℂˣ) : d g ≠ 0 := ((Group.isUnit g).map d).ne_zero
  let unit (g : ℂˣ) := d g / (‖d g‖ : ℂ)
  let η : PontryaginDual ℂˣ :=
    { toFun := fun g ↦ ⟨unit g, mem_sphere_zero_iff_norm.mpr (by
        simp only [unit, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (norm_ne_zero_iff.mpr (hn g))])⟩
      map_one' := Circle.ext (by simp [unit])
      map_mul' := fun g k ↦ Circle.ext (by
        change unit (g * k) = unit g * unit k
        simp only [unit, map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm])
      continuous_toFun := (d.continuous.div (Complex.continuous_ofReal.comp d.continuous.norm)
        (fun g ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn g)))).subtype_mk _ }
  obtain ⟨U, hU⟩ := modulatedExponentialDecay_mul_unitaryCharacter m (Ici a) hm hms
    ordConnected_Ici nonempty_Ici η
  have hshift (b : ℝ) (hb : b ∈ Ici a) : b + 1 / 2 ∈ Ici a :=
    hb.trans (le_add_of_nonneg_right (by norm_num))
  obtain ⟨W, hW⟩ := modulatedExponentialDecay_exists_weightMap m (Ici a) (Ici a) (1 / 2) hshift
  refine ⟨U.comp W, fun f g ↦ ?_⟩
  change (U (W f)).val g = _
  rw [hU, hW]
  have hw : ((m g).val : ℝ) ^ (1 / 2 : ℝ) = ‖d g‖ := by
    rw [hnorm, archimedeanUnitModulation_apply, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  change (d g / (‖d g‖ : ℂ)) * (((((m g).val : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * f.val g) = _
  rw [hw, ← mul_assoc, div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn g))), hd]

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuously invertible for decay at all exponents. -/
theorem complexCoordinate_mul_allExponentialDecay (conjugate : Bool) :
    ∃ M : 𝓔(ℂ, 2, univ) ≃L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by
  letI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm := complexCoordinate_mul_allExponentialDecay_modulation.1
  have hms := complexCoordinate_mul_allExponentialDecay_modulation.2
  cases conjugate
  · exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms
      ⟨Units.coeHom ℂ, Units.continuous_val⟩
  · exact modulatedExponentialDecay_mul_quasiCharacter _ hm hms
      ⟨(starRingEnd ℂ).toMonoidHom.comp (Units.coeHom ℂ),
        Complex.continuous_conj.comp Units.continuous_val⟩

-- TODO(paper-gap): Footnote 8 flags the closed-range argument. A convergent net in the LF
-- space of tests need not eventually be bounded and a directed set need not have countable cofinality.

/-- Integrating from the puncture gives a compactly supported primitive when the two
half-line integrals vanish. -/
private theorem iteratedDeriv_puncturedTest_primitive (f : 𝒟₀(ℝ))
    (hpos : ∫ x in Ioi (0 : ℝ), f x = 0) (hneg : ∫ x in Iic (0 : ℝ), f x = 0) :
    ∃ g : 𝒟₀(ℝ), deriv (g : ℝ → ℂ) = f := by
  let G (x : ℝ) := ∫ t in (0 : ℝ)..x, f t
  have hd (x : ℝ) : HasDerivAt G (f x) x := (f.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt
  have he : deriv G = f := funext fun x ↦ (hd x).deriv
  have hc : ContDiff ℝ (∞) G := contDiff_infty_iff_deriv.mpr
    ⟨fun x ↦ (hd x).differentiableAt, he ▸ f.contDiff⟩
  have hi : Integrable (f : ℝ → ℂ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨a, ha⟩ := f.hasCompactSupport.bddBelow
  obtain ⟨b, hb⟩ := f.hasCompactSupport.bddAbove
  have hs : HasCompactSupport G := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (α := ℝ) (a := a) (b := b))
    intro x hx
    constructor
    · by_contra! h
      have hz : ∫ t in Iic x, f t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
        notMem_support.mp fun ht' ↦ (not_lt_of_ge (ha (subset_tsupport f ht'))) (ht.trans_lt h)
      exact hx (by simp [G, ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn, hz, hneg])
    · by_contra! h
      have hz : ∫ t in Ioi x, f t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦
        notMem_support.mp fun ht' ↦ (not_lt_of_ge (hb (subset_tsupport f ht'))) (h.trans ht)
      exact hx (by simpa only [hz, add_zero, hpos] using
        intervalIntegral.integral_interval_add_Ioi (a := 0) (b := x) hi.integrableOn hi.integrableOn)
  have h₀ : (0 : ℝ) ∉ tsupport f := fun h ↦ (f.tsupport_subset h) (by simp)
  obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (isClosed_closure.isOpen_compl.mem_nhds h₀)
  have hG : (0 : ℝ) ∉ tsupport G := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [Ioo_mem_nhds hlr.1 hlr.2] with x hx
    calc
      G x = ∫ _ in (0 : ℝ)..x, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact image_eq_zero_of_notMem_tsupport (hsub (ordConnected_Ioo.uIcc_subset hlr hx ht))
      _ = 0 := by simp
  refine ⟨⟨G, hc, hs, ?_⟩, he⟩
  rintro x hx (rfl : x = 0)
  exact hG hx

/-- Integration by parts relates successive moments on each component of the punctured line. -/
private theorem iteratedDeriv_puncturedTest_moment (f : 𝒟₀(ℝ)) (k : ℕ)
    (s : Set ℝ) (hs : s = Ioi 0 ∨ s = Iic 0) :
    (∫ x in s, deriv (f : ℝ → ℂ) x * (x : ℂ) ^ k) +
      (k : ℂ) * (∫ x in s, f x * (x : ℂ) ^ (k - 1)) = 0 := by
  let P (x : ℝ) := f x * (x : ℂ) ^ k
  have hp : ContDiff ℝ 1 P := (f.contDiff.of_le (by simp)).mul (Complex.ofRealCLM.contDiff.pow k)
  have hcomp : HasCompactSupport P := f.hasCompactSupport.mul_right
  have f₀ : f 0 = 0 := notMem_support.mp fun h ↦ (f.tsupport_subset (subset_tsupport f h)) (by simp)
  have hP : ∫ x in s, deriv P x = 0 := by
    rcases hs with rfl | rfl
    · simpa [P, f₀] using hcomp.integral_Ioi_deriv_eq hp 0
    · simpa [P, f₀] using hcomp.integral_Iic_deriv_eq hp 0
  have hd (x : ℝ) : deriv P x = deriv (f : ℝ → ℂ) x * (x : ℂ) ^ k +
      (k : ℂ) * (f x * (x : ℂ) ^ (k - 1)) := by
    have h := ((f.contDiff.differentiable (by simp) x).hasDerivAt.mul
      ((Complex.ofRealCLM.hasDerivAt (x := x)).fun_pow k)).deriv
    change deriv P x = deriv (f : ℝ → ℂ) x * (x : ℂ) ^ k +
      f x * ((k : ℂ) * (x : ℂ) ^ (k - 1) * (1 : ℂ)) at h
    rw [h]
    ring
  have h1 : Integrable (fun x : ℝ ↦ deriv (f : ℝ → ℂ) x * (x : ℂ) ^ k) :=
    ((f.contDiff.continuous_deriv (by simp)).mul (Complex.continuous_ofReal.pow k)).integrable_of_hasCompactSupport
      f.hasCompactSupport.deriv.mul_right
  have h2 : Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ (k - 1)) :=
    (f.continuous.mul (Complex.continuous_ofReal.pow _)).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  simpa only [hd, integral_add h1.integrableOn ((h2.const_mul _).integrableOn), integral_const_mul] using hP

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Each ordinary derivative is a continuous operator of closed range on punctured real tests. -/
theorem iteratedDeriv_puncturedTest_closedRange (m : ℕ) :
    ∃ D : 𝒟₀(ℝ) →L[ℂ] 𝒟₀(ℝ), IsClosed (range D) ∧
      ∀ f x, D f x = iteratedDeriv m (f : ℝ → ℂ) x := by
  let D : 𝒟₀(ℝ) →L[ℂ] 𝒟₀(ℝ) := TestFunction.lineDerivCLM ℂ (1 : ℝ)
  have hD (f : 𝒟₀(ℝ)) : ⇑(D f) = deriv (f : ℝ → ℂ) := by
    funext x
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ le_top]
    rfl
  let sides := {s : Set ℝ // s = Ioi 0 ∨ s = Iic 0}
  let M (s : sides) (k : ℕ) (f : 𝒟₀(ℝ)) := ∫ x in s.val, f x * (x : ℂ) ^ k
  have step (s : sides) (k : ℕ) (f : 𝒟₀(ℝ)) :
      M s k (D f) + (k : ℂ) * M s (k - 1) f = 0 := by
    simpa only [M, hD] using iteratedDeriv_puncturedTest_moment f k s.val s.property
  have range_iff (n : ℕ) (f : 𝒟₀(ℝ)) :
      f ∈ range ⇑(D ^ n) ↔ ∀ (s : sides) (k : ℕ), k < n → M s k f = 0 := by
    induction n generalizing f with
    | zero => simp
    | succ n ih =>
      constructor
      · rintro ⟨g, rfl⟩ s k hk
        rw [pow_succ', mul_apply_eq_comp]
        have h := step s k ((D ^ n) g)
        cases k with
        | zero => simpa using h
        | succ k =>
          have hz := (ih _).mp ⟨g, rfl⟩ s k (by omega)
          simpa only [Nat.succ_sub_one, hz, mul_zero, add_zero] using h
      · intro hf
        obtain ⟨g, hg⟩ := iteratedDeriv_puncturedTest_primitive f
          (by simpa [M] using hf ⟨Ioi 0, Or.inl rfl⟩ 0 (Nat.zero_lt_succ n))
          (by simpa [M] using hf ⟨Iic 0, Or.inr rfl⟩ 0 (Nat.zero_lt_succ n))
        have hgf : D g = f := TestFunction.ext (congrFun ((hD g).trans hg))
        obtain ⟨v, hv⟩ := (ih g).mpr (by
          intro s k hk
          have h := step s (k + 1) g
          rw [hgf, hf s (k + 1) (by omega), zero_add, Nat.add_sub_cancel] at h
          exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast Nat.succ_ne_zero k))
        exact ⟨v, by rw [pow_succ', mul_apply_eq_comp, hv, hgf]⟩
  refine ⟨D ^ m, ?_, ?_⟩
  · have hc (s : sides) (k : ℕ) : Continuous (M s k) := by
      let w (x : ℝ) := (x : ℂ) ^ k
      have hw : LocallyIntegrableOn w punctured(ℝ) (volume.restrict s.val) :=
        (Complex.continuous_ofReal.pow k).locallyIntegrable.locallyIntegrableOn _
      let L : 𝒟₀(ℝ) →L[ℂ] ℂ := TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ)
        (volume.restrict s.val) w
      exact L.continuous.congr fun f ↦ TestFunction.integralAgainstBilinCLM_eq_integral hw
    have heq : range ⇑(D ^ m) = ⋂ s : sides, ⋂ k : Fin m, {f | M s k f = 0} := by
      ext f
      simp only [range_iff, mem_iInter, mem_ofPred_eq, Fin.forall_iff]
    rw [heq]
    exact isClosed_iInter fun s ↦ isClosed_iInter fun k ↦ isClosed_eq (hc s k) continuous_const
  · intro f
    induction m with
    | zero => exact fun _ ↦ rfl
    | succ n ih =>
      intro x
      rw [pow_succ', mul_apply_eq_comp, hD, iteratedDeriv_succ, funext ih]

/-- If all geometric moments vanish, the integral of the geometric series vanishes wherever
its ratio is uniformly smaller than one on the support. -/
private theorem wirtinger_puncturedTest_geometric {q g : ℂ → ℂ}
    (hq : Measurable q) (hg : Integrable g) (hb : ∀ z, g z ≠ 0 → ‖q z‖ ≤ 1 / 2)
    (hm : ∀ n : ℕ, ∫ z, q z ^ n * g z = 0) :
    ∫ z, (1 - q z)⁻¹ * g z = 0 := by
  let b (n : ℕ) (z : ℂ) := (1 / 2 : ℝ) ^ n * ‖g z‖
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun n z ↦ q z ^ n * g z) (f := fun z ↦ (1 - q z)⁻¹ * g z) b
    (fun n ↦ (hq.pow_const n).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (fun n ↦ ae_of_all _ fun z ↦ by
      by_cases hz : g z = 0
      · simp [hz, b]
      · simpa only [b, norm_mul, norm_pow] using
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb z hz) n) (norm_nonneg _))
    (ae_of_all _ fun z ↦ hs.mul_right _) (by
      simpa only [b, tsum_mul_right] using hg.norm.const_mul (∑' n : ℕ, (1 / 2 : ℝ) ^ n))
    (ae_of_all _ fun z ↦ by
      by_cases hz : g z = 0
      · simp [hz]
      · exact (hasSum_geometric_of_norm_lt_one ((hb z hz).trans_lt (by norm_num))).mul_right _)
  simpa only [hm, tsum_zero] using hsum.tsum_eq.symm

/-- The Cauchy transform of a test annihilating the Laurent monomials vanishes near both
ends of the punctured plane. Expand its kernel in the two complementary annuli. -/
private theorem wirtinger_puncturedTest_support (f : 𝒟₀(ℂ))
    (hm : ∀ k : ℤ, ∫ z : ℂ, z ^ k * f z = 0) :
    let C := External.TauCeti.cauchyTransform (f : ℂ → ℂ)
    HasCompactSupport C ∧ (0 : ℂ) ∉ tsupport C := by
  intro C
  have hf : Integrable (f : ℂ → ℂ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨R, hR, hbound⟩ := f.hasCompactSupport.isBounded.exists_pos_norm_le
  have hzero : (0 : ℂ) ∉ tsupport f := fun h ↦ (f.tsupport_subset h) rfl
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhds_iff.mp (isClosed_closure.isOpen_compl.mem_nhds hzero)
  have hn {z : ℂ} (hz : f z ≠ 0) : r ≤ ‖z‖ := by
    by_contra! h
    exact hsmall (by simpa [Metric.mem_ball] using h) (subset_tsupport f hz)
  have far (w : ℂ) (hw : 2 * R < ‖w‖) : C w = 0 := by
    have hw' : w ≠ 0 := norm_pos_iff.mp (by linarith)
    have h := wirtinger_puncturedTest_geometric (q := fun z ↦ z / w) (measurable_id.div_const w) hf
      (fun z hz ↦ by rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hw')]; linarith [hbound z (subset_tsupport f hz)])
      (fun n ↦ by
        simp only [div_pow, div_mul_eq_mul_div, integral_div,
          show ∫ z : ℂ, z ^ n * f z = 0 by simpa using hm (n : ℤ), zero_div])
    have he (z : ℂ) : (w - z)⁻¹ * f z = (1 - z / w)⁻¹ * f z / w := by
      rw [show 1 - z / w = (w - z) / w by field_simp]
      simp [div_eq_mul_inv, hw', mul_comm, mul_assoc]
    change External.TauCeti.cauchyTransform (f : ℂ → ℂ) w = 0
    rw [External.TauCeti.cauchyTransform_apply]
    simp only [smul_eq_mul]
    rw [show (fun z : ℂ ↦ (w - z)⁻¹ * f z) = _ from funext he, integral_div, h, zero_div, mul_zero]
  have near (w : ℂ) (hw : ‖w‖ < r / 2) : C w = 0 := by
    let g (z : ℂ) := z⁻¹ * f z
    have hc : Continuous g := by
      apply continuous_iff_continuousAt.mpr
      intro z
      by_cases hz : z = 0
      · subst z
        apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzero] with z hz
        simp [g, hz]
      · exact (continuousAt_id.inv₀ hz).mul f.continuous.continuousAt
    have h := wirtinger_puncturedTest_geometric (q := fun z ↦ w / z) (measurable_const.div measurable_id)
      (hc.integrable_of_hasCompactSupport f.hasCompactSupport.mul_left) (fun z hz ↦ by
        have hfz : f z ≠ 0 := right_ne_zero_of_mul hz
        rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hr (hn hfz))]
        linarith [hn hfz]) (fun n ↦ by
          have he (z : ℂ) : (w / z) ^ n * g z = w ^ n * (z ^ (-((n : ℤ) + 1)) * f z) := by
            rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp, zpow_neg, zpow_natCast]
            dsimp only [g]
            rw [div_pow, pow_succ]
            simp only [div_eq_mul_inv, mul_inv_rev]; ring
          rw [show (fun z ↦ (w / z) ^ n * g z) = _ from funext he, integral_const_mul, hm, mul_zero])
    have he (z : ℂ) : (w - z)⁻¹ * f z = -((1 - w / z)⁻¹ * g z) := by
      by_cases hz : z = 0
      · subst z
        simp [g, image_eq_zero_of_notMem_tsupport hzero]
      · rw [show 1 - w / z = (z - w) / z by field_simp]
        rw [show z - w = -(w - z) by ring]
        simp only [g, div_eq_mul_inv, inv_neg, neg_mul, neg_neg]
        field_simp
    change External.TauCeti.cauchyTransform (f : ℂ → ℂ) w = 0
    rw [External.TauCeti.cauchyTransform_apply]
    simp only [smul_eq_mul]
    rw [show (fun z : ℂ ↦ (w - z)⁻¹ * f z) = _ from funext he, integral_neg, h, neg_zero, mul_zero]
  refine ⟨HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (2 * R))
    (fun z hz ↦ ?_), notMem_tsupport_iff_eventuallyEq.mpr ?_⟩
  · simpa [Metric.mem_closedBall] using (le_of_not_gt fun h ↦ hz (far z h))
  · filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hr)] with z hz
    exact near z (by simpa [Metric.mem_ball] using hz)

/-- Apply Cauchy–Pompeiu at zero to the test multiplied by the next Laurent monomial.
The multiplier is holomorphic on the support. -/
private theorem wirtinger_puncturedTest_moment (f : 𝒟₀(ℂ)) (k : ℤ) :
    ∫ z : ℂ, z ^ k * External.TauCeti.conjWirtingerDeriv (f : ℂ → ℂ) z 1 = 0 := by
  let g (z : ℂ) := z ^ (k + 1) * f z
  have hf0 : f =ᶠ[𝓝 (0 : ℂ)] (0 : ℂ → ℂ) := notMem_tsupport_iff_eventuallyEq.mp
    (fun h ↦ f.tsupport_subset h rfl)
  have hg0 : g =ᶠ[𝓝 (0 : ℂ)] (0 : ℂ → ℂ) := by
    filter_upwards [hf0] with z hz
    simp [g, hz]
  have hg : ContDiff ℝ 1 g := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z; exact contDiffAt_const.congr_of_eventuallyEq hg0
    · have h : AnalyticAt ℝ (fun z : ℂ ↦ z ^ (k+1)) z := analyticAt_id.zpow hz
      exact h.contDiffAt.mul (f.contDiff.of_le (by simp)).contDiffAt
  have hc : HasCompactSupport g := f.hasCompactSupport.mul_left
  have h := hc.cauchyTransform_conjWirtingerDeriv hg 0
  rw [External.TauCeti.cauchyTransform_apply, hg0.eq_of_nhds] at h
  have he (z : ℂ) : (0 - z)⁻¹ • External.TauCeti.conjWirtingerDeriv g z 1 =
      -(z ^ k * External.TauCeti.conjWirtingerDeriv (f : ℂ → ℂ) z 1) := by
    by_cases hz : z = 0
    · subst z
      rw [hf0.conjWirtingerDeriv_eq]
      simp [External.TauCeti.conjWirtingerDeriv_apply]
    · have hd := (hasDerivAt_zpow (k + 1) z (Or.inl hz)).differentiableAt
      change _ • External.TauCeti.conjWirtingerDeriv (fun z : ℂ ↦ z ^ (k+1) • f z) z 1 = _
      rw [External.TauCeti.conjWirtingerDeriv_smul_apply (hd.restrictScalars ℝ)
        (f.contDiff.differentiable (by simp) _) 1, hd.conjWirtingerDeriv_eq_zero]
      simp only [zero_sub, inv_neg, smul_eq_mul, zpow_add_one₀ hz, zero_apply, zero_mul, add_zero]
      field_simp
  simp only [he, integral_neg, smul_eq_mul, Pi.zero_apply, mul_eq_zero,
    inv_eq_zero, Complex.ofReal_eq_zero, Real.pi_ne_zero, false_or, neg_eq_zero] at h
  exact h

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both first Wirtinger operators have closed range on punctured complex tests. -/
theorem wirtinger_puncturedTest_closedRange (conjugate : Bool) :
    ∃ D : 𝒟₀(ℂ) →L[ℂ] 𝒟₀(ℂ), IsClosed (range D) ∧
      ∀ f z, D f z = wirtinger(conjugate) f z := by
  let X := 𝒟₀(ℂ)
  let Dx : X →L[ℂ] X := TestFunction.lineDerivCLM ℂ (1 : ℂ)
  let Dy : X →L[ℂ] X := TestFunction.lineDerivCLM ℂ Complex.I
  let scale (c : ℂ) : X →L[ℂ] X := TestFunction.postcompCLM (c • ContinuousLinearMap.id ℂ ℂ)
  let D := (scale 2⁻¹).comp (Dx + (scale Complex.I).comp Dy)
  let E := (scale 2⁻¹).comp (Dx - (scale Complex.I).comp Dy)
  have hDx (f : X) (z : ℂ) : Dx f z = fderiv ℝ (f : ℂ → ℂ) z 1 := by
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ le_top]
  have hDy (f : X) (z : ℂ) : Dy f z = fderiv ℝ (f : ℂ → ℂ) z Complex.I := by
    rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ le_top]
  have hD (f : X) (z : ℂ) : D f z = wirtingerConjDeriv f z := by
    change (2 : ℂ)⁻¹ * (Dx f z + Complex.I * Dy f z) = _
    rw [hDx, hDy, wirtingerConjDeriv, div_eq_inv_mul]
  have hE (f : X) (z : ℂ) : E f z = wirtingerDeriv f z := by
    change (2 : ℂ)⁻¹ * (Dx f z - Complex.I * Dy f z) = _
    rw [hDx, hDy, wirtingerDeriv, div_eq_inv_mul]
  have hd (f : X) (z : ℂ) : D f z = External.TauCeti.conjWirtingerDeriv (f : ℂ → ℂ) z 1 := by
    rw [hD, wirtingerConjDeriv, External.TauCeti.conjWirtingerDeriv_apply]
    simp [smul_eq_mul, div_eq_inv_mul]
  let M (k : ℤ) (f : X) := ∫ z : ℂ, z ^ k * f z
  have rangeD : range D = ⋂ k : ℤ, {f : X | M k f = 0} := by
    ext f
    rw [mem_iInter]
    constructor
    · rintro ⟨u, rfl⟩ k
      simpa only [mem_ofPred_eq, M, hd] using wirtinger_puncturedTest_moment u k
    · intro hf
      obtain ⟨hc, hz⟩ := wirtinger_puncturedTest_support f hf
      let u : X := ⟨External.TauCeti.cauchyTransform (f : ℂ → ℂ),
        f.hasCompactSupport.contDiff_cauchyTransform f.contDiff, hc, fun _ h he ↦ hz (he ▸ h)⟩
      exact ⟨u, TestFunction.ext fun z ↦ (hd u z).trans (f.hasCompactSupport.conjWirtingerDeriv_cauchyTransform
        (f.contDiff.of_le (by simp)) z)⟩
  have closedD : IsClosed (range D) := by
    rw [rangeD]
    refine isClosed_iInter fun k ↦ isClosed_eq ?_ continuous_const
    let φ (z : ℂ) := z ^ k
    have hφ : ContinuousOn φ punctured(ℂ) := fun z hz ↦
      ((hasDerivAt_zpow k z (Or.inl hz)).continuousAt).continuousWithinAt
    let L : X →L[ℂ] ℂ := TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume φ
    apply L.continuous.congr
    intro f
    exact (TestFunction.integralAgainstBilinCLM_eq_integral (hφ.locallyIntegrableOn
      isClosed_singleton.isOpen_compl.measurableSet)).trans (integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _))
  cases conjugate
  · let J : X →L[ℝ] X := TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap
    have hJ (f : X) : J (J f) = f := TestFunction.ext fun z ↦ Complex.conj_conj (f z)
    have hcomm (f : X) : D (J f) = J (E f) := by
      apply TestFunction.ext
      intro z
      rw [hD, wirtingerConjDeriv]
      have hh := (Complex.conjCLE.hasFDerivAt.comp z
        (f.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
      change fderiv ℝ (↑(J f) : ℂ → ℂ) z = _ at hh
      rw [hh]
      change (star (fderiv ℝ (f : ℂ → ℂ) z 1) + Complex.I * star (fderiv ℝ (f : ℂ → ℂ) z Complex.I)) / 2 =
        star (E f z)
      rw [hE, wirtingerDeriv]
      simp [sub_eq_add_neg]
    have hr : range E = J ⁻¹' range D := by
      ext f
      exact ⟨fun ⟨g, hg⟩ ↦ ⟨J g, (hcomm g).trans (congrArg J hg)⟩, fun ⟨g, hg⟩ ↦
        ⟨J g, by rw [← hJ (E (J g)), ← hcomm, hJ, hg, hJ]⟩⟩
    exact ⟨E, hr ▸ closedD.preimage J.continuous, hE⟩
  · exact ⟨D, closedD, hD⟩

/-- Elementary logarithmic coordinates on the two components of the punctured line. -/
private theorem iteratedDeriv_exponentialDecay_chart :
    ∃ w : ℝˣ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (ZMod 2)), ∀ x,
      realBruhatCoordinate (w x).toAdd.1 = Real.log x.val ∧
      (w x).toAdd.2.2.2 = if 0 < x.val then 0 else 1 := by
  let X := ElementaryLieGroup 1 0 0 (ZMod 2)
  let s (x : ℝˣ) : ZMod 2 := if 0 < x.val then 0 else 1
  let u (x : ℝˣ) : Multiplicative X := Multiplicative.ofAdd
    (realBruhatCoordinate.symm (Real.log x.val), 0, 0, s x)
  let r (y : X) := Real.exp (realBruhatCoordinate y.1)
  let v (y : Multiplicative X) : ℝˣ := Units.mk0
    (if y.toAdd.2.2.2 = 0 then r y.toAdd else -r y.toAdd)
    (by split <;> simp [r, Real.exp_ne_zero])
  have hs : Continuous s := by
    have hco : IsClopen {x : ℝˣ | 0 < x.val} := by
      refine ⟨?_, isOpen_lt continuous_const Units.continuous_val⟩
      have h : {x : ℝˣ | 0 < x.val} = {x | 0 ≤ x.val} :=
        Set.ext fun x ↦ (show 0 < x.val ↔ 0 ≤ x.val from ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h x.ne_zero.symm⟩)
      rw [h]
      exact isClosed_le continuous_const Units.continuous_val
    exact Continuous.if (by simp [hco.frontier_eq]) continuous_const continuous_const
  have hlog : Continuous (fun x : ℝˣ ↦ Real.log x.val) := continuous_iff_continuousAt.mpr
    fun x ↦ (Real.continuousAt_log x.ne_zero).comp Units.continuous_val.continuousAt
  let w : ℝˣ ≃ₜ* Multiplicative X :=
    { toFun := u
      invFun := v
      left_inv := fun x ↦ by
        apply Units.ext
        change (if s x = 0 then Real.exp (Real.log x.val) else -Real.exp (Real.log x.val)) = x.val
        rw [Real.exp_log_eq_abs x.ne_zero]
        by_cases h : 0 < x.val
        · simp [s, h, abs_of_pos h]
        · simp [s, h, abs_of_nonpos (le_of_not_gt h)]
      right_inv := fun y ↦ by
        change (realBruhatCoordinate.symm (Real.log (v y).val), 0, 0, s (v y)) = y.toAdd
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · change realBruhatCoordinate.symm (Real.log (if y.toAdd.2.2.2 = 0 then _ else _)) = _
          split <;> simp only [r, Real.log_neg_eq_log, Real.log_exp, realBruhatCoordinate.symm_apply_apply]
        · have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
          rcases hb y.toAdd.2.2.2 with h | h <;> simp [s, v, h, r, Real.exp_pos, (Real.exp_pos _).le]
      map_mul' := fun x y ↦ by
        change (realBruhatCoordinate.symm (Real.log (x.val * y.val)), 0, 0, s (x*y)) =
          ((realBruhatCoordinate.symm (Real.log x.val), 0, 0, s x) : X) +
          (realBruhatCoordinate.symm (Real.log y.val), 0, 0, s y)
        refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
        · change realBruhatCoordinate.symm (Real.log (x.val * y.val)) = _
          rw [Real.log_mul x.ne_zero y.ne_zero, map_add]
          rfl
        · change s (x*y) = s x + s y
          rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;> rcases lt_or_gt_of_ne y.ne_zero with hy | hy
          · simp [s, hx.not_gt, hy.not_gt, mul_pos_of_neg_of_neg hx hy]; decide
          · simp [s, hx.not_gt, hy, (mul_neg_of_neg_of_pos hx hy).not_gt]
          · simp [s, hx, hy.not_gt, (mul_neg_of_pos_of_neg hx hy).not_gt]
          · simp [s, hx, hy, mul_pos hx hy]
      continuous_toFun := (realBruhatCoordinate.symm.continuous.comp hlog).prodMk
        (continuous_const.prodMk (continuous_const.prodMk hs))
      continuous_invFun := by
        apply Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
        change Continuous (fun y : X ↦ if y.2.2.2 = 0 then r y else -r y)
        have hco : IsClopen {y : X | y.2.2.2 = 0} :=
          (isClopen_discrete ({0} : Set (ZMod 2))).preimage (continuous_snd.comp (continuous_snd.comp continuous_snd))
        have hr : Continuous r := Real.continuous_exp.comp (realBruhatCoordinate.continuous.comp continuous_fst)
        exact Continuous.if (by simp [hco.frontier_eq]) hr hr.neg }
  exact ⟨w, fun x ↦ ⟨realBruhatCoordinate.apply_symm_apply _, rfl⟩⟩

private theorem iteratedDeriv_exponentialDecay_goodBot :
    IsCompactlyGeneratedGroup (lcaAnnihilator (⊥ : Subgroup ℝˣ)) := by
  obtain ⟨w, _⟩ := iteratedDeriv_exponentialDecay_chart
  let e : ElementaryLCAPresentation ℝˣ := ⟨1, 0, 0, ZMod 2, w⟩
  exact (isBruhatGoodSubgroup_bot_iff.mpr ((lca_elementary_iff.mpr ⟨e⟩).2)).2.2

/-- Glue two elementary real-line functions on the two fibres. Each output seminorm
is controlled by the maximum of the corresponding input seminorms. -/
private theorem iteratedDeriv_exponentialDecay_glue :
    ∃ L : (ElementarySchwartz 1 0 0 PUnit × ElementarySchwartz 1 0 0 PUnit) →L[ℂ]
        ElementarySchwartz 1 0 0 (ZMod 2), ∀ f p,
      L f p = (if p.2.2.2 = 0 then f.1 else f.2) (p.1, p.2.1, p.2.2.1, PUnit.unit) := by
  let E := ElementarySchwartz 1 0 0 PUnit
  let X := ElementaryLieGroup 1 0 0 (ZMod 2)
  let fn (f : E × E) (p : X) :=
    (if p.2.2.2 = 0 then f.1 else f.2) (p.1, p.2.1, p.2.2.1, PUnit.unit)
  have hb (f : E × E) (i : ElementarySchwartzIndex 1 0 0) :
      elementarySchwartzBound (fn f) i ≤
        max (elementarySchwartzBound f.1.val i) (elementarySchwartzBound f.2.val i) := by
    refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
    let g : E := if b = 0 then f.1 else f.2
    have h : elementarySchwartzBound g.val i ≤
        max (elementarySchwartzBound f.1.val i) (elementarySchwartzBound f.2.val i) := by
      dsimp only [g]; split <;> simp
    refine le_trans ?_ h
    unfold elementarySchwartzBound
    exact le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le PUnit.unit le_rfl))
  let A : E × E →ₗ[ℂ] ElementarySchwartz 1 0 0 (ZMod 2) :=
    { toFun := fun f ↦ ⟨fn f, fun a b ↦ (if b = 0 then f.1 else f.2).property.1 a PUnit.unit,
        fun i ↦ (hb f i).trans_lt (max_lt (f.1.property.2 i) (f.2.property.2 i))⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun p ↦ by
        change fn (f+g) p = fn f p + fn g p
        by_cases h : p.2.2.2 = 0 <;> simp [fn, h] <;> rfl)
      map_smul' := fun c f ↦ Subtype.ext (funext fun p ↦ by
        change fn (c • f) p = c • fn f p
        by_cases h : p.2.2.2 = 0 <;> simp [fn, h] <;> rfl) }
  refine ⟨⟨A, elementarySchwartz_withSeminorms.continuous_of_continuous_comp A fun i ↦ ?_⟩,
    fun _ _ ↦ rfl⟩
  let q : Seminorm ℂ E := elementarySchwartzSeminorm i
  have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm i
  let Q := (q.comp (LinearMap.fst ℂ E E)) ⊔ (q.comp (LinearMap.snd ℂ E E))
  have hQ : Continuous Q := (hq.comp continuous_fst).max (hq.comp continuous_snd)
  apply Seminorm.continuous_of_le hQ
  intro f
  change (elementarySchwartzBound (fn f) i).toReal ≤
    max (elementarySchwartzBound f.1.val i).toReal (elementarySchwartzBound f.2.val i).toReal
  rw [← ENNReal.toReal_max (f.1.property.2 i).ne (f.2.property.2 i).ne]
  exact ENNReal.toReal_mono (max_lt (f.1.property.2 i) (f.2.property.2 i)).ne (hb f i)

/-- Continuous forward realization from an elementary presentation; only the stage
inclusion is needed, not its inverse. -/
private theorem iteratedDeriv_exponentialDecay_realize {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (e : ElementaryLCAPresentation G) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G, ∀ g x, j g x = g (e.equiv x).toAdd := by
  have hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  let hk := (isBruhatGoodSubgroup_bot_iff (G := G)).mpr hE.2
  let a := fullBruhatStage hE.1 hk
  have hV := fullBruhatStage_quotientEquiv hE.1 hk (MonoidHom.id G) IsOpenQuotientMap.id (by simp)
  let v := hV.choose
  let d : ElementaryLCAPresentation a.quotient := {e with equiv := v.trans e.equiv}
  let j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion a d, (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _
      fun q ↦ q.property a d⟩
  refine ⟨j, fun g x ↦ ?_⟩
  change schwartzBruhatStageRealization a d g x = _
  have hx : x ∈ a.val.1 := Subgroup.mem_top x
  rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
  exact congrArg (fun y : G ↦ g (e.equiv y).toAdd) (hV.choose_spec x)

/-- Assemble independently prescribed logarithmic profiles by realizing them in the
full elementary stage with trivial kernel. -/
private theorem iteratedDeriv_exponentialDecay_assemble :
    ∃ J : (𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ)) →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f x, J f x = if 0 < x.val then f.1 (Real.log x.val) else f.2 (Real.log x.val) := by
  let w := iteratedDeriv_exponentialDecay_chart.choose
  have hw := iteratedDeriv_exponentialDecay_chart.choose_spec
  let e : ElementaryLCAPresentation ℝˣ := ⟨1, 0, 0, ZMod 2, w⟩
  let j := (iteratedDeriv_exponentialDecay_realize e).choose
  have hj := (iteratedDeriv_exponentialDecay_realize e).choose_spec
  let I := (elementarySchwartz_real_equiv PUnit.{1}).choose
  have hI := (elementarySchwartz_real_equiv PUnit.{1}).choose_spec
  let L := iteratedDeriv_exponentialDecay_glue.choose
  have hL := iteratedDeriv_exponentialDecay_glue.choose_spec
  refine ⟨j.comp (L.comp (I.toContinuousLinearMap.prodMap I.toContinuousLinearMap)), fun f x ↦ ?_⟩
  change j (L (I f.1, I f.2)) x = _
  rw [hj, hL]
  change (if (w x).toAdd.2.2.2 = 0 then I f.1 else I f.2)
    ((w x).toAdd.1, (w x).toAdd.2.1, (w x).toAdd.2.2.1, PUnit.unit) = _
  rw [(hw x).2]
  by_cases hx : 0 < x.val <;> simp only [hx, ite_true, ite_false, one_ne_zero]
  · exact (hI f.1 _).trans (congrArg (f.1 : ℝ → ℂ) (hw x).1)
  · exact (hI f.2 _).trans (congrArg (f.2 : ℝ → ℂ) (hw x).1)

/-- Exponential coordinates on either component restrict an elementary Bruhat stage
of the real units to the elementary Schwartz space of a line. -/
private theorem iteratedDeriv_exponentialDecay_stage_slice
    (u : ℝˣ) (q : ℝ ≃ₜ+ ElementaryLieGroup 1 0 0 PUnit.{1})
    (a : BruhatStructuralPair ℝˣ) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) :
    (fun x ↦ schwartzBruhatStageRealization a e s
      (u * Units.mk0 (Real.exp (q.symm x)) (Real.exp_pos _).ne')) ∈
        elementarySchwartzSubmodule 1 0 0 PUnit.{1} := by
  classical
  let expU : Multiplicative ℝ →* ℝˣ :=
    { toFun := fun x ↦ Units.mk0 (Real.exp x.toAdd) (Real.exp_pos _).ne'
      map_one' := Units.ext Real.exp_zero
      map_mul' := fun x y ↦ Units.ext (Real.exp_add _ _) }
  have hc : Continuous expU := Units.isEmbedding_val₀.continuous_iff.mpr Real.continuous_exp
  have ho : IsOpenMap expU :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ)).isOpenMap_iff.mpr Real.isOpenEmbedding_exp.isOpenMap
  have hmem (t : Multiplicative ℝ) : expU t ∈ a.val.1 := by
    let V : OpenSubgroup ℝˣ := ⟨a.val.1, a.property.1⟩
    have h : IsClopen ((fun x : ℝ ↦ expU (.ofAdd x)) ⁻¹' (V : Set ℝˣ)) := V.isClopen.preimage hc
    have h1 : (0 : ℝ) ∈ (fun x : ℝ ↦ expU (.ofAdd x)) ⁻¹' (V : Set ℝˣ) := by
      change expU 1 ∈ a.val.1
      rw [map_one]; exact a.val.1.one_mem
    exact (Set.eq_univ_iff_forall.mp (h.eq_univ ⟨0, h1⟩)) t.toAdd
  by_cases hu : u ∈ a.val.1
  · let E := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
    let j : Multiplicative ℝ →* a.val.1 := expU.codRestrict _ hmem
    let k : a.val.1 →* Multiplicative E := e.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
    let p : ℝ →+ E := MonoidHom.toAdditive (k.comp j)
    have hkc : Continuous k := e.equiv.continuous.comp QuotientGroup.continuous_mk
    have hko : IsOpenMap k := e.equiv.toHomeomorph.isOpenMap.comp (QuotientGroup.isOpenMap_coe
      (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))
    have hpc : Continuous p := hkc.comp (hc.subtype_mk hmem)
    have hpo : IsOpenMap p := hko.comp (ho.subtype_mk hmem)
    have hk : p.ker ≤ q.toAddEquiv.toAddMonoidHom.ker := by
      intro t ht
      have hqt : (QuotientGroup.mk (j (.ofAdd t)) : a.quotient) = 1 :=
        e.equiv.injective ((show k (j (.ofAdd t)) = 1 from ht).trans (map_one e.equiv).symm)
      have hkernel := (a.quotient_mk_eq_one _).mp hqt
      let m := archimedeanUnitModulation ℝ 1
      have hm : m (expU (.ofAdd t)) = 1 := compactSubgroup_le_modulation_ker m _ (compact_bruhat_kernel a) hkernel
      have ht0 := congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) hm
      change ((archimedeanUnitModulation ℝ 1 (expU (.ofAdd t))).val : ℝ) = 1 at ht0
      rw [archimedeanUnitModulation_apply, pow_one] at ht0
      change ‖Real.exp t‖ = 1 at ht0
      rw [Real.norm_of_nonneg (Real.exp_pos t).le] at ht0
      rw [(Real.exp_eq_one_iff t).mp ht0]
      exact q.toAddEquiv.toAddMonoidHom.ker.zero_mem
    obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly (m := e.realDim) (n := e.torusDim)
      (r := e.latticeRank) (F := e.finiteFactor)
    let v : a.val.1 := ⟨u, hu⟩
    apply elementarySchwartz_of_common_pullback p hpc hpo q.toAddEquiv.toAddMonoidHom q.continuous
      q.toHomeomorph.isOpenMap q.surjective hk (T ((k v).toAdd, s))
    intro t
    rw [hT]
    change s ((k v).toAdd + p t) = schwartzBruhatStageRealization a e s (u * expU (.ofAdd (q.symm (q t))))
    rw [q.symm_apply_apply, schwartzBruhatStageRealization_apply, dite_eq_left (a.val.1.mul_mem hu (hmem _))]
    exact congrArg (fun w ↦ s w.toAdd) (map_mul k v (j (.ofAdd t))).symm
  · have hz (t : ℝ) : schwartzBruhatStageRealization a e s (u * expU (.ofAdd t)) = 0 := by
      rw [schwartzBruhatStageRealization_apply, dite_eq_right ((a.val.1.mul_mem_cancel_right (hmem _)).not.mpr hu)]
    convert (elementarySchwartzSubmodule 1 0 0 PUnit.{1}).zero_mem using 1
    exact funext fun x ↦ hz (q.symm x)

/-- Stagewise restriction assembles into a continuous linear map, since the
source has the final seminorm topology and each stage is Fréchet. -/
private theorem iteratedDeriv_exponentialDecay_elementary_slice (u : ℝˣ)
    (v : ElementaryLieGroup 1 0 0 PUnit.{1} ≃ₜ+ ℝ) :
    ∃ A : SchwartzBruhat ℝˣ →L[ℂ] ElementarySchwartz 1 0 0 PUnit.{1},
      ∀ f x, A f x = f (u * Units.mk0 (Real.exp (v x)) (Real.exp_pos _).ne') := by
  let E := ElementaryLieGroup 1 0 0 PUnit.{1}
  let X := ElementarySchwartz 1 0 0 PUnit.{1}
  let pt (x : E) := u * Units.mk0 (Real.exp (v x)) (Real.exp_pos _).ne'
  let L := LinearMap.funLeft ℂ ℂ pt
  have hmem : schwartzBruhatSubmodule ℝˣ ≤ (elementarySchwartzSubmodule 1 0 0 PUnit.{1}).comap L := by
    unfold schwartzBruhatSubmodule
    apply iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨s, rfl⟩
    exact iteratedDeriv_exponentialDecay_stage_slice u v.symm a e s
  let A : SchwartzBruhat ℝˣ →ₗ[ℂ] X :=
    (L.comp (schwartzBruhatSubmodule ℝˣ).subtype).codRestrict _ fun f ↦ hmem f.property
  have hA : Continuous A := by
    let : PolynormableSpace ℂ X := elementarySchwartz_withSeminorms.toPolynormableSpace
    apply continuous_out_of_schwartzBruhat
    intro a e
    let : BarrelledSpace ℂ (SchwartzBruhatStage e) := isFrechetTVS_barrelled elementarySchwartz_isFrechet
    apply continuous_toElementarySchwartz_of_eval (A.comp (schwartzBruhatStageCLM a e).toLinearMap)
    intro x
    let ev := (LinearMap.proj (pt x)).comp (schwartzBruhatStageRealization a e)
    exact ⟨⟨ev, continuous_schwartzBruhatStage_eval a e (pt x)⟩, fun _ ↦ rfl⟩
  exact ⟨⟨A, hA⟩, fun _ _ ↦ rfl⟩

/-- Pulling back along a translate of the exponential gives an ordinary
Schwartz function, continuously and linearly in the Schwartz–Bruhat test. -/
private theorem iteratedDeriv_exponentialDecay_slice (u : ℝˣ) :
    ∃ S : SchwartzBruhat ℝˣ →L[ℂ] 𝓢(ℝ, ℂ),
      ∀ f (t : ℝ), S f t = f (u * Units.mk0 (Real.exp t) (Real.exp_pos t).ne') := by
  classical
  let E := ElementaryLieGroup 1 0 0 PUnit.{1}
  let X := ElementarySchwartz 1 0 0 PUnit.{1}
  let line := realBruhatCoordinate
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit.{1}) := uniqueOfSubsingleton 0
  let v : E ≃ₜ+ ℝ := ContinuousAddEquiv.mk' ((Homeomorph.prodUnique _ _).trans line.toHomeomorph)
    (fun x y ↦ line.map_add x.1 y.1)
  refine (iteratedDeriv_exponentialDecay_elementary_slice u v).elim fun A hA ↦ ?_
  refine (elementarySchwartz_real_equiv PUnit.{1}).elim fun T hT ↦ ?_
  refine ⟨T.symm.toContinuousLinearMap.comp A, fun f t ↦ ?_⟩
  let x : E := (line.symm t, 0)
  have hv : v x = t := line.apply_symm_apply t
  calc
    _ = (T (T.symm (A f))) x := ((hT (T.symm (A f)) x).trans (congrArg (⇑(T.symm (A f))) hv)).symm
    _ = A f x := congrArg (fun g : X ↦ g x) (T.apply_symm_apply (A f))
    _ = _ := (hA f x).trans (congrArg (fun z : ℝ ↦ f (u * Units.mk0 (Real.exp z) (Real.exp_pos z).ne')) hv)

/-- If the trivial subgroup gives an admissible stage, its inclusion is surjective,
so the ambient topology is induced by the joint Schwartz–Bruhat twists. -/
private theorem iteratedDeriv_exponentialDecay_inducing_of_bot {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ) (hb : IsCompactlyGeneratedGroup (lcaAnnihilator (⊥ : Subgroup G))) :
    IsInducing (fun (f : ModulatedExponentialDecay m I) (a : I) ↦ modulatedExponentialDecayTwist m I a f) := by
  let E := ModulatedExponentialDecay m I
  let K := {k : Subgroup G // IsCompact (k : Set G) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)}
  let k : K := ⟨⊥, by rw [Subgroup.coe_bot]; exact isCompact_singleton, hb⟩
  let S := ModulatedExponentialDecayStage m I k
  let j : S →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp
    j fun p ↦ p.property k
  have hsur : Surjective j := fun f ↦ ((modulatedExponentialDecayStageInclusion_range m I k).2 f).mpr
    fun g u ↦ congrArg f.val (by rw [show u.val = 1 from Subgroup.mem_bot.mp u.property, mul_one])
  let e : G ⧸ k.val ≃ₜ* G := QuotientGroup.quotientBot.toContinuousMulEquiv fun _ ↦
    (QuotientGroup.isQuotientMap_mk k.val).isOpen_preimage.symm
  let P := schwartzBruhatPullbackEquiv e
  let T (f : E) (a : I) := modulatedExponentialDecayTwist m I a f
  have hT : Continuous T := continuous_pi (continuous_decay_twist m I)
  let d (F : I → SchwartzBruhat G) (a : I) := P (F a)
  have hd : Continuous d := continuous_pi fun a ↦ P.continuous.comp (continuous_apply a)
  let U (f : S) (a : I) :=
    modulatedExponentialDecayTwist (quotientModulation m k.val k.property.1) I a f
  have hfac : d ∘ (T ∘ j) = U := by
    funext f a
    apply Subtype.ext
    funext q
    exact QuotientGroup.induction_on q fun g ↦ rfl
  have hU : IsInducing U := modulatedExponentialDecayStage_twists_isInducing m I k
  have hcomp : IsInducing (d ∘ (T ∘ j)) := Eq.mpr (congrArg IsInducing hfac) hU
  have hi : IsInducing (T ∘ j) := IsInducing.of_comp (hT.comp hj) hd hcomp
  refine ⟨le_antisymm hT.le_induced (fun V hV ↦ ?_)⟩
  obtain ⟨B, hB, hpre⟩ := hi.isOpen_iff.mp (hV.preimage hj)
  exact isOpen_induced_iff.mpr ⟨B, hB, hsur.preimage_injective hpre⟩

private theorem iteratedDeriv_exponentialDecay_inducing (I : Set ℝ) :
    IsInducing (fun (f : ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) I) (a : I) ↦
      modulatedExponentialDecayTwist (archimedeanUnitModulation ℝ 1) I a f) :=
  iteratedDeriv_exponentialDecay_inducing_of_bot _ _ iteratedDeriv_exponentialDecay_goodBot

/-- A positive weight controls powers of the logarithmic coordinate near zero.
At infinity one additional integer Schwartz weight controls the same powers. -/
private theorem realSchwartz_logWeight_bound (b : ℝ) (hb : 0 < b) (k : ℕ) :
    ∃ (N : ℕ) (C : ℝ≥0), ∀ (f : 𝓢(ℝ, ℂ)) (x : ℝ),
      |x| ^ k * Real.exp (b * x) * ‖f (Real.exp x)‖ ≤
        C * (SchwartzMap.seminorm ℂ 0 0 f + SchwartzMap.seminorm ℂ N 0 f) := by
  let δ := min b 1
  have hδ : 0 < δ := lt_min hb zero_lt_one
  obtain ⟨N, hN⟩ := exists_nat_ge (b + δ)
  let C : ℝ≥0 := ⟨(k.factorial : ℝ) / δ ^ k, by positivity⟩
  have hpow (y : ℝ) (hy : 0 ≤ y) : y ^ k ≤ (C : ℝ) * Real.exp (δ * y) := by
    have h := (div_le_iff₀ (show 0 < (k.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp (δ * y) (mul_nonneg hδ.le hy) k)
    change _ ≤ _ / _ * _
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hδ k)]
    simpa only [mul_pow, mul_comm] using h
  refine ⟨N, C, fun f x ↦ ?_⟩
  have h := mul_le_mul_of_nonneg_right (hpow |x| (abs_nonneg _)) (Real.exp_pos (b*x)).le
  rw [mul_assoc, ← Real.exp_add] at h
  have hbnd (a d : ℝ) (ha : δ * |x| + b*x ≤ a)
      (hd : Real.exp a * ‖f (Real.exp x)‖ ≤ d) :
      |x| ^ k * Real.exp (b*x) * ‖f (Real.exp x)‖ ≤ C * d := by
    refine (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) (norm_nonneg _)).trans hd) C.property
  by_cases hx : 0 ≤ x
  · apply hbnd ((N : ℝ) * x)
    · rw [abs_of_nonneg hx]
      simpa only [add_mul, add_comm] using mul_le_mul_of_nonneg_right hN hx
    · rw [Real.exp_nat_mul]
      have hf := SchwartzMap.norm_pow_mul_le_seminorm ℂ f N (Real.exp x)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hf
      exact hf.trans (le_add_of_nonneg_left (apply_nonneg _ _))
  · apply hbnd 0
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      have hδb : δ ≤ b := min_le_left _ _
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hδb) (le_of_not_ge hx)]
    · rw [Real.exp_zero, one_mul]
      exact (SchwartzMap.norm_le_seminorm ℂ f _).trans
        (le_add_of_nonneg_right (apply_nonneg _ _))

/-- In exponential coordinates the derivative of the weighted profile is the
weighted profile of the Euler derivative plus the weight times the input. -/
private theorem realSchwartz_weightedExpProfile (b : ℝ) (hb : 0 < b) :
    ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ), ∀ f x,
      L f x = (Real.exp (b*x) : ℂ) * f (Real.exp x) := by
  let X := 𝓢(ℝ, ℂ)
  let T : X →L[ℂ] X := (b : ℂ) • ContinuousLinearMap.id ℂ X +
    (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (y : ℂ))).comp (SchwartzMap.derivCLM ℂ ℂ)
  let g (f : X) (x : ℝ) := (Real.exp (b*x) : ℂ) * f (Real.exp x)
  have hT (f : X) (y : ℝ) : T f y = (b : ℂ) * f y + (y : ℂ) * deriv f y := by
    change (b : ℂ) * f y + SchwartzMap.smulLeftCLM ℂ (fun t : ℝ ↦ (t : ℂ))
      (SchwartzMap.derivCLM ℂ ℂ f) y = _
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    rfl
  have hd (f : X) : deriv (g f) = g (T f) := by
    funext x
    have h1 := (((hasDerivAt_id x).const_mul b).exp).ofReal_comp
    have h2 := f.differentiableAt.hasDerivAt.scomp x (Real.hasDerivAt_exp x)
    rw [show deriv (g f) x = _ from (h1.fun_mul h2).deriv]
    change _ = (Real.exp (b*x) : ℂ) * T f (Real.exp x)
    rw [hT]
    simp only [id_eq, Function.comp_apply, mul_one, Complex.ofReal_mul, Complex.real_smul]
    ring
  have hi (f : X) (n : ℕ) : iteratedDeriv n (g f) = g ((T ^ n) f) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, ih, hd, pow_succ', mul_apply_eq_comp]
  choose N C hbnd using realSchwartz_logWeight_bound b hb
  let q (k n : ℕ) : Seminorm ℂ X := C k •
    ((SchwartzMap.seminorm ℂ 0 0 + SchwartzMap.seminorm ℂ (N k) 0).comp (T ^ n).toLinearMap)
  have hbound (k n : ℕ) (f : X) (x : ℝ) : |x| ^ k * ‖iteratedDeriv n (g f) x‖ ≤ q k n f := by
    rw [hi]
    change |x| ^ k * ‖(Real.exp (b*x) : ℂ) * _‖ ≤ _
    rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
    exact hbnd k ((T ^ n) f) x
  have hsmooth (f : X) : ContDiff ℝ (∞) (g f) :=
    (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).mul
      ((f.smooth (⊤ : ℕ∞)).comp Real.contDiff_exp)
  have hdec (f : X) (k n : ℕ) : ∃ c : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g f) x‖ ≤ c := by
    refine ⟨q k n f, fun x ↦ ?_⟩
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound k n f x
  let L : X →ₗ[ℂ] X :=
    { toFun := fun f ↦ ⟨g f, hsmooth f, hdec f⟩
      map_add' := fun f h ↦ SchwartzMap.ext fun x ↦ mul_add _ _ _
      map_smul' := fun c f ↦ SchwartzMap.ext fun x ↦ mul_left_comm _ _ _ }
  refine ⟨⟨L, (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp L fun i ↦ ?_⟩,
    fun _ _ ↦ rfl⟩
  have hp (j : ℕ) : Continuous (SchwartzMap.seminorm ℂ j 0 : X → ℝ) :=
    (schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (j, 0)
  have hc : Continuous (q i.1 i.2) := continuous_const.mul
    (((hp 0).add (hp (N i.1))).comp (T ^ i.2).continuous)
  apply Seminorm.continuous_of_le hc
  intro f
  exact SchwartzMap.seminorm_le_bound' ℂ i.1 i.2 (L f) (apply_nonneg _ _) (hbound i.1 i.2 f)

/-- Paper: §5.3.3, p. 249.
Restriction gives a continuous linear injection of additive real Schwartz functions into
the space with all positive weights. -/
theorem realSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℝ, ℂ) →L[ℂ] 𝓔(ℝ, 1, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (u : ℝˣ), (R f).val u = f u.val := by
  let X := 𝓢(ℝ, ℂ)
  let m := archimedeanUnitModulation ℝ 1
  let I : Set ℝ := Ioi 0
  let r : X →ₗ[ℂ] (ℝˣ → ℂ) :=
    { toFun := fun f u ↦ f u.val
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  obtain ⟨J, hJ⟩ := iteratedDeriv_exponentialDecay_assemble
  let negX : X →L[ℂ] X :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ)
  have ht (b : I) : ∃ B : X →L[ℂ] SchwartzBruhat ℝˣ, ∀ f,
      (B f).val = modulationWeight m b (r f) := by
    obtain ⟨L, hL⟩ := realSchwartz_weightedExpProfile b.val b.property
    refine ⟨J.comp (L.prod (L.comp negX)), fun f ↦ funext fun u ↦ ?_⟩
    change J (L f, L (negX f)) u = _
    rw [hJ]
    have hu := abs_pos.mpr u.ne_zero
    change _ = (((((m u).val : ℝ) ^ (b : ℝ) : ℝ)) : ℂ) * f u.val
    rw [archimedeanUnitModulation_apply, pow_one, Real.norm_eq_abs, Real.rpow_def_of_pos hu,
      Real.log_abs, mul_comm (Real.log u.val)]
    by_cases hpos : 0 < u.val
    · simp only [ite_eq_left hpos, hL, Real.exp_log hpos]
    · simp only [ite_eq_right hpos, hL, Real.exp_log_eq_abs u.ne_zero,
        abs_of_nonpos (le_of_not_gt hpos)]
      change _ * f (- -u.val) = _
      rw [neg_neg]
  let R : X →ₗ[ℂ] 𝓔(ℝ, 1, I) := r.codRestrict (modulatedExponentialDecaySubmodule m I) fun f ↦
    (Submodule.mem_iInf _).mpr fun b ↦ Submodule.mem_comap.mpr (by
      rw [← (ht b).choose_spec f]
      exact ((ht b).choose f).property)
  have hR : Continuous (R : X → 𝓔(ℝ, 1, I)) := by
    apply (iteratedDeriv_exponentialDecay_inducing I).continuous_iff.mpr
    refine continuous_pi fun b ↦ (ht b).choose.continuous.congr fun f ↦ ?_
    exact Subtype.ext ((ht b).choose_spec f)
  refine ⟨⟨R, hR⟩, fun f g hfg ↦ ?_, fun _ _ ↦ rfl⟩
  apply DFunLike.coe_injective
  apply Continuous.ext_on (dense_compl_singleton (0 : ℝ)) f.continuous g.continuous
  intro x hx
  exact congrArg (fun v : 𝓔(ℝ, 1, Ioi 0) ↦ v.val (Units.mk0 x hx)) hfg

private theorem iteratedDeriv_exponentialDecay_logDeriv (f : ℝ → ℂ) (g : 𝓢(ℝ, ℂ))
    (b x : ℝ) (hx : x ≠ 0) (hg : ∀ᶠ y in 𝓝 x,
      f y = (Real.exp (Real.log y * -b) : ℂ) * g (Real.log y)) :
    ((|x| ^ (b + 1) : ℝ) : ℂ) * deriv f x =
      ((|x| / x : ℝ) : ℂ) * (deriv g (Real.log x) - (b : ℂ) * g (Real.log x)) := by
  have hl := Real.hasDerivAt_log hx
  have hw := ((hl.mul_const (-b)).exp).ofReal_comp
  have hd := ((g.differentiableAt (x := Real.log x)).hasDerivAt.scomp x hl)
  have h := ((hw.fun_mul hd).congr_of_eventuallyEq hg).deriv
  have hcancel : |x| ^ b * Real.exp (Real.log x * -b) = 1 := by
    rw [Real.rpow_def_of_pos (abs_pos.mpr hx), Real.log_abs, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [h, Real.rpow_add_one (abs_ne_zero.mpr hx)]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.real_smul, Function.comp_apply]
  have hc : ((|x| ^ b : ℝ) : ℂ) * (Real.exp (Real.log x * -b) : ℂ) = 1 := by exact_mod_cast hcancel
  linear_combination ((|x| : ℝ) : ℂ) * (x : ℂ)⁻¹ *
    (deriv g (Real.log x) - (b : ℂ) * g (Real.log x)) * hc

private theorem iteratedDeriv_exponentialDecay_twistFormula (f : ℝˣ → ℂ)
    (g : 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ)) (b : ℝ) (hg : ∀ x : ℝˣ,
      (if 0 < x.val then g.1 else g.2) (Real.log x.val) = ((|x.val| ^ b : ℝ) : ℂ) * f x)
    (x : ℝˣ) :
    ((|x.val| ^ (b + 1) : ℝ) : ℂ) * deriv zeroExtension(f) x.val =
      if 0 < x.val then deriv g.1 (Real.log x.val) - b * g.1 (Real.log x.val)
      else -(deriv g.2 (Real.log x.val) - b * g.2 (Real.log x.val)) := by
  have hlocal (y : ℝ) (hy : y ≠ 0) : zeroExtension(f) y =
      (Real.exp (Real.log y * -b) : ℂ) *
        (if 0 < y then g.1 else g.2) (Real.log y) := by
    rw [show (if 0 < y then g.1 else g.2) (Real.log y) = _ from hg (Units.mk0 y hy)]
    simp only [dite_eq_left hy]
    change f _ = _ * (((|y| ^ b : ℝ) : ℂ) * f _)
    rw [Real.rpow_def_of_pos (abs_pos.mpr hy), Real.log_abs, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add, show Real.log y * -b + Real.log y * b = 0 by ring]
    simp
  by_cases hx : 0 < x.val
  · rw [ite_eq_left hx]
    have h := iteratedDeriv_exponentialDecay_logDeriv zeroExtension(f) g.1 b x.val x.ne_zero (by
      filter_upwards [lt_mem_nhds hx] with y hy
      simpa only [ite_eq_left hy] using hlocal y hy.ne')
    simpa only [abs_of_pos hx, div_self x.ne_zero, Complex.ofReal_one, one_mul] using h
  · rw [ite_eq_right hx]
    have hx' := lt_of_le_of_ne (le_of_not_gt hx) x.ne_zero
    have h := iteratedDeriv_exponentialDecay_logDeriv zeroExtension(f) g.2 b x.val x.ne_zero (by
      filter_upwards [gt_mem_nhds hx'] with y hy
      simpa only [ite_eq_right hy.not_gt] using hlocal y hy.ne)
    simpa only [abs_of_neg hx', neg_div, div_self x.ne_zero, Complex.ofReal_neg,
      Complex.ofReal_one, neg_one_mul] using h

/-- On the two logarithmic profiles of the twist at exponent \(b\), the twist of the
ordinary derivative at exponent \(b+1\) acts by \(\pm(\partial_t-b)\). -/
private theorem iteratedDeriv_exponentialDecay_onTwist (b : ℝ) :
    ∃ T : SchwartzBruhat ℝˣ →L[ℂ] SchwartzBruhat ℝˣ, ∀ (f : ℝˣ → ℂ) (w : SchwartzBruhat ℝˣ),
      (∀ x, w x = ((|x.val| ^ b : ℝ) : ℂ) * f x) → ∀ x,
        T w x = ((|x.val| ^ (b + 1) : ℝ) : ℂ) * deriv zeroExtension(f) x.val := by
  refine iteratedDeriv_exponentialDecay_assemble.elim fun J hJ ↦ ?_
  refine (iteratedDeriv_exponentialDecay_slice 1).elim fun P hP ↦ ?_
  refine (iteratedDeriv_exponentialDecay_slice (-1)).elim fun N hN ↦ ?_
  let B := SchwartzMap.derivCLM ℂ ℂ - (b : ℂ) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)
  refine ⟨J.comp ((B.comp P).prod (-(B.comp N))), fun f w hw x ↦ ?_⟩
  have hchart (y : ℝˣ) :
      (if 0 < y.val then P w else N w) (Real.log y.val) = ((|y.val| ^ b : ℝ) : ℂ) * f y := by
    refine Eq.trans ?_ (hw y)
    split_ifs with hy
    · refine (hP w _).trans (congrArg w.val ?_)
      rw [one_mul]
      exact Units.ext (Real.exp_log hy)
    · refine (hN w _).trans (congrArg w.val ?_)
      apply Units.ext
      change -1 * Real.exp (Real.log y.val) = y.val
      rw [Real.exp_log_eq_abs y.ne_zero, abs_of_nonpos (le_of_not_gt hy), neg_one_mul, neg_neg]
  exact (hJ _ x).trans (iteratedDeriv_exponentialDecay_twistFormula f (P w, N w) b hchart x).symm

private theorem iteratedDeriv_exponentialDecay_weight (b : ℝ) (f : ℝˣ → ℂ) (x : ℝˣ) :
    modulationWeight (archimedeanUnitModulation ℝ 1) b f x = ((|x.val| ^ b : ℝ) : ℂ) * f x := by
  change (((((archimedeanUnitModulation ℝ 1 x).val : ℝ) ^ b : ℝ) : ℂ) * f x) = _
  rw [archimedeanUnitModulation_apply, pow_one, Real.norm_eq_abs]

/-- Construct the derivative by untwisting at one output exponent; the coordinate
identities at all exponents give both membership and continuity. -/
private theorem iteratedDeriv_exponentialDecay_step (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + 1)),
      ∀ f x, (D f).val x = deriv zeroExtension(f.val) x.val := by
  let n := archimedeanUnitModulation ℝ 1
  let I := Ioi a
  let J := Ioi (a + 1)
  let E := ModulatedExponentialDecay n I
  let d (f : E) (x : ℝˣ) := deriv zeroExtension(f.val) x.val
  have htwist (c : J) : ∃ U : E →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f, (U f).val = modulationWeight n c (d f) := by
    let b : I := ⟨c.val - 1, lt_sub_iff_add_lt.mpr c.property⟩
    let W : E →L[ℂ] SchwartzBruhat ℝˣ := ⟨modulatedExponentialDecayTwist n I b,
      (continuous_apply b).comp (iteratedDeriv_exponentialDecay_inducing I).continuous⟩
    refine (iteratedDeriv_exponentialDecay_onTwist b).elim fun T hT ↦ ?_
    refine ⟨T.comp W, fun f ↦ funext fun x ↦ ?_⟩
    have h := hT f.val (W f) (fun y ↦ iteratedDeriv_exponentialDecay_weight b f.val y) x
    refine h.trans ?_
    rw [show (b : ℝ) + 1 = c.val from sub_add_cancel _ _, iteratedDeriv_exponentialDecay_weight]
  let c₀ : J := ⟨a + 1 + 1, lt_add_one _⟩
  let U := (htwist c₀).choose
  let L : E →ₗ[ℂ] (ℝˣ → ℂ) := (modulationWeight n (-c₀.val)).comp
    ((schwartzBruhatSubmodule ℝˣ).subtype.comp U.toLinearMap)
  have hL (f : E) : L f = d f := by
    funext x
    change modulationWeight n (-c₀.val) (U f).val x = _
    rw [(htwist c₀).choose_spec f, iteratedDeriv_exponentialDecay_weight,
      iteratedDeriv_exponentialDecay_weight, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (abs_pos.mpr x.ne_zero), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n J) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (by
      change modulationWeight n c (L f) ∈ schwartzBruhatSubmodule ℝˣ
      rw [hL f, ← (htwist c).choose_spec f]
      exact ((htwist c).choose f).property)
  refine ⟨⟨D, (iteratedDeriv_exponentialDecay_inducing J).continuous_iff.mpr (continuous_pi fun c ↦ ?_)⟩, fun f ↦ congrFun (hL f)⟩
  exact (htwist c).choose.continuous.congr fun f ↦ Subtype.ext
    (((htwist c).choose_spec f).trans (congrArg (modulationWeight n c) (hL f).symm))

private theorem iteratedDeriv_exponentialDecay_succ (m : ℕ) (g : ℝˣ → ℂ) (F : ℝ → ℂ)
    (hg : ∀ x : ℝˣ, g x = iteratedDeriv m F x.val) (x : ℝˣ) :
    deriv zeroExtension(g) x.val = iteratedDeriv (m + 1) F x.val := by
  rw [iteratedDeriv_succ]
  apply EventuallyEq.deriv_eq
  filter_upwards [isOpen_compl_singleton.mem_nhds (show x.val ∈ ({0}ᶜ : Set ℝ) from x.ne_zero)] with y hy
  exact (dite_eq_left (show y ≠ 0 from hy)).trans (hg (Units.mk0 y hy))

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
An ordinary derivative of order m shifts the lower endpoint of the decay interval by m. -/
theorem iteratedDeriv_exponentialDecay (m : ℕ) (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + m)),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by
  let P (k : ℕ) (b : ℝ) := ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi b),
    ∀ f x, (D f).val x = iteratedDeriv k zeroExtension(f.val) x.val
  change P m (a + m)
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    refine ⟨ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
    change f.val x = iteratedDeriv 0 _ x.val
    simp only [iteratedDeriv_zero, dite_eq_left x.ne_zero]
    exact congrArg f.val (Units.ext rfl)
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    refine ih.elim fun A hA ↦ ?_
    refine (iteratedDeriv_exponentialDecay_step (a + m)).elim fun B hB ↦ ?_
    refine ⟨B.comp A, fun f x ↦ ?_⟩
    refine (hB (A f) x).trans ?_
    exact iteratedDeriv_exponentialDecay_succ m (A f).val zeroExtension(f.val) (hA f) x

/-- Every output weight of the derivative comes from the input weight one lower;
the initial topology of all twists makes this a continuous endomorphism. -/
private theorem iteratedDeriv_allExponentialDecay_step :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = deriv zeroExtension(f.val) x.val := by
  let n := archimedeanUnitModulation ℝ 1
  let I : Set ℝ := univ
  let J : Set ℝ := univ
  let E := ModulatedExponentialDecay n I
  let d (f : E) (x : ℝˣ) := deriv zeroExtension(f.val) x.val
  have htwist (c : J) : ∃ U : E →L[ℂ] SchwartzBruhat ℝˣ,
      ∀ f, (U f).val = modulationWeight n c (d f) := by
    let b : I := ⟨c.val - 1, mem_univ _⟩
    let W : E →L[ℂ] SchwartzBruhat ℝˣ := ⟨modulatedExponentialDecayTwist n I b,
      (continuous_apply b).comp (iteratedDeriv_exponentialDecay_inducing I).continuous⟩
    refine (iteratedDeriv_exponentialDecay_onTwist b).elim fun T hT ↦ ?_
    refine ⟨T.comp W, fun f ↦ funext fun x ↦ ?_⟩
    have h := hT f.val (W f) (fun y ↦ iteratedDeriv_exponentialDecay_weight b f.val y) x
    refine h.trans ?_
    rw [show (b : ℝ) + 1 = c.val from sub_add_cancel _ _, iteratedDeriv_exponentialDecay_weight]
  let c₀ : J := ⟨0, mem_univ _⟩
  let U := (htwist c₀).choose
  let L : E →ₗ[ℂ] (ℝˣ → ℂ) := (modulationWeight n (-c₀.val)).comp
    ((schwartzBruhatSubmodule ℝˣ).subtype.comp U.toLinearMap)
  have hL (f : E) : L f = d f := by
    funext x
    change modulationWeight n (-c₀.val) (U f).val x = _
    rw [(htwist c₀).choose_spec f, iteratedDeriv_exponentialDecay_weight,
      iteratedDeriv_exponentialDecay_weight, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_add (abs_pos.mpr x.ne_zero), neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n J) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (by
      change modulationWeight n c (L f) ∈ schwartzBruhatSubmodule ℝˣ
      rw [hL f, ← (htwist c).choose_spec f]
      exact ((htwist c).choose f).property)
  refine ⟨⟨D, (iteratedDeriv_exponentialDecay_inducing J).continuous_iff.mpr (continuous_pi fun c ↦ ?_)⟩, fun f ↦ congrFun (hL f)⟩
  exact (htwist c).choose.continuous.congr fun f ↦ Subtype.ext
    (((htwist c).choose_spec f).trans (congrArg (modulationWeight n c) (hL f).symm))

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Ordinary derivatives act continuously on the punctured real space with decay at all exponents. -/
theorem iteratedDeriv_allExponentialDecay (m : ℕ) :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by
  induction m with
  | zero =>
    refine ⟨ContinuousLinearMap.id ℂ _, fun f x ↦ ?_⟩
    change f.val x = iteratedDeriv 0 _ x.val
    simp only [iteratedDeriv_zero, dite_eq_left x.ne_zero]
    exact congrArg f.val (Units.ext rfl)
  | succ m ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨B, hB⟩ := iteratedDeriv_allExponentialDecay_step
    refine ⟨B.comp A, fun f x ↦ ?_⟩
    exact (hB (A f) x).trans
      (iteratedDeriv_exponentialDecay_succ m (A f).val zeroExtension(f.val) (hA f) x)

namespace IteratedWirtinger

open Complex
open scoped ENNReal

/-- Resolve a real-linear differential in the frame tangent to dilation and rotation. -/
private theorem frame (L : ℂ →L[ℝ] ℂ) (z : ℂ) (s : Bool) :
    L z + (if s then I else -I) * L (z * I) =
      (if s then star z else z) * (L 1 + (if s then I else -I) * L I) := by
  have expand (w : ℂ) : L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L I := by
    have hw : w = w.re • (1 : ℂ) + w.im • I := by
      simp [Complex.real_smul]
    conv_lhs => rw [hw, map_add, map_smul, map_smul]
    simp [Complex.real_smul]
  rw [expand z, expand (z * I)]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_I_re, mul_I_im, ofReal_neg]
  · conv_rhs => lhs; rw [← re_add_im z]
    linear_combination ((z.im : ℂ) * L I) * I_sq
  · conv_rhs => lhs; rw [← re_add_im z]
    simp only [Complex.star_def, map_add, map_mul, conj_ofReal, conj_I]
    linear_combination ((z.im : ℂ) * L I) * I_sq

/-- Differentiate a weighted dilation or rotation orbit at time zero. -/
private theorem orbit (F : ℂ → ℂ) (z v : ℂ) (a : ℝ) (q : ℂ)
    (hF : DifferentiableAt ℝ F z) :
    deriv (fun t : ℝ ↦ q * (Real.exp (a * t) : ℂ) * F (z * exp ((t : ℂ) * v))) 0 =
      q * (a * F z + fderiv ℝ F z (z * v)) := by
  have hpath : HasDerivAt (fun t : ℝ ↦ z * exp ((t : ℂ) * v)) (z * v) 0 := by
    simpa using (((ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const v).cexp.const_mul z)
  have hf' : HasFDerivAt F (fderiv ℝ F z) (z * exp (((0 : ℝ) : ℂ) * v)) := by
    simpa using hF.hasFDerivAt
  have hf := hf'.comp_hasDerivAt (0 : ℝ) hpath
  have hw := (((hasDerivAt_id (0 : ℝ)).const_mul a).exp.ofReal_comp).const_mul q
  exact (hw.mul hf).deriv.trans (by simp [mul_add, mul_assoc])

/-- The weighted radial and angular generators recover both first Wirtinger derivatives.
Here b is the input exponent and q is the corresponding weight at z. -/
private theorem weightedFrame (s : Bool) (b : ℝ) (F : ℂ → ℂ) (z : ℂ)
    (hF : DifferentiableAt ℝ F z) :
    let q : ℂ := (((‖z‖ ^ 2 : ℝ) ^ b : ℝ) : ℂ)
    let radial := deriv (fun t : ℝ ↦ q * (Real.exp (2 * b * t) : ℂ) *
      F (z * exp (t : ℂ))) 0
    let angular := deriv (fun t : ℝ ↦ q * F (z * exp ((t : ℂ) * I))) 0
    radial + (if s then I else -I) * angular - 2 * b * q * F z =
      2 * q * (if s then star z else z) *
        (if s then wirtingerConjDeriv else wirtingerDeriv) F z := by
  dsimp only
  generalize ((‖z‖ ^ 2 : ℝ) ^ b : ℝ) = w
  have hr := orbit F z 1 (2*b) w hF
  have ha := orbit F z I 0 w hF
  simp only [mul_one, ofReal_mul, ofReal_ofNat] at hr
  simp only [zero_mul, Real.exp_zero, ofReal_one, mul_one, ofReal_zero, zero_add] at ha
  rw [hr, ha]
  have h := frame (fderiv ℝ F z) z s
  cases s <;> simp [wirtingerDeriv, wirtingerConjDeriv] at h ⊢ <;> linear_combination (w : ℂ) * h

private def twist (b : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (((‖z‖ ^ 2 : ℝ) ^ b : ℝ) : ℂ) * F z

/-- Multiplying by the unit phase r/z (or r/conj z) changes the input exponent
b into the output exponent b + 1/2. The two derivatives act on the same twisted function. -/
private theorem shifted (s : Bool) (b : ℝ) (F : ℂ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (hF : DifferentiableAt ℝ F z) :
    twist (b + 1/2) ((if s then wirtingerConjDeriv else wirtingerDeriv) F) z =
      (‖z‖ : ℂ) / (if s then star z else z) / 2 *
      (deriv (fun t : ℝ ↦ twist b F (z * exp (t : ℂ))) 0 +
        (if s then I else -I) * deriv (fun t : ℝ ↦ twist b F (z * exp ((t : ℂ) * I))) 0 -
        2 * b * twist b F z) := by
  have hr (t : ℝ) : (‖z * exp (t : ℂ)‖ ^ 2 : ℝ) ^ b =
      (‖z‖ ^ 2 : ℝ) ^ b * Real.exp (2 * b * t) := by
    rw [norm_mul, Complex.norm_exp, ofReal_re, mul_pow, Real.mul_rpow (sq_nonneg _) (sq_nonneg _)]
    congr 1
    rw [sq, ← Real.exp_add, ← Real.exp_mul]
    congr 1
    ring
  have ha (t : ℝ) : ‖z * exp ((t : ℂ) * I)‖ = ‖z‖ := by simp
  have h := weightedFrame s b F z hF
  dsimp only at h
  unfold twist
  simp_rw [hr, ha, ofReal_mul]
  rw [show 2 * (b : ℂ) * ((((‖z‖ ^ 2 : ℝ) ^ b : ℝ) : ℂ) * F z) =
      2 * b * ((((‖z‖ ^ 2 : ℝ) ^ b : ℝ) : ℂ)) * F z by ring, h]
  have hhalf : (‖z‖ ^ 2 : ℝ) ^ (1/2 : ℝ) = ‖z‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [Real.rpow_add (sq_pos_of_pos (norm_pos_iff.mpr hz)), hhalf, ofReal_mul]
  have hd : (if s then star z else z) ≠ 0 := by cases s <;> simpa using hz
  field_simp

private def flow (v : ℂ) : LCATopologicalLie ℂˣ where
  toFun t := Units.mk0 (exp ((t.toAdd : ℂ) * v)) (exp_ne_zero _)
  map_one' := Units.ext (by change exp (((0 : ℝ) : ℂ) * v) = 1; simp)
  map_mul' t u := Units.ext (by change exp (((t.toAdd + u.toAdd : ℝ) : ℂ) * v) = _; rw [ofReal_add, add_mul, exp_add]; rfl)
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
    (Complex.continuous_exp.comp ((continuous_ofReal.comp
      (continuous_id : Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ))).mul continuous_const))

private def extZero (f : 𝓔(ℂ, 2, univ)) (z : ℂ) := if h : z ≠ 0 then f.val (Units.mk0 z h) else 0
private theorem ext_unit (f : 𝓔(ℂ, 2, univ)) (u : ℂˣ) : extZero f u.val = f.val u := by
  simp [extZero, u.ne_zero]

/-- Combine a phase multiplier and differentiability on the punctured plane with the two orbit operators. -/
private theorem onWeightIn {S : Set ℝ}
    (hreg : ∀ (f : 𝓔(ℂ, 2, S)) (z : ℂˣ), DifferentiableAt ℝ zeroExtension(f.val) z.val)
    (s : Bool) (c : ℝ) (hc : c - 1/2 ∈ S) (M : SchwartzBruhat ℂˣ →L[ℂ] SchwartzBruhat ℂˣ)
    (hM : ∀ (g : SchwartzBruhat ℂˣ) (z : ℂˣ), M g z =
      ((‖z.val‖ : ℝ) : ℂ) / (if s then star z.val else z.val) * g z) :
    ∃ U : 𝓔(ℂ, 2, S) →L[ℂ] SchwartzBruhat ℂˣ, ∀ f (z : ℂˣ),
      U f z = twist c ((if s then wirtingerConjDeriv else wirtingerDeriv) zeroExtension(f.val)) z.val := by
  let b := c - 1/2
  let n := archimedeanUnitModulation ℂ 2
  let W : 𝓔(ℂ, 2, S) →L[ℂ] SchwartzBruhat ℂˣ :=
    ⟨modulatedExponentialDecayTwist n S ⟨b, hc⟩, continuous_decay_twist n S _⟩
  have hw (f : 𝓔(ℂ, 2, S)) (z : ℂˣ) : W f z = twist b zeroExtension(f.val) z.val := by
    change (((((archimedeanUnitModulation ℂ 2 z).val : ℝ) ^ b : ℝ) : ℂ) * f.val z) = _
    rw [archimedeanUnitModulation_apply, twist, dite_eq_left z.ne_zero, show Units.mk0 z.val z.ne_zero = z from Units.ext rfl]
  obtain ⟨R,hR⟩ := bruhatFirstOrder_schwartz (flow 1)
  obtain ⟨A,hA⟩ := bruhatFirstOrder_schwartz (flow I)
  let B := R + (if s then I else -I) • A - (2 * (b : ℂ)) • ContinuousLinearMap.id ℂ _
  refine ⟨((1/2 : ℂ) • M).comp (B.comp W), fun f z ↦ ?_⟩
  have hd := hreg f z
  have horbit (v : ℂ) : bruhatDirectionalDeriv (flow v) (W f) z =
      deriv (fun t : ℝ ↦ twist b zeroExtension(f.val) (z.val * exp ((t : ℂ) * v))) 0 := by
    unfold bruhatDirectionalDeriv
    congr 1
    funext t
    exact hw f _
  change (1/2 : ℂ) * M (B (W f)) z = _
  rw [hM]
  change _ * (_ * (R (W f) z + _ * A (W f) z - (2 * (b : ℂ)) * W f z)) = _
  rw [hR, hA, horbit, horbit, hw]
  have h := shifted s b zeroExtension(f.val) z.val z.ne_zero hd
  rw [show b + 1/2 = c by dsimp [b]; ring] at h
  simp only [mul_one] at *
  rw [h]
  ring

/-- Specialize the input twist to the space of all exponents. -/
private theorem onWeight
    (hreg : ∀ (f : 𝓔(ℂ, 2, univ)) (z : ℂˣ), DifferentiableAt ℝ (extZero f) z.val)
    (s : Bool) (c : ℝ) (M : SchwartzBruhat ℂˣ →L[ℂ] SchwartzBruhat ℂˣ)
    (hM : ∀ (g : SchwartzBruhat ℂˣ) (z : ℂˣ), M g z =
      ((‖z.val‖ : ℝ) : ℂ) / (if s then star z.val else z.val) * g z) :
    ∃ U : 𝓔(ℂ, 2, univ) →L[ℂ] SchwartzBruhat ℂˣ, ∀ f (z : ℂˣ),
      U f z = twist c ((if s then wirtingerConjDeriv else wirtingerDeriv) (extZero f)) z.val :=
  onWeightIn hreg s c (mem_univ _) M hM

private def phase (s : Bool) : PontryaginDual ℂˣ where
  toFun z := ⟨(‖z.val‖ : ℂ) / (if s then star z.val else z.val), by
    change ‖_‖ = 1
    cases s <;> simp [z.ne_zero]⟩
  map_one' := by apply Subtype.ext; cases s <;> simp
  map_mul' z w := by apply Subtype.ext; cases s <;> simp <;> exact (div_mul_div_comm _ _ _ _).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    cases s <;> dsimp <;> fun_prop (disch := simp)

/-- On every discrete fibre, translating the vector cover scales a character by a
unit scalar. All derivative norms are therefore constant across that cover. -/
private theorem elementaryPhaseMem {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (χ : PontryaginDual (Multiplicative (ElementaryLieGroup m n r F)))
    (s : ElementarySchwartz m n r F) :
    (fun y ↦ (χ (Multiplicative.ofAdd y) : ℂ) * s y) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let g (a : Fin r → ℤ) (b : F) (x : X) := (χ (Multiplicative.ofAdd (elementaryCover x a b)) : ℂ)
  have hg (a b) : ContDiff ℝ (∞ : ℕ∞ω) (g a b) := contDiff_elementary_character χ a b
  have hnorm (k : ℕ) (a b) (x : X) :
      ‖iteratedFDeriv ℝ k (g a b) x‖ = ‖iteratedFDeriv ℝ k (g 0 0) 0‖ := by
    have hshift : (fun t ↦ g a b (x + t)) = g a b x • g 0 0 := by
      funext t
      change (χ (Multiplicative.ofAdd _) : ℂ) = _ * _
      rw [← Circle.coe_mul, ← map_mul]
      apply congrArg (fun w ↦ (χ (Multiplicative.ofAdd w) : ℂ))
      simp [elementaryCover, Pi.zero_def, Pi.add_def]
      exact ⟨rfl, funext fun i ↦ AddCircle.coe_add _ _ _⟩
    have h := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := g a b) k x 0
    rw [add_zero, hshift, iteratedFDeriv_const_smul_apply ((hg 0 0).of_le (by simp)).contDiffAt] at h
    rw [← h, norm_smul]
    simp [g]
  refine ⟨fun a b ↦ (hg a b).mul (s.property.1 a b), fun i ↦ ?_⟩
  obtain ⟨α, β, γ, δ⟩ := i
  let D (β : Fin m → ℕ) (γ : Fin n → ℕ) : List X :=
    (List.ofFn (fun i : Fin m ↦ List.replicate (β i)
      ((EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin m)), (0 : EuclideanSpace ℝ (Fin n))))).flatten ++
    (List.ofFn (fun i : Fin n ↦ List.replicate (γ i)
      ((0 : EuclideanSpace ℝ (Fin m)), (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin n))))).flatten
  have hpartial (f : ElementaryLieGroup m n r F → ℂ) (β : Fin m → ℕ) (γ : Fin n → ℕ) (xt : X)
      (a : Fin r → ℤ) (b : F) : elementaryPartial f β γ xt a b =
        iteratedFDeriv ℝ (D β γ).length (fun v ↦ f (elementaryCover v a b)) xt (D β γ).get := rfl
  have hsub (L' : List X) (h : List.Sublist L' (D β γ)) : ∃ β' γ', L' = D β' γ' := by
    obtain ⟨r₁, r₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
    obtain ⟨β', rfl⟩ := sublist_flatten_ofFn_replicate _ _ h₁
    obtain ⟨γ', rfl⟩ := sublist_flatten_ofFn_replicate _ _ h₂
    exact ⟨β', γ', rfl⟩
  let mono (xt : X) (a : Fin r → ℤ) : ℂ :=
    (∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)
  let T (L' : List X) : ℝ≥0∞ := ⨆ (xt : X) (a : Fin r → ℤ) (b : F),
    (‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖₊ : ℝ≥0∞)
  have hT (L' : List X) (h : L' ∈ (D β γ).sublists) : T L' < ⊤ := by
    obtain ⟨β', γ', rfl⟩ := hsub L' (List.mem_sublists.mp h)
    exact s.property.2 (α, β', γ', δ)
  have hTle (L' : List X) (h : L' ∈ (D β γ).sublists) (xt : X) (a : Fin r → ℤ) (b : F) :
      ‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖ ≤
        (T L').toReal := by
    have := ENNReal.toReal_mono (hT L' h).ne
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)) :
        (‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖₊ :
          ℝ≥0∞) ≤ T L')
    simpa using this
  let N := (D β γ).length
  let Cψ := ∑ k ∈ Finset.range (N + 1), ‖iteratedFDeriv ℝ k (g 0 0) 0‖
  have hCψ (a b xt) (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (g a b) xt‖ ≤ Cψ := by
    rw [hnorm]
    exact Finset.single_le_sum (f := fun j ↦ ‖iteratedFDeriv ℝ j (g 0 0) 0‖)
      (fun _ _ ↦ norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  let Pr := ((D β γ).map fun v ↦ 1 + ‖v‖).prod
  have hPr : 0 ≤ Pr := List.prod_nonneg (by simp; intro a _; positivity)
  have hCψ0 : 0 ≤ Cψ := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  let K := Cψ * Pr * ((D β γ).sublists.map fun L' ↦ (T L').toReal).sum
  refine lt_of_le_of_lt (?_ : _ ≤ ENNReal.ofReal K) ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
  apply ENNReal.ofReal_le_ofReal
  change ‖mono xt a * elementaryPartial (fun y ↦ (χ (Multiplicative.ofAdd y) : ℂ) * s y) β γ xt a b‖ ≤ K
  rw [hpartial]
  change ‖mono xt a * iteratedFDeriv ℝ (D β γ).length
    (fun xt ↦ g a b xt * s (elementaryCover xt a b)) xt (D β γ).get‖ ≤ K
  rw [norm_mul]
  have hL := norm_iteratedFDeriv_list_mul_le (D β γ) _ _ (hg a b) (s.property.1 a b)
    xt Cψ (hCψ a b xt)
  calc _ ≤ ‖mono xt a‖ * (Cψ * Pr * ((D β γ).sublists.map fun L' ↦
        ‖iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖).sum) :=
        mul_le_mul_of_nonneg_left hL (norm_nonneg _)
    _ = Cψ * Pr * ((D β γ).sublists.map fun L' ↦
        ‖mono xt a * iteratedFDeriv ℝ L'.length (fun v ↦ s (elementaryCover v a b)) xt L'.get‖).sum := by
        rw [mul_left_comm, ← List.sum_map_mul_left]
        simp only [norm_mul]
    _ ≤ K := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCψ0 hPr)
        exact List.sum_le_sum fun L' h ↦ hTle L' h xt a b


private theorem maxEquiv {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] (a : BruhatStructuralPair G)
    (d : ElementaryLCAPresentation a.quotient) (hmax : ∀ b, b ≤ a) :
    ∃ j : SchwartzBruhatStage d ≃L[ℂ] SchwartzBruhat G, ∀ g, j g = schwartzBruhatStageInclusion a d g := by
  let J := schwartzBruhatStageCLM a d
  have hsur : Surjective J := by
    intro f
    have hle : schwartzBruhatSubmodule G ≤ (schwartzBruhatStageRealization a d).range :=
      iSup_le fun b ↦ iSup_le fun p ↦ fun _ ⟨g,hg⟩ ↦ hg ▸ kernelStage_realization_mono (hmax b) p d g
    obtain ⟨g,hg⟩ := hle (show f.val ∈ schwartzBruhatSubmodule G from f.property)
    exact ⟨g, Subtype.ext hg⟩
  let j := LinearEquiv.ofBijective J.toLinearMap ⟨schwartzBruhatStageInclusion_injective a d, hsur⟩
  let _ := d.finiteGroup
  let _ := d.finiteTopology
  let _ := d.finiteDiscrete
  let _ := d.finiteFintype
  have hj : Continuous j.symm := by
    apply elementarySchwartz_withSeminorms.continuous_of_continuous_comp j.symm.toLinearMap
    intro i
    let q := (elementarySchwartzSeminorm i).comp j.symm.toLinearMap
    apply (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm
      (⟨q, ?_⟩ : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
        ∀ b p', Continuous (p ∘ schwartzBruhatStageInclusion b p')})
    intro b p
    obtain ⟨T,hT⟩ := kernelStage_transitionMap (hmax b) p d
    apply ((elementarySchwartz_withSeminorms.continuous_seminorm i).comp T.continuous).congr
    intro g
    apply congrArg (elementarySchwartzSeminorm i)
    apply j.injective
    exact (Subtype.ext (hT g)).trans (j.apply_symm_apply _).symm
  exact ⟨⟨j,J.continuous,hj⟩, fun _ ↦ rfl⟩

/-- The whole punctured plane with trivial stage kernel gives one elementary model
for every Schwartz–Bruhat function. Continuity of the inverse is tested on stages. -/
private theorem wholeChart :
    ∃ (e : ElementaryLCAPresentation ℂˣ)
      (J : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat ℂˣ),
      ∀ g z, J g z = g (e.equiv z).toAdd := by
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm := complexCoordinate_mul_allExponentialDecay_modulation
  have hG := compactlyGenerated_of_surjective_modulation _ hm.1 hm.2
  let iso := (stdOrthonormalBasis ℝ ℂ).repr
  have hk : IsBruhatGoodSubgroup (⊥ : Subgroup ℂˣ) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨_, ⟨(iso.toHomeomorph.isOpenEmbedding.comp
      (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩
  let a := fullBruhatStage hG hk
  let d := a.elementary.some
  obtain ⟨w,hw⟩ := fullBruhatStage_quotientEquiv hG hk (MonoidHom.id ℂˣ) IsOpenQuotientMap.id (by simp)
  let e : ElementaryLCAPresentation ℂˣ := {d with equiv := w.symm.trans d.equiv}
  have hmax (b : BruhatStructuralPair ℂˣ) : b ≤ a := ⟨le_top, (bot_le : (⊥ : Subgroup ℂˣ) ≤ OrderDual.ofDual b.val.2)⟩
  obtain ⟨j,hj⟩ := maxEquiv a d hmax
  refine ⟨e, j, fun g z ↦ ?_⟩
  rw [hj]
  change schwartzBruhatStageRealization a d g z = _
  rw [schwartzBruhatStageRealization_apply, dite_eq_left (show z ∈ a.val.1 from Subgroup.mem_top z)]
  exact congrArg (fun t ↦ g (d.equiv t).toAdd) (w.symm_apply_eq.mpr (hw z).symm).symm

private theorem phaseMultiplier (s : Bool) :
    ∃ M : SchwartzBruhat ℂˣ →L[ℂ] SchwartzBruhat ℂˣ,
      ∀ f z, M f z = (phase s z : ℂ) * f z := by
  obtain ⟨e,J,hJ⟩ := wholeChart
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let χ := (phase s).comp ⟨e.equiv.symm.toMulEquiv.toMonoidHom, e.equiv.symm.continuous⟩
  let X := SchwartzBruhatStage e
  let M : X →ₗ[ℂ] X :=
    { toFun := fun f ↦ ⟨_, elementaryPhaseMem χ f⟩
      map_add' := fun f g ↦ Subtype.ext (funext fun y ↦ mul_add _ _ _)
      map_smul' := fun c f ↦ Subtype.ext (funext fun y ↦ mul_left_comm _ _ _) }
  let : BarrelledSpace ℂ X := isFrechetTVS_barrelled elementarySchwartz_isFrechet
  let : ContinuousSMul ℂ X := elementarySchwartz_withSeminorms.continuousSMul
  have hc : Continuous M := by
    apply continuous_toElementarySchwartz_of_eval
    intro y
    obtain ⟨ev,hev⟩ := elementarySchwartz_eval_continuousLinear (F := e.finiteFactor) y
    exact ⟨(χ (Multiplicative.ofAdd y) : ℂ) • ev, fun f ↦ congrArg (_ * ·) (hev f)⟩
  refine ⟨J.toContinuousLinearMap.comp ((⟨M,hc⟩ : X →L[ℂ] X).comp J.symm.toContinuousLinearMap), fun f z ↦ ?_⟩
  change J (M (J.symm f)) z = _
  rw [hJ]
  change (phase s (e.equiv.symm (e.equiv z)) : ℂ) * (J.symm f) _ = _
  rw [e.equiv.symm_apply_apply, ← hJ, J.apply_symm_apply]


private def expUnits : Multiplicative ℂ →ₜ* ℂˣ where
  toFun v := Units.mk0 (exp v.toAdd) (exp_ne_zero _)
  map_one' := Units.ext exp_zero
  map_mul' x y := Units.ext (exp_add x.toAdd y.toAdd)
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr continuous_exp

/-- Around z, use log(y/z) to lift a punctured-plane argument to the vector cover. -/
private theorem chartDifferentiable (f : 𝓔(ℂ, 2, univ)) (z : ℂˣ) : DifferentiableAt ℝ (extZero f) z.val := by
  obtain ⟨e,J,hJ⟩ := wholeChart
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  let w := modulatedExponentialDecayTwist (archimedeanUnitModulation ℂ 2) Set.univ
    ⟨0, Set.mem_univ _⟩ f
  have hw (u : ℂˣ) : w u = f.val u := by
    change (((((archimedeanUnitModulation ℂ 2 u).val : ℝ) ^ (0 : ℝ) : ℝ) : ℂ) * f.val u) = _
    simp
  let g := J.symm w
  let a := AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp expUnits.toMonoidHom)
  have ha : Continuous a := e.equiv.continuous.comp expUnits.continuous
  have h := contDiff_comp_affine_elementary a ha (e.equiv z).toAdd (f := g.val) g.property.1
  have hlog : DifferentiableAt ℝ (fun y : ℂ ↦ log (y / z.val)) z.val := by
    apply DifferentiableAt.comp (g := log) (f := fun y : ℂ ↦ y / z.val)
    · exact (differentiableAt_log (z := z.val / z.val) (by simp [z.ne_zero])).restrictScalars ℝ
    · exact ((differentiableAt_id (𝕜 := ℂ) (x := z.val)).div_const z.val).restrictScalars ℝ
  apply (h.differentiable (by decide) _ |>.comp z.val hlog).congr_of_eventuallyEq
  filter_upwards [isOpen_compl_singleton.mem_nhds (show z.val ∈ ({0}ᶜ : Set ℂ) from z.ne_zero)] with y hy
  have hy' : y ≠ 0 := hy
  let u := Units.mk0 y hy'
  have hu : expUnits (Multiplicative.ofAdd (log (y / z.val))) * z = u := by
    apply Units.ext
    change exp (log (y / z.val)) * z.val = y
    rw [exp_log (div_ne_zero hy' z.ne_zero), div_mul_cancel₀ _ z.ne_zero]
  change extZero f u.val = g (a (log (y / z.val)) + (e.equiv z).toAdd)
  rw [ext_unit, ← hw, ← J.apply_symm_apply w, hJ]
  apply congrArg g.val
  rw [← hu, map_mul]
  rfl

/-- Both first derivatives, at each output weight, as continuous maps to Schwartz–Bruhat space. -/
private theorem firstTwist (s : Bool) (c : ℝ) :
    ∃ U : 𝓔(ℂ, 2, univ) →L[ℂ] SchwartzBruhat ℂˣ, ∀ f (z : ℂˣ),
      U f z = twist c ((if s then wirtingerConjDeriv else wirtingerDeriv) (extZero f)) z.val := by
  obtain ⟨M,hM⟩ := phaseMultiplier s
  exact onWeight chartDifferentiable s c M hM

/-- The output at weight zero gives the underlying function. The output at each
other weight proves membership and continuity in the all-exponent space. -/
private theorem firstEndomorphism (s : Bool) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ), ∀ f (z : ℂˣ),
      (D f).val z = (if s then wirtingerConjDeriv else wirtingerDeriv) (extZero f) z.val := by
  let n := archimedeanUnitModulation ℂ 2
  let I : Set ℝ := univ
  let U (c : ℝ) := (firstTwist s c).choose
  let L := (schwartzBruhatSubmodule ℂˣ).subtype.comp (U 0).toLinearMap
  have hL (f : 𝓔(ℂ, 2, univ)) (z : ℂˣ) : L f z =
      (if s then wirtingerConjDeriv else wirtingerDeriv) (extZero f) z.val := by
    change (U 0 f).val z = _
    simpa [U,twist] using (firstTwist s 0).choose_spec f z
  have hw (c : I) (f : 𝓔(ℂ, 2, univ)) : modulationWeight n c (L f) = (U c f).val := by
    funext z
    change (((((archimedeanUnitModulation ℂ 2 z).val : ℝ) ^ (c : ℝ) : ℝ) : ℂ) * L f z) = _
    rw [archimedeanUnitModulation_apply, hL, (firstTwist s c).choose_spec f z]
    rfl
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n I) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (hw c f ▸ (U c f).property)
  let iso := (stdOrthonormalBasis ℝ ℂ).repr
  have hk : IsBruhatGoodSubgroup (⊥ : Subgroup ℂˣ) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨_, ⟨(iso.toHomeomorph.isOpenEmbedding.comp
      (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩
  have hi := iteratedDeriv_exponentialDecay_inducing_of_bot n I hk.2.2
  refine ⟨⟨D, hi.continuous_iff.mpr (continuous_pi fun c ↦ ?_)⟩, hL⟩
  exact (U c).continuous.congr fun f ↦ Subtype.ext (hw c f).symm

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250. Both iterated derivatives act
continuously on the all-exponent decay space. -/
private theorem iterated (s : Bool) (m : ℕ) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ), ∀ f (z : ℂˣ), (D f).val z =
      ((if s then wirtingerConjDeriv else wirtingerDeriv)^[m] (extZero f)) z.val := by
  let W := if s then wirtingerConjDeriv else wirtingerDeriv
  induction m with
  | zero => exact ⟨ContinuousLinearMap.id ℂ _, fun f z ↦ (ext_unit f z).symm⟩
  | succ m ih =>
    obtain ⟨A,hA⟩ := ih
    obtain ⟨B,hB⟩ := firstEndomorphism s
    refine ⟨B.comp A, fun f z ↦ (hB (A f) z).trans ?_⟩
    change W (extZero (A f)) z.val = (W^[m+1] (extZero f)) z.val
    rw [Function.iterate_succ_apply']
    have he : extZero (A f) =ᶠ[𝓝 z.val] W^[m] (extZero f) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (show z.val ∈ ({0}ᶜ : Set ℂ) from z.ne_zero)] with y hy
      let u := Units.mk0 y (show y ≠ 0 from hy)
      exact (ext_unit (A f) u).trans (hA f u)
    have hd := he.fderiv_eq (𝕜 := ℝ)
    cases s <;> simp [W, wirtingerConjDeriv, wirtingerDeriv] at hd ⊢ <;> rw [hd]

end IteratedWirtinger

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both iterated Wirtinger operators preserve the punctured complex space with decay at all
exponents and act continuously there. -/
theorem iteratedWirtinger_allExponentialDecay (conjugate : Bool) (m : ℕ) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val :=
  IteratedWirtinger.iterated conjugate m

/-- In exponential coordinates, the realization of a Schwartz–Bruhat stage is
smooth along every translate of a continuous homomorphism from a real vector space. -/
private theorem complexExponentialDecay_contDiffOn_alongTranslate {K G : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (U : Multiplicative K →ₜ* G) (f : SchwartzBruhat G) (u : G) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun t : K ↦ f (U (Multiplicative.ofAdd t) * u)) := by
  obtain ⟨p, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let H := p.val.1
  have hU : Continuous (fun t : K ↦ U (Multiplicative.ofAdd t)) := U.continuous
  have hpre : IsClopen ((fun t : K ↦ U (Multiplicative.ofAdd t)) ⁻¹' (H : Set G)) :=
    (show IsClopen (H : Set G) from ⟨H.isClosed_of_isOpen p.property.1, p.property.1⟩).preimage hU
  have hfull := hpre.eq_univ ⟨0, by change U 1 ∈ H; simp⟩
  have hmem (t : Multiplicative K) : U t ∈ H := by
    change t.toAdd ∈ (fun v : K ↦ U (Multiplicative.ofAdd v)) ⁻¹' (H : Set G)
    rw [hfull]
    exact mem_univ _
  let UH : Multiplicative K →* H := U.toMonoidHom.codRestrict H hmem
  by_cases hu : u ∈ H
  · let q : H →* p.quotient := QuotientGroup.mk' _
    let a := AddMonoidHom.toMultiplicative.symm
      (e.equiv.toMulEquiv.toMonoidHom.comp (q.comp UH))
    let c := Multiplicative.toAdd (e.equiv (q ⟨u, hu⟩))
    have ha : Continuous a := e.equiv.continuous.comp
      (QuotientGroup.continuous_mk.comp (hU.subtype_mk _))
    have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = s (a t + c) := by
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_left (H.mul_mem (hmem _) hu)]
      change s (Multiplicative.toAdd (e.equiv (q (UH (Multiplicative.ofAdd t) * ⟨u, hu⟩)))) = _
      rw [map_mul, map_mul]
      rfl
    rw [funext heq]
    exact contDiff_comp_affine_elementary a ha c s.property.1
  · have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = 0 := by
      have hnot : U (Multiplicative.ofAdd t) * u ∉ H := by
        intro h
        exact hu (H.mul_mem_cancel_left (hmem _) |>.mp h)
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_right hnot]
    rw [funext heq]
    exact contDiff_const

/-- The local inverse of the Banach-algebra exponential transfers smoothness in
multiplicative coordinates to smoothness in the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_unitsChart {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K] (f : SchwartzBruhat Kˣ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let +nondep : NormedAlgebra ℚ K := .restrictScalars ℚ ℝ K
  let U : Multiplicative K →ₜ* Kˣ :=
    { toFun := fun v ↦ ⟨NormedSpace.exp v.toAdd, NormedSpace.exp (-v.toAdd),
        by rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero],
        by rw [← NormedSpace.exp_add, neg_add_cancel, NormedSpace.exp_zero]⟩
      map_one' := Units.ext NormedSpace.exp_zero
      map_mul' := fun x y ↦ Units.ext NormedSpace.exp_add
      continuous_toFun := Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
        ((show Continuous (NormedSpace.exp : K → K) from NormedSpace.exp_continuous).comp
          (show Continuous (Multiplicative.toAdd : Multiplicative K → K) from continuous_id)) }
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  have hExp : ContDiffAt ℝ (∞ : ℕ∞ω) (NormedSpace.exp : K → K) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (x := (0 : K))).contDiffAt
  let L := ContinuousLinearEquiv.refl ℝ K
  have hD : HasFDerivAt NormedSpace.exp (L : K →L[ℝ] K) 0 := hasFDerivAt_exp_zero
  let log := hExp.localInverse (f' := L) hD (by simp)
  have hlog : ContDiffAt ℝ (∞ : ℕ∞ω) log 1 := by
    simpa only [NormedSpace.exp_zero] using hExp.to_localInverse (f' := L) hD (by simp)
  have hright : ∀ᶠ y : K in 𝓝 1, NormedSpace.exp (log y) = y := by
    unfold log ContDiffAt.localInverse
    simpa only [NormedSpace.exp_zero] using
      (hExp.hasStrictFDerivAt (f' := L) hD (by simp)).eventually_right_inverse
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  have hp : ContDiff ℝ (∞ : ℕ∞ω) (fun y : K ↦ y / x) := contDiff_id.div_const x
  have hp0 : x / x = 1 := div_self hx0
  have hlogx : ContDiffAt ℝ (∞ : ℕ∞ω) log (x / x) := by rw [hp0]; exact hlog
  have hg := complexExponentialDecay_contDiffOn_alongTranslate U f u
  have hc : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun y : K ↦ f (U (Multiplicative.ofAdd (log (y / x))) * u)) x :=
    hg.contDiffAt.comp x (hlogx.comp (f := fun y : K ↦ y / x) (g := log) x hp.contDiffAt)
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  have hnear : Tendsto (fun y : K ↦ y / x) (𝓝 x) (𝓝 1) :=
    hp0 ▸ hp.continuous.continuousAt
  filter_upwards [hnear.eventually hright, isOpen_compl_singleton.mem_nhds hx] with y hy hy0
  have hunit : U (Multiplicative.ofAdd (log (y / x))) * u = Units.mk0 y hy0 := by
    apply Units.ext
    change NormedSpace.exp (log (y / x)) * x = y
    rw [hy, div_mul_cancel₀ _ hx0]
  have hy0' : y ≠ 0 := hy0
  simp only [hunit, dite_eq_left hy0']

/-- Dividing a positive weighted Schwartz–Bruhat twist by its smooth nonzero
weight recovers the original function on the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_of_weightIn {S : Set ℝ} {K : Type*} [NormedField K]
    [NormedAlgebra ℝ K] [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K]
    (m : Kˣ →ₜ* ℝ≥0ˣ) (a : ℝ) (ha : a ∈ S)
    (f : ModulatedExponentialDecay m S)
    (w : K → ℂ) (hw : ContDiff ℝ (∞ : ℕ∞ω) w)
    (hwu : ∀ u : Kˣ, w u.val = (((m u).val : ℝ) ^ a : ℝ)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let g := modulatedExponentialDecayTwist m S ⟨a, ha⟩ f
  have hn (x : K) (hx : x ≠ 0) : w x ≠ 0 := by
    change w (Units.mk0 x hx).val ≠ 0
    rw [hwu]
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _).ne'
  have h := (complexExponentialDecay_contDiffOn_unitsChart g).mul (hw.contDiffOn.inv fun x hx ↦ hn x hx)
  apply h.congr
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  simp only [dite_eq_left hx0, Pi.inv_apply]
  have hg : g.val u = w x * f.val u :=
    (modulatedExponentialDecayTwist_apply m _ _ f u).trans (by rw [← hwu]; rfl)
  change f.val u = g.val u * (w x)⁻¹
  rw [hg, mul_right_comm, mul_inv_cancel₀ (hn x hx0), one_mul]

private theorem complexExponentialDecay_contDiffOn_of_weight {K : Type*} [NormedField K]
    [NormedAlgebra ℝ K] [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K]
    (m : Kˣ →ₜ* ℝ≥0ˣ) (a : ℝ) (ha : a ∈ Ioi (0 : ℝ))
    (f : ModulatedExponentialDecay m (Ioi (0 : ℝ)))
    (w : K → ℂ) (hw : ContDiff ℝ (∞ : ℕ∞ω) w)
    (hwu : ∀ u : Kˣ, w u.val = (((m u).val : ℝ) ^ a : ℝ)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) :=
  complexExponentialDecay_contDiffOn_of_weightIn m a ha f w hw hwu

/-- Paper: Proposition 5.3.3.2(2)(1), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured real line. -/
theorem realExponentialDecay_contDiffOn (f : 𝓔(ℝ, 1, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℝ) := by
  apply complexExponentialDecay_contDiffOn_of_weight (archimedeanUnitModulation ℝ 1) 2
    (by norm_num : (2 : ℝ) ∈ Ioi 0) f (fun x ↦ ((x ^ 2 : ℝ) : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.pow 2))
  intro u
  rw [archimedeanUnitModulation_apply, pow_one, Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured complex plane
as functions of two real variables. -/
theorem complexExponentialDecay_contDiffOn (f : 𝓔(ℂ, 2, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℂ) := by
  have hRe : ContDiff ℝ (∞ : ℕ∞ω) Complex.re := Complex.reCLM.contDiff
  have hIm : ContDiff ℝ (∞ : ℕ∞ω) Complex.im := Complex.imCLM.contDiff
  have hn : ContDiff ℝ (∞ : ℕ∞ω) (fun z : ℂ ↦ Complex.normSq z) := by
    simp only [Complex.normSq_apply]
    exact (hRe.mul hRe).add (hIm.mul hIm)
  apply complexExponentialDecay_contDiffOn_of_weight (archimedeanUnitModulation ℂ 2) 1
    (by norm_num : (1 : ℝ) ∈ Ioi 0) f (fun z ↦ (Complex.normSq z : ℂ))
    (Complex.ofRealCLM.contDiff.comp hn)
  intro u
  rw [archimedeanUnitModulation_apply, Real.rpow_one, Complex.normSq_eq_norm_sq]

namespace IteratedWirtinger

open Complex

/-- Recover local differentiability by taking one positive integral power of the
squared norm whose exponent belongs to the input interval. -/
private theorem intervalDifferentiable (a : ℝ) (f : 𝓔(ℂ, 2, Ioi a)) (z : ℂˣ) :
    DifferentiableAt ℝ zeroExtension(f.val) z.val := by
  obtain ⟨k, hk⟩ := exists_nat_gt a
  have hn : ContDiff ℝ (∞ : ℕ∞ω) (fun y : ℂ ↦ normSq y) := by
    simp only [normSq_apply]
    exact (reCLM.contDiff.mul reCLM.contDiff).add (imCLM.contDiff.mul imCLM.contDiff)
  have hc := complexExponentialDecay_contDiffOn_of_weightIn (archimedeanUnitModulation ℂ 2)
    (k : ℝ) (show (k : ℝ) ∈ Ioi a from hk) f (fun y ↦ ((normSq y)^k : ℝ))
    (ofRealCLM.contDiff.comp (hn.pow k)) (fun u ↦ by
      rw [archimedeanUnitModulation_apply, normSq_eq_norm_sq, Real.rpow_natCast])
  exact (hc.contDiffAt (isOpen_compl_singleton.mem_nhds z.ne_zero)).differentiableAt (by decide)

/-- At each output weight the derivative uses the input weight one half lower.
Untwist at one such weight to construct the underlying linear map. -/
private theorem intervalStep (s : Bool) (a : ℝ) :
    ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi (a + 1)), ∀ f (z : ℂˣ),
      (D f).val z = (wirtinger(s)) zeroExtension(f.val) z.val := by
  let n := archimedeanUnitModulation ℂ 2
  let J := Ioi (a + 1)
  let E := ModulatedExponentialDecay n (Ioi a)
  let d (f : E) (z : ℂˣ) := (wirtinger(s)) zeroExtension(f.val) z.val
  obtain ⟨M, hM⟩ := phaseMultiplier s
  have htwist (c : J) : ∃ U : E →L[ℂ] SchwartzBruhat ℂˣ,
      ∀ f, (U f).val = modulationWeight n c (d f) := by
    have hc : c.val - 1/2 ∈ Ioi a := by
      have hc' : a + 1 < c.val := c.property
      change a < _
      linarith
    obtain ⟨U, hU⟩ := onWeightIn (intervalDifferentiable a) s c hc M hM
    refine ⟨U, fun f ↦ funext fun z ↦ (hU f z).trans ?_⟩
    change _ = (((((archimedeanUnitModulation ℂ 2 z).val : ℝ) ^ (c : ℝ) : ℝ) : ℂ) * d f z)
    rw [archimedeanUnitModulation_apply]
    rfl
  let c₀ : J := ⟨a + 1 + 1, lt_add_one _⟩
  let U := (htwist c₀).choose
  let L : E →ₗ[ℂ] (ℂˣ → ℂ) := (modulationWeight n (-c₀.val)).comp
    ((schwartzBruhatSubmodule ℂˣ).subtype.comp U.toLinearMap)
  have hL (f : E) : L f = d f := by
    funext z
    change modulationWeight n (-c₀.val) (U f).val z = _
    rw [(htwist c₀).choose_spec f]
    change (((((n z).val : ℝ) ^ (-c₀.val) : ℝ) : ℂ) *
      (((((n z).val : ℝ) ^ c₀.val : ℝ) : ℂ) * d f z)) = _
    rw [← mul_assoc, ← ofReal_mul, ← Real.rpow_add (NNReal.coe_pos.mpr (Units.zero_lt _)),
      neg_add_cancel, Real.rpow_zero, ofReal_one, one_mul]
  let D := L.codRestrict (modulatedExponentialDecaySubmodule n J) fun f ↦
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr (by
      change modulationWeight n c (L f) ∈ schwartzBruhatSubmodule ℂˣ
      rw [hL f, ← (htwist c).choose_spec f]
      exact ((htwist c).choose f).property)
  let iso := (stdOrthonormalBasis ℝ ℂ).repr
  have hk : IsBruhatGoodSubgroup (⊥ : Subgroup ℂˣ) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨_, ⟨(iso.toHomeomorph.isOpenEmbedding.comp
      (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩
  refine ⟨⟨D, (iteratedDeriv_exponentialDecay_inducing_of_bot n J hk.2.2).continuous_iff.mpr
    (continuous_pi fun c ↦ ?_)⟩, fun f ↦ congrFun (hL f)⟩
  exact (htwist c).choose.continuous.congr fun f ↦ Subtype.ext
    (((htwist c).choose_spec f).trans (congrArg (modulationWeight n c) (hL f).symm))

end IteratedWirtinger

-- TODO(paper-gap): The first Wirtinger operator in the printed weighted shift is
-- missing the exponent m. The proof uses m derivatives for both operators.

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Either iterated Wirtinger derivative gives a continuous operator into the indicated decay space.
Deviation: Both derivatives have order m, as in the proof. The stated target with shift m is
retained, although the squared norm permits a shift of m/2. -/
theorem iteratedWirtinger_exponentialDecay (conjugate : Bool) (m : ℕ) {a : ℝ} (_ha : a < 0) :
    ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi (a + m)),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by
  let W := wirtinger(conjugate)
  let P (k : ℕ) (b : ℝ) := ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi b),
    ∀ f (z : ℂˣ), (D f).val z = (W^[k] zeroExtension(f.val)) z.val
  change P m (a + m)
  induction m with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    refine ⟨ContinuousLinearMap.id ℂ _, fun f z ↦ ?_⟩
    change f.val z = zeroExtension(f.val) z.val
    simp only [dite_eq_left z.ne_zero]
    exact congrArg f.val (Units.ext rfl)
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc]
    obtain ⟨A, hA⟩ := ih
    obtain ⟨B, hB⟩ := IteratedWirtinger.intervalStep conjugate (a + m)
    refine ⟨B.comp A, fun f z ↦ (hB (A f) z).trans ?_⟩
    change W zeroExtension((A f).val) z.val = (W^[m+1] zeroExtension(f.val)) z.val
    rw [Function.iterate_succ_apply']
    have he : zeroExtension((A f).val) =ᶠ[𝓝 z.val] W^[m] zeroExtension(f.val) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds (show z.val ∈ ({0}ᶜ : Set ℂ) from z.ne_zero)] with y hy
      exact (dite_eq_left (show y ≠ 0 from hy)).trans (hA f (Units.mk0 y hy))
    have hd := he.fderiv_eq (𝕜 := ℝ)
    cases conjugate <;> simp [W, wirtingerConjDeriv, wirtingerDeriv] at hd ⊢ <;> rw [hd]

end PuncturedLine

section ArchimedeanProduct

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation "archAdd(" ι ", " κ ")" => ((ι → ℝ) × (κ → ℂ))
local notation "archMul(" ι ", " κ ")" => ((ι → ℝˣ) × (κ → ℂˣ))
local notation "archVal" => fun u ↦ (fun i ↦ (u.1 i).val, fun j ↦ (u.2 j).val)
local notation "meetsWall(" x ")" => ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0))
local notation "weights(" ι ", " κ ", " I ")" =>
  ((ι → (insert 0 I : Set ℝ)) × (κ → (insert 0 I : Set ℝ)))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "weightMap(" a ")" => LinearMap.mulLeft ℂ
  (fun u : archMul(ι, κ) ↦
    ((∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℝ) *
    ((∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℝ) : archMul(ι, κ) → ℂ)

/-- Paper: Lemma 5.3.3.3, p. 252.
Every partial coordinate weight with exponents in I must yield a Schwartz–Bruhat function.
Deviation: A zero exponent encodes an omitted coordinate in (5.3.3.5), including the
unweighted condition when every coordinate is omitted. -/
def archimedeanWeightedSchwartzSubmodule (I : Set ℝ) :
    Submodule ℂ (archMul(ι, κ) → ℂ) :=
  ⨅ a : weights(ι, κ, I), (schwartzBruhatSubmodule _).comap (weightMap(a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The map for a family of exponents applies its weight and returns a Schwartz–Bruhat function. -/
def archimedeanSchwartzTwist (I : Set ℝ) (a : weights(ι, κ, I)) :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I →ₗ[ℂ]
      SchwartzBruhat (archMul(ι, κ)) :=
  ((weightMap(a)).comp (archimedeanWeightedSchwartzSubmodule I).subtype).codRestrict
    (schwartzBruhatSubmodule _) (fun f ↦
      Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 f.property a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The twist uses one power of the real norm and the corresponding power of the squared
complex norm in each coordinate. -/
theorem archimedeanSchwartzTwist_apply (I : Set ℝ) (a : weights(ι, κ, I))
    (f : archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (u : archMul(ι, κ)) :
    archimedeanSchwartzTwist I a f u =
      (↑(∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℂ) *
      (↑(∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℂ) * f.val u := by
  rfl

/-- Paper: Lemma 5.3.3.3, p. 252.
On both the real and complex coordinates, choosing only zero exponents gives the
unweighted Schwartz–Bruhat space. -/
theorem archimedeanWeightedSchwartzSubmodule_singleton_zero :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) {0} =
      schwartzBruhatSubmodule (archMul(ι, κ)) := by
  have hw : ∀ a : weights(ι, κ, ({0} : Set ℝ)), ∀ f : archMul(ι, κ) → ℂ, weightMap(a) f = f := by
    intro a f
    have h1 : ∀ i, (a.1 i : ℝ) = 0 := fun i ↦ by simpa using (a.1 i).property
    have h2 : ∀ j, (a.2 j : ℝ) = 0 := fun j ↦ by simpa using (a.2 j).property
    funext u
    simp [h1, h2]
  ext f
  simp only [archimedeanWeightedSchwartzSubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h
    have := h (fun _ ↦ ⟨0, by simp⟩, fun _ ↦ ⟨0, by simp⟩)
    rwa [hw] at this
  · intro h a
    rwa [hw]

/-- Paper: Lemma 5.3.3.3, p. 252.
The topology is the initial locally convex topology for all the partial weight maps into
the Schwartz–Bruhat space in (5.3.3.8).

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its seminorm family (#5398). -/
def ArchimedeanWeightedSchwartz (I : Set ℝ) :=
  WithGeneratingSeminorms (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : weights(ι, κ, I) ×
      {p : Seminorm ℂ (SchwartzBruhat (archMul(ι, κ))) // Continuous p} ↦
      i.2.val.comp (archimedeanSchwartzTwist I i.1))

namespace ArchimedeanWeightedSchwartz

variable (I : Set ℝ)

instance instAddCommGroup : AddCommGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (AddCommGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instModule : Module ℂ (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (Module ℂ (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instTopologicalSpace :
    TopologicalSpace (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (TopologicalSpace (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instPolynormableSpace :
    PolynormableSpace ℂ (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (PolynormableSpace ℂ (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instIsTopologicalAddGroup :
    IsTopologicalAddGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (IsTopologicalAddGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instUniformSpace : UniformSpace (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (UniformSpace (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

instance instIsUniformAddGroup :
    IsUniformAddGroup (ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I) :=
  inferInstanceAs (IsUniformAddGroup (WithGeneratingSeminorms
    (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I) _))

end ArchimedeanWeightedSchwartz

local notation "𝓦(" I ")" => ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I

/-- Paper: Lemma 5.3.3.3, p. 252.
When there are no coordinates, the weighted Schwartz space is the scalar field. -/
theorem archimedeanWeightedSchwartz_empty_equiv (I : Set ℝ) :
    ∃ e : ArchimedeanWeightedSchwartz (ι := Empty) (κ := Empty) I ≃L[ℂ] ℂ,
      ∀ f, e f = f.val (1 : archMul(Empty, Empty)) := by
  classical
  let G := archMul(Empty, Empty)
  let W := weights(Empty, Empty, I)
  let E := archimedeanWeightedSchwartzSubmodule (ι := Empty) (κ := Empty) I
  let P : SeminormFamily ℂ E (W × {p : Seminorm ℂ (SchwartzBruhat G) // Continuous p}) :=
    fun i ↦ i.2.val.comp (archimedeanSchwartzTwist I i.1)
  let X := WithGeneratingSeminorms E P
  let a : W := (Empty.elim, Empty.elim)
  have htwist (b : W) (f : E) (u : G) : archimedeanSchwartzTwist I b f u = f.val u := by
    simp [archimedeanSchwartzTwist_apply]
  obtain ⟨f, hf, _⟩ := schwartzBruhat_exists_test (1 : G) 1
  let f₀ : E := ⟨f.val, by
    apply (Submodule.mem_iInf _).mpr
    intro b
    change (fun u : G ↦ _ * _ * f.val u) ∈ schwartzBruhatSubmodule G
    simpa using f.property⟩
  let L : X →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp E.subtype
  have hL : Bijective L := by
    constructor
    · intro f g h
      apply Subtype.ext
      funext u
      exact (congrArg f.val (Subsingleton.elim u 1)).trans
        (h.trans (congrArg g.val (Subsingleton.elim 1 u)))
    · intro c
      refine ⟨(c / f 1) • f₀, ?_⟩
      change (c / f 1) * f 1 = c
      exact div_mul_cancel₀ c hf
  let e : X ≃ₗ[ℂ] ℂ := LinearEquiv.ofBijective L hL
  have hP := withGeneratingSeminorms_spec E P
  let : ContinuousSMul ℂ X := hP.continuousSMul
  have he : Continuous e := by
    let ev : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp (schwartzBruhatSubmodule G).subtype
    let q : Seminorm ℂ (SchwartzBruhat G) := (normSeminorm ℂ ℂ).comp ev
    have hq : Continuous q := (continuous_schwartzBruhat_eval_forEndpoints (1 : G)).norm
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp e.toLinearMap
    intro _
    exact (hP.continuous_seminorm (a, ⟨q, hq⟩)).congr (fun f ↦ by
      change ‖archimedeanSchwartzTwist I a f 1‖ = ‖f.val 1‖
      exact congrArg norm (htwist a f 1))
  have he' : Continuous e.symm := by
    have h : (e.symm : ℂ → X) = fun c ↦ c • e.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h]
    fun_prop
  exact ⟨⟨e, he, he'⟩, fun _ ↦ rfl⟩

private theorem compactlyGenerated_pi_finite {ι : Type*} [Finite ι]
    (H : ι → Type*) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    (h : ∀ i, IsCompactlyGeneratedGroup (H i)) : IsCompactlyGeneratedGroup (∀ i, H i) := by
  choose K hK hKc hKg using h
  refine ⟨Set.univ.pi K, set_pi_mem_nhds finite_univ (fun i _ ↦ hK i), isCompact_univ_pi hKc, ?_⟩
  rw [Subgroup.closure_pi (fun i ↦ mem_of_mem_nhds (hK i))]
  simpa only [hKg] using Subgroup.pi_top (f := H) Set.univ

/-- The product of the real and complex unit groups is compactly generated
and locally Euclidean, so its Schwartz–Bruhat space has a full stage. -/
private theorem schwartzBruhat_archimedean_metrizable :
    MetrizableSpace (SchwartzBruhat (archMul(ι, κ))) := by
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hR := compactlyGenerated_of_surjective_modulation (archimedeanUnitModulation ℝ 1)
    realCoordinate_mul_allExponentialDecay_modulation.1 realCoordinate_mul_allExponentialDecay_modulation.2
  have hC := compactlyGenerated_of_surjective_modulation (archimedeanUnitModulation ℂ 2)
    complexCoordinate_mul_allExponentialDecay_modulation.1 complexCoordinate_mul_allExponentialDecay_modulation.2
  obtain ⟨K, hK, hKc, hKg⟩ := compactlyGenerated_pi_finite (fun _ : ι ↦ ℝˣ) fun _ ↦ hR
  obtain ⟨L, hL, hLc, hLg⟩ := compactlyGenerated_pi_finite (fun _ : κ ↦ ℂˣ) fun _ ↦ hC
  let G := archMul(ι, κ)
  have hgen : IsCompactlyGeneratedGroup G :=
    ⟨K ×ˢ L, prod_mem_nhds hK hL, hKc.prod hLc, by
      rw [Subgroup.closure_prod (mem_of_mem_nhds hK) (mem_of_mem_nhds hL), hKg, hLg,
        Subgroup.top_prod_top]⟩
  let V := (ι → ℝ) × (κ → ℂ)
  let n := Module.finrank ℝ V
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  have hval : IsOpenEmbedding
      (fun u : G ↦ ((fun i ↦ (u.1 i).val, fun j ↦ (u.2 j).val) : V)) :=
    (Topology.IsOpenEmbedding.piMap (fun _ : ι ↦ Units.isOpenEmbedding_val (R := ℝ))).prodMap
      (Topology.IsOpenEmbedding.piMap (fun _ : κ ↦ Units.isOpenEmbedding_val (R := ℂ)))
  have hloc : IsLocallyEuclidean G :=
    ⟨n, ⟨(e.toHomeomorph.isOpenEmbedding.comp hval).singletonChartedSpace⟩⟩
  let top : G ≃ₜ* (⊤ : Subgroup G) :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  let a : BruhatStructuralPair G :=
    ⟨(⊤, OrderDual.toDual (⊥ : Subgroup G)), isOpen_univ,
      isCompactlyGeneratedGroup_of_continuousMulEquiv top hgen,
      isBruhatGoodSubgroup_bot_iff.mpr hloc, le_top⟩
  let d := Classical.choice a.elementary
  let j : SchwartzBruhatStage d →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a d
  have hj : Function.Surjective j := by
    intro f
    obtain ⟨b, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
    have hba : b ≤ a := ⟨le_top, le_top⟩
    obtain ⟨L, hL⟩ := schwartzBruhatStage_transition hba e d
    exact ⟨L s, Subtype.ext ((hL.1 s).trans hs)⟩
  let _ := d.finiteGroup
  let _ := d.finiteTopology
  let _ := d.finiteDiscrete
  let _ := d.finiteFintype
  let : MetrizableSpace (SchwartzBruhatStage d) := elementarySchwartz_isFrechet.choose_spec.2.1
  exact ((schwartzBruhatStage_isEmbedding a d).toHomeomorphOfSurjective hj).symm.isEmbedding.metrizableSpace

/-- The product of all partial twists induces the weighted Schwartz topology. -/
private theorem archimedeanSchwartzTwists_isEmbedding (I : Set ℝ) :
    Topology.IsEmbedding (LinearMap.pi (archimedeanSchwartzTwist (ι := ι) (κ := κ) I) :
      𝓦(I) →ₗ[ℂ] (weights(ι, κ, I) → SchwartzBruhat (archMul(ι, κ)))) := by
  classical
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let X := SchwartzBruhat (archMul(ι, κ))
  let Z := weights(ι, κ, I)
  let t : 𝓦(I) →ₗ[ℂ] (Z → X) := LinearMap.pi (archimedeanSchwartzTwist I)
  let : PolynormableSpace ℂ X := (schwartzBruhat_nuclear.{0} (G := archMul(ι, κ))).2.1
  have hp := withSeminorms_pi fun _ : Z ↦ PolynormableSpace.withSeminorms ℂ X
  have hs := withGeneratingSeminorms_spec (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : Z × {p : Seminorm ℂ X // Continuous p} ↦ i.2.val.comp (archimedeanSchwartzTwist I i.1))
  constructor
  · constructor
    refine hs.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf
      (t := TopologicalSpace.induced t inferInstance) (t.withSeminorms_induced hp)).symm
    rw [iInf_sigma, iInf_prod]
    rfl
  · intro f g h
    let a : Z := (fun _ ↦ ⟨0, Set.mem_insert _ _⟩, fun _ ↦ ⟨0, Set.mem_insert _ _⟩)
    apply Subtype.ext
    funext u
    have hu := congrArg (fun v : X ↦ v u) (congrFun h a)
    change archimedeanSchwartzTwist I a f u = archimedeanSchwartzTwist I a g u at hu
    have hv := (archimedeanSchwartzTwist_apply I a f u).symm.trans
      (hu.trans (archimedeanSchwartzTwist_apply I a g u))
    simpa [a] using hv

/-- Paper: Lemma 5.3.3.3(1), p. 252.
Metrizability half of the lemma. Coordinatewise interpolation between rational
exponents in `I`, together with zero for omitted coordinates, gives a countable
family of twists that induces the topology.
Deviation: The printed proof uses integer exponents, which need not lie in `I`. -/
theorem archimedeanWeightedSchwartz_metrizable {I : Set ℝ} (ho : IsOpen I)
    (hi : OrdConnected I) (hne : I.Nonempty) : MetrizableSpace 𝓦(I) := by
  clear hi hne
  classical
  let W := 𝓦(I)
  let G := archMul(ι, κ)
  let S := SchwartzBruhat G
  let J := ι ⊕ κ
  let A := (insert 0 I : Set ℝ)
  let D := insert 0 (I ∩ range (Rat.cast : ℚ → ℝ))
  let d : D → A := fun x ↦ ⟨x.val, by
    rcases Set.mem_insert_iff.mp x.property with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_of_mem _ h.1⟩
  have hbracket (x : A) (hx : x.val ∉ D) :
      ∃ p q : D, p.val ≤ x.val ∧ x.val ≤ q.val := by
    have hx0 : x.val ≠ 0 := fun h ↦ hx (h ▸ mem_insert _ _)
    have hxI := (mem_insert_iff.mp x.property).resolve_left hx0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho _ hxI
    obtain ⟨p, hp₁, hp₂⟩ := exists_rat_btwn (sub_lt_self x.val hε)
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (lt_add_of_pos_right x.val hε)
    have hp : (p : ℝ) ∈ Metric.ball x.val ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hq : (q : ℝ) ∈ Metric.ball x.val ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact ⟨⟨p, mem_insert_of_mem _ ⟨hball hp, mem_range_self p⟩⟩,
      ⟨q, mem_insert_of_mem _ ⟨hball hq, mem_range_self q⟩⟩, hp₂.le, hq₁.le⟩
  let e : (J → A) ≃ weights(ι, κ, I) := Equiv.sumArrowEquivProdArrow _ _ _
  let twist (a : J → A) : W →ₗ[ℂ] S := archimedeanSchwartzTwist I (e a)
  let m : J → (G →ₜ* ℝ≥0ˣ) := Sum.elim
    (fun i ↦ (archimedeanUnitModulation ℝ 1).comp
      ⟨(Pi.evalMonoidHom _ i).comp (MonoidHom.fst _ _), (continuous_apply i).comp continuous_fst⟩)
    (fun j ↦ (archimedeanUnitModulation ℂ 2).comp
      ⟨(Pi.evalMonoidHom _ j).comp (MonoidHom.snd _ _), (continuous_apply j).comp continuous_snd⟩)
  have htw (a : J → A) (f : W) (u : G) :
      twist a f u = (↑(∏ i, ((m i u).val : ℝ) ^ (a i : ℝ)) : ℂ) * f.val u := by
    refine (archimedeanSchwartzTwist_apply I (e a) f u).trans ?_
    rw [Fintype.prod_sum_type, Complex.ofReal_mul]
    have hl (i : ι) : ((m (.inl i) u).val : ℝ) = ‖(u.1 i).val‖ := by
      change ((archimedeanUnitModulation ℝ 1 (u.1 i)).val : ℝ) = _
      rw [archimedeanUnitModulation_apply, pow_one]
    have hr (j : κ) : ((m (.inr j) u).val : ℝ) = ‖(u.2 j).val‖ ^ (2 : ℕ) :=
      archimedeanUnitModulation_apply ℂ 2 _
    simp only [hl, hr]
    rfl
  let t (f : W) (j : J → D) : S := twist (d ∘ j) f
  let Y := (J → D) → S
  -- Replace one coordinate at a time using the Appendix D modulation interpolation.
  have hall (a : J → A) : ∃ F : Y → S, Continuous F ∧ ∀ f, F (t f) = twist a f := by
    suffices h : ∀ (s : Finset J) (a : J → A), (∀ i ∉ s, (a i).val ∈ D) →
        ∃ F : Y → S, Continuous F ∧ ∀ f, F (t f) = twist a f by
      exact h Finset.univ a (by simp)
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      let j : J → D := fun i ↦ ⟨a i, ha i (by simp)⟩
      have he : d ∘ j = a := funext fun i ↦ Subtype.ext rfl
      exact ⟨fun g ↦ g j, continuous_apply j, fun f ↦ congrArg (fun a ↦ twist a f) he⟩
    | insert i s his ih =>
      intro a ha
      have hrest (j : J) (hj : j ∉ s) (hne : j ≠ i) : (a j).val ∈ D :=
        ha j (by simpa [Finset.mem_insert, hne] using hj)
      by_cases hi : (a i).val ∈ D
      · exact ih a fun j hj ↦ by
          by_cases hji : j = i
          · simpa [hji] using hi
          · exact hrest j hj hji
      obtain ⟨p, q, hp, hq⟩ := hbracket (a i) hi
      have hup (x : D) : ∃ F : Y → S, Continuous F ∧
          ∀ f, F (t f) = twist (Function.update a i (d x)) f :=
        ih _ fun j hj ↦ by
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self, d] using x.property
          · simpa [Function.update_of_ne hji] using hrest j hj hji
      obtain ⟨F, hF⟩ := modulationWeight_between_continuous (m i) p.val (a i).val q.val hp hq
      obtain ⟨Fp, hcp, hpF⟩ := hup p
      obtain ⟨Fq, hcq, hqF⟩ := hup q
      refine ⟨fun g ↦ F (Fp g, Fq g), F.continuous.comp (hcp.prodMk hcq), fun f ↦ ?_⟩
      change F (Fp (t f), Fq (t f)) = twist a f
      rw [hpF f, hqF f]
      let g (u : G) : ℂ :=
        (↑(∏ j ∈ Finset.univ.erase i, ((m j u).val : ℝ) ^ (a j : ℝ)) : ℂ) * f.val u
      have hg (b : J → A) (hb : ∀ j ≠ i, b j = a j) :
          (twist b f).val = modulationWeight (m i) (b i).val g := by
        funext u
        change twist b f u = _
        rw [htw, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Complex.ofReal_mul, mul_assoc]
        congr 2
        apply congrArg Complex.ofReal
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        rw [hb j (Finset.ne_of_mem_erase hj)]
      have hl (x : D) : (twist (Function.update a i (d x)) f).val =
          modulationWeight (m i) x.val g := by
        simpa only [Function.update_self] using
          hg (Function.update a i (d x)) (fun j hj ↦ Function.update_of_ne hj _ _)
      exact Subtype.ext ((hF g _ (hl p) (hl q)).trans (hg a (fun _ _ ↦ rfl)).symm)
  let T : W →ₗ[ℂ] (weights(ι, κ, I) → S) := LinearMap.pi (archimedeanSchwartzTwist I)
  have hs := withGeneratingSeminorms_spec (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : weights(ι, κ, I) × {p : Seminorm ℂ S // Continuous p} ↦
      i.2.val.comp (archimedeanSchwartzTwist I i.1))
  let hSgen := PolynormableSpace.withSeminorms ℂ S
  have hT : IsInducing T := by
    constructor
    refine hs.topologicalSpace_eq_iInf.trans ?_
    refine Eq.trans ?_ (WithSeminorms.topologicalSpace_eq_iInf
      (t := TopologicalSpace.induced T inferInstance)
      (T.withSeminorms_induced (withSeminorms_pi fun _ : weights(ι, κ, I) ↦ hSgen))).symm
    rw [iInf_sigma, iInf_prod]
    rfl
  choose F hF hfact using hall
  let U (g : Y) (a : weights(ι, κ, I)) : S := F (e.symm a) g
  have hU : Continuous U := continuous_pi fun a ↦ hF (e.symm a)
  have hUt : U ∘ t = T := by
    funext f a
    exact (hfact (e.symm a) f).trans (congrArg (fun a ↦ archimedeanSchwartzTwist I a f)
      (e.apply_symm_apply a))
  have ht : IsEmbedding t := by
    constructor
    · have hcont : Continuous t := continuous_pi fun j ↦
        (continuous_apply (e (d ∘ j))).comp hT.continuous
      exact IsInducing.of_comp (f := t) (g := U) hcont hU (hUt.symm ▸ hT)
    · intro f g h
      let z : D := ⟨0, mem_insert _ _⟩
      exact Subtype.ext (funext fun u ↦ by
        have hu := congrArg (fun s : S ↦ s u) (congrFun h (fun _ ↦ z))
        change twist (d ∘ fun _ ↦ z) f u = twist (d ∘ fun _ ↦ z) g u at hu
        simpa [htw, d, z] using hu)
  have hcount : D.Countable := ((countable_range (Rat.cast : ℚ → ℝ)).mono inter_subset_right).insert _
  let : Countable D := hcount.to_subtype
  let : Fintype J := inferInstanceAs (Fintype (ι ⊕ κ))
  let : Countable (J → D) := inferInstance
  let : MetrizableSpace S := schwartzBruhat_archimedean_metrizable
  have : (uniformity S).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  let : MetrizableSpace Y := UniformSpace.metrizableSpace
  exact ht.metrizableSpace

/-- Paper: Lemma 5.3.3.3(1), p. 252.
Completeness half of the lemma. The partial weight maps embed the weighted space as a
closed submodule of a product of complete Schwartz–Bruhat spaces, so every Cauchy
filter of twists converges to the family of its pointwise limits. -/
theorem archimedeanWeightedSchwartz_complete {I : Set ℝ} (ho : IsOpen I)
    (hi : OrdConnected I) (hne : I.Nonempty) : CompleteSpace 𝓦(I) := by
  classical
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let G := archMul(ι, κ)
  let X := SchwartzBruhat G
  let Z := weights(ι, κ, I)
  let a₀ : Z := (fun _ ↦ ⟨0, Set.mem_insert _ _⟩, fun _ ↦ ⟨0, Set.mem_insert _ _⟩)
  let w (a : Z) (u : G) : ℂ :=
    (↑(∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℂ) *
      (↑(∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℂ)
  let T : 𝓦(I) →ₗ[ℂ] (Z → X) := LinearMap.pi (archimedeanSchwartzTwist I)
  have hr : Set.range T = ⋂ a : Z, ⋂ u : G, {p : Z → X | p a u = w a u * p a₀ u} := by
    ext y
    simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩ a u
      change w a u * x.val u = w a u * (w a₀ u * x.val u)
      simp [w, a₀]
    · intro hy
      have he (a : Z) : weightMap(a) (y a₀).val = (y a).val := funext fun u ↦ (hy a u).symm
      let x : 𝓦(I) := ⟨(y a₀).val, (Submodule.mem_iInf _).mpr fun a ↦
        Submodule.mem_comap.mpr ((he a).symm ▸ (y a).property)⟩
      exact ⟨x, funext fun a ↦ Subtype.ext (he a)⟩
  have ev (u : G) : Continuous (fun x : X ↦ x u) := continuous_schwartzBruhat_eval_forEndpoints u
  have hcl : IsClosed (Set.range T) := by
    rw [hr]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun u ↦ isClosed_eq
      ((ev u).comp (continuous_apply a)) (continuous_const.mul ((ev u).comp (continuous_apply a₀)))
  let : CompleteSpace X := schwartzBruhat_complete
  have ht : Topology.IsEmbedding T := archimedeanSchwartzTwists_isEmbedding I
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom)
    ht.isInducing).completeSpace hcl.isComplete

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the topology from the partial weight maps is Fréchet. -/
theorem archimedeanWeightedSchwartz_frechet {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsFrechetTVS 𝓦(I) := by
  refine ⟨inferInstance, inferInstance,
    archimedeanWeightedSchwartz_metrizable _ho _hi _hne, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact archimedeanWeightedSchwartz_complete _ho _hi _hne

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is separable. -/
theorem archimedeanWeightedSchwartz_separable {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : SeparableSpace 𝓦(I) := by
  classical
  have sep {E : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [FirstCountableTopology E] (h : IsNuclearTVS.{0} E) : SeparableSpace E := by
    let := h.1
    let := h.2.1
    let := PolynormableSpace.isTopologicalAddGroup ℂ E
    have hw := PolynormableSpace.withSeminorms ℂ E
    let : ContinuousSMul ℂ E := hw.continuousSMul
    obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
    have hex (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∃ r > 0, q.ball 0 r ⊆ U n := by
      obtain ⟨s, r, hr, hsub⟩ := (hw.mem_nhds_iff 0 (U n)).mp (hU.mem n)
      refine ⟨s.sup fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1, ?_, r, hr, hsub⟩
      exact hw.continuous_finsetSup_seminorm s
    choose q hq r hr hsub using hex
    have hsep (n : ℕ) : SeparableSpace (WithLocalSeminorm (q n)) :=
      seminorm_separable_of_nuclear h (q n) (hq n)
    have hd (n : ℕ) : ∃ d : ℕ → E, ∀ x : E, ∃ m, q n (x - d m) < r n := by
      obtain ⟨d, hd⟩ := exists_dense_seq (WithLocalSeminorm (q n))
      refine ⟨d, fun x ↦ ?_⟩
      let x' : WithLocalSeminorm (q n) := x
      obtain ⟨m, hm⟩ := hd.exists_dist_lt x' (hr n)
      rw [dist_eq_norm] at hm
      exact ⟨m, hm⟩
    choose d hd using hd
    refine ⟨range fun m : ℕ × ℕ ↦ d m.1 m.2, countable_range _, ?_⟩
    intro x
    rw [mem_closure_iff_nhds]
    intro W hW
    have hW0 : (fun y ↦ x + y) ⁻¹' W ∈ 𝓝 (0 : E) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨n, -, hn⟩ := hU.1.mem_iff.mp hW0
    obtain ⟨m, hm⟩ := hd n x
    refine ⟨d n m, ?_, ⟨(n, m), rfl⟩⟩
    have : d n m - x ∈ U n := hsub n (by rw [Seminorm.mem_ball, sub_zero, map_sub_rev]; exact hm)
    simpa using hn this
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let X := SchwartzBruhat (archMul(ι, κ))
  let Z := weights(ι, κ, I)
  let t : 𝓦(I) →ₗ[ℂ] (Z → X) := LinearMap.pi (archimedeanSchwartzTwist I)
  let : PolynormableSpace ℂ X := (schwartzBruhat_nuclear.{0} (G := archMul(ι, κ))).2.1
  have ht : Topology.IsEmbedding t := archimedeanSchwartzTwists_isEmbedding I
  have hn : IsNuclearTVS.{0} 𝓦(I) := isNuclearTVS_of_linearEmbedding t ht
    (isNuclearTVS_pi fun _ : Z ↦ schwartzBruhat_nuclear (G := archMul(ι, κ)))
  obtain ⟨_, -, _, -⟩ := archimedeanWeightedSchwartz_frechet (ι := ι) (κ := κ) _ho _hi _hne
  exact sep hn

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is nuclear. -/
theorem archimedeanWeightedSchwartz_nuclear {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsNuclearTVS 𝓦(I) := by
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let T := LinearMap.pi (archimedeanSchwartzTwist (ι := ι) (κ := κ) I)
  exact isNuclearTVS_of_linearEmbedding T (archimedeanSchwartzTwists_isEmbedding I)
    (isNuclearTVS_pi fun _ : weights(ι, κ, I) ↦ schwartzBruhat_nuclear (G := archMul(ι, κ)))

/-- Paper: Lemma 5.3.3.3(2), p. 252.
The finite projective tensor topology is generated by seminorms with jointly continuous
pullback along the pure tensor map, as for the binary projective tensor product of §C.2.3. -/
abbrev FiniteProjectiveTensor {ι : Type*} [Fintype ι] (E : ι → Type*)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)] :=
  WithGeneratingSeminorms (⨂[ℂ] i, E i)
    (fun p : {p : Seminorm ℂ (⨂[ℂ] i, E i) //
      Continuous (fun f : ∀ i, E i ↦ p (⨂ₜ[ℂ] i, f i))} ↦ p.val)

/-- Paper: Lemma 5.3.3.3(2), p. 252.
With no factors the projective tensor product identifies topologically with the scalars
and the empty pure tensor maps to one. -/
theorem finiteProjectiveTensor_empty_equiv :
    ∃ e : FiniteProjectiveTensor (fun _ : Empty ↦ ℂ) ≃L[ℂ] ℂ,
      e (⨂ₜ[ℂ] i : Empty, (0 : ℂ)) = 1 := by
  let X := ⨂[ℂ] _i : Empty, ℂ
  let P : SeminormFamily ℂ X
      {p : Seminorm ℂ X // Continuous (fun f : Empty → ℂ ↦ p (⨂ₜ[ℂ] i, f i))} := fun p ↦ p.val
  let l : WithGeneratingSeminorms X P ≃ₗ[ℂ] ℂ := PiTensorProduct.isEmptyEquiv Empty
  have hP := withGeneratingSeminorms_spec X P
  have : ContinuousSMul ℂ (WithGeneratingSeminorms X P) := hP.continuousSMul
  -- The norm of the scalar coordinate is one of the generating seminorms.
  have hl : Continuous l := by
    let q : Seminorm ℂ X := (normSeminorm ℂ ℂ).comp (PiTensorProduct.isEmptyEquiv Empty).toLinearMap
    have hq : Continuous (fun f : Empty → ℂ ↦ q (⨂ₜ[ℂ] i, f i)) := continuous_of_discreteTopology
    refine WithSeminorms.continuous_normedSpace_rng ℂ hP l.toLinearMap
      ⟨{⟨q, hq⟩}, 1, Seminorm.le_def.mpr fun x ↦ ?_⟩
    have hx : (({⟨q, hq⟩} : Finset _).sup P) x = q x :=
      congrArg (fun p : Seminorm ℂ X ↦ p x) Finset.sup_singleton
    exact le_of_eq (hx.symm.trans (one_smul ℝ≥0 _).symm)
  have hl' : Continuous l.symm := by
    have hsymm : (l.symm : ℂ → WithGeneratingSeminorms X P) = fun c ↦ c • l.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hsymm]
    fun_prop
  exact ⟨⟨l, hl, hl'⟩, PiTensorProduct.isEmptyEquiv_apply_tprod Empty _⟩

-- TODO(paper-gap): If 0 ∉ I the factors S_I need not be unweighted Schwartz–Bruhat,
-- whereas (5.3.3.6) requires this. Include the unweighted twist on each factor.

section

/-- The product of finitely many local tests belongs to the Schwartz–Bruhat space
of the product group. -/
private theorem sLocalIdelicZFunction_principalValue_productTest {ι : Type*} [Fintype ι] (G : ι → Type*)
    [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
    (f : ∀ i, SchwartzBruhat (G i)) : ∃ g : SchwartzBruhat (∀ i, G i),
      ∀ x, g x = ∏ i, f i (x i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    let : CompactSpace (∀ i, G i) := Finite.compactSpace
    obtain ⟨g, hg⟩ := compact_schwartzBruhat_one (H := (i : ι) → G i)
    exact ⟨g, fun x ↦ (hg x).trans (by simp)⟩
  | inr hi =>
    obtain ⟨i⟩ := hi
    let J := {j : ι // j ≠ i}
    obtain ⟨g, hg⟩ := sLocalIdelicZFunction_principalValue_productTest (ι := J) (fun j ↦ G j.val) (fun j ↦ f j.val)
    let e : ((j : ι) → G j) ≃ₜ* (G i × ((j : J) → G j.val)) :=
      { Homeomorph.piSplitAt i G with map_mul' := fun _ _ ↦ rfl }
    obtain ⟨t, ht⟩ := schwartzBruhat_kernel_equiv (G := G i) (H := (j : J) → G j.val)
    let q := t (UniformSpace.Completion.coe' (α := InductiveTensor (SchwartzBruhat (G i))
      (SchwartzBruhat ((j : J) → G j.val))) ((f i) ⊗ₜ[ℂ] g))
    refine ⟨⟨q.val ∘ e, schwartzBruhat_pullback_mem e q⟩, fun x ↦ ?_⟩
    change q (x i, fun j ↦ x j.val) = _
    rw [show q (x i, fun j ↦ x j.val) = _ from ht (f i) g _ _, hg, Fintype.prod_eq_mul_prod_compl i]
    exact congrArg (_ * ·) (Finset.prod_subtype _ (fun j ↦ by simp) (fun j ↦ f j (x j))).symm
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- Every separate product belongs to the simultaneously weighted Schwartz space.
For each tuple of weights, twist each factor before applying the unweighted kernel theorem. -/
private theorem archimedeanWeightedSchwartz_tensor_pure (I : Set ℝ)
    (f : ι → ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) (insert 0 I))
    (g : κ → ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) (insert 0 I)) :
    (fun u : archMul(ι, κ) ↦ (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)) ∈
      archimedeanWeightedSchwartzSubmodule I := by
  classical
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  apply (Submodule.mem_iInf _).mpr
  intro a
  let F := fun i ↦ modulatedExponentialDecayTwist (archimedeanUnitModulation ℝ 1)
    (insert 0 I) (a.1 i) (f i)
  let G := fun j ↦ modulatedExponentialDecayTwist (archimedeanUnitModulation ℂ 2)
    (insert 0 I) (a.2 j) (g j)
  obtain ⟨r, hr⟩ := sLocalIdelicZFunction_principalValue_productTest (fun _ : ι ↦ ℝˣ) F
  obtain ⟨c, hc⟩ := sLocalIdelicZFunction_principalValue_productTest (fun _ : κ ↦ ℂˣ) G
  obtain ⟨e, he⟩ := schwartzBruhat_kernel_equiv (G := ι → ℝˣ) (H := κ → ℂˣ)
  let q := e (UniformSpace.Completion.coe' (α := InductiveTensor _ _) (r ⊗ₜ[ℂ] c))
  apply Submodule.mem_comap.mpr
  convert q.property using 1
  funext u
  change _ * _ = q (u.1, u.2)
  rw [show q (u.1, u.2) = r (u.1) * c (u.2) from he r c _ _, hr, hc]
  have hf (i : ι) : F i (u.1 i) = ((‖(u.1 i).val‖ ^ (a.1 i : ℝ) : ℝ) : ℂ) * (f i).val (u.1 i) := by
    simpa only [archimedeanUnitModulation_apply, pow_one] using
      modulatedExponentialDecayTwist_apply (archimedeanUnitModulation ℝ 1) _ (a.1 i) (f i) (u.1 i)
  have hg (j : κ) : G j (u.2 j) = (((‖(u.2 j).val‖ ^ (2:ℕ)) ^ (a.2 j : ℝ) : ℝ) : ℂ) *
      (g j).val (u.2 j) := by
    simpa only [archimedeanUnitModulation_apply] using
      modulatedExponentialDecayTwist_apply (archimedeanUnitModulation ℂ 2) _ (a.2 j) (g j) (u.2 j)
  simp only [hf, hg, Finset.prod_mul_distrib, Complex.ofReal_prod]
  ring

/-- Evaluation on two independent sets of coordinates separates algebraic tensors.
Evaluating the left coordinate recovers a vector in the right factor, and taking
its basis coordinates recovers the coefficients of the original tensor. -/
private theorem archimedeanWeightedSchwartz_tensor_binary_injective
    {U V A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (r : A →ₗ[ℂ] (U → ℂ)) (c : B →ₗ[ℂ] (V → ℂ)) (hr : Injective r) (hc : Injective c)
    (P : A ⊗[ℂ] B →ₗ[ℂ] (U × V → ℂ))
    (hP : ∀ a b u v, P (a ⊗ₜ[ℂ] b) (u,v) = r a u * c b v) : Injective P := by
  classical
  let b := Module.Free.chooseBasis ℂ B
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  let S (u : U) : A ⊗[ℂ] B →ₗ[ℂ] B := TensorProduct.lift
    ((LinearMap.lsmul ℂ B).comp ((LinearMap.proj u).comp r))
  have hs (u : U) (v : V) (z : A ⊗[ℂ] B) : c (S u z) v = P z (u,v) := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [S, hP, smul_eq_mul]
    | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (·+·) hx hy
  have hb (u : U) (i) (z : A ⊗[ℂ] B) : b.repr (S u z) i = r (e z i) u := by
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      simp [S, e, smul_eq_mul, mul_comm]
    | add x y hx hy =>
      simpa only [map_add, Finsupp.add_apply, Pi.add_apply] using congrArg₂ (·+·) hx hy
  apply (LinearMap.ker_eq_bot.mp ?_)
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have hzero (u : U) : S u z = 0 := by
    apply hc
    ext v
    rw [hs, hz, map_zero]
    rfl
  apply e.injective
  ext i
  apply_fun r using hr
  ext u
  simp only [← hb, hzero, map_zero, Finsupp.zero_apply, Pi.zero_apply]

/-- Separate-coordinate evaluation is injective on a finite algebraic tensor, including
the scalar tensor on an empty family. Split off one coordinate at a time. -/
private theorem archimedeanWeightedSchwartz_tensor_pi_injective
    {ι U A : Type*} [Fintype ι] [AddCommGroup A] [Module ℂ A]
    (r : A →ₗ[ℂ] (U → ℂ)) (hr : Injective r)
    (P : (⨂[ℂ] _ : ι, A) →ₗ[ℂ] ((ι → U) → ℂ))
    (hP : ∀ f u, P (PiTensorProduct.tprod ℂ f) u = ∏ i, r (f i) (u i)) :
    Injective P := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let u : ι → U := isEmptyElim
    let e := PiTensorProduct.isEmptyEquiv (R := ℂ) (s := fun _ : ι ↦ A) ι
    have hx (z : ⨂[ℂ] _ : ι, A) : P z u = e z := by
      induction z using PiTensorProduct.induction_on with
      | smul_tprod b f =>
        have h1 : e (PiTensorProduct.tprod ℂ f) = 1 := PiTensorProduct.isEmptyEquiv_apply_tprod ι f
        rw [map_smul, Pi.smul_apply, map_smul, hP, h1, Fintype.prod_empty]
      | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (·+·) hx hy
    exact fun x y hxy ↦ e.injective ((hx x).symm.trans ((congrFun hxy u).trans (hx y)))
  | inr h =>
    obtain ⟨i⟩ := h
    let J := {j : ι // j ≠ i}
    let R : (⨂[ℂ] _ : J, A) →ₗ[ℂ] ((J → U) → ℂ) := LinearMap.pi fun u ↦
      PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ J ℂ).compLinearMap
        (fun j ↦ (LinearMap.proj (u j)).comp r))
    have hR (f : J → A) (u : J → U) : R (PiTensorProduct.tprod ℂ f) u = ∏ j, r (f j) (u j) := by
      simp [R, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra]
    have hRi := archimedeanWeightedSchwartz_tensor_pi_injective r hr R hR
    let Z := LinearMap.pi fun (u : (J → U) × U) ↦ TensorProduct.lift
      (LinearMap.compl₁₂ (LinearMap.mul ℂ ℂ) ((LinearMap.proj u.1).comp R) ((LinearMap.proj u.2).comp r))
    have hZ (x : ⨂[ℂ] _ : J, A) (y : A) (u : J → U) (v : U) :
        Z (x ⊗ₜ[ℂ] y) (u,v) = R x u * r y v := by simp [Z]
    have hZi := archimedeanWeightedSchwartz_tensor_binary_injective R r hRi hr Z hZ
    let split : J ⊕ Unit ≃ ι := Equiv.subtypeNeSumPUnit i
    let e : (⨂[ℂ] _ : ι, A) ≃ₗ[ℂ] (⨂[ℂ] _ : J, A) ⊗[ℂ] A :=
      ((PiTensorProduct.reindex ℂ (s := fun _ : ι ↦ A) split.symm).trans
        (PiTensorProduct.tmulEquiv ℂ A).symm).trans
          (LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv ()))
    have he (f : ι → A) : e (PiTensorProduct.tprod ℂ f) =
        (⨂ₜ[ℂ] j : J, f j.val) ⊗ₜ[ℂ] f i := by
      simp [e, PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
        PiTensorProduct.subsingletonEquiv_apply_tprod, split, Equiv.subtypeNeSumPUnit]
    have hev (z : ⨂[ℂ] _ : ι, A) (u : ι → U) : P z u = Z (e z) (fun j : J ↦ u j, u i) := by
      induction z using PiTensorProduct.induction_on with
      | smul_tprod b f =>
        simp only [map_smul, Pi.smul_apply, hP, he, hZ, hR]
        rw [Fintype.prod_eq_mul_prod_compl i]
        congr 1
        rw [mul_comm]
        congr 1
        exact Finset.prod_subtype _ (fun j ↦ by simp) _
      | add x y hx hy => simpa only [map_add, Pi.add_apply] using congrArg₂ (·+·) hx hy
    intro x y hxy
    apply e.injective
    apply hZi
    funext ⟨u,v⟩
    let extend (j : ι) := if h : j = i then v else u ⟨j,h⟩
    have hrest : (fun j : J ↦ extend j.val) = u := by funext j; simp [extend, j.property]
    simpa only [hev, hrest, show extend i = v by simp [extend]] using congrFun hxy extend
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- Lift the coordinate product through the two finite tensors and then their binary tensor.
The range lies in any submodule containing all separate products. -/
private theorem archimedeanWeightedSchwartz_tensor_lift
    {U V A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (r : A →ₗ[ℂ] (U → ℂ)) (c : B →ₗ[ℂ] (V → ℂ)) (hr : Injective r) (hc : Injective c)
    (W : Submodule ℂ (((ι → U) × (κ → V)) → ℂ))
    (hp : ∀ (f : ι → A) (g : κ → B),
      (fun u : (ι → U) × (κ → V) ↦ (∏ i, r (f i) (u.1 i)) * ∏ j, c (g j) (u.2 j)) ∈ W) :
    ∃ L : (⨂[ℂ] _ : ι, A) ⊗[ℂ] (⨂[ℂ] _ : κ, B) →ₗ[ℂ] W, Injective L ∧
      ∀ (f : ι → A) (g : κ → B) (u : (ι → U) × (κ → V)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, r (f i) (u.1 i)) * ∏ j, c (g j) (u.2 j) := by
  classical
  let R (u : ι → U) := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap
    (fun i ↦ (LinearMap.proj (u i)).comp r))
  let C (v : κ → V) := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap
    (fun j ↦ (LinearMap.proj (v j)).comp c))
  let L := LinearMap.pi fun (u : (ι → U) × (κ → V)) ↦
    TensorProduct.lift (LinearMap.compl₁₂ (LinearMap.mul ℂ ℂ) (R u.1) (C u.2))
  have hv (f : ι → A) (g : κ → B) : L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j)) =
      fun u ↦ (∏ i, r (f i) (u.1 i)) * ∏ j, c (g j) (u.2 j) := by
    funext u
    simp [L, R, C, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra]
  have hW z : L z ∈ W := by
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simpa only [map_add] using W.add_mem ha hb
    | tmul x y =>
      induction x using PiTensorProduct.induction_on with
      | add x x' hx hx' => simpa only [TensorProduct.add_tmul, map_add] using W.add_mem hx hx'
      | smul_tprod b f =>
        rw [← TensorProduct.smul_tmul', map_smul]
        apply W.smul_mem
        induction y using PiTensorProduct.induction_on with
        | add y y' hy hy' => simpa only [TensorProduct.tmul_add, map_add] using W.add_mem hy hy'
        | smul_tprod b' g =>
          rw [TensorProduct.tmul_smul, map_smul, hv]
          exact W.smul_mem _ (hp f g)
  have hR := archimedeanWeightedSchwartz_tensor_pi_injective r hr (LinearMap.pi R)
    (fun f u ↦ by simp [R, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra])
  have hC := archimedeanWeightedSchwartz_tensor_pi_injective c hc (LinearMap.pi C)
    (fun g v ↦ by simp [C, PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra])
  have hinj := archimedeanWeightedSchwartz_tensor_binary_injective (LinearMap.pi R) (LinearMap.pi C)
    hR hC L (fun x y u v ↦ by simp [L])
  exact ⟨L.codRestrict W hW, fun _ _ h ↦ hinj (congrArg Subtype.val h), fun f g u ↦ congrFun (hv f g) u⟩

/-- A densely embedded algebraic tensor has precisely the completion of its image. -/
private theorem archimedeanWeightedSchwartz_tensor_completion
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [ContinuousConstSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y]
    [IsUniformAddGroup Y] [ContinuousConstSMul ℂ Y] [T2Space Y] [CompleteSpace Y]
    (L : X →L[ℂ] Y) (hL : IsEmbedding L) (hd : DenseRange L) :
    ∃ e : UniformSpace.Completion X ≃L[ℂ] Y, ∀ z : X, e z = L z := by
  have hi := AddMonoidHom.isUniformInducing_of_isInducing (f := L.toLinearMap.toAddMonoidHom)
    hL.isInducing
  have he : IsUniformInducing L.fromCompletion := UniformSpace.Completion.isUniformInducing_extension hi
  have hr : DenseRange L.fromCompletion := by
    apply Dense.mono _ hd
    rintro _ ⟨x, rfl⟩
    exact ⟨(x : UniformSpace.Completion X), L.fromCompletion_apply_coe x⟩
  have hs : Surjective L.fromCompletion := by
    rw [← range_eq_univ, ← he.isComplete_range.isClosed.closure_eq, hr.closure_range]
  have hh : IsHomeomorph L.fromCompletion :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨he.isUniformEmbedding.isEmbedding, hs⟩
  exact ⟨.ofIsHomeomorph (.ofBijective L.fromCompletion.toLinearMap hh.bijective) hh,
    L.fromCompletion_apply_coe⟩

section WeightedTensorEstimates
local notation "realFactors(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) (insert 0 I)
local notation "complexFactors(" I ")" => ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) (insert 0 I)
local notation "productTensor(" I ")" => ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ realFactors(I)))
  (FiniteProjectiveTensor (fun _ : κ ↦ complexFactors(I)))
local notation "separateValue(" f ", " g ", " u ")" =>
  (∏ i, (f i).val ((u : archMul(ι, κ)).1 i)) * ∏ j, (g j).val (u.2 j)

/-- Joint continuity on pure tensors gives a product bound by continuous seminorms on the factors. -/
private theorem archimedeanWeightedSchwartz_tensor_pure_bound
    {ι A : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] [PolynormableSpace ℂ A]
    (p : Seminorm ℂ (⨂[ℂ] _ : ι, A))
    (hp : Continuous (fun f : ι → A ↦ p (PiTensorProduct.tprod ℂ f))) :
    ∃ q : ι → Seminorm ℂ A, (∀ i, Continuous (q i)) ∧
      ∀ f, p (PiTensorProduct.tprod ℂ f) ≤ ∏ i, q i (f i) := by
  classical
  have h0 : p ((PiTensorProduct.tprod ℂ) (0 : ι → A)) = 0 := by simp
  have hn := hp.continuousAt (x := (0 : ι → A)) |>.preimage_mem_nhds
    (h0 ▸ Iio_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  rw [nhds_pi, Filter.mem_pi'] at hn
  obtain ⟨s, U, hU, h⟩ := hn
  choose q hq hqU using fun i ↦ (PolynormableSpace.hasBasis_zero_ball ℂ A).mem_iff.mp (hU i)
  refine ⟨q, hq, fun f ↦ ?_⟩
  have hE (ε : ℝ) (hε : 0 < ε) : p (PiTensorProduct.tprod ℂ f) ≤ ∏ i, (q i (f i) + ε) := by
    let r (i : ι) := q i (f i) + ε
    have hr (i : ι) : 0 < r i := add_pos_of_nonneg_of_pos (apply_nonneg _ _) hε
    let g (i : ι) := ((r i : ℂ)⁻¹) • f i
    have hg (i : ι) : g i ∈ U i := by
      apply hqU i
      rw [Seminorm.mem_ball_zero]
      change q i ((r i : ℂ)⁻¹ • f i) < 1
      rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (hr i).le,
        inv_mul_lt_iff₀ (hr i), mul_one]
      exact lt_add_of_pos_right _ hε
    have hg' : p (PiTensorProduct.tprod ℂ g) < 1 := h (fun i _ ↦ hg i)
    have hf : f = fun i ↦ (r i : ℂ) • g i := by
      funext i
      exact (smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (hr i).ne') _).symm
    calc
      p (PiTensorProduct.tprod ℂ f) =
          (∏ i, r i) * p (PiTensorProduct.tprod ℂ g) := by
        conv_lhs => rw [hf, MultilinearMap.map_smul_univ, map_smul_eq_mul, norm_prod]
        congr 1
        exact Finset.prod_congr rfl fun i _ ↦ (Complex.norm_real _).trans (Real.norm_of_nonneg (hr i).le)
      _ ≤ _ := by simpa [r] using mul_le_mul_of_nonneg_left hg'.le (Finset.prod_nonneg fun i _ ↦ (hr i).le)
  have hT : Continuous (fun ε : ℝ ↦ ∏ i, (q i (f i) + ε)) :=
    continuous_finsetProd _ fun _ _ ↦ continuous_const.add continuous_id
  have ht : Tendsto (fun ε : ℝ ↦ ∏ i, (q i (f i) + ε)) (𝓝[>] 0) (𝓝 (∏ i, (q i (f i) + 0))) :=
    hT.continuousAt.mono_left inf_le_left
  exact (show p (PiTensorProduct.tprod ℂ f) ≤ ∏ i, (q i (f i) + 0) from
    ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with ε hε using hE ε hε)) |>.trans_eq (by simp)
/-- A bound on the pure tensors of seminormed spaces extends to their projective tensor seminorm. -/
private theorem archimedeanWeightedSchwartz_tensor_normed_bound
    {ι : Type*} [Fintype ι] {B : ι → Type*} [∀ i, SeminormedAddCommGroup (B i)] [∀ i, NormedSpace ℂ (B i)]
    (p : Seminorm ℂ (⨂[ℂ] i, B i)) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ f : ∀ i, B i, p (PiTensorProduct.tprod ℂ f) ≤ C * ∏ i, ‖f i‖) (x : ⨂[ℂ] i, B i) :
    p x ≤ C * ‖x‖ := by
  rw [PiTensorProduct.norm_def, Real.mul_iInf_of_nonneg hC]
  refine le_ciInf fun ⟨l, hl⟩ ↦ ?_
  change p x ≤ C * PiTensorProduct.projectiveSeminormAux l
  rw [← (PiTensorProduct.mem_lifts_iff x l).mp hl]
  unfold PiTensorProduct.projectiveSeminormAux
  induction l.toList with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, mul_add]
    refine (map_add_le_add p _ _).trans (add_le_add ?_ ih)
    rw [map_smul_eq_mul]
    exact (mul_le_mul_of_nonneg_left (hp a.2) (norm_nonneg a.1)).trans_eq (by ring)

/-- Continuous seminorms on the individual factors define a continuous projective seminorm on the
finite tensor. -/
private theorem archimedeanWeightedSchwartz_tensor_finite_bound
    {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalAddGroup (A i)]
    (q : ∀ i, Seminorm ℂ (A i)) (hq : ∀ i, Continuous (q i)) :
    ∃ r : Seminorm ℂ (FiniteProjectiveTensor A), Continuous r ∧
      ∀ (p : Seminorm ℂ (⨂[ℂ] i, A i)) {C : ℝ} (_ : 0 ≤ C),
        (∀ f, p (PiTensorProduct.tprod ℂ f) ≤ C * ∏ i, q i (f i)) → ∀ z, p z ≤ C * r z := by
  let B (i : ι) := ULift.{0} (A i)
  let e (i : ι) : B i ≃ₗ[ℂ] A i := ULift.moduleEquiv
  let q' (i : ι) := (q i).comp (e i).toLinearMap
  let (i : ι) : SeminormedAddCommGroup (B i) := (q' i).toAddGroupSeminorm.toSeminormedAddCommGroup
  let (i : ι) : TopologicalSpace (B i) := PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let (i : ι) : NormedSpace ℂ (B i) := ⟨fun c w ↦ (map_smul_eq_mul (q' i) c w).le⟩
  let E := PiTensorProduct.congr fun i ↦ (e i).symm
  let r := (normSeminorm ℂ (⨂[ℂ] i, B i)).comp E.toLinearMap
  have he (i : ι) : Continuous (e i).symm := by
    exact (norm_withSeminorms ℂ (B i)).continuous_of_continuous_comp (e i).symm.toLinearMap fun _ ↦ hq i
  have hc : Continuous (fun f : ∀ i, A i ↦ r (PiTensorProduct.tprod ℂ f)) := by
    have ht := (PiTensorProduct.tprodL ℂ (E := B)).cont.comp (continuous_pi fun i ↦ (he i).comp (continuous_apply i))
    exact ht.norm.congr fun f ↦ (congrArg norm (PiTensorProduct.congr_tprod _ f)).symm
  let fam := (fun p : {p : Seminorm ℂ (⨂[ℂ] i, A i) //
    Continuous (fun f : ∀ i, A i ↦ p (PiTensorProduct.tprod ℂ f))} ↦ p.val)
  refine ⟨r, (withGeneratingSeminorms_spec _ fam).continuous_seminorm ⟨r, hc⟩, ?_⟩
  intro p C hC hp z
  let p' := p.comp E.symm.toLinearMap
  have h (f : ∀ i, B i) : p' (PiTensorProduct.tprod ℂ f) ≤ C * ∏ i, ‖f i‖ := by
    change p (E.symm (PiTensorProduct.tprod ℂ f)) ≤ _
    rw [PiTensorProduct.congr_symm_tprod]
    exact hp _
  have hbound := archimedeanWeightedSchwartz_tensor_normed_bound p' hC h (E z)
  exact (show p' (E z) = p z from congrArg p (E.symm_apply_apply z)) ▸ hbound

/-- The projective tensor universal property applied to the identity gives joint continuity of
the pure tensor map. -/
private theorem archimedeanWeightedSchwartz_tensor_tmul_continuous
    (X Y : Type*) [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [PolynormableSpace ℂ X]
    [PolynormableSpace ℂ Y] [T2Space X] [T2Space Y] :
    @Continuous (X × Y) (ProjectiveTensor X Y) _ _ (fun v ↦ v.1 ⊗ₜ[ℂ] v.2) := by
  let : PolynormableSpace ℂ (ProjectiveTensor X Y) :=
    (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  exact (continuous_projectiveTensor_iff (LinearMap.id (R := ℂ) (M := ProjectiveTensor X Y))).mp
    continuous_id

/-- Splitting off one coordinate preserves the projective topology. To bound the inverse, apply the
finite projective seminorm to the remaining coordinates. -/
private theorem archimedeanWeightedSchwartz_tensor_split_coordinate.{uS}
    {ι : Type uS} {A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [PolynormableSpace ℂ A] [T2Space A] (i : ι)
    [T2Space (FiniteProjectiveTensor (fun _ : {j : ι // j ≠ i} ↦ A))]
    (hrest : @Continuous ({j : ι // j ≠ i} → A) (FiniteProjectiveTensor (fun _ : {j : ι // j ≠ i} ↦ A)) _ _ (PiTensorProduct.tprod ℂ)) :
    ∃ e : FiniteProjectiveTensor (fun _ : ι ↦ A) ≃L[ℂ]
        ProjectiveTensor (FiniteProjectiveTensor (fun _ : {j : ι // j ≠ i} ↦ A)) A,
      ∀ f : ι → A, e (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.tprod ℂ fun j : {j : ι // j ≠ i} ↦ f j.val) ⊗ₜ[ℂ] f i := by
  classical
  let J := {j : ι // j ≠ i}
  let T (I : Type uS) [Fintype I] := FiniteProjectiveTensor (fun _ : I ↦ A)
  let fam (I : Type uS) [Fintype I] := fun p : {p : Seminorm ℂ (⨂[ℂ] _ : I, A) //
    Continuous (fun f : I → A ↦ p (PiTensorProduct.tprod ℂ f))} ↦ p.val
  let split : J ⊕ Unit ≃ ι := Equiv.subtypeNeSumPUnit i
  let e₀ : (⨂[ℂ] _ : ι, A) ≃ₗ[ℂ] (⨂[ℂ] _ : J, A) ⊗[ℂ] A :=
    ((PiTensorProduct.reindex ℂ (s := fun _ : ι ↦ A) split.symm).trans
      (PiTensorProduct.tmulEquiv ℂ A).symm).trans
        (LinearEquiv.lTensor _ (PiTensorProduct.subsingletonEquiv ()))
  have he₀ (f : ι → A) : e₀ (PiTensorProduct.tprod ℂ f) =
      (PiTensorProduct.tprod ℂ fun j : J ↦ f j.val) ⊗ₜ[ℂ] f i := by
    simp [e₀, PiTensorProduct.reindex_tprod, PiTensorProduct.tmulEquiv_symm_apply,
      PiTensorProduct.subsingletonEquiv_apply_tprod, split, Equiv.subtypeNeSumPUnit]
  let e : T ι ≃ₗ[ℂ] ProjectiveTensor (T J) A := e₀
  have he (f : ι → A) : e (PiTensorProduct.tprod ℂ f) =
      (PiTensorProduct.tprod ℂ fun j : J ↦ f j.val) ⊗ₜ[ℂ] f i := he₀ f
  let : PolynormableSpace ℂ (T J) := (withGeneratingSeminorms_spec _ (fam J)).toPolynormableSpace
  let projectiveFamily := fun p : {p : Seminorm ℂ ((T J) ⊗[ℂ] A) //
    ContinuousAt (fun v : (T J) × A ↦ p (v.1 ⊗ₜ[ℂ] v.2)) 0} ↦ p.val
  have hprojective := withGeneratingSeminorms_spec _ projectiveFamily
  have hpure : Continuous (fun f : ι → A ↦ e (PiTensorProduct.tprod ℂ f)) := by
    refine ((archimedeanWeightedSchwartz_tensor_tmul_continuous (T J) A).comp ((hrest.comp (continuous_pi fun j ↦ continuous_apply j.val)).prodMk
      (continuous_apply i))).congr fun f ↦ (he f).symm
  have hc : Continuous e := hprojective.continuous_of_continuous_comp
    e.toLinearMap fun p ↦ (withGeneratingSeminorms_spec _ (fam ι)).continuous_seminorm
      ⟨p.val.comp e.toLinearMap, (hprojective.continuous_seminorm p).comp hpure⟩
  have : Nonempty ι := ⟨i⟩
  have : IsTopologicalAddGroup A := PolynormableSpace.isTopologicalAddGroup ℂ A
  have hd : Continuous e.symm := by
    refine (withGeneratingSeminorms_spec _ (fam ι)).continuous_of_continuous_comp e.symm.toLinearMap fun p ↦ ?_
    obtain ⟨q,hq,hpq⟩ := archimedeanWeightedSchwartz_tensor_pure_bound p.val p.property
    obtain ⟨r,hr,hpr⟩ := archimedeanWeightedSchwartz_tensor_finite_bound (fun j : J ↦ q j.val) (fun j ↦ hq j.val)
    have hbound (x : T J) (y : A) : p.val (e.symm (x ⊗ₜ[ℂ] y)) ≤ q i y * r x := by
      let u := e.symm.toLinearMap.comp ((TensorProduct.mk ℂ (T J) A).flip y)
      refine hpr (p.val.comp u) (apply_nonneg _ _) (fun f ↦ ?_) x
      let g := (Homeomorph.piSplitAt i (fun _ ↦ A)).symm (y, f)
      have hs := (Homeomorph.piSplitAt i (fun _ ↦ A)).apply_symm_apply (y,f)
      change (g i, fun j : J ↦ g j.val) = (y,f) at hs
      have he' := (e₀.symm_apply_apply (PiTensorProduct.tprod ℂ g)).symm.trans (congrArg e₀.symm (he₀ g))
      have hi : g i = y := congrArg Prod.fst hs
      have hj : (fun j : J ↦ g j.val) = f := congrArg Prod.snd hs
      rw [hi, hj] at he'
      change p.val (e.symm (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] y)) ≤ _
      refine ((congrArg p.val he').symm.trans_le (hpq g)).trans_eq ?_
      rw [Fintype.prod_eq_mul_prod_compl i, hi]
      congr 1
      exact (Finset.prod_subtype ({i}ᶜ : Finset ι) (p := fun j ↦ j ≠ i) (fun j ↦ by simp) (fun j ↦ q j (g j))).trans (Finset.prod_congr rfl (fun j _ ↦ congrArg (q j.val) (congrFun hj j)))
    refine hprojective.continuous_seminorm ⟨p.val.comp e.symm.toLinearMap, ?_⟩
    change ContinuousAt (fun z : T J × A ↦ p.val (e.symm (z.1 ⊗ₜ[ℂ] z.2))) 0
    have hz : p.val (e.symm (((0 : T J × A).1) ⊗ₜ[ℂ] (0 : T J × A).2)) = 0 :=
      ((congrArg (fun z ↦ p.val (e.symm z)) (TensorProduct.zero_tmul (T J) (0 : A))).trans
        (congrArg p.val e.symm.map_zero)).trans (map_zero p.val)
    rw [ContinuousAt, hz]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ ↦ 0)
      (h := fun z ↦ q i z.2 * r z.1)
    · exact tendsto_const_nhds
    · have hT : Continuous (fun z : T J × A ↦ q i z.2 * r z.1) :=
        ((hq i).comp continuous_snd).mul (hr.comp continuous_fst)
      simpa [ContinuousAt, Function.comp_def] using hT.continuousAt (x := (0 : T J × A))
    · exact Eventually.of_forall fun z ↦ apply_nonneg _ _
    · exact Eventually.of_forall fun z ↦ hbound z.1 z.2
  exact ⟨⟨e,hc,hd⟩,he⟩

/-- For nuclear factors embedded by families of Schwartz tests, tensoring their coordinates and
applying the ordinary Schwartz kernel theorem yields an embedding on the product. -/
private theorem archimedeanWeightedSchwartz_tensor_kernel_coordinates
    {G H A B I J : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    (hN : @IsHomeomorph (ProjectiveTensor A B) (InjectiveTensor A B) _ _ id)
    (hG : IsFrechetTVS (SchwartzBruhat G)) (hH : IsFrechetTVS (SchwartzBruhat H))
    (t : A →L[ℂ] (I → SchwartzBruhat G)) (u : B →L[ℂ] (J → SchwartzBruhat H))
    (ht : IsEmbedding t) (hu : IsEmbedding u) :
    ∃ L : ProjectiveTensor A B →L[ℂ] (I × J → SchwartzBruhat (G × H)), IsEmbedding L ∧
      ∀ a b i j x y, L (a ⊗ₜ[ℂ] b) (i,j) (x,y) = (t a i x) * (u b j y) := by
  let X := SchwartzBruhat G
  let Y := SchwartzBruhat H
  let Z := SchwartzBruhat (G × H)
  let : PolynormableSpace ℂ X := (schwartzBruhat_nuclear.{0} (G := G)).2.1
  let : PolynormableSpace ℂ Y := (schwartzBruhat_nuclear.{0} (G := H)).2.1
  let : T2Space X := schwartzBruhat_t2
  let : T2Space Y := schwartzBruhat_t2
  let E₁ := InjectiveTensor (I → X) (J → Y)
  let E₂ := InjectiveTensor X Y
  let D := InductiveTensor X Y
  have hp := (schwartzBruhat_nuclear (G := G)).tensorComparison (Y := Y)
  have hd := inductiveTensor_to_projectiveTensor_of_frechet hG hH
  have hi : @IsInducing E₂ D _ _ id := by
    let ex : D ≃ E₂ := Equiv.refl _
    let hx : D ≃ₜ E₂ := ex.toHomeomorphOfIsInducing (hp.isInducing.comp hd.isInducing)
    exact hx.symm.isInducing
  obtain ⟨K,hK⟩ := schwartzBruhat_kernel_equiv (G := G) (H := H)
  let : ContinuousSMul ℂ D := (withGeneratingSeminorms_spec _ _).continuousSMul
  let : UniformContinuousConstSMul ℂ D := uniformContinuousConstSMul_of_continuousConstSMul ℂ D
  let incl : D →L[ℂ] UniformSpace.Completion D := UniformSpace.Completion.toComplL
  let k : E₂ →ₗ[ℂ] Z := K.toLinearMap.comp (show E₂ →ₗ[ℂ] UniformSpace.Completion D from incl.toLinearMap)
  have hk : IsInducing k := K.toHomeomorph.isInducing.comp
    ((UniformSpace.Completion.isUniformInducing_coe D).isInducing.comp hi)
  let T : InjectiveTensor A B →ₗ[ℂ] E₁ := injectiveTensorMap t.toLinearMap u.toLinearMap
  let V (p : I × J) : E₁ →ₗ[ℂ] E₂ := injectiveTensorMap (LinearMap.proj p.1) (LinearMap.proj p.2)
  have hT := injectiveTensorMap_isEmbedding t u ht hu
  have hV : IsInducing (fun z : E₁ ↦ fun p : I × J ↦ V p z) := by
    let inc (w : I × J → E₂) := fun p ↦ (w p : UniformSpace.Completion E₂)
    have hinc : IsInducing inc := IsInducing.piMap fun _ : I × J ↦
      (UniformSpace.Completion.isUniformInducing_coe E₂).isInducing
    apply (IsInducing.of_comp_iff hinc).mp
    have hfull := (completedInjectiveTensor_products (fun _ : I ↦ X) (fun _ : J ↦ Y)).isInducing.comp
      (UniformSpace.Completion.isUniformInducing_coe E₁).isInducing
    convert hfull using 1
    funext z p
    have hc : Continuous (V p) := injectiveTensorMap_continuous
      (ContinuousLinearMap.proj p.1 : (I → X) →L[ℂ] X) (ContinuousLinearMap.proj p.2 : (J → Y) →L[ℂ] Y)
    exact (UniformSpace.Completion.map_coe
      ((V p).toAddMonoidHom.uniformContinuous_of_continuousAt_zero hc.continuousAt) z).symm
  let L : ProjectiveTensor A B →ₗ[ℂ] (I × J → Z) := LinearMap.pi fun p ↦
    (k.comp (V p)).comp (show ProjectiveTensor A B →ₗ[ℂ] E₁ from T)
  have hL : IsInducing L := (IsInducing.piMap (fun _ : I × J ↦ hk)).comp
    (hV.comp (hT.isInducing.comp hN.isInducing))
  let : T2Space (ProjectiveTensor A B) := hN.isEmbedding.t2Space
  refine ⟨⟨L,hL.continuous⟩,hL.isEmbedding,fun a b i j x y ↦ ?_⟩
  exact hK (t a i) (u b j) x y

/-- When the trivial subgroup is a Bruhat stage, the one-place twists induce the topology for any
nonempty set of weights. The inverse on their image reconstructs that stage. -/
private theorem archimedeanWeightedSchwartz_tensor_one_place_embedding
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)
    (hne : I.Nonempty) (hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G)) :
    IsEmbedding (fun (f : ModulatedExponentialDecay m I) (a : I) ↦
      modulatedExponentialDecayTwist m I a f) := by
  let E := ModulatedExponentialDecay m I
  let X := SchwartzBruhat G
  let Y := I → X
  let t : E →ₗ[ℂ] Y := LinearMap.pi (modulatedExponentialDecayTwist m I)
  have ht : Continuous t := continuous_pi fun a ↦ continuous_decay_twist m I a
  obtain ⟨a, ha⟩ := hne
  have hti : Injective t := fun f g h ↦ decay_twist_injective m I ⟨a, ha⟩ (congrFun h ⟨a, ha⟩)
  let k : {k : Subgroup G // IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)} :=
    ⟨⊥, by simpa only [Subgroup.coe_bot] using isCompact_singleton (x := (1 : G)), hgood.2.2⟩
  let P := ModulatedExponentialDecayStage m I k
  let j : P →ₗ[ℂ] E := modulatedExponentialDecayStageInclusion m I k
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp j (fun p ↦ p.property k)
  have hjs : Surjective j := by
    intro f
    apply ((modulatedExponentialDecayStageInclusion_range m I k).2 f).mpr
    intro g u
    have h : (u : G) = 1 := u.property
    rw [h, mul_one]
  let ej := LinearEquiv.ofBijective j ⟨(modulatedExponentialDecayStageInclusion_range m I k).1, hjs⟩
  let et := LinearEquiv.ofInjective t hti
  let v : (G ⧸ k.val) ≃ₜ* G :=
    { QuotientGroup.quotientBot with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_id
      continuous_invFun := QuotientGroup.continuous_mk }
  obtain ⟨pull, hp⟩ := exists_schwartzBruhat_pullback v
  let R (y : t.range) := ej.symm (et.symm y)
  have hR : Continuous R := by
    refine (modulatedExponentialDecayStage_twists_isInducing m I k).continuous_iff.mpr (continuous_pi fun b ↦ ?_)
    apply (pull.continuous.comp ((continuous_apply b).comp continuous_subtype_val)).congr
    intro y
    apply Subtype.ext
    funext q
    refine QuotientGroup.induction_on q fun g ↦ ?_
    have h : t (j (R y)) = y.val := (congrArg t (ej.apply_symm_apply (et.symm y))).trans
      (congrArg Subtype.val (et.apply_symm_apply y))
    have hy := congrArg (fun w : Y ↦ w b g) h
    exact (hp (y.val b) _).trans hy.symm
  have hi : IsEmbedding (fun f : E ↦ et f) := Function.LeftInverse.isEmbedding
    (g := fun f : E ↦ et f) (f := j ∘ R) (fun f ↦ (ej.apply_symm_apply _).trans (et.symm_apply_apply f))
    (hj.comp hR) (ht.subtype_mk _)
  exact IsEmbedding.subtypeVal.comp hi

/-- Over the empty set of factors the pure tensor is one and the projective topology is the scalar
topology. -/
private theorem archimedeanWeightedSchwartz_tensor_empty
    {ι A : Type*} [Fintype ι] [IsEmpty ι] [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] :
    ∃ e : FiniteProjectiveTensor (fun _ : ι ↦ A) ≃L[ℂ] ℂ, ∀ f, e (PiTensorProduct.tprod ℂ f) = 1 := by
  let X := ⨂[ℂ] _ : ι, A
  let P := fun p : {p : Seminorm ℂ X // Continuous (fun f : ι → A ↦ p (PiTensorProduct.tprod ℂ f))} ↦ p.val
  let l : WithGeneratingSeminorms X P ≃ₗ[ℂ] ℂ := PiTensorProduct.isEmptyEquiv ι
  have hP := withGeneratingSeminorms_spec X P
  have : ContinuousSMul ℂ (WithGeneratingSeminorms X P) := hP.continuousSMul
  have hl : Continuous l := by
    let q : Seminorm ℂ X := (normSeminorm ℂ ℂ).comp (PiTensorProduct.isEmptyEquiv ι).toLinearMap
    have hq : Continuous (fun f : ι → A ↦ q (PiTensorProduct.tprod ℂ f)) := continuous_of_discreteTopology
    refine WithSeminorms.continuous_normedSpace_rng ℂ hP l.toLinearMap
      ⟨{⟨q, hq⟩}, 1, Seminorm.le_def.mpr fun x ↦ ?_⟩
    have hx : (({⟨q, hq⟩} : Finset _).sup P) x = q x :=
      congrArg (fun p : Seminorm ℂ X ↦ p x) Finset.sup_singleton
    exact le_of_eq (hx.symm.trans (one_smul ℝ≥0 _).symm)
  have hl' : Continuous l.symm := by
    have eqn : (l.symm : ℂ → WithGeneratingSeminorms X P) = fun c ↦ c • l.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [eqn]
    fun_prop
  exact ⟨⟨l, hl, hl'⟩, PiTensorProduct.isEmptyEquiv_apply_tprod ι⟩

/-- Iterating the binary coordinate embedding realizes the finite projective tensor in the Schwartz
spaces on the product group. -/
private theorem archimedeanWeightedSchwartz_tensor_finite_coordinates.{uS}
    {G A W : Type} [TopologicalSpace W] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    (t : A →L[ℂ] (W → SchwartzBruhat G)) (ht : IsEmbedding t)
    (hG : IsFrechetTVS (SchwartzBruhat G))
    (hprod : ∀ (K : Type uS) [Fintype K], IsFrechetTVS (SchwartzBruhat (K → G)))
    (hempty : ∀ (K : Type uS) [IsEmpty K], ∃ L : ℂ →L[ℂ] SchwartzBruhat (K → G),
      IsEmbedding L ∧ ∀ c u, L c u = c)
    (ι : Type uS) [Fintype ι] :
    @Continuous (ι → A) (FiniteProjectiveTensor (fun _ : ι ↦ A)) _ _ (PiTensorProduct.tprod ℂ) ∧
      ∃ L : FiniteProjectiveTensor (fun _ : ι ↦ A) →L[ℂ] ((ι → W) → SchwartzBruhat (ι → G)),
        IsEmbedding L ∧ ∀ f w u, L (PiTensorProduct.tprod ℂ f) w u = ∏ i, t (f i) (w i) (u i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    obtain ⟨e,he⟩ := archimedeanWeightedSchwartz_tensor_empty (ι := ι) (A := A)
    obtain ⟨k,hk,hv⟩ := hempty ι
    let L := ContinuousLinearMap.pi fun _ : ι → W ↦ k.comp e.toContinuousLinearMap
    have hc : Continuous L := L.continuous
    let w₀ : ι → W := isEmptyElim
    have hi : IsInducing L := IsInducing.of_comp hc (continuous_apply w₀) (hk.isInducing.comp e.toHomeomorph.isInducing)
    have hli : Injective L := fun _ _ hxy ↦ e.injective (hk.injective (congrFun hxy w₀))
    refine ⟨continuous_of_discreteTopology, L, ⟨hi,hli⟩, fun f w u ↦ ?_⟩
    exact (hv _ _).trans ((he f).trans (by simp))
  | inr h =>
    obtain ⟨i⟩ := h
    let J := {j : ι // j ≠ i}
    obtain ⟨hc,L,hL,hv⟩ := archimedeanWeightedSchwartz_tensor_finite_coordinates t ht hG hprod hempty J
    let T := FiniteProjectiveTensor (fun _ : J ↦ A)
    let : PolynormableSpace ℂ T := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
    let : T2Space (SchwartzBruhat (J → G)) := schwartzBruhat_t2
    let : T2Space T := hL.t2Space
    obtain ⟨e,he⟩ := archimedeanWeightedSchwartz_tensor_split_coordinate i hc
    have hN : IsNuclearTVS.{0} T := isNuclearTVS_of_linearEmbedding L.toLinearMap hL
      (isNuclearTVS_pi fun _ : J → W ↦ schwartzBruhat_nuclear (G := J → G))
    obtain ⟨K,hK,hKv⟩ := archimedeanWeightedSchwartz_tensor_kernel_coordinates hN.tensorComparison (hprod J) hG L t hL ht
    let d : (ι → G) ≃ₜ* ((J → G) × G) :=
      { (Homeomorph.piSplitAt i (fun _ ↦ G)).trans (Homeomorph.prodComm _ _) with map_mul' := fun _ _ ↦ rfl }
    let l := schwartzBruhatPullbackEquiv d
    let w : (ι → W) ≃ₜ ((J → W) × W) := (Homeomorph.piSplitAt i (fun _ ↦ W)).trans (Homeomorph.prodComm _ _)
    let D := ContinuousLinearMap.pi fun a : ι → W ↦ l.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj (R := ℂ) (w a)).comp (K.comp e.toContinuousLinearMap))
    have hik : IsInducing (fun f : ((J → W) × W → SchwartzBruhat (ι → G)) ↦ f ∘ w) :=
      (Function.LeftInverse.isEmbedding (f := fun f : (ι → W) → SchwartzBruhat (ι → G) ↦ f ∘ w.symm)
        (g := fun f : ((J → W) × W) → SchwartzBruhat (ι → G) ↦ f ∘ w)
        (fun f ↦ funext fun p ↦ congrArg f (w.apply_symm_apply p))
        (continuous_pi fun p ↦ continuous_apply (w.symm p))
        (continuous_pi fun a ↦ continuous_apply (w a))).isInducing
    have hpi := (IsInducing.piMap fun _ : (J → W) × W ↦ l.toHomeomorph.isInducing)
    have hi : IsInducing D := hik.comp (hpi.comp (hK.isInducing.comp e.toHomeomorph.isInducing))
    let : T2Space (SchwartzBruhat ((J → G) × G)) := schwartzBruhat_t2
    let : T2Space (FiniteProjectiveTensor (fun _ : ι ↦ A)) := (hK.comp e.toHomeomorph.isEmbedding).t2Space
    have hcp : @Continuous (ι → A) (ProjectiveTensor T A) _ _ (fun f ↦ e (PiTensorProduct.tprod ℂ f)) := by
      exact ((archimedeanWeightedSchwartz_tensor_tmul_continuous T A).comp
        ((hc.comp (continuous_pi fun j ↦ continuous_apply j.val)).prodMk (continuous_apply i))).congr fun f ↦ (he f).symm
    refine ⟨e.toHomeomorph.isInducing.continuous_iff.mpr hcp, D, hi.isEmbedding, fun f a u ↦ ?_⟩
    change K (e (PiTensorProduct.tprod ℂ f)) (w a) (d u) = _
    rw [he]
    refine (hKv (PiTensorProduct.tprod ℂ fun j : J ↦ f j.val) (f i)
      (fun j : J ↦ a j.val) (a i) (fun j : J ↦ u j.val) (u i)).trans ?_
    rw [hv, Fintype.prod_eq_mul_prod_compl i, mul_comm]
    congr 1
    exact (Finset.prod_subtype ({i}ᶜ : Finset ι) (p := fun j ↦ j ≠ i)
      (fun j ↦ by simp) (fun j ↦ t (f j) (a j) (u j))).symm
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- A finite power of a compactly generated group with an open Euclidean chart
is again elementary: compact generating neighborhoods and charts both multiply. -/
private theorem archimedeanWeightedSchwartz_finite_unweighted_frechet {ι G V : Type*}
    [Fintype ι] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hG : IsCompactlyGeneratedGroup G) (v : G → V) (hv : IsOpenEmbedding v) :
    IsFrechetTVS (SchwartzBruhat (ι → G)) := by
  classical
  obtain ⟨U,hU,hc,hg⟩ := hG
  have hpi : IsCompactlyGeneratedGroup (ι → G) := by
    refine ⟨univ.pi (fun _ ↦ U), ?_, isCompact_univ_pi (fun _ ↦ hc), ?_⟩
    · apply set_pi_mem_nhds finite_univ
      exact fun i _ ↦ hU
    · rw [Subgroup.closure_pi (fun _ ↦ mem_of_mem_nhds hU)]
      simp only [hg, Subgroup.pi_top]
  let n := Module.finrank ℝ (ι → V)
  let e : (ι → V) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let q := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm
  exact schwartzBruhat_frechet_of_elementary hpi ⟨n,
    ⟨((e.trans q).toHomeomorph.isOpenEmbedding.comp (IsOpenEmbedding.piMap (fun _ : ι ↦ hv))).singletonChartedSpace⟩⟩

private theorem archimedeanWeightedSchwartz_real_unweighted_frechet (ι : Type*) [Fintype ι] :
    IsFrechetTVS (SchwartzBruhat (ι → ℝˣ)) := by
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  have h := realCoordinate_mul_allExponentialDecay_modulation
  exact archimedeanWeightedSchwartz_finite_unweighted_frechet
    (compactlyGenerated_of_surjective_modulation _ h.1 h.2) _ (Units.isOpenEmbedding_val (R := ℝ))

private theorem archimedeanWeightedSchwartz_complex_unweighted_frechet (ι : Type*) [Fintype ι] :
    IsFrechetTVS (SchwartzBruhat (ι → ℂˣ)) := by
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have h := complexCoordinate_mul_allExponentialDecay_modulation
  exact archimedeanWeightedSchwartz_finite_unweighted_frechet
    (compactlyGenerated_of_surjective_modulation _ h.1 h.2) _ (Units.isOpenEmbedding_val (R := ℂ))

/-- On a one-point group, the constant functions identify Schwartz space with the scalars. -/
private theorem archimedeanWeightedSchwartz_subsingleton_equiv {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Subsingleton G] :
    ∃ e : ℂ ≃L[ℂ] SchwartzBruhat G, ∀ c x, e c x = c := by
  let : CompactSpace G := Finite.compactSpace
  obtain ⟨u,hu⟩ := compact_schwartzBruhat_one (H := G)
  let M : ℂ →L[ℂ] SchwartzBruhat G := (ContinuousLinearMap.id ℂ ℂ).smulRight u
  let E : SchwartzBruhat G →L[ℂ] ℂ :=
    ⟨(LinearMap.proj 1).comp (schwartzBruhatSubmodule G).subtype, continuous_schwartzBruhat_eval_forEndpoints 1⟩
  have hv (c : ℂ) (x : G) : M c x = c := by
    change c * u x = c
    rw [hu, mul_one]
  have hEM (c : ℂ) : E (M c) = c := hv c 1
  have hME (g : SchwartzBruhat G) : M (E g) = g :=
    Subtype.ext (funext fun x ↦ (hv (E g) x).trans (congrArg g (Subsingleton.elim 1 x)))
  exact ⟨ContinuousLinearEquiv.equivOfInverse M E hEM hME, hv⟩

/-- The punctured complex plane is an open real Euclidean chart. -/
private theorem archimedeanWeightedSchwartz_complex_trivial_good :
    IsBruhatGoodSubgroup (⊥ : Subgroup ℂˣ) := by
  let e := (stdOrthonormalBasis ℝ ℂ).repr
  exact isBruhatGoodSubgroup_bot_iff.mpr ⟨_, ⟨(e.toHomeomorph.isOpenEmbedding.comp
    (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩

private theorem archimedeanWeightedSchwartz_real_factor_unweighted_frechet :
    IsFrechetTVS (SchwartzBruhat ℝˣ) := by
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  have h := realCoordinate_mul_allExponentialDecay_modulation
  exact schwartzBruhat_frechet_of_elementary (compactlyGenerated_of_surjective_modulation _ h.1 h.2)
    (isBruhatGoodSubgroup_bot_iff.mp realCoordinate_mul_exponentialDecay_good)

private theorem archimedeanWeightedSchwartz_complex_factor_unweighted_frechet :
    IsFrechetTVS (SchwartzBruhat ℂˣ) := by
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have h := complexCoordinate_mul_allExponentialDecay_modulation
  exact schwartzBruhat_frechet_of_elementary (compactlyGenerated_of_surjective_modulation _ h.1 h.2)
    (isBruhatGoodSubgroup_bot_iff.mp archimedeanWeightedSchwartz_complex_trivial_good)

/-- Two linear maps on the tensor product agree if they agree on the separate products. -/
private theorem archimedeanWeightedSchwartz_tensor_ext {ι κ R C Z : Type*}
    [Fintype ι] [Fintype κ] [AddCommGroup R] [Module ℂ R] [AddCommGroup C] [Module ℂ C]
    [AddCommGroup Z] [Module ℂ Z]
    (V P : (⨂[ℂ] _ : ι, R) ⊗[ℂ] (⨂[ℂ] _ : κ, C) →ₗ[ℂ] Z)
    (h : ∀ f g, V ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ g)) =
      P ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ g))) : V = P := by
  have hright (f : ι → R) (y : ⨂[ℂ] _ : κ, C) : V ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] y) = P ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] y) := by
    induction y using PiTensorProduct.induction_on with
    | smul_tprod b g => simp only [TensorProduct.tmul_smul, map_smul, h]
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  apply TensorProduct.ext'
  intro x y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod b f => simp only [← TensorProduct.smul_tmul', map_smul, hright]
  | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]

set_option maxHeartbeats 600000 in
/-- The topology estimate in Lemma 5.3.3.3(2), p. 252: the projective
tensor topology is induced by its maps to the unweighted Schwartz space, one for
each tuple of exponents. This is an estimate on the algebraic tensor only. -/
private theorem archimedeanWeightedSchwartz_tensor_twists {I : Set ℝ} (ho : IsOpen I)
    (hi : OrdConnected I) (hne : I.Nonempty) (L : productTensor(I) →ₗ[ℂ] 𝓦(I))
    (hL : ∀ (f : ι → realFactors(I)) (g : κ → complexFactors(I)) (u : archMul(ι, κ)),
      (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u = separateValue(f, g, u)) :
    IsInducing (fun z a ↦ archimedeanSchwartzTwist I a (L z)) := by
  classical
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let J := insert 0 I
  let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
  let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
  let A := FiniteProjectiveTensor (fun _ : ι ↦ R)
  let B := FiniteProjectiveTensor (fun _ : κ ↦ C)
  let W := ((ι → J) × (κ → J))
  let S := SchwartzBruhat ((ι → ℝˣ) × (κ → ℂˣ))
  have hne : J.Nonempty := ⟨0, Set.mem_insert _ _⟩
  let r : R →L[ℂ] (J → SchwartzBruhat ℝˣ) := ContinuousLinearMap.pi fun a ↦
    ⟨modulatedExponentialDecayTwist (archimedeanUnitModulation ℝ 1) J a, continuous_decay_twist _ J a⟩
  let c : C →L[ℂ] (J → SchwartzBruhat ℂˣ) := ContinuousLinearMap.pi fun a ↦
    ⟨modulatedExponentialDecayTwist (archimedeanUnitModulation ℂ 2) J a, continuous_decay_twist _ J a⟩
  have hr : IsEmbedding r := archimedeanWeightedSchwartz_tensor_one_place_embedding _ J hne realCoordinate_mul_exponentialDecay_good
  have hc : IsEmbedding c := archimedeanWeightedSchwartz_tensor_one_place_embedding _ J hne archimedeanWeightedSchwartz_complex_trivial_good
  let : T2Space (SchwartzBruhat ℝˣ) := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat ℂˣ) := schwartzBruhat_t2
  let : T2Space R := hr.t2Space
  let : T2Space C := hc.t2Space
  let : PolynormableSpace ℂ R := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ C := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  have realCoordinates := archimedeanWeightedSchwartz_tensor_finite_coordinates (G := ℝˣ) (A := R) (W := J) r hr archimedeanWeightedSchwartz_real_factor_unweighted_frechet
    archimedeanWeightedSchwartz_real_unweighted_frechet
    (fun K _ ↦ (archimedeanWeightedSchwartz_subsingleton_equiv (G := K → ℝˣ)).elim
      fun e he ↦ ⟨e.toContinuousLinearMap, e.toHomeomorph.isEmbedding, he⟩) ι
  let F := realCoordinates.2.choose
  have hF := realCoordinates.2.choose_spec.1
  have hFv := realCoordinates.2.choose_spec.2
  have complexCoordinates := archimedeanWeightedSchwartz_tensor_finite_coordinates (G := ℂˣ) (A := C) (W := J) c hc archimedeanWeightedSchwartz_complex_factor_unweighted_frechet
    archimedeanWeightedSchwartz_complex_unweighted_frechet
    (fun K _ ↦ (archimedeanWeightedSchwartz_subsingleton_equiv (G := K → ℂˣ)).elim
      fun e he ↦ ⟨e.toContinuousLinearMap, e.toHomeomorph.isEmbedding, he⟩) κ
  let D := complexCoordinates.2.choose
  have hD := complexCoordinates.2.choose_spec.1
  have hDv := complexCoordinates.2.choose_spec.2
  let : T2Space (SchwartzBruhat (ι → ℝˣ)) := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat (κ → ℂˣ)) := schwartzBruhat_t2
  let : PolynormableSpace ℂ A := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : PolynormableSpace ℂ B := (withGeneratingSeminorms_spec _ _).toPolynormableSpace
  let : T2Space A := hF.t2Space
  let : T2Space B := hD.t2Space
  have hComparison : @IsHomeomorph (ProjectiveTensor A B) (InjectiveTensor A B) _ _ id :=
    (isNuclearTVS_of_linearEmbedding F.toLinearMap hF
      (isNuclearTVS_pi fun _ : ι → J ↦ schwartzBruhat_nuclear (G := ι → ℝˣ))).tensorComparison
  have bothCoordinates := archimedeanWeightedSchwartz_tensor_kernel_coordinates (A := A) (B := B) (G := ι → ℝˣ) (H := κ → ℂˣ)
    (I := ι → J) (J := κ → J) hComparison
    (archimedeanWeightedSchwartz_real_unweighted_frechet ι)
    (archimedeanWeightedSchwartz_complex_unweighted_frechet κ) F D hF hD
  let P := bothCoordinates.choose
  have hP := bothCoordinates.choose_spec.1
  have hPv := bothCoordinates.choose_spec.2
  let V : ProjectiveTensor A B →ₗ[ℂ] (W → S) := LinearMap.pi fun a ↦ (archimedeanSchwartzTwist I a).comp L
  have h0 (f : ι → R) (g : κ → C) :
      V ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ g)) =
        P ((PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ g)) := by
    funext a
    apply Subtype.ext
    funext u
    refine ((archimedeanSchwartzTwist_apply I a _ u).trans ?_).trans
      (hPv (PiTensorProduct.tprod ℂ f) (PiTensorProduct.tprod ℂ g) a.1 a.2 u.1 u.2).symm
    refine (congrArg (fun z : ℂ ↦ ((∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ) : ℝ) : ℂ) *
      ((∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ) : ℝ) : ℂ) * z) (hL f g u)).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) (hFv f a.1 u.1) (hDv g a.2 u.2)).symm
    have hR (i : ι) : r (f i) (a.1 i) (u.1 i) =
        ((‖(u.1 i).val‖ ^ (a.1 i : ℝ) : ℝ) : ℂ) * (f i).val (u.1 i) := by
      change (modulatedExponentialDecayTwist (archimedeanUnitModulation ℝ 1) J (a.1 i) (f i)).val (u.1 i) = _
      simpa only [archimedeanUnitModulation_apply, pow_one] using
        modulatedExponentialDecayTwist_apply (archimedeanUnitModulation ℝ 1) J (a.1 i) (f i) (u.1 i)
    have hC (j : κ) : c (g j) (a.2 j) (u.2 j) =
        (((‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ) : ℝ) : ℂ) * (g j).val (u.2 j) := by
      change (modulatedExponentialDecayTwist (archimedeanUnitModulation ℂ 2) J (a.2 j) (g j)).val (u.2 j) = _
      simpa only [archimedeanUnitModulation_apply] using
        modulatedExponentialDecayTwist_apply (archimedeanUnitModulation ℂ 2) J (a.2 j) (g j) (u.2 j)
    simp only [hR,hC,Finset.prod_mul_distrib,Complex.ofReal_prod]
    ring
  have he : V = P.toLinearMap := archimedeanWeightedSchwartz_tensor_ext V P.toLinearMap h0
  exact (show IsInducing V from he ▸ hP.isInducing)


/-- The sum of two twists of a decay function has dense range in the unweighted
Schwartz space, even when the allowed exponents are disconnected. In logarithmic
coordinates divide compact test profiles by the sum of the two exponential weights. -/
private theorem archimedeanWeightedSchwartz_dense_factor {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hs : Surjective m) (J : Set ℝ) (a b : J) :
    DenseRange (modulatedExponentialDecayTwist m J a + modulatedExponentialDecayTwist m J b) := by
  classical
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let σ := hm.exists_section.choose
  let τ : ℝ≥0ˣ →ₜ* G := σ.comp
    ⟨MonoidHom.codRestrict (MonoidHom.id _) m.toMonoidHom.range (fun t ↦ hs t), continuous_id.subtype_mk _⟩
  have hτ : RightInverse τ m := fun t ↦ hm.exists_section.choose_spec ⟨t, hs t⟩
  obtain ⟨d, hd⟩ := hm.exists_sectionEquiv τ hτ
  obtain ⟨e, he⟩ := split_schwartz_kernel d
  obtain ⟨v, hv⟩ := schwartzBruhat_realCoordinate_equiv positiveRealLogEquiv
  let D := {f : SchwartzMap ℝ ℂ | HasCompactSupport (f : ℝ → ℂ)}
  have hD : Dense (v '' D) := v.surjective.denseRange.dense_image v.continuous SchwartzMap.dense_hasCompactSupport
  let T := modulatedExponentialDecayTwist m J a + modulatedExponentialDecayTwist m J b
  refine dense_of_split_products e T.range hD ?_
  rintro h _ ⟨f,hf,rfl⟩
  let au : (univ : Set ℝ) := ⟨a, mem_univ _⟩
  let bu : (univ : Set ℝ) := ⟨b, mem_univ _⟩
  obtain ⟨g, hg⟩ := compact_profile_sum_twists univ au bu f hf
  obtain ⟨z,hz⟩ := split_pure_decay_mem m univ hm ordConnected_univ univ_nonempty τ hτ h g
  let y : modulatedExponentialDecaySubmodule m J := ⟨z.val,
    (Submodule.mem_iInf _).mpr fun c ↦ Submodule.mem_comap.mpr
      (modulationWeight_mem_schwartzBruhat m univ ⟨c, mem_univ _⟩ z)⟩
  refine ⟨y, Subtype.ext (funext fun u ↦ ?_)⟩
  obtain ⟨⟨k,t⟩,rfl⟩ := d.surjective u
  have hmt (k : K) (t : ℝ≥0ˣ) : m (d (k,t)) = t := by
    rw [hd, map_mul, show m k.val = 1 from k.property, hτ, one_mul]
  have hz' : z.val (d (k,t)) = h k * g.val (Real.log (t.val : ℝ)) := (congrArg z.val (hd _)).trans (hz k t)
  change modulatedExponentialDecayTwist m J a y (d (k,t)) + modulatedExponentialDecayTwist m J b y (d (k,t)) = _
  rw [modulatedExponentialDecayTwist_apply, modulatedExponentialDecayTwist_apply, hmt, he, hv]
  change _ * z.val (d (k,t)) + _ * z.val (d (k,t)) = h k * f (positiveRealLogEquiv t).toAdd
  rw [hz', ← add_mul, mul_left_comm, ← Complex.ofReal_add, identityWeight_log, identityWeight_log,
    positiveRealLogEquiv_apply]
  exact congrArg (h k * ·) (hg _)

/-- A finite box of requested weights factors through the sum of the corner
twists. Its pointwise multiplier is the product of sums of the endpoint weights. -/
private theorem archimedeanWeightedSchwartz_endpoint_box {δ G E : Type*} [Fintype δ]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] (J : Set ℝ) (m : δ → G →ₜ* ℝ≥0ˣ)
    (t : (δ → J) → E →ₗ[ℂ] SchwartzBruhat G) (v : E → G → ℂ)
    (ht : ∀ a f x, t a f x = (∏ i, (((m i x).val : ℝ) ^ (a i : ℝ) : ℝ) : ℂ) * v f x)
    (a b : δ → J) :
    let w (i : δ) (k : J) (x : G) : ℂ := (((m i x).val : ℝ) ^ (k : ℝ) : ℝ)
    ∃ L : E →ₗ[ℂ] SchwartzBruhat G,
      (∀ f x, L f x = (∏ i, (w i (a i) x + w i (b i) x)) * v f x) ∧
      ∀ c : δ → J, (∀ i, a i ≤ c i) → (∀ i, c i ≤ b i) →
        ∃ R : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f, R (L f) = t c f := by
  classical
  intro w
  let p (i : δ) (j : Bool) := if j then b i else a i
  let L : E →ₗ[ℂ] SchwartzBruhat G := ∑ s : δ → Bool, t (fun i ↦ p i (s i))
  have hL (f : E) (x : G) : L f x = (∏ i, (w i (a i) x + w i (b i) x)) * v f x := by
    let ev : SchwartzBruhat G →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
    change ev (L f) = _
    simp only [L, LinearMap.sum_apply, map_sum]
    change (∑ s : δ → Bool, t (fun i ↦ p i (s i)) f x) = _
    simp_rw [ht]
    rw [← Finset.sum_mul]
    congr 1
    change (∑ s : δ → Bool, ∏ i, w i (p i (s i)) x) = _
    rw [← Fintype.prod_sum (fun i (j : Bool) ↦ w i (p i j) x)]
    simp [p, add_comm]
  refine ⟨L, hL, fun c hac hcb ↦ ?_⟩
  let φ (i : δ) (z : ℝ) : ℂ :=
    ((Real.exp (-((c i : ℝ) - a i) * z) + Real.exp (((b i : ℝ) - c i) * z))⁻¹ : ℝ)
  let r (i : δ) (x : G) := φ i (Real.log ((m i x).val : ℝ))
  have hsingle (i : δ) := twoSidedExpWeight_bounds_of_nonneg (sub_nonneg.mpr (hac i) : 0 ≤ (c i : ℝ) - a i)
    (sub_nonneg.mpr (hcb i) : 0 ≤ (b i : ℝ) - c i)
  have hm (i : δ) := logModulation_mul_schwartzBruhat_continuousLinear (φ := φ i) (m i)
    (hsingle i).1 (hsingle i).2
  have hprod (s : Finset δ) : ∃ M : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f x,
      M f x = (∏ i ∈ s, r i x) * f x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨.id ℂ _, fun _ _ ↦ by simp⟩
    | @insert i s hi ih =>
      obtain ⟨M,hM⟩ := ih
      obtain ⟨P,hP⟩ := hm i
      exact ⟨P.comp M, fun f x ↦ by
        rw [ContinuousLinearMap.comp_apply, hP, hM, Finset.prod_insert hi, mul_assoc]⟩
  obtain ⟨M,hM⟩ := hprod Finset.univ
  refine ⟨M, fun f ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  change M (L f) x = t c f x
  rw [hM, hL, ht, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  have hv := congrFun (modulationWeight_between_eq (m i) (fun _ ↦ 1) (a i) (c i) (b i)) x
  change w i (c i) x * 1 = r i x * (w i (a i) x * 1 + w i (b i) x * 1) at hv
  simpa only [mul_one] using hv.symm

/-- Tensoring two sets with dense linear spans again gives a set with dense linear
span. The two density arguments use separate continuity of the product. -/
private theorem archimedeanWeightedSchwartz_dense_binary {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousConstSMul ℂ Z]
    (e : UniformSpace.Completion (InductiveTensor X Y) ≃L[ℂ] Z)
    {A : Set X} {B : Set Y} (hA : Dense (Submodule.span ℂ A : Set X)) (hB : Dense (Submodule.span ℂ B : Set Y))
    (S : Submodule ℂ Z)
    (hp : ∀ x ∈ A, ∀ y ∈ B, e (UniformSpace.Completion.coe' (α := InductiveTensor X Y) (x ⊗ₜ[ℂ] y)) ∈ S) :
    Dense (S : Set Z) := by
  let T := InductiveTensor X Y
  let L := e.toContinuousLinearMap.comp (UniformSpace.Completion.toComplL : T →L[ℂ] UniformSpace.Completion T)
  let P := (TensorProduct.mk ℂ X Y).compr₂ L.toLinearMap
  let p := fun q : {q : Seminorm ℂ (X ⊗[ℂ] Y) //
    (∀ x : X, Continuous (fun y : Y ↦ q (x ⊗ₜ[ℂ] y))) ∧ (∀ y : Y, Continuous (fun x : X ↦ q (x ⊗ₜ[ℂ] y)))} ↦ q.val
  have hgen := withGeneratingSeminorms_spec (X ⊗[ℂ] Y) p
  have right (x : X) : Continuous (P x) := L.continuous.comp
    (hgen.continuous_of_continuous_comp (TensorProduct.mk ℂ X Y x) fun q ↦ q.property.1 x)
  have left (y : Y) : Continuous (P.flip y) := L.continuous.comp
    (hgen.continuous_of_continuous_comp ((TensorProduct.mk ℂ X Y).flip y) fun q ↦ q.property.2 y)
  let C := S.topologicalClosure
  have hxy (x : X) (y : Y) : P x y ∈ C := by
    have ha : Submodule.span ℂ A ≤ C.comap (P.flip y) := by
      apply Submodule.span_le.mpr
      intro u hu
      have hb : Submodule.span ℂ B ≤ C.comap (P u) :=
        Submodule.span_le.mpr (fun v hv ↦ S.le_topologicalClosure (hp u hu v hv))
      exact closure_minimal hb (S.isClosed_topologicalClosure.preimage (right u)) (hB y)
    exact closure_minimal ha (S.isClosed_topologicalClosure.preimage (left y)) (hA x)
  have hL (z : T) : L z ∈ C := TensorProduct.inductionOn (motive := fun z ↦ L z ∈ C) z hxy
    (fun _ _ hx hy ↦ (C.comap L.toLinearMap).add_mem hx hy)
  intro z
  obtain ⟨v, rfl⟩ := e.surjective z
  exact UniformSpace.Completion.induction_on (p := fun x ↦ e x ∈ C) v
    (S.isClosed_topologicalClosure.preimage e.continuous) hL


/-- Separate products of one-variable dense sets generate the unweighted
Schwartz space of a finite product, including the empty product. -/
private theorem archimedeanWeightedSchwartz_dense_pi {ι G : Type*} [Fintype ι]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (A : ι → Set (SchwartzBruhat G)) (hA : ∀ i, Dense (A i)) :
    Dense (Submodule.span ℂ {z : SchwartzBruhat (ι → G) | ∃ f : ι → SchwartzBruhat G,
      (∀ i, f i ∈ A i) ∧ ∀ x, z x = ∏ i, f i (x i)} : Set (SchwartzBruhat (ι → G))) := by
  classical
  let S := Submodule.span ℂ {z : SchwartzBruhat (ι → G) | ∃ f : ι → SchwartzBruhat G,
    (∀ i, f i ∈ A i) ∧ ∀ x, z x = ∏ i, f i (x i)}
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    let : CompactSpace (ι → G) := Finite.compactSpace
    obtain ⟨one, hone⟩ := compact_schwartzBruhat_one (H := ι → G)
    have h1 : one ∈ S := Submodule.subset_span ⟨isEmptyElim, fun i ↦ isEmptyElim i, fun x ↦ by simp [hone]⟩
    intro f
    apply subset_closure
    have hf : f = f 1 • one := Subtype.ext (funext fun x ↦ by
      change f x = f 1 * one x
      rw [hone, mul_one, Subsingleton.elim x 1])
    exact hf ▸ S.smul_mem _ h1
  | inr hn =>
    obtain ⟨i⟩ := hn
    let J := {j : ι // j ≠ i}
    let d : (ι → G) ≃ₜ* (G × (J → G)) := { Homeomorph.piSplitAt i (fun _ ↦ G) with map_mul' := fun _ _ ↦ rfl }
    obtain ⟨e,he⟩ := split_schwartz_kernel d.symm
    have hy := archimedeanWeightedSchwartz_dense_pi (fun j : J ↦ A j.val) (fun j ↦ hA j.val)
    apply archimedeanWeightedSchwartz_dense_binary e ((hA i).mono Submodule.subset_span) hy S
    rintro f hf g ⟨v,hv,hg⟩
    let q (j : ι) : SchwartzBruhat G := if h : j = i then f else v ⟨j,h⟩
    have hq (j : ι) : q j ∈ A j := by
      by_cases h : j = i
      · subst j; simpa [q] using hf
      · simpa [q, h] using hv ⟨j,h⟩
    refine Submodule.subset_span ⟨q, hq, fun x ↦ ?_⟩
    have hx := he f g (d x).1 (d x).2
    rw [Prod.mk.eta, d.symm_apply_apply] at hx
    rw [hx, hg, Fintype.prod_eq_mul_prod_compl i]
    change f (x i) * (∏ j : J, v j (x j.val)) = q i (x i) * _
    rw [show q i = f by simp [q]]
    congr 1
    refine Eq.trans ?_ (Finset.prod_subtype (F := inferInstanceAs (Fintype J)) (p := fun j ↦ j ≠ i) _ (fun j ↦ by simp) (fun j ↦ q j (x j))).symm
    apply Finset.prod_congr rfl
    intro j _
    simp [q,j.property]
termination_by Fintype.card ι
decreasing_by
  classical
  exact Fintype.card_subtype_lt (x := i) (not_not_intro rfl)

/-- The approximation estimate in Lemma 5.3.3.3(2), p. 252: finite sums of
separate products approximate every weighted test simultaneously in the partial
Schwartz seminorms. This assertion involves only the function spaces. -/
private theorem archimedeanWeightedSchwartz_tensor_dense {I : Set ℝ} (ho : IsOpen I)
    (hi : OrdConnected I) (hne : I.Nonempty) :
    Dense (Submodule.span ℂ {w : 𝓦(I) | ∃ (f : ι → realFactors(I)) (g : κ → complexFactors(I)),
      ∀ u : archMul(ι, κ), w.val u = separateValue(f, g, u)} : Set 𝓦(I)) := by
  classical
  let G := archMul(ι, κ)
  let J := (insert 0 I : Set ℝ)
  let W := weights(ι, κ, I)
  let S := Submodule.span ℂ {w : 𝓦(I) | ∃ (f : ι → realFactors(I)) (g : κ → complexFactors(I)),
    ∀ u, w.val u = separateValue(f, g, u)}
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let mr := archimedeanUnitModulation ℝ 1
  let mc := archimedeanUnitModulation ℂ 2
  let mr' (i : ι) : G →ₜ* ℝ≥0ˣ :=
    { toFun := fun u ↦ mr (u.1 i)
      map_one' := mr.map_one
      map_mul' := fun u v ↦ mr.map_mul (u.1 i) (v.1 i)
      continuous_toFun := mr.continuous.comp ((continuous_apply i).comp continuous_fst) }
  let mc' (j : κ) : G →ₜ* ℝ≥0ˣ :=
    { toFun := fun u ↦ mc (u.2 j)
      map_one' := mc.map_one
      map_mul' := fun u v ↦ mc.map_mul (u.2 j) (v.2 j)
      continuous_toFun := mc.continuous.comp ((continuous_apply j).comp continuous_snd) }
  let m := Sum.elim mr' mc'
  let t (c : ι ⊕ κ → J) : 𝓦(I) →ₗ[ℂ] SchwartzBruhat G :=
    archimedeanSchwartzTwist I (c ∘ Sum.inl, c ∘ Sum.inr)
  have ht (c : ι ⊕ κ → J) (f : 𝓦(I)) (u : G) : t c f u =
      (∏ i, (((m i u).val : ℝ) ^ (c i : ℝ) : ℝ) : ℂ) * f.val u := by
    refine (archimedeanSchwartzTwist_apply I (c ∘ Sum.inl, c ∘ Sum.inr) f u).trans ?_
    rw [Fintype.prod_sum_type]
    have hr (i : ι) : ((m (.inl i) u).val : ℝ) = ‖(u.1 i).val‖ := by
      change (((archimedeanUnitModulation ℝ 1 (u.1 i)).val : ℝ) = _)
      rw [archimedeanUnitModulation_apply, pow_one]
    have hc (j : κ) : ((m (.inr j) u).val : ℝ) = ‖(u.2 j).val‖ ^ 2 := by
      change (((archimedeanUnitModulation ℂ 2 (u.2 j)).val : ℝ) = _)
      exact archimedeanUnitModulation_apply ℂ 2 (u.2 j)
    simp only [Function.comp_apply, Complex.ofReal_prod, hr, hc]
  refine dense_of_finite_coordinates (Z := SchwartzBruhat G) (fun (f : 𝓦(I)) (c : W) ↦
    archimedeanSchwartzTwist I c f) (archimedeanSchwartzTwists_isEmbedding I).isInducing
    (S : Set 𝓦(I)) fun F ↦ ?_
  let V (i : ι ⊕ κ) : Finset J := insert ⟨0, Set.mem_insert _ _⟩ (F.image fun c ↦ Sum.elim c.1 c.2 i)
  have hn (i) : (V i).Nonempty := Finset.insert_nonempty _ _
  let a (i) := (V i).min' (hn i)
  let b (i) := (V i).max' (hn i)
  obtain ⟨L,hL,hc⟩ := archimedeanWeightedSchwartz_endpoint_box J m t (fun f ↦ f.val) ht a b
  refine ⟨L, ?_, fun c hcF ↦ ?_⟩
  · let A (i : ι) := modulatedExponentialDecayTwist mr J (a (.inl i)) + modulatedExponentialDecayTwist mr J (b (.inl i))
    let B (j : κ) := modulatedExponentialDecayTwist mc J (a (.inr j)) + modulatedExponentialDecayTwist mc J (b (.inr j))
    have hA (i : ι) : Dense (range (A i)) := archimedeanWeightedSchwartz_dense_factor mr
      realCoordinate_mul_allExponentialDecay_modulation.1 realCoordinate_mul_allExponentialDecay_modulation.2 J _ _
    have hB (j : κ) : Dense (range (B j)) := archimedeanWeightedSchwartz_dense_factor mc
      complexCoordinate_mul_allExponentialDecay_modulation.1 complexCoordinate_mul_allExponentialDecay_modulation.2 J _ _
    obtain ⟨e,he⟩ := schwartzBruhat_kernel_equiv (G := ι → ℝˣ) (H := κ → ℂˣ)
    change Dense ((S.map L) : Set (SchwartzBruhat G))
    apply archimedeanWeightedSchwartz_dense_binary e
      (archimedeanWeightedSchwartz_dense_pi _ hA) (archimedeanWeightedSchwartz_dense_pi _ hB)
    rintro p ⟨F,hF,hp⟩ q ⟨Q,hQ,hq⟩
    choose f hf using hF
    choose g hg using hQ
    let z : 𝓦(I) := ⟨_, archimedeanWeightedSchwartz_tensor_pure I f g⟩
    refine ⟨z, Submodule.subset_span ⟨f,g,fun _ ↦ rfl⟩, Subtype.ext (funext fun u ↦ ?_)⟩
    obtain ⟨ur,uc⟩ := u
    change L z (ur,uc) = _
    rw [hL, Fintype.prod_sum_type, he, hp, hq]
    simp_rw [← hf, ← hg]
    change (_ * _) * ((∏ i, (f i).val (ur i)) * ∏ j, (g j).val (uc j)) =
      (∏ i, A i (f i) (ur i)) * ∏ j, B j (g j) (uc j)
    have hreal (i : ι) : A i (f i) (ur i) =
        (((((mr (ur i)).val : ℝ) ^ (a (.inl i) : ℝ) : ℝ) : ℂ) +
        ((((mr (ur i)).val : ℝ) ^ (b (.inl i) : ℝ) : ℝ) : ℂ)) * (f i).val (ur i) := by
      exact (add_mul _ _ _).symm
    have hcomplex (j : κ) : B j (g j) (uc j) =
        (((((mc (uc j)).val : ℝ) ^ (a (.inr j) : ℝ) : ℝ) : ℂ) +
        ((((mc (uc j)).val : ℝ) ^ (b (.inr j) : ℝ) : ℝ) : ℂ)) * (g j).val (uc j) := by
      exact (add_mul _ _ _).symm
    have hr (i : ι) : m (.inl i) (ur,uc) = mr (ur i) := rfl
    have hc (j : κ) : m (.inr j) (ur,uc) = mc (uc j) := rfl
    simp_rw [hreal, hcomplex, Finset.prod_mul_distrib, hr, hc]
    ring
  · let c' := Sum.elim c.1 c.2
    have hmem (i) : c' i ∈ V i := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨c,hcF,rfl⟩)
    obtain ⟨R,hR⟩ := hc c' (fun i ↦ (V i).min'_le _ (hmem i)) (fun i ↦ (V i).le_max' _ (hmem i))
    exact ⟨R, R.continuous, hR⟩

end WeightedTensorEstimates

end

set_option maxHeartbeats 600000 in
/-- Paper: Lemma 5.3.3.3(2), p. 252.
The canonical map multiplies pure factors evaluated in their own coordinates and
extends to a linear homeomorphism on the completion.
Deviation: The factors include weight zero for the unweighted condition in (5.3.3.6).
When zero already belongs to I these are the factors printed in the paper. -/
theorem archimedeanWeightedSchwartz_tensor {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) :
    let J := insert 0 I
    let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
    let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] 𝓦(I), IsEmbedding L ∧
      (∀ (f : ι → R) (g : κ → C) (u : archMul(ι, κ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)) ∧
      ∃ e : UniformSpace.Completion T ≃L[ℂ] 𝓦(I), ∀ z : T, e z = L z := by
  classical
  let J := insert 0 I
  let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
  let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
  let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R)) (FiniteProjectiveTensor (fun _ : κ ↦ C))
  let r : R →ₗ[ℂ] (ℝˣ → ℂ) := (modulatedExponentialDecaySubmodule (archimedeanUnitModulation ℝ 1) J).subtype
  let c : C →ₗ[ℂ] (ℂˣ → ℂ) := (modulatedExponentialDecaySubmodule (archimedeanUnitModulation ℂ 2) J).subtype
  have hr : Injective r := fun _ _ h ↦ Subtype.ext h
  have hc : Injective c := fun _ _ h ↦ Subtype.ext h
  have hp (f : ι → R) (g : κ → C) :
      (fun u : archMul(ι, κ) ↦ (∏ i, r (f i) (u.1 i)) * ∏ j, c (g j) (u.2 j)) ∈
          archimedeanWeightedSchwartzSubmodule I :=
    archimedeanWeightedSchwartz_tensor_pure I f g
  have hA := archimedeanWeightedSchwartz_tensor_lift (ι := ι) (κ := κ)
    (U := ℝˣ) (V := ℂˣ) (A := R) (B := C) r c hr hc (archimedeanWeightedSchwartzSubmodule I) hp
  let L := hA.choose
  have hLi := hA.choose_spec.1
  have hL := hA.choose_spec.2
  let M : T →ₗ[ℂ] 𝓦(I) := L
  have hM : IsInducing M := (archimedeanSchwartzTwists_isEmbedding I).isInducing.of_comp_iff.mp
    (archimedeanWeightedSchwartz_tensor_twists _ho _hi _hne M hL)
  let P : T →L[ℂ] 𝓦(I) := ⟨M, hM.continuous⟩
  have hd : DenseRange P := by
    apply Dense.mono _ (archimedeanWeightedSchwartz_tensor_dense (ι := ι) (κ := κ) _ho _hi _hne)
    change Submodule.span ℂ _ ≤ M.range
    apply Submodule.span_le.mpr
    rintro w ⟨f, g, h⟩
    exact ⟨(⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j), Subtype.ext (funext fun u ↦ (hL f g u).trans (h u).symm)⟩
  have hP : IsEmbedding P := ⟨hM, hLi⟩
  let : T2Space 𝓦(I) := (show IsNuclearTVS.{0} 𝓦(I) from
    archimedeanWeightedSchwartz_nuclear _ho _hi _hne).1
  let : CompleteSpace 𝓦(I) := archimedeanWeightedSchwartz_complete _ho _hi _hne
  exact ⟨P, hP, hL, archimedeanWeightedSchwartz_tensor_completion P hP hd⟩

local notation "jet(" n ", " x ", " v ")" =>
  (fun f : 𝓢(archAdd(ι, κ), ℂ) ↦ iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x v)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Evaluation of the real derivative of order n at a point and a tuple of directions
is complex-linear in the Schwartz function. -/
theorem archimedeanSchwartzJet_isLinear (n : ℕ) (x : archAdd(ι, κ))
    (v : Fin n → archAdd(ι, κ)) : IsLinearMap ℂ (jet(n, x, v)) := by
  constructor
  · intro f g
    change iteratedFDeriv ℝ n ((f : _ → ℂ) + (g : _ → ℂ)) x v = _
    rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt,
      ContinuousMultilinearMap.add_apply]
  · intro a f
    change iteratedFDeriv ℝ n (a • (f : _ → ℂ)) x v = _
    rw [iteratedFDeriv_const_smul_apply (f.smooth n).contDiffAt, ContinuousMultilinearMap.smul_apply]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The flat Schwartz subspace is the intersection of the kernels of all jets on the
union of the coordinate hyperplanes.
Deviation: Full real Fréchet derivatives express the equivalent vanishing of the
mixed ordinary and Wirtinger derivatives. The coordinates are the product field coordinates. -/
def archimedeanFlatSchwartz : Submodule ℂ 𝓢(archAdd(ι, κ), ℂ) :=
  ⨅ x : {x : archAdd(ι, κ) // meetsWall(x)}, ⨅ n : ℕ, ⨅ v : Fin n → archAdd(ι, κ),
    LinearMap.ker ((archimedeanSchwartzJet_isLinear n x.val v).mk' _)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one real factor the jet conditions recover the real flat subspace of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_real :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ] ↥realSchwartzFlatAtOrigin,
      ∀ f (x : ℝ), (e f).val x = f.val (fun _ ↦ x, fun j ↦ Empty.elim j) := by
  let L : ℝ ≃ₗ[ℝ] ((Unit → ℝ) × (Empty → ℂ)) :=
    { toFun := fun x ↦ (fun _ ↦ x, fun j ↦ Empty.elim j)
      invFun := fun p ↦ p.1 ()
      map_add' := fun x y ↦ Prod.ext rfl (funext fun j ↦ Empty.elim j)
      map_smul' := fun t x ↦ Prod.ext rfl (funext fun j ↦ Empty.elim j)
      left_inv := fun x ↦ rfl
      right_inv := fun p ↦ Prod.ext (funext fun _ ↦ rfl) (funext fun j ↦ Empty.elim j) }
  let φ : ℝ ≃L[ℝ] ((Unit → ℝ) × (Empty → ℂ)) := L.toContinuousLinearEquiv
  let A : 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ
  let B : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ.symm
  -- Pulling back along the coordinate line gives a real function flat at zero.
  have hA (f : 𝓢((Unit → ℝ) × (Empty → ℂ), ℂ))
      (hf : f ∈ archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) :
      A f ∈ realSchwartzFlatAtOrigin := by
    rw [mem_realSchwartzFlatAtOrigin_iff]
    intro k
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply] at hf
    have h0 := hf ⟨φ 0, Or.inl ⟨(), rfl⟩⟩ k (fun _ ↦ φ 1)
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change iteratedFDeriv ℝ k ((f : (Unit → ℝ) × (Empty → ℂ) → ℂ) ∘ φ) 0 (fun _ ↦ 1) = 0
    erw [φ.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth ⊤) 0 (i := k)
      (mod_cast le_top)]
    exact h0
  -- Conversely every jet on the wall is a multiple of a derivative at zero.
  have hB (g : 𝓢(ℝ, ℂ)) (hg : g ∈ realSchwartzFlatAtOrigin) :
      B g ∈ archimedeanFlatSchwartz (ι := Unit) (κ := Empty) := by
    rw [mem_realSchwartzFlatAtOrigin_iff] at hg
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply]
    rintro ⟨x, hx⟩ n v
    have hx0 : φ.symm x = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨j, _⟩
      · cases i
        exact hi
      · exact j.elim
    change iteratedFDeriv ℝ n ((g : ℝ → ℂ) ∘ φ.symm) x v = 0
    erw [φ.symm.toContinuousLinearMap.iteratedFDeriv_comp_right (g.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ n (g : ℝ → ℂ) (φ.symm x) (fun i ↦ φ.symm (v i)) = 0
    rw [hx0, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, hg, smul_zero]
  let e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ]
      ↥realSchwartzFlatAtOrigin :=
    ContinuousLinearEquiv.equivOfInverse
      ((A.comp (archimedeanFlatSchwartz (ι := Unit) (κ := Empty)).subtypeL).codRestrict
        realSchwartzFlatAtOrigin fun f ↦ hA f f.2)
      ((B.comp realSchwartzFlatAtOrigin.subtypeL).codRestrict
        (archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) fun g ↦ hB g g.2)
      (fun f ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (f.val : (Unit → ℝ) × (Empty → ℂ) → ℂ) (φ (φ.symm y)) = f.val y
        rw [ContinuousLinearEquiv.apply_symm_apply]))
      (fun g ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (g.val : ℝ → ℂ) (φ.symm (φ y)) = g.val y
        rw [ContinuousLinearEquiv.symm_apply_apply]))
  exact ⟨e, fun f x ↦ rfl⟩

private theorem archimedeanFlatSchwartz_one_complex_direction_jet
    (f : 𝓢(ℂ, ℂ)) (u : ℂ) (n : ℕ) (v : Fin n → ℂ) :
    iteratedFDeriv ℝ n
      ((LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u f) : ℂ → ℂ) 0 v =
      iteratedFDeriv ℝ (n + 1) (f : ℂ → ℂ) 0 (Fin.snoc v u) := by
  have he : ((LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u f) : ℂ → ℂ) =
      fun z ↦ fderiv ℝ (f : ℂ → ℂ) z u := by
    funext z
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
  rw [he, iteratedFDeriv_clm_apply_const_apply
    ((f.smooth (n + 1)).fderiv_right (m := n) (by simp)) (by simp),
    iteratedFDeriv_succ_apply_right]
  simp

private theorem archimedeanFlatSchwartz_one_complex_jet_linear
    (f g : 𝓢(ℂ, ℂ)) (a b : ℂ) (n : ℕ) (v : Fin n → ℂ) :
    iteratedFDeriv ℝ n ((a • f + b • g : 𝓢(ℂ, ℂ)) : ℂ → ℂ) 0 v =
      a • iteratedFDeriv ℝ n (f : ℂ → ℂ) 0 v +
      b • iteratedFDeriv ℝ n (g : ℂ → ℂ) 0 v := by
  change iteratedFDeriv ℝ n ((fun y ↦ a • f y) + fun y ↦ b • g y) 0 v = _
  rw [iteratedFDeriv_add_apply ((f.smooth n).const_smul a).contDiffAt
    ((g.smooth n).const_smul b).contDiffAt,
    iteratedFDeriv_const_smul_apply' (f.smooth n).contDiffAt,
    iteratedFDeriv_const_smul_apply' (g.smooth n).contDiffAt]
  rfl

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Vanishing of all real Fréchet jets implies vanishing of all mixed Wirtinger jets. -/
private theorem archimedeanFlatSchwartz_one_complex_wirtinger_of_jets (f : 𝓢(ℂ, ℂ))
    (h : ∀ (n : ℕ) (v : Fin n → ℂ), iteratedFDeriv ℝ n (f : ℂ → ℂ) 0 v = 0) :
    ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0 := by
  let P (g : 𝓢(ℂ, ℂ)) := ∀ (n : ℕ) (v : Fin n → ℂ),
    iteratedFDeriv ℝ n (g : ℂ → ℂ) 0 v = 0
  have hd (g : 𝓢(ℂ, ℂ)) (hg : P g) (u : ℂ) :
      P (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u g) := by
    intro n v
    rw [archimedeanFlatSchwartz_one_complex_direction_jet]
    exact hg _ _
  have hl (g j : 𝓢(ℂ, ℂ)) (hg : P g) (hj : P j) (a b : ℂ) :
      P (a • g + b • j) := by
    intro n v
    rw [archimedeanFlatSchwartz_one_complex_jet_linear, hg, hj, smul_zero, smul_zero, add_zero]
  have hz (g : 𝓢(ℂ, ℂ)) (hg : P g) : P (schwartzWirtingerZ g) := by
    have he : schwartzWirtingerZ g = (2 : ℂ)⁻¹ •
        (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) (1 : ℂ) g) +
        (-(2 : ℂ)⁻¹ * Complex.I) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) Complex.I g) := by
      simp only [schwartzWirtingerZ, smul_apply, sub_apply]
      module
    rw [he]
    exact hl _ _ (hd g hg 1) (hd g hg Complex.I) _ _
  have hb (g : 𝓢(ℂ, ℂ)) (hg : P g) : P (schwartzWirtingerZBar g) := by
    have he : schwartzWirtingerZBar g = (2 : ℂ)⁻¹ •
        (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) (1 : ℂ) g) +
        ((2 : ℂ)⁻¹ * Complex.I) • (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) Complex.I g) := by
      simp only [schwartzWirtingerZBar, smul_apply, add_apply]
      module
    rw [he]
    exact hl _ _ (hd g hg 1) (hd g hg Complex.I) _ _
  have hp (T : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ)) (hT : ∀ g, P g → P (T g))
      (g : 𝓢(ℂ, ℂ)) (hg : P g) (k : ℕ) : P ((T ^ k) g) := by
    induction k with
    | zero => simpa using hg
    | succ k ih => simpa [pow_succ'] using hT _ ih
  intro k l
  simpa [P] using hp _ hz _ (hp _ hb f h l) k 0 (fun i ↦ Fin.elim0 i)

private theorem archimedeanFlatSchwartz_one_complex_comm :
    Commute schwartzWirtingerZ schwartzWirtingerZBar := by
  have hd (u v : ℂ) (g : 𝓢(ℂ, ℂ)) :
      LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) v g) =
      LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) v (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u g) := by
    have he (a b z : ℂ) :
        LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) b g) z =
          fderiv ℝ (fderiv ℝ (g : ℂ → ℂ)) z a b := by
      change fderiv ℝ (fun t ↦ fderiv ℝ (g : ℂ → ℂ) t b) z a = _
      rw [fderiv_clm_apply (c := fderiv ℝ (g : ℂ → ℂ)) (u := fun _ ↦ b)
        (((g.smooth 2).fderiv_right (m := 1) (by decide)).differentiable (by decide) _)
        (differentiableAt_const b)]
      simp
    ext z
    rw [he, he]
    exact ((g.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)) u v
  apply ContinuousLinearMap.ext
  intro g
  change schwartzWirtingerZ (schwartzWirtingerZBar g) =
    schwartzWirtingerZBar (schwartzWirtingerZ g)
  simp only [schwartzWirtingerZ, schwartzWirtingerZBar, smul_apply, add_apply,
    sub_apply, map_smul, map_add, map_sub, hd 1 Complex.I g]
  module

private theorem archimedeanFlatSchwartz_one_complex_direction
    (f : 𝓢(ℂ, ℂ)) (u : ℂ) :
    LineDeriv.lineDerivOpCLM ℂ 𝓢(ℂ, ℂ) u f =
      u • schwartzWirtingerZ f + star u • schwartzWirtingerZBar f := by
  ext z
  change fderiv ℝ (f : ℂ → ℂ) z u = _
  let L := fderiv ℝ (f : ℂ → ℂ) z
  have hu : L u = u.re • L 1 + u.im • L Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul]
  change L u = u * schwartzWirtingerZ f z + star u * schwartzWirtingerZBar f z
  rw [hu, (schwartzWirtinger_apply f z).1, (schwartzWirtinger_apply f z).2]
  change _ = u * ((L 1 - Complex.I * L Complex.I) / 2) +
    star u * ((L 1 + Complex.I * L Complex.I) / 2)
  simp only [Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im u]
  simp only [star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (L Complex.I * (u.im : ℂ)) * Complex.I_sq

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Vanishing of all mixed Wirtinger jets implies vanishing of all real Fréchet jets. -/
private theorem archimedeanFlatSchwartz_one_complex_jets_of_wirtinger (f : 𝓢(ℂ, ℂ))
    (h : ∀ k l : ℕ, (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) f) 0 = 0) :
    ∀ (n : ℕ) (v : Fin n → ℂ), iteratedFDeriv ℝ n (f : ℂ → ℂ) 0 v = 0 := by
  intro n
  induction n generalizing f with
  | zero => intro v; simpa using h 0 0
  | succ n ih =>
    have hz : ∀ k l : ℕ,
        (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) (schwartzWirtingerZ f)) 0 = 0 := by
      intro k l
      have hc := congrArg (fun T : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢(ℂ, ℂ) ↦ T f)
        (archimedeanFlatSchwartz_one_complex_comm.symm.pow_left l).eq
      change (schwartzWirtingerZBar ^ l) (schwartzWirtingerZ f) =
        schwartzWirtingerZ ((schwartzWirtingerZBar ^ l) f) at hc
      rw [hc]
      simpa [pow_succ] using h (k + 1) l
    have hb : ∀ k l : ℕ,
        (schwartzWirtingerZ^k) ((schwartzWirtingerZBar^l) (schwartzWirtingerZBar f)) 0 = 0 := by
      intro k l
      simpa [pow_succ] using h k (l + 1)
    intro v
    rw [← Fin.snoc_init_self v, ← archimedeanFlatSchwartz_one_complex_direction_jet,
      archimedeanFlatSchwartz_one_complex_direction,
      archimedeanFlatSchwartz_one_complex_jet_linear, ih _ hz, ih _ hb,
      smul_zero, smul_zero, add_zero]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one complex factor the real jet conditions recover the mixed Wirtinger conditions of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_complex :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) ≃L[ℂ] ↥complexSchwartzFlatAtOrigin,
      ∀ f (z : ℂ), (e f).val z = f.val (fun i ↦ Empty.elim i, fun _ ↦ z) := by
  let L : ℂ ≃ₗ[ℝ] ((Empty → ℝ) × (Unit → ℂ)) :=
    { toFun := fun z ↦ (fun i ↦ Empty.elim i, fun _ ↦ z)
      invFun := fun p ↦ p.2 ()
      map_add' := fun x y ↦ Prod.ext (funext fun i ↦ Empty.elim i) rfl
      map_smul' := fun t x ↦ Prod.ext (funext fun i ↦ Empty.elim i) rfl
      left_inv := fun x ↦ rfl
      right_inv := fun p ↦ Prod.ext (funext fun i ↦ Empty.elim i) (funext fun _ ↦ rfl) }
  let φ : ℂ ≃L[ℝ] ((Empty → ℝ) × (Unit → ℂ)) := L.toContinuousLinearEquiv
  let A : 𝓢((Empty → ℝ) × (Unit → ℂ), ℂ) →L[ℂ] 𝓢(ℂ, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ
  let B : 𝓢(ℂ, ℂ) →L[ℂ] 𝓢((Empty → ℝ) × (Unit → ℂ), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ φ.symm
  have hA (f : 𝓢((Empty → ℝ) × (Unit → ℂ), ℂ))
      (hf : f ∈ archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) :
      A f ∈ complexSchwartzFlatAtOrigin := by
    rw [mem_complexSchwartzFlatAtOrigin_iff]
    apply archimedeanFlatSchwartz_one_complex_wirtinger_of_jets
    intro n v
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply] at hf
    have h0 := hf ⟨φ 0, Or.inr ⟨(), rfl⟩⟩ n (fun i ↦ φ (v i))
    change iteratedFDeriv ℝ n ((f : (Empty → ℝ) × (Unit → ℂ) → ℂ) ∘ φ) 0 v = 0
    erw [φ.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth ⊤) 0 (i := n)
      (mod_cast le_top)]
    exact h0
  have hB (g : 𝓢(ℂ, ℂ)) (hg : g ∈ complexSchwartzFlatAtOrigin) :
      B g ∈ archimedeanFlatSchwartz (ι := Empty) (κ := Unit) := by
    rw [mem_complexSchwartzFlatAtOrigin_iff] at hg
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply]
    rintro ⟨x, hx⟩ n v
    have hx0 : φ.symm x = 0 := by
      rcases hx with ⟨i, _⟩ | ⟨j, hj⟩
      · exact i.elim
      · cases j
        exact hj
    change iteratedFDeriv ℝ n ((g : ℂ → ℂ) ∘ φ.symm) x v = 0
    erw [φ.symm.toContinuousLinearMap.iteratedFDeriv_comp_right (g.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ n (g : ℂ → ℂ) (φ.symm x) (fun i ↦ φ.symm (v i)) = 0
    rw [hx0]
    exact archimedeanFlatSchwartz_one_complex_jets_of_wirtinger g hg n _
  let e : ↥(archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) ≃L[ℂ]
      ↥complexSchwartzFlatAtOrigin :=
    ContinuousLinearEquiv.equivOfInverse
      ((A.comp (archimedeanFlatSchwartz (ι := Empty) (κ := Unit)).subtypeL).codRestrict
        complexSchwartzFlatAtOrigin fun f ↦ hA f f.2)
      ((B.comp complexSchwartzFlatAtOrigin.subtypeL).codRestrict
        (archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) fun g ↦ hB g g.2)
      (fun f ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (f.val : (Empty → ℝ) × (Unit → ℂ) → ℂ) (φ (φ.symm y)) = f.val y
        rw [ContinuousLinearEquiv.apply_symm_apply]))
      (fun g ↦ Subtype.ext (SchwartzMap.ext fun y ↦ by
        change (g.val : ℂ → ℂ) (φ.symm (φ y)) = g.val y
        rw [ContinuousLinearEquiv.symm_apply_apply]))
  exact ⟨e, fun f z ↦ rfl⟩

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Schwartz functions supported away from every coordinate hyperplane are flat along them. -/
theorem mem_archimedeanFlatSchwartz_of_tsupport (f : 𝓢(archAdd(ι, κ), ℂ))
    (_hf : Disjoint (tsupport f) {x : archAdd(ι, κ) | meetsWall(x)}) :
    f ∈ archimedeanFlatSchwartz := by
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x n v
  have hx : x.val ∉ tsupport f := fun h ↦ Set.disjoint_left.mp _hf h x.2
  have hev : (f : archAdd(ι, κ) → ℂ) =ᶠ[nhds x.val] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have h0 : iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x.val =
      iteratedFDeriv ℝ n (0 : archAdd(ι, κ) → ℂ) x.val :=
    (hev.iteratedFDeriv ℝ n).self_of_nhds
  simp [IsLinearMap.mk', h0]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The subspace of Schwartz functions with all jets zero on the coordinate hyperplanes is closed. -/
theorem archimedeanFlatSchwartz_isClosed :
    IsClosed (↑(archimedeanFlatSchwartz (ι := ι) (κ := κ)) : Set 𝓢(archAdd(ι, κ), ℂ)) := by
  simp only [archimedeanFlatSchwartz, Submodule.coe_iInf]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun n ↦ isClosed_iInter fun v ↦ ?_
  let J := (TemperedDistribution.delta x.val).comp
    (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(archAdd(ι, κ), ℂ) v)
  have hJ : (archimedeanSchwartzJet_isLinear n x.val v).mk' _ = J.toLinearMap := by
    ext f
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  rw [hJ]
  exact J.isClosed_ker

-- TODO(paper-gap): The estimates (5.3.3.21)–(5.3.3.23) fail for bumps
-- supported close to, but away from, the origin.

/-- Repeated mean-value bounds on the unit segment bound a flat function by its highest
derivative. -/
private theorem archimedeanFlatSchwartz_restrict_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (n : ℕ) (hf : ContDiff ℝ (n + 1) f)
    (hflat : ∀ k ≤ n, iteratedDeriv k f 0 = 0) {C : ℝ}
    (hC : ∀ t ∈ Icc 0 1, ‖iteratedDeriv (n + 1) f t‖ ≤ C) :
    ∀ t ∈ Icc 0 1, ‖f t‖ ≤ C := by
  have hpos := (norm_nonneg _).trans (hC 0 (by simp))
  have step (g : ℝ → E) (hd : Differentiable ℝ g) (hz : g 0 = 0)
      (hder : ∀ t ∈ Icc 0 1, ‖deriv g t‖ ≤ C) (x : ℝ) (hx : x ∈ Icc 0 1) :
      ‖g x‖ ≤ C := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t _ ↦ (hd t).hasDerivAt.hasDerivWithinAt)
      (fun t ht ↦ hder t (Ico_subset_Icc_self ht)) x hx
    simpa [hz] using h.trans (mul_le_of_le_one_right hpos (by simpa using hx.2))
  induction n generalizing f with
  | zero =>
    exact step f (hf.differentiable (by norm_num)) (by simpa using hflat 0 le_rfl)
      (by simpa [iteratedDeriv_one] using hC)
  | succ n ih =>
    apply step f (hf.differentiable (by exact_mod_cast Nat.succ_ne_zero (n + 1)))
      (by simpa using hflat 0 (Nat.zero_le _))
    apply ih (deriv f) (hf.deriv')
    · intro k hk
      rw [← iteratedDeriv_succ']
      exact hflat (k + 1) (Nat.succ_le_succ hk)
    · simpa only [← iteratedDeriv_succ'] using hC

/-- Taylor expansion on the segment from a wall point bounds the value by a power of the
distance to the wall. -/
private theorem archimedeanFlatSchwartz_restrict_taylor_ray
    {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (f : V → B) (a v : V) (n : ℕ) (hf : ContDiff ℝ (n + 1) f)
    (hflat : ∀ k ≤ n, iteratedFDeriv ℝ k f a (fun _ ↦ v) = 0) (C : ℝ)
    (hbound : ∀ (t : ℝ), t ∈ Icc 0 1 → ‖iteratedFDeriv ℝ (n + 1) f (t • v + a)‖ ≤ C) :
    ‖f (a + v)‖ ≤ C * ‖v‖ ^ (n + 1) := by
  let L : ℝ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g : ℝ → B := (fun y ↦ f (y + a)) ∘ L
  have hc : ContDiff ℝ (n + 1) (fun y ↦ f (y + a)) :=
    hf.comp (show ContDiff ℝ (n + 1) (fun y : V ↦ y + a) by fun_prop)
  have hd (k : ℕ) (hk : k ≤ n + 1) (t : ℝ) :
      iteratedDeriv k g t = iteratedFDeriv ℝ k f (L t + a) (fun _ ↦ v) := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change (iteratedFDeriv ℝ k ((fun y ↦ f (y + a)) ∘ L) t) _ = _
    rw [L.iteratedFDeriv_comp_right hc t (mod_cast hk)]
    simp [iteratedFDeriv_comp_add_right, ContinuousMultilinearMap.compContinuousLinearMap_apply, L]
  have h0 (k : ℕ) (hk : k ≤ n) : iteratedDeriv k g 0 = 0 := by
    simpa [hd k (hk.trans (Nat.le_succ n))] using hflat k hk
  have hC (t : ℝ) (ht : t ∈ Icc 0 1) :
      ‖iteratedDeriv (n + 1) g t‖ ≤ C * ‖v‖ ^ (n + 1) := by
    rw [hd _ le_rfl]
    refine ((iteratedFDeriv ℝ (n + 1) f (L t + a)).le_opNorm _).trans ?_
    simpa [L] using mul_le_mul_of_nonneg_right
      (hbound t ht) (pow_nonneg (norm_nonneg v) (n + 1))
  have h := archimedeanFlatSchwartz_restrict_segment g n (hc.comp L.contDiff) h0 hC 1 (by simp)
  simpa [g, L, add_comm v a] using h

/-- Iterating the Fréchet derivative of a jet gives the norm of the derivative of the combined
order. -/
private theorem archimedeanFlatSchwartz_restrict_iterated_norm
    {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (f : V → B) (j k : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (k + j) f x‖ := by
  induction j generalizing k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.add_zero]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      norm_iteratedFDeriv_fderiv, ih]
    rw [Nat.succ_add, Nat.add_succ]

/-- At a point where all jets vanish, the Taylor estimate applies to every derivative of a
Schwartz function. -/
private theorem archimedeanFlatSchwartz_restrict_jet_at_wall
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : 𝓢(V, ℂ)) (a v : V) (j n : ℕ)
    (hflat : ∀ k, iteratedFDeriv ℝ k (f : V → ℂ) a = 0) :
    ‖iteratedFDeriv ℝ j (f : V → ℂ) (a + v)‖ ≤
      SchwartzMap.seminorm ℝ 0 (n + 1 + j) f * ‖v‖ ^ (n + 1) := by
  let g := iteratedFDeriv ℝ j (f : V → ℂ)
  have hg : ContDiff ℝ (n + 1) g := (f.smooth _).iteratedFDeriv_right'
  refine archimedeanFlatSchwartz_restrict_taylor_ray g a v n hg (fun k _ ↦ ?_) _ (fun t ht ↦ ?_)
  · have hz : iteratedFDeriv ℝ k g a = 0 := norm_eq_zero.mp (by
      dsimp only [g]
      rw [archimedeanFlatSchwartz_restrict_iterated_norm, hflat, norm_zero])
    rw [hz]
    rfl
  · dsimp only [g]
    rw [archimedeanFlatSchwartz_restrict_iterated_norm]
    exact f.norm_iteratedFDeriv_le_seminorm ℝ _ _

/-- Every derivative of a flat Schwartz function vanishes to arbitrary order in each separate
coordinate. -/
private theorem archimedeanFlatSchwartz_restrict_wall_bounds
    (f : archimedeanFlatSchwartz (ι := ι) (κ := κ)) (j m : ℕ) :
    ∃ C ≥ 0, ∀ x : archAdd(ι, κ),
      (∀ i, ‖iteratedFDeriv ℝ j (f.val : archAdd(ι, κ) → ℂ) x‖ ≤ C * ‖x.1 i‖ ^ m) ∧
      (∀ k, ‖iteratedFDeriv ℝ j (f.val : archAdd(ι, κ) → ℂ) x‖ ≤ C * ‖x.2 k‖ ^ m) := by
  classical
  let A := archAdd(ι, κ)
  have hflat (a : A) (ha : meetsWall(a)) (k : ℕ) :
      iteratedFDeriv ℝ k (f.val : A → ℂ) a = 0 := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := f.property
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply] at h
    exact h ⟨a, ha⟩ k v
  cases m with
  | zero =>
    refine ⟨SchwartzMap.seminorm ℝ 0 j f.val, apply_nonneg _ _, fun x ↦ ?_⟩
    have h := f.val.norm_iteratedFDeriv_le_seminorm ℝ j x
    simp [h]
  | succ n =>
    let C := SchwartzMap.seminorm ℝ 0 (n + 1 + j) f.val
    have hC : 0 ≤ C := apply_nonneg _ _
    have bound (x v : A) (ha : meetsWall(x - v)) :
        ‖iteratedFDeriv ℝ j (f.val : A → ℂ) x‖ ≤ C * ‖v‖ ^ (n + 1) := by
      have ht := archimedeanFlatSchwartz_restrict_jet_at_wall f.val (x - v) v j n (hflat _ ha)
      rw [sub_add_cancel] at ht
      exact ht
    refine ⟨C, hC, fun x ↦ ⟨fun i ↦ ?_, fun k ↦ ?_⟩⟩
    · let v : A := (Pi.single i (x.1 i), 0)
      have hv : ‖v‖ = ‖x.1 i‖ := by
        change ‖((Pi.single i (x.1 i) : ι → ℝ), (0 : κ → ℂ))‖ = _
        rw [Prod.norm_def, Pi.norm_single, norm_zero, max_eq_left (norm_nonneg _)]
      have h := bound x v (Or.inl ⟨i, by
        change x.1 i - (Pi.single i (x.1 i) : ι → ℝ) i = 0
        simp⟩)
      rwa [hv] at h
    · let v : A := (0, Pi.single k (x.2 k))
      have hv : ‖v‖ = ‖x.2 k‖ := by
        change ‖((0 : ι → ℝ), (Pi.single k (x.2 k) : κ → ℂ))‖ = _
        rw [Prod.norm_def, Pi.norm_single, norm_zero, max_eq_right (norm_nonneg _)]
      have h := bound x v (Or.inr ⟨k, by
        change x.2 k - (Pi.single k (x.2 k) : κ → ℂ) k = 0
        simp⟩)
      rwa [hv] at h

/-- A common bound on the individual coordinate norms also bounds their maximum, including the
empty product. -/
private theorem archimedeanFlatSchwartz_restrict_pi_bound
    {S K : Type*} [Fintype S] [NormedAddCommGroup K] (y : S → K)
    (m : ℕ) (d C : ℝ) (hd : 0 ≤ d) (h0 : d ≤ C) (hC : 0 ≤ C)
    (hy : ∀ i, ‖y i‖ ^ m * d ≤ C) : ‖y‖ ^ m * d ≤ C := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have hzero : y = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    cases m <;> simp [h0, hC]
  | inr h =>
    obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ ‖y i‖) Finset.univ_nonempty
    have hn : ‖y‖ ≤ ‖y i‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k ↦ hi k (Finset.mem_univ _)
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn _) hd).trans (hy i)

/-- All jets decay faster than every power of the maximum of one, the coordinate norm and the
inverse-coordinate norm. -/
private theorem archimedeanFlatSchwartz_restrict_jet_decay
    (f : archimedeanFlatSchwartz (ι := ι) (κ := κ)) (j m : ℕ) :
    ∃ C ≥ 0, ∀ u : archMul(ι, κ), (max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) ^ m *
      ‖iteratedFDeriv ℝ j (f.val : archAdd(ι, κ) → ℂ) (archVal u)‖ ≤ C := by
  classical
  obtain ⟨B, hB, hb⟩ := archimedeanFlatSchwartz_restrict_wall_bounds f j m
  let C := max B (max (SchwartzMap.seminorm ℝ 0 j f.val) (SchwartzMap.seminorm ℝ m j f.val))
  refine ⟨C, hB.trans (le_max_left _ _), fun u ↦ ?_⟩
  let d := ‖iteratedFDeriv ℝ j (f.val : archAdd(ι, κ) → ℂ) (archVal u)‖
  have hd : 0 ≤ d := norm_nonneg _
  have h0 : d ≤ C := (f.val.norm_iteratedFDeriv_le_seminorm ℝ j _).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hbC : B ≤ C := le_max_left _ _
  have hC : 0 ≤ C := hB.trans hbC
  have join {a b : ℝ} (ha : a ^ m * d ≤ C) (hb : b ^ m * d ≤ C) :
      max a b ^ m * d ≤ C := by
    rcases max_choice a b with h | h
    · rwa [h]
    · rwa [h]
  have invBound {r : ℝ} (hr : 0 < r) (h : d ≤ B * r ^ m) : r⁻¹ ^ m * d ≤ C := by
    rw [inv_pow, inv_mul_eq_div]
    exact ((div_le_iff₀ (pow_pos hr m)).mpr h).trans hbC
  apply join (by simpa using h0)
  apply join ((f.val.le_seminorm ℝ m j _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  rw [Prod.norm_def]
  apply join
  · apply archimedeanFlatSchwartz_restrict_pi_bound _ _ _ _ hd h0 hC
    intro i
    change ‖(↑((u.1 i)⁻¹) : ℝ)‖ ^ m * d ≤ C
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact invBound (norm_pos_iff.mpr (u.1 i).ne_zero) ((hb (archVal u)).1 i)
  · apply archimedeanFlatSchwartz_restrict_pi_bound _ _ _ _ hd h0 hC
    intro k
    change ‖(↑((u.2 k)⁻¹) : ℂ)‖ ^ m * d ≤ C
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact invBound (norm_pos_iff.mpr (u.2 k).ne_zero) ((hb (archVal u)).2 k)

/-- Assemble the one-place cylinders into one elementary presentation. Real and complex
logarithmic radii share the vector factor, while only the complex angles are periodic. -/
private theorem archimedeanFlatSchwartz_restrict_chart
    (r : ℝˣ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (ZMod 2)))
    (c : ℂˣ ≃ₜ* Multiplicative (ElementaryLieGroup 1 1 0 PUnit.{1}))
    (iR : ι ≃ Fin (Fintype.card ι)) (iC : κ ≃ Fin (Fintype.card κ))
    (iA : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ))) :
    let H := ElementaryLieGroup (Fintype.card (ι ⊕ κ)) (Fintype.card κ) 0
      (Fin (Fintype.card ι) → ZMod 2)
    ∃ e : archMul(ι, κ) ≃ₜ* Multiplicative H, ∀ y : H,
      (∀ i, (e.symm (Multiplicative.ofAdd y)).1 i = r.symm (Multiplicative.ofAdd
        (WithLp.toLp 2 (fun _ ↦ y.1 (iA (.inl i))), 0, 0, y.2.2.2 (iR i)))) ∧
      (∀ j, (e.symm (Multiplicative.ofAdd y)).2 j = c.symm (Multiplicative.ofAdd
        (WithLp.toLp 2 (fun _ ↦ y.1 (iA (.inr j))), (fun _ ↦ y.2.1 (iC j)), 0, PUnit.unit))) := by
  classical
  intro H
  let G := archMul(ι, κ)
  let R (y : H) (i : ι) : ElementaryLieGroup 1 0 0 (ZMod 2) :=
    (WithLp.toLp 2 (fun _ ↦ y.1 (iA (.inl i))), 0, 0, y.2.2.2 (iR i))
  let C (y : H) (j : κ) : ElementaryLieGroup 1 1 0 PUnit.{1} :=
    (WithLp.toLp 2 (fun _ ↦ y.1 (iA (.inr j))), fun _ ↦ y.2.1 (iC j), 0, PUnit.unit)
  let Z (y : H) : G := (fun i ↦ r.symm (Multiplicative.ofAdd (R y i)),
    fun j ↦ c.symm (Multiplicative.ofAdd (C y j)))
  let rad (u : G) := Sum.elim (fun i ↦ (r (u.1 i)).toAdd.1 0) (fun j ↦ (c (u.2 j)).toAdd.1 0)
  let Y (u : G) : H := (WithLp.toLp 2 (fun k ↦ rad u (iA.symm k)),
    fun k ↦ (c (u.2 (iC.symm k))).toAdd.2.1 0, 0, fun k ↦ (r (u.1 (iR.symm k))).toAdd.2.2.2)
  have hR (u : G) (i : ι) : R (Y u) i = (r (u.1 i)).toAdd := by
    refine Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) ?_))
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk; simp [R, Y, rad]
    · simp [R, Y]
  have hC (u : G) (j : κ) : C (Y u) j = (c (u.2 j)).toAdd := by
    refine Prod.ext ?_ (Prod.ext ?_ (Subsingleton.elim _ _))
    · ext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk; simp [C, Y, rad]
    · funext k
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk; simp [C, Y]
  have hrz (y : H) (i : ι) : r ((Z y).1 i) = Multiplicative.ofAdd (R y i) := r.apply_symm_apply _
  have hcz (y : H) (j : κ) : c ((Z y).2 j) = Multiplicative.ofAdd (C y j) := c.apply_symm_apply _
  let e : Multiplicative H ≃ₜ* G :=
    { toFun := fun y ↦ Z y.toAdd
      invFun := fun u ↦ Multiplicative.ofAdd (Y u)
      left_inv := fun y ↦ by
        change Y (Z y.toAdd) = y.toAdd
        refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext (Subsingleton.elim _ _) ?_))
        · ext k
          obtain ⟨k, rfl⟩ := iA.surjective k
          cases k with
          | inl i => simp [Y, rad, hrz, R]
          | inr j => simp [Y, rad, hcz, C]
        · funext k; simp [Y, hcz, C]
        · funext k; simp [Y, hrz, R]
      right_inv := fun u ↦ Prod.ext (funext fun i ↦ r.injective
        ((hrz (Y u) i).trans (congrArg Multiplicative.ofAdd (hR u i)))) (funext fun j ↦ c.injective
        ((hcz (Y u) j).trans (congrArg Multiplicative.ofAdd (hC u j))))
      map_mul' := fun x y ↦ by
        refine Prod.ext (funext fun i ↦ ?_) (funext fun j ↦ ?_)
        · apply r.injective
          change r ((Z (x.toAdd + y.toAdd)).1 i) = r ((Z x.toAdd).1 i * (Z y.toAdd).1 i)
          simp only [hrz, map_mul]
          exact congrArg Multiplicative.ofAdd (Prod.ext rfl (Prod.ext (Subsingleton.elim _ _)
            (Prod.ext (Subsingleton.elim _ _) rfl)))
        · apply c.injective
          change c ((Z (x.toAdd + y.toAdd)).2 j) = c ((Z x.toAdd).2 j * (Z y.toAdd).2 j)
          simp only [hcz, map_mul]
          exact congrArg Multiplicative.ofAdd (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))
      continuous_toFun := by
        change Continuous Z
        apply Continuous.prodMk (continuous_pi fun i ↦ r.symm.continuous.comp ?_)
          (continuous_pi fun j ↦ c.symm.continuous.comp ?_)
        · change Continuous (fun y : H ↦ R y i)
          exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ ↦
            (PiLp.continuous_apply 2 _ _).comp continuous_fst)).prodMk (continuous_const.prodMk
              (continuous_const.prodMk ((continuous_apply _).comp
                (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
        · change Continuous (fun y : H ↦ C y j)
          exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ ↦
            (PiLp.continuous_apply 2 _ _).comp continuous_fst)).prodMk ((continuous_pi fun _ ↦
              (continuous_apply _).comp (continuous_fst.comp continuous_snd)).prodMk continuous_const)
      continuous_invFun := by
        have hr (i : ι) : Continuous (fun u : G ↦ (r (u.1 i)).toAdd) :=
          r.continuous.comp ((continuous_apply _).comp continuous_fst)
        have hc (j : κ) : Continuous (fun u : G ↦ (c (u.2 j)).toAdd) :=
          c.continuous.comp ((continuous_apply _).comp continuous_snd)
        change Continuous Y
        refine ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun k ↦ ?_)).prodMk
          ((continuous_pi fun k ↦ (continuous_apply 0).comp (continuous_fst.comp (continuous_snd.comp
            (hc (iC.symm k))))).prodMk (continuous_const.prodMk (continuous_pi fun k ↦
              continuous_snd.comp (continuous_snd.comp (continuous_snd.comp (hr (iR.symm k)))))))
        cases h : iA.symm k with
        | inl i => exact (PiLp.continuous_apply 2 _ 0).comp (continuous_fst.comp (hr i))
        | inr j => exact (PiLp.continuous_apply 2 _ 0).comp (continuous_fst.comp (hc j)) }
  exact ⟨e.symm, fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

/-- In the combined presentation each real unit is a signed exponential and each
complex unit is the exponential of a linear combination of radius and angle. -/
private theorem archimedeanFlatSchwartz_restrict_cover
    (iR : ι ≃ Fin (Fintype.card ι)) (iC : κ ≃ Fin (Fintype.card κ))
    (iA : ι ⊕ κ ≃ Fin (Fintype.card (ι ⊕ κ))) :
    let H := ElementaryLieGroup (Fintype.card (ι ⊕ κ)) (Fintype.card κ) 0
      (Fin (Fintype.card ι) → ZMod 2)
    ∃ e : archMul(ι, κ) ≃ₜ* Multiplicative H, ∀ t a b,
      let u := e.symm (Multiplicative.ofAdd (elementaryCover t a b))
      (∀ i, (u.1 i).val = (if b (iR i) = 0 then 1 else -1) * Real.exp (t.1 (iA (.inl i)))) ∧
      (∀ j, (u.2 j).val = Complex.exp ((t.1 (iA (.inr j)) : ℂ) +
        ((2 * Real.pi * t.2 (iC j) : ℝ) : ℂ) * Complex.I)) := by
  intro H
  obtain ⟨r, hr⟩ := iteratedDeriv_exponentialDecay_chart
  obtain ⟨c, hc⟩ := complexSchwartz_restrict_chart
  obtain ⟨e, he⟩ := archimedeanFlatSchwartz_restrict_chart r c iR iC iA
  refine ⟨e, fun t a b ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩⟩
  · let u := (e.symm (Multiplicative.ofAdd (elementaryCover t a b))).1 i
    have h := hr u
    have hu := congrArg r ((he (elementaryCover t a b)).1 i)
    change r u = _ at hu
    rw [r.apply_symm_apply] at hu
    rw [hu] at h
    have hlog : Real.exp (t.1 (iA (.inl i))) = |u.val| :=
      (congrArg Real.exp h.1).trans (Real.exp_log_eq_abs u.ne_zero)
    change u.val = _ * _
    rw [hlog, show b (iR i) = _ from h.2]
    by_cases hp : 0 < u.val
    · simp [hp, abs_of_pos hp]
    · simp [hp, abs_of_nonpos (le_of_not_gt hp)]
  · rw [(he (elementaryCover t a b)).2 j]
    exact hc (WithLp.toLp 2 fun _ ↦ t.1 (iA (.inr j)), WithLp.toLp 2 fun _ ↦ t.2 (iC j)) 0 PUnit.unit

/-- Each inverse coordinate norm is bounded by the maximum norm of the inverse tuple. -/
private theorem archimedeanFlatSchwartz_restrict_coords_bound (u : archMul(ι, κ)) :
    let M := max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)
    (∀ i, ‖(u.1 i).val‖ ≤ M ∧ ‖(u.1 i).val‖⁻¹ ≤ M) ∧
    (∀ j, ‖(u.2 j).val‖ ≤ M ∧ ‖(u.2 j).val‖⁻¹ ≤ M) := by
  intro M
  have hr (u : archMul(ι, κ)) (i : ι) : ‖(u.1 i).val‖ ≤ ‖archVal u‖ :=
    (norm_le_pi_norm (fun k : ι ↦ (u.1 k).val) i).trans (norm_fst_le (archVal u : archAdd(ι, κ)))
  have hc (u : archMul(ι, κ)) (j : κ) : ‖(u.2 j).val‖ ≤ ‖archVal u‖ :=
    (norm_le_pi_norm (fun k : κ ↦ (u.2 k).val) j).trans (norm_snd_le (archVal u : archAdd(ι, κ)))
  have h₁ : ‖archVal u‖ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₂ : ‖archVal (u⁻¹)‖ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨fun i ↦ ⟨(hr u i).trans h₁, by simpa using (hr (u⁻¹) i).trans h₂⟩,
    fun j ↦ ⟨(hc u j).trans h₁, by simpa using (hc (u⁻¹) j).trans h₂⟩⟩

/-- The inverse-coordinate estimate of order one forces every additive jet to vanish
at a wall, by density of the tuples of units. -/
private theorem archimedeanFlatSchwartz_restrict_flat_of_jets (f : 𝓢(archAdd(ι, κ), ℂ))
    (hjets : ∀ j m : ℕ, ∃ C ≥ 0, ∀ u : archMul(ι, κ),
      (max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) ^ m *
        ‖iteratedFDeriv ℝ j (f : archAdd(ι, κ) → ℂ) (archVal u)‖ ≤ C) :
    f ∈ archimedeanFlatSchwartz := by
  have hd (K : Type) [NontriviallyNormedField K] : DenseRange (Units.val : Kˣ → K) :=
    (dense_compl_singleton (0 : K)).mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have dense : DenseRange (archVal : archMul(ι, κ) → archAdd(ι, κ)) :=
    (DenseRange.piMap fun _ : ι ↦ hd ℝ).prodMap (DenseRange.piMap fun _ : κ ↦ hd ℂ)
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply]
  rintro ⟨x, hx⟩ n v
  obtain ⟨C, _, hC⟩ := hjets n 1
  let d (x : archAdd(ι, κ)) := ‖iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x‖
  have hc : Continuous d := ((f.smooth n).continuous_iteratedFDeriv le_rfl).norm
  have bound (q : archAdd(ι, κ) → ℝ) (hq : Continuous q) (hpos : ∀ u : archMul(ι, κ), 0 < q (archVal u))
      (hle : ∀ u : archMul(ι, κ), (q (archVal u))⁻¹ ≤ max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) :
      ∀ x, d x ≤ C * q x := fun x ↦ dense.induction_on x (isClosed_le hc (continuous_const.mul hq)) fun u ↦ by
    apply (div_le_iff₀ (hpos u)).mp
    rw [← inv_mul_eq_div]
    exact (mul_le_mul_of_nonneg_right (hle u) (norm_nonneg _)).trans (by simpa using hC u)
  have hzero : d x ≤ 0 := by
    rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
    · have h := bound (fun x : archAdd(ι, κ) ↦ ‖x.1 i‖) (by fun_prop) (fun u ↦ norm_pos_iff.mpr (u.1 i).ne_zero)
        (fun u ↦ ((archimedeanFlatSchwartz_restrict_coords_bound u).1 i).2) x
      simpa only [hi, norm_zero, mul_zero] using h
    · have h := bound (fun x : archAdd(ι, κ) ↦ ‖x.2 j‖) (by fun_prop) (fun u ↦ norm_pos_iff.mpr (u.2 j).ne_zero)
        (fun u ↦ ((archimedeanFlatSchwartz_restrict_coords_bound u).2 j).2) x
      simpa only [hj, norm_zero, mul_zero] using h
  rw [norm_le_zero_iff.mp hzero]
  rfl

/-- Applying a linear vector field to a flat test preserves flatness, by the bilinear
Leibniz bound and the vanishing of every derivative of the differential at a wall. -/
private theorem archimedeanFlatSchwartz_restrict_euler (f : archimedeanFlatSchwartz (ι := ι) (κ := κ))
    (l : archAdd(ι, κ) →L[ℝ] archAdd(ι, κ)) : ∃ g : archimedeanFlatSchwartz (ι := ι) (κ := κ),
      ∀ x, g.val x = fderiv ℝ (f.val : archAdd(ι, κ) → ℂ) x (l x) := by
  let A := archAdd(ι, κ)
  let B := ContinuousLinearMap.id ℝ (A →L[ℝ] ℂ)
  let g := SchwartzMap.bilinLeftCLM B l.hasTemperateGrowth (SchwartzMap.fderivCLM ℝ A ℂ f.val)
  have hf := f.property
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply] at hf
  refine ⟨⟨g, ?_⟩, fun _ ↦ rfl⟩
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply]
  intro x n v
  have hjet (i : ℕ) : iteratedFDeriv ℝ (i + 1) (f.val : A → ℂ) x.val = 0 :=
    ContinuousMultilinearMap.ext (fun v ↦ hf x _ v)
  have h := B.norm_iteratedFDeriv_le_of_bilinear (f.val.smooth'.fderiv_right (by simp))
    (l.contDiff (n := ∞)) x.val (n := n) (by simp)
  change ‖iteratedFDeriv ℝ n (g : A → ℂ) x.val‖ ≤ ‖B‖ * ∑ i ∈ Finset.range (n+1),
    (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ (f.val : A → ℂ)) x.val‖ *
      ‖iteratedFDeriv ℝ (n-i) l x.val‖ at h
  have hz (i : ℕ) : ‖iteratedFDeriv ℝ i (fderiv ℝ (f.val : A → ℂ)) x.val‖ = 0 :=
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ)).trans ((congrArg norm (hjet i)).trans norm_zero)
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero] at h
  rw [show iteratedFDeriv ℝ n (g : A → ℂ) x.val = 0 from norm_le_zero_iff.mp h]
  rfl

/-- The differential of an exponential chart at a translate is multiplication by
the chart value followed by the differential at zero. -/
private theorem archimedeanFlatSchwartz_restrict_translate {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedCommRing B] [NormedAlgebra ℝ B]
    (Z W : V → B) (hZ : Differentiable ℝ Z) (hW : Differentiable ℝ W)
    (h : ∀ t y, Z (t + y) = Z t * W y) (t v : V) :
    fderiv ℝ Z t v = fderiv ℝ W 0 v * Z t := by
  have hs : HasFDerivAt Z (fderiv ℝ Z t) (t + 0) := (add_zero t).symm ▸ (hZ t).hasFDerivAt
  have h₁ := hs.comp 0 ((hasFDerivAt_id (𝕜 := ℝ) (0 : V)).const_add t)
  have h₂ := (((ContinuousLinearMap.mul ℝ B) (Z t)).hasFDerivAt.comp 0 (hW 0).hasFDerivAt)
  have heq : (Z ∘ (fun y : V ↦ t + y)) = _ := funext (h t)
  rw [heq] at h₁
  exact (congrArg (fun l : V →L[ℝ] B ↦ l v) (h₁.unique h₂)).trans (mul_comm _ _)

/-- Paper: Lemma 5.3.3.3(3), p. 253.
In logarithmic radial and angular coordinates, coordinate weights preserve Schwartz–Bruhat
decay for a Schwartz function whose Euclidean jets decay rapidly in the norms of both
the coordinates and their inverses. -/
private theorem archimedeanFlatSchwartz_restrict_twist_mem
    (f : 𝓢(archAdd(ι, κ), ℂ))
    (hjets : ∀ j m : ℕ, ∃ C ≥ 0, ∀ u : archMul(ι, κ),
      (max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) ^ m *
        ‖iteratedFDeriv ℝ j (f : archAdd(ι, κ) → ℂ) (archVal u)‖ ≤ C)
    (a : weights(ι, κ, (univ : Set ℝ))) :
    weightMap(a) (fun u ↦ f (archVal u)) ∈ schwartzBruhatSubmodule (archMul(ι, κ)) := by
  classical
  let m := Fintype.card (ι ⊕ κ)
  let n := Fintype.card κ
  let F := Fin (Fintype.card ι) → ZMod 2
  let A := archAdd(ι, κ)
  let R := EuclideanSpace ℝ (Fin m)
  let T := EuclideanSpace ℝ (Fin n)
  let X := R × T
  let H := ElementaryLieGroup m n 0 F
  let iA := Fintype.equivFin (ι ⊕ κ)
  let iR := Fintype.equivFin ι
  let iC := Fintype.equivFin κ
  obtain ⟨e, he⟩ := archimedeanFlatSchwartz_restrict_cover iR iC iA
  let d : ElementaryLCAPresentation (archMul(ι, κ)) := ⟨m, n, 0, F, e⟩
  obtain ⟨J, hJ⟩ := elementarySchwartz_equiv_schwartzBruhat d
  let U (b : F) (t : X) := e.symm (Multiplicative.ofAdd (elementaryCover t 0 b))
  let Z (b : F) (t : X) : A := archVal (U b t)
  let r (k : Fin m) : X →L[ℝ] ℝ := (EuclideanSpace.proj k).comp (ContinuousLinearMap.fst ℝ R T)
  let s (j : κ) : X →L[ℝ] ℝ :=
    (2 * Real.pi) • (EuclideanSpace.proj (iC j)).comp (ContinuousLinearMap.snd ℝ R T)
  let L (j : κ) := Complex.ofRealCLM.comp (r (iA (.inr j))) + Complex.I • Complex.ofRealCLM.comp (s j)
  let B : X →L[ℝ] ℝ := (∑ i, (a.1 i : ℝ) • r (iA (.inl i))) +
    ∑ j, (2 * (a.2 j : ℝ)) • r (iA (.inr j))
  have hB (t : X) : B t = (∑ i, (a.1 i : ℝ) * t.1 (iA (.inl i))) +
      ∑ j, 2 * (a.2 j : ℝ) * t.1 (iA (.inr j)) := by
    simp [B, smul_eq_mul, r]; rfl
  have hR (b : F) (t : X) (i : ι) : (Z b t).1 i =
      (if b (iR i) = 0 then 1 else -1) * Real.exp (r (iA (.inl i)) t) := (he t 0 b).1 i
  have hC (b : F) (t : X) (j : κ) : (Z b t).2 j = Complex.exp (L j t) := by
    rw [show (Z b t).2 j = _ from (he t 0 b).2 j]
    congr 1
    change _ + _ * Complex.I = _ + Complex.I * _
    rw [mul_comm _ Complex.I]
    rfl
  have hrn (b : F) (t : X) (i : ι) : ‖((U b t).1 i).val‖ = Real.exp (t.1 (iA (.inl i))) := by
    change ‖(Z b t).1 i‖ = _
    rw [hR, norm_mul]
    split <;> simp [r, Real.norm_of_nonneg (Real.exp_pos _).le] <;> rfl
  have hcn (b : F) (t : X) (j : κ) : ‖((U b t).2 j).val‖ = Real.exp (t.1 (iA (.inr j))) := by
    change ‖(Z b t).2 j‖ = _
    rw [hC, Complex.norm_exp]
    simp [L, r, s]; rfl
  have hZ (b : F) : ContDiff ℝ (∞) (Z b) := by
    apply ContDiff.prodMk
    · apply contDiff_pi.mpr
      intro i
      rw [show (fun t ↦ (Z b t).1 i) = _ from funext fun t ↦ hR b t i]
      exact contDiff_const.mul (Real.contDiff_exp.comp (r _).contDiff)
    · apply contDiff_pi.mpr
      intro j
      rw [show (fun t ↦ (Z b t).2 j) = _ from funext fun t ↦ hC b t j]
      exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp (L j).contDiff : ContDiff ℝ (∞) (Complex.exp ∘ (L j)))
  have hadd (b : F) (t v : X) : Z b (t + v) = Z b t * Z 0 v := by
    have h := elementaryCover_add t v (0 : Fin 0 → ℤ) 0 b 0
    simp only [add_zero] at h
    dsimp only [Z, U]
    rw [← h, ofAdd_add, map_mul]
    rfl
  have hD (b : F) (t v : X) : fderiv ℝ (Z b) t v = fderiv ℝ (Z 0) 0 v * Z b t := by
    exact archimedeanFlatSchwartz_restrict_translate _ _ ((hZ b).differentiable (by simp))
      ((hZ 0).differentiable (by simp)) (hadd b) t v
  let P (g : archimedeanFlatSchwartz (ι := ι) (κ := κ)) (y : H) :=
    weightMap(a) (fun u ↦ g.val (archVal u)) (e.symm (Multiplicative.ofAdd y))
  let E := Complex.ofRealCLM.comp B
  have hP (g : archimedeanFlatSchwartz) (z : Fin 0 → ℤ) (b : F) : (fun t ↦ P g (elementaryCover t z b)) =
      fun t ↦ Complex.exp (E t) * g.val (Z b t) := by
    obtain rfl : z = 0 := Subsingleton.elim _ _
    funext t
    change (((∏ i, ‖((U b t).1 i).val‖ ^ (a.1 i : ℝ)) : ℝ) : ℂ) *
        (((∏ j, (‖((U b t).2 j).val‖ ^ 2) ^ (a.2 j : ℝ)) : ℝ) : ℂ) * _ = _
    rw [← Complex.ofReal_mul, show Complex.exp (E t) = (Real.exp (B t) : ℂ) from (Complex.ofReal_exp _).symm]
    congr 2
    rw [hB, Real.exp_add, Real.exp_sum, Real.exp_sum]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [hrn, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
    · apply Finset.prod_congr rfl
      intro j _
      rw [hcn, Real.rpow_def_of_pos (pow_pos (Real.exp_pos _) _), Real.log_pow, Real.log_exp]
      congr 1
      push_cast
      ring
  let f₀ : archimedeanFlatSchwartz := ⟨f, archimedeanFlatSchwartz_restrict_flat_of_jets f hjets⟩
  have hmem : P f₀ ∈ elementarySchwartzSubmodule m n 0 F := by
    apply archimedean_profile_mem P _ _ _ f₀
    · intro g z b
      rw [hP]
      have hw : ContDiff ℝ (∞) (Complex.exp ∘ E) := (Complex.contDiff_exp (𝕜 := ℝ)).comp E.contDiff
      exact hw.mul (g.val.smooth'.comp (hZ b))
    · intro g v
      let l := (ContinuousLinearMap.mul ℝ A) (fderiv ℝ (Z 0) 0 v)
      obtain ⟨g', hg'⟩ := archimedeanFlatSchwartz_restrict_euler g l
      refine ⟨g' + E v • g, fun t z b ↦ ?_⟩
      rw [hP, congrFun (hP _ z b) t]
      have h := ((((Complex.hasDerivAt_exp (E t)).hasFDerivAt.restrictScalars ℝ).comp t E.hasFDerivAt).mul
        (g.val.differentiableAt.hasFDerivAt.comp t ((hZ b).differentiable (by simp) t).hasFDerivAt)).fderiv
      change fderiv ℝ (Complex.exp ∘ E * (g.val : A → ℂ) ∘ Z b) t v = _
      rw [h]
      change _ = Complex.exp (E t) * (g'.val (Z b t) + E v * g.val (Z b t))
      rw [hg']
      simp [smul_eq_mul, l]
      rw [hD b t v]
      change _ = Complex.exp (E t) * (fderiv ℝ (g.val : A → ℂ) (Z b t)
        (fderiv ℝ (Z 0) 0 v * Z b t) + E v * g.val (Z b t))
      ring
    · intro g α
      let K := (∑ i, |(a.1 i : ℝ)|) + ∑ j, |2 * (a.2 j : ℝ)|
      obtain ⟨N, hN⟩ := exists_nat_ge K
      obtain ⟨C, hC₀, hC⟩ := archimedeanFlatSchwartz_restrict_jet_decay g 0 ((∑ k, α k) + N)
      refine ⟨⟨C, hC₀⟩, fun t z b ↦ ?_⟩
      rw [congrFun (hP _ z b) t]
      let M := max 1 (max ‖archVal (U b t)‖ ‖archVal ((U b t)⁻¹)‖)
      have hM : 1 ≤ M := le_max_left _ _
      have hM₀ := zero_lt_one.trans_le hM
      have hcoord (k : Fin m) : |t.1 k| ≤ Real.log M := by
        have hh : ∀ x : ℝ, Real.exp x ≤ M ∧ (Real.exp x)⁻¹ ≤ M → |x| ≤ Real.log M := by
          intro x h
          rw [abs_le]
          constructor
          · rw [neg_le, ← Real.exp_le_exp, Real.exp_neg, Real.exp_log hM₀]
            exact h.2
          · rw [← Real.exp_le_exp, Real.exp_log hM₀]
            exact h.1
        obtain ⟨i, rfl⟩ := iA.surjective k
        cases i with
        | inl i => exact hh _ (hrn b t i ▸ (archimedeanFlatSchwartz_restrict_coords_bound (U b t)).1 i)
        | inr j => exact hh _ (hcn b t j ▸ (archimedeanFlatSchwartz_restrict_coords_bound (U b t)).2 j)
      have hlin (d : ℝ) (k : Fin m) : d * t.1 k ≤ |d| * Real.log M :=
        (le_abs_self _).trans ((abs_mul d _).le.trans (mul_le_mul_of_nonneg_left (hcoord k) (abs_nonneg _)))
      have hw : Real.exp (B t) ≤ M ^ N := by
        rw [← Real.exp_log hM₀, ← Real.exp_nat_mul, Real.exp_le_exp, hB]
        calc
          _ ≤ (∑ i, |(a.1 i : ℝ)| * Real.log M) + ∑ j, |2 * (a.2 j : ℝ)| * Real.log M :=
            add_le_add (Finset.sum_le_sum fun i _ ↦ hlin _ _) (Finset.sum_le_sum fun j _ ↦ hlin _ _)
          _ = K * Real.log M := by simp only [K, add_mul, Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right hN (Real.log_nonneg hM)
      have hp : (∏ k, |t.1 k| ^ α k) ≤ M ^ ∑ k, α k := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun k _ ↦
          pow_le_pow_left₀ (abs_nonneg _) ((hcoord k).trans (Real.log_le_self hM₀.le)) _
      rw [norm_mul, norm_prod, norm_mul, Complex.norm_exp]
      simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul hp hw (Real.exp_pos _).le (pow_nonneg hM₀.le _))
        (norm_nonneg _)).trans (by
          change M ^ (∑ k, α k) * M ^ N * ‖g.val (Z b t)‖ ≤ C
          simpa only [M, Z, pow_add, norm_iteratedFDeriv_zero] using hC (U b t))
  have hj := (J ⟨P f₀, hmem⟩).property
  convert hj using 1
  funext u
  refine Eq.trans ?_ (hJ ⟨P f₀, hmem⟩ u).symm
  change _ = weightMap(a) (fun u ↦ f (archVal u)) (e.symm (e u))
  rw [e.symm_apply_apply]

/-- Paper: Lemma 5.3.3.3(3), p. 253.
Forward half of the restriction equivalence: restricting a flat Schwartz function to the
product of the punctured lines is a continuous linear map into the all-exponent weighted
space. The estimates (5.3.3.21)–(5.3.3.23) fail for bumps supported close to, but away
from, the origin; the bound comes instead from Taylor's theorem at the coordinate walls. -/
theorem archimedeanFlatSchwartz_restrict_to_weighted :
    ∃ R : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) →L[ℂ] 𝓦(univ),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (R f).val u = f.val (archVal u) := by
  classical
  let G := archMul(ι, κ)
  let A := archAdd(ι, κ)
  let X := archimedeanFlatSchwartz (ι := ι) (κ := κ)
  let Y := 𝓦(univ)
  let R : X →ₗ[ℂ] Y :=
    { toFun := fun f ↦ ⟨fun u ↦ f.val (archVal u),
        (Submodule.mem_iInf _).mpr fun a ↦ Submodule.mem_comap.mpr
          (archimedeanFlatSchwartz_restrict_twist_mem f.val
            (archimedeanFlatSchwartz_restrict_jet_decay f) a)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hY : IsFrechetTVS Y :=
    archimedeanWeightedSchwartz_frechet isOpen_univ ordConnected_univ univ_nonempty
  -- The zero twist makes point evaluations continuous on the weighted space.
  let W := weights(ι, κ, (univ : Set ℝ))
  let a₀ : W := (fun _ ↦ ⟨0, by simp⟩, fun _ ↦ ⟨0, by simp⟩)
  let P : SeminormFamily ℂ (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) univ)
      (W × {p : Seminorm ℂ (SchwartzBruhat G) // Continuous p}) :=
    fun i ↦ i.2.val.comp (archimedeanSchwartzTwist univ i.1)
  let T : Y →ₗ[ℂ] SchwartzBruhat G := archimedeanSchwartzTwist univ a₀
  have htw : Continuous T := by
    apply (PolynormableSpace.withSeminorms ℂ (SchwartzBruhat G)).continuous_of_continuous_comp
    intro p
    exact (withGeneratingSeminorms_spec _ P).continuous_seminorm (a₀, p)
  have evY (u : G) : Continuous (fun g : Y ↦ g.val u) := by
    apply ((continuous_schwartzBruhat_eval_forEndpoints u).comp htw).congr
    intro g
    change archimedeanSchwartzTwist univ a₀ g u = g.val u
    simpa [a₀] using archimedeanSchwartzTwist_apply univ a₀ g u
  have evX (u : G) : Continuous (fun f : X ↦ f.val (archVal u)) :=
    (TemperedDistribution.delta (archVal u)).continuous.comp continuous_subtype_val
  -- Equality on every tuple of units cuts out the graph of the restriction map.
  have hgraph : IsClosed (R.graph : Set (X × Y)) := by
    have heq : (R.graph : Set (X × Y)) = ⋂ u : G, {p : X × Y | p.2.val u = p.1.val (archVal u)} := by
      ext p
      change p ∈ R.graph ↔ _
      rw [LinearMap.mem_graph_iff, mem_iInter]
      exact ⟨fun h u ↦ congrArg (fun y : Y ↦ y.val u) h,
        fun h ↦ Subtype.ext (funext h)⟩
    rw [heq]
    exact isClosed_iInter fun u ↦ isClosed_eq ((evY u).comp continuous_snd) ((evX u).comp continuous_fst)
  -- Project the closed graph onto the complete space of flat tests. Open mapping
  -- makes this projection a quotient map, so continuity can be tested on its graph.
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  have : CompleteSpace 𝓢(A, ℂ) := completeSpace_schwartzMap
  have : CompleteSpace X := completeSpace_coe_iff_isComplete.mpr archimedeanFlatSchwartz_isClosed.isComplete
  have : IsUniformAddGroup X := X.toAddSubgroup.isUniformAddGroup
  have : (uniformity 𝓢(A, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  have : (uniformity X).IsCountablyGenerated :=
    inferInstanceAs (uniformity (X : Set 𝓢(A, ℂ))).IsCountablyGenerated
  have : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  let Γ := R.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hgraph.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology Γ := inferInstanceAs (FirstCountableTopology (Γ : Set (X × Y)))
  let P : Γ →L[ℂ] X := (ContinuousLinearMap.fst ℂ X Y).comp Γ.subtypeL
  have hs : Surjective P := fun x ↦ ⟨⟨(x, R x), (LinearMap.mem_graph_iff _ _).mpr rfl⟩, rfl⟩
  have ho : IsOpenMap P := isOpenMap_of_not_isMeagre_range P
    (hs.range_eq ▸ not_isMeagre_of_isOpen isOpen_univ univ_nonempty)
  have hq : IsOpenQuotientMap P := ⟨hs, P.continuous, ho⟩
  have hR : Continuous R := hq.isQuotientMap.continuous_iff.mpr <|
    (continuous_snd.comp continuous_subtype_val).congr fun p ↦
      (LinearMap.mem_graph_iff R p.val).mp p.property
  exact ⟨⟨R, hR⟩, fun _ _ ↦ rfl⟩

/-- Uniform bounds on the evaluations on a finite basis bound the multilinear
operator norm, including the zeroth derivative. -/
private theorem archimedeanWeightedSchwartz_multilinear_bound
    {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {n : ℕ} (T : I → X [×n]→L[ℝ] ℂ)
    (h : ∀ v, ∃ C : ℝ, ∀ u, ‖T u v‖ ≤ C) : ∃ C : ℝ, ∀ u, ‖T u‖ ≤ C := by
  classical
  let b := Module.finBasis ℝ X
  let K := Fin n → Fin (Module.finrank ℝ X)
  let L : (X [×n]→L[ℝ] ℂ) →ₗ[ℝ] (K → ℂ) :=
    { toFun := fun t k ↦ t (fun j ↦ b (k j))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : Injective L := by
    intro s t h
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    exact Module.Basis.ext_multilinear (fun _ ↦ b) (fun k ↦ congrFun h k)
  obtain ⟨l, hl⟩ := L.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hL)
  let R := l.toContinuousLinearMap
  choose C hC using fun k : K ↦ h (fun j ↦ b (k j))
  let D := ∑ k, |C k|
  have hD : 0 ≤ D := Finset.sum_nonneg fun k _ ↦ abs_nonneg _
  refine ⟨‖R‖ * D, fun u ↦ ?_⟩
  have hr : R (L (T u)) = T u := DFunLike.congr_fun hl (T u)
  rw [← hr]
  apply (R.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg hD).mpr fun k ↦ ((hC k u).trans (le_abs_self _)).trans
    (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ k))

/-- All derivatives at the identity of the translates of a Schwartz–Bruhat function
in exponential coordinates have uniform bounds. Each fixed directional derivative
is the realization of another Schwartz–Bruhat function. -/
private theorem archimedeanWeightedSchwartz_translate_bound
    {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (U : Multiplicative X →ₜ* G) (f : SchwartzBruhat G) (n : ℕ) :
    ∃ C : ℝ, ∀ u : G, ‖iteratedFDeriv ℝ n (fun t : X ↦ f (U (Multiplicative.ofAdd t) * u)) 0‖ ≤ C := by
  let P (f : SchwartzBruhat G) (u : G) (t : X) := f (U (Multiplicative.ofAdd t) * u)
  have hs (f : SchwartzBruhat G) (u : G) := complexExponentialDecay_contDiffOn_alongTranslate U f u
  have hd (f : SchwartzBruhat G) (v : X) : ∃ g : SchwartzBruhat G, ∀ u t, fderiv ℝ (P f u) t v = P g u t := by
    let L := (ContinuousLinearMap.id ℝ ℝ).smulRight v
    let flow : LCATopologicalLie G := U.comp
      ⟨AddMonoidHom.toMultiplicative L.toLinearMap.toAddMonoidHom, L.continuous⟩
    obtain ⟨D, hD⟩ := bruhatFirstOrder_schwartz flow
    refine ⟨D f, fun u t ↦ ?_⟩
    have hp : HasDerivAt (fun s : ℝ ↦ t + s • v) v 0 := by
      simpa [L] using L.hasDerivAt.const_add t (x := (0 : ℝ))
    have hf := ((hs f u).differentiable (by simp) t).hasFDerivAt
    have hf' : HasFDerivAt (P f u) (fderiv ℝ (P f u) t) (t + (0 : ℝ) • v) := by simpa using hf
    change _ = D f (U (Multiplicative.ofAdd t) * u)
    rw [hD, bruhatDirectionalDeriv, ← (hf'.comp_hasDerivAt 0 hp).deriv]
    congr 1
    funext s
    change f (U (Multiplicative.ofAdd (t + s • v)) * u) = f (_ * U (Multiplicative.ofAdd (s • v)))
    rw [ofAdd_add, map_mul, mul_right_comm]
  have jets (l : List X) : ∃ g : SchwartzBruhat G, ∀ u t,
      iteratedFDeriv ℝ l.length (P f u) t l.get = P g u t := by
    induction l with
    | nil => exact ⟨f, by simp⟩
    | cons v l ih =>
      obtain ⟨g, hg⟩ := ih
      obtain ⟨g', hg'⟩ := hd g v
      refine ⟨g', fun u t ↦ ?_⟩
      refine (((hs f u).differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top l.length)
        t).iteratedFDeriv_succ_apply_left' (m := (v :: l).get)).trans ?_
      exact (congrArg (fun g : X → ℂ ↦ fderiv ℝ g t v) (funext fun t ↦ hg u t)).trans (hg' u t)
  apply archimedeanWeightedSchwartz_multilinear_bound
  intro v
  obtain ⟨g, hg⟩ := jets (List.ofFn v)
  obtain ⟨b, hb⟩ := schwartzBruhat_boundedContinuous g
  refine ⟨‖b‖, fun u ↦ ?_⟩
  have hv : iteratedFDeriv ℝ n (P f u) 0 v = P g u 0 :=
    (congrArg (fun q : Σ k, Fin k → X ↦ iteratedFDeriv ℝ q.1 (P f u) 0 q.2)
      (List.equivSigmaTuple.apply_symm_apply ⟨n, v⟩)).symm.trans (hg u 0)
  rw [hv, show P g u 0 = g u by simp [P], ← hb]
  exact b.norm_coe_le_norm u

/-- Componentwise exponentiation has a smooth logarithm near the identity. -/
private theorem archimedeanWeightedSchwartz_log_chart :
    ∃ (U : Multiplicative (archAdd(ι, κ)) →ₜ* archMul(ι, κ)) (L : archAdd(ι, κ) → archAdd(ι, κ)),
      (∀ t : archAdd(ι, κ), archVal (U (Multiplicative.ofAdd t)) =
        (fun i ↦ Real.exp (t.1 i), fun j ↦ Complex.exp (t.2 j))) ∧
      L 1 = 0 ∧ ContDiffAt ℝ (∞) L 1 ∧ ∀ᶠ y in 𝓝 1, archVal (U (Multiplicative.ofAdd (L y))) = y := by
  let A := archAdd(ι, κ)
  let U : Multiplicative A →ₜ* archMul(ι, κ) :=
    { toFun := fun t ↦ (fun i ↦ Units.mk0 (Real.exp (t.toAdd.1 i)) (Real.exp_pos _).ne',
                         fun j ↦ Units.mk0 (Complex.exp (t.toAdd.2 j)) (Complex.exp_ne_zero _))
      map_one' := Prod.ext (funext fun _ ↦ Units.ext Real.exp_zero) (funext fun _ ↦ Units.ext Complex.exp_zero)
      map_mul' := fun _ _ ↦ Prod.ext (funext fun _ ↦ Units.ext (Real.exp_add _ _))
        (funext fun _ ↦ Units.ext (Complex.exp_add _ _))
      continuous_toFun := by
        apply Continuous.prodMk
        · apply continuous_pi
          intro i
          apply Units.isEmbedding_val₀.continuous_iff.mpr
          exact Real.continuous_exp.comp (((continuous_apply i).comp continuous_fst).comp
            (continuous_toAdd : Continuous (Multiplicative.toAdd : Multiplicative A → A)))
        · apply continuous_pi
          intro j
          apply Units.isEmbedding_val₀.continuous_iff.mpr
          exact Complex.continuous_exp.comp (((continuous_apply j).comp continuous_snd).comp
            (continuous_toAdd : Continuous (Multiplicative.toAdd : Multiplicative A → A))) }
  let L (y : archAdd(ι, κ)) : A := (fun i ↦ Real.log (y.1 i), fun j ↦ Complex.log (y.2 j))
  refine ⟨U, L, fun _ ↦ rfl, Prod.ext (funext fun _ ↦ Real.log_one) (funext fun _ ↦ Complex.log_one), ?_, ?_⟩
  · apply ContDiffAt.prodMk
    · apply contDiffAt_pi.mpr
      intro i
      exact (Real.contDiffAt_log.mpr (by exact one_ne_zero)).comp 1
        ((contDiff_apply ℝ _ i).comp contDiff_fst).contDiffAt
    · apply contDiffAt_pi.mpr
      intro j
      have hc : ContDiffAt ℝ (∞) Complex.log (((1 : archAdd(ι, κ)).2 j)) :=
        (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
      exact hc.comp (f := fun y : archAdd(ι, κ) ↦ y.2 j) 1
        ((contDiff_apply ℝ _ j).comp contDiff_snd).contDiffAt
  · have hr : ∀ᶠ y : archAdd(ι, κ) in 𝓝 1, ∀ i, 0 < y.1 i := eventually_all.mpr fun i ↦
      (((continuous_apply i).comp continuous_fst).continuousAt).eventually (Ioi_mem_nhds one_pos)
    have hc : ∀ᶠ y : archAdd(ι, κ) in 𝓝 1, ∀ j, y.2 j ≠ 0 := eventually_all.mpr fun j ↦
      (((continuous_apply j).comp continuous_snd).continuousAt).eventually (isOpen_ne.mem_nhds one_ne_zero)
    filter_upwards [hr, hc] with y hy hz
    exact Prod.ext (funext fun i ↦ Real.exp_log (hy i)) (funext fun j ↦ Complex.exp_log (hz j))

/-- Uniform jet bounds for a family survive composition with a fixed local chart.
Only its finitely many derivatives at the base point enter the bound. -/
private theorem archimedeanWeightedSchwartz_comp_bound
    {X Y I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : I → Y → ℂ) (L : X → Y) (x : X) (hs : ∀ u, ContDiff ℝ (∞) (g u))
    (hL : ContDiffAt ℝ (∞) L x)
    (h : ∀ n : ℕ, ∃ C : ℝ, ∀ u, ‖iteratedFDeriv ℝ n (g u) (L x)‖ ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ u, ‖iteratedFDeriv ℝ n (g u ∘ L) x‖ ≤ C := by
  classical
  choose C hC using h
  let K := ∑ i ∈ Finset.range (n+1), |C i|
  let D := 1 + ∑ i ∈ Finset.range (n+1), ‖iteratedFDeriv ℝ i L x‖
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hlocal := (hL.of_le (show (n : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  obtain ⟨s, hsub, hopen, hx⟩ := mem_nhds_iff.mp hlocal
  have hLs : ContDiffOn ℝ n L s := fun y hy ↦ (hsub hy).contDiffWithinAt
  refine ⟨n.factorial * K * D ^ n, fun u ↦ ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen n hopen hx]
  apply norm_iteratedFDerivWithin_comp_le ((hs u).of_le (by simp : (n : ℕ∞ω) ≤ ∞)).contDiffOn hLs
    le_rfl uniqueDiffOn_univ hopen.uniqueDiffOn (mapsTo_univ _ _) hx
  · intro i hi
    rw [iteratedFDerivWithin_univ]
    exact ((hC i u).trans (le_abs_self _)).trans (Finset.single_le_sum (fun j _ ↦ abs_nonneg (C j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  · intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hopen hx]
    have hb : ‖iteratedFDeriv ℝ i L x‖ ≤ D :=
      (Finset.single_le_sum (fun j _ ↦ norm_nonneg (iteratedFDeriv ℝ j L x))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))).trans (le_add_of_nonneg_left zero_le_one)
    exact hb.trans (le_self_pow₀ hD (by omega))

/-- The positive product of coordinate powers, with exponents measured relative to
the ordinary real and complex norms. -/
private def archimedeanWeightedSchwartz_power (p : ι → ℝ) (q : κ → ℝ) (u : archMul(ι, κ)) : ℝ :=
  (∏ i, ‖(u.1 i).val‖ ^ p i) * ∏ j, ‖(u.2 j).val‖ ^ q j

/-- Near the multiplicative identity use the same logarithm for every translate.
Untwisting in these relative coordinates costs a fixed smooth exponential. Thus
every coordinate power times any relative derivative is bounded uniformly. -/
private theorem archimedeanWeightedSchwartz_relative (f : 𝓦(univ)) (E : archAdd(ι, κ) → ℂ)
    (hE : ∀ u : archMul(ι, κ), E (archVal u) = f.val u)
    (p : ι → ℝ) (q : κ → ℝ) (n : ℕ) : ∃ C : ℝ, ∀ u : archMul(ι, κ),
      let F := fun y : archAdd(ι, κ) ↦ E (y * archVal u)
      ContDiffAt ℝ (∞) F 1 ∧ archimedeanWeightedSchwartz_power p q u * ‖iteratedFDeriv ℝ n F 1‖ ≤ C := by
  classical
  let A := archAdd(ι, κ)
  let G := archMul(ι, κ)
  let w : weights(ι, κ, (univ : Set ℝ)) :=
    (fun i ↦ ⟨p i, by simp⟩, fun j ↦ ⟨q j / 2, by simp⟩)
  let W := archimedeanWeightedSchwartz_power p q
  let g := archimedeanSchwartzTwist univ w f
  have hg (u : G) : g u = (W u : ℂ) * f.val u := by
    rw [show g u = _ from archimedeanSchwartzTwist_apply univ w f u, ← Complex.ofReal_mul]
    have he (j : κ) : (‖(u.2 j).val‖ ^ 2) ^ (w.2 j : ℝ) = ‖(u.2 j).val‖ ^ q j := by
      rw [← Real.rpow_natCast_mul (norm_nonneg _)]
      congr 1
      change (2 : ℝ) * (q j / 2) = q j
      ring
    simp only [he]
    rfl
  obtain ⟨U, L, hU, hL₀, hL, hloc⟩ := archimedeanWeightedSchwartz_log_chart (ι := ι) (κ := κ)
  let b (t : archAdd(ι, κ)) := (∑ i, t.1 i * p i) + ∑ j, (t.2 j).re * q j
  let Q (t : A) := (Real.exp (-(b t)) : ℂ)
  have hQ : ContDiff ℝ (∞) Q := by
    apply Complex.ofRealCLM.contDiff.comp
    apply Real.contDiff_exp.comp
    apply ContDiff.neg
    apply ContDiff.add <;> apply ContDiff.sum <;> intro k _ <;> refine ContDiff.mul ?_ contDiff_const
    · exact (contDiff_apply ℝ _ k).comp contDiff_fst
    · exact Complex.reCLM.contDiff.comp ((contDiff_apply ℝ _ k).comp contDiff_snd)
  have hw (t : A) (u : G) : W (U (Multiplicative.ofAdd t) * u) = Real.exp (b t) * W u := by
    have hr (i : ι) : ((U (Multiplicative.ofAdd t)).1 i).val = Real.exp (t.1 i) :=
      congrArg (fun x : A ↦ x.1 i) (hU t)
    have hc (j : κ) : ((U (Multiplicative.ofAdd t)).2 j).val = Complex.exp (t.2 j) :=
      congrArg (fun x : A ↦ x.2 j) (hU t)
    have hrp (i : ι) : ‖((U (Multiplicative.ofAdd t) * u).1 i).val‖ ^ p i =
        Real.exp (t.1 i * p i) * ‖(u.1 i).val‖ ^ p i := by
      change ‖((U (Multiplicative.ofAdd t)).1 i).val * (u.1 i).val‖ ^ _ = _
      rw [hr, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.mul_rpow (Real.exp_pos _).le (norm_nonneg _), Real.exp_mul]
    have hcp (j : κ) : ‖((U (Multiplicative.ofAdd t) * u).2 j).val‖ ^ q j =
        Real.exp ((t.2 j).re * q j) * ‖(u.2 j).val‖ ^ q j := by
      change ‖((U (Multiplicative.ofAdd t)).2 j).val * (u.2 j).val‖ ^ _ = _
      rw [hc, norm_mul, Complex.norm_exp, Real.mul_rpow (Real.exp_pos _).le (norm_nonneg _), Real.exp_mul]
    simp only [W, archimedeanWeightedSchwartz_power, hrp, hcp, b, Real.exp_add, Real.exp_sum,
      Finset.prod_mul_distrib]
    ring
  let P (u : G) (t : A) := g (U (Multiplicative.ofAdd t) * u)
  have hP (u : G) : ContDiff ℝ (∞) (P u) := complexExponentialDecay_contDiffOn_alongTranslate U g u
  let T (u : G) (t : A) := Q t * P u t
  have hT (u : G) : ContDiff ℝ (∞) (T u) := hQ.mul (hP u)
  choose D hD using archimedeanWeightedSchwartz_translate_bound U g
  have hB (k : ℕ) : ∃ C, ∀ u, ‖iteratedFDeriv ℝ k (T u) (L 1)‖ ≤ C := by
    rw [hL₀]
    refine ⟨∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i Q 0‖ * D (k-i), fun u ↦ ?_⟩
    exact (norm_iteratedFDeriv_mul_le hQ (hP u) 0 (by simp : (k : ℕ∞ω) ≤ ∞)).trans
      (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hD (k-i) u) (by positivity))
  obtain ⟨C, hC⟩ := archimedeanWeightedSchwartz_comp_bound T L 1 hT hL hB n
  refine ⟨C, fun u ↦ ?_⟩
  let F (y : A) := E (y * archVal u)
  have hwp : 0 < W u := mul_pos (Finset.prod_pos fun i _ ↦
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (u.1 i).ne_zero) _) (Finset.prod_pos fun j _ ↦
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (u.2 j).ne_zero) _)
  have heq : (W u • F) =ᶠ[𝓝 1] T u ∘ L := by
    filter_upwards [hloc] with y hy
    change (W u : ℂ) * E (y * archVal u) = (Real.exp (-(b (L y))) : ℂ) * g (U (Multiplicative.ofAdd (L y)) * u)
    conv_lhs => rw [← hy]
    rw [show archVal (U (Multiplicative.ofAdd (L y))) * archVal u =
      archVal (U (Multiplicative.ofAdd (L y)) * u) from rfl, hE, hg, hw, Real.exp_neg,
      Complex.ofReal_inv, Complex.ofReal_mul]
    field_simp
  have hF' := ((hT u).contDiffAt.comp 1 hL).congr_of_eventuallyEq heq
  have hF : ContDiffAt ℝ (∞) F 1 := by
    have h := hF'.const_smul (W u)⁻¹
    simpa only [← Pi.smul_def, inv_smul_smul₀ hwp.ne'] using h
  refine ⟨hF, ?_⟩
  have h := (heq.iteratedFDeriv ℝ n).eq_of_nhds
  rw [iteratedFDeriv_const_smul_apply (hF.of_le (by simp))] at h
  have hn := congrArg norm h
  rw [norm_smul, Real.norm_of_nonneg hwp.le] at hn
  exact hn.le.trans (hC u)

private theorem archimedeanWeightedSchwartz_single {K : Type*} [Fintype K] [DecidableEq K]
    (r : K → ℝ) (i : K) (s : ℝ) : (∏ j, r j ^ ((Pi.single i s : K → ℝ) j)) = r i ^ s := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  rw [Finset.prod_eq_one (fun j hj ↦ ?_), one_mul, Pi.single_eq_same]
  rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), Real.rpow_zero]

private theorem archimedeanWeightedSchwartz_finite_bound {K G : Type*} [Fintype K] {g : G → K → ℝ}
    (hb : ∀ k, ∃ c : ℝ, ∀ u, g u k ≤ c) : ∃ c ≥ 0, ∀ u k, g u k ≤ c := by
  choose c hc using hb
  exact ⟨∑ k, |c k|, Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), fun u k ↦
    ((hc k u).trans (le_abs_self _)).trans (Finset.single_le_sum (fun k _ ↦ abs_nonneg (c k)) (Finset.mem_univ k))⟩

/-- Bounding all coordinate twists controls any power of the largest coordinate or
inverse coordinate. Taking finite sums of constants also works with no places. -/
private theorem archimedeanWeightedSchwartz_max_bound (d : archMul(ι, κ) → ℝ) (hd : ∀ u, 0 ≤ d u)
    (h : ∀ (p : ι → ℝ) (q : κ → ℝ), ∃ C : ℝ, ∀ u, archimedeanWeightedSchwartz_power p q u * d u ≤ C)
    (m : ℕ) : ∃ C ≥ 0, ∀ u : archMul(ι, κ),
      (max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) ^ m * d u ≤ C := by
  classical
  have hr (s : ℝ) : ∃ C ≥ 0, ∀ (u : archMul(ι, κ)) (i : ι), ‖(u.1 i).val‖ ^ s * d u ≤ C := by
    apply archimedeanWeightedSchwartz_finite_bound
    intro i
    obtain ⟨C, hC⟩ := h (Pi.single i s) 0
    exact ⟨C, fun u ↦ by simpa [archimedeanWeightedSchwartz_power, archimedeanWeightedSchwartz_single] using hC u⟩
  have hc (s : ℝ) : ∃ C ≥ 0, ∀ (u : archMul(ι, κ)) (j : κ), ‖(u.2 j).val‖ ^ s * d u ≤ C := by
    apply archimedeanWeightedSchwartz_finite_bound
    intro j
    obtain ⟨C, hC⟩ := h 0 (Pi.single j s)
    exact ⟨C, fun u ↦ by simpa [archimedeanWeightedSchwartz_power, archimedeanWeightedSchwartz_single] using hC u⟩
  obtain ⟨C₀, h₀⟩ := h 0 0
  obtain ⟨R, hR, h₁⟩ := hr m
  obtain ⟨T, hT, h₂⟩ := hc m
  obtain ⟨R', hR', h₃⟩ := hr (-m)
  obtain ⟨T', hT', h₄⟩ := hc (-m)
  let C := |C₀| + R + T + R' + T'
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, fun u ↦ ?_⟩
  have base : d u ≤ C := by
    have : d u ≤ C₀ := by simpa [archimedeanWeightedSchwartz_power] using h₀ u
    dsimp [C]; linarith [le_abs_self C₀]
  have join {a b : ℝ} (ha : a ^ m * d u ≤ C) (hb : b ^ m * d u ≤ C) : max a b ^ m * d u ≤ C := by
    rcases max_choice a b with h | h <;> rwa [h]
  apply join (by simpa using base)
  apply join <;> rw [Prod.norm_def] <;> apply join <;>
    apply archimedeanFlatSchwartz_restrict_pi_bound _ _ _ _ (hd u) base hC
  · intro i
    have hh : ‖(u.1 i).val‖ ^ m * d u ≤ R := by simpa using h₁ u i
    apply le_trans hh
    change _ ≤ |C₀| + R + T + R' + T'
    linarith [abs_nonneg C₀]
  · intro j
    have hh : ‖(u.2 j).val‖ ^ m * d u ≤ T := by simpa using h₂ u j
    apply le_trans hh
    change _ ≤ |C₀| + R + T + R' + T'
    linarith [abs_nonneg C₀]
  · intro i
    have hh := h₃ u i
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow, ← norm_inv] at hh
    change ‖(↑((u.1 i)⁻¹) : ℝ)‖ ^ m * d u ≤ C
    rw [Units.val_inv_eq_inv_val]
    apply le_trans hh
    change _ ≤ |C₀| + R + T + R' + T'
    linarith [abs_nonneg C₀]
  · intro j
    have hh := h₄ u j
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, ← inv_pow, ← norm_inv] at hh
    change ‖(↑((u.2 j)⁻¹) : ℂ)‖ ^ m * d u ≤ C
    rw [Units.val_inv_eq_inv_val]
    apply le_trans hh
    change _ ≤ |C₀| + R + T + R' + T'
    linarith [abs_nonneg C₀]

/-- Rescaling a relative derivative back to the additive variables costs at most one
inverse tuple norm per derivative. The estimate with that many extra powers absorbs it. -/
private theorem archimedeanWeightedSchwartz_additive_bounds (f : 𝓦(univ)) (E : archAdd(ι, κ) → ℂ)
    (hE : ∀ u : archMul(ι, κ), E (archVal u) = f.val u) :
    (∀ u : archMul(ι, κ), ContDiffAt ℝ (∞) E (archVal u)) ∧ ∀ n k : ℕ, ∃ C ≥ 0,
      ∀ u : archMul(ι, κ), (max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)) ^ k *
        ‖iteratedFDeriv ℝ n E (archVal u)‖ ≤ C := by
  let A := archAdd(ι, κ)
  let G := archMul(ι, κ)
  let z (u : G) : Aˣ := MulEquiv.prodUnits.symm (MulEquiv.piUnits.symm u.1, MulEquiv.piUnits.symm u.2)
  let F (u : G) (y : A) := E (y * (z u).val)
  let m (u : G) := (ContinuousLinearMap.mul ℝ A) (z u).val
  have hz (u : G) : (z u⁻¹).val * (z u).val = 1 := (z u).inv_val
  have hmul (u : G) (x : A) : m u⁻¹ (m u x) = x := by
    change (z u⁻¹).val * ((z u).val * x) = x
    rw [← mul_assoc, hz, one_mul]
  let e (u : G) := ContinuousLinearEquiv.equivOfInverse (m u⁻¹) (m u)
    (show LeftInverse (m u) (m u⁻¹) by intro x; simpa only [inv_inv] using hmul u⁻¹ x) (hmul u)
  have he (u : G) : e u (archVal u) = 1 := hz u
  have hcomp (u : G) : F u ∘ e u = E := by
    funext x
    change E (((z u⁻¹).val * x) * (z u).val) = E x
    rw [mul_right_comm, hz, one_mul]
  have hs (u : G) : ContDiffAt ℝ (∞) (F u) 1 :=
    ((archimedeanWeightedSchwartz_relative f E hE 0 0 0).choose_spec u).1
  constructor
  · intro u
    rw [← hcomp u]
    apply ContDiffAt.comp (g := F u) (f := e u)
    · rw [he]; exact hs u
    · exact (e u).contDiff.contDiffAt
  · intro n k
    let d (u : G) := ‖iteratedFDeriv ℝ n (F u) 1‖
    have hb (p : ι → ℝ) (q : κ → ℝ) : ∃ C, ∀ u, archimedeanWeightedSchwartz_power p q u * d u ≤ C :=
      (archimedeanWeightedSchwartz_relative f E hE p q n).imp fun _ h u ↦ (h u).2
    obtain ⟨C, hC, h⟩ := archimedeanWeightedSchwartz_max_bound d (fun _ ↦ norm_nonneg _) hb (k+n)
    refine ⟨C, hC, fun u ↦ ?_⟩
    let M := max 1 (max ‖archVal u‖ ‖archVal (u⁻¹)‖)
    have hM : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
    have hnorm : ‖(e u : A →L[ℝ] A)‖ ≤ M := (ContinuousLinearMap.opNorm_mul_apply_le
      ℝ A (z u⁻¹).val).trans ((le_max_right _ _).trans (le_max_right _ _))
    have heq := (e u).iteratedFDerivWithin_comp_right (F u) uniqueDiffOn_univ (mem_univ (e u (archVal u))) n
    rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ, hcomp, he] at heq
    rw [heq]
    have hle := (iteratedFDeriv ℝ n (F u) 1).norm_compContinuousLinearMap_le
      (fun _ : Fin n ↦ (e u : A →L[ℝ] A))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
    have ht := hle.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (norm_nonneg _))
    refine (mul_le_mul_of_nonneg_left ht (pow_nonneg hM k)).trans ?_
    change M ^ k * (d u * M ^ n) ≤ C
    rw [mul_left_comm, ← pow_add, mul_comm]
    exact h u

/-- A quadratic bound in distance to a wall point gives zero differential there. -/
private theorem archimedeanWeightedSchwartz_wall_deriv {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {g : X → Y} {x : X} (hx : g x = 0) (C : ℝ) (h : ∀ y, ‖g y‖ ≤ C * ‖y-x‖ ^ 2) :
    HasFDerivAt g (0 : X →L[ℝ] Y) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have ht : Tendsto (fun y : X ↦ C * ‖y - x‖) (𝓝 x) (𝓝 0) := by
    have ht : ContinuousAt (fun y : X ↦ C * ‖y - x‖) x :=
      (continuous_const.mul (continuous_id.sub continuous_const).norm).continuousAt
    simpa only [sub_self, norm_zero, mul_zero] using ht.tendsto
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with y hy
  simp [hx]
  exact (h y).trans ((by ring : C * ‖y-x‖ ^ 2 = (C * ‖y-x‖) * ‖y-x‖).le.trans
    (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)))

/-- Paper: Lemma 5.3.3.3(3), p. 253. An all-exponent weighted function on
the punctured lines admits an ordinary Schwartz extension in additive coordinates. -/
private theorem archimedeanWeightedSchwartz_exists_zero_extension (f : 𝓦(univ)) :
    ∃ g : 𝓢(archAdd(ι, κ), ℂ), ∀ u : archMul(ι, κ), g (archVal u) = f.val u := by
  classical
  let A := archAdd(ι, κ)
  let G := archMul(ι, κ)
  let val : G → A := archVal
  have inj : Injective val := fun u v h ↦ Prod.ext
    (funext fun i ↦ Units.ext (congrArg (fun z : A ↦ z.1 i) h))
    (funext fun j ↦ Units.ext (congrArg (fun z : A ↦ z.2 j) h))
  let E := Function.extend val f.val (fun _ ↦ 0)
  have hE (u : G) : E (val u) = f.val u := inj.extend_apply _ _ _
  have h0 (x : A) (hx : x ∉ range val) : E x = 0 := Function.extend_apply' _ _ _ hx
  obtain ⟨hs, hb⟩ := archimedeanWeightedSchwartz_additive_bounds f E hE
  let J (n : ℕ) := iteratedFDeriv ℝ n E
  have wall (x : A) (hx : x ∉ range val) : meetsWall(x) := by
    by_contra! h
    exact hx ⟨(fun i ↦ Units.mk0 (x.1 i) (h.1 i), fun j ↦ Units.mk0 (x.2 j) (h.2 j)), rfl⟩
  have hd (n : ℕ) (hz : ∀ x ∉ range val, J n x = 0) (x : A) (hx : x ∉ range val) :
      HasFDerivAt (J n) (0 : A →L[ℝ] _) x := by
    obtain ⟨C, hC, hh⟩ := hb n 2
    apply archimedeanWeightedSchwartz_wall_deriv (hz x hx) C
    intro y
    by_cases hy : y ∈ range val
    · obtain ⟨u, rfl⟩ := hy
      let M := max 1 (max ‖val u‖ ‖val u⁻¹‖)
      have small (r : ℝ) (hr : 0 < r) (hinv : r⁻¹ ≤ M) (hle : r ≤ ‖val u - x‖) :
          ‖J n (val u)‖ ≤ C * ‖val u - x‖ ^ 2 := by
        have h := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hr.le) hinv 2)
          (norm_nonneg (J n (val u)))).trans (hh u)
        rw [inv_pow, inv_mul_eq_div] at h
        exact ((div_le_iff₀ (pow_pos hr 2)).mp h).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hr.le hle 2) hC)
      rcases wall x hx with ⟨i, hi⟩ | ⟨j, hj⟩
      · apply small ‖(u.1 i).val‖ (norm_pos_iff.mpr (u.1 i).ne_zero)
          ((archimedeanFlatSchwartz_restrict_coords_bound u).1 i).2
        have h := (norm_le_pi_norm (val u - x).1 i).trans (norm_fst_le (val u - x))
        change ‖(u.1 i).val - x.1 i‖ ≤ _ at h
        simpa only [hi, sub_zero] using h
      · apply small ‖(u.2 j).val‖ (norm_pos_iff.mpr (u.2 j).ne_zero)
          ((archimedeanFlatSchwartz_restrict_coords_bound u).2 j).2
        have h := (norm_le_pi_norm (val u - x).2 j).trans (norm_snd_le (val u - x))
        change ‖(u.2 j).val - x.2 j‖ ≤ _ at h
        simpa only [hj, sub_zero] using h
    · rw [hz y hy, norm_zero]
      positivity
  have hz (n : ℕ) : ∀ x ∉ range val, J n x = 0 := by
    induction n with
    | zero =>
      intro x hx
      exact norm_eq_zero.mp (by simp only [J, norm_iteratedFDeriv_zero, h0 x hx, norm_zero])
    | succ n ih =>
      intro x hx
      ext v
      rw [show J (n+1) x v = _ from iteratedFDeriv_succ_apply_left v, (hd n ih x hx).fderiv]
      rfl
  have hdiff (n : ℕ) : Differentiable ℝ (J n) := by
    intro x
    by_cases hx : x ∈ range val
    · obtain ⟨u, rfl⟩ := hx
      exact (hs u).differentiableAt_iteratedFDeriv (mod_cast ENat.natCast_lt_top n)
    · exact (hd n (hz n) x hx).differentiableAt
  refine ⟨{ toFun := E, smooth' := contDiff_of_differentiable_iteratedFDeriv (fun n _ ↦ hdiff n),
            decay' := ?_ }, hE⟩
  intro k n
  obtain ⟨C, hC, hh⟩ := hb n k
  refine ⟨C, fun x ↦ ?_⟩
  by_cases hx : x ∈ range val
  · obtain ⟨u, rfl⟩ := hx
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ((le_max_left _ _).trans
      (le_max_right _ _)) k) (norm_nonneg _)).trans (hh u)
  · change ‖x‖ ^ k * ‖J n x‖ ≤ C
    rw [hz n x hx, norm_zero, mul_zero]
    exact hC

/-- The points with every real and complex coordinate nonzero are dense. -/
private theorem archimedeanVal_denseRange :
    DenseRange (archVal : archMul(ι, κ) → archAdd(ι, κ)) := by
  have hd (K : Type) [NontriviallyNormedField K] : DenseRange (Units.val : Kˣ → K) := by
    apply (dense_compl_singleton (0 : K)).mono
    intro x hx
    exact ⟨Units.mk0 x hx, rfl⟩
  exact (DenseRange.piMap (fun _ : ι ↦ hd ℝ)).prodMap
    (DenseRange.piMap (fun _ : κ ↦ hd ℂ))

/-- The product of the squared absolute values is smooth and vanishes at every wall. -/
private def archimedeanWallProduct (x : archAdd(ι, κ)) : ℂ :=
  (∏ i, ((x.1 i : ℂ) ^ 2)) * ∏ j, (Complex.normSq (x.2 j) : ℂ)

private theorem archimedeanWallProduct_smooth :
    ContDiff ℝ (∞) (archimedeanWallProduct (ι := ι) (κ := κ)) := by
  have hn : ContDiff ℝ (∞) Complex.normSq := by
    have hRe := Complex.reCLM.contDiff (n := (∞ : ℕ∞ω))
    have hIm := Complex.imCLM.contDiff (n := (∞ : ℕ∞ω))
    exact (hRe.mul hRe).add (hIm.mul hIm)
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    apply ContDiff.pow
    apply Complex.ofRealCLM.contDiff.comp
    fun_prop
  · apply contDiff_prod
    intro j _
    apply Complex.ofRealCLM.contDiff.comp
    apply hn.comp
    fun_prop

private theorem archimedeanWallProduct_zero (x : archAdd(ι, κ)) (hx : meetsWall(x)) :
    archimedeanWallProduct x = 0 := by
  classical
  rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])) _
  · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]))

/-- Division by the wall product subtracts two from each real exponent and one
from each complex exponent in the defining family of Schwartz twists. -/
private theorem archimedeanWeightedSchwartz_div_wall (f : 𝓦(univ)) :
    ∃ h : 𝓦(univ), ∀ u : archMul(ι, κ),
      f.val u = archimedeanWallProduct (archVal u) * h.val u := by
  classical
  let P (u : archMul(ι, κ)) := archimedeanWallProduct (archVal u)
  have hP (u : archMul(ι, κ)) : P u ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (u.1 i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ Complex.ofReal_ne_zero.mpr
      ((Complex.normSq_pos.mpr (u.2 j).ne_zero).ne'))
  let h (u : archMul(ι, κ)) := f.val u / P u
  have hh : h ∈ archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) univ := by
    simp only [archimedeanWeightedSchwartzSubmodule, Submodule.mem_iInf, Submodule.mem_comap]
    intro a
    let b : weights(ι, κ, univ) :=
      (fun i ↦ ⟨a.1 i - 2, by simp⟩, fun j ↦ ⟨a.2 j - 1, by simp⟩)
    have he : weightMap(a) h = weightMap(b) f.val := by
      funext u
      change _ * _ * (f.val u / P u) = _ * _ * f.val u
      have hreal (i : ι) : ‖((u.1 i).val)‖ ^ ((a.1 i : ℝ) - 2) =
          ‖((u.1 i).val)‖ ^ (a.1 i : ℝ) / (u.1 i).val ^ 2 := by
        rw [Real.rpow_sub (norm_pos_iff.mpr (u.1 i).ne_zero), Real.rpow_two,
          Real.norm_eq_abs, sq_abs]
      have hcomplex (j : κ) : (‖((u.2 j).val)‖ ^ 2) ^ ((a.2 j : ℝ) - 1) =
          (‖((u.2 j).val)‖ ^ 2) ^ (a.2 j : ℝ) / Complex.normSq (u.2 j).val := by
        rw [Real.rpow_sub (pow_pos (norm_pos_iff.mpr (u.2 j).ne_zero) _),
          Real.rpow_one, Complex.normSq_eq_norm_sq]
      dsimp only [b, P, archimedeanWallProduct]
      simp_rw [hreal, hcomplex, Finset.prod_div_distrib]
      push_cast
      ring
    rw [he]
    exact (archimedeanSchwartzTwist univ b f).property
  exact ⟨⟨h, hh⟩, fun u ↦ by change _ = P u * (f.val u / P u); rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hP u)]⟩

/-- Repeated division by a smooth wall factor forces every jet of the ordinary
Schwartz zero extension to vanish at every coordinate wall. -/
private theorem archimedeanWeightedSchwartz_exists_flat_extension (f : 𝓦(univ)) :
    ∃ g : archimedeanFlatSchwartz (ι := ι) (κ := κ),
      ∀ u : archMul(ι, κ), g.val (archVal u) = f.val u := by
  classical
  choose E hE using archimedeanWeightedSchwartz_exists_zero_extension (ι := ι) (κ := κ)
  have hjet (x : archAdd(ι, κ)) (hx : meetsWall(x)) (n : ℕ) :
      ∀ a : 𝓦(univ), iteratedFDeriv ℝ n (E a : archAdd(ι, κ) → ℂ) x = 0 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro a
      obtain ⟨b, hb⟩ := archimedeanWeightedSchwartz_div_wall a
      have he : (E a : archAdd(ι, κ) → ℂ) = fun y ↦ archimedeanWallProduct y * E b y := by
        apply archimedeanVal_denseRange.equalizer (E a).continuous
          (archimedeanWallProduct_smooth.continuous.mul (E b).continuous)
        exact funext fun u ↦ (hE a u).trans ((hb u).trans (congrArg (_ * ·) (hE b u).symm))
      rw [he, ← norm_eq_zero]
      apply le_antisymm _ (norm_nonneg _)
      apply (norm_iteratedFDeriv_mul_le archimedeanWallProduct_smooth ((E b).smooth ⊤) x
        (n := n) (by simp)).trans
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      by_cases h : i = 0
      · subst i
        simp [norm_iteratedFDeriv_zero, archimedeanWallProduct_zero x hx]
      · have hi := Finset.mem_range.mp hi
        simp [ih (n - i) (by omega) b]
  refine ⟨⟨E f, ?_⟩, hE f⟩
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply]
  rintro ⟨x, hx⟩ n v
  rw [hjet x hx n f]
  rfl


/-- Paper: Lemma 5.3.3.3(3), p. 253.
Inverse half of the restriction equivalence, for a fixed restriction map: a function of
the all-exponent weighted space extends by zero across the coordinate walls to a flat
Schwartz function, the extension is continuous, and it is a left inverse of restriction. -/
theorem archimedeanWeightedSchwartz_zeroExtension
    (R : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) →L[ℂ] 𝓦(univ))
    (hR : ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (R f).val u =
      f.val (archVal u)) :
    ∃ E : 𝓦(univ) →L[ℂ] ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)),
      (∀ (f : 𝓦(univ)) (u : archMul(ι, κ)), (E f).val (archVal u) = f.val u) ∧
        ∀ f, E (R f) = f := by
  classical
  let A := ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ))
  let : CompleteSpace 𝓢(archAdd(ι, κ), ℂ) := completeSpace_schwartzMap
  let : CompleteSpace A := (archimedeanFlatSchwartz_isClosed (ι := ι) (κ := κ)).completeSpace_coe
  let : PolynormableSpace ℂ 𝓢(archAdd(ι, κ), ℂ) :=
    (schwartz_withSeminorms ℂ _ ℂ).toPolynormableSpace
  have : (uniformity 𝓢(archAdd(ι, κ), ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : MetrizableSpace 𝓢(archAdd(ι, κ), ℂ) := UniformSpace.metrizableSpace
  let : IsUniformAddGroup A := (archimedeanFlatSchwartz (ι := ι) (κ := κ)).toAddSubgroup.isUniformAddGroup
  have hA : IsFrechetTVS A := by
    refine ⟨inferInstance, inferInstance, MetrizableSpace.subtype _, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hB := archimedeanWeightedSchwartz_frechet (ι := ι) (κ := κ)
    isOpen_univ (inferInstance : OrdConnected (univ : Set ℝ)) univ_nonempty
  have hi : Function.Injective R := by
    intro f g h
    apply Subtype.ext
    apply SchwartzMap.ext
    exact congrFun (archimedeanVal_denseRange.equalizer f.val.continuous g.val.continuous
      (funext fun u ↦ (hR f u).symm.trans
        ((congrArg (fun a : 𝓦(univ) ↦ a.val u) h).trans (hR g u))))
  have hs : Function.Surjective R := by
    intro f
    obtain ⟨g, hg⟩ := archimedeanWeightedSchwartz_exists_flat_extension f
    exact ⟨g, Subtype.ext (funext fun u ↦ (hR g u).trans (hg u))⟩
  have hopen : IsOpenMap R := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hB)
    (X := fun _ ↦ A) (fun _ ↦ hA) (fun _ ↦ ContinuousLinearMap.id ℂ A) (fun _ ↦ Subset.rfl)
    (fun x ↦ ⟨0, x, rfl⟩) R hs
  let e := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective R.toLinearMap ⟨hi, hs⟩)
    ⟨R.continuous, hopen, hi, hs⟩
  refine ⟨e.symm.toContinuousLinearMap, fun f u ↦ ?_, fun f ↦ e.symm_apply_apply f⟩
  exact (hR (e.symm f) u).symm.trans (congrArg (fun a : 𝓦(univ) ↦ a.val u) (e.apply_symm_apply f))

/-- Paper: Lemma 5.3.3.3(3), p. 253.
Restriction to the product of the punctured lines identifies flat Schwartz functions
with the all-exponent weighted space. The inverse extends by zero. -/
theorem archimedeanFlatSchwartz_restrict_equiv :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ] 𝓦(univ),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (e f).val u = f.val (archVal u) := by
  obtain ⟨R, hR⟩ := archimedeanFlatSchwartz_restrict_to_weighted (ι := ι) (κ := κ)
  obtain ⟨E, hE, hER⟩ :=
    archimedeanWeightedSchwartz_zeroExtension (ι := ι) (κ := κ) R hR
  have hRE : ∀ g : 𝓦(univ), R (E g) = g := by
    intro g
    apply Subtype.ext
    funext u
    rw [hR (E g) u, hE g u]
  exact ⟨ContinuousLinearEquiv.equivOfInverse R E hER hRE, hR⟩

/-- The modulus of a quasi-character is a product of real powers of the coordinate norms. -/
private theorem archimedeanFlatSchwartz_quasiCharacter_norm
    (c : QuasiCharacter (archMul(ι, κ))) :
    ∃ (a : ι → ℝ) (b : κ → ℝ), ∀ u : archMul(ι, κ),
      ‖c u‖ = (∏ i, ‖(u.1 i).val‖ ^ a i) * ∏ j, (‖(u.2 j).val‖ ^ 2) ^ b j := by
  classical
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let c₁ := c.comp (ContinuousMonoidHom.inl (ι → ℝˣ) (κ → ℂˣ))
  let c₂ := c.comp (ContinuousMonoidHom.inr (ι → ℝˣ) (κ → ℂˣ))
  let r (i : ι) : QuasiCharacter ℝˣ :=
    c₁.comp ⟨MonoidHom.mulSingle (fun _ : ι ↦ ℝˣ) i, continuous_mulSingle (A := fun _ : ι ↦ ℝˣ) i⟩
  let t (j : κ) : QuasiCharacter ℂˣ :=
    c₂.comp ⟨MonoidHom.mulSingle (fun _ : κ ↦ ℂˣ) j, continuous_mulSingle (A := fun _ : κ ↦ ℂˣ) j⟩
  have hr := realCoordinate_mul_allExponentialDecay_modulation.1
  have ht := complexCoordinate_mul_allExponentialDecay_modulation.1
  let a (i : ι) := quasiCharacterAbscissa (archimedeanUnitModulation ℝ 1) hr.1 hr.2 (r i)
  let b (j : κ) := quasiCharacterAbscissa (archimedeanUnitModulation ℂ 2) ht.1 ht.2 (t j)
  refine ⟨a, b, fun u ↦ ?_⟩
  have hprod : c u = (∏ i, r i (u.1 i)) * ∏ j, t j (u.2 j) := by
    change c u = (∏ i, c₁ (Pi.mulSingle i (u.1 i))) * ∏ j, c₂ (Pi.mulSingle j (u.2 j))
    rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle, Finset.univ_prod_mulSingle]
    change c u = c (u.1, 1) * c (1, u.2)
    rw [← map_mul]
    simp
  have h₁ (i : ι) : ‖r i (u.1 i)‖ = ‖(u.1 i).val‖ ^ a i := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (archimedeanUnitModulation ℝ 1) hr.1 hr.2]
    change (((archimedeanUnitModulation ℝ 1 (u.1 i)).val : ℝ) ^ a i) = _
    rw [archimedeanUnitModulation_apply, pow_one]
  have h₂ (j : κ) : ‖t j (u.2 j)‖ = (‖(u.2 j).val‖ ^ 2) ^ b j := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (archimedeanUnitModulation ℂ 2) ht.1 ht.2]
    change (((archimedeanUnitModulation ℂ 2 (u.2 j)).val : ℝ) ^ b j) = _
    rw [archimedeanUnitModulation_apply]
  simp only [hprod, norm_mul, norm_prod, h₁, h₂]

/-- On the all-exponent space the modulus shifts the weights, and the unitary factor
acts continuously on each Schwartz–Bruhat twist. -/
private theorem archimedeanFlatSchwartz_quasiCharacter_weighted
    (c : QuasiCharacter (archMul(ι, κ))) :
    ∃ M : 𝓦(univ) →L[ℂ] 𝓦(univ), ∀ f u, (M f).val u = c u * f.val u := by
  classical
  let G := archMul(ι, κ)
  let W := weights(ι, κ, (univ : Set ℝ))
  let E := archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) univ
  let P : SeminormFamily ℂ E (W × {p : Seminorm ℂ (SchwartzBruhat G) // Continuous p}) :=
    fun i ↦ i.2.val.comp (archimedeanSchwartzTwist univ i.1)
  let L : E →ₗ[ℂ] (G → ℂ) := (LinearMap.mulLeft ℂ (⇑c)).comp E.subtype
  obtain ⟨a, b, hab⟩ := archimedeanFlatSchwartz_quasiCharacter_norm c
  have hn (u : G) : (‖c u‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ((Group.isUnit u).map c).ne_zero)
  let η : PontryaginDual G :=
    { toFun := fun u ↦ ⟨c u / (‖c u‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
          div_self (Complex.ofReal_ne_zero.mp (hn u))])⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun u v ↦ Circle.ext (by
        change c (u * v) / (‖c (u * v)‖ : ℂ) = (c u / (‖c u‖ : ℂ)) * (c v / (‖c v‖ : ℂ))
        rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm])
      continuous_toFun := (c.continuous.div (Complex.continuous_ofReal.comp c.continuous.norm) hn).subtype_mk _ }
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  obtain ⟨U, hU⟩ := schwartzBruhat_mul_unitaryCharacter η
  let shift (w : W) : W :=
    (fun i ↦ ⟨(w.1 i : ℝ) + a i, by simp⟩, fun j ↦ ⟨(w.2 j : ℝ) + b j, by simp⟩)
  have hshift (w : W) (f : E) :
      weightMap(w) (L f) = (U (archimedeanSchwartzTwist univ (shift w) f)).val := by
    funext u
    rw [hU, archimedeanSchwartzTwist_apply]
    change _ = c u / (‖c u‖ : ℂ) *
      (((∏ i, ‖(u.1 i).val‖ ^ ((w.1 i : ℝ) + a i) : ℝ) : ℂ) *
       ((∏ j, (‖(u.2 j).val‖ ^ 2) ^ ((w.2 j : ℝ) + b j) : ℝ) : ℂ) * f.val u)
    have hr (i : ι) : 0 < ‖(u.1 i).val‖ := norm_pos_iff.mpr (u.1 i).ne_zero
    have ht (j : κ) : 0 < ‖(u.2 j).val‖ ^ 2 := pow_pos (norm_pos_iff.mpr (u.2 j).ne_zero) _
    simp only [Real.rpow_add (hr _), Real.rpow_add (ht _), Finset.prod_mul_distrib, Complex.ofReal_mul]
    change _ * _ * (c u * f.val u) = _
    have he := congrArg (fun x : ℝ ↦ (x : ℂ)) (hab u)
    push_cast only [Complex.ofReal_mul] at he
    field_simp [hn u]
    rw [he]
    ring
  let M : 𝓦(univ) →ₗ[ℂ] 𝓦(univ) := L.codRestrict E fun f ↦ (Submodule.mem_iInf _).mpr fun w ↦
    (Submodule.mem_comap.mpr ((hshift w f) ▸ (U (archimedeanSchwartzTwist univ (shift w) f)).property))
  have hM (w : W) (f : E) : archimedeanSchwartzTwist univ w (M f) =
      U (archimedeanSchwartzTwist univ (shift w) f) := Subtype.ext (hshift w f)
  have hP := withGeneratingSeminorms_spec E P
  have hc : Continuous M := by
    apply hP.continuous_of_continuous_comp M
    rintro ⟨w, p⟩
    let q := p.val.comp U.toLinearMap
    have hq : Continuous q := p.property.comp U.continuous
    exact (hP.continuous_seminorm (shift w, ⟨q, hq⟩)).congr fun f ↦ congrArg p.val (hM w f).symm
  exact ⟨⟨M, hc⟩, fun _ _ ↦ rfl⟩

/-- Paper: Lemma 5.3.3.3(3), p. 253.
A continuous quasi-character on the product of punctured fields acts by multiplication
through a unique linear homeomorphism of the flat Schwartz space. -/
theorem archimedeanFlatSchwartz_quasiCharacter_mul (c : QuasiCharacter (archMul(ι, κ))) :
    ∃! M : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ]
        ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)),
        (M f).val (archVal u) = c u * f.val (archVal u) := by
  obtain ⟨e, he⟩ := archimedeanFlatSchwartz_restrict_equiv (ι := ι) (κ := κ)
  let d := c.comp (ContinuousMonoidHom.inv (archMul(ι, κ)))
  obtain ⟨A, hA⟩ := archimedeanFlatSchwartz_quasiCharacter_weighted c
  obtain ⟨B, hB⟩ := archimedeanFlatSchwartz_quasiCharacter_weighted d
  have hleft (f : 𝓦(univ)) : B (A f) = f := by
    apply Subtype.ext
    funext u
    rw [hB, hA, ← mul_assoc]
    change c u⁻¹ * c u * _ = _
    rw [← map_mul, inv_mul_cancel, map_one, one_mul]
  have hright (f : 𝓦(univ)) : A (B f) = f := by
    apply Subtype.ext
    funext u
    rw [hA, hB, ← mul_assoc]
    change c u * c u⁻¹ * _ = _
    rw [← map_mul, mul_inv_cancel, map_one, one_mul]
  let M := (e.trans (ContinuousLinearEquiv.equivOfInverse A B hleft hright)).trans e.symm
  have hM (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)) :
      (M f).val (archVal u) = c u * f.val (archVal u) := by
    rw [← he (M f), ← he f]
    change (e (e.symm (A (e f)))).val u = _
    rw [e.apply_symm_apply, hA]
  refine ⟨M, hM, fun N hN ↦ ?_⟩
  apply ContinuousLinearEquiv.ext
  funext f
  apply e.injective
  apply Subtype.ext
  funext u
  rw [he, he, hN, hM]

end ArchimedeanProduct

section ArchimedeanMellin

local notation "realProfile(" f ", " ε ")" =>
  (fun t : ℝ ↦ f t + (-1 : ℂ) ^ (ε).val * f (-t))
local notation "unitAngle(" θ ")" => Complex.exp ((θ : ℂ) * Complex.I)
local notation "complexProfile(" f ", " n ")" =>
  (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (unitAngle(θ)) ^ n * f ((Real.sqrt t : ℂ) * unitAngle(θ)))

/-- A Schwartz function is `O(x^(-a))` at infinity for every `a`. -/
private theorem realArchimedeanMellin_existsUnique_isBigO_atTop (G : SchwartzMap ℝ ℂ) (a : ℝ) :
    (G : ℝ → ℂ) =O[atTop] (· ^ (-a)) := by
  have h := G.isBigO_cocompact_rpow (-a)
  refine (h.mono atTop_le_cocompact).congr' (EventuallyEq.refl _ _) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos hx]

/-- A Schwartz function is bounded near zero. -/
private theorem realArchimedeanMellin_existsUnique_isBigO_zero (G : SchwartzMap ℝ ℂ) :
    (G : ℝ → ℂ) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  have hb : (G : ℝ → ℂ) =O[⊤] (fun _ ↦ (1 : ℝ)) := by
    obtain ⟨C, -, hC⟩ := G.decay 0 0
    refine Asymptotics.isBigO_iff.mpr ⟨C, .of_forall fun x ↦ ?_⟩
    simpa using hC x
  refine (hb.mono le_top).congr' (EventuallyEq.refl _ _) (.of_forall fun x ↦ ?_)
  simp

private theorem realArchimedeanMellin_existsUnique_convergent (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent G s :=
  mellinConvergent_of_isBigO_rpow (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1)) (lt_add_one _) (realArchimedeanMellin_existsUnique_isBigO_zero G) (by simpa using hs)

private theorem realArchimedeanMellin_existsUnique_differentiableAt (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin G) s :=
  mellin_differentiableAt_of_isBigO_rpow
    (G.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1)) (lt_add_one _) (realArchimedeanMellin_existsUnique_isBigO_zero G) (by simpa using hs)

private theorem realArchimedeanMellin_existsUnique_ibp (G : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin G s = -(1 / s) * mellin (SchwartzMap.derivCLM ℂ ℂ G) (s + 1) := by
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  let G' := SchwartzMap.derivCLM ℂ ℂ G
  let u : ℝ → ℂ := fun t ↦ (t : ℂ) ^ ((s - 1) + 1) / ((s - 1) + 1)
  have hu_eq (t : ℝ) : u t = (t : ℂ) ^ s / s := by simp [u]
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u ((x : ℂ) ^ (s - 1)) x := fun x hx ↦
    hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) (fun h ↦ hs0 (by linear_combination h))
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (G : ℝ → ℂ) (G' x) x := fun x _ ↦
    (G.differentiableAt).hasDerivAt
  have hs1 : 0 < (s + 1).re := by simp; linarith
  have hG's := realArchimedeanMellin_existsUnique_convergent G' hs1
  have hGs := realArchimedeanMellin_existsUnique_convergent G hs
  have huv' : IntegrableOn (u * (G' : ℝ → ℂ)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hG's.const_mul (1 / s)) (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ (x : ℂ) ^ (s - 1)) * (G : ℝ → ℂ)) (Ioi 0) := hGs
  have h0 : Tendsto (u * (G : ℝ → ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (t : ℂ) ^ s / s * G t) 0 :=
      ((Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).div_const s).mul
        G.continuous.continuousAt
    have := hc.tendsto
    simp only [Complex.ofReal_zero, Complex.zero_cpow hs0, zero_div, zero_mul] at this
    refine tendsto_nhdsWithin_of_tendsto_nhds (this.congr fun t ↦ ?_)
    simp only [Pi.mul_apply, hu_eq]
  have hinf : Tendsto (u * (G : ℝ → ℂ)) atTop (𝓝 0) := by
    have hub : u =O[atTop] (fun t : ℝ ↦ t ^ s.re) := by
      refine Asymptotics.isBigO_iff.mpr ⟨‖s‖⁻¹, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [hu_eq, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos ht _), div_eq_mul_inv, mul_comm]
    have hprod := hub.mul (realArchimedeanMellin_existsUnique_isBigO_atTop G (s.re + 1))
    have hexp : (fun t : ℝ ↦ t ^ s.re * t ^ (-(s.re + 1))) =ᶠ[atTop] fun t ↦ t ^ (-1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [← Real.rpow_add ht]
      ring_nf
    exact (hprod.congr' (EventuallyEq.refl _ _) hexp).trans_tendsto
      (tendsto_rpow_neg_atTop one_pos)
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at key
  unfold mellin
  have hL : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G t) =
      -∫ t in Ioi (0 : ℝ), u t * G' t := by
    rw [key, neg_neg]
    rfl
  rw [hL]
  have hR : (∫ t in Ioi (0 : ℝ), u t * G' t) =
      (1 / s) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1 - 1) • G' t := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    simp only [hu_eq, smul_eq_mul, add_sub_cancel_right]
    ring
  rw [hR]
  ring

private theorem realArchimedeanMellin_existsUnique_succ (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)) (N : ℕ) {s : ℂ} (hs : 0 < (s + N).re) :
    E N s = E (N + 1) s := by
  rw [hE, hE]
  rw [realArchimedeanMellin_existsUnique_ibp _ hs, Function.iterate_succ_apply', Finset.prod_range_succ,
    pow_succ, Nat.cast_succ, ← add_assoc, mul_inv]
  ring

private theorem realArchimedeanMellin_existsUnique_eq (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)) {s : ℂ} {N M : ℕ} (hN : 0 < (s + N).re) (hNM : N ≤ M) :
    E N s = E M s := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    refine ih.trans (realArchimedeanMellin_existsUnique_succ G E hE M ?_)
    have : (N : ℝ) ≤ M := by exact_mod_cast hNM
    simp only [Complex.add_re, Complex.natCast_re] at hN ⊢
    linarith

private theorem realArchimedeanMellin_existsUnique_contEq (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} {N : ℕ} (hN : 0 < (s + N).re) :
    F s = E N s := by
  rw [hF]
  have hn : 0 < (s + ((⌈-s.re⌉₊ + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
    have := Nat.le_ceil (-s.re)
    linarith
  rcases le_total N (⌈-s.re⌉₊ + 1) with h | h
  · exact (realArchimedeanMellin_existsUnique_eq G E hE hN h).symm
  · exact realArchimedeanMellin_existsUnique_eq G E hE hn h

private theorem realArchimedeanMellin_existsUnique_analyticAt (G : SchwartzMap ℝ ℂ) (N : ℕ) {s : ℂ} (hs : 0 < (s + N).re) :
    AnalyticAt ℂ (fun z ↦ mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (z + N)) s := by
  have hU : IsOpen {z : ℂ | 0 < (z + N).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))
  have hd : DifferentiableOn ℂ (fun z ↦ mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (z + N))
      {z : ℂ | 0 < (z + N).re} := fun z hz ↦
    ((realArchimedeanMellin_existsUnique_differentiableAt _ hz).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hs)

private theorem realArchimedeanMellin_existsUnique_meromorphicAt (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) (s : ℂ) :
    MeromorphicAt F s := by
  set N := ⌈-s.re⌉₊ + 1
  have hN : 0 < (s + N).re := by
    simp only [N, Complex.add_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one, Complex.one_re]
    have := Nat.le_ceil (-s.re)
    linarith
  have hU : IsOpen {z : ℂ | 0 < (z + N).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))
  have hP : AnalyticAt ℂ (fun z : ℂ ↦ ∏ j ∈ Finset.range N, (z + j)) s := by fun_prop
  have hE' : MeromorphicAt (E N) s := by
    have h0 := ((MeromorphicAt.const ((-1 : ℂ) ^ N) s).mul hP.meromorphicAt.inv).mul
      (realArchimedeanMellin_existsUnique_analyticAt G N hN).meromorphicAt
    exact h0.congr (Eventually.of_forall fun z ↦ (hE N z).symm)
  refine hE'.congr ?_
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hN)] with z hz
  exact (realArchimedeanMellin_existsUnique_contEq G E hE F hF hz).symm

private theorem realArchimedeanMellin_existsUnique_eqMellin (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} (hs : 0 < s.re) :
    F s = mellin G s := by
  rw [realArchimedeanMellin_existsUnique_contEq G E hE F hF (N := 0) (by simpa using hs), hE]
  simp

private theorem realArchimedeanMellin_existsUnique_contAnalyticAt (G : SchwartzMap ℝ ℂ) (E : ℕ → ℂ → ℂ)
    (hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N))
    (F : ℂ → ℂ) (hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ F s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h := realArchimedeanMellin_existsUnique_analyticAt G 0 (s := s) (by simpa using hs)
  simp only [Function.iterate_zero, id_eq, Nat.cast_zero, add_zero] at h
  refine h.congr ?_
  filter_upwards [hU.mem_nhds hs] with z hz
  exact (realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hz).symm

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem realArchimedeanMellin_existsUnique_eqNF {G H : ℂ → ℂ}
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

private theorem realArchimedeanMellin_existsUnique_schwartz (G : SchwartzMap ℝ ℂ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧ ∀ s : ℂ, 0 < s.re → HasMellin G s (L s) := by
  let E : ℕ → ℂ → ℂ := fun N s ↦ (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
    mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N)
  have hE : ∀ N s, E N s = (-1 : ℂ) ^ N * (∏ j ∈ Finset.range N, (s + j))⁻¹ *
      mellin ((SchwartzMap.derivCLM ℂ ℂ)^[N] G) (s + N) := fun _ _ ↦ rfl
  let F : ℂ → ℂ := fun s ↦ E (⌈-s.re⌉₊ + 1) s
  have hF : ∀ s, F s = E (⌈-s.re⌉₊ + 1) s := fun _ ↦ rfl
  have hm : MeromorphicOn F univ := fun s _ ↦ realArchimedeanMellin_existsUnique_meromorphicAt G E hE F hF s
  refine ⟨toMeromorphicNFOn F univ, ⟨meromorphicNFOn_toMeromorphicNFOn _ _,
    fun s hs ↦ ⟨realArchimedeanMellin_existsUnique_convergent G hs, ?_⟩⟩, ?_⟩
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (realArchimedeanMellin_existsUnique_contAnalyticAt G E hE F hF hs).meromorphicNFAt,
      realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hs]
  · rintro L ⟨hL, hLm⟩
    funext s
    refine realArchimedeanMellin_existsUnique_eqNF hL (meromorphicNFOn_toMeromorphicNFOn _ _) (fun z hz ↦ ?_) s
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ z),
      toMeromorphicNFAt_eq_self.mpr (realArchimedeanMellin_existsUnique_contAnalyticAt G E hE F hF hz).meromorphicNFAt,
      realArchimedeanMellin_existsUnique_eqMellin G E hE F hF hz]
    exact (hLm z hz).2.symm

/-- Paper: Proposition 5.3.3.4, p. 258.
The real Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each sign parity. -/
theorem realArchimedeanMellin_existsUnique (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (realProfile(f, ε)) s (L s) := by
  let G : 𝓢(ℝ, ℂ) := f + ((-1 : ℂ) ^ ε.val) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) f
  have hG : realProfile(f, ε) = ⇑G := by
    funext t
    simp [G]
  rw [hG]
  exact realArchimedeanMellin_existsUnique_schwartz G

/-- Paper: Proposition 5.3.3.4, p. 258.
The real local Mellin transform is the meromorphic continuation of the weighted
integral over the two signs in (5.3.3.26). -/
def realArchimedeanMellin (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) : ℂ → ℂ :=
  (realArchimedeanMellin_existsUnique f ε).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the real Mellin transform. -/
theorem realArchimedeanMellin_eq_integral (f : 𝓢(ℝ, ℂ)) (ε : Fin 2)
    (s : ℂ) (_hs : 0 < s.re) :
    realArchimedeanMellin f ε s = mellin (realProfile(f, ε)) s :=
  ((realArchimedeanMellin_existsUnique f ε).exists.choose_spec.2 s _hs).2.symm

section ComplexArchimedeanMellin

private theorem complexArchimedeanMellin_continuous_eval_iteratedFDeriv (f : 𝓢(ℂ, ℂ)) (j : ℕ) :
    Continuous (fun p : ℝ × ℝ ↦
      iteratedFDeriv ℝ j (f : ℂ → ℂ) ((p.1 : ℂ) * unitAngle(p.2)) (fun _ ↦ unitAngle(p.2))) := by
  have hcont : Continuous (fun p : ℝ × ℝ ↦ iteratedFDeriv ℝ j (f : ℂ → ℂ) ((p.1 : ℂ) * unitAngle(p.2))) :=
    (f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top) |>.comp (by fun_prop)
  have hev : Continuous (fun q : ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℂ) ℂ × (Fin j → ℂ) ↦ q.1 q.2) :=
    continuous_eval
  exact hev.comp (hcont.prodMk (continuous_pi fun _ ↦ by fun_prop))

private theorem complexArchimedeanMellin_iteratedDeriv_integral (f : 𝓢(ℂ, ℂ)) (n : ℤ) (j : ℕ) (r : ℝ) :
    iteratedDeriv j (fun x : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (unitAngle(θ)) ^ n * f ((x : ℂ) * unitAngle(θ))) r =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (unitAngle(θ)) ^ n * iteratedFDeriv ℝ j (f : ℂ → ℂ)
          ((r : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ)) := by
  induction j generalizing r with
  | zero =>
    simp only [iteratedDeriv_zero, iteratedFDeriv_zero_apply]
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hfun : (iteratedDeriv j fun x : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (unitAngle(θ)) ^ n * f ((x : ℂ) * unitAngle(θ))) =
        fun x : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (unitAngle(θ)) ^ n * iteratedFDeriv ℝ j (f : ℂ → ℂ)
            ((x : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ)) := funext ih
    rw [hfun]
    let Φ : ℝ → ℝ → ℂ := fun x θ ↦
      (unitAngle(θ)) ^ n * iteratedFDeriv ℝ j (f : ℂ → ℂ)
        ((x : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ))
    let Φ' : ℝ → ℝ → ℂ := fun x θ ↦
      (unitAngle(θ)) ^ n * iteratedFDeriv ℝ (j + 1) (f : ℂ → ℂ)
        ((x : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ))
    have hzpow : Continuous (fun p : ℝ × ℝ ↦ (unitAngle(p.2)) ^ n) := by
      have heq : (fun p : ℝ × ℝ ↦ (unitAngle(p.2)) ^ n) =
          fun p ↦ Complex.exp ((n : ℂ) * ((p.2 : ℂ) * Complex.I)) :=
        funext fun p ↦ (Complex.exp_int_mul _ n).symm
      rw [heq]
      fun_prop
    have hΦcont : Continuous Φ.uncurry :=
      hzpow.mul (complexArchimedeanMellin_continuous_eval_iteratedFDeriv f j)
    have hΦ'cont : Continuous Φ'.uncurry :=
      hzpow.mul (complexArchimedeanMellin_continuous_eval_iteratedFDeriv f (j + 1))
    have hderiv (θ : ℝ) (x : ℝ) : HasDerivAt (fun y : ℝ ↦ Φ y θ) (Φ' x θ) x := by
      let g : ℝ →L[ℝ] ℂ := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (unitAngle(θ))
      have hg (y : ℝ) : g y = (y : ℂ) * unitAngle(θ) := by simp [g, Complex.real_smul]
      have hd1 : DifferentiableAt ℝ (iteratedFDeriv ℝ j (f : ℂ → ℂ)) (g x) :=
        ((f.smooth ⊤).differentiable_iteratedFDeriv (mod_cast WithTop.coe_lt_top j)) (g x)
      let ev : (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ ℂ) ℂ) →L[ℝ] ℂ :=
        { toFun := fun L ↦ L (fun _ ↦ unitAngle(θ))
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl
          cont := continuous_eval.comp (continuous_id.prodMk continuous_const) }
      have hf' : HasFDerivAt (fun z : ℂ ↦ iteratedFDeriv ℝ j (f : ℂ → ℂ) z (fun _ ↦ unitAngle(θ)))
          (ev.comp (fderiv ℝ (iteratedFDeriv ℝ j (f : ℂ → ℂ)) (g x))) (g x) :=
        ev.hasFDerivAt.comp (g x) hd1.hasFDerivAt
      have hcomp := (hf'.comp x g.hasFDerivAt).hasDerivAt
      have hval : (ev.comp (fderiv ℝ (iteratedFDeriv ℝ j (f : ℂ → ℂ)) (g x))) (g 1) =
          iteratedFDeriv ℝ (j + 1) (f : ℂ → ℂ) (g x) (fun _ ↦ unitAngle(θ)) := by
        have hg1 : g 1 = unitAngle(θ) := by simp [g]
        rw [ContinuousLinearMap.comp_apply, hg1]
        exact (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := (f : ℂ → ℂ)) (x := g x)
          (fun _ : Fin (j + 1) ↦ unitAngle(θ))).symm
      rw [ContinuousLinearMap.comp_apply] at hcomp
      rw [hval, hg x] at hcomp
      dsimp only [Function.comp_def, hg] at hcomp
      simpa only [Φ, Φ', hg, Pi.mul_def, zero_mul, zero_add] using
        (hasDerivAt_const x ((unitAngle(θ)) ^ n)).mul hcomp
    have hfderiv_cont : Continuous (fun p : ℝ × ℝ ↦ fderiv ℝ (fun y ↦ Φ y p.2) p.1) := by
      have heq : (fun p : ℝ × ℝ ↦ fderiv ℝ (fun y ↦ Φ y p.2) p.1) =
          fun p : ℝ × ℝ ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Φ' p.1 p.2) := by
        funext p
        rw [(hderiv p.2 p.1).hasFDerivAt.fderiv]
        ext
        simp
      rw [heq]
      exact (ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)).continuous.comp hΦ'cont
    have hF := intervalIntegral.hasFDerivAt_integral_of_continuousOn_fderiv (𝕜 := ℝ)
      (μ := volume) (f := Φ) (x₀ := r) (u := univ) (a := 0) (b := 2 * Real.pi)
      univ_mem hΦcont.continuousOn (fun θ _ ↦ fun x _ ↦ (hderiv θ x).differentiableAt.differentiableWithinAt)
      hfderiv_cont.continuousOn
    have hD : HasDerivAt (fun x : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi), Φ x θ)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Φ' r θ) r := by
      have hD' := hF.hasDerivAt
      refine hD'.congr_deriv ?_
      change (∫ θ in (0 : ℝ)..(2 * Real.pi), fderiv ℝ (fun y ↦ Φ y θ) r) (1 : ℝ) = _
      have hint : IntervalIntegrable (fun θ ↦ fderiv ℝ (fun y ↦ Φ y θ) r) volume 0 (2 * Real.pi) :=
        (hfderiv_cont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * Real.pi)
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
      have hint' : MeasureTheory.Integrable (fun θ ↦ fderiv ℝ (fun y ↦ Φ y θ) r)
          (volume.restrict (Ioc 0 (2 * Real.pi))) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hint
      change (ContinuousLinearMap.apply ℝ ℂ (1 : ℝ))
          (∫ θ in Ioc 0 (2 * Real.pi), fderiv ℝ (fun y ↦ Φ y θ) r) =
        ∫ θ in Ioc 0 (2 * Real.pi), Φ' r θ
      rw [← (ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).integral_comp_comm hint']
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun θ _ ↦ ?_
      simp [(hderiv θ r).hasFDerivAt.fderiv]
    exact hD.deriv

private theorem exists_angularAverage_schwartz (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    ∃ G : 𝓢(ℝ, ℂ), ∀ r : ℝ, G r = ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (unitAngle(θ)) ^ n * f ((r : ℂ) * unitAngle(θ)) := by
  let A : ℝ → ℂ := fun r ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (unitAngle(θ)) ^ n * f ((r : ℂ) * unitAngle(θ))
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) A := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ (unitAngle(p.2)) ^ n) := by
      have heq : (fun p : ℝ × ℝ ↦ (unitAngle(p.2)) ^ n) =
          fun p ↦ Complex.exp ((n : ℂ) * ((p.2 : ℂ) * Complex.I)) :=
        funext fun p ↦ (Complex.exp_int_mul _ n).symm
      rw [heq]
      exact Complex.contDiff_exp.comp
        (contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ ↦ f ((p.1 : ℂ) * unitAngle(p.2))) :=
      (f.smooth (⊤ : ℕ∞)).comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
        (Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)))
    exact (h1.mul h2).parametric_intervalIntegral
  have hdecay : ∀ k j : ℕ, ∃ C : ℝ, ∀ r : ℝ, ‖r‖ ^ k * ‖iteratedFDeriv ℝ j A r‖ ≤ C := by
    intro k j
    obtain ⟨C, hC⟩ := f.decay' k j
    have hC0 : 0 ≤ C := by
      have h0 := hC 0
      exact le_trans (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)) h0
    refine ⟨2 * Real.pi * C, fun r ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [complexArchimedeanMellin_iteratedDeriv_integral f n j r]
    by_cases hpow : ‖r‖ ^ k = 0
    · rw [hpow, zero_mul]
      positivity
    · have hpos : 0 < ‖r‖ ^ k := lt_of_le_of_ne (pow_nonneg (norm_nonneg _) _) (Ne.symm hpow)
      have hbound : ∀ θ ∈ Set.uIoc (0 : ℝ) (2 * Real.pi),
          ‖(unitAngle(θ)) ^ n * iteratedFDeriv ℝ j (f : ℂ → ℂ)
              ((r : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ))‖ ≤
            C / ‖r‖ ^ k := by
        intro θ _
        have hu : ‖unitAngle(θ)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
        have hun : ‖(unitAngle(θ)) ^ n‖ = 1 := by rw [norm_zpow, hu, one_zpow]
        have harg : ‖(r : ℂ) * unitAngle(θ)‖ = ‖r‖ := by
          rw [norm_mul, hu, mul_one, Complex.norm_real]
        have hnorm : ‖iteratedFDeriv ℝ j (f : ℂ → ℂ)
              ((r : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ))‖ ≤
            ‖iteratedFDeriv ℝ j (f : ℂ → ℂ) ((r : ℂ) * unitAngle(θ))‖ := by
          calc
            _ ≤ ‖iteratedFDeriv ℝ j (f : ℂ → ℂ) ((r : ℂ) * unitAngle(θ))‖ *
                ∏ _i : Fin j, ‖unitAngle(θ)‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
            _ = ‖iteratedFDeriv ℝ j (f : ℂ → ℂ) ((r : ℂ) * unitAngle(θ))‖ := by
              simp [hu]
        have hdec : ‖r‖ ^ k * ‖iteratedFDeriv ℝ j (f : ℂ → ℂ) ((r : ℂ) * unitAngle(θ))‖ ≤ C := by
          rw [← harg]
          exact hC ((r : ℂ) * unitAngle(θ))
        rw [norm_mul, hun, one_mul]
        exact hnorm.trans ((le_div_iff₀ hpos).mpr (by rw [mul_comm]; exact hdec))
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
      rw [sub_zero, abs_of_pos Real.two_pi_pos] at hint
      calc
        ‖r‖ ^ k * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), (unitAngle(θ)) ^ n *
            iteratedFDeriv ℝ j (f : ℂ → ℂ) ((r : ℂ) * unitAngle(θ)) (fun _ ↦ unitAngle(θ))‖
          ≤ ‖r‖ ^ k * (C / ‖r‖ ^ k * (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hint hpos.le
        _ = 2 * Real.pi * C := by
            field_simp [hpow]
  exact ⟨⟨A, hsmooth, hdecay⟩, fun _ ↦ rfl⟩

end ComplexArchimedeanMellin

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each integral angular weight.
Deviation: The angular measure is dθ in the norm coordinate t = |z|², as in §3.3.
The printed 2 dθ would double the Tamagawa integral. -/
theorem complexArchimedeanMellin_existsUnique (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (complexProfile(f, n)) s (L s) := by
  obtain ⟨G, hG⟩ := exists_angularAverage_schwartz f n
  obtain ⟨K, ⟨hK, hKm⟩, _⟩ := realArchimedeanMellin_existsUnique_schwartz G
  let L : ℂ → ℂ := fun s ↦ (2 : ℂ) * K (2 * s)
  have hL : MeromorphicNFOn L univ := by
    intro s _
    have h2 : MeromorphicNFAt (fun z : ℂ ↦ K (2 * z)) s := (hK (mem_univ (2 * s))).comp_analyticAt
      (show AnalyticAt ℂ (fun z : ℂ ↦ 2 * z) s by fun_prop)
    have h3 : MeromorphicNFAt ((2 : ℂ) • fun z : ℂ ↦ K (2 * z)) s := h2.smul_const (s := (2 : ℂ))
    convert h3 using 1
  have hLm : ∀ s : ℂ, 0 < s.re → HasMellin (complexProfile(f, n)) s (L s) := by
    intro s hs
    have h2s : 0 < (2 * s).re := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hs
    have hG2 := hKm (2 * s) h2s
    have heq : EqOn (complexProfile(f, n)) (fun t : ℝ ↦ (G : ℝ → ℂ) (t ^ (1 / 2 : ℝ))) (Ioi 0) := by
      intro t _
      change (∫ θ in (0 : ℝ)..(2 * Real.pi), (unitAngle(θ)) ^ n *
          f ((Real.sqrt t : ℂ) * unitAngle(θ))) = G (t ^ (1 / 2 : ℝ))
      rw [hG, ← Real.sqrt_eq_rpow]
    have hconv : MellinConvergent (fun t : ℝ ↦ (G : ℝ → ℂ) (t ^ (1 / 2 : ℝ))) s := by
      rw [MellinConvergent.comp_rpow (one_div_ne_zero (by norm_num : (2 : ℝ) ≠ 0))]
      convert hG2.1 using 2
      push_cast
      ring
    have hmell : mellin (fun t : ℝ ↦ (G : ℝ → ℂ) (t ^ (1 / 2 : ℝ))) s = L s := by
      rw [mellin_comp_rpow _ s (1 / 2 : ℝ)]
      have hdiv : s / ((1 / 2 : ℝ) : ℂ) = 2 * s := by push_cast; ring
      have habs : |1 / (2 : ℝ)|⁻¹ = (2 : ℝ) := by norm_num
      rw [hdiv, habs, hG2.2, Complex.real_smul]
      simp [L]
    refine ⟨?_, ?_⟩
    · exact hconv.congr_fun (fun t ht ↦ by simp [heq ht]) measurableSet_Ioi
    · refine (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_).trans hmell
      simp [heq ht]
  refine ⟨L, ⟨hL, hLm⟩, ?_⟩
  rintro H ⟨hH, hHm⟩
  funext s
  exact realArchimedeanMellin_existsUnique_eqNF hH hL
    (fun z hz ↦ (hHm z hz).2.symm.trans (hLm z hz).2) s

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex local Mellin transform is the meromorphic continuation of the angular
and radial integral in (5.3.3.26).
Deviation: The angular measure is normalized as in §3.3. -/
def complexArchimedeanMellin (f : 𝓢(ℂ, ℂ)) (n : ℤ) : ℂ → ℂ :=
  (complexArchimedeanMellin_existsUnique f n).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the complex Mellin transform.
Deviation: The angular measure is normalized as in §3.3. -/
theorem complexArchimedeanMellin_eq_integral (f : 𝓢(ℂ, ℂ)) (n : ℤ)
    (s : ℂ) (_hs : 0 < s.re) :
    complexArchimedeanMellin f n s = mellin (complexProfile(f, n)) s :=
  ((complexArchimedeanMellin_existsUnique f n).exists.choose_spec.2 s _hs).2.symm

/-- Multiplicative Tamagawa integration in real coordinates is integration against dx/|x|. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_measure {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (H : ℝ → ℂ) :
    let : MeasurableSpace w.Completion := borel _
    (∫ u : w.Completionˣ, H ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) =
      ∫ t : ℝ, (‖t‖ : ℂ)⁻¹ * H t := by
  let : MeasurableSpace w.Completion := borel _
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (volume : Measure ℝ).map e.symm := by
    exact dite_eq_left hw
  have hj : MeasurableEmbedding (e.symm : ℝ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    rw [hpre, measure_singleton]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : ((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simpa [D, hw.mult_eq_one] using hx
  calc
    _ = ∫ x : K, H (e x) ∂(((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map]
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_one, pow_one, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.real_smul, Complex.ofReal_inv]

/-- Splitting the real local integral into its positive and negative rays gives the Mellin integral. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_integral {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (g : SchwartzMap ℝ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (a : Fin 2)
    (hc : (∀ x : ℝˣ, c (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) = (‖(x : ℝ)‖ : ℂ) ^ z * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.val)) (hz : 0 < z.re) :
    let : MeasurableSpace w.Completion := borel _
    localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ g ((InfinitePlace.Completion.ringEquivRealOfIsReal hw) x)) c =
      mellin (fun x : ℝ ↦ g x + (-1:ℂ)^a.val * g (-x)) z := by
  let : MeasurableSpace w.Completion := borel _
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  let H (t : ℝ) := g t * ((‖t‖:ℂ)^z * (if 0 < t then 1 else (-1:ℂ))^a.val)
  let J (t : ℝ) := (‖t‖ : ℂ)⁻¹ * H t
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_measure]
  change (∫ x : ℝ, J x) = _
  let P (t : ℝ) := (t : ℂ) ^ (z-1)
  have hpos {t : ℝ} (ht : 0<t) : J t = P t * g t ∧ J (-t) = P t * ((-1:ℂ)^a.val * g (-t)) := by
    have hne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    simp only [P, J, H, Real.norm_eq_abs, abs_neg, abs_of_pos ht, ite_eq_left ht, one_pow,
      ite_eq_right (not_lt.mpr (neg_nonpos.mpr ht.le)), Complex.cpow_sub _ _ hne, Complex.cpow_one]
    constructor <;> ring
  have hconv (k : SchwartzMap ℝ ℂ) : MellinConvergent (fun t : ℝ ↦ k t) z := by
    apply mellinConvergent_of_isBigO_rpow (a := z.re+1) (b := 0) (k.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    · have h := (k.isBigO_cocompact_rpow (-(z.re+1))).mono (atTop_le_cocompact (α := ℝ))
      apply h.congr' .rfl
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      simp [Real.norm_eq_abs, abs_of_nonneg ht]
    · linarith
    · simpa using ((k.continuous.continuousAt (x := 0)).isBigO_one ℝ).mono nhdsWithin_le_nhds
    · exact hz
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ) (F := ℂ) g
  have hi₁ : IntegrableOn (fun x ↦ P x * g x) (Ioi (0:ℝ)) := hconv g
  have hi₂ : IntegrableOn (fun x ↦ P x * ((-1:ℂ)^a.val * g (-x))) (Ioi (0:ℝ)) := by
    apply ((hconv k).const_mul ((-1:ℂ)^a.val)).congr
    filter_upwards with x
    change (-1:ℂ)^a.val * (P x * g (-x)) = _
    ring
  have hiPos : IntegrableOn J (Ioi 0) := hi₁.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).1.symm)
  have hiNeg : IntegrableOn (fun t ↦ J (-t)) (Ioi 0) := hi₂.congr (ae_restrict_mem measurableSet_Ioi |>.mono fun t ht ↦ (hpos ht).2.symm)
  have hiLeft : IntegrableOn J (Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    simpa using hiNeg.comp_neg
  have hneg : (∫ x in Iic (0:ℝ), J x) = ∫ x in Ioi (0:ℝ), J (-x) := by
    simpa only [neg_zero] using (integral_comp_neg_Ioi 0 J).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hiLeft hiPos, hneg]
  rw [setIntegral_congr_fun (f := fun t ↦ J (-t)) measurableSet_Ioi (fun t ht ↦ (hpos ht).2),
    setIntegral_congr_fun (f := J) measurableSet_Ioi (fun t ht ↦ (hpos ht).1), add_comm, ← integral_add hi₁ hi₂]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  change (P t * g t + P t * _) = P t * _
  ring

/-- Uniqueness of continuation identifies the Mellin transform with the local zeta function. -/
private theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) :
    ∀ c : QuasiCharacter w.Completionˣ,
      infiniteLocalIdelicZFunction w f c =
        realArchimedeanMellin g (realLocalEulerParameters w hw c).exists.choose.2
          (realLocalEulerParameters w hw c).exists.choose.1 := by
  let Z (c : QuasiCharacter w.Completionˣ) :=
    realArchimedeanMellin g (realLocalEulerParameters w hw c).exists.choose.2
      (realLocalEulerParameters w hw c).exists.choose.1
  have hZ : Z = infiniteLocalIdelicZFunction w f := by
    apply (infiniteLocalIdelicZFunction_existsUnique w f).unique
    · intro χ
      let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
      let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
      let unit : QuasiCharacter w.Completionˣ :=
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
      obtain ⟨p, ht, hp⟩ :=
        (existsUnique_realUnits_character_parameters (unit.comp i)
          (fun _ ↦ Circle.norm_coe _)).exists
      let chart := quasiCharacterNormTwist
        (Units.map nnNormHom.toMonoidHom ^ w.mult) (continuous_infiniteLocalModule w) unit
      have hshape (s : ℂ) (x : ℝˣ) :
          chart s (Units.map e.symm.toMonoidHom x) =
            (‖(x : ℝ)‖ : ℂ) ^ (s + p.1) *
              (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
        have hn : ‖e.symm x.val‖ = ‖x.val‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero e.symm) x.val
        change unit (Units.map e.symm.toMonoidHom x) *
          ((‖e.symm x.val‖ ^ w.mult : ℝ) : ℂ) ^ s = _
        have hx := hp x
        change unit (Units.map e.symm.toMonoidHom x) = _ at hx
        rw [hx, hn, hw.mult_eq_one, pow_one,
          Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
        ring
      have hparam (s : ℂ) :
          (realLocalEulerParameters w hw (chart s)).exists.choose = (s + p.1, p.2) :=
        (realLocalEulerParameters w hw (chart s)).unique
          (realLocalEulerParameters w hw (chart s)).exists.choose_spec (hshape s)
      have he : (Z ∘ chart) = fun s ↦ realArchimedeanMellin g p.2 (s + p.1) := by
        funext s
        dsimp only [Function.comp_def, Z]
        rw [hparam]
      change MeromorphicNFOn (Z ∘ chart) univ ∧ _
      constructor
      · rw [he]
        intro s _
        exact (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
          (f := realArchimedeanMellin g p.2)).mpr
          ((realArchimedeanMellin_existsUnique g p.2).exists.choose_spec.1 (mem_univ _))
      · intro s hs
        change (Z ∘ chart) s = _
        rw [he]
        dsimp only
        have hz : 0 < (s + p.1).re := by simpa [Complex.add_re, ht] using hs
        rw [realArchimedeanMellin_eq_integral g p.2 _ hz]
        have hf : (fun x ↦ f (Multiplicative.ofAdd x)) = fun x ↦ g (e x) :=
          funext fun x ↦ (hg x).symm
        rw [hf]
        exact (realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_integral
          w hw g (chart s) (s + p.1) p.2 (hshape s) hz).symm
    · exact (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec
  intro c
  exact congrFun hZ.symm c

/-- Paper: Proposition 5.3.3.4, p. 258.
In the real field model the local zeta function of §3.3 is the two-sign Mellin transform
at the radial exponent and parity of the given quasi-character. -/
theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (realLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = realArchimedeanMellin g p.2 p.1 := by
  let e : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toAddEquiv.toMultiplicative with
      continuous_toFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
      continuous_invFun := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous }
  obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv e
  let g := E.symm f
  have hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x) := by
    intro x
    have h := hE (E.symm f) (Multiplicative.ofAdd x)
    rw [E.apply_symm_apply] at h
    exact h.symm
  refine ⟨g, hg, ?_⟩
  intro c
  exact realArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare w hw f g hg c

/-- Euclidean coordinates identify Schwartz–Bruhat functions with classical Schwartz functions. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_euclidean
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] {n : ℕ}
    (v : A ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin n))) (g : A → ℂ) :
    g ∈ schwartzBruhatSubmodule A ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ, ∀ x, s (v x).toAdd = g x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let P := ElementaryLieGroup n 0 0 PUnit
  let D := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit
  let : Unique D := uniqueOfSubsingleton 0
  let p : Multiplicative E ≃ₜ* Multiplicative P :=
    { toMulEquiv := (AddEquiv.prodUnique (M := E) (N := D)).symm.toMultiplicative
      continuous_toFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : E ↦ (x, (default : D))))
      continuous_invFun := (continuous_fst : Continuous (Prod.fst : E × D → E)) }
  let e : ElementaryLCAPresentation A :=
    { realDim := n, torusDim := 0, latticeRank := 0, finiteFactor := PUnit, equiv := v.trans p }
  have hA := (lca_elementary_iff (G := A)).mpr ⟨e⟩
  let i : (⊤ : Subgroup A) ≃ₜ* A :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair A := ⟨(⊤, OrderDual.toDual ⊥), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv i.symm hA.1,
    isBruhatGoodSubgroup_bot_iff.mpr hA.2, bot_le⟩
  let q₀ : A →* a.quotient := (QuotientGroup.mk' _).comp i.symm.toMulEquiv.toMonoidHom
  have hq₀ : IsOpenQuotientMap q₀ :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.symm.toHomeomorph.isOpenQuotientMap
  have hinj : Injective q₀ := (MonoidHom.ker_eq_bot_iff q₀).mp (eq_bot_iff.mpr fun x hx ↦ by
    exact (a.quotient_mk_eq_one (i.symm x)).mp hx)
  let q := (MulEquiv.ofBijective q₀ ⟨hinj, hq₀.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hq₀.isQuotientMap.isOpen_preimage)
  let e₀ : ElementaryLCAPresentation a.quotient := { e with equiv := q.symm.trans e.equiv }
  have hreal (s : SchwartzBruhatStage e₀) (x : A) :
      schwartzBruhatStageRealization a e₀ s x = s ((v x).toAdd, 0, 0, PUnit.unit) := by
    have hx : x ∈ a.val.1 := Subgroup.mem_top x
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    change s ((e₀.equiv (q x)).toAdd) = _
    change s ((e.equiv (q.symm (q x))).toAdd) = _
    rw [q.symm_apply_apply]
    rfl
  have hrange : schwartzBruhatSubmodule A = (schwartzBruhatStageRealization a e₀).range := by
    refine le_antisymm (iSup_le fun b ↦ iSup_le fun eb ↦ ?_) ?_
    · rintro _ ⟨sb, rfl⟩
      obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition (show b ≤ a from ⟨le_top, le_top⟩) eb e₀
      exact ⟨j sb, hj sb⟩
    · exact le_iSup_of_le a (le_iSup (fun e ↦ (schwartzBruhatStageRealization a e).range) e₀)
  rw [hrange, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    let f : E → ℂ := fun x ↦ s (x, 0, 0, PUnit.unit)
    have hs' (y : P) : f y.1 = s y :=
      congrArg (fun z : P ↦ s z) (Prod.ext rfl (Subsingleton.elim _ _))
    have hf : (fun y : P ↦ f y.1) ∈ elementarySchwartzSubmodule n 0 0 PUnit :=
      (funext hs').symm ▸ s.property
    obtain ⟨S, hS⟩ := (elementarySchwartzSubmodule_real_iff f).mp hf
    refine ⟨S, fun x ↦ ?_⟩
    exact (congrFun hS (v x).toAdd).trans
      ((hreal s x).symm.trans (congrFun hs x))
  · rintro ⟨s, hs⟩
    let t : SchwartzBruhatStage e₀ :=
      ⟨fun y : P ↦ s y.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨s, rfl⟩⟩
    exact ⟨t, funext fun x ↦ (hreal t x).trans (hs x)⟩

/-- The complex coordinate model of a local Schwartz–Bruhat function is a Schwartz function. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_coordinates
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let v : Multiplicative w.Completion ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℂ))) :=
    { toMulEquiv := (e.toAddEquiv.trans L.toLinearEquiv.toAddEquiv).toMultiplicative
      continuous_toFun := L.continuous.comp j.continuous
      continuous_invFun := j.symm.continuous.comp L.symm.continuous }
  obtain ⟨G, hG⟩ :=
    (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_euclidean v f).mp f.property
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L G,
    fun x ↦ hG (Multiplicative.ofAdd x)⟩

/-- Multiplicative Tamagawa integration in complex coordinates uses twice Lebesgue measure divided by the squared norm. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexLocalIntegral_model {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex) (H : ℂ → ℂ) :
    let : MeasurableSpace w.Completion := borel _
    (∫ u : w.Completionˣ, H ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) u.val) ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) =
      (2:ℂ) * ∫ t : ℂ, ((‖t‖ : ℂ)^2)⁻¹ * H t := by
  let : MeasurableSpace w.Completion := borel _
  classical
  let K := w.Completion
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let μ := infiniteLocalAdditiveTamagawaMeasure F w
  let D (x : K) : ENNReal := (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  let ι : Kˣ → K := Units.val
  have hι : MeasurableEmbedding ι := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hμ : μ = (2 • (volume : Measure ℂ)).map e.symm := by
    exact dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)
  have hj : MeasurableEmbedding (e.symm : ℂ → K) := j.symm.toHomeomorph.measurableEmbedding
  have hμ₀ : μ {0} = 0 := by
    rw [hμ, hj.map_apply]
    have hpre : e.symm ⁻¹' ({0} : Set K) = {0} := by
      ext x
      exact e.symm.map_eq_zero_iff
    simp [hpre]
  have hneμ : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμ₀
  have hν : ∀ᵐ x ∂μ.withDensity D, x ≠ 0 :=
    (withDensity_absolutelyContinuous μ D).ae_le hneμ
  have hmap : ((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι = μ.withDensity D := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure, hι.map_comap, Measure.restrict_eq_self_of_ae_mem]
    exact hν.mono fun x hx ↦ ⟨Units.mk0 x hx, rfl⟩
  have hD : Measurable D := (measurable_coe_nnreal_ennreal.comp ((continuous_nnNorm.pow w.mult).measurable)).inv
  have hfinite : ∀ᵐ x ∂μ, D x < ⊤ := by
    filter_upwards [hneμ] with x hx
    change x ≠ 0 at hx
    simp [D, hw.mult_eq_two]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr (nnNorm_ne_zero_iff.mpr hx)))
  calc
    _ = ∫ x : K, H (e x) ∂(((infiniteLocalMultiplicativeTamagawaMeasure F w)).map ι) := (hι.integral_map (fun x ↦ H (e x))).symm
    _ = ∫ x : K, (D x).toReal • H (e x) ∂μ := by rw [hmap, integral_withDensity_eq_integral_toReal_smul hD hfinite]
    _ = _ := by
      rw [hμ, hj.integral_map, show (2 • (volume : Measure ℂ)) = (2 : ENNReal) • volume by simp [two_smul], integral_smul_measure]
      simp only [ENNReal.toReal_ofNat, Complex.real_smul, Complex.ofReal_ofNat]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      have hn : ‖e.symm t‖ = ‖t‖ := j.symm.isometry.norm_map_of_map_zero (map_zero e.symm) _
      simp only [D, hw.mult_eq_two, ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm,
        e.apply_symm_apply, hn, Complex.ofReal_inv, Complex.ofReal_pow, NNReal.coe_pow]

/-- Integral angular weights have unit norm. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm (r : ℤ) (θ : ℝ) : ‖(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Integral angular weights are smooth. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_smooth (r : ℤ) : ContDiff (ℝ) (∞) ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r) := by
  exact (Complex.contDiff_exp (𝕜 := ℝ)).comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul contDiff_const)

/-- Angular averaging preserves rapid decay on the positive ray. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularProfile_decay {g : ℂ → ℂ} {f : SchwartzMap ℂ ℂ}
    (h : ∀ z, ‖g z‖ ≤ ‖f z‖) (r : ℤ) (p : ℝ) :
    (fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r =O[atTop] (fun x : ℝ ↦ x^p) := by
  obtain ⟨C,hC⟩ := (f.isBigO_cocompact_rpow p).bound
  obtain ⟨R,hR⟩ := (Metric.mem_cocompact_iff_closedBall_compl_subset (0:ℂ)).mp hC
  refine Asymptotics.isBigO_iff.mpr ⟨C * volume.real (Ioo (-Real.pi) Real.pi), ?_⟩
  filter_upwards [eventually_gt_atTop (max R 0)] with t ht
  have ht₀ : 0<t := (le_max_right _ _).trans_lt ht
  have hn (θ : ℝ) : ‖(t:ℂ) * (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ‖ = t := by
    simp [abs_of_pos ht₀]
  have hnorm (θ : ℝ) : ‖(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ * g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖ ≤ C * ‖t^p‖ := by
    rw [norm_mul, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm, one_mul]
    have hx : (t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ ∉ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right, hn]
      exact not_le.mpr ((le_max_left _ _).trans_lt ht)
    have hb : ‖f ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖ ≤ C * ‖‖(t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ‖^p‖ := hR hx
    rw [hn θ] at hb
    exact (h _).trans hb
  exact (norm_setIntegral_le_of_norm_le_const (measure_mono Ioo_subset_Icc_self |>.trans_lt
    (isCompact_Icc.measure_lt_top (μ := volume))) (fun θ _ ↦ hnorm θ)).trans_eq (by ring)

/-- Absolute integrability permits angular integration before the radial Mellin transform. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularMellin_fubini (g : SchwartzMap ℂ ℂ) (r : ℤ) (z : ℂ) (hz : 0 < z.re) :
    (∫ p in Ioi (0 : ℝ) ×ˢ (Ioo (-Real.pi) Real.pi), (p.1:ℂ)^(z-1) * ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r p.2 *
      g ((p.1:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 p.2))) = mellin ((fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r) z := by
  let J := fun p : ℝ × ℝ ↦ (p.1:ℂ)^(z-1) * ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r p.2 * g ((p.1:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 p.2))
  let B (t : ℝ) := ∫ θ in (Ioo (-Real.pi) Real.pi), ‖g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)‖
  let Bc (t : ℝ) : ℂ := B t
  have hω (j : ℤ) := (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_smooth j).continuous
  have hfin : volume (Ioo (-Real.pi) Real.pi) < ⊤ := (measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  have hc : Continuous B := by
    apply continuous_of_dominated (bound := fun _ ↦ SchwartzMap.seminorm ℝ 0 0 g)
    · intro x
      exact (g.continuous.comp (continuous_const.mul (hω 1))).norm.aestronglyMeasurable
    · intro x
      exact .of_forall fun θ ↦ (Real.norm_of_nonneg (norm_nonneg _)).le.trans (g.norm_le_seminorm ℝ _)
    · exact integrableOn_const hfin.ne
    · exact .of_forall fun θ ↦ (g.continuous.comp (Complex.continuous_ofReal.mul continuous_const)).norm
  have he : Bc = (fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) (fun x ↦ (‖g x‖ : ℂ)) 0 := by
    funext t
    simp [Bc, B, integral_complex_ofReal]
  have hbc : Continuous Bc := Complex.continuous_ofReal.comp hc
  have hdec (p : ℝ) : Bc =O[atTop] fun t : ℝ ↦ t^p := by
    rw [he]
    exact complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularProfile_decay (g := fun x ↦ (‖g x‖ : ℂ)) (f := g) (fun x ↦ by simp) 0 p
  have hconv : MellinConvergent Bc z := mellinConvergent_of_isBigO_rpow
    (hbc.continuousOn.locallyIntegrableOn measurableSet_Ioi) (hdec _) (lt_add_one z.re)
    (b := 0) (by simpa using (hbc.continuousAt (x := 0)).isBigO_one ℝ |>.mono nhdsWithin_le_nhds) hz
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let ν := (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)
  have hmeas : Measurable J := by
    exact ((Complex.continuous_ofReal.comp continuous_fst).measurable.pow measurable_const).mul
      (((hω r).comp continuous_snd).mul (g.continuous.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul ((hω 1).comp continuous_snd)))).measurable
  have hInt : Integrable J (μ.prod ν) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · apply Eventually.of_forall
      intro t
      have ht : Continuous (fun θ : ℝ ↦ J (t,θ)) :=
        (continuous_const (y := (t:ℂ)^(z-1))).mul ((hω r).mul (g.continuous.comp
          ((continuous_const (y := (t:ℂ))).mul (hω 1))))
      exact (ht.continuousOn.integrableOn_compact (K := Icc (-Real.pi) Real.pi) isCompact_Icc).mono_set Ioo_subset_Icc_self
    · apply hconv.norm.congr
      filter_upwards with t
      change ‖(t:ℂ)^(z-1) * Bc t‖ = ∫ θ in (Ioo (-Real.pi) Real.pi), ‖J (t,θ)‖
      simp only [J, norm_mul, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularWeight_norm, one_mul, integral_const_mul, Bc, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ B t from integral_nonneg fun _ ↦ norm_nonneg _)]
      rfl
  change (∫ p in Ioi (0:ℝ) ×ˢ (Ioo (-Real.pi) Real.pi), J p) = _
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod J hInt]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact integral_const_mul (μ := ν) ((t:ℂ)^(z-1)) (fun θ ↦ (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ * g ((t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ))

/-- Polar coordinates express the complex local integral as twice a radial Mellin transform. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexIntegral_shape {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (g : SchwartzMap ℂ ℂ) (c : QuasiCharacter w.Completionˣ) (z : ℂ) (r : ℤ)
    (hc : (∀ x : ℂˣ, c (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) = ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ r)) (hz : 0 < z.re) :
    let : MeasurableSpace w.Completion := borel _
    localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w) (fun x ↦ g ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw) x)) c =
      2 * mellin ((fun (g : ℂ → ℂ) (r : ℤ) (t : ℝ) ↦ ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I) * g ((t : ℂ) * Complex.exp (((1 : ℤ) : ℂ) * (θ : ℂ) * Complex.I))) g r) (2*z) := by
  let : MeasurableSpace w.Completion := borel _
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  let H (t : ℂ) := g t * (((‖t‖^2:ℝ):ℂ)^z * (t / (‖t‖:ℂ))^r)
  have he (u : w.Completionˣ) : g (e u.val) * c u = H (e u.val) := by
    let x := Units.map e.toMonoidHom u
    have h := hc x
    rw [show Units.map e.symm.toMonoidHom x = u from Units.ext (e.symm_apply_apply u.val)] at h
    exact congrArg (g (e u.val) * ·) h
  change (∫ u : w.Completionˣ, g (e u.val) * c u ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)) = _
  rw [integral_congr_ae (.of_forall he)]
  rw [complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexLocalIntegral_model, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  congr 1
  rw [← complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_angularMellin_fubini g r (2*z) (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hz)]
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  obtain ⟨t,θ⟩ := p
  have ht : 0<t := hp.1
  have ht' : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hn : ‖Complex.polarCoord.symm (t,θ)‖ = t := (Complex.norm_polarCoord_symm _).trans (abs_of_pos ht)
  have ha : Complex.polarCoord.symm (t,θ) = (t:ℂ)*(fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ := by
    simp [Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  have hpow : (((t:ℂ)^2)^z) = (t:ℂ)^(2*z) := by
    rw [pow_two, Complex.mul_cpow_ofReal_nonneg ht.le ht.le]
    rw [show (2:ℂ)*z = z+z by ring, Complex.cpow_add _ _ ht']
  have hr : ((fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) 1 θ)^r = (fun (r : ℤ) (θ : ℝ) ↦ Complex.exp ((r : ℂ) * (θ : ℂ) * Complex.I)) r θ := by
    simp only [Int.cast_one, one_mul, ← Complex.exp_int_mul]
    congr 1
    ring
  dsimp only [H, Prod.fst, Prod.snd]
  rw [hn, ha, Complex.real_smul, mul_div_cancel_left₀ _ ht', hr, Complex.ofReal_pow, hpow, Complex.cpow_sub _ _ ht', Complex.cpow_one]
  field_simp

/-- Changing the angular interval and substituting the squared radius gives the complex Mellin profile. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change (g : ℂ → ℂ) (n : ℤ) (s : ℂ) :
    mellin (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((Real.sqrt t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) s =
    2 * mellin (fun t : ℝ ↦ ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (2 * s) := by
  let A (t : ℝ) := ∫ θ in Set.Ioo (-Real.pi) Real.pi,
    Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) *
      g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have hp (t : ℝ) : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) = A t := by
    let H (θ : ℝ) := (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
      g ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    have hper : Function.Periodic H (2 * Real.pi) := by
      intro θ
      have he : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
        rw [Complex.ofReal_add, add_mul, Complex.exp_add]
        simp [Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
      simp only [H, he]
    have h := hper.intervalIntegral_add_eq 0 (-Real.pi)
    rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at h
    rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
      integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ _
    dsimp [H, A]
    rw [← Complex.exp_int_mul]
    congr 2
    ring
  have hprofile : (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (Complex.exp ((θ : ℂ) * Complex.I)) ^ n *
        g ((Real.sqrt t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) =
      fun t : ℝ ↦ A (t ^ (1 / 2 : ℝ)) := by
    funext t
    rw [hp, Real.sqrt_eq_rpow]
  rw [hprofile, mellin_comp_rpow]
  norm_num [Complex.real_smul, smul_eq_mul, div_eq_mul_inv]
  congr 1
  ring

/-- Uniqueness of continuation identifies the complex Mellin transform with the local zeta function. -/
private theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) (g : 𝓢(ℂ, ℂ))
    (hg : ∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) :
    ∀ c : QuasiCharacter w.Completionˣ,
      infiniteLocalIdelicZFunction w f c =
        complexArchimedeanMellin g (complexLocalEulerParameters w hw c).exists.choose.2
          (complexLocalEulerParameters w hw c).exists.choose.1 := by
  let Z (c : QuasiCharacter w.Completionˣ) :=
    complexArchimedeanMellin g (complexLocalEulerParameters w hw c).exists.choose.2
      (complexLocalEulerParameters w hw c).exists.choose.1
  have hZ : Z = infiniteLocalIdelicZFunction w f := by
    apply (infiniteLocalIdelicZFunction_existsUnique w f).unique
    · intro χ
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
      let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
      let unit : QuasiCharacter w.Completionˣ :=
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
      obtain ⟨p, ht, hp⟩ :=
        (existsUnique_complexUnits_character_parameters (unit.comp i)
          (fun _ ↦ Circle.norm_coe _)).exists
      let chart := quasiCharacterNormTwist
        (Units.map nnNormHom.toMonoidHom ^ w.mult) (continuous_infiniteLocalModule w) unit
      have hshape (s : ℂ) (x : ℂˣ) :
          chart s (Units.map e.symm.toMonoidHom x) =
            ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (s + p.1) *
              ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
        have hn : ‖e.symm x.val‖ = ‖x.val‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
            (map_zero e.symm) x.val
        change unit (Units.map e.symm.toMonoidHom x) *
          ((‖e.symm x.val‖ ^ w.mult : ℝ) : ℂ) ^ s = _
        have hx := hp x
        change unit (Units.map e.symm.toMonoidHom x) = _ at hx
        rw [hx, hn, hw.mult_eq_two,
          Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr x.ne_zero)))]
        ring
      have hparam (s : ℂ) :
          (complexLocalEulerParameters w hw (chart s)).exists.choose = (s + p.1, p.2) :=
        (complexLocalEulerParameters w hw (chart s)).unique
          (complexLocalEulerParameters w hw (chart s)).exists.choose_spec (hshape s)
      have he : (Z ∘ chart) = fun s ↦ complexArchimedeanMellin g p.2 (s + p.1) := by
        funext s
        dsimp only [Function.comp_def, Z]
        rw [hparam]
      change MeromorphicNFOn (Z ∘ chart) univ ∧ _
      constructor
      · rw [he]
        intro s _
        exact (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
          (f := complexArchimedeanMellin g p.2)).mpr
          ((complexArchimedeanMellin_existsUnique g p.2).exists.choose_spec.1 (mem_univ _))
      · intro s hs
        change (Z ∘ chart) s = _
        rw [he]
        dsimp only
        have hz : 0 < (s + p.1).re := by simpa [Complex.add_re, ht] using hs
        rw [complexArchimedeanMellin_eq_integral g p.2 _ hz, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change]
        have hf : (fun x ↦ f (Multiplicative.ofAdd x)) = fun x ↦ g (e x) :=
          funext fun x ↦ (hg x).symm
        rw [hf]
        simpa only [Int.cast_one, one_mul] using (complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_complexIntegral_shape
          w hw g (chart s) (s + p.1) p.2 (hshape s) hz).symm
    · exact (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec
  intro c
  exact congrFun hZ.symm c

/-- Paper: Proposition 5.3.3.4, p. 258.
In the complex field model the local zeta function of §3.3 is the angular Mellin transform
at the squared-norm exponent and angular weight of the given quasi-character. -/
theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (complexLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = complexArchimedeanMellin g p.2 p.1 := by
  obtain ⟨g, hg⟩ := complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_coordinates w hw f
  exact ⟨g, hg, complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_compare w hw f g hg⟩

local notation "realMonomial(" n ")" => SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n)
local notation "complexMonomial(" p ", " q ")" =>
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q)
local notation "shiftParity(" ε ", " n ")" => Fin.ofNat 2 ((ε).val + n)
local notation "rhoReal(" ε ", " s ")" =>
  ((Complex.I ^ (ε).val) *
    (Complex.Gammaℝ (s + (ε).val) / Complex.Gammaℝ (1 - s + (ε).val)))
local notation "rhoComplex(" n ", " s ")" =>
  ((Complex.I ^ (n).natAbs) *
    (Complex.Gammaℂ (s + ((n).natAbs : ℂ) / 2) / Complex.Gammaℂ (1 - s + ((n).natAbs : ℂ) / 2)))

/-- Translating the argument preserves meromorphic normal form on the whole plane. -/
private theorem archimedeanMellin_meromorphicNFOn_comp_add_const {L : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (d : ℂ) : MeromorphicNFOn (fun s ↦ L (s + d)) univ := fun _ _ ↦
  (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := L)).mpr (hL (mem_univ _))

-- TODO(paper-gap): (5.3.3.28) drops M_{x^n} on the left. Its proof supplies the multiplier.

/-- Paper: Proposition 5.3.3.4(1), p. 258.
Multiplying by xⁿ shifts the real Mellin exponent by n and shifts the sign character by
the parity of n.
Deviation: The multiplier on the left is restored from (5.3.3.32)–(5.3.3.34). -/
theorem realArchimedeanMellin_monomial (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    realArchimedeanMellin (realMonomial(n) f) ε =
      fun s ↦ realArchimedeanMellin f shiftParity(ε, n) (s + n) := by
  have hspec := (realArchimedeanMellin_existsUnique f shiftParity(ε, n)).exists.choose_spec
  have hg : (fun x : ℝ ↦ (x : ℂ) ^ n).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.pow n
  -- On the profiles, the monomial is the Mellin shift by n with the parity moved by n.
  have hprofile : realProfile(realMonomial(n) f, ε) =
      fun t : ℝ ↦ (t : ℂ) ^ (n : ℂ) • realProfile(f, shiftParity(ε, n)) t := by
    funext t
    have hsign : (-1 : ℂ) ^ (shiftParity(ε, n)).val = (-1) ^ ε.val * (-1) ^ n := by
      rw [Fin.val_ofNat, ← neg_one_pow_eq_pow_mod_two, pow_add]
    change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f t +
        (-1 : ℂ) ^ ε.val * SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f (-t) =
      (t : ℂ) ^ (n : ℂ) • (f t + (-1 : ℂ) ^ (shiftParity(ε, n)).val * f (-t))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg, hsign,
      Complex.cpow_natCast, Complex.ofReal_neg, neg_pow]
    simp only [smul_eq_mul]
    ring
  refine (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).unique
    (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 n, fun s hs ↦ ?_⟩
  have hsn : 0 < (s + (n : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have h := hspec.2 (s + n) hsn
  rw [hprofile]
  exact ⟨MellinConvergent.cpow_smul.mpr h.1, (mellin_cpow_smul _ s n).trans h.2⟩

/-- Continue a Fourier–Mellin identity from the fundamental strip, then translate the exponent.
Here `G` is the archimedean gamma factor, `a` its shift and `ε` the Fourier phase. -/
private theorem archimedeanMellin_translate_strip_identity {L D G : ℂ → ℂ}
    (hL : Meromorphic L) (hD : Meromorphic D) (hG : Meromorphic G) (ε a d : ℂ)
    (hstrip : ∀ z : ℂ, z.re ∈ Ioo (0 : ℝ) 1 →
      L z = ε * (G (z + a) / G (1 - z + a)) * D (1 - z)) :
    ∀ᶠ s : ℂ in codiscrete ℂ, L (s + d) =
      ε * (G ((s + d) + a) / G (1 - (s + d) + a)) * D (1 - (s + d)) := by
  have hR : Meromorphic (fun z : ℂ ↦ ε * (G (z + a) / G (1 - z + a)) * D (1 - z)) := fun z ↦
    ((MeromorphicAt.const ε z).mul
      (((hG _).comp_analyticAt (g := fun t : ℂ ↦ t + a) (by fun_prop)).div
        ((hG _).comp_analyticAt (g := fun t : ℂ ↦ 1 - t + a) (by fun_prop)))).mul
      ((hD _).comp_analyticAt (g := fun t : ℂ ↦ 1 - t) (by fun_prop))
  have hmid : ∀ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (by norm_num [mem_preimage, mem_Ioo]))
  have hdiff : Meromorphic (L - fun z ↦ ε * (G (z + a) / G (1 - z + a)) * D (1 - z)) :=
    fun z ↦ (hL z).sub (hR z)
  have hzero := hdiff.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp
    ⟨(1 / 2 : ℂ), meromorphicOrderAt_eq_top_iff.mpr
      (hmid.mono fun z hz ↦ sub_eq_zero.mpr (hstrip z hz))⟩
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro x
  have ht : Tendsto (fun z : ℂ ↦ z + d) (𝓝[≠] x) (𝓝[≠] (x + d)) :=
    ((Homeomorph.addRight d).map_punctured_nhds_eq x).le
  have heq : L =ᶠ[codiscrete ℂ] fun z ↦ ε * (G (z + a) / G (1 - z + a)) * D (1 - z) :=
    hzero.mono fun _ h ↦ sub_eq_zero.mp h
  exact ht.eventually (heq.filter_mono (nhdsNE_le_codiscrete (x + d)))

/-- On the fundamental strip the real Tate factor has the phase and gamma quotient
of (5.3.3.24), for the ordinary Euclidean Fourier transform. -/
private theorem realArchimedeanMellin_fourier_strip {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsReal) (f : 𝓢(ℝ, ℂ)) (a : Fin 2)
    (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    realArchimedeanMellin f a z = rhoReal(a, z) * realArchimedeanMellin (𝓕 f) a (1 - z) := by
  have hdz : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
  rw [realArchimedeanMellin_eq_integral f a z hz.1,
    realArchimedeanMellin_eq_integral (𝓕 f) a (1 - z) hdz]
  exact realLocalTate_mellin_fourier w hw f a z hz

/-- Paper: Proposition 5.3.3.4(1), p. 258.
The real monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and parity. The product is understood as a meromorphic identity. -/
theorem realArchimedeanMellin_monomial_functionalEquation (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let a := shiftParity(ε, n)
      let t := s + (n : ℂ)
      realArchimedeanMellin (realMonomial(n) f) ε s =
        rhoReal(a, t) * realArchimedeanMellin (𝓕 f) a (1 - t) := by
  let a := shiftParity(ε, n)
  have hM (g : 𝓢(ℝ, ℂ)) : Meromorphic (realArchimedeanMellin g a) :=
    meromorphicOn_univ.mp (realArchimedeanMellin_existsUnique g a).exists.choose_spec.1.meromorphicOn
  have hG : Meromorphic Complex.Gammaℝ := fun z ↦
    (MeromorphicAt.inv_iff (f := Complex.Gammaℝ)).mp
      (Complex.differentiable_Gammaℝ_inv.analyticAt z).meromorphicAt
  rw [realArchimedeanMellin_monomial]
  exact archimedeanMellin_translate_strip_identity (hM f) (hM (𝓕 f)) hG
    (Complex.I ^ a.val) a.val n
    (realArchimedeanMellin_fourier_strip Rat.infinitePlace Rat.isReal_infinitePlace f a)

/-- Paper: Proposition 5.3.3.4(2), p. 258.
Multiplying by zᵖ times the qth power of its conjugate shifts the Mellin exponent
by (p+q)/2 and the angular weight by p−q. -/
theorem complexArchimedeanMellin_monomial (p q : ℕ) (n : ℤ) (f : 𝓢(ℂ, ℂ)) :
    complexArchimedeanMellin (complexMonomial(p, q) f) n =
      fun s ↦ complexArchimedeanMellin f (n + (p : ℤ) - q) (s + ((p : ℂ) + q) / 2) := by
  have hspec := (complexArchimedeanMellin_existsUnique f (n + (p : ℤ) - q)).exists.choose_spec
  have hg : (fun z : ℂ ↦ z ^ p * star z ^ q).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.id'.pow p).mul (Complex.conjCLE.hasTemperateGrowth.pow q)
  have hE (θ : ℝ) : unitAngle(θ) ≠ 0 := Complex.exp_ne_zero _
  have hstar (θ : ℝ) : star (unitAngle(θ)) = (unitAngle(θ))⁻¹ := by
    rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  -- For positive t the monomial contributes the radial power t^((p+q)/2) and the angular
  -- weight p - q.
  have hprofile : EqOn (complexProfile(complexMonomial(p, q) f, n))
      (fun t : ℝ ↦ (t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)
      (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hroot : (Real.sqrt t : ℂ) ^ (p + q) = (t : ℂ) ^ (((p : ℂ) + q) / 2) := by
      have hr : Real.sqrt t ^ (p + q) = t ^ (((p : ℝ) + q) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1
        push_cast
        ring
      rw [← Complex.ofReal_pow, hr, Complex.ofReal_cpow ht0.le]
      congr 1
      push_cast
      ring
    change (∫ θ in (0 : ℝ)..(2 * Real.pi), unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ))) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
        unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    have hz : star ((Real.sqrt t : ℂ) * unitAngle(θ)) = (Real.sqrt t : ℂ) * (unitAngle(θ))⁻¹ := by
      rw [star_mul', hstar]
      congr 1
      exact Complex.conj_ofReal _
    change unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ)) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) *
        (unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ)))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hz, ← hroot, mul_pow, mul_pow,
      pow_add, zpow_sub₀ (hE θ), zpow_add₀ (hE θ), zpow_natCast, zpow_natCast, inv_pow]
    ring
  refine (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).unique
    (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 _, fun s hs ↦ ?_⟩
  have hsa : 0 < (s + ((p : ℂ) + q) / 2).re := by
    have hre : (((p : ℂ) + q) / 2).re = ((p : ℝ) + q) / 2 := by
      rw [show ((p : ℂ) + q) / 2 = ((((p : ℝ) + q) / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [Complex.add_re, hre]
    positivity
  have h := hspec.2 _ hsa
  have hmul : EqOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • complexProfile(complexMonomial(p, q) f, n) t)
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        ((t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)) (Ioi 0) :=
    fun t ht ↦ congrArg (fun w : ℂ ↦ (t : ℂ) ^ (s - 1) • w) (hprofile ht)
  exact ⟨IntegrableOn.congr_fun (MellinConvergent.cpow_smul.mpr h.1) hmul.symm measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi hmul).trans
      ((mellin_cpow_smul _ s (((p : ℂ) + q) / 2)).trans h.2)⟩

-- TODO(paper-gap): The complex phase in (5.3.3.25) disagrees with the trace-pairing Fourier
-- transform for nontrivial angular weights. Use the phase from §3.3, per ERRATA I91.

/-- The local Tate equation on the fundamental strip uses the trace-pairing Fourier transform
and reverses the angular weight. -/
private theorem complexArchimedeanMellin_fourier_strip {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (f fHat : 𝓢(ℂ, ℂ))
    (hfHat : ∀ x : ℂ, fHat x = 2 * (𝓕 f) (2 * star x)) (k : ℤ)
    (z : ℂ) (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    complexArchimedeanMellin f k z = rhoComplex(k, z) * complexArchimedeanMellin fHat (-k) (1 - z) := by
  have hdz : 0 < (1 - z).re := by simpa using sub_pos.mpr hz.2
  rw [complexArchimedeanMellin_eq_integral f k z hz.1,
    complexArchimedeanMellin_eq_integral fHat (-k) (1 - z) hdz,
    complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change (f : ℂ → ℂ) k z,
    complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction_change (fHat : ℂ → ℂ) (-k) (1 - z)]
  exact complexLocalTate_mellin_fourier w hw f fHat hfHat k z hz

/-- Paper: Proposition 5.3.3.4(2), p. 258.
The complex monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and angular weight. The trace-pairing transform is the Euclidean Fourier
transform evaluated at twice the conjugate argument and multiplied by the self-dual mass factor.
Deviation: The phase is i to the absolute angular weight, as in ERRATA I91. -/
theorem complexArchimedeanMellin_monomial_functionalEquation (p q : ℕ) (n : ℤ)
    (f : 𝓢(ℂ, ℂ)) :
    ∃ fHat : 𝓢(ℂ, ℂ), (∀ z : ℂ, fHat z = 2 * (𝓕 f) (2 * star z)) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ,
        let k := n + (p : ℤ) - q
        let t := s + ((p : ℂ) + q) / 2
        complexArchimedeanMellin (complexMonomial(p, q) f) n s =
          rhoComplex(k, t) * complexArchimedeanMellin fHat (-k) (1 - t) := by
  let k := n + (p : ℤ) - q
  let D : ℂ ≃L[ℝ] ℂ :=
    Complex.conjCLE.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℂ) two_ne_zero))
  let fHat : 𝓢(ℂ, ℂ) := (2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D (𝓕 f)
  have hfHat (x : ℂ) : fHat x = 2 * (𝓕 f) (2 * star x) := rfl
  refine ⟨fHat, hfHat, ?_⟩
  have hM (g : 𝓢(ℂ, ℂ)) (j : ℤ) : Meromorphic (complexArchimedeanMellin g j) :=
    meromorphicOn_univ.mp (complexArchimedeanMellin_existsUnique g j).exists.choose_spec.1.meromorphicOn
  have hG : Meromorphic Complex.Gammaℂ := fun z ↦
    (MeromorphicAt.inv_iff (f := Complex.Gammaℂ)).mp
      (Complex.differentiable_Gammaℂ_inv.analyticAt z).meromorphicAt
  -- A complex place of ℚ(i) realizes the complex local Tate equation.
  let K := CyclotomicField 4 ℚ
  let w : InfinitePlace K := Classical.choice inferInstance
  have : @IsCyclotomicExtension {4} ℚ K _ _ DivisionRing.toRatAlgebra := by
    rw [Subsingleton.elim (DivisionRing.toRatAlgebra : Algebra ℚ K) (CyclotomicField.algebra 4 ℚ)]
    exact CyclotomicField.isCyclotomicExtension 4 ℚ
  have hw : w.IsComplex := (IsCyclotomicExtension.Rat.isTotallyComplex K (n := 4) (by decide)).isComplex w
  rw [complexArchimedeanMellin_monomial]
  exact archimedeanMellin_translate_strip_identity (hM f k) (hM fHat (-k)) hG
    (Complex.I ^ k.natAbs) (k.natAbs / 2) (((p : ℂ) + q) / 2)
    (complexArchimedeanMellin_fourier_strip w hw f fHat hfHat k)

end ArchimedeanMellin

section SAdele

open Classical

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => ℬ(Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp (χ))
local notation "χ₁(" χ ")" =>
  ((χ : Jₛ →ₜ* Circle).comp
    (⟨((mₛ).ker).subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ) : PontryaginDual J₁)
local notation "thetaAt(" χ ")" => sLocalHomogeneousAdelicThetaLinearMap F S (χ)
local notation "A∞" => InfiniteAdeleRing F
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "RealModels" => ((w : RealPlaces) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : ComplexPlaces) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "assemble(" r ", " c ", " x ")" =>
  (show A∞ from fun w ↦ if h : w.IsReal then ((r ⟨w, h⟩).val.symm) ((x).1 ⟨w, h⟩)
    else ((c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩).val.symm)
      ((x).2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩))

-- TODO(paper-gap): In (5.3.4.1), (5.3.4.7) and (5.3.4.15), the finite
-- zero-extension factors must be compactly supported locally constant tests on the
-- units. Remark 2.1.2.1 distinguishes these from the full multiplicative Schwartz
-- space. On Q_p, the sequence p^(-k) on shells of valuation k ≥ 0 is Schwartz on Z,
-- but its zero extension is not locally constant at zero.

/-- Paper: Definition 5.3.4.1, p. 259.
A function on the unit group has an additive Schwartz extension vanishing at zero
exactly when it is locally constant and compactly supported there.
Deviation: The finite punctured test space in (5.3.4.1) is interpreted as
compactly supported locally constant tests, consistently with Remark 2.1.2.1. -/
theorem exists_finitePlaceSchwartz_zeroExtension_iff (v : V) (h : (v.adicCompletion F)ˣ → ℂ) :
    (∃ f : ℬ(v.adicCompletion F), f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) = h u) ↔
      IsLocallyConstant h ∧ HasCompactSupport h := by
  classical
  let K := v.adicCompletion F
  let j : Kˣ → K := Units.val
  have hj : IsOpenEmbedding j := Units.isOpenEmbedding_val
  have hn : (0 : K) ∉ Set.range j := by
    rintro ⟨u, hu⟩
    exact u.ne_zero hu
  constructor
  · rintro ⟨f, hzero, hh⟩
    let g : K → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
    have hg := (mem_finitePlaceSchwartz_iff F v g).mp ⟨f, fun _ ↦ rfl⟩
    have he : h = g ∘ j := funext fun u ↦ (hh u).symm
    refine ⟨he.symm ▸ hg.1.comp_continuous hj.continuous, ?_⟩
    have hc : IsCompact (Function.support g) := by
      have hs : IsClosed (Function.support g) := (hg.1.isOpen_fiber 0).isClosed_compl
      simpa only [tsupport, hs.closure_eq] using (show IsCompact (tsupport g) from hg.2)
    have hr : Function.support g ⊆ Set.range j := by
      intro x hx
      have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ hzero)
      exact ⟨Units.mk0 x hx0, rfl⟩
    apply HasCompactSupport.of_support_subset_isCompact
      ((hj.isEmbedding.isInducing.isCompact_preimage_iff hr).2 hc)
    intro u hu
    exact fun hz ↦ hu ((hh u).symm.trans hz)
  · rintro ⟨hl, hc⟩
    let g : K → ℂ := Function.extend j h (fun _ ↦ 0)
    have he (u : Kˣ) : g (j u) = h u := hj.injective.extend_apply _ _ _
    have hz {x : K} (hx : x ∉ Set.range j) : g x = 0 :=
      Function.extend_apply' _ _ _ hx
    have hk : IsCompact (j '' tsupport h) := hc.image hj.continuous
    have hs : Function.support g ⊆ j '' tsupport h := by
      intro x hx
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        exact ⟨u, subset_tsupport h (fun hu ↦ hx ((he u).trans hu)), rfl⟩
      · exact False.elim (hx (hz hr))
    have hl' : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        refine ⟨j '' {w | h w = h u}, hj.isOpenMap _ (hl.isOpen_fiber _), ⟨u, rfl, rfl⟩, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        exact (he w).trans (hw.trans (he u).symm)
      · refine ⟨(j '' tsupport h)ᶜ, hk.isClosed.isOpen_compl, ?_, ?_⟩
        · rintro ⟨u, _, hu⟩
          exact hr ⟨u, hu⟩
        · intro y hy
          exact (not_not.mp (fun hy' ↦ hy (hs hy'))).trans (hz hr).symm
    obtain ⟨f, hf⟩ :=
      (mem_finitePlaceSchwartz_iff F v g).mpr ⟨hl', HasCompactSupport.of_support_subset_isCompact hk hs⟩
    exact ⟨f, (hf 0).trans (hz hn), fun u ↦ (hf (j u)).trans (he u)⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The finite-place conditions are the kernels of evaluation at adeles with a zero
coordinate at one of the selected finite places. -/
def sAdeleFiniteZeroSchwartz (S T : Finset V) : Submodule ℂ ℬ(SAdeleRing F S) :=
  ⨅ x : {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0},
    LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
      (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
Passing from a Schwartz function in archimedean coordinates to its underlying
function is complex-linear. -/
theorem archimedeanSchwartz_coe_isLinear :
    IsLinearMap ℂ (fun f : 𝓢(ArchCoordinates, ℂ) ↦ (f : ArchCoordinates → ℂ)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The polar-free subspace imposes flatness on every archimedean slice and vanishing
at a zero coordinate at every finite place.
Deviation: The finite punctured factors in (5.3.4.1) are compactly supported tests on
the units. The subspace has the topology inherited from the S-adelic Schwartz space
of Proposition 2.1.4.1, which uses the inductive archimedean–finite tensor topology.
The span identity below is algebraic. The projective topology in print is generally coarser. -/
def sAdelePolarFree (S : Finset V) (r : RealModels) (c : ComplexModels) :
    Submodule ℂ ℬ(SAdeleRing F S) :=
  sAdeleFiniteZeroSchwartz S S ⊓
    ⨅ y : (v : S) → v.val.adicCompletion F,
      let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
        ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
      let slice := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦
        Multiplicative.ofAdd (assemble(r, c, x), y))
      flat.comap (slice.comp (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
For a pure tensor with nonzero factors, finite-coordinate vanishing is exactly
vanishing at zero of each factor selected by T. -/
theorem sAdeleFiniteZeroSchwartz_tmul_iff (T : Finset V)
    (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) (_hf : f ≠ 0)
    (_hg : ∀ v, g v ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) ∈ sAdeleFiniteZeroSchwartz S T ↔
      ∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0 := by
  classical
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let u := e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))
  let X := {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}
  have mem : u ∈ sAdeleFiniteZeroSchwartz S T ↔ ∀ x : X, u (Multiplicative.ofAdd x.val) = 0 :=
    Submodule.mem_iInf _
  have he (x : SAdeleRing F S) : u (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x.1) * ∏ v : S, g v (Multiplicative.ofAdd (x.2 v)) :=
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f g x
  change u ∈ sAdeleFiniteZeroSchwartz S T ↔ _
  rw [mem]
  constructor
  · intro hu v hv
    by_contra hne
    obtain ⟨a, ha⟩ : ∃ a : A∞, f (Multiplicative.ofAdd a) ≠ 0 := by
      by_contra! hn
      exact _hf (Subtype.ext (funext fun x ↦ hn x.toAdd))
    have hnon (w : S) : ∃ y : w.val.adicCompletion F, g w (Multiplicative.ofAdd y) ≠ 0 := by
      by_contra! hn
      exact _hg w (Subtype.ext (funext fun x ↦ hn x.toAdd))
    choose y hy using hnon
    let b := Function.update y v 0
    have hz := hu ⟨(a, b), v, hv, Function.update_self ..⟩
    rw [he] at hz
    apply (mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr ?_)) hz
    intro w _
    by_cases hw : w = v
    · subst w
      simpa [b] using hne
    · simpa [b, Function.update_of_ne hw] using hy w
  · intro h x
    obtain ⟨v, hv, hx⟩ := x.property
    rw [he, Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hx, h v hv]), mul_zero]

/-- A submodule containing every pure tensor of an inductive tensor product with a tensor
power contains the whole space. -/
private theorem sAdeleFiniteZeroSchwartz_eq_span_tmul_top {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} {D : ι → Type*}
    [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B) (s : Submodule ℂ B)
    (h : ∀ (a : A) (g : ∀ i, D i), e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)) ∈ s) (x : B) : x ∈ s := by
  obtain ⟨t, rfl⟩ := e.surjective x
  let W := FinestLocallyConvex (⨂[ℂ] i, D i)
  let M : A ⊗[ℂ] W →ₗ[ℂ] B := (e.toLinearMap : InductiveTensor A W →ₗ[ℂ] B)
  change M t ∈ s
  refine TensorProduct.induction_on (motive := fun t : A ⊗[ℂ] W ↦ M t ∈ s) t
    (by rw [map_zero]; exact s.zero_mem) (fun a z ↦ ?_) fun t₁ t₂ h₁ h₂ ↦ by
      rw [map_add]; exact s.add_mem h₁ h₂
  refine PiTensorProduct.induction_on (motive := fun z : ⨂[ℂ] i, D i ↦
    M (a ⊗ₜ[ℂ] (z : W)) ∈ s) z ?_ ?_
  · intro r g
    have ht : (a ⊗ₜ[ℂ] (((r • (⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
        r • (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) :=
      (TensorProduct.mk ℂ A W a).map_smul r (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)
    have hp : M (a ⊗ₜ[ℂ] (((⨂ₜ[ℂ] i, g i) : ⨂[ℂ] i, D i) : W)) ∈ s := h a g
    exact (congrArg (· ∈ s) ((congrArg M ht).trans (map_smul M r _))).mpr (s.smul_mem r hp)
  · intro z₁ z₂ h₁ h₂
    have ht : (a ⊗ₜ[ℂ] (((z₁ + z₂ : ⨂[ℂ] i, D i)) : W) : A ⊗[ℂ] W) =
        a ⊗ₜ[ℂ] (z₁ : W) + a ⊗ₜ[ℂ] (z₂ : W) :=
      (TensorProduct.mk ℂ A W a).map_add (z₁ : W) (z₂ : W)
    exact (congrArg (· ∈ s) ((congrArg M ht).trans (map_add M _ _))).mpr (s.add_mem h₁ h₂)

/-- Applying a linear map in one factor of a tensor power, conjugated by the identification,
acts on pure tensors by updating that factor. -/
private theorem sAdeleFiniteZeroSchwartz_eq_span_tmul_conj {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] {ι : Type*} [DecidableEq ι]
    {D : ι → Type*} [∀ i, AddCommGroup (D i)] [∀ i, Module ℂ (D i)]
    (e : InductiveTensor A (FinestLocallyConvex (⨂[ℂ] i, D i)) ≃L[ℂ] B) (w : ι)
    (L : D w →ₗ[ℂ] D w) (a : A) (g : ∀ i, D i) :
    let W := FinestLocallyConvex (⨂[ℂ] i, D i)
    let P : W →ₗ[ℂ] W := PiTensorProduct.map (R := ℂ)
      (Function.update (fun i ↦ (LinearMap.id : D i →ₗ[ℂ] D i)) w L)
    let I : A →ₗ[ℂ] A := LinearMap.id
    (e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap))
        (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) =
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, Function.update g w (L (g w)) i)) := by
  intro W P I
  change e (TensorProduct.map I P (e.symm (e _))) = e _
  erw [e.symm_apply_apply, TensorProduct.map_tmul]
  apply congrArg e
  apply congrArg (TensorProduct.tmul ℂ a)
  refine (PiTensorProduct.map_tprod _ g).trans (congrArg (PiTensorProduct.tprod ℂ) (funext fun i ↦ ?_))
  by_cases hi : i = w
  · subst hi
    simp
  · simp [Function.update_of_ne hi]

/-- At a selected place, subtracting the value at zero times the integer indicator gives a
linear map that fixes every test vanishing where that coordinate is zero, and on a pure
tensor replaces the factor by one vanishing at zero. -/
private theorem sAdeleFiniteZeroSchwartz_eq_span_tmul_step (w : S) :
    ∃ Q : ℬₛ →ₗ[ℂ] ℬₛ,
      (∀ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        ∃ g' : ∀ v : S, ℬ(v.val.adicCompletion F),
          g' w (Multiplicative.ofAdd 0) = 0 ∧ (∀ v, v ≠ w → g' v = g v) ∧
          Q ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) =
            (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g' v))) ∧
      ∀ h : ℬₛ, (∀ x : Aₛ, x.2 w = 0 → h (Multiplicative.ofAdd x) = 0) → Q h = h := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let K := w.val.adicCompletion F
  let φ : ℬ(K) := finiteStandardGaussian w.val 1
  have hφ : φ (Multiplicative.ofAdd 0) = 1 := by
    change finiteStandardGaussianValue w.val 1 0 = 1
    unfold finiteStandardGaussianValue
    rw [if_pos (by intro u _; rfl)]
    exact Set.indicator_of_mem (w.val.adicCompletionIntegers F).zero_mem _
  let ev : ℬ(K) →ₗ[ℂ] ℂ :=
    { toFun := fun g ↦ g (Multiplicative.ofAdd 0)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let L : ℬ(K) →ₗ[ℂ] ℬ(K) := LinearMap.id - LinearMap.smulRight ev φ
  have hL (g : ℬ(K)) : L g = g - g (Multiplicative.ofAdd 0) • φ := rfl
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))
  let P : W →ₗ[ℂ] W := PiTensorProduct.map (R := ℂ)
    (Function.update (fun v : S ↦ (LinearMap.id : ℬ(v.val.adicCompletion F) →ₗ[ℂ] _)) w L)
  let I : ℬ(A∞) →ₗ[ℂ] ℬ(A∞) := LinearMap.id
  let Q : ℬₛ →ₗ[ℂ] ℬₛ := e.toLinearMap.comp ((TensorProduct.map I P).comp e.symm.toLinearMap)
  have hQ' (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      Q (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) =
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, Function.update g w (L (g w)) v)) := by
    with_reducible exact sAdeleFiniteZeroSchwartz_eq_span_tmul_conj e w L f g
  refine ⟨Q, fun f g ↦ ⟨Function.update g w (L (g w)), ?_, fun v hv ↦ ?_, hQ' f g⟩, ?_⟩
  · rw [Function.update_self, hL]
    change g w (Multiplicative.ofAdd 0) - g w (Multiplicative.ofAdd 0) * φ (Multiplicative.ofAdd 0) = 0
    rw [hφ, mul_one, sub_self]
  · exact Function.update_of_ne hv _ _
  · intro h hh
    apply Subtype.ext
    funext y
    let x : Aₛ := y.toAdd
    let x₀ : Aₛ := (x.1, Function.update x.2 w 0)
    let Λ₁ : ℬₛ →ₗ[ℂ] ℂ :=
      { toFun := fun k ↦ Q k (Multiplicative.ofAdd x)
        map_add' := fun k₁ k₂ ↦ by rw [map_add]; rfl
        map_smul' := fun r k ↦ by rw [map_smul]; rfl }
    let Λ₂ : ℬₛ →ₗ[ℂ] ℂ :=
      { toFun := fun k ↦ k (Multiplicative.ofAdd x) -
          k (Multiplicative.ofAdd x₀) * φ (Multiplicative.ofAdd (x.2 w))
        map_add' := fun k₁ k₂ ↦ by
          change (k₁ + k₂) _ - (k₁ + k₂) _ * _ = (k₁ _ - k₁ _ * _) + (k₂ _ - k₂ _ * _)
          change (k₁ _ + k₂ _) - (k₁ _ + k₂ _) * _ = _
          ring
        map_smul' := fun r k ↦ by
          change (r • k) _ - (r • k) _ * _ = r • (k _ - k _ * _)
          change r * k _ - r * k _ * _ = r * (k _ - k _ * _)
          ring }
    have hpure (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
        (Λ₁ - Λ₂) (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) = 0 := by
      rw [LinearMap.sub_apply, sub_eq_zero]
      have h1 : ∏ v : S, Function.update g w (L (g w)) v (Multiplicative.ofAdd (x.2 v)) =
          L (g w) (Multiplicative.ofAdd (x.2 w)) *
            ∏ v ∈ Finset.univ.erase w, g v (Multiplicative.ofAdd (x.2 v)) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w), Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun v hv ↦ by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
      have h2 : ∏ v : S, g v (Multiplicative.ofAdd (x.2 v)) =
          g w (Multiplicative.ofAdd (x.2 w)) *
            ∏ v ∈ Finset.univ.erase w, g v (Multiplicative.ofAdd (x.2 v)) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ w)).symm
      have h3 : ∏ v : S, g v (Multiplicative.ofAdd (x₀.2 v)) =
          g w (Multiplicative.ofAdd 0) *
            ∏ v ∈ Finset.univ.erase w, g v (Multiplicative.ofAdd (x.2 v)) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
        congr 1
        · exact congrArg (fun z ↦ g w (Multiplicative.ofAdd z)) (Function.update_self ..)
        · exact Finset.prod_congr rfl fun v hv ↦ congrArg (fun z ↦ g v (Multiplicative.ofAdd z))
            (Function.update_of_ne (Finset.ne_of_mem_erase hv) _ _)
      have hLw : L (g w) (Multiplicative.ofAdd (x.2 w)) = g w (Multiplicative.ofAdd (x.2 w)) -
          g w (Multiplicative.ofAdd 0) * φ (Multiplicative.ofAdd (x.2 w)) := rfl
      have hval : f (Multiplicative.ofAdd x.1) *
            ∏ v : S, Function.update g w (L (g w)) v (Multiplicative.ofAdd (x.2 v)) =
          f (Multiplicative.ofAdd x.1) * ∏ v : S, g v (Multiplicative.ofAdd (x.2 v)) -
            (f (Multiplicative.ofAdd x₀.1) * ∏ v : S, g v (Multiplicative.ofAdd (x₀.2 v))) *
              φ (Multiplicative.ofAdd (x.2 w)) := by
        rw [h1, h2, h3, hLw]
        ring
      exact (congrArg (fun k : ℬₛ ↦ k (Multiplicative.ofAdd x)) (hQ' f g)).trans
        ((he f _ x).trans (hval.trans (congrArg₂ (fun a b ↦ a - b * φ (Multiplicative.ofAdd (x.2 w)))
          (he f g x).symm (he f g x₀).symm)))
    have hall := sAdeleFiniteZeroSchwartz_eq_span_tmul_top
      (D := fun v : S ↦ ℬ(v.val.adicCompletion F)) e (LinearMap.ker (Λ₁ - Λ₂))
      (fun a g ↦ LinearMap.mem_ker.mpr (by with_reducible exact hpure a g)) h
    have hx := sub_eq_zero.mp (LinearMap.mem_ker.mp hall)
    change Q h (Multiplicative.ofAdd x) = h (Multiplicative.ofAdd x)
    refine hx.trans ?_
    change h _ - h (Multiplicative.ofAdd x₀) * _ = _
    rw [hh x₀ (Function.update_self ..), zero_mul, sub_zero]

/-- Every test with finite-coordinate vanishing at the places of `T` lies in the span of the
pure tensors whose factors vanish at zero at the places of any `T' ⊆ T`. -/
private theorem sAdeleFiniteZeroSchwartz_eq_span_tmul_ind (T T' : Finset V) (hT' : T' ⊆ T)
    (h : ℬₛ) (hh : h ∈ sAdeleFiniteZeroSchwartz S T) :
    h ∈ Submodule.span ℂ {k : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v : S, v.val ∈ T' → g v (Multiplicative.ofAdd 0) = 0) ∧
        (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = k} := by
  induction T' using Finset.induction_on with
  | empty =>
    have hgen (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
        (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) ∈
          Submodule.span ℂ {k : ℬₛ |
            ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
              (∀ v : S, v.val ∈ (∅ : Finset V) → g v (Multiplicative.ofAdd 0) = 0) ∧
              (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = k} :=
      Submodule.subset_span ⟨f, g, fun v hv ↦ absurd hv (Finset.notMem_empty _), rfl⟩
    exact sAdeleFiniteZeroSchwartz_eq_span_tmul_top
      (D := fun v : S ↦ ℬ(v.val.adicCompletion F)) _ _ (by with_reducible exact hgen) h
  | insert w T' hw ih =>
    have hprev := ih ((Finset.subset_insert w T').trans hT')
    by_cases hwS : w ∈ S
    · let w' : S := ⟨w, hwS⟩
      have hstep := sAdeleFiniteZeroSchwartz_eq_span_tmul_step (F := F) w'
      let Q := hstep.choose
      have hQpure := hstep.choose_spec.1
      have hfix : Q h = h := hstep.choose_spec.2 h fun x hx ↦
        (Submodule.mem_iInf _).mp hh ⟨x, w', hT' (Finset.mem_insert_self w T'), hx⟩
      refine (congrArg (· ∈ _) hfix).mp ?_
      refine Submodule.mem_comap.mp (Submodule.span_le.mpr ?_ hprev)
      rintro _ ⟨f, g, hg, rfl⟩
      have hg' := hQpure f g
      let g' := hg'.choose
      have hg'w := hg'.choose_spec.1
      have hg'v := hg'.choose_spec.2.1
      have hQ := hg'.choose_spec.2.2
      have hmem : (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g' v)) ∈
          Submodule.span ℂ {k : ℬₛ |
            ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
              (∀ v : S, v.val ∈ insert w T' → g v (Multiplicative.ofAdd 0) = 0) ∧
              (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = k} := by
        apply Submodule.subset_span
        refine ⟨f, g', fun v hv ↦ ?_, rfl⟩
        by_cases hvw : v = w'
        · rw [hvw]; exact hg'w
        · refine (congrArg (fun k : ℬ(v.val.adicCompletion F) ↦ k (Multiplicative.ofAdd 0))
            (hg'v v hvw)).trans (hg v ?_)
          rcases Finset.mem_insert.mp hv with h' | h'
          · exact absurd (Subtype.ext h') hvw
          · exact h'
      exact (congrArg (· ∈ Submodule.span ℂ {k : ℬₛ |
            ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
              (∀ v : S, v.val ∈ insert w T' → g v (Multiplicative.ofAdd 0) = 0) ∧
              (sAdeleSchwartz_inductiveTensor_equiv F S).choose (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = k})
        hQ).mpr hmem
    · have hiff (v : S) : v.val ∈ insert w T' ↔ v.val ∈ T' := by
        rw [Finset.mem_insert]
        exact or_iff_right fun h' ↦ hwS (h' ▸ v.property)
      simp only [hiff]
      exact hprev

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The selected finite zero-coordinate conditions cut out the span in (5.3.4.15).
Deviation: At the selected places its factors are the zero extensions of compactly
supported locally constant tests on the unit group. -/
theorem sAdeleFiniteZeroSchwartz_eq_span_tmul (T : Finset V) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdeleFiniteZeroSchwartz S T = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by
  intro e
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  have mem (h : ℬₛ) : h ∈ sAdeleFiniteZeroSchwartz S T ↔
      ∀ x : {x : Aₛ // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}, h (Multiplicative.ofAdd x.val) = 0 :=
    Submodule.mem_iInf _
  refine le_antisymm ?_ ?_
  · exact fun h hh ↦ sAdeleFiniteZeroSchwartz_eq_span_tmul_ind T T subset_rfl h hh
  · rw [Submodule.span_le]
    rintro _ ⟨f, g, hg, rfl⟩
    refine (mem _).mpr fun x ↦ ?_
    refine x.property.elim fun v hvx ↦ ?_
    have hv := hvx.1
    have hx := hvx.2
    exact (he f g x.val).trans
      (by rw [Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hx, hg v hv]), mul_zero])

/-- Paper: Definition 5.3.4.1, p. 259.
The slice definition equals the span of the corrected pure tensors in (5.3.4.1). Their
archimedean factor is flat and their finite factors vanish at zero. -/
theorem sAdelePolarFree_eq_span_tmul (r : RealModels) (c : ComplexModels) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePolarFree S r c = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∃ f₀ : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces),
          ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x)))) ∧
        (∀ v : S, g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by
  classical
  intro e
  let A := archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)
  let coord : ℬ(A∞) →ₗ[ℂ] (ArchCoordinates → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦ Multiplicative.ofAdd (assemble(r, c, x)))).comp
      (schwartzBruhatSubmodule (Multiplicative A∞)).subtype
  let flat := A.map ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
  let U := flat.comap coord
  let V' := U.exists_isCompl.choose
  have hV := U.exists_isCompl.choose_spec
  let P := U.projection V' hV
  let T (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :=
    e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))
  let W := Submodule.span ℂ {h : ℬₛ | ∃ f ∈ U, ∃ g : ∀ v : S, ℬ(v.val.adicCompletion F),
    (∀ v, g v (Multiplicative.ofAdd 0) = 0) ∧ T f g = h}
  have hT (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) (x : Aₛ) :
      T f g (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd x.1) *
        ∏ v, g v (Multiplicative.ofAdd (x.2 v)) :=
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f g x
  have hU (f : ℬ(A∞)) : f ∈ U ↔ ∃ f₀ : A,
      ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x))) := by
    change (∃ u ∈ A, (u : ArchCoordinates → ℂ) = coord f) ↔ _
    exact ⟨fun ⟨u, hu, he⟩ ↦ ⟨⟨u, hu⟩, congrFun he⟩,
      fun ⟨u, hu⟩ ↦ ⟨u.val, u.property, funext hu⟩⟩
  suffices sAdelePolarFree S r c = W by
    simpa only [W, hU, T, and_assoc, exists_and_left, exists_prop] using this
  refine le_antisymm (fun h hh ↦ ?_) (Submodule.span_le.mpr ?_)
  · have hfin := (Submodule.mem_inf.mp hh).1
    rw [sAdeleFiniteZeroSchwartz_eq_span_tmul] at hfin
    -- Project the archimedean factor in a finite sum, recording the effect on each slice.
    let sliced (h k : ℬₛ) := ∀ y : (v : S) → v.val.adicCompletion F, ∃ a : ℬ(A∞),
      (∀ x : A∞, a (Multiplicative.ofAdd x) = h (Multiplicative.ofAdd (x, y))) ∧
      (∀ x : A∞, P a (Multiplicative.ofAdd x) = k (Multiplicative.ofAdd (x, y)))
    have projected : ∃ k ∈ W, sliced h k := by
      clear hh
      induction hfin using Submodule.span_induction with
      | mem h hh =>
        obtain ⟨f, g, hg, rfl⟩ := hh
        refine ⟨T (P f) g, Submodule.subset_span ⟨P f, U.projection_apply_mem hV f,
          g, fun v ↦ hg v v.property, rfl⟩, fun y ↦ ?_⟩
        let s := ∏ v : S, g v (Multiplicative.ofAdd (y v))
        refine ⟨s • f, fun x ↦ (mul_comm s _).trans (hT f g (x, y)).symm, fun x ↦ ?_⟩
        rw [map_smul]
        exact (mul_comm s _).trans (hT (P f) g (x, y)).symm
      | zero => exact ⟨0, W.zero_mem, fun _ ↦ ⟨0, fun _ ↦ rfl, by rw [map_zero]; intro; rfl⟩⟩
      | add h k _ _ ih ik =>
        obtain ⟨h', hh', eh⟩ := ih
        obtain ⟨k', hk', ek⟩ := ik
        refine ⟨h' + k', W.add_mem hh' hk', fun y ↦ ?_⟩
        obtain ⟨a, ha, hpa⟩ := eh y
        obtain ⟨b, hb, hpb⟩ := ek y
        exact ⟨a + b, fun x ↦ congrArg₂ (· + ·) (ha x) (hb x), by
          rw [map_add]; exact fun x ↦ congrArg₂ (· + ·) (hpa x) (hpb x)⟩
      | smul s h _ ih =>
        obtain ⟨k, hk, e'⟩ := ih
        refine ⟨s • k, W.smul_mem s hk, fun y ↦ ?_⟩
        obtain ⟨a, ha, hpa⟩ := e' y
        exact ⟨s • a, fun x ↦ congrArg (s * ·) (ha x), by
          rw [map_smul]; exact fun x ↦ congrArg (s * ·) (hpa x)⟩
    obtain ⟨k, hk, ek⟩ := projected
    suffices h = k by rwa [this]
    apply SchwartzBruhat.ext
    rintro ⟨x, y⟩
    obtain ⟨a, ha, hpa⟩ := ek y
    have hslice := (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hh).2 y
    have hflat : a ∈ U := by
      obtain ⟨u, hu, eu⟩ := hslice
      exact (hU a).mpr ⟨⟨u, hu⟩, fun z ↦ (congrFun eu z).trans (ha _).symm⟩
    rw [show P a = a from U.projection_apply_of_mem_left hV hflat] at hpa
    exact (ha x).symm.trans (hpa x)
  · rintro _ ⟨f, hf, g, hg, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun y ↦ ?_⟩
    · apply (Submodule.mem_iInf _).mpr
      rintro ⟨x, v, _, hx⟩
      change T f g (Multiplicative.ofAdd x) = 0
      rw [hT, Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hx, hg v]), mul_zero]
    · let s := ∏ v : S, g v (Multiplicative.ofAdd (y v))
      obtain ⟨u, hu⟩ := (hU f).mp hf
      refine ⟨s • u.val, A.smul_mem s u.property, funext fun z ↦ ?_⟩
      exact (congrArg (s * ·) (hu z)).trans ((mul_comm _ _).trans (hT f g (_, y)).symm)

/-- In archimedean coordinates the chosen models differ from the mixed-space coordinates
by a continuous real-linear equivalence. -/
private theorem sAdelePolarFree_mixedCoordinates (r : RealModels) (c : ComplexModels) :
    ∃ D : ArchCoordinates ≃L[ℝ] mixedEmbedding.mixedSpace F,
      ∀ x, D x = InfiniteAdeleRing.ringEquiv_mixedSpace F (assemble(r, c, x)) := by
  have hcontR (w : RealPlaces) : Continuous (r w).val.symm := by
    convert (IsHomeomorph.homeomorph _ (r w).property).symm.continuous using 1
    funext z
    apply (r w).property.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph _ (r w).property).apply_symm_apply z).symm
  have hR (w : RealPlaces) (t : ℝ) :
      InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((r w).val.symm t) = t := by
    let φ : ℝ →+ ℝ := ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).toRingHom.comp
      (r w).val.symm.toRingHom).toAddMonoidHom
    have hφ : Continuous φ :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp (hcontR w)
    have h1 : φ 1 = 1 := map_one ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).toRingHom.comp
      (r w).val.symm.toRingHom)
    have h := map_real_smul φ hφ t 1
    rw [smul_eq_mul, mul_one, h1, smul_eq_mul, mul_one] at h
    exact h
  have hcont (w : ComplexPlaces) : Continuous (c w).val.symm := by
    convert (IsHomeomorph.homeomorph _ (c w).property).symm.continuous using 1
    funext z
    apply (c w).property.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph _ (c w).property).apply_symm_apply z).symm
  let ψ (w : ComplexPlaces) : ℂ ≃+* ℂ :=
    (c w).val.symm.trans (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2)
  have hreal (w : ComplexPlaces) (t : ℝ) : ψ w t = t := by
    rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := (ψ w).toRingHom)
      ((InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
        (hcont w)) with h | h
    · exact RingHom.congr_fun h t
    · exact (RingHom.congr_fun h t).trans (Complex.conj_ofReal t)
  let L : ArchCoordinates ≃ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    { toFun := fun x ↦ (x.1, fun w ↦ ψ w (x.2 w))
      invFun := fun x ↦ (x.1, fun w ↦ (ψ w).symm (x.2 w))
      map_add' := fun x y ↦ Prod.ext rfl (funext fun w ↦ map_add _ _ _)
      map_smul' := fun t x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ w (t • x.2 w) = t • ψ w (x.2 w)
        rw [Complex.real_smul, Complex.real_smul, map_mul, hreal])
      left_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ (ψ w).symm_apply_apply _)
      right_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ (ψ w).apply_symm_apply _) }
  refine ⟨L.toContinuousLinearEquiv, fun x ↦ ?_⟩
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
  · change x.1 w = _
    have hw : w.1.IsReal := w.2
    simp only [hw, ↓reduceDIte]
    exact (hR w _).symm
  · change ψ w (x.2 w) = _
    have hw : ¬ w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
    simp only [hw, ↓reduceDIte]
    rfl

/-- Restricting an S-adelic Schwartz–Bruhat function to an archimedean slice gives a
classical Schwartz function, continuously in the S-adelic topology. -/
private theorem sAdelePolarFree_slice (r : RealModels) (c : ComplexModels)
    (y : (v : S) → v.val.adicCompletion F) :
    ∃ Φ : ℬₛ →L[ℂ] 𝓢(ArchCoordinates, ℂ),
      ∀ f x, Φ f x = f (Multiplicative.ofAdd (assemble(r, c, x), y)) := by
  obtain ⟨D, hD⟩ := sAdelePolarFree_mixedCoordinates r c
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F))
  let Q : ℬ(A∞) →L[ℂ] 𝓢(ArchCoordinates, ℂ) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D).comp J.symm.toContinuousLinearMap
  have hQ (f : ℬ(A∞)) (x : ArchCoordinates) :
      Q f x = f (Multiplicative.ofAdd (assemble(r, c, x))) := by
    change J.symm f (D x) = _
    rw [hD, ← hJ, J.apply_symm_apply]
  let ev (v : S) : ℬ(v.val.adicCompletion F) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (Multiplicative.ofAdd (y v))).comp (schwartzBruhatSubmodule _).subtype
  let E : W →ₗ[ℂ] ℂ := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ S ℂ).compLinearMap ev)
  let B : ℬ(A∞) →ₗ[ℂ] W →ₗ[ℂ] 𝓢(ArchCoordinates, ℂ) :=
    LinearMap.mk₂ ℂ (fun f w ↦ E w • Q f)
      (fun f f' w ↦ by simp only [map_add, smul_add])
      (fun a f w ↦ by simp only [map_smul, smul_comm a (E w)])
      (fun f w w' ↦ by simp only [map_add, add_smul])
      (fun a f w ↦ by simp only [map_smul, smul_eq_mul, mul_smul])
  let T : InductiveTensor ℬ(A∞) W →ₗ[ℂ] 𝓢(ArchCoordinates, ℂ) := TensorProduct.lift B
  let : PolynormableSpace ℂ 𝓢(ArchCoordinates, ℂ) :=
    (schwartz_withSeminorms ℂ ArchCoordinates ℂ).toPolynormableSpace
  let : T2Space ℬ(A∞) := schwartzBruhat_eval_t2
  let : T2Space W := finestLocallyConvex_t2 _
  have hT : Continuous T := by
    rw [continuous_inductiveTensor_iff]
    refine ⟨fun f ↦ ?_, fun w ↦ ?_⟩
    · change Continuous fun w : W ↦ E w • Q f
      exact (continuous_of_finestLocallyConvex _ E).smul continuous_const
    · change Continuous fun f ↦ E w • Q f
      exact (continuous_const (y := E w)).smul Q.continuous
  have hTe (t : InductiveTensor ℬ(A∞) W) (x : ArchCoordinates) :
      T t x = e t (Multiplicative.ofAdd (assemble(r, c, x), y)) := by
    let p : Multiplicative Aₛ := Multiplicative.ofAdd (assemble(r, c, x), y)
    let evx : 𝓢(ArchCoordinates, ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun g ↦ g x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    let evp : ℬₛ →ₗ[ℂ] ℂ := (LinearMap.proj p).comp (schwartzBruhatSubmodule _).subtype
    let L₁ : InductiveTensor ℬ(A∞) W →ₗ[ℂ] ℂ := evx.comp T
    let L₂ : InductiveTensor ℬ(A∞) W →ₗ[ℂ] ℂ := evp.comp e.toLinearMap
    have key : L₁ = L₂ := by
      refine TensorProduct.ext' fun f w ↦ ?_
      let M₁ : (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)) →ₗ[ℂ] ℂ :=
        L₁.comp (TensorProduct.mk ℂ ℬ(A∞) W f)
      let M₂ : (⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)) →ₗ[ℂ] ℂ :=
        L₂.comp (TensorProduct.mk ℂ ℬ(A∞) W f)
      have hM : M₁ = M₂ := by
        refine PiTensorProduct.ext (MultilinearMap.ext fun g ↦ ?_)
        have hE : E (PiTensorProduct.tprod ℂ g) = ∏ v, g v (Multiplicative.ofAdd (y v)) := by
          erw [PiTensorProduct.lift.tprod]
          rfl
        have h1 : M₁ (PiTensorProduct.tprod ℂ g) = E (PiTensorProduct.tprod ℂ g) * Q f x := rfl
        have h2 : M₂ (PiTensorProduct.tprod ℂ g) =
            e (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g) p := rfl
        refine h1.trans (Eq.trans ?_ h2.symm)
        exact (congrArg₂ (· * ·) hE (hQ f x)).trans
          ((mul_comm _ _).trans (he f g (assemble(r, c, x), y)).symm)
      exact LinearMap.congr_fun hM w
    exact LinearMap.congr_fun key t
  refine ⟨⟨T.comp e.symm.toLinearMap, hT.comp e.symm.continuous⟩, fun f x ↦ ?_⟩
  change T (e.symm f) x = _
  rw [hTe, e.apply_symm_apply]
/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free functions form a closed subspace in the S-adelic Schwartz–Bruhat topology. -/
theorem sAdelePolarFree_isClosed (r : RealModels) (c : ComplexModels) :
    IsClosed (↑(sAdelePolarFree S r c) : Set ℬₛ) := by
  obtain ⟨D, hD⟩ := sAdelePolarFree_mixedCoordinates r c
  choose Φ hΦ using sAdelePolarFree_slice (S := S) r c
  have hset : (↑(sAdelePolarFree S r c) : Set ℬₛ) =
      (⋂ x : {x : Aₛ // ∃ v : S, v.val ∈ S ∧ x.2 v = 0},
        {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) ∩
        ⋂ y, Φ y ⁻¹' (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces) : Set _) := by
    ext f
    simp only [SetLike.mem_coe, sAdelePolarFree, sAdeleFiniteZeroSchwartz, Submodule.mem_inf,
      Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker,
      Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun y ↦ ⟨?_, fun hf ↦ ⟨Φ y f, hf, ?_⟩⟩)
    · rintro ⟨h, hh, hfun⟩
      have : Φ y f = h := SchwartzMap.ext fun x ↦ (hΦ y f x).trans (congrFun hfun x).symm
      rwa [this]
    · exact funext fun x ↦ hΦ y f x
  rw [hset]
  refine (isClosed_iInter fun x ↦ ?_).inter (isClosed_iInter fun y ↦
    (archimedeanFlatSchwartz_isClosed).preimage (Φ y).continuous)
  let z := D.symm (InfiniteAdeleRing.ringEquiv_mixedSpace F x.val.1)
  have hz : assemble(r, c, z) = x.val.1 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    ((hD z).symm.trans (D.apply_symm_apply _))
  have hev : Continuous fun f : ℬₛ ↦ Φ x.val.2 f z :=
    ((BoundedContinuousFunction.evalCLM ℂ z).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ArchCoordinates ℂ)).continuous.comp
      (Φ x.val.2).continuous
  have heq : (fun f : ℬₛ ↦ Φ x.val.2 f z) = fun f ↦ f (Multiplicative.ofAdd x.val) :=
    funext fun f ↦ by rw [hΦ, hz]
  exact isClosed_eq (heq ▸ hev) continuous_const

/-- Paper: Lemma 5.3.4.2(1), p. 260.
Inverse left translation by an S-idele preserves the polar-free subspace. -/
theorem sAdelePolarFree_translate (r : RealModels) (c : ComplexModels)
    (g : Aₛˣ) (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) :
    schwartzBruhatUnitTranslate g f ∈ sAdelePolarFree S r c := by
  classical
  obtain ⟨hz, hflat⟩ := Submodule.mem_inf.1 _hf
  let u : Aₛ := (g⁻¹ : Aₛˣ).val
  have hu (w : InfinitePlace F) : u.1 w ≠ 0 := by
    have h1 : u.1 w * (g : Aₛ).1 w = 1 := by
      change (u * (g : Aₛ)).1 w = 1
      simp only [u, Units.inv_mul]
      rfl
    exact left_ne_zero_of_mul_eq_one h1
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · -- Multiplying by a unit keeps a zero finite coordinate.
    simp only [sAdeleFiniteZeroSchwartz, Submodule.mem_iInf, LinearMap.mem_ker] at hz ⊢
    rintro ⟨x, v, hv, hx⟩
    exact hz ⟨u * x, v, hv, by simp [hx]⟩
  · -- The archimedean part of the unit dilates the coordinates of every slice.
    let a : RealPlaces → ℝ := fun w ↦ (r w).val (u.1 w.val)
    let b : ComplexPlaces → ℂ := fun w ↦ (c w).val (u.1 w.val)
    have ha (w : RealPlaces) : a w ≠ 0 := (map_ne_zero_iff _ (r w).val.injective).2 (hu w.val)
    have hb (w : ComplexPlaces) : b w ≠ 0 := (map_ne_zero_iff _ (c w).val.injective).2 (hu w.val)
    let L : ArchCoordinates ≃ₗ[ℝ] ArchCoordinates :=
      { toFun := fun x ↦ (fun w ↦ a w * x.1 w, fun w ↦ b w * x.2 w)
        invFun := fun x ↦ (fun w ↦ (a w)⁻¹ * x.1 w, fun w ↦ (b w)⁻¹ * x.2 w)
        map_add' := fun x y ↦ Prod.ext (funext fun w ↦ mul_add _ _ _)
          (funext fun w ↦ mul_add _ _ _)
        map_smul' := fun t x ↦ Prod.ext (funext fun w ↦ by simp [mul_left_comm])
          (funext fun w ↦ by simp [Complex.real_smul, mul_left_comm])
        left_inv := fun x ↦ Prod.ext (funext fun w ↦ inv_mul_cancel_left₀ (ha w) _)
          (funext fun w ↦ inv_mul_cancel_left₀ (hb w) _)
        right_inv := fun x ↦ Prod.ext (funext fun w ↦ mul_inv_cancel_left₀ (ha w) _)
          (funext fun w ↦ mul_inv_cancel_left₀ (hb w) _) }
    let D : ArchCoordinates ≃L[ℝ] ArchCoordinates := L.toContinuousLinearEquiv
    have hD (x : ArchCoordinates) : D x = (fun w ↦ a w * x.1 w, fun w ↦ b w * x.2 w) := rfl
    have hasm (x : ArchCoordinates) : u.1 * assemble(r, c, x) = assemble(r, c, D x) := by
      funext w
      change u.1 w * _ = _
      by_cases hw : w.IsReal
      · simp only [hw, ↓reduceDIte, hD, a, map_mul, RingEquiv.symm_apply_apply]
      · simp only [hw, ↓reduceDIte, hD, b, map_mul, RingEquiv.symm_apply_apply]
    simp only [Submodule.mem_iInf] at hflat ⊢
    intro y
    have hy := hflat (u.2 * y)
    simp only [Submodule.mem_comap, Submodule.mem_map] at hy ⊢
    obtain ⟨h, hh, hfun⟩ := hy
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h, ?_, ?_⟩
    · simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
        IsLinearMap.mk'_apply] at hh ⊢
      rintro ⟨x, hx⟩ n v
      have hwall : (∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0) := by
        rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
        · exact Or.inl ⟨i, by simp [hD, hi]⟩
        · exact Or.inr ⟨j, by simp [hD, hj]⟩
      have hcomp := D.toContinuousLinearMap.iteratedFDeriv_comp_right (h.smooth ⊤) x
        (i := n) (mod_cast le_top)
      change iteratedFDeriv ℝ n ((h : ArchCoordinates → ℂ) ∘ D) x v = 0
      erw [hcomp]
      exact hh ⟨D x, hwall⟩ n (fun i ↦ D (v i))
    · funext x
      have e := congrFun hfun (D x)
      refine e.trans ?_
      change f (Multiplicative.ofAdd (assemble(r, c, D x), u.2 * y)) =
        f (Multiplicative.ofAdd (u * (assemble(r, c, x), y)))
      rw [← hasm]
      rfl

/-- Composing a flat Schwartz function with a real-linear automorphism of the
archimedean coordinates that keeps the coordinate walls keeps it flat. -/
private theorem archimedeanFlatSchwartz_comp_wall (D : ArchCoordinates ≃L[ℝ] ArchCoordinates)
    (hD : ∀ x : ArchCoordinates, ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0)) →
      ((∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0)))
    (h : 𝓢(ArchCoordinates, ℂ))
    (hh : h ∈ archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)) :
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h ∈
      archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces) := by
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
    IsLinearMap.mk'_apply] at hh ⊢
  rintro ⟨x, hx⟩ n v
  have hcomp := D.toContinuousLinearMap.iteratedFDeriv_comp_right (h.smooth ⊤) x
    (i := n) (mod_cast le_top)
  change iteratedFDeriv ℝ n ((h : ArchCoordinates → ℂ) ∘ D) x v = 0
  erw [hcomp]
  exact hh ⟨D x, hD x hx⟩ n (fun i ↦ D (v i))

/-- Changing the archimedean field identifications changes each slice by a
real-linear automorphism of the coordinates that keeps the walls. -/
private theorem sAdelePolarFree_le_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c ≤ sAdelePolarFree S r' c' := by
  classical
  intro f hf
  obtain ⟨hz, hflat⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨hz, ?_⟩
  -- At a real place both identifications agree, since `ℝ` has one ring endomorphism.
  have hR (w : RealPlaces) (t : ℝ) : (r' w).val.symm t = (r w).val.symm t := by
    have hρ : (r w).val.toRingHom.comp (r' w).val.symm.toRingHom = RingHom.id ℝ :=
      Subsingleton.elim _ _
    have h1 := RingHom.congr_fun hρ t
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply] at h1
    calc (r' w).val.symm t = (r w).val.symm ((r w).val ((r' w).val.symm t)) :=
          ((r w).val.symm_apply_apply _).symm
      _ = (r w).val.symm t := by rw [h1]
  -- At a complex place they differ by a continuous automorphism of `ℂ`.
  have hcont (w : ComplexPlaces) : Continuous (c' w).val.symm := by
    convert (IsHomeomorph.homeomorph _ (c' w).property).symm.continuous using 1
    funext z
    apply (c' w).property.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph _ (c' w).property).apply_symm_apply z).symm
  let ψ (w : ComplexPlaces) : ℂ →+* ℂ :=
    (c w).val.toRingHom.comp (c' w).val.symm.toRingHom
  let ψ' (w : ComplexPlaces) : ℂ →+* ℂ :=
    (c' w).val.toRingHom.comp (c w).val.symm.toRingHom
  have hψ (w : ComplexPlaces) (z : ℂ) : ψ w z = (c w).val ((c' w).val.symm z) := rfl
  have hψ' (w : ComplexPlaces) (z : ℂ) : ψ' w z = (c' w).val ((c w).val.symm z) := rfl
  have hreal (w : ComplexPlaces) (t : ℝ) : ψ w t = t := by
    rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := ψ w)
      ((c w).property.continuous.comp (hcont w)) with h | h
    · rw [h, RingHom.id_apply]
    · rw [h]
      exact Complex.conj_ofReal t
  let L : ArchCoordinates ≃ₗ[ℝ] ArchCoordinates :=
    { toFun := fun x ↦ (x.1, fun w ↦ ψ w (x.2 w))
      invFun := fun x ↦ (x.1, fun w ↦ ψ' w (x.2 w))
      map_add' := fun x y ↦ Prod.ext rfl (funext fun w ↦ map_add _ _ _)
      map_smul' := fun t x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ w (t • x.2 w) = t • ψ w (x.2 w)
        rw [Complex.real_smul, Complex.real_smul, map_mul, hreal])
      left_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ' w (ψ w (x.2 w)) = x.2 w
        rw [hψ, hψ', RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply])
      right_inv := fun x ↦ Prod.ext rfl (funext fun w ↦ by
        change ψ w (ψ' w (x.2 w)) = x.2 w
        rw [hψ, hψ', RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]) }
  let D : ArchCoordinates ≃L[ℝ] ArchCoordinates := L.toContinuousLinearEquiv
  have hD (x : ArchCoordinates) : D x = (x.1, fun w ↦ ψ w (x.2 w)) := rfl
  have hwall (x : ArchCoordinates) : ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0)) →
      ((∃ i, (D x).1 i = 0) ∨ (∃ j, (D x).2 j = 0)) := by
    rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact Or.inl ⟨i, by simp [hD, hi]⟩
    · exact Or.inr ⟨j, by simp [hD, hj]⟩
  have hasm (x : ArchCoordinates) : assemble(r, c, D x) = assemble(r', c', x) := by
    funext w
    by_cases hw : w.IsReal
    · simp only [hw, ↓reduceDIte, hD, hR]
    · simp only [hw, ↓reduceDIte, hD, hψ, RingEquiv.symm_apply_apply]
  simp only [Submodule.mem_iInf] at hflat ⊢
  intro y
  have hy := hflat y
  simp only [Submodule.mem_comap, Submodule.mem_map] at hy ⊢
  obtain ⟨h, hh, hfun⟩ := hy
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ D h,
    archimedeanFlatSchwartz_comp_wall D hwall h hh, ?_⟩
  funext x
  refine (congrFun hfun (D x)).trans ?_
  change f (Multiplicative.ofAdd (assemble(r, c, D x), y)) =
    f (Multiplicative.ofAdd (assemble(r', c', x), y))
  rw [hasm]

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free subspace is independent of the archimedean field identifications. -/
theorem sAdelePolarFree_eq_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c = sAdelePolarFree S r' c' :=
  le_antisymm (sAdelePolarFree_le_of_models r r' c c') (sAdelePolarFree_le_of_models r' r c' c)

/-- A Schwartz–Bruhat function on a group, pulled back along a topological group
isomorphism, is integrable for every Haar measure. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_pullback {G H : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Measure G) [μ.IsHaarMeasure] (Φ : G ≃ₜ* H) (T : SchwartzBruhat H) :
    Integrable (fun g ↦ T.val (Φ g)) μ := by
  have hT := SchwartzBruhat.integrable (μ.map Φ) T
  exact (Φ.toHomeomorph.measurableEmbedding.integrable_map_iff.mp hT)

/-- A finite-place Schwartz–Bruhat function vanishing at zero is integrable on the
units against every norm power. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_finite {K : Type*} [NormedField K]
    [MeasurableSpace Kˣ] [OpensMeasurableSpace Kˣ] (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    (h : Kˣ → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) (σ : ℝ) :
    Integrable (fun u : Kˣ ↦ ‖h u‖ * ‖u.val‖ ^ σ) μ := by
  have hc : Continuous (fun u : Kˣ ↦ ‖u.val‖ ^ σ) :=
    (continuous_norm.comp Units.continuous_val).rpow_const
      (fun u ↦ Or.inl (norm_ne_zero_iff.mpr u.ne_zero))
  exact (hh.norm.mul hc).integrable_of_hasCompactSupport (hs.norm.mul_right)


/-- A ring isomorphism that is a homeomorphism has a continuous inverse. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_symm {A B : Type*} [Ring A] [Ring B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃+* B) (he : IsHomeomorph e) :
    Continuous e.symm := by
  convert (IsHomeomorph.homeomorph _ he).symm.continuous using 1
  funext z
  apply he.injective
  rw [RingEquiv.apply_symm_apply]
  exact ((IsHomeomorph.homeomorph _ he).apply_symm_apply z).symm

/-- A product over the infinite places splits into the real and the complex places. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_prod (φ : InfinitePlace F → ℝ) :
    ∏ w, φ w = (∏ i : RealPlaces, φ i.val) * ∏ j : ComplexPlaces, φ j.val := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F ↦ w.IsReal) φ]
  congr 1
  exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun w ↦ InfinitePlace.not_isReal_iff_isComplex)
    _ _ (fun _ ↦ rfl)

/-- The modulus of a norm twist of a unitary character is the corresponding real norm power. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_norm (χ : PontryaginDual Jₛ) (s : ℂ)
    (g : Aₛˣ) :
    ‖chartₛ(χ) s (QuotientGroup.mk g)‖ =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ ((w.mult : ℝ) * s.re)) *
        ∏ v : S, ‖g.val.2 v‖ ^ s.re := by
  change ‖(χ (QuotientGroup.mk g) : ℂ) * ((((mₛ (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ)) ^ s‖ = _
  rw [norm_mul, Circle.norm_coe, one_mul, sIdeleQuotientNorm_mk,
    Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hnorm : (((sIdeleNorm F S g : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖ := by
    simp [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map,
      NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_pow]
  rw [hnorm, Real.mul_rpow (by positivity) (by positivity),
    ← Real.finsetProd_rpow _ _ (fun w _ ↦ by positivity),
    ← Real.finsetProd_rpow _ _ (fun v _ ↦ by positivity)]
  congr 1
  exact Finset.prod_congr rfl fun w _ ↦
    (Real.rpow_natCast_mul (norm_nonneg (g.val.1 w)) w.mult s.re).symm


/-- On a pure tensor with a flat archimedean factor and finite factors vanishing at zero,
the zeta integrand is absolutely integrable at every norm twist. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_tensor (r : RealModels)
    (c : ComplexModels)
    (hr : ∀ (w : RealPlaces) (x : w.val.Completion), ‖(r w).val x‖ = ‖x‖)
    (hc : ∀ (w : ComplexPlaces) (x : w.val.Completion), ‖(c w).val x‖ = ‖x‖)
    (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F))
    (f₀ : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces))
    (hf₀ : ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x))))
    (hg : ∀ v : S, g v (Multiplicative.ofAdd 0) = 0) (h : ℬₛ)
    (hh : ∀ x : Aₛ, h (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x.1) * ∏ v : S, g v (Multiplicative.ofAdd (x.2 v)))
    (χ : PontryaginDual Jₛ) (z : ℂ) :
    Integrable (fun u : Aₛˣ ↦ h (Multiplicative.ofAdd u.val) * chartₛ(χ) z (QuotientGroup.mk u))
      (sMultiplicativeTamagawaMeasure F S) := by
  classical
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  have (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  have (v : V) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let (v : V) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have (v : V) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have (w : InfinitePlace F) : BorelSpace w.Completionˣ := ⟨by
    change (borel w.Completion).comap Units.val = _
    rw [← borel_comap, ← (Units.isEmbedding_val₀ (G₀ := w.Completion)).eq_induced]⟩
  have (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  have (v : V) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have (v : V) : SecondCountableTopology (v.adicCompletion F)ˣ :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
  have (v : V) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace Aₛ :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let μa := infiniteLocalMultiplicativeTamagawaMeasure F
  let μb := fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val
  have (w : InfinitePlace F) : (μa w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure w
  have (v : S) : (μb v).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let ψ : (((w : InfinitePlace F) → w.Completionˣ) × ((v : S) → (v.val.adicCompletion F)ˣ)) →
      Aₛˣ := fun x ↦ e.symm (eArch.symm x.1, eS.symm x.2)
  have hmap : sMultiplicativeTamagawaMeasure F S =
      ((Measure.pi μa).prod (Measure.pi μb)).map ψ := rfl
  have hB := sIdeleGroup_borelSpace (F := F) (S := S)
  let φ (u : Aₛˣ) : ℂ := h (Multiplicative.ofAdd u.val) * chartₛ(χ) z (QuotientGroup.mk u)
  have hφ : Continuous φ :=
    ((schwartzBruhat_continuous (G := Multiplicative Aₛ) h).comp
      (continuous_ofAdd.comp Units.continuous_val)).mul
      ((chartₛ(χ) z).continuous.comp QuotientGroup.continuous_mk)
  have hψ : Continuous ψ := e.symm.continuous.comp
    ((eArch.symm.continuous.comp continuous_fst).prodMk (eS.symm.continuous.comp continuous_snd))
  rw [hmap]
  refine (integrable_map_measure ?_ hψ.measurable.aemeasurable).mpr ?_
  · rw [← hmap]
    exact hφ.aestronglyMeasurable
  let A (a : (w : InfinitePlace F) → w.Completionˣ) : ℝ :=
    ‖f (Multiplicative.ofAdd (show A∞ from fun w ↦ (a w).val))‖ *
      ∏ w, ‖(a w).val‖ ^ ((w.mult : ℝ) * z.re)
  let Bf (v : S) (u : (v.val.adicCompletion F)ˣ) : ℝ :=
    ‖g v (Multiplicative.ofAdd u.val)‖ * ‖u.val‖ ^ z.re
  have hA : Integrable A (Measure.pi μa) := by
    obtain ⟨R, hR⟩ :=
      archimedeanFlatSchwartz_restrict_to_weighted (ι := RealPlaces) (κ := ComplexPlaces)
    let wt : ((RealPlaces → (insert 0 univ : Set ℝ)) × (ComplexPlaces → (insert 0 univ : Set ℝ))) :=
      (fun _ ↦ ⟨z.re, by simp⟩, fun _ ↦ ⟨z.re, by simp⟩)
    let f₁ : ↥(archimedeanWeightedSchwartzSubmodule (ι := RealPlaces) (κ := ComplexPlaces) univ) :=
      R f₀
    let T := archimedeanSchwartzTwist univ wt f₁
    let : MeasurableSpace ((RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)) := borel _
    have : BorelSpace ((RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)) := ⟨rfl⟩
    have hrs (i : RealPlaces) :=
      sLocalIdelicZFunction_entire_of_polarFree_symm (r i).val (r i).property
    have hcs (j : ComplexPlaces) :=
      sLocalIdelicZFunction_entire_of_polarFree_symm (c j).val (c j).property
    let Φ : ((w : InfinitePlace F) → w.Completionˣ) ≃ₜ*
        ((RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)) :=
      { toFun := fun a ↦ (fun i ↦ Units.map (r i).val.toMonoidHom (a i.val),
          fun j ↦ Units.map (c j).val.toMonoidHom (a j.val))
        invFun := fun u w ↦ if hw : w.IsReal then
            Units.map (r ⟨w, hw⟩).val.symm.toMonoidHom (u.1 ⟨w, hw⟩)
          else Units.map (c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).val.symm.toMonoidHom
            (u.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)
        left_inv := fun a ↦ funext fun w ↦ by
          by_cases hw : w.IsReal
          · simp only [hw, ↓reduceDIte]
            ext
            simp
          · simp only [hw, ↓reduceDIte]
            ext
            simp
        right_inv := fun u ↦ Prod.ext (funext fun i ↦ by
            simp only [i.2, ↓reduceDIte]
            ext
            simp)
          (funext fun j ↦ by
            simp only [InfinitePlace.not_isReal_iff_isComplex.mpr j.2, ↓reduceDIte]
            ext
            simp)
        map_mul' := fun a b ↦ Prod.ext (funext fun i ↦ map_mul _ _ _)
          (funext fun j ↦ map_mul _ _ _)
        continuous_toFun := (continuous_pi fun i ↦
            (Continuous.units_map _ (r i).property.continuous).comp (continuous_apply i.val)).prodMk
          (continuous_pi fun j ↦
            (Continuous.units_map _ (c j).property.continuous).comp (continuous_apply j.val))
        continuous_invFun := continuous_pi fun w ↦ by
          by_cases hw : w.IsReal
          · simp only [hw, ↓reduceDIte]
            exact (Continuous.units_map _ (hrs _)).comp ((continuous_apply _).comp continuous_fst)
          · simp only [hw, ↓reduceDIte]
            exact (Continuous.units_map _ (hcs _)).comp ((continuous_apply _).comp continuous_snd) }
    refine (sLocalIdelicZFunction_entire_of_polarFree_pullback (Measure.pi μa) Φ T).norm.congr
      (ae_of_all _ fun a ↦ ?_)
    have hT := archimedeanSchwartzTwist_apply univ wt f₁ (Φ a)
    have hRv := hR f₀ (Φ a)
    have e1 (i : RealPlaces) : ‖((Φ a).1 i).val‖ = ‖(a i.val).val‖ := hr i _
    have e2 (j : ComplexPlaces) : ‖((Φ a).2 j).val‖ = ‖(a j.val).val‖ := hc j _
    have hasm : assemble(r, c, ((fun i ↦ ((Φ a).1 i).val, fun j ↦ ((Φ a).2 j).val) :
        ArchCoordinates)) = (show A∞ from fun w ↦ (a w).val) := by
      funext w
      by_cases hw : w.IsReal
      · simp [hw, Φ]
      · simp [hw, Φ]
    change ‖T (Φ a)‖ = A a
    rw [hT, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ by positivity),
      Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ ↦ by positivity)]
    change _ * _ * ‖(R f₀).val (Φ a)‖ = A a
    rw [hRv, hf₀, hasm]
    simp only [A, e1, e2]
    rw [sLocalIdelicZFunction_entire_of_polarFree_prod
      (fun w ↦ ‖(a w).val‖ ^ ((w.mult : ℝ) * z.re))]
    have hre (i : RealPlaces) : ‖(a i.val).val‖ ^ ((i.val.mult : ℝ) * z.re) =
        ‖(a i.val).val‖ ^ ((wt.1 i : ℝ)) := by
      simp [wt, i.2.mult_eq_one]
    have hco (j : ComplexPlaces) : ‖(a j.val).val‖ ^ ((j.val.mult : ℝ) * z.re) =
        (‖(a j.val).val‖ ^ (2 : ℕ)) ^ ((wt.2 j : ℝ)) := by
      rw [j.2.mult_eq_two, ← Real.rpow_natCast_mul (norm_nonneg _)]
    simp only [hre, hco]
    ring
  have hBf (v : S) : Integrable (Bf v) (μb v) := by
    obtain ⟨-, hcs⟩ := (exists_finitePlaceSchwartz_zeroExtension_iff v.val
      (fun u ↦ g v (Multiplicative.ofAdd u.val))).mp ⟨g v, hg v, fun u ↦ rfl⟩
    exact sLocalIdelicZFunction_entire_of_polarFree_finite (μb v) _
      ((schwartzBruhat_continuous (G := Multiplicative (v.val.adicCompletion F)) (g v)).comp
        (continuous_ofAdd.comp Units.continuous_val)) hcs z.re
  have hmaj := hA.mul_prod (Integrable.fintype_prod_dep hBf)
  refine hmaj.mono' (hφ.comp hψ).aestronglyMeasurable (ae_of_all _ fun p ↦ le_of_eq ?_)
  change ‖h (Multiplicative.ofAdd (ψ p).val) * chartₛ(χ) z (QuotientGroup.mk (ψ p))‖ =
    A p.1 * ∏ v, Bf v (p.2 v)
  have h₁ : (ψ p).val.1 = (show A∞ from fun w ↦ (p.1 w).val) := rfl
  have h₂ (v : S) : (ψ p).val.2 v = (p.2 v).val := rfl
  rw [norm_mul, sLocalIdelicZFunction_entire_of_polarFree_norm, hh, norm_mul, norm_prod, h₁]
  simp only [h₂, A, Bf, Finset.prod_mul_distrib]
  ring


/-- A logarithm times a power with exponent within one of σ is bounded by the
powers with exponents σ - 2, σ and σ + 2. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_log {σ x t : ℝ} (hx : |x - σ| < 1) (ht : 0 < t) :
    t ^ x * |Real.log t| ≤ t ^ (σ - 2) + 2 * t ^ σ + t ^ (σ + 2) := by
  have hlog : |Real.log t| ≤ t + t⁻¹ := by
    rcases le_or_gt 1 t with h1 | h1
    · rw [abs_of_nonneg (Real.log_nonneg h1)]
      have := Real.log_le_sub_one_of_pos ht
      have : 0 < t⁻¹ := inv_pos.mpr ht
      linarith
    · rw [abs_of_neg (Real.log_neg ht h1), ← Real.log_inv]
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
      linarith
  have hpow : t ^ x ≤ t ^ (σ - 1) + t ^ (σ + 1) := by
    have h1 := abs_lt.mp hx
    rcases le_or_gt 1 t with h | h
    · have := Real.rpow_le_rpow_of_exponent_le h (show x ≤ σ + 1 by linarith)
      have : 0 ≤ t ^ (σ - 1) := by positivity
      linarith
    · have := Real.rpow_le_rpow_of_exponent_ge ht h.le (show σ - 1 ≤ x by linarith)
      have : 0 ≤ t ^ (σ + 1) := by positivity
      linarith
  have e1 : t ^ (σ - 1) * t = t ^ σ := by
    rw [← Real.rpow_add_one ht.ne']; ring_nf
  have e2 : t ^ (σ - 1) * t⁻¹ = t ^ (σ - 2) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; ring_nf
  have e3 : t ^ (σ + 1) * t = t ^ (σ + 2) := by
    rw [← Real.rpow_add_one ht.ne']; ring_nf
  have e4 : t ^ (σ + 1) * t⁻¹ = t ^ σ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]; ring_nf
  calc t ^ x * |Real.log t| ≤ (t ^ (σ - 1) + t ^ (σ + 1)) * (t + t⁻¹) :=
        mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
    _ = _ := by
        rw [add_mul, mul_add, mul_add, e1, e2, e3, e4]; ring

/-- An integral of a test times a unitary weight times a complex power of a positive
function is entire when it converges absolutely at every exponent. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_analytic {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (f χ : G → ℂ) (t : G → ℝ) (ht : ∀ g, 0 < t g) (htm : Measurable t)
    (hχ : ∀ g, ‖χ g‖ = 1)
    (hint : ∀ z : ℂ, Integrable (fun g ↦ f g * (χ g * (t g : ℂ) ^ z)) μ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∫ g, f g * (χ g * (t g : ℂ) ^ z) ∂μ) univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro s _
  refine DifferentiableAt.differentiableWithinAt ?_
  let W (z : ℂ) (g : G) : ℂ := f g * (χ g * (t g : ℂ) ^ z)
  let D (z : ℂ) (g : G) : ℂ := W z g * Complex.log (t g : ℂ)
  have hnormW (z : ℂ) (g : G) : ‖W z g‖ = ‖f g‖ * t g ^ z.re := by
    simp only [W, norm_mul, hχ, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ht g)]
  let Vb : Set ℂ := Metric.ball s 1
  have hV : Vb ∈ 𝓝 s := Metric.ball_mem_nhds s one_pos
  have hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (W z) μ :=
    Eventually.of_forall fun z ↦ (hint z).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable (D s) μ :=
    (hint s).aestronglyMeasurable.mul (Complex.measurable_log.comp
      (Complex.measurable_ofReal.comp htm)).aestronglyMeasurable
  let bound (g : G) : ℝ := ‖W ((s.re - 2 : ℝ) : ℂ) g‖ + 2 * ‖W (s.re : ℂ) g‖ +
    ‖W ((s.re + 2 : ℝ) : ℂ) g‖
  have hbound : Integrable bound μ :=
    (((hint _).norm.add ((hint _).norm.const_mul 2)).add (hint _).norm)
  have hDbound : ∀ᵐ g ∂μ, ∀ z ∈ Vb, ‖D z g‖ ≤ bound g := Eventually.of_forall fun g z hz ↦ by
    have hlog : Complex.log (t g : ℂ) = (Real.log (t g) : ℂ) :=
      (Complex.ofReal_log (ht g).le).symm
    have hzr : |z.re - s.re| < 1 := by
      have h := Complex.abs_re_le_norm (z - s)
      rw [Complex.sub_re] at h
      exact h.trans_lt (by simpa [Vb, dist_eq_norm] using hz)
    simp only [D, bound]
    rw [norm_mul, hnormW, hlog, Complex.norm_real, Real.norm_eq_abs, hnormW, hnormW, hnormW,
      Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re, mul_assoc]
    calc ‖f g‖ * (t g ^ z.re * |Real.log (t g)|)
        ≤ ‖f g‖ * (t g ^ (s.re - 2) + 2 * t g ^ s.re + t g ^ (s.re + 2)) :=
          mul_le_mul_of_nonneg_left (sLocalIdelicZFunction_entire_of_polarFree_log hzr (ht g)) (norm_nonneg _)
      _ = _ := by ring
  have hdiff : ∀ᵐ g ∂μ, ∀ z ∈ Vb, HasDerivAt (fun w ↦ W w g) (D z g) z :=
    Eventually.of_forall fun g z _ ↦ by
      have hg : (t g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ht g).ne'
      simpa only [W, D, id_eq, mul_assoc, mul_one] using
        (((hasDerivAt_id z).const_cpow (Or.inl hg)).const_mul (χ g)).const_mul (f g)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hV hmeas (hint s) hDmeas
    hDbound hbound hdiff).2.differentiableAt

/-- The zeta integrand of a polar-free test is absolutely integrable at every norm twist. -/
private theorem sLocalIdelicZFunction_entire_of_polarFree_integrable (r : RealModels)
    (c : ComplexModels) (f : ℬₛ) (hf : f ∈ sAdelePolarFree S r c) (χ : PontryaginDual Jₛ)
    (z : ℂ) :
    Integrable (fun u : Aₛˣ ↦ f (Multiplicative.ofAdd u.val) * chartₛ(χ) z (QuotientGroup.mk u))
      (sMultiplicativeTamagawaMeasure F S) := by
  let r₀ : RealModels := fun w ↦ ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.2,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph.isHomeomorph⟩
  let c₀ : ComplexModels := fun w ↦ ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toHomeomorph.isHomeomorph⟩
  have hr₀ (w : RealPlaces) (x : w.val.Completion) : ‖(r₀ w).val x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal w.2)) x
  have hc₀ (w : ComplexPlaces) (x : w.val.Completion) : ‖(c₀ w).val x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2)) x
  have hspan := sAdelePolarFree_eq_span_tmul (S := S) r₀ c₀
  dsimp only at hspan
  rw [sAdelePolarFree_eq_of_models r r₀ c c₀, hspan] at hf
  refine Submodule.span_induction (p := fun f _ ↦ Integrable (fun u : Aₛˣ ↦
      f (Multiplicative.ofAdd u.val) * chartₛ(χ) z (QuotientGroup.mk u))
      (sMultiplicativeTamagawaMeasure F S)) ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨f, g, ⟨f₀, hf₀⟩, hg, hx⟩ := hx
    subst hx
    exact sLocalIdelicZFunction_entire_of_polarFree_tensor r₀ c₀ hr₀ hc₀ f g f₀ hf₀ hg _
      (fun x ↦ (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f g x) χ z
  · exact (integrable_zero _ _ _).congr (ae_of_all _ fun u ↦ (zero_mul _).symm)
  · intro x y _ _ hx hy
    exact (hx.add hy).congr (ae_of_all _ fun u ↦ (add_mul _ _ _).symm)
  · intro a x _ hx
    exact (hx.const_mul a).congr (ae_of_all _ fun u ↦ (mul_assoc _ _ _).symm)

-- TODO(paper-gap): The proof of (2) starts from entireness and concludes local vanishing.
-- Restricted local characters are coupled by the S-units, and a pole can cancel against
-- a zero of a different factor. The stated implication goes in the other direction.

/-- Paper: Lemma 5.3.4.2(2), p. 260.
The zeta transform of a polar-free test is entire on every norm-twist component. -/
theorem sLocalIdelicZFunction_entire_of_polarFree (r : RealModels) (c : ComplexModels)
    (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ := by
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : V) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace Aₛ :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  have hB := sIdeleGroup_borelSpace (F := F) (S := S)
  let t (u : Aₛˣ) : ℝ := (((mₛ (QuotientGroup.mk u) : ℝ≥0ˣ) : ℝ≥0) : ℝ)
  have ht (u : Aₛˣ) : 0 < t u := NNReal.coe_pos.mpr (Units.zero_lt _)
  have htc : Continuous t := NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((isProperMap_sIdeleQuotientNorm F S).continuous.comp QuotientGroup.continuous_mk))
  have hI := sLocalIdelicZFunction_entire_of_polarFree_analytic (sMultiplicativeTamagawaMeasure F S)
    (fun u : Aₛˣ ↦ f (Multiplicative.ofAdd u.val)) (fun u ↦ (χ (QuotientGroup.mk u) : ℂ)) t ht
    htc.measurable (fun u ↦ Circle.norm_coe _)
    (sLocalIdelicZFunction_entire_of_polarFree_integrable r c f _hf χ)
  have hI' : AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZetaIntegral f (chartₛ(χ) s)) univ := hI
  have hEq (s : ℂ) : sLocalIdelicZFunction f (chartₛ(χ) s) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) s) := by
    exact realArchimedeanMellin_existsUnique_eqNF (sLocalIdelicZFunction_meromorphic f χ) hI'.meromorphicNFOn
      (fun z hz ↦ sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩) s
  simpa only [hEq] using hI'

/-- A local quasi-character is constant on a neighborhood of each finite unit.
All powers of a sufficiently small principal unit lie in a neighborhood whose
image in the complex units contains no nontrivial cyclic group. -/
private theorem sAdelePolarFree_quasiCharacter_locallyConstant {K : Type*} [NormedField K]
    [IsUltrametricDist K] (b : QuasiCharacter Kˣ) : IsLocallyConstant (b : Kˣ → ℂ) := by
  let c : Kˣ →* ℂˣ := MonoidHom.toHomUnits b.toMonoidHom
  have hc : Continuous c := Units.isEmbedding_val₀.continuous_iff.mpr b.continuous
  have heu : IsLocallyEuclidean ℂˣ := by
    let d := (stdOrthonormalBasis ℝ ℂ).repr
    exact ⟨_, ⟨(d.toHomeomorph.isOpenEmbedding.comp (Units.isOpenEmbedding_val (R := ℂ))).singletonChartedSpace⟩⟩
  obtain ⟨W, hW, hpow⟩ := exists_nhds_one_of_isLocallyEuclidean heu
  have hn : c ⁻¹' W ∈ 𝓝 (1 : Kˣ) := hc.continuousAt.preimage_mem_nhds (by rwa [map_one])
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hn
  obtain ⟨N, hV, hsub⟩ := mem_comap.mp hn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hnear : ∀ᶠ u : Kˣ in 𝓝 1, b u = 1 := by
    have h₀ : ∀ᶠ u : Kˣ in 𝓝 1, u.val ∈ Metric.ball (1 : K) (min r 1) :=
      Units.continuous_val.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (lt_min hr one_pos))
    filter_upwards [h₀] with u hu
    have hdist : ‖u.val - 1‖ < min r 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hu
    have hb : ‖u.val‖ ≤ 1 := by
      calc ‖u.val‖ = ‖(u.val - 1) + 1‖ := by rw [sub_add_cancel]
           _ ≤ max ‖u.val - 1‖ ‖(1 : K)‖ := IsUltrametricDist.norm_add_le_max _ _
           _ ≤ 1 := max_le (hdist.le.trans (min_le_right _ _)) norm_one.le
    have heq : c u = 1 := hpow _ fun k ↦ by
      rw [← map_pow]
      apply hsub
      apply hball
      change dist (u.val ^ k) 1 < r
      rw [dist_eq_norm]
      exact (local_unit_pow_bound u.val hb k).trans_lt (hdist.trans_le (min_le_left _ _))
    exact congrArg Units.val heq
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hlim : Tendsto (fun y : Kˣ ↦ x⁻¹ * y) (𝓝 x) (𝓝 1) := by
    simpa using (continuous_const.mul continuous_id).tendsto x (f := fun y : Kˣ ↦ x⁻¹ * y)
  filter_upwards [hlim.eventually hnear] with y hy
  have eq := congrArg (b x * ·) hy
  simpa only [← map_mul, mul_inv_cancel_left, mul_one] using eq

/-- Multiply finite tests vanishing at zero on their compact support in the units.
An algebraic projection permits using the resulting map on the ambient finite tensor factor. -/
private theorem sAdelePolarFree_quasiCharacter_finite (v : V) (b : QuasiCharacter (v.adicCompletion F)ˣ) :
    ∃ P : ℬ(v.adicCompletion F) →ₗ[ℂ] ℬ(v.adicCompletion F), ∀ f : ℬ(v.adicCompletion F),
      f (Multiplicative.ofAdd 0) = 0 → P f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, P f (Multiplicative.ofAdd u.val) = b u * f (Multiplicative.ofAdd u.val) := by
  classical
  let K := v.adicCompletion F
  let A := ℬ(K)
  let Z : Submodule ℂ A := ((LinearMap.proj (Multiplicative.ofAdd (0 : K))).comp (schwartzBruhatSubmodule _).subtype).ker
  obtain ⟨Z', hZ⟩ := Z.exists_isCompl
  let p := Z.projection Z' hZ
  let h (x : Multiplicative K) : ℂ := if h : x.toAdd ≠ 0 then b (Units.mk0 x.toAdd h) else 0
  have hu (u : Kˣ) : h (Multiplicative.ofAdd u.val) = b u := by
    change (if hn : u.val ≠ 0 then b (Units.mk0 u.val hn) else 0) = b u
    rw [dite_eq_left u.ne_zero]
    exact congrArg b (Units.ext rfl)
  let L := (LinearMap.mulLeft ℂ h).comp ((schwartzBruhatSubmodule (Multiplicative K)).subtype.comp p)
  have hmem (f : A) : L f ∈ schwartzBruhatSubmodule (Multiplicative K) := by
    let t (u : Kˣ) := p f (Multiplicative.ofAdd u.val)
    have hz : p f (Multiplicative.ofAdd 0) = 0 := Z.projection_apply_mem hZ f
    obtain ⟨hl, hs⟩ := (exists_finitePlaceSchwartz_zeroExtension_iff v t).mp ⟨p f, hz, fun _ ↦ rfl⟩
    obtain ⟨g, h₀, hg⟩ := (exists_finitePlaceSchwartz_zeroExtension_iff v ((b : Kˣ → ℂ) * t)).mpr
      ⟨(sAdelePolarFree_quasiCharacter_locallyConstant b).mul hl, hs.mul_left⟩
    suffices heq : L f = g.val by rw [heq]; exact g.property
    funext x
    by_cases hn : x.toAdd = 0
    · change h x * p f x = g x
      rw [show x = Multiplicative.ofAdd 0 from congrArg Multiplicative.ofAdd hn, hz, mul_zero, h₀]
    · let u := Units.mk0 x.toAdd hn
      change h (Multiplicative.ofAdd u.val) * t u = g (Multiplicative.ofAdd u.val)
      rw [hu]; exact (hg u).symm
  let P : A →ₗ[ℂ] A := L.codRestrict _ hmem
  refine ⟨P, fun f hf ↦ ?_⟩
  have hp : p f = f := Z.projection_apply_of_mem_left hZ hf
  constructor
  · change _ * p f (Multiplicative.ofAdd 0) = 0
    rw [hp, hf, mul_zero]
  · intro u
    change h (Multiplicative.ofAdd u.val) * p f _ = _
    rw [hu, hp]

/-- Tensoring an inducing map with a space carrying its finest locally convex
topology still detects continuity. Expand in a Hamel basis of the second factor
and extend the seminorms on the first factor one coordinate at a time. -/
private theorem sAdelePolarFree_quasiCharacter_tensor_continuous
    {A B D X : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [IsTopologicalAddGroup B] [PolynormableSpace ℂ B]
    [AddCommGroup D] [Module ℂ D] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (i : A →ₗ[ℂ] B) (hi : IsInducing i)
    (L : X →ₗ[ℂ] InductiveTensor A (FinestLocallyConvex D))
    (hc : Continuous ((inductiveTensorMap i (LinearMap.id (R := ℂ) (M := FinestLocallyConvex D))).comp L)) :
    Continuous L := by
  classical
  let W := FinestLocallyConvex D
  let I := Module.Free.ChooseBasisIndex ℂ W
  let b := Module.Free.chooseBasis ℂ W
  let a := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  let c := TensorProduct.equivFinsuppOfBasisRight (M := B) b
  let t := c.trans (finsuppLequivDFinsupp ℂ)
  let j : A ⊗[ℂ] W →ₗ[ℂ] B ⊗[ℂ] W := TensorProduct.map i LinearMap.id
  have coords (u : A ⊗[ℂ] W) (k : I) : c (j u) k = i (a u k) := by
    induction u using TensorProduct.inductionOn with
    | tmul x y =>
      change c (i x ⊗ₜ[ℂ] y) k = i (a (x ⊗ₜ[ℂ] y) k)
      simp [a, c]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  apply (withGeneratingSeminorms_spec (A ⊗[ℂ] W) _).continuous_of_continuous_comp L
  intro s
  let p := s.val
  choose r hr he using fun k : I ↦ exists_seminorm_extension (f := i) hi
    (p := p.comp ((TensorProduct.mk ℂ A W).flip (b k))) (s.property.2 (b k))
  let P := (directSumSeminorm r).comp t.toLinearMap
  have hval (x : B) (y : W) : P (x ⊗ₜ[ℂ] y) = ∑ k ∈ (b.repr y).support, ‖b.repr y k‖ * r k x := by
    have hcoord (k : I) : t (x ⊗ₜ[ℂ] y) k = b.repr y k • x :=
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply _ _ _ _
    change directSumSeminorm r (t _) = _
    rw [directSumSeminorm_apply r _ (b.repr y).support (by
      intro k hk
      contrapose hk
      rw [DFinsupp.notMem_support_iff, hcoord, Finsupp.notMem_support_iff.mp hk, zero_smul])]
    simp only [hcoord, map_smul_eq_mul]
    rfl
  have hP : @Continuous (InductiveTensor B W) ℝ _ _ P := by
    let tests := fun p : {p : Seminorm ℂ (B ⊗[ℂ] W) //
      (∀ x : B, Continuous (fun y : W ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : W, Continuous (fun x : B ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val
    refine (withGeneratingSeminorms_spec _ tests).continuous_seminorm ⟨P, ?_, ?_⟩
    · intro x
      exact (finestLocallyConvex_withSeminorms D).continuous_seminorm (P.comp (TensorProduct.mk ℂ B W x))
    · intro y
      exact (continuous_finsetSum _ fun k _ ↦ continuous_const.mul (hr k)).congr fun x ↦ (hval x y).symm
  have hle (u : A ⊗[ℂ] W) : p u ≤ P (j u) := by
    let w := a u
    have hu : ∑ k ∈ w.support, w k ⊗ₜ[ℂ] b k = u :=
      (TensorProduct.equivFinsuppOfBasisRight_symm_apply b w).symm.trans (a.symm_apply_apply u)
    have hsub := Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) w.support
      (fun k ↦ w k ⊗ₜ[ℂ] b k)
    rw [hu] at hsub
    apply hsub.trans
    apply le_trans _ (sum_le_directSumSeminorm r (t (j u)) w.support)
    apply Finset.sum_le_sum
    intro k _
    change p (w k ⊗ₜ[ℂ] b k) ≤ r k (c (j u) k)
    rw [coords]
    exact (DFunLike.congr_fun (he k) (w k)).symm.le
  exact Seminorm.continuous_of_le (p := p.comp L) (q := P.comp (j.comp L))
    (hP.comp hc) (fun x ↦ hle (L x))

/-- On a subspace spanned by tensors with first factor in an embedded subspace,
the tensor action of an endomorphism of that subspace is continuous for the
inherited topology when the second factor has its finest locally convex topology. -/
private theorem sAdelePolarFree_quasiCharacter_tensor_action
    {A B D Y : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [PolynormableSpace ℂ A] [T2Space A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B] [PolynormableSpace ℂ B] [T2Space B]
    [AddCommGroup D] [Module ℂ D]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (e : InductiveTensor B (FinestLocallyConvex D) ≃L[ℂ] Y)
    (i : A →L[ℂ] B) (hi : IsEmbedding i) (M : A →L[ℂ] A) (P : FinestLocallyConvex D →ₗ[ℂ] FinestLocallyConvex D) (X : Submodule ℂ Y)
    (hX : X ≤ Submodule.span ℂ (range fun z : A × FinestLocallyConvex D ↦ e (i z.1 ⊗ₜ[ℂ] z.2))) :
    ∃ H : Y →ₗ[ℂ] Y, Continuous (H.comp X.subtype) ∧ ∀ a (d : FinestLocallyConvex D),
      H (e (i a ⊗ₜ[ℂ] d)) = e (i (M a) ⊗ₜ[ℂ] P d) := by
  let W := FinestLocallyConvex D
  let : T2Space W := finestLocallyConvex_t2 D
  let : IsTopologicalAddGroup B := PolynormableSpace.isTopologicalAddGroup ℂ B
  obtain ⟨l, hl⟩ := i.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi.injective)
  let U : Y →ₗ[ℂ] InductiveTensor A W := (TensorProduct.map l (LinearMap.id (M := W))).comp e.symm.toLinearMap
  let j : InductiveTensor A W →ₗ[ℂ] InductiveTensor B W := inductiveTensorMap i.toLinearMap LinearMap.id
  let m := i.comp M
  let P' : W →L[ℂ] W := ⟨P, continuous_of_finestLocallyConvex D P⟩
  let T : InductiveTensor A W →L[ℂ] InductiveTensor B W :=
    ⟨inductiveTensorMap m.toLinearMap P'.toLinearMap, inductiveTensorMap_continuous m P'⟩
  have hU (a : A) (d : W) : U (e (i a ⊗ₜ[ℂ] d)) = a ⊗ₜ[ℂ] d := by
    change TensorProduct.map l LinearMap.id (e.symm (e (i a ⊗ₜ[ℂ] d))) = _
    exact (congrArg (TensorProduct.map l (LinearMap.id (M := W))) (e.symm_apply_apply _)).trans
      (congrArg (fun x : A ↦ x ⊗ₜ[ℂ] d) (DFunLike.congr_fun hl a))
  have hloc : X ≤ LinearMap.eqLocus (j.comp U) e.symm.toLinearMap := by
    apply hX.trans (Submodule.span_le.mpr ?_)
    rintro _ ⟨⟨a, d⟩, rfl⟩
    change j (U (e (i a ⊗ₜ[ℂ] d))) = e.symm (e _)
    exact (congrArg j (hU a d)).trans (e.symm_apply_apply _).symm
  have hR : Continuous (U.comp X.subtype) := by
    apply sAdelePolarFree_quasiCharacter_tensor_continuous i.toLinearMap hi.isInducing
    exact (e.symm.continuous.comp continuous_subtype_val).congr fun z ↦ (LinearMap.mem_eqLocus.mp (hloc z.property)).symm
  refine ⟨e.toLinearMap.comp (T.toLinearMap.comp U), e.continuous.comp (T.continuous.comp hR), fun a d ↦ ?_⟩
  change e (T (U (e (i a ⊗ₜ[ℂ] d)))) = _
  exact congrArg (fun x : InductiveTensor A W ↦ e (T x)) (hU a d)

/-- An action on a spanning family restricts to its span. The multiplication
identity for evaluations extends from the family by linearity. -/
private theorem sAdelePolarFree_quasiCharacter_span_action
    {A D U Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (X : Submodule ℂ Y) (pure : A → D → Y) (valid : D → Prop)
    (hspan : X = Submodule.span ℂ {z | ∃ a d, valid d ∧ pure a d = z})
    (H : Y →ₗ[ℂ] Y) (hc : Continuous (H.comp X.subtype))
    (m : A → A) (p : D → D) (hp : ∀ d, valid d → valid (p d))
    (ht : ∀ a d, H (pure a d) = pure (m a) (p d))
    (ev : U → (Y →ₗ[ℂ] ℂ)) (b : U → ℂ)
    (he : ∀ a d, valid d → ∀ u, ev u (pure (m a) (p d)) = b u * ev u (pure a d)) :
    ∃ M : X →L[ℂ] X, ∀ f u, ev u (M f).val = b u * ev u f.val := by
  let Z := X.comap H ⊓ ⨅ u, LinearMap.eqLocus ((ev u).comp H) (b u • ev u)
  have hXZ : X ≤ Z := by
    apply hspan.le.trans (Submodule.span_le.mpr ?_)
    rintro z ⟨a, d, hd, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, (Submodule.mem_iInf _).mpr fun u ↦ ?_⟩
    · change H (pure a d) ∈ X
      rw [ht]
      exact hspan.ge (Submodule.subset_span ⟨m a, p d, hp _ hd, rfl⟩)
    · exact (congrArg (ev u) (ht a d)).trans (he a d hd u)
  let op : X →L[ℂ] Y := ⟨H.comp X.subtype, hc⟩
  refine ⟨op.codRestrict X (fun z ↦ (Submodule.mem_inf.mp (hXZ z.property)).1), fun z u ↦ ?_⟩
  exact (Submodule.mem_iInf _).mp (Submodule.mem_inf.mp (hXZ z.property)).2 u

/-- Pull the quotient character back to the product of the archimedean units and
the individual finite unit groups and take its restrictions to the factors. -/
private theorem sAdelePolarFree_quasiCharacter_split (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ (a : QuasiCharacter ((RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)))
      (d : ∀ v : S, QuasiCharacter (v.val.adicCompletion F)ˣ), ∀ g : Aₛˣ,
      ∃ (x : (RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)) (y : (v : S) → (v.val.adicCompletion F)ˣ),
        assemble(r, c, ((fun i ↦ (x.1 i).val, fun j ↦ (x.2 j).val) : ArchCoordinates)) = g.val.1 ∧
        (∀ v, (y v).val = g.val.2 v) ∧ b (QuotientGroup.mk g) = a x * ∏ v, d v (y v) := by
  let E := (RealPlaces → ℝˣ) × (ComplexPlaces → ℂˣ)
  let K := (v : S) → v.val.adicCompletion F
  let e := ContinuousMulEquiv.prodUnits A∞ K
  let eA := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eD := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let α : E →ₜ* ((w : InfinitePlace F) → w.Completionˣ) :=
    { toFun := fun x w ↦ if hw : w.IsReal then
          Units.map (r ⟨w, hw⟩).val.symm.toMonoidHom (x.1 ⟨w, hw⟩)
        else Units.map (c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).val.symm.toMonoidHom
          (x.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)
      map_one' := funext fun w ↦ by split <;> exact map_one _
      map_mul' := fun x y ↦ funext fun w ↦ by
        by_cases hw : w.IsReal <;> simp [hw, Pi.mul_apply] <;> exact map_mul _ _ _
      continuous_toFun := continuous_pi fun w ↦ by
        by_cases hw : w.IsReal
        · simp only [hw, ↓reduceDIte]
          exact (Continuous.units_map _ (sLocalIdelicZFunction_entire_of_polarFree_symm
            (r ⟨w, hw⟩).val (r ⟨w, hw⟩).property)).comp ((continuous_apply _).comp continuous_fst)
        · simp only [hw, ↓reduceDIte]
          exact (Continuous.units_map _ (sLocalIdelicZFunction_entire_of_polarFree_symm
            (c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).val
            (c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).property)).comp
              ((continuous_apply _).comp continuous_snd) }
  let χ : QuasiCharacter Aₛˣ := b.comp ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let χ' : QuasiCharacter (A∞ˣ × Kˣ) := χ.comp ⟨e.symm.toMonoidHom, e.symm.continuous⟩
  let a₀ := (χ'.comp (ContinuousMonoidHom.inl A∞ˣ Kˣ)).comp ⟨eA.symm.toMonoidHom, eA.symm.continuous⟩
  let d₀ := (χ'.comp (ContinuousMonoidHom.inr A∞ˣ Kˣ)).comp ⟨eD.symm.toMonoidHom, eD.symm.continuous⟩
  let d (v : S) := d₀.comp ⟨MonoidHom.mulSingle (fun v : S ↦ (v.val.adicCompletion F)ˣ) v,
    continuous_mulSingle (A := fun v : S ↦ (v.val.adicCompletion F)ˣ) v⟩
  refine ⟨a₀.comp α, d, fun g ↦ ?_⟩
  let t := eA (e g).1
  let x : E := (fun i ↦ Units.map (r i).val.toMonoidHom (t i.val),
    fun j ↦ Units.map (c j).val.toMonoidHom (t j.val))
  let y := eD (e g).2
  have hα : α x = t := by
    funext w
    change (if hw : w.IsReal then Units.map (r ⟨w, hw⟩).val.symm.toMonoidHom (x.1 ⟨w, hw⟩)
      else Units.map (c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩).val.symm.toMonoidHom
        (x.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hw⟩)) = t w
    by_cases hw : w.IsReal <;> simp only [hw, ↓reduceDIte] <;> apply Units.ext <;> simp [x]
  refine ⟨x, y, ?_, fun _ ↦ rfl, ?_⟩
  · funext w
    by_cases hw : w.IsReal <;> simp [x, hw, t, eA, e] <;> rfl
  · have hprod : ∏ v, d v (y v) = d₀ y := by
      change ∏ v, d₀ (Pi.mulSingle v (y v)) = _
      rw [← map_prod, Finset.univ_prod_mulSingle]
    rw [hprod]
    change χ g = a₀ (α x) * d₀ y
    rw [hα]
    change χ g = χ' (eA.symm (eA (e g).1), 1) * χ' (1, eD.symm (eD (e g).2))
    rw [eA.symm_apply_apply, eD.symm_apply_apply, ← map_mul]
    simp only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta]
    exact (congrArg χ (e.symm_apply_apply g)).symm

/-- The additive archimedean test in the chosen real and complex models is its
ordinary Schwartz realization after precomposition with the model equivalence. -/
private theorem sAdelePolarFree_quasiCharacter_archCoordinates (r : RealModels) (c : ComplexModels) :
    ∃ Q : ℬ(A∞) ≃L[ℂ] 𝓢(ArchCoordinates, ℂ), ∀ f x, Q f x = f (Multiplicative.ofAdd (assemble(r, c, x))) := by
  obtain ⟨D, hD⟩ := sAdelePolarFree_mixedCoordinates r c
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  let l := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ D
  let m := SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ D.symm
  let E := ContinuousLinearEquiv.equivOfInverse l m
    (fun f ↦ DFunLike.ext _ _ fun x ↦ congrArg f (D.apply_symm_apply x))
    (fun f ↦ DFunLike.ext _ _ fun x ↦ congrArg f (D.symm_apply_apply x))
  refine ⟨J.symm.trans E, fun f x ↦ ?_⟩
  change J.symm f (D x) = _
  rw [hD, ← hJ, J.apply_symm_apply]

/-- In mixed coordinates the first factors in the spanning tensors are exactly
the image of the embedded flat Schwartz space. -/
private theorem sAdelePolarFree_quasiCharacter_generators (r : RealModels) (c : ComplexModels) :
    let A := archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    ∃ i : A →L[ℂ] ℬ(A∞), IsEmbedding i ∧
      (∀ (s : A) (x : ArchCoordinates), i s (Multiplicative.ofAdd (assemble(r, c, x))) = s.val x) ∧
      sAdelePolarFree S r c = Submodule.span ℂ {z : ℬₛ | ∃ (s : A) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v, g v (Multiplicative.ofAdd 0) = 0) ∧ e (i s ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = z} := by
  intro A e
  let B := ℬ(A∞)
  let Q := (sAdelePolarFree_quasiCharacter_archCoordinates r c).choose
  have hQ := (sAdelePolarFree_quasiCharacter_archCoordinates r c).choose_spec
  let i : A →L[ℂ] B := Q.symm.toContinuousLinearMap.comp A.subtypeL
  have hi : IsEmbedding i := Q.symm.toHomeomorph.isEmbedding.comp IsEmbedding.subtypeVal
  have hiQ (s : A) : Q (i s) = s.val := Q.apply_symm_apply s.val
  have hiEval (s : A) (x : ArchCoordinates) : i s (Multiplicative.ofAdd (assemble(r, c, x))) = s.val x :=
    (hQ (i s) x).symm.trans (congrArg (fun g : 𝓢(ArchCoordinates, ℂ) ↦ g x) (hiQ s))
  have identify (a : B) (s : A) (hs : ∀ x, s.val x = a (Multiplicative.ofAdd (assemble(r, c, x)))) :
      a = i s := Q.injective (by rw [hiQ]; exact DFunLike.ext _ _ fun x ↦ (hQ a x).trans (hs x).symm)
  refine ⟨i, hi, hiEval, (sAdelePolarFree_eq_span_tmul (S := S) r c).trans (congrArg (Submodule.span ℂ) ?_)⟩
  apply Set.ext
  intro z
  constructor
  · rintro ⟨a, g, ⟨s, hs⟩, hg, hz⟩
    exact ⟨s, g, hg, (congrArg (fun t : B ↦ e (t ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) (identify a s hs).symm).trans hz⟩
  · rintro ⟨s, g, hg, hz⟩
    exact ⟨i s, g, ⟨s, fun x ↦ (hiEval s x).symm⟩, hg, hz⟩

/-- Paper: Lemma 5.3.4.2(3), p. 260.
Pointwise multiplication by a continuous quasi-character of the S-ideles is a continuous
complex-linear self-map of the polar-free subspace, and it acts there by multiplication at
the S-ideles. This is the analytic content of the linear homeomorphism of part (3): the
printed proof (p. 261) obtains only that the range is dense and concludes surjectivity, which
is the gap reported on the issue. The homeomorphism is recovered below by applying this
statement to the quasi-character and to its inverse, with no closed-range argument. -/
theorem sAdelePolarFree_quasiCharacter_mul_clm (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ M : ↥(sAdelePolarFree S r c) →L[ℂ] ↥(sAdelePolarFree S r c),
      ∀ f (g : Aₛˣ), (M f).val (Multiplicative.ofAdd g.val) =
        b (QuotientGroup.mk g) * f.val (Multiplicative.ofAdd g.val) := by
  classical
  let A := archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)
  let B := ℬ(A∞)
  let D := ⨂[ℂ] v : S, ℬ(v.val.adicCompletion F)
  let W := FinestLocallyConvex D
  let X := sAdelePolarFree S r c
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  obtain ⟨i, hi, hiEval, hspan⟩ := sAdelePolarFree_quasiCharacter_generators (S := S) r c
  obtain ⟨bA, bv, hsplit⟩ := sAdelePolarFree_quasiCharacter_split r c b
  obtain ⟨M, hM, _⟩ := archimedeanFlatSchwartz_quasiCharacter_mul bA
  choose p hp using fun v : S ↦ sAdelePolarFree_quasiCharacter_finite v.val (bv v)
  let : T2Space B := schwartzBruhat_eval_t2
  let : T2Space A := inferInstanceAs (T2Space (↥(A : Set 𝓢(ArchCoordinates, ℂ))))
  let : PolynormableSpace ℂ A := A.subtype.withSeminorms_induced
    (schwartz_withSeminorms ℂ ArchCoordinates ℂ) |>.toPolynormableSpace
  let pure (a : B) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) : ℬₛ := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))
  have hX : X ≤ Submodule.span ℂ (range fun z : A × W ↦ e (i z.1 ⊗ₜ[ℂ] z.2)) := by
    apply hspan.le.trans (Submodule.span_le.mpr ?_)
    rintro z ⟨s, g, _, hz⟩
    exact Submodule.subset_span ⟨(s, ⨂ₜ[ℂ] v, g v), hz⟩
  obtain ⟨H, hcont, ht⟩ := sAdelePolarFree_quasiCharacter_tensor_action (D := D) e i hi M.toContinuousLinearMap
    (PiTensorProduct.map p) X hX
  have hH (s : A) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      H (pure (i s) g) = pure (i (M s)) (fun v ↦ p v (g v)) := by
    exact (ht s (⨂ₜ[ℂ] v, g v)).trans (congrArg (fun y : W ↦ e (i (M s) ⊗ₜ[ℂ] y)) (PiTensorProduct.map_tprod _ _))
  let ev (u : Aₛˣ) : ℬₛ →ₗ[ℂ] ℂ := (LinearMap.proj (Multiplicative.ofAdd u.val)).comp (schwartzBruhatSubmodule _).subtype
  refine sAdelePolarFree_quasiCharacter_span_action X (fun s ↦ pure (i s))
    (fun g ↦ ∀ v, g v (Multiplicative.ofAdd 0) = 0) hspan H hcont
    (fun s ↦ M s) (fun g v ↦ p v (g v)) (fun g hg v ↦ (hp v _ (hg v)).1) hH ev
    (fun u ↦ b (QuotientGroup.mk u)) ?_
  intro s g hg u
  obtain ⟨x, y, hx, hy, hχ⟩ := hsplit u
  have harch (s : A) : i s (Multiplicative.ofAdd u.val.1) =
      s.val ((fun j ↦ (x.1 j).val, fun j ↦ (x.2 j).val) : ArchCoordinates) :=
    (congrArg (fun z : A∞ ↦ i s (Multiplicative.ofAdd z)) hx.symm).trans (hiEval s _)
  have hfin (v : S) : p v (g v) (Multiplicative.ofAdd (u.val.2 v)) =
      bv v (y v) * g v (Multiplicative.ofAdd (u.val.2 v)) := by
    rw [← hy v]
    exact (hp v _ (hg v)).2 _
  change pure (i (M s)) (fun v ↦ p v (g v)) (Multiplicative.ofAdd u.val) =
    b (QuotientGroup.mk u) * pure (i s) g (Multiplicative.ofAdd u.val)
  have hval (s : A) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      pure (i s) g (Multiplicative.ofAdd u.val) = i s (Multiplicative.ofAdd u.val.1) *
        ∏ v, g v (Multiplicative.ofAdd (u.val.2 v)) := he _ _ _
  rw [hval, hval, harch, harch, hM, hχ]
  simp only [hfin, Finset.prod_mul_distrib]
  ring

/-- Paper: Lemma 5.3.4.2(3), p. 260.
A polar-free test is determined by its values on the units of the S-adelic ring. Every point
of the ring is either a unit or has a zero coordinate: at a zero finite coordinate a
polar-free test vanishes by the finite vanishing condition of (5.3.4.1), and at a zero
archimedean coordinate it vanishes because its archimedean slices are flat. This is what
makes the pointwise constraint of part (3) at the S-ideles determine the operator on the
whole subspace, without the density argument that the printed proof uses. -/
theorem sAdelePolarFree_eq_of_eqOn_units (r : RealModels) (c : ComplexModels) {f g : ℬₛ}
    (hf : f ∈ sAdelePolarFree S r c)
    (hg : g ∈ sAdelePolarFree S r c)
    (h : ∀ u : Aₛˣ, f (Multiplicative.ofAdd (u : Aₛ)) =
      g (Multiplicative.ofAdd (u : Aₛ))) :
    f = g := by
  classical
  -- A polar-free test vanishes at every point with a zero finite coordinate.
  have hfin : ∀ (k : ℬₛ), k ∈ sAdelePolarFree S r c → ∀ (x : Aₛ) (v : S), x.2 v = 0 →
      k (Multiplicative.ofAdd x) = 0 := by
    intro k hk x v hv
    have h1 : k ∈ sAdeleFiniteZeroSchwartz S S := (Submodule.mem_inf.1 hk).1
    simp only [sAdeleFiniteZeroSchwartz, Submodule.mem_iInf, LinearMap.mem_ker] at h1
    exact h1 ⟨x, v, v.2, hv⟩
  -- A polar-free test vanishes on the union of the archimedean coordinate hyperplanes,
  -- because each of its archimedean slices is flat there.
  have hwall : ∀ (k : ℬₛ), k ∈ sAdelePolarFree S r c →
      ∀ (x : Aₛ), (∃ w : InfinitePlace F, x.1 w = 0) → k (Multiplicative.ofAdd x) = 0 := by
    intro k hk x hx
    obtain ⟨h', hh', hfun'⟩ : ∃ h' ∈ archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces),
        ∀ a : ArchCoordinates, (h' : ArchCoordinates → ℂ) a =
          k (Multiplicative.ofAdd (assemble(r, c, a), x.2)) := by
      have h2 := (Submodule.mem_inf.1 hk).2
      simp only [Submodule.mem_iInf] at h2
      have hy := h2 x.2
      simp only [Submodule.mem_comap, Submodule.mem_map] at hy
      obtain ⟨h', hh', hfun'⟩ := hy
      exact ⟨h', hh', fun a => congrFun hfun' a⟩
    -- The model point whose assembled coordinates are those of `x`.
    let a : ArchCoordinates := (fun w : RealPlaces ↦ (r w).val (x.1 w.val),
      fun w : ComplexPlaces ↦ (c w).val (x.1 w.val))
    have ha : assemble(r, c, a) = x.1 := by
      funext w
      by_cases hw : w.IsReal
      · simp only [a, hw, ↓reduceDIte, RingEquiv.symm_apply_apply]
      · simp only [a, hw, ↓reduceDIte, RingEquiv.symm_apply_apply]
    have hwall_a : (∃ i, a.1 i = 0) ∨ (∃ j, a.2 j = 0) := by
      obtain ⟨w, hw⟩ := hx
      by_cases hr : w.IsReal
      · refine Or.inl ⟨⟨w, hr⟩, ?_⟩
        simp only [a]
        rw [hw, map_zero]
      · refine Or.inr ⟨⟨w, InfinitePlace.not_isReal_iff_isComplex.mp hr⟩, ?_⟩
        simp only [a]
        rw [hw, map_zero]
    have h0 : (h' : ArchCoordinates → ℂ) a = 0 := by
      simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker,
        IsLinearMap.mk'_apply] at hh'
      have hz := hh' ⟨a, hwall_a⟩ 0 (fun i => Fin.elim0 i)
      simpa only [iteratedFDeriv_zero_apply] using hz
    have hx' : x = (assemble(r, c, a), x.2) := Prod.ext ha.symm rfl
    rw [hx', ← hfun' a]
    exact h0
  have key : ∀ x : Aₛ, f (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd x) := by
    intro x
    by_cases hz : ∃ v : S, x.2 v = 0
    · obtain ⟨v, hv⟩ := hz
      rw [hfin f hf x v hv, hfin g hg x v hv]
    · push Not at hz
      by_cases hw : ∃ w : InfinitePlace F, x.1 w = 0
      · rw [hwall f hf x hw, hwall g hg x hw]
      · push Not at hw
        -- All coordinates are nonzero, so `x` is a unit of the S-adelic ring.
        let y : Aₛ := ((fun w => (x.1 w)⁻¹), fun v => (x.2 v)⁻¹)
        have hmul : x * y = 1 := by
          refine Prod.ext ?_ ?_
          · funext w
            exact mul_inv_cancel₀ (hw w)
          · funext v
            exact mul_inv_cancel₀ (hz v)
        let u : Aₛˣ := Units.mkOfMulEqOne x y hmul
        have hu : (u : Aₛ) = x := rfl
        rw [← hu]
        exact h u
  exact SchwartzBruhat.ext fun z => key (Multiplicative.toAdd z)

/-- Paper: Lemma 5.3.4.2(3), p. 260.
A continuous quasi-character of the S-ideles trivial on S-units acts on polar-free
functions by pointwise multiplication and defines a linear homeomorphism.
The character is given on the S-idele quotient. -/
theorem sAdelePolarFree_quasiCharacter_mul (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ M : ↥(sAdelePolarFree S r c) ≃L[ℂ] ↥(sAdelePolarFree S r c),
      ∀ f (g : Aₛˣ), (M f).val (Multiplicative.ofAdd g.val) =
        b (QuotientGroup.mk g) * f.val (Multiplicative.ofAdd g.val) := by
  classical
  -- The inverse of multiplication by the character is multiplication by its inverse.
  let bInv : Xₛ := b.comp (ContinuousMonoidHom.inv Jₛ)
  have hInv (g : Jₛ) : bInv g = (b g)⁻¹ := map_inv b g
  have hcancel (g : Jₛ) : bInv g * b g = 1 := by
    rw [hInv, inv_mul_cancel₀]
    exact ((Group.isUnit g).map b).ne_zero
  obtain ⟨M, hM⟩ := sAdelePolarFree_quasiCharacter_mul_clm (F := F) (S := S) r c b
  obtain ⟨N, hN⟩ := sAdelePolarFree_quasiCharacter_mul_clm (F := F) (S := S) r c bInv
  have hleft : LeftInverse N M := by
    intro f
    apply Subtype.ext
    apply sAdelePolarFree_eq_of_eqOn_units r c (N (M f)).2 f.2
    intro g
    rw [hN (M f) g, hM f g, ← mul_assoc, hcancel, one_mul]
  have hright : RightInverse N M := by
    intro f
    apply Subtype.ext
    apply sAdelePolarFree_eq_of_eqOn_units r c (M (N f)).2 f.2
    intro g
    have h : b (QuotientGroup.mk g) * bInv (QuotientGroup.mk g) = 1 := by
      rw [mul_comm]
      exact hcancel _
    rw [hM (N f) g, hN f g, ← mul_assoc, h, one_mul]
  exact ⟨ContinuousLinearEquiv.equivOfInverse M N hleft hright, hM⟩

section PolarFreeConstruction

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous section identifies the group with norm-one elements times positive reals. -/
private def polarFree_logSplit (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) :
    m.toMonoidHom.ker × ℝ≥0ˣ ≃ₜ* G where
  toFun p := p.1.val * τ p.2
  invFun x := (⟨x / τ (m x), by
    change m (x / τ (m x)) = 1
    rw [map_div, hτ, div_self']⟩, m x)
  left_inv p := by
    have hk : m p.1.val = 1 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change p.1.val * τ p.2 / τ (m (p.1.val * τ p.2)) = p.1.val
      rw [map_mul, hk, one_mul, hτ, mul_div_cancel_right]
    · change m (p.1.val * τ p.2) = p.2
      rw [map_mul, hk, one_mul, hτ]
  right_inv x := by
    change x / τ (m x) * τ (m x) = x
    simp [div_eq_mul_inv, mul_assoc]
  map_mul' p q := by
    change (p.1.val * q.1.val) * τ (p.2 * q.2) = _
    rw [map_mul]
    ac_rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd)
  continuous_invFun := by
    simp only [div_eq_mul_inv]
    exact Continuous.prodMk
      ((continuous_id.mul (continuous_inv.comp (τ.continuous.comp m.continuous))).subtype_mk _) m.continuous

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- A nonnegative compact shape on a locally compact group can be made one at its unit. -/
private theorem polarFree_compact_shape :
    ∃ q : SchwartzBruhat G, HasCompactSupport q.val ∧ q 1 = 1 ∧
      ∀ x, q x = ((q x).re : ℂ) ∧ 0 ≤ (q x).re := by
  obtain ⟨q, hq, _, h1⟩ := schwartzBruhat_exists_local_unit (x := (1 : G)) isOpen_univ (mem_univ _)
  have hnorm : ContDiff ℝ (∞ : ℕ∞ω) (fun z : ℂ ↦ Complex.normSq z) :=
    (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  obtain ⟨Q, hQ⟩ := compact_schwartzBruhat_comp hq
    (φ := fun z ↦ (Complex.normSq z : ℂ)) (Complex.ofRealCLM.contDiff.comp hnorm) (by simp)
  have hQx (x : G) : Q x = (Complex.normSq (q x) : ℂ) := congrFun hQ x
  have hq1 : q 1 = 1 := h1.self_of_nhds
  refine ⟨Q, ?_, by simp [hQx, hq1], fun x ↦ ?_⟩
  · rw [hQ]
    exact hq.comp_left (by simp)
  · simp [hQx, Complex.normSq_nonneg]

/-- Decompose the log of a second positive character on a norm section. -/
private theorem polarFree_section_weight (w : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) :
    ∃ a : ℝ, ∀ t : ℝ≥0ˣ, ((w (τ t)).val : ℝ) = Real.exp (a * Real.log (t.val : ℝ)) := by
  let inclusion : ℝ≥0ˣ →ₜ* ℂ :=
    ⟨Complex.ofRealHom.toMonoidHom.comp
      (NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0)),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp Units.continuous_val)⟩
  let c := inclusion.comp (w.comp τ)
  obtain ⟨a, ha, _⟩ := existsUnique_complexPower c
  refine ⟨a.re, fun t ↦ ?_⟩
  have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hwt : 0 < ((w (τ t)).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have h := congrArg norm (ha t)
  change ‖(((w (τ t)).val : ℝ) : ℂ)‖ = ‖((t.val : ℝ) : ℂ) ^ a‖ at h
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwt,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Real.rpow_def_of_pos ht] at h
  simpa only [mul_comm] using h

/-- On a compactly supported shape, a positive weight is implemented by a
compact smooth multiplier in logarithmic coordinates. -/
private theorem polarFree_weight_shape (w : G →ₜ* ℝ≥0ˣ) (q : SchwartzBruhat G)
    (hq : HasCompactSupport q.val) :
    ∃ Q : SchwartzBruhat G, ∀ x, Q x = (((w x).val : ℝ) : ℂ) * q x := by
  let L (x : G) := Real.log ((w x).val : ℝ)
  have hp (x : G) : 0 < ((w x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp w.continuous)).log fun x ↦ (hp x).ne'
  obtain ⟨R, hR, hbound⟩ := (hq.image hL).isBounded.exists_pos_norm_le
  let b : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let θ (t : ℝ) : ℂ := (b t * Real.exp t : ℝ)
  have hS : HasCompactSupport (fun t : ℝ ↦ b t * Real.exp t) := b.hasCompactSupport.mul_right
  have hs : HasCompactSupport θ := hS.comp_left Complex.ofReal_zero
  have hc : ContDiff ℝ (∞ : ℕ∞ω) θ :=
    Complex.ofRealCLM.contDiff.comp (b.contDiff.mul Real.contDiff_exp)
  have hb (j : ℕ) : ∃ D, ∀ t, ‖iteratedFDeriv ℝ j θ t‖ ≤ D :=
    (hc.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (hs.iteratedFDeriv j)
  let Q : SchwartzBruhat G := ⟨_, logModulation_mul_mem_schwartzBruhat w hc hb q.property⟩
  refine ⟨Q, fun x ↦ ?_⟩
  change θ (L x) * q x = _
  by_cases hx : x ∈ tsupport q.val
  · have hbx : b (L x) = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound (L x) ⟨x, hx, rfl⟩)
    simp only [θ, hbx, one_mul, L, Real.exp_log (hp x)]
  · simp only [show q x = 0 from image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- A tensor of a compact norm-one shape and an exponential-decay profile
remains Schwartz after multiplying by any positive continuous character. -/
private theorem polarFree_split_product (m w : G →ₜ* ℝ≥0ˣ)
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (q : SchwartzBruhat m.toMonoidHom.ker) (hq : HasCompactSupport q.val)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ H : SchwartzBruhat G, ∀ (u : m.toMonoidHom.ker) (t : ℝ≥0ˣ),
      H (u.val * τ t) = (((w (u.val * τ t)).val : ℝ) : ℂ) * (q u * φ.val (Real.log (t.val : ℝ))) := by
  have hK : IsClosed (m.toMonoidHom.ker : Set G) := isClosed_singleton.preimage m.continuous
  let : LocallyCompactSpace m.toMonoidHom.ker := hK.locallyCompactSpace
  let : SecondCountableTopology m.toMonoidHom.ker :=
    inferInstanceAs (SecondCountableTopology (m.toMonoidHom.ker : Set G))
  let wk : m.toMonoidHom.ker →ₜ* ℝ≥0ˣ :=
    w.comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩
  obtain ⟨Q, hQ⟩ := polarFree_weight_shape wk q hq
  obtain ⟨a, ha⟩ := polarFree_section_weight w τ
  obtain ⟨P, hP⟩ := split_schwartz_product (polarFree_logSplit m τ hτ)
  let v := logExponentialDecayTwist univ ⟨a, mem_univ _⟩ φ
  refine ⟨P (Q ⊗ₜ[ℂ] v), fun u t ↦ ?_⟩
  refine (hP Q v u t).trans ?_
  have hwv : v (Real.log (t.val : ℝ)) =
      (Real.exp (a * Real.log (t.val : ℝ)) : ℂ) * φ.val (Real.log (t.val : ℝ)) :=
    logExponentialDecayTwist_apply univ ⟨a, mem_univ _⟩ φ _
  have hwv' : v (Real.log (t.val : ℝ)) =
      (((w (τ t)).val : ℝ) : ℂ) * φ.val (Real.log (t.val : ℝ)) :=
    hwv.trans (congrArg (fun x : ℝ ↦ (x : ℂ) * φ.val (Real.log (t.val : ℝ))) (ha t).symm)
  refine (congrArg₂ (· * ·) (hQ u) hwv').trans ?_
  change ((((w u.val).val : ℝ) : ℂ) * q u) * ((((w (τ t)).val : ℝ) : ℂ) * φ.val _) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul]
  ring

section ArchimedeanWeights

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "ArchU" => ((ι → ℝˣ) × (κ → ℂˣ))

private def polarFree_normWeight {R : Type*} [NormedField R] (d : ℕ) (a : ℝ) :
    Rˣ →ₜ* ℝ≥0ˣ :=
  let N : Rˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom
  { toMonoidHom := (Units.map (NNReal.rpowMonoidHom a)).comp (N ^ d)
    continuous_toFun := by
      apply Units.isEmbedding_val₀.continuous_iff.mpr
      change Continuous (fun x : Rˣ ↦ (‖x.val‖₊ ^ d) ^ a)
      have hc : Continuous (fun u : Rˣ ↦ ‖u.val‖₊ ^ d) :=
        (continuous_nnNorm.comp Units.continuous_val).pow d
      refine continuous_iff_continuousAt.mpr fun x ↦ ?_
      have hpow : ContinuousAt (fun x : ℝ≥0 ↦ x ^ a) (‖x.val‖₊ ^ d) :=
        NNReal.continuousAt_rpow_const (Or.inl (pow_ne_zero d (nnNorm_ne_zero_iff.mpr x.ne_zero)))
      exact hpow.comp (f := fun u : Rˣ ↦ ‖u.val‖₊ ^ d) (hc.continuousAt (x := x)) }

private theorem polarFree_normWeight_apply {R : Type*} [NormedField R]
    (d : ℕ) (a : ℝ) (u : Rˣ) :
    ((polarFree_normWeight d a u).val : ℝ) = (‖u.val‖ ^ d) ^ a := by
  change (((‖u.val‖₊ ^ d) ^ a : ℝ≥0) : ℝ) = _
  rw [NNReal.coe_rpow, NNReal.coe_pow]
  rfl

private def polarFree_archWeight (a : (ι → ℝ) × (κ → ℝ)) : ArchU →ₜ* ℝ≥0ˣ :=
  { toFun := fun u ↦ (∏ i, polarFree_normWeight 1 (a.1 i) (u.1 i)) *
      ∏ j, polarFree_normWeight 2 (a.2 j) (u.2 j)
    map_one' := by simp
    map_mul' := fun x y ↦ by
      simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
      ac_rfl
    continuous_toFun :=
      (continuous_finsetProd _ fun i _ ↦
        (polarFree_normWeight 1 (a.1 i)).continuous.comp ((continuous_apply i).comp continuous_fst)).mul
        (continuous_finsetProd _ fun j _ ↦
          (polarFree_normWeight 2 (a.2 j)).continuous.comp ((continuous_apply j).comp continuous_snd)) }

private theorem polarFree_archWeight_apply (a : (ι → ℝ) × (κ → ℝ)) (u : ArchU) :
    ((polarFree_archWeight a u).val : ℝ) =
      (∏ i, ‖(u.1 i).val‖ ^ a.1 i) * ∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ a.2 j := by
  change (((∏ i, polarFree_normWeight 1 (a.1 i) (u.1 i)) *
    ∏ j, polarFree_normWeight 2 (a.2 j) (u.2 j)).val : ℝ) = _
  simp only [Units.val_mul, NNReal.coe_mul, Units.coe_prod, NNReal.coe_prod,
    polarFree_normWeight_apply, pow_one]

/-- Inserting a compact shape into all weighted twists gives an archimedean
flat Schwartz extension. -/
private theorem polarFree_arch_profile (m : ArchU →ₜ* ℝ≥0ˣ)
    (τ : ℝ≥0ˣ →ₜ* ArchU) (hτ : RightInverse τ m)
    (q : SchwartzBruhat m.toMonoidHom.ker) (hq : HasCompactSupport q.val)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : archimedeanFlatSchwartz (ι := ι) (κ := κ),
      ∀ (u : m.toMonoidHom.ker) (t : ℝ≥0ˣ),
        f.val (fun i ↦ ((u.val * τ t).1 i).val, fun j ↦ ((u.val * τ t).2 j).val) =
          q u * φ.val (Real.log (t.val : ℝ)) := by
  let : LocallyCompactSpace ℝˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : LocallyCompactSpace ℂˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  let D := polarFree_logSplit m τ hτ
  let H (x : ArchU) := q (D.symm x).1 * φ.val (Real.log (((D.symm x).2).val : ℝ))
  have hH (u : m.toMonoidHom.ker) (t : ℝ≥0ˣ) :
      H (u.val * τ t) = q u * φ.val (Real.log (t.val : ℝ)) := by
    change q (D.symm (D (u,t))).1 * φ.val (Real.log (((D.symm (D (u,t))).2).val : ℝ)) = _
    rw [D.symm_apply_apply]
  have hw : H ∈ archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) univ := by
    apply (Submodule.mem_iInf _).2
    intro a
    let w := polarFree_archWeight (fun i ↦ (a.1 i : ℝ), fun j ↦ (a.2 j : ℝ))
    obtain ⟨h, hh⟩ := polarFree_split_product m w τ hτ q hq φ
    apply Submodule.mem_comap.2
    have heq (x : ArchU) : h x = ((w x).val : ℝ) • H x := by
      obtain ⟨p, rfl⟩ := D.surjective x
      rw [show D p = p.1.val * τ p.2 from rfl, hH, hh, Complex.real_smul]
    convert h.property using 1
    funext x
    rw [heq, Complex.real_smul, show ((w x).val : ℝ) = _ from polarFree_archWeight_apply _ _]
    push_cast
    rfl
  let X : ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) univ := ⟨H, hw⟩
  obtain ⟨E, hE⟩ := archimedeanFlatSchwartz_restrict_equiv (ι := ι) (κ := κ)
  refine ⟨E.symm X, fun u t ↦ ?_⟩
  exact ((hE (E.symm X) (u.val * τ t)).symm.trans
    (congrArg (fun z : ArchimedeanWeightedSchwartz univ ↦ z.val (u.val * τ t))
      (E.apply_symm_apply X))).trans (hH u t)

end ArchimedeanWeights

section PolarFreeArithmetic
variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}
local notation "I" => (SAdeleRing F S)ˣ
local notation "finEval(" v ")" =>
  Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom

/-- On finite integer units, the S-norm is the product of the real radii and squared complex radii. -/
private theorem thetaFiber_norm_of_finiteUnits (g : I)
    (hg : ∀ v : S, finEval(v) g ∈ (v.val.adicCompletionIntegers F).units) :
    ((sIdeleNorm F S g).val : ℝ) =
      (∏ i : {w : InfinitePlace F // w.IsReal}, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).1 i‖) *
        ∏ j : {w : InfinitePlace F // w.IsComplex}, ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1).2 j‖ ^ 2 := by
  classical
  have hfin (v : S) : ‖g.val.2 v‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (a := finEval(v) g)).mp (hg v))
  let ev : (I →* ℝ≥0ˣ) →* ℝ := NNReal.toRealHom.toMonoidHom.comp
    ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
  have hN : ((sIdeleNorm F S g).val : ℝ) =
      (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) * ∏ v : S, ‖g.val.2 v‖ := by
    change ev (sIdeleNorm F S) = _
    simp only [sIdeleNorm, map_mul, map_prod, map_pow]
    rfl
  rw [hN, Finset.prod_eq_one fun v _ ↦ hfin v, mul_one, InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [InfinitePlace.mult_isReal i, pow_one, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal i.property).norm_map_of_map_zero
      (map_zero _) _).symm
  · apply Finset.prod_congr rfl
    intro j _
    rw [InfinitePlace.mult_isComplex j, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact congrArg (· ^ 2) ((InfinitePlace.Completion.isometry_extensionEmbedding j.val).norm_map_of_map_zero
      (map_zero _) _).symm

/-- The section through a single infinite place changes no finite coordinates. -/
private theorem thetaFiber_exists_archSection (w : InfinitePlace F) :
    ∃ σ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ, RightInverse σ (sIdeleNorm F S) ∧
      ∀ (t : ℝ≥0ˣ) (v : S), finEval(v) (σ t) = 1 := by
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let σ : ℝ≥0ˣ →ₜ* I := ⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩
  refine ⟨σ, fun t ↦ ?_, fun t v ↦ Units.ext rfl⟩
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

local notation "NormRealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "NormComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "MixedUnits" => ((NormRealPlaces → ℝˣ) × (NormComplexPlaces → ℂˣ))

/-- Take the real and complex unit coordinates of the archimedean part. -/
private def polarFree_archProjection : I →ₜ* MixedUnits := by
  let ev (w : InfinitePlace F) := (Pi.evalRingHom _ w).comp
    (RingHom.fst (InfiniteAdeleRing F) (∀ v : S, v.val.adicCompletion F))
  let a (i : NormRealPlaces) := (InfinitePlace.Completion.extensionEmbeddingOfIsReal i.property).comp (ev i.val)
  let b (j : NormComplexPlaces) := (InfinitePlace.Completion.extensionEmbedding j.val).comp (ev j.val)
  let p := (MonoidHom.pi fun i ↦ Units.map (a i).toMonoidHom).prod
    (MonoidHom.pi fun j ↦ Units.map (b j).toMonoidHom)
  refine ⟨p, Continuous.prodMk (continuous_pi fun i ↦ ?_) (continuous_pi fun j ↦ ?_)⟩
  · have hc : Continuous (a i) := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal i.property).continuous.comp
      ((continuous_apply i.val).comp continuous_fst)
    exact hc.units_map _
  · have hc : Continuous (b j) := (InfinitePlace.Completion.isometry_extensionEmbedding j.val).continuous.comp
      ((continuous_apply j.val).comp continuous_fst)
    exact hc.units_map _

/-- Forgetting the units gives exactly the canonical mixed coordinates. -/
private theorem polarFree_archProjection_val (g : I) :
    ((fun i ↦ ((polarFree_archProjection (F := F) (S := S) g).1 i).val),
      fun j ↦ ((polarFree_archProjection (F := F) (S := S) g).2 j).val) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.1 := rfl

private theorem polarFree_archProjection_norm (g : I)
    (hg : ∀ v : S, finEval(v) g ∈ (v.val.adicCompletionIntegers F).units) :
    ((sIdeleNorm F S g).val : ℝ) =
      (∏ i, ‖((polarFree_archProjection (F := F) (S := S) g).1 i).val‖) *
        ∏ j, ‖((polarFree_archProjection (F := F) (S := S) g).2 j).val‖ ^ 2 :=
  thetaFiber_norm_of_finiteUnits g hg


/-- On finite integer units the mixed archimedean weight of exponent one is the full S-norm. -/
private theorem polarFree_archWeight_norm (g : I)
    (hg : ∀ v : S, finEval(v) g ∈ (v.val.adicCompletionIntegers F).units) :
    polarFree_archWeight ((fun _ : NormRealPlaces ↦ 1), (fun _ : NormComplexPlaces ↦ 1))
      (polarFree_archProjection (F := F) (S := S) g) = sIdeleNorm F S g := by
  apply Units.ext
  apply NNReal.coe_injective
  rw [polarFree_archWeight_apply, polarFree_archProjection_norm g hg]
  simp only [Real.rpow_one]


end PolarFreeArithmetic

section PolarFreeFinite

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "PFR" => {w : InfinitePlace F // w.IsReal}
local notation "PFC" => {w : InfinitePlace F // w.IsComplex}
local notation "PFA" => ((PFR → ℝ) × (PFC → ℂ))
local notation "PFV" => HeightOneSpectrum (𝓞 F)
local notation "PFM" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "PFI" => (SAdeleRing F S)ˣ
local notation "pfEval(" v ")" =>
  Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom
local notation "pfUnits(" g ")" => (∀ v : S, pfEval(v) g ∈ (v.val.adicCompletionIntegers F).units)

private noncomputable def polarFree_realModel (w : PFR) :
    {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
  ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.2,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph.isHomeomorph⟩

private noncomputable def polarFree_complexModel (w : PFC) :
    {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
  ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.2).toHomeomorph.isHomeomorph⟩

/-- The indicator of integer units has a zero extension at a finite place. -/
private theorem polarFree_finite_indicator (v : PFV) :
    ∃ f : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) =
        if u ∈ (v.adicCompletionIntegers F).units then 1 else 0 := by
  classical
  let U : Set (v.adicCompletion F)ˣ := (v.adicCompletionIntegers F).units
  have ho : IsOpen U := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hc : IsCompact U :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let f (u : (v.adicCompletion F)ˣ) : ℂ := if u ∈ U then 1 else 0
  have hl : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_exists_open]
    intro u
    by_cases h : u ∈ U
    · refine ⟨U, ho, h, fun w hw ↦ ?_⟩
      simp only [f, ite_eq_left h, ite_eq_left hw]
    · refine ⟨Uᶜ, hc.isClosed.isOpen_compl, h, fun w hw ↦ ?_⟩
      simp only [f, ite_eq_right h, ite_eq_right (show w ∉ U from hw)]
  have hs : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hc (fun x hx ↦ by
    by_contra h
    exact hx (ite_eq_right h))
  exact (exists_finitePlaceSchwartz_zeroExtension_iff v f).2 ⟨hl, hs⟩

/-- A flat archimedean profile times the finite integer-unit indicators is polar-free. -/
private theorem polarFree_lift_archimedean
    (a : archimedeanFlatSchwartz (ι := PFR) (κ := PFC)) :
    ∃ f : sAdelePolarFree S polarFree_realModel polarFree_complexModel, ∀ g : PFI,
      f.val (Multiplicative.ofAdd g.val) = if pfUnits(g) then a.val (PFM g.val.1) else 0 := by
  classical
  let A : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨_, (mem_archimedeanSchwartzBruhat_iff (fun x ↦ a.val (PFM x))).2 ⟨a.val, fun _ ↦ rfl⟩⟩
  choose b hb0 hb using (fun v : S ↦ polarFree_finite_indicator v.val)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let f := e (A ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))
  have happly (x : SAdeleRing F S) :
      f (Multiplicative.ofAdd x) = a.val (PFM x.1) * ∏ v : S, b v (Multiplicative.ofAdd (x.2 v)) :=
    he A b x
  have hmem : f ∈ sAdelePolarFree S polarFree_realModel polarFree_complexModel := by
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · apply (Submodule.mem_iInf _).2
      intro x
      obtain ⟨v, _, hv⟩ := x.property
      change f (Multiplicative.ofAdd x.val) = 0
      rw [happly, Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, hb0]), mul_zero]
    · apply (Submodule.mem_iInf _).2
      intro y
      apply Submodule.mem_comap.2
      let c : ℂ := ∏ v : S, b v (Multiplicative.ofAdd (y v))
      refine Submodule.mem_map.2 ⟨c • a.val, Submodule.smul_mem _ _ a.property, ?_⟩
      funext x
      let X : InfiniteAdeleRing F := fun w ↦ if h : w.IsReal then (polarFree_realModel ⟨w,h⟩).val.symm (x.1 ⟨w,h⟩)
        else (polarFree_complexModel ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩).val.symm
          (x.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩)
      change c * a.val x = f (Multiplicative.ofAdd (X,y))
      have hx : PFM X = x := by
        apply Prod.ext
        · funext i
          rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          change (polarFree_realModel i).val (X i.val) = _
          simp only [X, i.property, ↓reduceDIte, RingEquiv.apply_symm_apply]
        · funext j
          rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
          change (polarFree_complexModel j).val (X j.val) = _
          have hj : ¬ j.val.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr j.property
          simp only [X, hj, ↓reduceDIte, RingEquiv.apply_symm_apply]
      rw [happly, show (X,y).1 = X from rfl, hx, mul_comm]
  refine ⟨⟨f,hmem⟩, fun g ↦ ?_⟩
  change f (Multiplicative.ofAdd g.val) = _
  rw [happly]
  have hval (v : S) :
      b v (Multiplicative.ofAdd (g.val.2 v)) =
        if pfEval(v) g ∈ (v.val.adicCompletionIntegers F).units then 1 else 0 := by
    let x : (v.val.adicCompletion F)ˣ := pfEval(v) g
    have hx : x.val = g.val.2 v := rfl
    rw [← hx]
    exact hb v x
  by_cases hg : pfUnits(g)
  · simp only [ite_eq_left hg, hval, ite_eq_left (hg _), Finset.prod_const_one, mul_one]
  · obtain ⟨v,hv⟩ := not_forall.mp hg
    rw [ite_eq_right hg, Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hval, ite_eq_right hv]), mul_zero]

end PolarFreeFinite


section ThetaFiber4249
variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "I" => (SAdeleRing F S)ˣ
local notation "J" => SIdeleQuotient F S
local notation "N" => (sIdeleNorm F S).ker
local notation "K" => (sIdeleQuotientNorm F S).ker
local notation "B" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "U" => ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ
local notation "D" => MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
  (Subring.subtype (integralAdelesOutside F S))))) (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))
local notation "Ev(" f ", " x ")" => (f : B) (Multiplicative.ofAdd (x : I).val)
local notation "θ(" f ")" => sLocalAdelicThetaOnClasses F S f
local notation "T(" f ")" => sLocalHomogeneousAdelicThetaLinearMap F S (1 : PontryaginDual K) f
local notation "ell(" t ")" => Real.log (((t : ℝ≥0ˣ).val : ℝ))

-- BEGIN THETA FIBER
/-- The diagonal S-units preserve each norm fiber of the S-ideles. -/
private theorem thetaFiber_unit_norm (ξ : U) : sIdeleNorm F S (D ξ) = 1 :=
  (sIdeleNorm_spec F S).2 ⟨ξ, rfl⟩

/-- Pull the radial factor through the S-unit sum. -/
private theorem thetaFiber_local_factor (σ : ℝ≥0ˣ → I) (φ : ℝ → ℂ) (f b : B)
    (hf : ∀ (t : ℝ≥0ˣ) (u : N), Ev(f, σ t * u.val) = φ ell(t) * Ev(b, u.val))
    (t : ℝ≥0ˣ) (h : K) :
    θ(f) (QuotientGroup.mk (σ t) * h.val) = φ ell(t) * θ(b) h.val := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective h.val
  have hnv : sIdeleNorm F S v = 1 := by
    rw [← sIdeleQuotientNorm_mk, hv]
    exact h.property
  rw [← hv, ← QuotientGroup.mk_mul, sLocalAdelicThetaOnClasses_mk,
    sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply, sLocalAdelicTheta_apply,
    ← tsum_mul_left]
  apply tsum_congr
  intro ξ
  have hu : D ξ * v ∈ N := by
    change sIdeleNorm F S (D ξ * v) = 1
    rw [map_mul, thetaFiber_unit_norm, hnv, one_mul]
  exact (congrArg (fun x : I ↦ Ev(f, x)) (mul_left_comm (D ξ) (σ t) v)).trans
    (hf t ⟨_, hu⟩)

/-- Norm-one Haar averaging removes the dependence on the representative of the fiber. -/
private theorem thetaFiber_average (σ : ℝ≥0ˣ → I) (hσ : RightInverse σ (sIdeleNorm F S))
    (φ : ℝ → ℂ) (f b : B)
    (hf : ∀ (t : ℝ≥0ˣ) (u : N), Ev(f, σ t * u.val) = φ ell(t) * Ev(b, u.val))
    (g : J) : T(f) g = φ ell(sIdeleQuotientNorm F S g) * T(b) 1 := by
  let t := sIdeleQuotientNorm F S g
  let p : J := QuotientGroup.mk (σ t)
  have hp : sIdeleQuotientNorm F S p = t := hσ t
  let u : K := ⟨g / p, by change sIdeleQuotientNorm F S (g / p) = 1; rw [map_div, hp, div_self']⟩
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hval (h : K) : g * h.val = p * (u * h).val := by
    change g * h.val = p * (g / p * h.val)
    exact (congrArg (fun v : J ↦ v * h.val) (mul_div_cancel p g).symm).trans (mul_assoc p (g/p) h.val)
  change T(f) g = φ ell(t) * T(b) 1
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one]
  have h1 (v : K) : (1 : J) * v.val = v.val := one_mul (v.val : J)
  simp_rw [h1]
  calc
    _ = ∫ h : K, φ ell(t) * θ(b) (u * h).val ∂μ := integral_congr_ae (.of_forall fun h ↦
      (congrArg (θ(f)) (hval h)).trans (thetaFiber_local_factor σ φ f b hf t (u * h)))
    _ = _ := by
      rw [integral_const_mul]
      exact congrArg (φ ell(t) * ·) (integral_mul_left_eq_self (μ := μ) (fun h : K ↦ θ(b) h.val) u)

/-- A test nonnegative on the norm-one fiber and positive at its identity has
strictly positive real homogeneous theta value at the identity. -/
private theorem thetaFiber_positive (b : B)
    (hn : ∀ x : N, 0 ≤ (Ev(b, x.val)).re) (hp : 0 < (Ev(b, (1 : I))).re) :
    0 < (T(b) 1).re := by
  classical
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let Z (h : K) := θ(b) h.val
  have hc : Continuous Z := (θ(b)).continuous.comp continuous_subtype_val
  have lower (v : I) (hv : v ∈ N) : (Ev(b, v)).re ≤ (θ(b) (QuotientGroup.mk v)).re := by
    rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
    let terms (ξ : U) := Ev(b, D ξ * v)
    have hs : Summable terms := ((sLocalAdelicTheta_summableUniformlyOn_norm F S b {v}
      isCompact_singleton).summable (by rfl)).of_norm
    change _ ≤ (∑' ξ, terms ξ).re
    rw [Complex.re_tsum hs]
    have hnV (ξ : U) : 0 ≤ (terms ξ).re := hn ⟨D ξ * v, by
      change sIdeleNorm F S (D ξ * v) = 1
      rw [map_mul, thetaFiber_unit_norm, show sIdeleNorm F S v = 1 from hv, one_mul]⟩
    have h := (Complex.hasSum_re hs.hasSum).summable.le_tsum (1 : U) (fun i _ ↦ hnV i)
    simpa only [terms, map_one, one_mul] using h
  have hZ (h : K) : 0 ≤ (Z h).re := by
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective h.val
    have hnv : v ∈ N := by change sIdeleNorm F S v = 1; rw [← sIdeleQuotientNorm_mk, hv]; exact h.property
    exact ((hn ⟨v, hnv⟩).trans (lower v hnv)).trans_eq (congrArg (fun x : J ↦ (θ(b) x).re) hv)
  have h1 : 0 < (Z 1).re := hp.trans_le (lower 1 (Subgroup.one_mem _))
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one]
  have hbase (v : K) : (1 : J) * v.val = v.val := one_mul (v.val : J)
  simp_rw [hbase]
  change 0 < (∫ h, Z h ∂μ).re
  have hi : Integrable Z μ := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact ((Complex.continuous_re.comp hc).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (μ := μ) (HasCompactSupport.of_compactSpace _) hZ (x := 1) h1.ne').trans_eq (integral_re hi)

/-- A common nonnegative fiber profile produces a positive normalization
independent of the radial test. -/
private theorem thetaFiber_normalize (σ : ℝ≥0ˣ →* I) (hσ : RightInverse σ (sIdeleNorm F S))
    (φ β : ℝ → ℂ) (hβ : β 0 = 1) (q : N → ℝ) (hq : ∀ u, 0 ≤ q u) (hq₁ : 0 < q 1)
    (f b : B) (hf : ∀ (t : ℝ≥0ˣ) (u : N), Ev(f, σ t * u.val) = φ ell(t) * (q u : ℂ))
    (hb : ∀ (t : ℝ≥0ˣ) (u : N), Ev(b, σ t * u.val) = β ell(t) * (q u : ℂ)) :
    (∀ g : J, T(f) g = φ ell(sIdeleQuotientNorm F S g) * T(b) 1) ∧ 0 < (T(b) 1).re := by
  have hunit (u : N) : Ev(b, u.val) = (q u : ℂ) := by
    simpa only [map_one, one_mul, Units.val_one, NNReal.coe_one, Real.log_one, hβ] using hb 1 u
  exact ⟨thetaFiber_average σ hσ φ f b (fun t u ↦ (hf t u).trans (congrArg (φ ell(t) * ·) (hunit u).symm)),
    thetaFiber_positive b (fun u ↦ by rw [hunit]; exact hq u)
      (hq₁.trans_eq (congrArg Complex.re (hunit (1 : N))).symm)⟩

end ThetaFiber4249

section PolarFreeAssembly

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "AI" => (SAdeleRing F S)ˣ
local notation "AM" => (InfiniteAdeleRing.ringEquiv_mixedSpace F)
local notation "AR" => {w : InfinitePlace F // w.IsReal}
local notation "AC" => {w : InfinitePlace F // w.IsComplex}
local notation "AU" => ((AR → ℝˣ) × (AC → ℂˣ))
local notation "RN" => sIdeleNorm F S
local notation "EvS(" f ", " x ")" =>
  (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (Multiplicative.ofAdd (x : AI).val)
local notation "ThetaS(" f ")" =>
  sLocalHomogeneousAdelicThetaLinearMap F S (1 : PontryaginDual (sIdeleQuotientNorm F S).ker) f
local notation "logPos(" t ")" => Real.log (((t : ℝ≥0ˣ).val : ℝ))
local notation "fiEval(" v ")" =>
  Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom
local notation "unitsSupport(" g ")" =>
  (∀ v : S, fiEval(v) g ∈ (v.val.adicCompletionIntegers F).units)

/-- Compactly supported unit factors separate the archimedean lift from the finite
coordinates, which contribute norm one on the support. -/
private theorem polarFree_assemble_profile
    (r : (w : AR) → {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : AC) → {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (m : AU →ₜ* ℝ≥0ˣ) (π : AI →ₜ* AU) (σ : ℝ≥0ˣ →ₜ* AI)
    (hσ : RightInverse σ RN)
    (hσfin : ∀ (t : ℝ≥0ˣ) (v : S), fiEval(v) (σ t) = 1)
    (hπ : ∀ g : AI, (fun i ↦ ((π g).1 i).val, fun j ↦ ((π g).2 j).val) = AM g.val.1)
    (hnorm : ∀ g : AI, unitsSupport(g) → m (π g) = RN g)
    (lift : ∀ a : archimedeanFlatSchwartz (ι := AR) (κ := AC),
      ∃ f : sAdelePolarFree S r c, ∀ g : AI,
        EvS(f.val, g) = if unitsSupport(g) then a.val (AM g.val.1) else 0)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : SIdeleQuotient F S,
      ThetaS(f.val) g = φ.val logPos(sIdeleQuotientNorm F S g) := by
  classical
  let τ := π.comp σ
  have hτ : RightInverse τ m := fun t ↦
    (hnorm (σ t) (fun v ↦ by rw [hσfin]; exact Submonoid.one_mem _)).trans (hσ t)
  let : LocallyCompactSpace ℝˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : LocallyCompactSpace ℂˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology ℝˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hclosed : IsClosed (m.toMonoidHom.ker : Set AU) := isClosed_singleton.preimage m.continuous
  let : LocallyCompactSpace m.toMonoidHom.ker := hclosed.locallyCompactSpace
  let : SecondCountableTopology m.toMonoidHom.ker :=
    inferInstanceAs (SecondCountableTopology (m.toMonoidHom.ker : Set AU))
  with_reducible refine (polarFree_compact_shape (G := m.toMonoidHom.ker)).elim fun qA hshape ↦ ?_
  obtain ⟨hqA, hqA1, hqApos⟩ := hshape
  let ku (u : (RN).ker) (hu : unitsSupport(u.val)) : m.toMonoidHom.ker :=
    ⟨π u.val, (hnorm u.val hu).trans u.property⟩
  let q (u : (RN).ker) : ℝ := if hu : unitsSupport(u.val) then (qA (ku u hu)).re else 0
  have hq (u : (RN).ker) : 0 ≤ q u := by
    dsimp only [q]
    split
    · exact (hqApos _).2
    · exact le_rfl
  have hq₁ : 0 < q 1 := by
    have hu : unitsSupport((1 : AI)) := fun v ↦ by rw [map_one]; exact Submonoid.one_mem _
    have hku : ku (1 : (RN).ker) hu = 1 := Subtype.ext (map_one π)
    dsimp only [q, Subgroup.coe_one]
    rw [dite_eq_left hu, hku, hqA1, Complex.one_re]
    exact zero_lt_one
  have hfin (t : ℝ≥0ˣ) (g : AI) : unitsSupport(σ t * g) ↔ unitsSupport(g) := by
    have he (v : S) : fiEval(v) (σ t * g) = fiEval(v) g := by rw [map_mul, hσfin, one_mul]
    simp only [he]
  have htest (ψ : PositiveRealExponentialDecay univ) :
      ∃ f : sAdelePolarFree S r c, ∀ (t : ℝ≥0ˣ) (u : (RN).ker),
        EvS(f.val, σ t * u.val) = ψ.val logPos(t) * (q u : ℂ) := by
    with_reducible refine (polarFree_arch_profile m τ hτ qA hqA ψ).elim fun a ha ↦ ?_
    with_reducible refine (lift a).elim fun f hf ↦ ?_
    refine ⟨f, fun t u ↦ ?_⟩
    rw [hf, if_congr (hfin t u.val) rfl rfl]
    by_cases hu : unitsSupport(u.val)
    · rw [ite_eq_left hu, show q u = (qA (ku u hu)).re from dite_eq_left hu]
      have he : π (σ t * u.val) = (ku u hu).val * τ t := by
        rw [map_mul, mul_comm]
        rfl
      rw [← hπ, he, ha]
      exact (congrArg (· * ψ.val logPos(t)) (hqApos (ku u hu)).1).trans (mul_comm _ _)
    · rw [ite_eq_right hu, show q u = 0 from dite_eq_right hu, Complex.ofReal_zero, mul_zero]
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let β : PositiveRealExponentialDecay univ :=
    ⟨fun t ↦ (b t : ℂ), mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
      (b.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp b.contDiff)⟩
  have hβ : β.val 0 = 1 := by
    change (b 0 : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  with_reducible refine (htest φ).elim fun f hf ↦ ?_
  with_reducible refine (htest β).elim fun b₀ hb₀ ↦ ?_
  obtain ⟨he, hpos⟩ :=
    thetaFiber_normalize σ.toMonoidHom hσ φ.val β.val hβ q hq hq₁ f.val b₀.val hf hb₀
  let z := ThetaS(b₀.val) 1
  have hz : z ≠ 0 := fun h ↦ (ne_of_gt hpos) (by simpa only [Complex.zero_re] using congrArg Complex.re h)
  refine ⟨z⁻¹ • f, fun g ↦ ?_⟩
  change ThetaS(z⁻¹ • f.val) g = _
  rw [map_smul, ContinuousMap.smul_apply, he]
  change z⁻¹ * (φ.val logPos(sIdeleQuotientNorm F S g) * z) = _
  rw [mul_left_comm, inv_mul_cancel₀ hz, mul_one]

end PolarFreeAssembly

section PolarFreeTarget

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

private theorem polarFree_section_lift
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : SIdeleQuotient F S,
      sLocalHomogeneousAdelicThetaLinearMap F S 1 f.val g =
        φ.val (Real.log ((sIdeleQuotientNorm F S g).val : ℝ)) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  with_reducible refine (thetaFiber_exists_archSection (S := S) w).elim fun σ hσ ↦ ?_
  have h := polarFree_assemble_profile (F := F) (S := S)
    polarFree_realModel polarFree_complexModel
    (polarFree_archWeight ((fun _ ↦ 1), (fun _ ↦ 1)))
    polarFree_archProjection σ hσ.1 hσ.2 polarFree_archProjection_val polarFree_archWeight_norm
    polarFree_lift_archimedean φ
  with_reducible refine h.elim fun f hf ↦ ?_
  refine ⟨⟨f.val, ?_⟩, hf⟩
  rw [sAdelePolarFree_eq_of_models r polarFree_realModel c polarFree_complexModel]
  exact f.property

end PolarFreeTarget

end PolarFreeConstruction

-- TODO(paper-gap): In (5.3.4.9), the summation index m_v does not occur in the summand.
-- Norm-one class representatives with archimedean component one need not exist.

/-- Paper: Lemma 5.3.4.3, p. 261.
Every log-Schwartz function decaying at all real exponents lifts to a polar-free test
whose trivial homogeneous theta function is the given radial function.
Deviation: Split the norm at a single archimedean place and average a compact
norm-one shape with finite integer-unit factors. -/
theorem sLocalHomogeneousTheta_trivial_exists_polarFree (r : RealModels) (c : ComplexModels)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : Jₛ,
      thetaAt(1) f.val g = φ.val (Real.log ((mₛ g).val : ℝ)) := by
  exact polarFree_section_lift (S := S) r c φ

section EulerFactors

open Complex Metric

/-- A nonzero analytic function is bounded away from zero on a sufficiently small
circle around each point, even if it vanishes at the center. -/
private theorem exists_pos_norm_on_sphere {p : ℂ → ℂ} (hp : AnalyticOnNhd ℂ p univ)
    (hne : ∃ z, p z ≠ 0) (c : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ d > (0 : ℝ), ∀ w ∈ sphere c r, d ≤ ‖p w‖ := by
  have hcod := (hp.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun h ↦ let ⟨z, hz⟩ := hne; hz (h (mem_univ z)))
  obtain ⟨R, hR, hnonzero⟩ := Metric.mem_nhdsWithin_iff.mp (nhdsNE_le_codiscrete c hcod)
  let r := min (R / 2) 1
  have hr : 0 < r := lt_min (half_pos hR) zero_lt_one
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hex : (sphere c r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere c r).exists_isMinOn hex
    (fun z _ ↦ (hp z trivial).continuousAt.continuousWithinAt.norm)
  have hw' : w ∈ ball c R ∩ {c}ᶜ := by
    rw [mem_sphere] at hw
    exact ⟨mem_ball.mpr (hw.trans_lt hrR), by
      rintro rfl
      exact hr.ne' (by simpa only [dist_self] using hw.symm)⟩
  exact ⟨r, hr, min_le_right _ _, ‖p w‖, norm_pos_iff.mpr (hnonzero hw'), fun z hz ↦ hmin hz⟩

/-- Removing an analytic multiplier periodic in height preserves boundedness on
closed vertical strips when the quotient is entire. -/
private theorem bounded_strip_of_periodic_mul {p f : ℂ → ℂ} {T : ℝ} (hT : 0 < T)
    (hperiod : Periodic p ((T : ℂ) * I)) (hp : AnalyticOnNhd ℂ p univ) (hne : ∃ z, p z ≠ 0)
    (hf : Differentiable ℂ f) {a b : ℝ}
    (hbound : ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc (a - 1) (b + 1) → ‖p z * f z‖ ≤ C) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C := by
  classical
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose r hr hr₁ d hd hnorm using exists_pos_norm_on_sphere hp hne
  have hcover : K ⊆ ⋃ c : K, ball c.val (r c.val) := fun c hc ↦
    mem_iUnion.mpr ⟨⟨c, hc⟩, mem_ball_self (hr c)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun c : K ↦ ball c.val (r c.val))
    (fun _ ↦ isOpen_ball) hcover
  obtain ⟨C, hC⟩ := hbound
  let M := 1 + ∑ c ∈ s, max C 0 / d c.val
  refine ⟨M, fun z hz ↦ ?_⟩
  let n := ⌊z.im / T⌋
  let v := (n : ℂ) * ((T : ℂ) * I)
  have hvre : v.re = 0 := by simp [v, Complex.mul_re, Complex.mul_im]
  have hvim : v.im = (n : ℝ) * T := by simp [v, Complex.mul_re, Complex.mul_im]
  have hzK : z - v ∈ K := by
    have hfloor := (le_div_iff₀ hT).mp (Int.floor_le (z.im / T))
    have hceil := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (z.im / T))
    change (z - v).re ∈ Icc a b ∧ (z - v).im ∈ Icc 0 T
    rw [Complex.sub_re, hvre, sub_zero, Complex.sub_im, hvim]
    exact ⟨hz, ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩⟩
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp (hs hzK)
  have hz' : z ∈ ball (c.val + v) (r c.val) := by
    simpa only [mem_ball, dist_eq_norm, sub_add_eq_sub_sub, add_comm c.val] using hzc
  have hc' : c.val.re ∈ Icc a b := c.property.1
  have hsph (w : ℂ) (hw : w ∈ sphere (c.val + v) (r c.val)) : ‖f w‖ ≤ M := by
    have hw₀ : w - v ∈ sphere c.val (r c.val) := by
      simpa only [mem_sphere, dist_eq_norm, sub_add_eq_sub_sub, add_comm c.val] using hw
    have hre : |w.re - c.val.re| ≤ 1 := by
      have h := Complex.abs_re_le_norm (w - (c.val + v))
      rw [Complex.sub_re, Complex.add_re, hvre, add_zero, ← dist_eq_norm, mem_sphere.mp hw] at h
      exact h.trans (hr₁ c.val)
    have hwstrip : w.re ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨hlo, hhi⟩ := abs_le.mp hre
      exact ⟨by linarith [hc'.1], by linarith [hc'.2]⟩
    have hper : p w = p (w - v) := by
      simpa only [v, zsmul_eq_mul, sub_add_cancel] using (hperiod.zsmul n (w - v))
    have hpw : d c.val ≤ ‖p w‖ := by rw [hper]; exact hnorm c.val (w - v) hw₀
    have hmul := hC w hwstrip
    rw [norm_mul] at hmul
    calc
      ‖f w‖ ≤ max C 0 / d c.val :=
        (le_div_iff₀ (hd c.val)).2 ((mul_le_mul_of_nonneg_left hpw (norm_nonneg _)).trans
          (by rw [mul_comm]; exact hmul.trans (le_max_left _ _)))
      _ ≤ M := by
        have hsum := Finset.single_le_sum
          (f := fun d' : K ↦ max C 0 / d d'.val)
          (fun i _ ↦ div_nonneg (le_max_right _ _) (hd i.val).le) hc
        dsimp [M]
        linarith
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hf.diffContOnCl ?_
    (subset_closure hz')
  exact fun w hw ↦ hsph w (frontier_ball_subset_sphere hw)

/-- The inverse Euler factor at a finite place is periodic with respect to an
imaginary translation. It is entire and not identically zero. -/
private theorem inv_finiteHeckeEulerFactor_periodic {F : Type*} [Field F] [NumberField F]
    (η : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ T : ℝ, 0 < T ∧
      Periodic (fun z ↦ (finiteHeckeEulerFactor η v z)⁻¹) ((T : ℂ) * I) ∧
      AnalyticOnNhd ℂ (fun z ↦ (finiteHeckeEulerFactor η v z)⁻¹) univ ∧
      ∃ z, (finiteHeckeEulerFactor η v z)⁻¹ ≠ 0 := by
  classical
  let q := (Ideal.absNorm v.asIdeal : ℝ)
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  let T := (2 * Real.pi) / Real.log q
  have hT : 0 < T := div_pos (by positivity) (Real.log_pos hq)
  refine ⟨T, hT, ?_⟩
  unfold finiteHeckeEulerFactor
  split_ifs with h
  · simp only [inv_inv]
    let a := (ideleClassNormTwist η 0).localValue v
    have hperiod : (q : ℂ) ^ (-((T : ℂ) * I)) = 1 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq₀.ne'),
        ← Complex.ofReal_log hq₀.le]
      have hprod : (Real.log q : ℂ) * (-((T : ℂ) * I)) = -(2 * (Real.pi : ℂ) * I) := by
        dsimp only [T]
        push_cast
        field_simp [(Real.log_pos hq).ne']
      rw [hprod, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
    have hregular : Differentiable ℂ (fun z : ℂ ↦ (q : ℂ) ^ (-z)) :=
      differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hq₀.ne'))
    refine ⟨fun z ↦ ?_, fun z _ ↦ ?_, ?_⟩
    · change 1 - a * (q : ℂ) ^ (-(z + (T : ℂ) * I)) = 1 - a * (q : ℂ) ^ (-z)
      rw [neg_add, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hq₀.ne'), hperiod, mul_one]
    · exact ((hregular.const_mul a).const_sub 1).analyticAt z
    · by_cases ha : a = 1
      · refine ⟨1, ?_⟩
        change 1 - a * (q : ℂ) ^ (-(1 : ℂ)) ≠ 0
        rw [ha, one_mul, sub_ne_zero]
        intro hzero
        have hnorm := congrArg norm hzero
        rw [norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re,
          Complex.one_re, Real.rpow_neg_one] at hnorm
        exact (inv_lt_one_of_one_lt₀ hq).ne' hnorm
      · refine ⟨0, ?_⟩
        change 1 - a * (q : ℂ) ^ (-(0 : ℂ)) ≠ 0
        simpa only [neg_zero, Complex.cpow_zero, mul_one] using sub_ne_zero.mpr (Ne.symm ha)
  · simp only [inv_one]
    exact ⟨fun _ ↦ rfl, fun _ _ ↦ analyticAt_const, 0, one_ne_zero⟩

/-- If multiplying an entire function by a finite Euler denominator produces
rapid decay on all strips, the original function has that same strip property. -/
private theorem schwartzBergman_of_finiteEulerFactors {F : Type*} [Field F] [NumberField F]
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (η : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (h : ∀ (a b : ℝ) (N : ℕ), ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
      ‖z ^ N * ((∏ v : S, (finiteHeckeEulerFactor η v.val z)⁻¹) * f z)‖ ≤ C) :
    f ∈ schwartzBergmanSubmodule univ := by
  classical
  let p (v : S) (z : ℂ) := (finiteHeckeEulerFactor η v.val z)⁻¹
  have hstep (s : Finset S) (N : ℕ)
      (hbound : ∀ a b : ℝ, ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b →
        ‖z ^ N * ((∏ v ∈ s, p v z) * f z)‖ ≤ C) :
      ∀ a b : ℝ, ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖z ^ N * f z‖ ≤ C := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, one_mul] using hbound
    | insert v s hv ih =>
      obtain ⟨T, hT, hperiod, hp, hne⟩ := inv_finiteHeckeEulerFactor_periodic η v.val
      apply ih
      intro a b
      let g (z : ℂ) := z ^ N * ((∏ v ∈ s, p v z) * f z)
      have hdiff (v : S) : Differentiable ℂ (p v) := by
        obtain ⟨_, _, _, hA, _⟩ := inv_finiteHeckeEulerFactor_periodic η v.val
        exact fun z ↦ (hA z (mem_univ z)).differentiableAt
      have hg : Differentiable ℂ g := (differentiable_id.pow N).mul
        ((Differentiable.fun_finsetProd fun v _ ↦ hdiff v).mul
          (fun z ↦ (hf z (mem_univ z)).differentiableAt))
      refine bounded_strip_of_periodic_mul hT hperiod hp hne hg ?_
      obtain ⟨C, hC⟩ := hbound (a - 1) (b + 1)
      refine ⟨C, fun z hz ↦ ?_⟩
      change ‖p v z * g z‖ ≤ C
      have hw := hC z hz
      rw [Finset.prod_insert hv] at hw
      dsimp only [g]
      convert hw using 1
      congr 1
      ac_rfl
  refine ⟨by simp, hf.differentiableOn.mono (subset_univ _), fun a b _ _ N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hstep Finset.univ N (fun a b ↦ h a b N) a b
  exact ⟨C, by rintro _ ⟨z, hz, rfl⟩; exact hC z hz⟩

end EulerFactors

/-- Project the canonical norm section to the S-ideles. -/
private theorem polarFree_exists_normSection :
    ∃ τ : ℝ≥0ˣ →ₜ* Aₛˣ, RightInverse τ (sIdeleNorm F S) := by
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let s := canonicalIdeleNormSection F
  refine ⟨⟨p.comp s, hp.comp (canonicalIdeleNormSection_continuous F)⟩, fun t ↦ ?_⟩
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    change (canonicalIdeleNormSection F u).val.2 v ∈ v.adicCompletionIntegers F
    rw [canonicalIdeleNormSection_finite F u]
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units := by
    refine ⟨hmem t, ?_⟩
    change ((s t)⁻¹).val ∈ A
    rw [← map_inv]
    exact hmem t⁻¹
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (canonicalIdeleNormSection_rightInverse F t)

/-- A polar-free test with trivial homogeneous theta given by a log profile has
trivial-component zeta transform equal to the profile's Mellin transform. -/
private theorem polarFree_zeta_of_radial (f : ℬₛ) (φ : ℝ → ℂ)
    (hφ : ∀ g : Jₛ, thetaAt(1) f g = φ (Real.log ((mₛ g).val : ℝ)))
    (z : ℂ) (hz : 0 < z.re) :
    sLocalIdelicZFunction f (chartₛ(1) z) = mellin (fun t ↦ φ (Real.log t)) z := by
  obtain ⟨τ, hτ⟩ := polarFree_exists_normSection (F := F) (S := S)
  let c : QuasiCharacter Jₛ := chartₛ(1) z
  have hc : ∃ (χ : PontryaginDual Jₛ) (s : ℂ), 0 < s.re ∧ c = chartₛ(χ) s :=
    ⟨1, z, hz, rfl⟩
  change sLocalIdelicZFunction f c = _
  refine (sLocalIdelicZFunction_eq_integral f hc).trans
    ((sLocalThetaMellinIntegral_eq_zeta f hc).symm.trans
      ((sLocalRadialMellinIntegral_eq_theta τ hτ f 1 z hz).symm.trans ?_))
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hmeasure : positiveRealHaar = volume.map e := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext x
    apply Units.ext
    apply NNReal.eq
    exact Real.coe_toNNReal _ (Real.exp_pos x).le
  simp only [sLocalRadialMellinIntegral, hmeasure]
  rw [e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
  apply integral_congr_ae
  filter_upwards with x
  have ht (t : ℝ≥0ˣ) : mₛ (QuotientGroup.mk (τ t)) = t :=
    (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have he : (((e x).val : ℝ≥0) : ℝ) = Real.exp x := rfl
  have hp : (Real.exp x : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  change thetaAt(1) f (QuotientGroup.mk (τ (e x))) *
      (1 * ((((mₛ (QuotientGroup.mk (τ (e x)))).val : ℝ) : ℂ) ^ z)) = _
  rw [hφ, ht, he, one_mul, hp]
  simp only [Real.log_exp, Complex.real_smul, Complex.ofReal_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), ← Complex.ofReal_exp,
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  rw [smul_eq_mul, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm (φ x)]
  congr 2
  ring

/-- Twisting the test by the inverse character cancels the unitary part of the zeta integral. -/
private theorem polarFree_zeta_twist (f g : ℬₛ) (χ : PontryaginDual Jₛ)
    (h : ∀ u : Aₛˣ, g (Multiplicative.ofAdd u.val) =
      ((circleToComplex).comp χ⁻¹) (QuotientGroup.mk u) * f (Multiplicative.ofAdd u.val))
    (z : ℂ) (hz : 0 < z.re) :
    sLocalIdelicZFunction g (chartₛ(χ) z) = sLocalIdelicZFunction f (chartₛ(1) z) := by
  refine (sLocalIdelicZFunction_eq_integral g ⟨χ, z, hz, rfl⟩).trans
    (Eq.trans ?_ (sLocalIdelicZFunction_eq_integral f ⟨1, z, hz, rfl⟩).symm)
  unfold sLocalIdelicZetaIntegral
  apply integral_congr_ae
  filter_upwards with u
  let q : Jₛ := QuotientGroup.mk u
  let p := ((((mₛ q).val : ℝ) : ℂ) ^ z)
  rw [h]
  change (((χ⁻¹ q : Circle) : ℂ) * f (Multiplicative.ofAdd u.val)) * ((χ q : ℂ) * p) =
    f (Multiplicative.ofAdd u.val) * (1 * p)
  change (((χ q)⁻¹ : Circle) : ℂ) * _ * _ = _
  rw [Circle.coe_inv, one_mul]
  rw [show ((χ q : ℂ)⁻¹ * f (Multiplicative.ofAdd u.val)) * ((χ q : ℂ) * p) =
      ((χ q : ℂ)⁻¹ * (χ q : ℂ)) * (f (Multiplicative.ofAdd u.val) * p) by ac_rfl,
    inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
/-- Invert the scalar Fourier–Mellin transform, lift its profile, and twist the lift. -/
private theorem polarFree_exists_of_schwartzBergman (r : RealModels) (c : ComplexModels)
    (χ : PontryaginDual Jₛ) (f : ℬₛ)
    (h : (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) ∈ schwartzBergmanSubmodule univ) :
    ∃ f₀ : sAdelePolarFree S r c, ∀ s : ℂ,
      sLocalIdelicZFunction f (chartₛ(χ) s) = sLocalIdelicZFunction f₀.val (chartₛ(χ) s) := by
  let M := positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
  let Z : SchwartzBergman univ := ⟨_, h⟩
  let φ : PositiveRealExponentialDecay univ := M.symm Z
  obtain ⟨g, hg⟩ := sLocalHomogeneousTheta_trivial_exists_polarFree r c φ
  obtain ⟨A, hA⟩ := sAdelePolarFree_quasiCharacter_mul r c ((circleToComplex).comp χ⁻¹)
  refine ⟨A g, fun s ↦ ?_⟩
  apply realArchimedeanMellin_existsUnique_eqNF
    (sLocalIdelicZFunction_meromorphic f χ) (sLocalIdelicZFunction_meromorphic (A g).val χ) _ s
  intro z hz
  have hM := positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty
    φ z (mem_univ z)
  change (M φ).val z = _ at hM
  rw [show M φ = Z from M.apply_symm_apply Z] at hM
  exact hM.trans ((polarFree_zeta_of_radial g.val φ.val hg z hz).symm.trans
    (polarFree_zeta_twist g.val (A g).val χ (hA g) z hz).symm)

section EntireChartStripBounds

open Complex Metric

/-- Entire division by a periodic factor preserves every polynomial weight on vertical strips. -/
theorem schwartzBergman_of_periodic_mul {D G : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hne : ∃ z, D z ≠ 0) {T : ℝ} (hT : 0 < T) (hper : Function.Periodic D ((T : ℂ) * I))
    (hG : Differentiable ℂ G) (h : (fun z ↦ D z * G z) ∈ schwartzBergmanSubmodule univ) :
    G ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hG.differentiableOn, ?_⟩
  intro a b _ _ N
  apply bddAbove_strip_of_periodic_mul hD hne hT hper ((differentiable_id.pow N).mul hG) _ a b
  intro u v huv
  simpa only [Pi.pow_apply, Pi.mul_apply, id_eq, mul_left_comm] using h.2.2 u v huv (subset_univ _) N

/-- Each cleared factor can have its own imaginary period. -/
theorem schwartzBergman_of_periodic_prod {ι : Type*} (s : Finset ι) (D : ι → ℂ → ℂ)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hD : ∀ j ∈ s, Differentiable ℂ (D j) ∧ (∃ z, D j z ≠ 0) ∧
      ∃ T : ℝ, 0 < T ∧ Function.Periodic (D j) ((T : ℂ) * I))
    (h : (fun z ↦ (∏ j ∈ s, D j z) * G z) ∈ schwartzBergmanSubmodule univ) :
    G ∈ schwartzBergmanSubmodule univ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | @insert i s hi IH =>
    obtain ⟨hd, hn, T, hT, hp⟩ := hD i (Finset.mem_insert_self ..)
    have hrest (j) (hj : j ∈ s) := hD j (Finset.mem_insert_of_mem hj)
    apply IH hrest
    refine schwartzBergman_of_periodic_mul hd hn hT hp ?_ ?_
    · exact (Differentiable.fun_finsetProd fun j hj ↦ (hrest j hj).1).mul hG
    · simpa only [Finset.prod_insert hi, mul_assoc] using h

private theorem cpow_at_norm_period {q : ℝ} (hq : 1 < q) :
    (q : ℂ) ^ (((2 * Real.pi / Real.log q : ℝ) : ℂ) * I) = 1 := by
  have hlog : (Real.log q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne'), ← ofReal_log (zero_lt_one.trans hq).le]
  push_cast
  rw [show (Real.log q : ℂ) * (2 * (Real.pi : ℂ) / Real.log q * I) = 2 * Real.pi * I by field_simp]
  exact exp_two_pi_mul_I

/-- An inverse finite Euler factor is entire and has a positive imaginary period. -/
private theorem finiteEulerInverse_periodic (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (v : V) : let D := fun z : ℂ ↦ (finiteHeckeEulerFactor χ v z)⁻¹
    Differentiable ℂ D ∧ (∃ z, D z ≠ 0) ∧ ∃ T : ℝ, 0 < T ∧ Function.Periodic D ((T : ℂ) * I) := by
  classical
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans hq).ne'
  dsimp only
  unfold finiteHeckeEulerFactor
  split_ifs with hu
  · simp_rw [inv_inv]
    let c := (ideleClassNormTwist χ 0).localValue v
    change Differentiable ℂ (fun z : ℂ ↦ 1 - c * (q : ℂ)^(-z)) ∧ _
    refine ⟨(differentiable_const _).sub ((differentiable_const _).mul
      (differentiable_neg.const_cpow (Or.inl hq'))), ?_, 2 * Real.pi / Real.log q,
      div_pos (by positivity) (Real.log_pos hq), ?_⟩
    · change ∃ z : ℂ, 1 - c * (q : ℂ)^(-z) ≠ 0
      by_cases hc : c = 1
      · refine ⟨1, ?_⟩
        rw [hc, one_mul, cpow_neg, cpow_one]
        exact sub_ne_zero.mpr (by
          intro eq
          have eq' := congrArg Inv.inv eq
          simp at eq'
          exact hq.ne (ofReal_injective (by simpa using eq')))
      · exact ⟨0, by simpa using (sub_ne_zero.mpr (Ne.symm hc))⟩
    · intro z
      change 1 - c * (q : ℂ)^(-(z + _)) = 1 - c * (q : ℂ)^(-z)
      rw [neg_add, cpow_add _ _ hq', cpow_neg _ (((2 * Real.pi / Real.log q : ℝ) : ℂ) * I),
        cpow_at_norm_period hq, inv_one, mul_one]
  · simp only [inv_one]
    exact ⟨differentiable_const _, ⟨0, one_ne_zero⟩, 1, zero_lt_one, fun _ ↦ rfl⟩

/-- A norm twist at a finite place has the imaginary period of its discrete value group. -/
private theorem finite_norm_chart_period (v : V) (η : PontryaginDual (v.adicCompletion F)ˣ) :
    let q : ℝ := v.asIdeal.absNorm
    Function.Periodic (quasiCharacterNormTwist (Units.map nnNormHom.toMonoidHom : (v.adicCompletion F)ˣ →* ℝ≥0ˣ) (continuous_finiteLocalModule v)
      ((circleToComplex).comp η)) (((2 * Real.pi / Real.log q : ℝ) : ℂ) * I) := by
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  dsimp only
  intro z
  ext1 u
  change (η u : ℂ) * ((‖u.val‖ : ℝ) : ℂ)^(z + _) = (η u : ℂ) * ((‖u.val‖ : ℝ) : ℂ)^z
  rw [cpow_add _ _ (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr u.ne_zero))]
  suffices h : ((‖u.val‖ : ℝ) : ℂ)^(((2 * Real.pi / Real.log q : ℝ) : ℂ) * I) = 1 by rw [h, mul_one]
  let n : ℤ := WithZero.log (Valued.v u.val)
  have hn : ‖u.val‖ = q ^ n := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ (by simp [u.ne_zero]), NNReal.coe_zpow]
    rfl
  rw [hn, show q^n = q^(n : ℝ) by simp, ← cpow_mul_ofReal_nonneg (zero_lt_one.trans hq).le]
  rw [ofReal_intCast, cpow_int_mul, cpow_at_norm_period hq, one_zpow]
private theorem sLocalEpsilonFactor_norm_strip (χ : PontryaginDual Jₛ) (a b : ℝ) :
    ∃ C ≥ (1 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖sLocalEpsilonFactor (chartₛ(χ) z)‖ ≤ C := by
  classical
  have hf (v : S) : ∃ C ≥ (1 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b →
      ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ ≤ C := by
    obtain ⟨η, hη, _⟩ := sLocalFiniteRestriction_exists_normTwistChart χ v
    have ht := finite_norm_chart_period v.val η
    have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
    have hcont := (finiteLocalEpsilonFactor_entire v.val η).differentiableOn
    rw [differentiableOn_univ] at hcont
    obtain ⟨C, h⟩ := norm_bounded_on_strip_of_imaginary_period hcont.continuous
      (div_pos (by positivity) (Real.log_pos hq)) (ht.comp (finiteLocalEpsilonFactor v.val)) a b
    refine ⟨max 1 C, le_max_left _ _, fun z hz ↦ ?_⟩
    rw [hη z]
    exact (h z hz).trans (le_max_right _ _)
  choose C hC hCn using hf
  refine ⟨max 1 (∏ v, C v), le_max_left _ _, fun z hz ↦ ?_⟩
  apply le_trans _ (le_max_right _ _)
  rw [sLocalEpsilonFactor, norm_mul, norm_prod, norm_prod]
  have ha (w : InfinitePlace F) : ‖infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))‖ = 1 := by
    unfold infiniteLocalEpsilonFactor
    split <;> simp
  simp only [ha, Finset.prod_const_one, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ hCn v z hz)
private theorem local_chart_inverse_extension (χ : PontryaginDual Jₛ)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (h : ideleClassNormTwist ψ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ψ 0, h⟩ = chartₛ(χ) 0) :
    ∃ h' : ideleClassNormTwist ψ⁻¹ 0 ∈ unramifiedOutside F S,
      sIdeleRestriction F S ⟨ideleClassNormTwist ψ⁻¹ 0, h'⟩ = chartₛ(χ⁻¹) 0 := by
  have hinv (x : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist ψ⁻¹ 0 x = (ideleClassNormTwist ψ 0 x)⁻¹ := by
    change ((ψ x)⁻¹ : Circle) * _ ^ (0 : ℂ) = ((_ : ℂ) * _ ^ (0 : ℂ))⁻¹
    simp
    rfl
  have h' : ideleClassNormTwist ψ⁻¹ 0 ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v hv u
    have hx := (mem_unramifiedOutside_iff F S _).mp h v hv u
    change ideleClassNormTwist ψ 0 _ = 1 at hx
    change ideleClassNormTwist ψ⁻¹ 0 _ = 1
    rw [hinv, hx, inv_one]
  refine ⟨h', ?_⟩
  ext1 x
  induction x using QuotientGroup.induction_on with
  | H x =>
    have hx := DFunLike.congr_fun he (QuotientGroup.mk x)
    rw [sIdeleRestriction_mk] at hx ⊢
    rw [hinv, hx]
    change ((_ : ℂ) * _ ^ (0 : ℂ))⁻¹ = ((χ (QuotientGroup.mk x))⁻¹ : Circle) * _ ^ (0 : ℂ)
    simp
    rfl

private theorem local_entire_normalized_eq (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (ha : AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) univ) (z : ℂ) :
    sLocalNormalizedZFunction f (chartₛ(χ) z) =
      sLocalIdelicZFunction f (chartₛ(χ) z) * (sLocalHeckeL (chartₛ(χ) z))⁻¹ := by
  apply (sLocalNormalizedZFunction_entire f χ).eqOn_of_preconnected_of_eventuallyEq
    (ha.mul (fun z _ ↦ (sLocalHeckeL_inv_differentiable χ).analyticAt z)) isPreconnected_univ
    (mem_univ (1 : ℂ)) _ (mem_univ z)
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (show 0 < (1 : ℂ).re by simp)] with s hs
  rw [sLocalNormalizedZFunction_eq_div f χ hs, sLocalIdelicZFunction_eq_integral f ⟨χ, s, hs, rfl⟩,
    div_eq_mul_inv]

private theorem cleared_chart_reflection (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (ha : AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) univ)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (h : ideleClassNormTwist ψ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ψ 0, h⟩ = chartₛ(χ) 0) (s : ℂ)
    (hs : s.re < 1) (hΓ : heckeGammaFactor ψ s ≠ 0) :
    (∏ v : S, (finiteHeckeEulerFactor ψ v.val s)⁻¹) * sLocalIdelicZFunction f (chartₛ(χ) s) =
      (heckeGammaFactor ψ s / heckeGammaFactor ψ⁻¹ (1-s)) *
      sLocalEpsilonFactor (chartₛ(χ) s) * (∏ v : S, (finiteHeckeEulerFactor ψ⁻¹ v.val (1-s))⁻¹) *
      sLocalIdelicZFunction (sAdeleSchwartzFourier f) (chartₛ(χ⁻¹) (1-s)) := by
  obtain ⟨h', he'⟩ := local_chart_inverse_extension χ ψ h he
  have heq := sLocalNormalizedZFunction_functionalEquation f (chartₛ(χ) s)
  have hpos : 0 < (1-s).re := by simpa using hs
  erw [sLocalNormTwistChart_dual χ s, local_entire_normalized_eq χ f ha,
    sLocalNormalizedZFunction_eq_div (sAdeleSchwartzFourier f) χ⁻¹ (s := 1-s) hpos,
    ← sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1-s, hpos, rfl⟩,
    sLocalHeckeL_eq_partialEulerProduct χ ψ h he,
    sLocalHeckeL_eq_partialEulerProduct χ⁻¹ ψ⁻¹ h' he'] at heq
  simp only [div_eq_mul_inv, mul_inv, ← Finset.prod_inv_distrib] at heq
  calc
    _ = heckeGammaFactor ψ s * (sLocalIdelicZFunction f (chartₛ(χ) s) *
        ((heckeGammaFactor ψ s)⁻¹ * ∏ v : S, (finiteHeckeEulerFactor ψ v.val s)⁻¹)) := by
          field_simp
    _ = _ := by erw [heq]; rw [div_eq_mul_inv]; ac_rfl
private theorem schwartzBergman_of_height_bounds {G : ℂ → ℂ} (hd : Differentiable ℂ G)
    (h : ∀ a b : ℝ, a ≤ b → ∀ N : ℕ, ∃ C T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| →
      ‖G z‖ ≤ C / |z.im| ^ N) : G ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hd.differentiableOn, ?_⟩
  intro a b hab _ N
  obtain ⟨C, T, hC⟩ := h a b hab N
  let H := max 1 (max T (max |a| |b|))
  let K := reProdIm (Icc a b) (Icc (-H) H)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hK.bddAbove_image (((continuous_id.pow N).mul hd.continuous).norm.continuousOn)
  refine ⟨max B (2^N*C), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change z.re ∈ Icc a b at hz
  by_cases hy : |z.im| ≤ H
  · exact (hB ⟨z, ⟨hz, abs_le.mp hy⟩, rfl⟩).trans (le_max_left _ _)
  have hH := (not_le.mp hy).le
  have hT := (le_max_left T _).trans ((le_max_right _ _).trans hH)
  have h1 := (le_max_left (1:ℝ) _).trans hH
  have hA := (le_max_right T (max |a| |b|)).trans ((le_max_right _ _).trans hH)
  have hx : |z.re| ≤ max |a| |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, hz.1],
     by linarith [le_abs_self b, le_max_right |a| |b|, hz.2]⟩
  have hzB : ‖z‖ ≤ 2 * |z.im| := (norm_le_abs_re_add_abs_im z).trans (by linarith)
  have hC' := (le_div_iff₀ (pow_pos (zero_lt_one.trans_le h1) N)).mp (hC z hz hT)
  apply le_trans _ (le_max_right _ _)
  change ‖z^N*G z‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2*|z.im|)^N * ‖G z‖ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hzB _) (norm_nonneg _)
    _ = 2^N * (‖G z‖ * |z.im|^N) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hC' (by positivity)

private theorem finiteEulerInverse_prod_bounds (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖∏ v : S, (finiteHeckeEulerFactor ψ v.val z)⁻¹‖ ≤ C := by
  classical
  have hv (v : S) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖(finiteHeckeEulerFactor ψ v.val z)⁻¹‖ ≤ C := by
    obtain ⟨hd, _, T, hT, hp⟩ := finiteEulerInverse_periodic ψ v.val
    obtain ⟨C, hc⟩ := norm_bounded_on_strip_of_imaginary_period hd.continuous hT hp a b
    exact ⟨max C 0, le_max_right _ _, fun z hz ↦ (hc z hz).trans (le_max_left _ _)⟩
  choose C hc h using hv
  exact ⟨∏ v, C v, Finset.prod_nonneg (fun i _ ↦ hc i), fun z hz ↦ (norm_prod ..).trans_le
    (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ h v z hz))⟩

private theorem zetaChart_positive_height_tail (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (a b : ℝ) (ha : 0 < a) (N : ℕ) :
    ∃ C > (0 : ℝ), ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| →
      ‖sLocalIdelicZFunction f (chartₛ(χ) z)‖ ≤ C / |z.im| ^ N := by
  obtain ⟨C, hC, ht⟩ := sLocalIdelicZFunction_rapid_decay_on_positive_strip f χ a (max a b + 1) ha
    (by linarith [le_max_left a b]) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp ht)
  refine ⟨C, hC, max T 1, fun z hz hy ↦ ?_⟩
  have h1 := (le_max_right _ _).trans hy
  have h := hT |z.im| ((le_max_left _ _).trans hy) z.im rfl z.re
    (show z.re ∈ Icc a (max a b + 1) from ⟨hz.1, by linarith [le_max_right a b, hz.2]⟩)
  rw [Complex.re_add_im] at h
  exact h.trans (div_le_div_of_nonneg_left hC.le (pow_pos (zero_lt_one.trans_le h1) N)
    (pow_le_pow_right₀ h1 (by omega)))
/-- Once the finite Euler denominators are cleared, reflection bounds the left half of a strip by a positive-strip zeta estimate. -/
private theorem cleared_chart_left_tail (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (ha : AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) univ)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (h : ideleClassNormTwist ψ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ψ 0, h⟩ = chartₛ(χ) 0) (a : ℝ) (N : ℕ) :
    ∃ C ≥ (0 : ℝ), ∃ T : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ 1/2 → T ≤ |z.im| → heckeGammaFactor ψ z ≠ 0 →
      ‖(∏ v : S, (finiteHeckeEulerFactor ψ v.val z)⁻¹) * sLocalIdelicZFunction f (chartₛ(χ) z)‖ ≤
        C / |z.im|^N := by
  obtain ⟨A,T,hA,hT,hΓ⟩ := heckeGammaFactor_reflection_bound_on_strip ψ⁻¹ (1/2) (1-a)
  obtain ⟨B,hB,hε⟩ := sLocalEpsilonFactor_norm_strip χ a (1/2)
  obtain ⟨C,hC,hD⟩ := finiteEulerInverse_prod_bounds (S := S) ψ⁻¹ (1/2) (1-a)
  obtain ⟨E,hE,H,hZ⟩ := zetaChart_positive_height_tail χ⁻¹ (sAdeleSchwartzFourier f) (1/2) (1-a) (by norm_num) N
  refine ⟨A * B * C * E, by positivity, max 1 (max T H), fun z hl hr ht hn ↦ ?_⟩
  have h1 := (le_max_left (1:ℝ) _).trans ht
  have hT' := (le_max_left T H).trans ((le_max_right _ _).trans ht)
  have hH' := (le_max_right T H).trans ((le_max_right _ _).trans ht)
  have hx : (1-z).re ∈ Icc (1/2) (1-a) := by
    rw [sub_re, one_re]
    exact ⟨by linarith, by linarith⟩
  have hy : |(1-z).im| = |z.im| := by simp
  have hg := hΓ (1-z) hx.1 hx.2 (hy ▸ hT')
  rw [inv_inv, sub_sub_cancel, hy] at hg
  have hp : (Module.finrank ℚ F : ℝ) * (1/2-(1-z).re) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hx.1])
  have hg' := hg.trans (mul_le_of_le_one_right hA.le (Real.rpow_le_one_of_one_le_of_nonpos h1 hp))
  have hz := hZ (1-z) hx (hy ▸ hH')
  rw [hy] at hz
  rw [cleared_chart_reflection χ f ha ψ h he z (by linarith) hn, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ A * B * C * (E / |z.im|^N) :=
      mul_le_mul (mul_le_mul (mul_le_mul hg' (hε z ⟨hl,hr⟩) (norm_nonneg _) hA.le)
        (hD (1-z) hx) (norm_nonneg _) (by positivity)) hz (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- For an entire chart, the high-height estimate on the cleared product extends across exceptional gamma values by continuity. -/
private theorem cleared_chart_all_strips (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (ha : AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) univ)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (h : ideleClassNormTwist ψ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ψ 0, h⟩ = chartₛ(χ) 0) :
    (fun z ↦ (∏ v : S, (finiteHeckeEulerFactor ψ v.val z)⁻¹) * sLocalIdelicZFunction f (chartₛ(χ) z))
      ∈ schwartzBergmanSubmodule univ := by
  let G (z : ℂ) := (∏ v : S, (finiteHeckeEulerFactor ψ v.val z)⁻¹) * sLocalIdelicZFunction f (chartₛ(χ) z)
  have hd : Differentiable ℂ G :=
    (Differentiable.fun_finsetProd fun v _ ↦ (finiteEulerInverse_periodic ψ v.val).1).mul
      (differentiableOn_univ.mp ha.differentiableOn)
  apply schwartzBergman_of_height_bounds hd
  intro a b hab N
  obtain ⟨L,hL,T,hl⟩ := cleared_chart_left_tail χ f ha ψ h he (a-1) N
  obtain ⟨D,hD,hD'⟩ := finiteEulerInverse_prod_bounds (S := S) ψ a b
  obtain ⟨P,hP,U,hP'⟩ := zetaChart_positive_height_tail χ f (1/4) b (by norm_num) N
  have hΓa : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor ψ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor ψ).analyticAt z
  have hdisc := (hΓa.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun hΓ ↦ (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos ψ (s := 1) (by simp))) (hΓ (mem_univ 1)))
  refine ⟨max L (D*P), max 1 (max (T+1) U), fun z hz ht ↦ ?_⟩
  have h1 := (le_max_left (1:ℝ) _).trans ht
  have hu := (le_max_right (T+1) U).trans ((le_max_right _ _).trans ht)
  have hT := (le_max_left (T+1) U).trans ((le_max_right _ _).trans ht)
  by_cases hright : 1/4 ≤ z.re
  · change ‖_ * _‖ ≤ _
    rw [norm_mul]
    apply le_trans (mul_le_mul (hD' z hz) (hP' z ⟨hright,hz.2⟩ hu) (norm_nonneg _) hD)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  have hne : |z.im| ^ N ≠ 0 := pow_ne_zero _ (by linarith : |z.im| ≠ 0)
  have hc : ContinuousAt (fun w : ℂ ↦ L / |w.im|^N) z :=
    continuousAt_const.div (continuous_im.abs.pow N).continuousAt hne
  have hbound : ∀ᶠ w in 𝓝[≠] z, ‖G w‖ ≤ L / |w.im|^N := by
    have hwin : ∀ᶠ w : ℂ in 𝓝 z, a-1 < w.re ∧ w.re < 1/2 ∧ T < |w.im| := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show a-1 < z.re by linarith [hz.1]),
        (isOpen_lt continuous_re continuous_const).mem_nhds (show z.re < 1/2 by linarith),
        (isOpen_lt continuous_const continuous_im.abs).mem_nhds (show T < |z.im| by linarith)] with w hw₁ hw₂ hw₃
      exact ⟨hw₁, hw₂, hw₃⟩
    have hgood : ∀ᶠ w in 𝓝[≠] z, (heckeGammaFactor ψ w)⁻¹ ≠ 0 := hdisc.filter_mono (nhdsNE_le_codiscrete z)
    filter_upwards [nhdsWithin_le_nhds hwin, hgood] with w hw hΓ
    exact hl w hw.1.le hw.2.1.le hw.2.2.le (fun e ↦ hΓ (by simp [e]))
  have h₀ := le_of_tendsto_of_tendsto (hd.continuous.norm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hc.tendsto.mono_left nhdsWithin_le_nhds) hbound
  exact h₀.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))

/-- Paper: Proposition 5.3.4.4(1) ⇒ (3), p. 264.
An entire S-local zeta chart is Schwartz on every closed vertical strip.
Deviation: The proof clears the finite Euler denominators before estimating the
reflected chart and divides them out using the maximum modulus principle. -/
theorem sLocalIdelicZFunction_schwartzBergman_of_entire (χ : PontryaginDual Jₛ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (ha : AnalyticOnNhd ℂ (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) univ) :
    (fun z ↦ sLocalIdelicZFunction f (chartₛ(χ) z)) ∈ schwartzBergmanSubmodule univ := by
  classical
  obtain ⟨ψ, h, he, _⟩ := sLocal_character_extension χ
  apply schwartzBergman_of_periodic_prod (Finset.univ : Finset S)
    (fun v z ↦ (finiteHeckeEulerFactor ψ v.val z)⁻¹) (differentiableOn_univ.mp ha.differentiableOn)
    (fun v _ ↦ finiteEulerInverse_periodic ψ v.val)
  exact cleared_chart_all_strips χ f ha ψ h he

end EntireChartStripBounds

/-- Paper: Proposition 5.3.4.4(1)–(2), p. 264.
On the component of χ, a zeta transform is entire exactly when it agrees there
with the transform of a polar-free test. -/
theorem sLocalIdelicZFunction_entire_iff_eq_polarFree (r : RealModels) (c : ComplexModels)
    (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      ∃ f₀ : sAdelePolarFree S r c, ∀ s : ℂ,
        sLocalIdelicZFunction f (chartₛ(χ) s) = sLocalIdelicZFunction f₀.val (chartₛ(χ) s) := by
  constructor
  · intro h
    obtain ⟨η, hη⟩ := sLocalIdelicZFunction_cleared_strips χ f h
    exact polarFree_exists_of_schwartzBergman r c χ f
      (schwartzBergman_of_finiteEulerFactors η _ h hη)
  · rintro ⟨f₀, hf₀⟩
    exact (sLocalIdelicZFunction_entire_of_polarFree r c f₀.val f₀.property χ).congr
      isOpen_univ fun z _ ↦ (hf₀ z).symm

/-- Multiplication of a test by a character of the idele quotient factors that character
out of the S-unit sum, since every projected diagonal S-unit has class one. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_twist_sum (b : Xₛ)
    (f f' : ℬₛ) (h : ∀ z : Aₛˣ, f' (Multiplicative.ofAdd z.val) =
      b (QuotientGroup.mk z) * f (Multiplicative.ofAdd z.val)) (x : Jₛ) :
    sLocalAdelicThetaOnClasses F S f' x = b x * sLocalAdelicThetaOnClasses F S f x := by
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
    sLocalAdelicTheta_apply, sLocalAdelicTheta_apply, ← tsum_mul_left]
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  apply tsum_congr
  intro u
  have hu : (QuotientGroup.mk (d u) : Jₛ) = 1 := (sIdeleQuotient_mk_eq_one F S _).mpr ⟨u, rfl⟩
  have hz : (QuotientGroup.mk (d u * z) : Jₛ) = QuotientGroup.mk z := by
    exact (QuotientGroup.mk_mul _ (d u) z).trans ((congrArg (· * (QuotientGroup.mk z : Jₛ)) hu).trans (one_mul (QuotientGroup.mk z : Jₛ)))
  exact (h (d u * z)).trans (congrArg (fun a : Jₛ ↦ b a * f (Multiplicative.ofAdd (d u * z).val)) hz)

/-- Twisting a test by the inverse of a unitary character transports its trivial homogeneous
theta function to the restricted character isotype. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_twist (ψ : PontryaginDual J₁)
    (χ : PontryaginDual Jₛ) (hχ : ∀ u : J₁, χ u.val = ψ u) (f f' : ℬₛ)
    (h : ∀ z : Aₛˣ, f' (Multiplicative.ofAdd z.val) =
      ((circleToComplex).comp χ⁻¹) (QuotientGroup.mk z) * f (Multiplicative.ofAdd z.val))
    (g : Jₛ) : sLocalHomogeneousAdelicThetaLinearMap F S ψ f' g =
      (χ g : ℂ)⁻¹ * sLocalHomogeneousAdelicThetaLinearMap F S 1 f g := by
  let : MeasurableSpace J₁ := borel _
  let μ := sLocalNormOneQuotientMeasure F S
  let b := (circleToComplex).comp χ⁻¹
  have hfactor (u : J₁) : b (g * u.val) * (ψ u : ℂ) = (χ g : ℂ)⁻¹ := by
    change (((χ (g * u.val))⁻¹ : Circle) : ℂ) * (ψ u : ℂ) = _
    rw [map_mul, Circle.coe_inv, Circle.coe_mul, hχ]
    field_simp [Circle.coe_ne_zero]
  have hint (u : J₁) :
      sLocalAdelicThetaOnClasses F S f' (g * u.val) * (ψ u : ℂ) =
      (χ g : ℂ)⁻¹ * (sLocalAdelicThetaOnClasses F S f (g * u.val) * ((1 : PontryaginDual J₁) u : ℂ)) := by
    rw [sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_twist_sum b f f' h, mul_right_comm, hfactor]
    change _ = _ * (_ * ((1 : Circle) : ℂ))
    rw [Circle.coe_one, mul_one]
  exact (sLocalHomogeneousAdelicThetaLinearMap_apply ψ f' g).trans
    ((MeasureTheory.integral_congr_ae (μ := μ) (.of_forall hint)).trans
      ((MeasureTheory.integral_const_mul _ _).trans
        (congrArg ((χ g : ℂ)⁻¹ * ·) (sLocalHomogeneousAdelicThetaLinearMap_apply (F := F) (S := S) (1 : PontryaginDual J₁) f g).symm)))

/-- An idelic norm section through one archimedean place gives the radial integration
formula for the S-local zeta integral. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_section :
    ∃ τ : ℝ≥0ˣ →ₜ* Aₛˣ, RightInverse τ (sIdeleNorm F S) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ₀ : ℝ≥0ˣ →ₜ* Aₛˣ := ⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩
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
  exact ⟨τ₀, hτ₀⟩

/-- The logarithm identifies the positive-real Haar integral with the usual Mellin integral. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_mellin (p : ℝ → ℂ) (s : ℂ) :
    (∫ t : ℝ≥0ˣ, p (Real.log (t.val : ℝ)) * (((t.val : ℝ) : ℂ) ^ s) ∂positiveRealHaar) =
      mellin (fun t ↦ p (Real.log t)) s := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (x : ℝ) : (e x).val = (Real.exp x).toNNReal := by
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).symm
  have hm : positiveRealHaar = volume.map e := by
    apply congrArg (fun a : ℝ → ℝ≥0ˣ ↦ volume.map a)
    funext x
    exact Units.ext (he x).symm
  rw [hm, e.measurableEmbedding.integral_map, mellin, ← integral_comp_exp]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [he, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  rw [mul_comm (p x)]
  congr 2
  ring

/-- A homogeneous theta function with a scalar logarithmic profile has that profile’s
Mellin transform on the right half-plane. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial
    (χ : PontryaginDual Jₛ) (f : ℬₛ) (p : ℝ → ℂ)
    (hp : ∀ g : Jₛ, thetaAt(χ₁(χ)) f g = (χ g : ℂ)⁻¹ * p (Real.log ((mₛ g).val : ℝ)))
    (s : ℂ) (hs : 0 < s.re) :
    sLocalIdelicZFunction f (chartₛ(χ) s) = mellin (fun t ↦ p (Real.log t)) s := by
  obtain ⟨τ, hτ⟩ := sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_section (F := F) (S := S)
  have hpos : ∃ (ψ : PontryaginDual Jₛ) (z : ℂ), 0 < z.re ∧ chartₛ(χ) s = chartₛ(ψ) z :=
    ⟨χ, s, hs, rfl⟩
  rw [sLocalIdelicZFunction_eq_integral _ hpos, ← sLocalThetaMellinIntegral_eq_zeta _ hpos,
    ← sLocalRadialMellinIntegral_eq_theta τ hτ _ χ s hs]
  rw [← sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_mellin]
  apply integral_congr_ae (.of_forall fun t ↦ ?_)
  let g : Jₛ := QuotientGroup.mk (τ t)
  have ht : mₛ g = t := hτ t
  change thetaAt(χ₁(χ)) f g * ((χ g : ℂ) * (((mₛ g).val : ℝ) : ℂ) ^ s) = _
  rw [hp, ht]
  field_simp [Circle.coe_ne_zero]

/-- Schwartz–Bruhat membership of a function depending only on the norm can be checked
on the positive-real norm quotient. The projector to the trivial character fixes
such a function. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_quotient
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (u : ℝ≥0ˣ → ℂ) :
    (fun g ↦ u (m g)) ∈ schwartzBruhatSubmodule G ↔ u ∈ schwartzBruhatSubmodule ℝ≥0ˣ := by
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let μ : Measure K := Measure.haarMeasure ⊤
  let P := schwartzBruhatIsotypicProjector m hm μ 1
  obtain ⟨w, e, hw, he⟩ := schwartzBruhat_positiveReal_isotype_equiv m hm μ τ hτ 1
  have hw' (f : SchwartzBruhat ℝ≥0ˣ) (g : G) : w f g = f (m g) := by
    let k : K := ⟨g / τ (m g), by change m (g / τ (m g)) = 1; rw [map_div, hτ, div_self']⟩
    have h := hw f k (m g)
    simpa only [show (k : G) * τ (m g) = g from div_mul_cancel _ _, PontryaginDual.one_apply,
      Circle.coe_one, star_one, one_mul] using h
  have fix (f : SchwartzBruhat G) (v : ℝ≥0ˣ → ℂ) (hv : ∀ g, f g = v (m g)) : P f = f := by
    apply schwartzBruhatIsotypicProjector_apply_isotype
    apply (mem_actionIsotype _ _ _).mpr
    intro k
    apply Subtype.ext
    funext g
    change schwartzBruhatTranslationAction (G := G) (k : G) f g = ((1 : PontryaginDual K) k : ℂ) * f g
    rw [schwartzBruhatTranslationAction_apply, hv, map_mul, map_inv, show m k.val = 1 from k.property, inv_one, one_mul,
      PontryaginDual.one_apply, Circle.coe_one, one_mul, hv]
  constructor
  · intro h
    let f : SchwartzBruhat G := ⟨_, h⟩
    obtain ⟨g, hg⟩ := e.surjective (P.ker.mkQ f)
    have hclass : P.ker.mkQ (w g) = P.ker.mkQ f := (he g).symm.trans hg
    have hP : P (w g) = P f := by
      exact sub_eq_zero.mp ((map_sub P (w g) f).symm.trans (LinearMap.mem_ker.mp ((Submodule.Quotient.eq P.ker).mp hclass)))
    rw [fix _ _ (hw' g), fix f u (fun _ ↦ rfl)] at hP
    have hu : g.val = u := by
      funext t
      calc
        _ = g (m (τ t)) := congrArg g (hτ t).symm
        _ = w g (τ t) := (hw' g _).symm
        _ = f (τ t) := congrArg (fun H : SchwartzBruhat G ↦ H (τ t)) hP
        _ = u t := congrArg u (hτ t)
    exact hu ▸ g.property
  · intro h
    let f : SchwartzBruhat ℝ≥0ˣ := ⟨u, h⟩
    exact (show (w f).val = (fun g ↦ u (m g)) from funext (hw' f)) ▸ (w f).property

/-- Unitary character multiplication preserves ordinary Schwartz–Bruhat membership
in each direction. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_unitary
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (χ : PontryaginDual G) (f : G → ℂ) :
    (fun g ↦ (χ g : ℂ) * f g) ∈ schwartzBruhatSubmodule G ↔ f ∈ schwartzBruhatSubmodule G := by
  have mul (η : PontryaginDual G) (h : SchwartzBruhat G) :
      (fun g ↦ (η g : ℂ) * h g) ∈ schwartzBruhatSubmodule G := by
    obtain ⟨M, hM⟩ := schwartzBruhat_mul_unitaryCharacter η
    exact (show (M h).val = _ from funext (hM h)) ▸ (M h).property
  refine ⟨fun h ↦ ?_, fun h ↦ mul χ ⟨f, h⟩⟩
  have hi := mul χ⁻¹ ⟨_, h⟩
  change (fun g ↦ ((χ⁻¹ g : Circle) : ℂ) * ((χ g : ℂ) * f g)) ∈ _ at hi
  convert hi using 1
  funext g
  change f g = ((χ g)⁻¹ : Circle) * ((χ g : ℂ) * f g)
  rw [Circle.coe_inv, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]

/-- A character-homogeneous function has all-exponent decay exactly when its radial
logarithmic profile, after removing the unitary character, does. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_profile
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (χ : PontryaginDual G) (f : G → ℂ) (p : ℝ → ℂ)
    (hp : ∀ g, (χ g : ℂ) * f g = p (Real.log ((m g).val : ℝ))) :
    f ∈ modulatedExponentialDecaySubmodule m univ ↔ p ∈ logExponentialDecaySubmodule univ := by
  let idM := ContinuousMonoidHom.id ℝ≥0ˣ
  let u (t : ℝ≥0ˣ) := p (Real.log (t.val : ℝ))
  have hweight (a : ℝ) :
      modulationWeight m a f ∈ schwartzBruhatSubmodule G ↔
        modulationWeight idM a u ∈ schwartzBruhatSubmodule ℝ≥0ˣ := by
    rw [← sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_unitary χ]
    have he (g : G) : (χ g : ℂ) * modulationWeight m a f g = modulationWeight idM a u (m g) := by
      change (χ g : ℂ) * (((((m g).val : ℝ) ^ a : ℝ) : ℂ) * f g) =
        ((((m g).val : ℝ) ^ a : ℝ) : ℂ) * p (Real.log ((m g).val : ℝ))
      rw [mul_left_comm, hp]
    rw [funext he]
    exact sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_quotient m hm τ hτ _
  have hmem : f ∈ modulatedExponentialDecaySubmodule m univ ↔
      u ∈ modulatedExponentialDecaySubmodule idM univ := by
    simp only [modulatedExponentialDecaySubmodule, Submodule.mem_iInf, Submodule.mem_comap]
    exact forall_congr' fun a ↦ hweight a.val
  rw [hmem]
  obtain ⟨e, he⟩ := positiveRealExponentialDecay_log_equiv univ ordConnected_univ univ_nonempty
  constructor
  · intro hu
    let U : ModulatedExponentialDecay idM univ := ⟨u, hu⟩
    let b := e.symm U
    have hlog (t : ℝ≥0ˣ) : b.val (Real.log (t.val : ℝ)) = u t :=
      (he b t).symm.trans (congrArg (fun w : ModulatedExponentialDecay idM univ ↦ w.val t) (e.apply_symm_apply U))
    have hval : b.val = p := by
      funext x
      let t : ℝ≥0ˣ := Units.mk0 (Real.exp x).toNNReal (by positivity)
      have ht : Real.log (t.val : ℝ) = x := by
        change Real.log ((Real.exp x).toNNReal : ℝ) = x
        rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
      exact ht ▸ hlog t
    exact hval ▸ b.property
  · intro h
    let b : PositiveRealExponentialDecay univ := ⟨p, h⟩
    exact (show (e b).val = u from funext (he b)) ▸ (e b).property

/-- Multiplication of a polar-free representative by an S-idelic real norm power
translates its entire zeta chart. On the common half-plane this follows on the
integrands, and the identity theorem extends it to the whole plane. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_shift
    (r : RealModels) (c : ComplexModels) (χ : PontryaginDual Jₛ)
    (f : sAdelePolarFree S r c) (d : ℝ) :
    ∃ b : sAdelePolarFree S r c, ∀ s : ℂ,
      sLocalIdelicZFunction b.val (chartₛ(χ) s) =
        sLocalIdelicZFunction f.val (chartₛ(χ) (s + d)) := by
  let η := chartₛ((1 : PontryaginDual Jₛ)) (d : ℂ)
  obtain ⟨M, hM⟩ := sAdelePolarFree_quasiCharacter_mul r c η
  let b := M f
  have he (s : ℂ) (hs : 0 < s.re) (hd : 0 < (s + d).re) :
      sLocalIdelicZFunction b.val (chartₛ(χ) s) =
        sLocalIdelicZFunction f.val (chartₛ(χ) (s + d)) := by
    rw [sLocalIdelicZFunction_eq_integral _ ⟨χ, s, hs, rfl⟩,
      sLocalIdelicZFunction_eq_integral _ ⟨χ, s + d, hd, rfl⟩]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    let g : Jₛ := QuotientGroup.mk x
    let N : ℂ := ((mₛ g).val : ℝ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
    change b.val (Multiplicative.ofAdd x.val) * (chartₛ(χ) s) g =
      f.val (Multiplicative.ofAdd x.val) * (chartₛ(χ) (s + d)) g
    rw [hM]
    change ((1 : ℂ) * N ^ (d : ℂ) * _) * ((χ g : ℂ) * N ^ s) =
      _ * ((χ g : ℂ) * N ^ (s + d))
    rw [Complex.cpow_add _ _ hN]
    ring
  have h1 := sLocalIdelicZFunction_entire_of_polarFree r c b.val b.property χ
  have h2 := sLocalIdelicZFunction_entire_of_polarFree r c f.val f.property χ
  have h2' : AnalyticOnNhd ℂ (fun s : ℂ ↦ sLocalIdelicZFunction f.val (chartₛ(χ) (s+d))) univ :=
    fun z _ ↦ (h2 _ (mem_univ _)).comp (analyticAt_id.add analyticAt_const)
  let t : ℝ := |d| + 1
  have hne : ∀ᶠ z : ℂ in 𝓝 (t : ℂ), 0 < z.re ∧ 0 < (z+d).re := by
    apply Filter.Eventually.and
    · apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      change 0 < |d| + 1
      positivity
    · apply (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_id.add continuous_const))).mem_nhds
      change 0 < (|d| + 1) + d
      linarith [neg_abs_le d]
  exact ⟨b, fun z ↦ h1.eqOn_of_preconnected_of_eventuallyEq h2' isPreconnected_univ
    (mem_univ (t : ℂ)) (hne.mono fun s hs ↦ he s hs.1 hs.2) (mem_univ z)⟩

/-- The zeta transform of a polar-free representative is Schwartz on every closed
vertical strip. Translate that strip into the positive half-plane using a norm power. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_bergman
    (r : RealModels) (c : ComplexModels) (χ : PontryaginDual Jₛ) (f : sAdelePolarFree S r c) :
    (fun z ↦ sLocalIdelicZFunction f.val (chartₛ(χ) z)) ∈ schwartzBergmanSubmodule univ := by
  let Z := fun z ↦ sLocalIdelicZFunction f.val (chartₛ(χ) z)
  have hZ := sLocalIdelicZFunction_entire_of_polarFree r c f.val f.property χ
  refine ⟨fun z hz ↦ (hz (mem_univ _)).elim, hZ.differentiableOn, ?_⟩
  intro a b hab _ N
  let d := a - 1
  obtain ⟨g, hg⟩ := sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_shift r c χ f d
  let G := fun z ↦ sLocalIdelicZFunction g.val (chartₛ(χ) z)
  have hstrip : UniformlySchwartzOnStrip G (1/2) (b-d+1) := by
    simpa only [iteratedDeriv_zero] using sLocalIdelicZFunction_schwartzOnStrip g.val χ
      (1/2) (b-d+1) (by norm_num) (by dsimp [d]; linarith) 0
  obtain ⟨C, hC, htail⟩ := hstrip.2.2 (1/4) (by norm_num) (by dsimp [d]; linarith) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  let A := max |a| |b|
  let M := max T (max 1 A)
  let K := Complex.reProdIm (Icc a b) (Icc (-M) M)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun z : ℂ ↦ ‖z ^ N * Z z‖) K :=
    ((continuous_id.pow N).continuousOn.mul (hZ.differentiableOn.continuousOn.mono (subset_univ K))).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc
  refine ⟨max B (2 ^ N * C), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  by_cases hy : |z.im| ≤ M
  · exact (hB ⟨z, ⟨hz, abs_le.mp hy⟩, rfl⟩).trans (le_max_left _ _)
  have hy' := (lt_of_not_ge hy).le
  have hy1 : 1 ≤ |z.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hy')
  have hy0 : 0 < |z.im| := zero_lt_one.trans_le hy1
  have hz' : z.re ∈ Icc a b := hz
  have hdec := hT |z.im| ((le_max_left _ _).trans hy') z.im rfl (z.re-d)
    (show z.re-d ∈ Icc (1/2+1/4) (b-d+1-1/4) from ⟨by dsimp [d]; linarith [hz'.1], by linarith [hz'.2]⟩)
  have eqZ : G (((z.re - d : ℝ) : ℂ) + z.im * Complex.I) = Z z := by
    rw [show G _ = _ from hg _, show (((z.re - d : ℝ) : ℂ) + z.im * Complex.I) + d = z by
      push_cast; rw [sub_add_eq_add_sub, sub_add_cancel, Complex.re_add_im]]
  rw [eqZ] at hdec
  have hnorm : ‖z‖ ≤ 2 * |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    have hA : |z.re| ≤ A := abs_le.mpr
      ⟨by dsimp [A]; linarith [le_abs_self (-a), abs_neg a, le_max_left |a| |b|, hz'.1],
        hz'.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
    linarith [hA.trans ((le_max_right 1 A).trans ((le_max_right T _).trans hy'))]
  have hpow : |z.im| ^ N ≤ |z.im| ^ (N + 1) := pow_le_pow_right₀ hy1 (by omega)
  apply le_trans _ (le_max_right _ _)
  change ‖z ^ N * Z z‖ ≤ _
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * |z.im|) ^ N * (C / |z.im| ^ N) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (hdec.trans
        (div_le_div_of_nonneg_left hC.le (pow_pos hy0 _) hpow)) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * C := by rw [mul_pow]; field_simp

/-- Agreement of two zeta functions on one chart gives agreement of their homogeneous
theta functions by Lemma 5.1.2.2. The chart covers every quasicharacter with the
prescribed restriction to the norm-one subgroup. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_eq_theta
    (χ : PontryaginDual Jₛ) (f b : ℬₛ)
    (h : ∀ z : ℂ, sLocalIdelicZFunction f (chartₛ(χ) z) = sLocalIdelicZFunction b (chartₛ(χ) z)) :
    thetaAt(χ₁(χ)) f = thetaAt(χ₁(χ)) b := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply LinearMap.mem_ker.mp
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (χ₁(χ)) (f-b)).mpr
  intro d hd
  let η := d.val * (circleToComplex).comp χ⁻¹
  obtain ⟨z, hz, _⟩ := existsUnique_complexPower (η.comp τ)
  have eqChart : chartₛ(χ) z = d.val := by
    apply ContinuousMonoidHom.ext
    intro g
    let t := mₛ g
    let k : J₁ := ⟨g / τ t, by change mₛ (g / τ t) = 1; rw [map_div, hτ]; exact div_self' _⟩
    have hg : k.val * τ t = g := div_mul_cancel _ _
    have hk : d.val k.val = (χ k.val : ℂ) := hd k
    have hdt : d.val (τ t) * (χ (τ t) : ℂ)⁻¹ = (((t.val : ℝ) : ℂ) ^ z) := by
      have ht := hz t
      change d.val (τ t) * ((((χ (τ t))⁻¹ : Circle) : ℂ)) = _ at ht
      rwa [Circle.coe_inv] at ht
    change (χ g : ℂ) * (((t.val : ℝ) : ℂ) ^ z) = d.val g
    rw [← hdt, ← hg, map_mul, map_mul, Circle.coe_mul, hk]
    field_simp [Circle.coe_ne_zero]
  rw [map_sub]
  change sLocalIdelicZFunction f d.val - sLocalIdelicZFunction b d.val = 0
  rw [← eqChart]
  exact sub_eq_zero.mpr (h z)

/-- Removing the unitary character from a homogeneous theta function leaves a function
of the logarithmic norm. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_exists_profile
    (χ : PontryaginDual Jₛ) (f : ℬₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) :
    ∃ p : ℝ → ℂ, ∀ g : Jₛ,
      (χ g : ℂ) * thetaAt(χ₁(χ)) f g = p (Real.log ((mₛ g).val : ℝ)) := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (t : ℝ≥0ˣ) : E (Real.log (t.val : ℝ)) = t :=
    Units.ext (NNReal.eq (Real.exp_log (by exact_mod_cast Units.zero_lt t)))
  refine ⟨fun x ↦ (χ (τ (E x)) : ℂ) * thetaAt(χ₁(χ)) f (τ (E x)), fun g ↦ ?_⟩
  dsimp only
  rw [he (mₛ g)]
  let t := mₛ g
  let k : J₁ := ⟨g / τ t, by change mₛ (g / τ t) = 1; rw [map_div, hτ]; exact div_self' _⟩
  have hk : k.val⁻¹ * g = τ t := (inv_mul_eq_iff_eq_mul).mpr (div_mul_cancel g (τ t)).symm
  let := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hc := sLocalHomogeneousAdelicTheta_homogeneous F S (sLocalNormOneQuotientMeasure F S) (χ₁(χ)) f k g
  change thetaAt(χ₁(χ)) f (k.val⁻¹ * g) = (χ k.val : ℂ) * thetaAt(χ₁(χ)) f g at hc
  rw [hk] at hc
  change _ = (χ (τ t) : ℂ) * thetaAt(χ₁(χ)) f (τ t)
  rw [hc, ← mul_assoc, ← Circle.coe_mul, ← map_mul]
  congr 3
  change g = τ t * (g / τ t)
  exact (div_mul_cancel g (τ t)).symm.trans (mul_comm (g / τ t) (τ t))
/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_continue {G H : ℂ → ℂ}
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

/-- The inverse Mellin profile of an entire Schwartz–Bergman function lifts through the
trivial theta map and can then be twisted to the chosen component. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_lift
    (r : RealModels) (c : ComplexModels) (χ : PontryaginDual Jₛ) (p : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : Jₛ, thetaAt(χ₁(χ)) f.val g =
      (χ g : ℂ)⁻¹ * p.val (Real.log ((mₛ g).val : ℝ)) := by
  obtain ⟨a, ha⟩ := sLocalHomogeneousTheta_trivial_exists_polarFree (S := S) r c p
  obtain ⟨T, hT⟩ := sAdelePolarFree_quasiCharacter_mul r c ((circleToComplex).comp χ⁻¹)
  refine ⟨T a, fun g ↦ ?_⟩
  rw [sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_twist (χ₁(χ)) χ (fun _ ↦ rfl) a.val
    (T a).val (hT a), ha]

/-- The S-idele quotient has the separation and countability properties used by
the Schwartz–Bruhat projector on a split locally compact group. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_group :
    T2Space Jₛ ∧ SecondCountableTopology Jₛ ∧ LocallyCompactSpace Jₛ := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F) := inferInstanceAs
    (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  let : SecondCountableTopology Aₛ := inferInstanceAs
    (SecondCountableTopology (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Aₛˣ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : LocallyCompactSpace Aₛˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Apply the split-group decay criterion to the S-idele quotient with its proper norm. -/
private theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial_mem
    (χ : PontryaginDual Jₛ) (f : ℬₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) (p : ℝ → ℂ)
    (hp : ∀ g : Jₛ, (χ g : ℂ) * thetaAt(χ₁(χ)) f g = p (Real.log ((mₛ g).val : ℝ))) :
    (⇑(thetaAt(χ₁(χ)) f) : Jₛ → ℂ) ∈ modulatedExponentialDecaySubmodule
      ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ univ ↔ p ∈ logExponentialDecaySubmodule univ := by
  obtain ⟨ht₂, hsc, hlc⟩ := sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_group (F := F) (S := S)
  let m : Jₛ →ₜ* ℝ≥0ˣ := ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩
  obtain ⟨t₀, ht₀⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hm : IsModulation m := ⟨isProperMap_sIdeleQuotientNorm F S, τ t₀, (hτ t₀).trans_ne ht₀⟩
  let v : Jₛ → ℂ := thetaAt(χ₁(χ)) f
  have hτ' : RightInverse τ m := hτ
  have hp' : ∀ g, (χ g : ℂ) * v g = p (Real.log ((m g).val : ℝ)) := hp
  change v ∈ modulatedExponentialDecaySubmodule m univ ↔ p ∈ logExponentialDecaySubmodule univ
  with_reducible
    exact sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_profile (G := Jₛ) m hm τ hτ' χ v p hp'

/-- Paper: Proposition 5.3.4.4(1) and (3), p. 264.
On the component of χ, a zeta transform is entire exactly when the homogeneous theta
function has exponential decay at every real exponent. Its covariance is the
norm-one isotype property already supplied by §2.3. -/
theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      (⇑(thetaAt(χ₁(χ)) f) : Jₛ → ℂ) ∈ modulatedExponentialDecaySubmodule
        ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ univ := by
  let r (w : {w : InfinitePlace F // w.IsReal}) :
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)} :=
    ⟨InfinitePlace.Completion.ringEquivRealOfIsReal w.property,
      (InfinitePlace.Completion.isometryEquivRealOfIsReal w.property).toHomeomorph.isHomeomorph⟩
  let c (w : {w : InfinitePlace F // w.IsComplex}) :
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)} :=
    ⟨InfinitePlace.Completion.ringEquivComplexOfIsComplex w.property,
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex w.property).toHomeomorph.isHomeomorph⟩
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨M, hM, _⟩ := existsUnique_positiveRealFourierMellin univ isOpen_univ
    (ordConnected_univ : OrdConnected (univ : Set ℝ)) univ_nonempty
  constructor
  · intro ha
    obtain ⟨a, ha'⟩ := (sLocalIdelicZFunction_entire_iff_eq_polarFree r c χ f).mp ha
    let B : SchwartzBergman univ := ⟨_, sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_bergman r c χ a⟩
    let p := M.symm B
    obtain ⟨b, hb⟩ := sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_lift r c χ p
    have hchart (z : ℂ) : sLocalIdelicZFunction f (chartₛ(χ) z) = sLocalIdelicZFunction b.val (chartₛ(χ) z) := by
      apply sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_continue
        (sLocalIdelicZFunction_meromorphic f χ) (sLocalIdelicZFunction_meromorphic b.val χ) _ z
      intro s hs
      calc
        _ = B.val s := ha' s
        _ = (M p).val s := congrArg (fun v : SchwartzBergman univ ↦ v.val s) (M.apply_symm_apply B).symm
        _ = _ := hM p s (mem_univ _)
        _ = _ := (sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial χ b.val p.val hb s hs).symm
    rw [sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_eq_theta χ f b.val hchart]
    refine (sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial_mem χ b.val τ hτ p.val ?_).mpr p.property
    intro g
    rw [hb, mul_inv_cancel_left₀ (Circle.coe_ne_zero _)]
  · intro hd
    obtain ⟨p, hp⟩ := sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_exists_profile χ f τ hτ
    have hmem := (sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial_mem χ f τ hτ p hp).mp hd
    let v : PositiveRealExponentialDecay univ := ⟨p, hmem⟩
    have hrad : ∀ g : Jₛ, thetaAt(χ₁(χ)) f g = (χ g : ℂ)⁻¹ * p (Real.log ((mₛ g).val : ℝ)) := by
      intro g
      rw [← hp, inv_mul_cancel_left₀ (Circle.coe_ne_zero _)]
    have hdiff : Differentiable ℂ (M v).val := by
      simpa only [preimage_univ, differentiableOn_univ] using (M v).property.2.1
    have eqB : (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) = (M v).val := by
      funext z
      apply sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_continue
        (sLocalIdelicZFunction_meromorphic f χ) (fun z _ ↦ (hdiff.analyticAt z).meromorphicNFAt) _ z
      exact fun s hs ↦ (sLocalIdelicZFunction_entire_iff_theta_exponentialDecay_radial χ f p hrad s hs).trans
        (hM v s (mem_univ _)).symm
    rw [eqB]
    exact fun z _ ↦ hdiff.analyticAt z

/-- Mellin integration turns a compact unit average followed by dilation into the
average of the character times the scalar dilation. -/
private theorem sLocalIdelicZFunction_principalValue_average {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (U : Subgroup G) (π : G) (f : G → ℂ) (hf : Continuous f) (c : G →ₜ* ℂ)
    (hfc : Integrable (fun x ↦ f x * c x) μ) (hc : IntegrableOn c U μ) :
    (∫ x, (f x - (μ.real U : ℂ)⁻¹ *
      ∫ u in U, f (u⁻¹ * (π⁻¹ * x)) ∂μ) * c x ∂μ) =
      (1 - (μ.real U : ℂ)⁻¹ * (∫ u in U, c u ∂μ) * c π) *
        ∫ x, f x * c x ∂μ := by
  let b (u x : G) := f (u⁻¹ * (π⁻¹ * x)) * c x
  let h (x : G) := f x * c x
  have hb (u x : G) : b u x = (c u * c π) * h ((π * u)⁻¹ * x) := by
    have hx : x = (π * u) * ((π * u)⁻¹ * x) := by group
    unfold b h
    rw [← mul_assoc, ← mul_inv_rev, congrArg c hx, map_mul, map_mul]
    ring
  have hcont : Continuous (Function.uncurry b) := by
    unfold Function.uncurry b
    fun_prop
  have hnorm (u : G) : (∫ x, ‖h ((π * u)⁻¹ * x)‖ ∂μ) = ∫ x, ‖h x‖ ∂μ :=
    integral_mul_left_eq_self (μ := μ) (fun x ↦ ‖h x‖) _
  have hh : Integrable h μ := hfc
  have hi : Integrable (Function.uncurry b) ((μ.restrict U).prod μ) := by
    refine (integrable_prod_iff hcont.aestronglyMeasurable).mpr ⟨.of_forall fun u ↦ ?_, ?_⟩
    · simpa only [Function.uncurry_apply_pair, Function.comp_apply, hb] using
        ((measurePreserving_mul_left μ (π * u)⁻¹).integrable_comp_of_integrable hh).const_mul (c u * c π)
    · simp only [Function.uncurry_apply_pair, hb, norm_mul, integral_const_mul, hnorm]
      exact (hc.norm.mul_const _).mul_const _
  have hsub (x : G) : (f x - (μ.real U : ℂ)⁻¹ * ∫ u in U, f (u⁻¹ * (π⁻¹ * x)) ∂μ) * c x =
      h x - (μ.real U : ℂ)⁻¹ * ∫ u in U, b u x ∂μ := by
    rw [sub_mul, mul_assoc, ← integral_mul_const]
  simp_rw [hsub]
  have hbi : Integrable (fun x ↦ ∫ u in U, b u x ∂μ) μ := hi.integral_prod_right
  rw [integral_sub hh (hbi.const_mul _), integral_const_mul,
    ← integral_integral_swap hi]
  simp_rw [hb, integral_const_mul, integral_mul_left_eq_self, integral_mul_const]
  ring

/-- The integral of a character over the integer units is zero unless the character
is trivial there. -/
private theorem sLocalIdelicZFunction_principalValue_units {G : Type*} [CommGroup G]
    [MeasurableSpace G] [MeasurableMul G] [TopologicalSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (U : Subgroup G) (hU : MeasurableSet (U : Set G))
    (c : G →ₜ* ℂ) :
    (∫ u in U, c u ∂μ) = if ∀ u ∈ U, c u = 1 then (μ.real U : ℂ) else 0 := by
  classical
  split_ifs with h
  · rw [setIntegral_congr_fun hU h, setIntegral_const, Complex.real_smul, mul_one]
  · obtain ⟨a, ha, hne⟩ := not_forall.mp h |>.imp fun a h ↦ not_imp.mp h
    have he : (fun x : G ↦ a * x) ⁻¹' (U : Set G) = U := by
      ext x
      exact U.mul_mem_cancel_left ha
    have hv := (measurePreserving_mul_left μ a).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft a).measurableEmbedding (fun u ↦ c u) (U : Set G)
    rw [he] at hv
    simp only [map_mul, integral_const_mul] at hv
    exact (mul_eq_zero.mp (show (c a - 1) * (∫ u in U, c u ∂μ) = 0 by linear_combination hv)).resolve_left
      (sub_ne_zero.mpr hne)

/-- Restricting the global norm chart to a finite component gives the local norm chart. -/
private theorem sLocalIdelicZFunction_principalValue_chart (χ : PontryaginDual Jₛ) (v : S) :
    ∃ η : PontryaginDual (v.val.adicCompletion F)ˣ, ∀ z, sLocalFiniteRestriction v (chartₛ(χ) z) =
      quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η) z := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
          ((v : S) → v.val.adicCompletion F)).symm (1, ContinuousMulEquiv.piUnits.symm
            (@Pi.mulSingle _ _ _ (Classical.decEq _) v g))),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  refine ⟨χ.comp i, fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hn := sLocalFiniteRestriction_norm v g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) *
    (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at hn
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
  exact congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ z) hn

/-- The local principal value multiplies the zeta integral by the inverse Euler factor. -/
private theorem sLocalIdelicZFunction_principalValue_finite (v : S) (f : ℬ(v.val.adicCompletion F))
    (χ : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) :
    letI : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
    let c := sLocalFiniteRestriction v (chartₛ(χ) z)
    let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
    localIdelicZetaIntegral μ (fun x ↦ finitePlacePrincipalValue v.val f (Multiplicative.ofAdd x)) c =
      localIdelicZetaIntegral μ (fun x ↦ f (Multiplicative.ofAdd x)) c / finiteLocalEulerFactor v.val c := by
  let : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  intro c μ
  let K := v.val.adicCompletion F
  let O := v.val.adicCompletionIntegers F
  let : ProperSpace K := properSpace_adicCompletion v.val
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
  let h (u : Kˣ) := f (Multiplicative.ofAdd u.val)
  have hcont : Continuous h := (schwartzBruhat_continuous f).comp (continuous_ofAdd.comp Units.continuous_val)
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  have hf : Integrable (fun u ↦ h u * c u) μ := by
    dsimp only [c]
    rw [hη]
    exact finiteLocalIdelicZetaIntegral_integrable v.val f η hz
  have hK : IsCompact (O.units : Set Kˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v.val))
  have hO : IsOpen (O.units : Set Kˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hm : (μ.real O.units : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (finitePlacePrincipalValue_integrable v.val π f (Multiplicative.ofAdd 0)).1.ne'
  have hram : (∀ u : Oˣ, c (Units.map O.subtype.toMonoidHom u) = 1) ↔ ∀ u ∈ O.units, c u = 1 := by
    constructor
    · intro H u hu
      let t : Oˣ := ⟨⟨u.val, hu.1⟩, ⟨u.inv, hu.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
      exact H t
    · intro H u
      exact H _ ⟨u.val.property, u.inv.property⟩
  let avg (x : Kˣ) := ∫ u in O.units, h (u⁻¹ * (π⁻¹ * x)) ∂μ
  have hev (x : Kˣ) : finitePlacePrincipalValue v.val f (Multiplicative.ofAdd x.val) =
      h x - (μ.real O.units : ℂ)⁻¹ * avg x :=
    finitePlacePrincipalValue_spec v.val π hp.choose_spec f _
  have hI := sLocalIdelicZFunction_principalValue_average μ O.units π h hcont c hf
    (c.continuous.continuousOn.integrableOn_compact hK)
  let Z := ∫ x, h x * c x ∂μ
  have hF : 1 - (μ.real O.units : ℂ)⁻¹ * (∫ u in O.units, c u ∂μ) * c π =
      (finiteLocalEulerFactor v.val c)⁻¹ := by
    rw [sLocalIdelicZFunction_principalValue_units μ O.units hO.measurableSet c]
    unfold finiteLocalEulerFactor
    rw [hram]
    split_ifs <;> simp only [inv_inv, inv_mul_cancel₀ hm, one_mul, mul_zero, zero_mul, sub_zero, inv_one]
    rfl
  calc
    _ = ∫ x, (h x - (μ.real O.units : ℂ)⁻¹ * avg x) * c x ∂μ :=
      integral_congr_ae (.of_forall fun x ↦ congrArg (· * c x) (hev x))
    _ = (1 - (μ.real O.units : ℂ)⁻¹ * (∫ u in O.units, c u ∂μ) * c π) * Z := hI
    _ = _ := (congrArg (· * Z) hF).trans (mul_comm _ _)

/-- Assemble the archimedean product in the test space of the infinite adeles. -/
private theorem sLocalIdelicZFunction_principalValue_archTest
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) :
    ∃ arch : ℬ(A∞), ∀ x : A∞, arch (Multiplicative.ofAdd x) =
      ∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x w)) := by
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) := (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨a₀, ha⟩ := sLocalIdelicZFunction_principalValue_productTest G a
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  exact ⟨⟨a₀.val ∘ e, schwartzBruhat_pullback_mem e a₀⟩, fun x ↦ ha (e (Multiplicative.ofAdd x))⟩

/-- Tate's product formula and the tensor action of principal value give the identity on pure tests. -/
private theorem sLocalIdelicZFunction_principalValue_pure (T : Finset V) (hT : T ⊆ S)
    (χ : PontryaginDual Jₛ) (z : ℂ) (hz : 0 < z.re) (f : ℬₛ)
    (a : (w : InfinitePlace F) → ℬ(w.Completion)) (b : (v : S) → ℬ(v.val.adicCompletion F))
    (hf : ∀ x : Aₛ, f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b v (Multiplicative.ofAdd (x.2 v))) :
    let c := chartₛ(χ) z
    sLocalIdelicZetaIntegral (sAdelePrincipalValue F hT f) c = sLocalIdelicZetaIntegral f c /
      ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) else 1 := by
  classical
  intro c
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  obtain ⟨a₀, ha⟩ := sLocalIdelicZFunction_principalValue_archTest a
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let b' (v : S) := if v.val ∈ T then finitePlacePrincipalValue v.val (b v) else b v
  have hpack : f = e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v)) := by
    apply Subtype.ext
    funext x
    exact (hf x.toAdd).trans (((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b x.toAdd).trans
      (congrArg (· * _) (ha x.toAdd.1))).symm
  have hpv (x : Aₛ) : sAdelePrincipalValue F hT f (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b' v (Multiplicative.ofAdd (x.2 v)) := by
    rw [hpack, sAdelePrincipalValue_tmul hT a₀ b]
    exact ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b' x).trans
      (congrArg (· * _) (ha x.1))
  rw [sLocalIdelicZetaIntegral_pureTensor c ⟨χ, z, hz, rfl⟩ _ a b' hpv,
    sLocalIdelicZetaIntegral_pureTensor c ⟨χ, z, hz, rfl⟩ f a b hf, mul_div_assoc]
  apply congrArg (_ * ·)
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : v.val ∈ T
  · simp only [b', hv, ite_true]
    exact sLocalIdelicZFunction_principalValue_finite v (b v) χ z hz
  · simp only [b', hv, ite_false, div_one]

/-- The reciprocal of a finite Euler factor is entire along a norm chart. -/
private theorem sLocalIdelicZFunction_principalValue_analytic (χ : PontryaginDual Jₛ) (v : S) (t : ℂ) :
    AnalyticAt ℂ (fun z ↦ (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹) t := by
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  let K := v.val.adicCompletion F
  let O := v.val.adicCompletionIntegers F
  let c := quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) ((circleToComplex).comp η)
  have hu (u : Oˣ) (z : ℂ) : c z (Units.map O.subtype.toMonoidHom u) =
      (η (Units.map O.subtype.toMonoidHom u) : ℂ) := by
    let g := Units.map O.subtype.toMonoidHom u
    have hmem : g ∈ O.units := ⟨u.val.property, u.inv.property⟩
    have hnorm := Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hmem)
    change (η g : ℂ) * (‖g.val‖ : ℂ) ^ z = (η g : ℂ)
    simp [hnorm]
  let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
  have hc (z : ℂ) : (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹ =
      if ∀ u : Oˣ, (η (Units.map O.subtype.toMonoidHom u) : ℂ) = 1 then 1 - c z π else 1 := by
    rw [hη]
    change (finiteLocalEulerFactor v.val (c z))⁻¹ = _
    have H : (∀ u : Oˣ, c z (Units.map O.subtype.toMonoidHom u) = 1) ↔
        ∀ u : Oˣ, (η (Units.map O.subtype.toMonoidHom u) : ℂ) = 1 :=
      forall_congr' fun u ↦ by rw [hu u z]
    rw [finiteLocalEulerFactor, H]
    split_ifs <;> simp only [inv_inv, inv_one]
    rfl
  simp_rw [hc]
  split_ifs
  · have hn : (‖π.val‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)
    exact analyticAt_const.sub (analyticAt_const.mul ((differentiable_id.const_cpow (Or.inl hn)).analyticAt t))
  · exact analyticAt_const

/-- Equality on the positive half-plane continues to equality away from a discrete set. -/
private theorem sLocalIdelicZFunction_principalValue_continue {f g : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hg : MeromorphicOn g univ) (h : ∀ z : ℂ, 0 < z.re → f z = g z) :
    f =ᶠ[codiscrete ℂ] g := by
  have ho : meromorphicOrderAt (f - g) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.mpr
  intro z
  have hz := (hf.sub hg).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ (1 : ℂ)) (mem_univ z) ho
  exact (meromorphicOrderAt_eq_top_iff.mp hz).mono fun _ he ↦ sub_eq_zero.mp he

/-- Paper: Proposition 5.3.4.5(1), p. 264.
Applying the principal value at selected finite places divides the zeta function
by their Euler factors as a meromorphic identity. -/
theorem sLocalIdelicZFunction_principalValue (T : Finset V) (hT : T ⊆ S)
    (f : ℬₛ) (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalIdelicZFunction (sAdelePrincipalValue F hT f) c =
        sLocalIdelicZFunction f c /
          ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
            else 1 := by
  classical
  let d (z : ℂ) := ∏ v : S, if v.val ∈ T then
    (finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)))⁻¹ else 1
  have hd (z : ℂ) : d z = (∏ v : S, if v.val ∈ T then
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z)) else 1)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro v _
    split_ifs <;> simp only [inv_one]
  have ha (z : ℂ) : AnalyticAt ℂ d z := by
    dsimp only [d]
    apply Finset.analyticAt_fun_prod
    intro v _
    by_cases h : v.val ∈ T
    · simpa only [h, ite_true] using sLocalIdelicZFunction_principalValue_analytic χ v z
    · simp only [h, ite_false]
      exact analyticAt_const
  let P : ℬₛ →L[ℂ] ℬₛ := ⟨sAdelePrincipalValue F hT, (sAdelePrincipalValue_isClosedEmbedding hT).continuous⟩
  have hright (z : ℂ) (hz : 0 < z.re) : sLocalIdelicZetaIntegral (P f) (chartₛ(χ) z) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) z) * d z := by
    let c := chartₛ(χ) z
    obtain ⟨L, hL⟩ := sLocalIdelicZetaIntegral_tempered c ⟨χ, z, hz, rfl⟩
    let Λ := L.comp P - d z • L + L
    have he := sLocalIdelicZetaIntegral_eq_of_pureTensor c ⟨χ, z, hz, rfl⟩ Λ (fun g a b hg ↦ by
      change L (P g) - d z * L g + L g = _
      have hpure : sLocalIdelicZetaIntegral (P g) c = sLocalIdelicZetaIntegral g c * d z := by
        rw [hd, ← div_eq_mul_inv]
        exact sLocalIdelicZFunction_principalValue_pure T hT χ z hz g a b hg
      rw [hL, hL, hpure]
      ring) f
    change L (P f) - d z * L f + L f = _ at he
    rw [← hL f] at he
    rw [← hL, ← hL]
    linear_combination he
  have hmer := sLocalIdelicZFunction_principalValue_continue
    (sLocalIdelicZFunction_meromorphic (P f) χ).meromorphicOn
    ((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn.mul (fun z _ ↦ (ha z).meromorphicAt))
    (fun z hz ↦ (sLocalIdelicZFunction_eq_integral (P f) ⟨χ, z, hz, rfl⟩).trans
      ((hright z hz).trans (congrArg (· * d z) (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩).symm)))
  filter_upwards [hmer] with z hz
  change sLocalIdelicZFunction (P f) (chartₛ(χ) z) = sLocalIdelicZFunction f (chartₛ(χ) z) * d z at hz
  exact hz.trans (by rw [div_eq_mul_inv, hd])

-- TODO(paper-gap): (5.3.4.14) gives the allowed pole multiplicity, which can exceed
-- the actual order. A local gamma factor contributes a positive multiplicity at a pole.

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The archimedean pole bound counts the local Euler factors with a pole on the
given norm-twist line at the given exponent. Each such pole is simple. -/
def sLocalArchimedeanPoleMultiplicity (χ : PontryaginDual Jₛ) (s : ℂ) : ℕ :=
  (Finset.univ.filter (fun w : InfinitePlace F ↦
    meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0)).card

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The pole multiplicity is positive exactly at a pole of some pulled-back
archimedean Euler factor. -/
theorem sLocalArchimedeanPoleMultiplicity_pos_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    0 < sLocalArchimedeanPoleMultiplicity χ s ↔
      ∃ w : InfinitePlace F, meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0 := by
  rw [sLocalArchimedeanPoleMultiplicity, Finset.card_pos]
  simp [Finset.Nonempty]

/-- The reciprocal Gamma function satisfies the order recursion coming from
`1 / Γ(u) = u / Γ(u + 1)`. -/
private theorem meromorphicOrderAt_inv_Gamma_step (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      meromorphicOrderAt (id : ℂ → ℂ) x +
        meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) (x + 1) := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have heq : (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) =
      (id : ℂ → ℂ) * ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) := by
    funext u
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one u
  have hcomp : MeromorphicAt ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) x :=
    ((hg (x + 1)).comp (f := fun u : ℂ ↦ u + 1) (by fun_prop)).meromorphicAt
  calc meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x
      = meromorphicOrderAt ((id : ℂ → ℂ) *
          ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1))) x := by rw [← heq]
    _ = _ := by
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hcomp,
        meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- The reciprocal Gamma function has at most a simple zero at each point. -/
private theorem meromorphicOrderAt_inv_Gamma_le_one (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x ≤ 1 := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hzero : ∀ {f : ℂ → ℂ} {y : ℂ}, AnalyticAt ℂ f y → f y ≠ 0 →
      meromorphicOrderAt f y = 0 := by
    intro f y hf hy
    rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
      CharP.cast_eq_zero, WithTop.coe_zero]
  by_cases hx : ∃ m : ℕ, x = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hx
    refine le_of_eq ?_
    induction m with
    | zero =>
      rw [meromorphicOrderAt_inv_Gamma_step, Nat.cast_zero, neg_zero, zero_add,
        meromorphicOrderAt_id,
        hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
    | succ m ih =>
      rw [meromorphicOrderAt_inv_Gamma_step,
        hzero analyticAt_id (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero m))),
        zero_add, show -((m + 1 : ℕ) : ℂ) + 1 = -(m : ℂ) by push_cast; ring]
      exact ih
  · rw [hzero (hg x) (inv_ne_zero (Complex.Gamma_ne_zero fun m hm ↦ hx ⟨m, hm⟩))]
    exact zero_le_one

/-- Every pole of the Gamma function is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gamma (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gamma x := by
  have h := meromorphicOrderAt_inv_Gamma_le_one x
  have hinv : meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      -meromorphicOrderAt Complex.Gamma x := meromorphicOrderAt_inv
  rw [hinv] at h
  cases hn : meromorphicOrderAt Complex.Gamma x with
  | top => exact le_top
  | coe n =>
    rw [hn] at h
    have h1 : -n ≤ 1 := by exact_mod_cast h
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)

/-- Every pole of the real Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℝ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℝ x := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : Complex.Gammaℝ = (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) *
      (Complex.Gamma ∘ fun s : ℂ ↦ s / 2) := by
    funext s
    exact Complex.Gammaℝ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) x :=
    ((differentiable_id.neg.div_const 2).const_cpow (Or.inl hpi)).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi]),
    meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Every pole of the complex Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℂ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℂ x := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have heq : Complex.Gammaℂ = (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) * Complex.Gamma := by
    funext s
    exact Complex.Gammaℂ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) x :=
    ((differentiable_id.neg.const_cpow (Or.inl hpi)).const_mul 2).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi])]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Along a norm-twist chart, the restriction to an archimedean place is the restriction
at exponent zero times the complex power of the local module. -/
private theorem sLocalInfiniteRestriction_chart_apply (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (z : ℂ) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ(χ) z) g =
      sLocalInfiniteRestriction w (chartₛ(χ) 0) g *
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ z := by
  obtain ⟨x, hx⟩ : ∃ x : Jₛ, ∀ c : Xₛ, sLocalInfiniteRestriction w c g = c x :=
    ⟨_, fun _ ↦ rfl⟩
  have hN : ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) =
      ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
        ℂ) := by
    have he := sLocalInfiniteRestriction_norm (S := S) w g
    rw [hx] at he
    change ((1 : PontryaginDual Jₛ) x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at he
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using he
  rw [hx, hx, ← hN]
  change (χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z =
    ((χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z
  rw [Complex.cpow_zero, mul_one]

/-- Along a norm-twist chart, the Euler factor at a real place is a translate of the real
Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_real (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℝ (z + b) := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hp := (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × Fin 2, p = (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.val : ℂ), fun z ↦ ?_⟩
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ (z + p.1) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
    intro x
    have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℝ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
      simp [InfinitePlace.mult, hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
    ring
  have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, add_assoc]

/-- Along a norm-twist chart, the Euler factor at a complex place is half a translate of the
complex Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_complex (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℂ (z + b) / 2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  have hp := (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × ℤ, p = (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, fun z ↦ ?_⟩
  have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z + p.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
    intro x
    have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        hw).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero)))]
    ring
  have hq := (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, InfinitePlace.not_isReal_iff_isComplex.mpr hw,
    ↓reduceDIte, hq, add_assoc]

/-- For orders bounded below by minus one, the negative parts sum to minus the number of
negative orders. -/
private theorem neg_card_filter_eq_sum_min {ι : Type*} [Fintype ι] (ord : ι → WithTop ℤ)
    [DecidablePred fun i ↦ ord i < 0] (h : ∀ i, ((-1 : ℤ) : WithTop ℤ) ≤ ord i) :
    ((-((Finset.univ.filter fun i ↦ ord i < 0).card : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, min 0 (ord i) := by
  have hneg : ∀ i ∈ Finset.univ.filter (fun i ↦ ord i < 0),
      min 0 (ord i) = ((-1 : ℤ) : WithTop ℤ) := by
    intro i hi
    have hi' : ord i < 0 := (Finset.mem_filter.mp hi).2
    rw [min_eq_right hi'.le]
    refine le_antisymm ?_ (h i)
    cases hn : ord i with
    | top =>
      rw [hn] at hi'
      exact absurd hi' not_top_lt
    | coe n =>
      rw [hn] at hi'
      have h0 : n < 0 := by exact_mod_cast hi'
      exact_mod_cast (by omega : n ≤ -1)
  have hpos : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ ord i < 0), min 0 (ord i) = 0 := fun i hi ↦
    min_eq_left (not_lt.mp (Finset.mem_filter.mp hi).2)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ ord i < 0),
    Finset.sum_congr rfl hneg, Finset.sum_eq_zero hpos, add_zero, Finset.sum_const,
    ← WithTop.coe_nsmul]
  congr 1
  simp

/-- Along a norm-twist chart, every pole of an archimedean Euler factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (s : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s := by
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) = Complex.Gammaℝ ∘ (· + b) := funext hb
    rw [hfun, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℝ _
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) =
        (fun _ : ℂ ↦ (2 : ℂ)⁻¹) * (Complex.Gammaℂ ∘ (· + b)) :=
      funext fun z ↦ (hb z).trans (div_eq_inv_mul _ _)
    rw [hfun, meromorphicOrderAt_mul_of_ne_zero analyticAt_const (inv_ne_zero two_ne_zero),
      meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℂ _

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The negative of the allowed pole multiplicity is the sum of the negative parts
of the meromorphic orders of the local archimedean Euler factors. -/
theorem sLocalArchimedeanPoleMultiplicity_eq_sum (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) =
      ∑ w : InfinitePlace F, min 0
        (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chartₛ(χ) z))) s) := by
  rw [sLocalArchimedeanPoleMultiplicity]
  exact neg_card_filter_eq_sum_min _ fun w ↦
    neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart χ w s

/-- Paper: Proposition 5.3.4.5(2), p. 264.
After all finite principal values, the zeta pole order is bounded by the total
archimedean Euler pole multiplicity.
Deviation: The assertion gives an upper bound since the input can cancel poles.
The multiplicity counts positive pole orders. -/
theorem sLocalIdelicZFunction_principalValue_pole_bound (f : ℬₛ)
    (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s := by
  classical
  let E (w : InfinitePlace F) (z : ℂ) := infiniteLocalEulerFactor w
    (sLocalInfiniteRestriction w (chartₛ(χ) z))
  let A (z : ℂ) := ∏ w : InfinitePlace F, E w z
  let G (z : ℂ) := sLocalNormalizedZFunction f (chartₛ(χ) z)
  let Z (z : ℂ) := sLocalIdelicZFunction (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)
  have hw (w : InfinitePlace F) : Meromorphic (E w) ∧
      ∃ d : ℝ, ∀ z : ℂ, d < z.re → E w z ≠ 0 := by
    by_cases hr : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hr
      have hi : (E w)⁻¹ = fun z : ℂ ↦ (Complex.Gammaℝ (z + b))⁻¹ :=
        funext fun z ↦ congrArg Inv.inv (hb z)
      have hd : Differentiable ℂ ((E w)⁻¹) := hi ▸
        (Complex.differentiable_Gammaℝ_inv.comp (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop))
      refine ⟨fun z ↦ by simpa only [inv_inv] using (hd.analyticAt z).meromorphicAt.inv, -b.re, ?_⟩
      intro z hz
      rw [show E w z = _ from hb z]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa only [Complex.add_re] using
        (show 0 < z.re + b.re by linarith))
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w (InfinitePlace.not_isReal_iff_isComplex.mp hr)
      have hi : (E w)⁻¹ = fun z : ℂ ↦ 2 * (Complex.Gammaℂ (z + b))⁻¹ := by
        funext z
        rw [Pi.inv_apply, show E w z = _ from hb z, inv_div, div_eq_mul_inv]
      have hd : Differentiable ℂ ((E w)⁻¹) := by
        rw [hi]
        exact (Complex.differentiable_Gammaℂ_inv.comp
          (show Differentiable ℂ (fun z : ℂ ↦ z + b) by fun_prop)).const_mul 2
      refine ⟨fun z ↦ by simpa only [inv_inv] using (hd.analyticAt z).meromorphicAt.inv, -b.re, ?_⟩
      intro z hz
      rw [show E w z = _ from hb z]
      apply div_ne_zero _ two_ne_zero
      rw [Complex.Gammaℂ_def]
      have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      exact mul_ne_zero (mul_ne_zero two_ne_zero (fun h ↦ hpi ((Complex.cpow_eq_zero_iff _ _).mp h).1))
        (Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re]; linarith))
  choose d hd using fun w ↦ (hw w).2
  let R := ∑ w : InfinitePlace F, |d w|
  have hR : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hA : Meromorphic A := fun z ↦ MeromorphicAt.fun_prod fun w _ ↦ (hw w).1 z
  have hG : ∀ z, AnalyticAt ℂ G z := fun z ↦ (sLocalNormalizedZFunction_entire f χ) z (mem_univ z)
  have hZ : Meromorphic Z := fun z ↦ (sLocalIdelicZFunction_meromorphic _ χ).meromorphicOn z (mem_univ z)
  have hloc : Z =ᶠ[𝓝[≠] ((R + 1 : ℝ) : ℂ)] G * A := by
    have hs' : ∀ᶠ z : ℂ in 𝓝[≠] ((R + 1 : ℝ) : ℂ), R < z.re := nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp))
    filter_upwards [hs', nhdsNE_le_codiscrete _ (sLocalIdelicZFunction_principalValue S (Finset.Subset.refl S) f χ)]
      with z hz hpv
    have ha : A z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ ↦ hd w z <|
      ((le_abs_self _).trans (Finset.single_le_sum (fun v _ ↦ abs_nonneg (d v)) (Finset.mem_univ w))).trans_lt hz
    have hpos := hR.trans_lt hz
    change sLocalIdelicZFunction _ _ = sLocalNormalizedZFunction f _ * A z
    rw [hpv, sLocalNormalizedZFunction_eq_div f χ hpos, ← sLocalIdelicZFunction_eq_integral f ⟨χ, z, hpos, rfl⟩]
    have hmem (v : S) : v.val ∈ S := v.property
    simp only [hmem, ite_true, sLocalHeckeL]
    change _ / _ = _ / (A z * _) * A z
    simp only [div_eq_mul_inv, mul_inv]
    field_simp [ha]
  have hdiff : Meromorphic (Z - G * A) := fun z ↦ (hZ z).sub ((hG z).meromorphicAt.mul (hA z))
  have hall := hdiff.exists_meromorphicOrderAt_eq_top_iff_eventually_zero.mp
    ⟨_, meromorphicOrderAt_eq_top_iff.mpr (hloc.mono fun _ hz ↦ sub_eq_zero.mpr hz)⟩
  have he : Z =ᶠ[𝓝[≠] s] G * A := nhdsNE_le_codiscrete s
    (hall.mono fun _ hz ↦ sub_eq_zero.mp hz)
  change _ ≤ meromorphicOrderAt Z s
  rw [sLocalArchimedeanPoleMultiplicity_eq_sum, meromorphicOrderAt_congr he,
    meromorphicOrderAt_mul (hG s).meromorphicAt (hA s)]
  apply le_trans _ (le_add_of_nonneg_left (hG s).meromorphicOrderAt_nonneg)
  change _ ≤ meromorphicOrderAt (fun z ↦ ∏ w : InfinitePlace F, E w z) s
  rw [meromorphicOrderAt_fun_prod fun w _ ↦ (hw w).1 s]
  exact Finset.sum_le_sum fun w _ ↦ min_le_right _ _

/-- Extend the inverse unit character by zero as an additive Schwartz–Bruhat test. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_units (v : V)
    (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    let U := (v.adicCompletionIntegers F).units
    ∃ b : ℬ(v.adicCompletion F), b (Multiplicative.ofAdd 0) = 0 ∧ ∀ g : (v.adicCompletion F)ˣ,
      b (Multiplicative.ofAdd g.val) = if g ∈ U then (c g)⁻¹ else 0 := by
  classical
  intro U
  let K := v.adicCompletion F
  have h0 : (0 : K) ∉ Units.val '' (U : Set Kˣ) := fun ⟨g, _, hg⟩ ↦ g.ne_zero hg
  have hmem (g : Kˣ) : g.val ∈ Units.val '' (U : Set Kˣ) ↔ g ∈ U :=
    ⟨fun ⟨u, hu, he⟩ ↦ (Units.ext he : u = g) ▸ hu, fun hg ↦ ⟨g, hg, rfl⟩⟩
  by_cases h : ∀ g ∈ U, c g = 1
  · let hp := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π : Kˣ := Units.mk0 (hp.choose : K) hp.choose_spec.ne_zero
    refine ⟨finitePlaceDifference v π (finiteStandardGaussian v 1), ?_, fun g ↦ ?_⟩
    · exact (finitePlaceDifference_integerIndicator v π hp.choose_spec 0).trans (indicator_of_notMem h0 _)
    · rw [finitePlaceDifference_integerIndicator v π hp.choose_spec]
      by_cases hg : g ∈ U
      · rw [indicator_of_mem ((hmem g).mpr hg), ite_eq_left hg, h g hg, inv_one]
      · rw [indicator_of_notMem (mt (hmem g).mp hg), ite_eq_right hg]
  · refine ⟨finiteStandardGaussian v c, ?_, fun g ↦ ?_⟩
    · change finiteStandardGaussianValue v c 0 = 0
      rw [finiteStandardGaussianValue, ite_eq_right h, indicator_of_notMem h0]
    · by_cases hg : g ∈ U
      · exact (finiteStandardGaussian_integerUnit v c g hg).trans (ite_eq_left hg).symm
      · rw [ite_eq_right hg]
        change finiteStandardGaussianValue v c g.val = 0
        rw [finiteStandardGaussianValue, ite_eq_right h, indicator_of_notMem (mt (hmem g).mp hg)]

/-- A preimage of the inverse unit character contributes the positive unit mass at every exponent. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_finite
    (χ : PontryaginDual Jₛ) (v : S) :
    letI : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
    let μ := finiteLocalMultiplicativeTamagawaMeasure F v.val
    let U := (v.val.adicCompletionIntegers F).units
    ∃ b : ℬ(v.val.adicCompletion F), (μ.real U : ℂ) ≠ 0 ∧ ∀ z : ℂ,
      localIdelicZetaIntegral μ (fun x ↦ finitePlacePrincipalValue v.val b (Multiplicative.ofAdd x))
        (sLocalFiniteRestriction v (chartₛ(χ) z)) = μ.real U := by
  classical
  let : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  intro μ U
  let : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  obtain ⟨η, hη⟩ := sLocalIdelicZFunction_principalValue_chart χ v
  let c₀ := (circleToComplex).comp η
  obtain ⟨b₀, h0, hb₀⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles_units v.val c₀
  obtain ⟨b, hb⟩ : b₀ ∈ Set.range (finitePlacePrincipalValue v.val) := by
    rw [finitePlacePrincipalValue_range]
    exact h0
  refine ⟨b, Complex.ofReal_ne_zero.mpr
    (finitePlacePrincipalValue_integrable v.val 1 b (Multiplicative.ofAdd 0)).1.ne', fun z ↦ ?_⟩
  let hO : IsOpen (U : Set (v.val.adicCompletion F)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  rw [hb, hη]
  let c := quasiCharacterNormTwist _ (continuous_finiteLocalModule v.val) c₀ z
  have hh (g : (v.val.adicCompletion F)ˣ) : b₀ (Multiplicative.ofAdd g.val) * c g =
      (U : Set (v.val.adicCompletion F)ˣ).indicator (fun _ ↦ (1 : ℂ)) g := by
    rw [hb₀]
    by_cases hg : g ∈ U
    · rw [ite_eq_left hg, indicator_of_mem hg]
      have hn := Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg)
      change (η g : ℂ)⁻¹ * ((η g : ℂ) * (‖g.val‖ : ℂ) ^ z) = 1
      simp [hn, Circle.coe_ne_zero]
    · rw [ite_eq_right hg, indicator_of_notMem hg, zero_mul]
  change (∫ g, b₀ (Multiplicative.ofAdd g.val) * c g ∂μ) = _
  simp_rw [hh]
  rw [integral_indicator_const _ hO.measurableSet, Complex.real_smul, mul_one]

/-- The local standard Gaussian realizes the archimedean Euler factor on the entire positive half-plane. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_arch
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) :
    letI : MeasurableSpace w.Completion := borel _
    ∃ a : ℬ(w.Completion), ∀ z : ℂ, 0 < z.re →
      localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w)
        (fun x ↦ a (Multiplicative.ofAdd x)) (sLocalInfiniteRestriction w (chartₛ(χ) z)) =
        infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z)) := by
  let : MeasurableSpace w.Completion := borel _
  let h := sLocalInfiniteInsertion_properties (S := S) w
  let i : w.Completionˣ →ₜ* Jₛ :=
    ⟨{ toFun := fun g ↦ QuotientGroup.mk ((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
          ((v : S) → v.val.adicCompletion F)).symm (ContinuousMulEquiv.piUnits.symm
            (@Pi.mulSingle _ _ _ (Classical.decEq _) w g), 1)),
       map_one' := h.1, map_mul' := h.2.1 }, h.2.2⟩
  let η := χ.comp i
  refine ⟨infiniteStandardGaussian w η, fun z hz ↦ ?_⟩
  have hchart : sLocalInfiniteRestriction w (chartₛ(χ) z) =
      quasiCharacterNormTwist _ (continuous_infiniteLocalModule w) ((circleToComplex).comp η) z := by
    ext1 g
    have hn := sLocalInfiniteRestriction_norm w (S := S) g
    change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (((mₛ (i g) : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at hn
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] at hn
    exact congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ z) hn
  rw [hchart, ← infiniteLocalIdelicZFunction_eq_integral w _ η hz]
  exact infiniteLocalIdelicZFunction_standardGaussian w η z hz

/-- A function with an entire reciprocal which is nonzero somewhere has meromorphic order at most zero. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal (f : ℂ → ℂ)
    (ha : Differentiable ℂ (fun z ↦ (f z)⁻¹)) (u : ℂ) (hu : f u ≠ 0) (s : ℂ) :
    MeromorphicAt f s ∧ meromorphicOrderAt f s ≤ 0 := by
  let g (z : ℂ) := (f z)⁻¹
  have hm : MeromorphicOn g univ := fun z _ ↦ (ha.analyticAt z).meromorphicAt
  have h₀ : meromorphicOrderAt g u = 0 :=
    (ha.analyticAt u).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (inv_ne_zero hu)
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ u) (mem_univ s) (by rw [h₀]; exact WithTop.coe_ne_top)
  have hf : (fun z ↦ (g z)⁻¹) = f := funext fun z ↦ inv_inv _
  refine ⟨hf ▸ (hm s (mem_univ s)).inv, ?_⟩
  rw [← hf]
  change meromorphicOrderAt g⁻¹ s ≤ 0
  rw [meromorphicOrderAt_inv]
  have hn : 0 ≤ meromorphicOrderAt g s := (ha.analyticAt s).meromorphicOrderAt_nonneg
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hk] at hn ⊢
  exact_mod_cast neg_nonpos.mpr (show 0 ≤ k by exact_mod_cast hn)

/-- Shifted real and complex Gamma factors have no zeros. Their orders therefore equal their negative parts. -/
private theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles_order
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (s : ℂ) :
    let L := fun z ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))
    MeromorphicAt L s ∧ meromorphicOrderAt L s ≤ 0 := by
  intro L
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have h : L = fun z ↦ Complex.Gammaℝ (z + b) := funext hb
    rw [h]
    apply exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal _
      (Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const b)) (1 - b)
    simp [Complex.Gammaℝ_one]
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have h : L = fun z ↦ Complex.Gammaℂ (z + b) / 2 := funext hb
    rw [h]
    refine exists_sLocalIdelicZFunction_principalValue_attaining_poles_reciprocal _ ?_ (1 - b) ?_ s
    · simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      exact (Complex.differentiable_Gammaℂ_inv.comp (differentiable_id.add_const b)).const_mul 2
    · simp [Complex.Gammaℂ_one, Real.pi_ne_zero]

/-- Paper: Proposition 5.3.4.5(2), p. 264.
On each component a choice of test realizes the full allowed archimedean pole divisor.
Deviation: Attainment is an existence assertion. The input can cancel any allowed pole. -/
theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles (χ : PontryaginDual Jₛ) :
    ∃ f : ℬₛ, ∀ s : ℂ,
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s =
        (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) := by
  classical
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  choose a ha using exists_sLocalIdelicZFunction_principalValue_attaining_poles_arch χ
  choose b hmass hb using exists_sLocalIdelicZFunction_principalValue_attaining_poles_finite χ
  obtain ⟨a₀, ha₀⟩ := sLocalIdelicZFunction_principalValue_archTest a
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let f := e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))
  let p := sAdelePrincipalValue F (Finset.Subset.refl S) f
  let b' (v : S) := finitePlacePrincipalValue v.val (b v)
  have hp (x : Aₛ) : p (Multiplicative.ofAdd x) =
      (∏ w : InfinitePlace F, a w (Multiplicative.ofAdd (x.1 w))) *
        ∏ v : S, b' v (Multiplicative.ofAdd (x.2 v)) := by
    have H : p = e (a₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b' v)) := by
      simpa only [p, f, e, b', Finset.coe_mem, ite_true] using
        sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl S) a₀ b
    rw [H]
    exact ((sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a₀ b' x).trans
      (congrArg (· * _) (ha₀ x.1))
  let L (w : InfinitePlace F) (z : ℂ) := infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))
  let M := ∏ v : S, (((finiteLocalMultiplicativeTamagawaMeasure F v.val).real
    (v.val.adicCompletionIntegers F).units : ℝ) : ℂ)
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ hmass v
  have hL (w : InfinitePlace F) (z : ℂ) : MeromorphicAt (L w) z ∧ meromorphicOrderAt (L w) z ≤ 0 :=
    exists_sLocalIdelicZFunction_principalValue_attaining_poles_order χ w z
  have hmer (z : ℂ) : MeromorphicAt (fun t ↦ M * ∏ w, L w t) z :=
    MeromorphicAt.mul analyticAt_const.meromorphicAt (MeromorphicAt.fun_prod fun w _ ↦ (hL w z).1)
  have H := sLocalIdelicZFunction_principalValue_continue (sLocalIdelicZFunction_meromorphic p χ).meromorphicOn
    (fun z _ ↦ hmer z) (fun z hz ↦ by
      rw [sLocalIdelicZFunction_eq_integral p ⟨χ, z, hz, rfl⟩,
        sLocalIdelicZetaIntegral_pureTensor (chartₛ(χ) z) ⟨χ, z, hz, rfl⟩ p a b' hp]
      exact (congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ ↦ ha w z hz)
        (Finset.prod_congr rfl fun v _ ↦ hb v z)).trans (mul_comm _ _))
  refine ⟨f, fun s ↦ ?_⟩
  have hs := meromorphicOrderAt_congr (H.filter_mono (nhdsNE_le_codiscrete s))
  refine hs.trans ?_
  change meromorphicOrderAt ((fun _ : ℂ ↦ M) * (fun z ↦ ∏ w, L w z)) s = _
  rw [meromorphicOrderAt_mul_of_ne_zero analyticAt_const hM,
    meromorphicOrderAt_fun_prod (fun w _ ↦ (hL w s).1), sLocalArchimedeanPoleMultiplicity_eq_sum]
  exact Finset.sum_congr rfl fun w _ ↦ (min_eq_right (hL w s).2).symm

private theorem continuous_schwartzBruhat_pointEval {G : Type*} [CommGroup G]
    [TopologicalSpace G] (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (↑‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (↑‖f z‖₊ : ENNReal)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The subspace cut out by the selected finite zero-coordinate conditions is closed. -/
theorem sAdeleFiniteZeroSchwartz_isClosed (T : Finset V) :
    IsClosed (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) := by
  let X := {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}
  have h : IsClosed (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) :=
    isClosed_iInter fun x : X ↦
      isClosed_eq (continuous_schwartzBruhat_pointEval (Multiplicative.ofAdd x.val)) continuous_const
  have heq : (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) =
      (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) :=
    Set.ext fun f ↦ by
      refine Set.mem_iInter.trans ?_
      let K (x : X) : Submodule ℂ ℬₛ :=
        LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
          (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)
      change (∀ x : X, f ∈ K x) ↔ f ∈ ⨅ x : X, K x
      exact (Submodule.mem_iInf K).symm
  exact (congrArg (fun s : Set ℬₛ ↦ IsClosed s) heq).mp h

local notation "thetaQuotient(" χ ")" => (LinearMap.ker (thetaAt(χ))).mkQ

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value preserves the kernel of each homogeneous theta transform. -/
theorem sAdelePrincipalValue_preserves_homogeneousThetaKernel {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) :
    LinearMap.ker (thetaAt(ψ)) ≤
      (LinearMap.ker (thetaAt(ψ))).comap (sAdelePrincipalValue F hT) := by
  let K := LinearMap.ker (thetaAt(ψ))
  let A := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) ψ).exists.choose
  obtain ⟨e, he⟩ := (sLocalThetaIsotypicAverage_equiv (F := F) (S := S) ψ).2
  intro f hf
  have hz : K.mkQ f = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hf
  have hA : A (Submodule.Quotient.mk f) = 0 := (he f).symm.trans
    (congrArg Subtype.val ((congrArg e hz).trans e.map_zero))
  have hcomm := sLocalThetaPrincipalValue_isotypicAverage (F := F) hT ψ (Submodule.Quotient.mk f)
  have hzero : A (Submodule.Quotient.mk (sAdelePrincipalValue F hT f)) = 0 :=
    hcomm.symm.trans ((congrArg (sLocalThetaPrincipalValue F hT) hA).trans (map_zero _))
  apply (Submodule.Quotient.mk_eq_zero K).mp
  apply e.injective
  apply Subtype.ext
  exact ((he _).trans hzero).trans (congrArg Subtype.val e.map_zero).symm

/-- Paper: Proposition 5.3.4.5(3), p. 264.
Weil's operator on homogeneous theta classes is induced by its action on tests. -/
def sLocalHomogeneousThetaPrincipalValue {T : Finset V} (hT : T ⊆ S) (ψ : PontryaginDual J₁) :
    SLocalHomogeneousThetaSpace F S ψ →ₗ[ℂ] SLocalHomogeneousThetaSpace F S ψ :=
  (LinearMap.ker (thetaAt(ψ))).mapQ (LinearMap.ker (thetaAt(ψ))) (sAdelePrincipalValue F hT)
    (sAdelePrincipalValue_preserves_homogeneousThetaKernel hT ψ)

/-- Paper: Proposition 5.3.4.5(3), p. 264.
On a homogeneous theta class the operator sends the representative to its principal value. -/
theorem sLocalHomogeneousThetaPrincipalValue_mk {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) (f : ℬₛ) :
    sLocalHomogeneousThetaPrincipalValue hT ψ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F hT f) := rfl

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The closed embedding of Lemma 5.3.1.5 restricts to the homogeneous theta quotient,
identified with its isotype by §5.2. -/
theorem sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) : IsClosedEmbedding (sLocalHomogeneousThetaPrincipalValue hT ψ) :=
  by
  classical
  let K := LinearMap.ker (thetaAt(ψ))
  rcases T.eq_empty_or_nonempty with rfl | hn
  · have conjugate {E G Y : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
        [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
        [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
        (e : InductiveTensor E G ≃L[ℂ] Y) (P : G →ₗ[ℂ] G) (hp : ∀ x, P x = x) :
        e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) P).comp e.symm.toLinearMap)
          = LinearMap.id := by
      have he : P = LinearMap.id := LinearMap.ext hp
      subst he
      refine LinearMap.ext fun x ↦ ?_
      have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
      exact (congrArg e h).trans (e.apply_symm_apply x)
    have hP : sAdelePrincipalValue F hT = LinearMap.id := by
      unfold sAdelePrincipalValue
      refine conjugate _ _ fun x ↦ ?_
      simp only [Finset.notMem_empty, ite_false, PiTensorProduct.map_id]
      rfl
    have hU : ⇑(sLocalHomogeneousThetaPrincipalValue hT ψ) = id := by
      funext y
      obtain ⟨f, rfl⟩ := K.mkQ_surjective y
      exact congrArg K.mkQ (LinearMap.congr_fun hP f)
    rw [hU]
    exact IsClosedEmbedding.id
  · obtain ⟨hs, e, he⟩ := sLocalThetaIsotypicAverage_equiv (F := F) (S := S) ψ
    let j := Subtype.val ∘ e
    have hj : IsClosedEmbedding j := hs.isClosedEmbedding_subtypeVal.comp e.toHomeomorph.isClosedEmbedding
    have hcomp : j ∘ sLocalHomogeneousThetaPrincipalValue hT ψ = sLocalThetaPrincipalValue F hT ∘ j := by
      funext y
      obtain ⟨f, rfl⟩ := K.mkQ_surjective y
      exact (he (sAdelePrincipalValue F hT f)).trans
        ((sLocalThetaPrincipalValue_isotypicAverage (F := F) hT ψ (Submodule.Quotient.mk f)).symm.trans
          (congrArg (sLocalThetaPrincipalValue F hT) (he f).symm))
    apply hj.of_comp_iff.mp
    rw [hcomp]
    exact (sLocalThetaPrincipalValue_isClosedEmbedding (F := F) hT hn).comp hj

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value range in the homogeneous theta quotient is the image of tests
vanishing at the finite zero-coordinate hyperplanes. -/
theorem sLocalPrincipalValue_homogeneousTheta_range (χ : PontryaginDual Jₛ) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S S).map (thetaQuotient(χ₁(χ))) := by
  classical
  let pv := sAdelePrincipalValue F (Finset.Subset.refl S)
  let Z := sAdeleFiniteZeroSchwartz S S
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have ht (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) :
      pv (e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))) =
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, finitePlacePrincipalValue v.val (g v))) := by
    simpa [pv, e] using
      sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl S) f g
  let pack (a : ℬ(A∞)) (b : ∀ v : S, ℬ(v.val.adicCompletion F)) := e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, b v))
  let act (b : ∀ v : S, ℬ(v.val.adicCompletion F)) := fun v ↦ finitePlacePrincipalValue v.val (b v)
  let D (T : Finset V) (b : ∀ v : S, ℬ(v.val.adicCompletion F)) :=
    ∀ v : S, v.val ∈ T → b v (Multiplicative.ofAdd 0) = 0
  have rangeSpan {X A B : Type _} [AddCommGroup X] [Module ℂ X] (P : X →ₗ[ℂ] X)
      (w : A → B → X) (l : B → B) (p q : B → Prop)
      (hw : ∀ a b, P (w a b) = w a (l b))
      (hgen : ∀ x, x ∈ Submodule.span ℂ {y | ∃ a b, p b ∧ w a b = y})
      (hm : ∀ b, q (l b)) (hs : ∀ b, q b → ∃ c, l c = b) :
      LinearMap.range P = Submodule.span ℂ {y | ∃ a b, q b ∧ w a b = y} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      have incl : Submodule.span ℂ {y | ∃ a b, p b ∧ w a b = y} ≤
          (Submodule.span ℂ {y | ∃ a b, q b ∧ w a b = y}).comap P := by
        apply Submodule.span_le.mpr
        rintro _ ⟨a, b, -, rfl⟩
        exact Submodule.subset_span ⟨a, l b, hm b, (hw a b).symm⟩
      exact incl (hgen x)
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, b, hb, rfl⟩
      obtain ⟨c, rfl⟩ := hs b hb
      exact ⟨w a c, hw a c⟩
  have hgen (f : ℬₛ) : f ∈ Submodule.span ℂ {y | ∃ a b, D ∅ b ∧ pack a b = y} := by
    apply (sAdeleFiniteZeroSchwartz_eq_span_tmul (F := F) (S := S) ∅).le
    exact (Submodule.mem_iInf _).2 fun x ↦ by
      obtain ⟨v, hv, -⟩ := x.property
      exact False.elim (Finset.notMem_empty _ hv)
  have hm (b) : D S (act b) := by
    intro v _
    have hmem := Set.mem_range_self (f := finitePlacePrincipalValue v.val) (b v)
    rwa [finitePlacePrincipalValue_range] at hmem
  have hs (b) (hb : D S b) : ∃ c, act c = b := by
    have hmem (v : S) : b v ∈ Set.range (finitePlacePrincipalValue v.val) := by
      rw [finitePlacePrincipalValue_range]
      exact hb v v.property
    choose c hc using hmem
    exact ⟨c, funext hc⟩
  have hr : LinearMap.range pv = Z :=
    (rangeSpan pv pack act (D ∅) (D S) ht hgen hm hs).trans
      (sAdeleFiniteZeroSchwartz_eq_span_tmul (F := F) (S := S) S).symm
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ f => exact ⟨pv f, hr.le ⟨f, rfl⟩, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg⟩ := hr.ge hf
    exact ⟨Submodule.Quotient.mk g, congrArg (thetaQuotient(χ₁(χ))) hg⟩

/-- On a homogeneous theta class, translation by a norm-one idele acts by its character. -/
private theorem sLocalPrincipalValue_unramified_translate (χ : PontryaginDual Jₛ)
    (a : Aₛˣ) (ha : (QuotientGroup.mk a : Jₛ) ∈ (mₛ).ker) (f : ℬₛ) :
    (thetaQuotient(χ₁(χ))) (schwartzBruhatUnitTranslate a f) =
      (χ (QuotientGroup.mk a) : ℂ) • (thetaQuotient(χ₁(χ))) f := by
  obtain ⟨Z, hZ, hval⟩ := exists_sLocalHomogeneousThetaMellin (F := F) (S := S) χ₁(χ)
  let q := thetaQuotient(χ₁(χ))
  let z : ℂ := χ (QuotientGroup.mk a)
  apply hZ
  refine Eq.trans ?_ (Z.map_smul z (q f)).symm
  refine Subtype.ext (ContinuousMap.ext fun d ↦ ?_)
  exact (hval (schwartzBruhatUnitTranslate a f) d).trans
    ((sLocalIdelicMellin_unitTranslate a f ⟨d.val.val, d.property⟩).trans
      (congrArg₂ (· * ·) (d.val.property ⟨QuotientGroup.mk a, ha⟩) (hval f d).symm))

/-- At a ramified place there is a norm-one unit with nontrivial character. Its
dilation fixes the entire coordinate hyperplane at that place. -/
private theorem sLocalPrincipalValue_unramified_unit (χ : PontryaginDual Jₛ) (v : S)
    (h : ¬ ∀ u : (v.val.adicCompletionIntegers F)ˣ, sLocalFiniteRestriction v (chartₛ(χ) 0)
      (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) :
    ∃ a : Aₛˣ, (QuotientGroup.mk a : Jₛ) ∈ (mₛ).ker ∧ (χ (QuotientGroup.mk a) : ℂ) ≠ 1 ∧
      ∀ x : Aₛ, x.2 v = 0 → ((a⁻¹).val : Aₛ) * x = x := by
  classical
  obtain ⟨u, hu⟩ := not_forall.mp h
  let y := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u
  let e := @Pi.mulSingle S (fun w : S ↦ (w.val.adicCompletion F)ˣ) _ (Classical.decEq _) v y
  let a : Aₛˣ := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) _).symm
    (1, ContinuousMulEquiv.piUnits.symm e)
  have hy : ‖y.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := y)).mp
      ⟨u.val.prop, u.inv.prop⟩)
  have hn := sLocalFiniteRestriction_norm v y
  change ((1 : PontryaginDual Jₛ) (QuotientGroup.mk a) : ℂ) *
    (((mₛ (QuotientGroup.mk a)).val : ℝ) : ℂ) ^ (1 : ℂ) = (‖y.val‖ : ℂ) at hn
  simp only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one, hy,
    Complex.ofReal_one] at hn
  have hnorm : mₛ (QuotientGroup.mk a) = 1 :=
    Units.ext (NNReal.eq (Complex.ofReal_injective hn))
  refine ⟨a, hnorm, ?_, ?_⟩
  · change (χ (QuotientGroup.mk a) : ℂ) * _ ^ (0 : ℂ) ≠ 1 at hu
    simpa only [Complex.cpow_zero, mul_one] using hu
  · intro x hx
    apply Prod.ext
    · change 1 * x.1 = x.1
      exact one_mul _
    · funext w
      change ((e w)⁻¹).val * x.2 w = x.2 w
      by_cases hw : w = v
      · subst w
        simp [hx]
      · have hw' : e w = 1 := @Pi.mulSingle_eq_of_ne S (fun w : S ↦ (w.val.adicCompletion F)ˣ)
            _ (Classical.decEq _) v w hw y
        rw [hw']
        simp

/-- Finite zero-coordinate conditions can be checked one hyperplane at a time. -/
private theorem sLocalPrincipalValue_unramified_mem (U : Finset V) (f : ℬₛ) :
    f ∈ sAdeleFiniteZeroSchwartz S U ↔ ∀ (v : S), v.val ∈ U → ∀ x : Aₛ,
      x.2 v = 0 → f (Multiplicative.ofAdd x) = 0 := by
  rw [sAdeleFiniteZeroSchwartz, Submodule.mem_iInf]
  constructor
  · intro hf v hv x hx
    exact hf ⟨x, v, hv, hx⟩
  · intro hf x
    obtain ⟨v, hv, hx⟩ := x.property
    exact hf v hv x.val hx

/-- Normalizing a translation difference preserves its image in a character quotient. -/
private theorem sLocalPrincipalValue_unramified_difference {E Q : Type*}
    [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    (q : E →ₗ[ℂ] Q) (z : ℂ) (hz : z ≠ 1) (f g : E) (h : q f = z • q g) :
    q ((z - 1)⁻¹ • (f - g)) = q g := by
  have hsmul : (z - 1) • q g = z • q g - q g := by rw [sub_smul, one_smul]
  rw [map_smul, map_sub, h, ← hsmul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hz), one_smul]

/-- A normalized translation difference enforces vanishing on one additional
ramified hyperplane while preserving the homogeneous theta class. -/
private theorem sLocalPrincipalValue_unramified_insert (χ : PontryaginDual Jₛ) (w : S)
    (a : Aₛˣ) (ha : (QuotientGroup.mk a : Jₛ) ∈ (mₛ).ker) (hχa : (χ (QuotientGroup.mk a) : ℂ) ≠ 1)
    (hfix : ∀ x : Aₛ, x.2 w = 0 → ((a⁻¹).val : Aₛ) * x = x)
    (U : Finset V) (g : ℬₛ) (hg : g ∈ sAdeleFiniteZeroSchwartz S U) :
    ∃ k ∈ sAdeleFiniteZeroSchwartz S (insert w.val U),
      (thetaQuotient(χ₁(χ))) k = (thetaQuotient(χ₁(χ))) g := by
  classical
  let q := thetaQuotient(χ₁(χ))
  let z : ℂ := χ (QuotientGroup.mk a)
  let g' := schwartzBruhatUnitTranslate a g
  let k := (z - 1)⁻¹ • (g' - g)
  refine ⟨k, (sLocalPrincipalValue_unramified_mem _ _).mpr ?_, ?_⟩
  · intro v hv x hx
    change (z - 1)⁻¹ * (g (Multiplicative.ofAdd (((a⁻¹).val : Aₛ) * x)) -
      g (Multiplicative.ofAdd x)) = 0
    rcases Finset.mem_insert.mp hv with h | h
    · have hvw : v = w := Subtype.ext h
      subst v
      rw [hfix x hx, sub_self, mul_zero]
    · have hvan := (sLocalPrincipalValue_unramified_mem _ g).mp hg v h
      rw [hvan _ (show (((a⁻¹).val : Aₛ) * x).2 v = 0 by
        change _ * x.2 v = 0
        rw [hx, mul_zero]), hvan x hx, sub_self, mul_zero]
  · exact sLocalPrincipalValue_unramified_difference q z hχa g' g
      (sLocalPrincipalValue_unramified_translate (F := F) (S := S) χ a ha g)

/-- If representatives can be made to vanish at one additional place without
changing their class, they can be made to vanish at every remaining place. -/
private theorem sLocalPrincipalValue_unramified_enlarge {ι E Q : Type*}
    [DecidableEq ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    (S T : Finset ι) (hT : T ⊆ S) (Z : Finset ι → Submodule ℂ E) (q : E →ₗ[ℂ] Q)
    (hmono : Z S ≤ Z T) (step : ∀ v ∈ S \ T, ∀ U, ∀ g ∈ Z U,
      ∃ k ∈ Z (insert v U), q k = q g) : (Z S).map q = (Z T).map q := by
  apply le_antisymm (Submodule.map_mono hmono)
  rintro _ ⟨f, hf, rfl⟩
  have enlarge (U : Finset ι) (hU : U ⊆ S \ T) :
      ∃ g ∈ Z (T ∪ U), q g = q f := by
    induction U using Finset.induction_on with
    | empty => exact ⟨f, by simpa using hf, rfl⟩
    | @insert v U _ ih =>
      obtain ⟨g, hg, he⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hU)
      obtain ⟨k, hk, he'⟩ := step v (hU (Finset.mem_insert_self v U)) (T ∪ U) g hg
      exact ⟨k, by simpa only [Finset.union_insert] using hk, he'.trans he⟩
  obtain ⟨g, hg, he⟩ := enlarge (S \ T) (Finset.Subset.refl _)
  rw [Finset.union_sdiff_of_subset hT] at hg
  exact ⟨g, hg, he⟩

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The same homogeneous theta image is obtained by imposing finite zero-coordinate
vanishing only at the unramified places of χ. -/
theorem sLocalPrincipalValue_homogeneousTheta_range_unramified (χ : PontryaginDual Jₛ)
    (T : Finset V) (_hT : T ⊆ S)
    (_hχ : ∀ v : S, v.val ∈ T ↔ ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      sLocalFiniteRestriction v (chartₛ(χ) 0)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) = 1) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S T).map (thetaQuotient(χ₁(χ))) := by
  classical
  rw [sLocalPrincipalValue_homogeneousTheta_range]
  apply sLocalPrincipalValue_unramified_enlarge S T _hT (sAdeleFiniteZeroSchwartz (F := F) S)
    (thetaQuotient(χ₁(χ)))
  · exact fun f hf ↦ (sLocalPrincipalValue_unramified_mem T f).mpr
      fun v _ ↦ (sLocalPrincipalValue_unramified_mem S f).mp hf v v.property
  · intro v hv U g hg
    let w : S := ⟨v, (Finset.mem_sdiff.mp hv).1⟩
    have hram := mt (_hχ w).mpr (Finset.mem_sdiff.mp hv).2
    obtain ⟨a, ha, hχa, hfix⟩ := sLocalPrincipalValue_unramified_unit (F := F) (S := S) χ w hram
    exact sLocalPrincipalValue_unramified_insert (F := F) (S := S) χ w a ha hχa hfix U g hg

end SAdele

end RiemannMasullo
