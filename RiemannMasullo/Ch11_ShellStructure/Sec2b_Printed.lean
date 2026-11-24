module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch11_ShellStructure.Sec2a_PrimePVRefutation
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RiemannMasullo.AppC_LCTVS.Sec3a
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
import Mathlib.Analysis.Normed.Operator.Banach
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

/-! # §11.2.1–11.2.2 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "mₛ(" F ", " S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "Wω(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    0 0 _ (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm F).ker.subtype) ω
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "localTheta(" F ", " S ", " a ", " ω ", " f ")" =>
  modulationWeight (mₛ(F, S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω f)

local notation "qₛ(" F ", " S ", " ω ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)).mkQ

private theorem sec2bP_units (ξ : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) :
    ξ = 1 ∨ ξ = -1 := by
  have hmem : ∀ x : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ),
      ∃ y : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ y = (x : ℚ) := by
    intro x
    have he : ((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ = ⊥ := by
      rw [Finset.coe_empty, integer_empty]
    have hx : (x : ℚ) ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := he ▸ x.property
    exact Algebra.mem_bot.mp hx
  obtain ⟨a, ha⟩ := hmem ξ.val
  obtain ⟨b, hb⟩ := hmem (ξ⁻¹).val
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    have h := congrArg Subtype.val ξ.mul_inv
    exact h
  have hu : IsUnit (Rat.ringOfIntegersEquiv a) := (IsUnit.of_mul_eq_one b hab).map _
  rcases Int.isUnit_iff.mp hu with h | h
  · left
    have ha1 : a = 1 := Rat.ringOfIntegersEquiv.injective (h.trans (map_one _).symm)
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_one]
    rfl
  · right
    have ha1 : a = -1 := Rat.ringOfIntegersEquiv.injective (h.trans (by simp))
    apply Units.ext
    apply Subtype.ext
    rw [← ha, ha1, map_neg, map_one]
    rfl

private theorem sec2bP_one_ne_neg_one :
    (1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ) ≠ -1 := by
  intro h
  have h' := congrArg (fun u : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ ↦
    Subtype.val (Units.val u)) h
  norm_num at h'

private theorem sec2bP_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sec2bP_abs (z : Rat.infinitePlace.Completion) :
    |InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace z| = ‖z‖ := by
  rw [← Real.norm_eq_abs, ← dist_zero_right, ← dist_zero_right z,
    ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq z 0

private theorem sec2bP_thetaClasses (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (φ : ℝ → ℂ) (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace)) +
      φ (-(InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.val.1 Rat.infinitePlace))) := by
  have hU : (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
      (Subring.subtype (integralAdelesOutside ℚ ∅)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)) (-1)) = -1 := by
    apply Units.ext
    change ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val) =
      (-1 : (SAdeleRing ℚ ∅)ˣ).val
    simp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  dsimp only
  rw [tsum_eq_sum (s := {1, -1}) (fun ξ hξ ↦ ?_)]
  · rw [Finset.sum_pair sec2bP_one_ne_neg_one]
    simp only [MonoidHom.comp_apply, hU, map_one, one_mul, hf]
    simp only [Units.val_neg, neg_mul, one_mul]
    rw [show ((-(x : SAdeleRing ℚ ∅)).1 Rat.infinitePlace) =
      -((x : SAdeleRing ℚ ∅).1 Rat.infinitePlace) from rfl, map_neg]
  · rcases sec2bP_units ξ with h | h <;> simp_all

private theorem sec2bP_normOne_trivial (h : (sIdeleQuotientNorm ℚ ∅).ker) : h = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  apply Subtype.ext
  change (QuotientGroup.mk x : SIdeleQuotient ℚ ∅) = 1
  rw [sIdeleQuotient_mk_eq_one]
  have hn : ‖x.val.1 Rat.infinitePlace‖ = 1 := by
    rw [← sec2bP_norm]
    have h1 : sIdeleNorm ℚ ∅ x = 1 := hg
    rw [h1]
    simp
  rw [← sec2bP_abs] at hn
  rcases (abs_eq zero_le_one).mp hn with h1 | h1
  · refine ⟨1, ?_⟩
    simp only [map_one]
    apply Units.ext
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans (map_one _).symm
  · refine ⟨-1, ?_⟩
    apply Units.ext
    change (x : SAdeleRing ℚ ∅) = ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅
        (-1 : (Set.integer ((∅ : Finset V(ℚ)) : Set V(ℚ)) ℚ)ˣ).val)
    simp only [Units.val_neg, Units.val_one, map_neg, map_one]
    refine Prod.ext (funext fun w ↦ ?_) (Subsingleton.elim _ _)
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).injective
    exact h1.trans ((map_neg _ _).trans (congrArg Neg.neg (map_one _))).symm

open LineDeriv in
private theorem sec2bP_lineDeriv_tsupport (f : SchwartzMap ℝ ℂ) :
    tsupport ⇑(∂_{(1 : ℝ)} f : SchwartzMap ℝ ℂ) ⊆ tsupport ⇑f := by
  apply closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra h
  apply hx
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    image_eq_zero_of_notMem_tsupport (fun h' ↦ h (tsupport_fderiv_subset ℝ h'))]
  rfl

open scoped FourierTransform in
open LineDeriv in
private theorem sec2bP_test : ∃ φ : SchwartzMap ℝ ℂ,
    φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧ HasCompactSupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ∧
      tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1 ∧
      ∃ c > 0, ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖ := by
  let b : ContDiffBump (1 / 16 : ℝ) := ⟨1 / 64, 1 / 32, by norm_num, by norm_num⟩
  have hb_supp : HasCompactSupport (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ ↦ (b ξ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ₀ : SchwartzMap ℝ ℂ := hb_supp.toSchwartzMap hb_smooth
  have hψ₀ (ξ : ℝ) : ψ₀ ξ = (b ξ : ℂ) := rfl
  let ψ : SchwartzMap ℝ ℂ := ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} ψ₀)
  have hφ (t : ℝ) : (𝓕⁻ ψ) t = ((-(4 * Real.pi ^ 2 * t ^ 2) : ℝ) : ℂ) * (𝓕⁻ ψ₀) t := by
    have hg : (fun x : ℝ ↦ inner ℝ x (1 : ℝ)).HasTemperateGrowth := by fun_prop
    simp only [ψ, SchwartzMap.fourierInv_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    simp only [inner, one_mul, star_trivial, RCLike.re_to_real, Complex.real_smul]
    push_cast
    linear_combination ((4 : ℂ) * Real.pi ^ 2 * t ^ 2 * (𝓕⁻ ψ₀) t) * Complex.I_sq
  have htsψ₀ : tsupport ⇑ψ₀ ⊆ Metric.closedBall (1 / 16) (1 / 32) := by
    rw [← b.tsupport_eq]
    exact tsupport_comp_subset Complex.ofReal_zero _
  have htsψ : tsupport ⇑ψ ⊆ Metric.closedBall (1 / 16) (1 / 32) :=
    (sec2bP_lineDeriv_tsupport _).trans ((sec2bP_lineDeriv_tsupport _).trans htsψ₀)
  have hF : 𝓕 (𝓕⁻ ψ) = ψ := FourierTransform.fourier_fourierInv_eq ψ
  refine ⟨𝓕⁻ ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hφ]
    simp
  · rw [hF]
    refine image_eq_zero_of_notMem_tsupport fun h ↦ ?_
    have h' := htsψ h
    rw [Metric.mem_closedBall, Real.dist_eq] at h'
    norm_num [abs_le] at h'
  · rw [hF]
    exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsψ
  · rw [hF]
    refine htsψ.trans (Metric.closedBall_subset_closedBall' ?_)
    norm_num
  · have hint (t : ℝ) : Integrable (fun ξ : ℝ ↦ 𝐞 (inner ℝ ξ t) • ψ₀ ξ) := by
      refine ψ₀.integrable.norm.mono' (by fun_prop) (ae_of_all _ fun ξ ↦ ?_)
      rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
    have hsum (t : ℝ) : ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re =
        ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Real.fourierInv_eq,
        ← integral_add (hint t) (hint (-t))]
      refine (integral_re ((hint t).add (hint (-t)))).symm.trans ?_
      congr 1
      funext ξ
      simp only [Circle.smul_def, hψ₀, Real.fourierChar_apply, inner, star_trivial, RCLike.re_to_real]
      simp only [Pi.add_apply, smul_eq_mul, RCLike.re_to_complex, Complex.add_re,
        Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
      rw [show -t * ξ = -(t * ξ) by ring, mul_neg, Real.cos_neg, mul_comm ξ t]
      ring
    have hb_int : 0 < ∫ ξ, b ξ := b.integral_pos
    refine ⟨4 * Real.pi ^ 2 * ∫ ξ, b ξ, by positivity, fun t ht ↦ ?_⟩
    have hle : ∫ ξ, b ξ ≤ ∫ ξ, 2 * Real.cos (2 * Real.pi * (ξ * t)) * b ξ := by
      refine integral_mono b.integrable ?_ fun ξ ↦ ?_
      · exact (b.integrable.const_mul 2).mono'
          (Continuous.aestronglyMeasurable (by have := b.continuous; fun_prop))
          (ae_of_all _ fun ξ ↦ by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg (b.nonneg' ξ), Real.norm_two,
              Real.norm_eq_abs]
            have := Real.abs_cos_le_one (2 * Real.pi * (ξ * t))
            have := b.nonneg' ξ
            calc 2 * |Real.cos (2 * Real.pi * (ξ * t))| * b ξ ≤ 2 * 1 * b ξ := by gcongr
              _ = 2 * b ξ := by ring)
      · by_cases hξ : b ξ = 0
        · simp [hξ]
        have hmem : ξ ∈ Metric.ball (1 / 16 : ℝ) (1 / 32) := by
          rw [← b.support_eq]; exact hξ
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hmem
        have hx : |2 * Real.pi * (ξ * t)| ≤ 2 * 3.15 * (3 / 32) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
          have h1 : |ξ| ≤ 3 / 32 := by rw [abs_le]; constructor <;> linarith
          have := Real.pi_lt_d2
          have h2 : |ξ| * |t| ≤ 3 / 32 := by
            calc |ξ| * |t| ≤ 3 / 32 * 1 := by gcongr
              _ = 3 / 32 := by ring
          have h3 : 2 * Real.pi * (|ξ| * |t|) ≤ 2 * 3.15 * (3 / 32) := by
            gcongr
          exact h3
        have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (ξ * t))
        have hsq : (2 * Real.pi * (ξ * t)) ^ 2 ≤ (2 * 3.15 * (3 / 32)) ^ 2 := by
          rw [← sq_abs]; gcongr
        have hcos : 1 / 2 ≤ Real.cos (2 * Real.pi * (ξ * t)) := by norm_num at hsq; linarith
        have h2c : (1 : ℝ) ≤ 2 * Real.cos (2 * Real.pi * (ξ * t)) := by linarith
        have h4 := mul_le_mul_of_nonneg_right h2c (b.nonneg' ξ)
        rwa [one_mul] at h4
    have heq : (𝓕⁻ ψ) t + (𝓕⁻ ψ) (-t) =
        (((-(4 * Real.pi ^ 2 * t ^ 2)) : ℝ) : ℂ) * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)) := by
      rw [hφ, hφ]; push_cast; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity)]
    calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2
        ≤ 4 * Real.pi ^ 2 * t ^ 2 * ((𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)).re := by
          rw [hsum]
          have : 0 ≤ 4 * Real.pi ^ 2 * t ^ 2 := by positivity
          calc 4 * Real.pi ^ 2 * (∫ ξ, b ξ) * t ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 * (∫ ξ, b ξ) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hle this
      _ ≤ 4 * Real.pi ^ 2 * t ^ 2 * ‖(𝓕⁻ ψ₀) t + (𝓕⁻ ψ₀) (-t)‖ := by
          gcongr; exact Complex.re_le_norm _
    exact le_rfl

/-- The trivial character restricted to the norm-one classes is unramified outside `S = ∅`. -/
private theorem sec2bP_unramified :
    NormOneCharacterUnramifiedOutside ((1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Over ℚ with `S = ∅` the S-integers are a principal ideal ring. -/
private theorem sec2bP_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The norm-one quotient over ℚ with `S = ∅` is a point of positive finite mass. -/
private theorem sec2bP_mass_pos : 0 < (sLocalNormOneQuotientMeasure ℚ ∅).real univ := by
  have := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1
  have : Subsingleton (sIdeleQuotientNorm ℚ ∅).ker :=
    ⟨fun a b ↦ (sec2bP_normOne_trivial a).trans (sec2bP_normOne_trivial b).symm⟩
  have : Finite (sIdeleQuotientNorm ℚ ∅).ker := Finite.of_subsingleton
  have : CompactSpace (sIdeleQuotientNorm ℚ ∅).ker := Finite.compactSpace
  exact ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨1, trivial⟩).ne'
    isCompact_univ.measure_lt_top.ne

/-- Over ℚ with `S = ∅` the homogeneous theta function is the theta function on classes
times the total norm-one mass. -/
private theorem sec2bP_homTheta (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (g : SIdeleQuotient ℚ ∅) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f g =
      ((sLocalNormOneQuotientMeasure ℚ ∅).real univ : ℂ) * sLocalAdelicThetaOnClasses ℚ ∅ f g := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply,
    integral_congr_ae (g := fun _ ↦ sLocalAdelicThetaOnClasses ℚ ∅ f g) (ae_of_all _ fun h ↦ ?_)]
  · rw [integral_const, Complex.real_smul]
  · have := sec2bP_normOne_trivial h
    subst this
    simp

/-- The test of the counterexample weighted by the inverse square of the norm stays
bounded below on classes of norm less than one. -/
private theorem sec2bP_lower (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) (x : (SAdeleRing ℚ ∅)ˣ)
    (hx : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) < 1) :
    (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c ≤
      ‖localTheta(ℚ, ∅, -2, ω, f) (QuotientGroup.mk x)‖ := by
  set t := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
    (x.val.1 Rat.infinitePlace) with ht
  have hr : ((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) = |t| := by
    rw [ht, sec2bP_abs]; exact sec2bP_norm x
  have hpos : 0 < |t| := by
    rw [← hr]; exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  have hν := sec2bP_mass_pos
  have h1 := hlow t (by rw [← hr]; exact hx.le)
  change ‖((((sIdeleQuotientNorm ℚ ∅ (QuotientGroup.mk x) : ℝ≥0) : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) *
    sLocalHomogeneousAdelicThetaLinearMap ℚ ∅ ω f (QuotientGroup.mk x)‖ ≥ _
  rw [sec2bP_homTheta, sec2bP_thetaClasses f φ hf x, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hν.le, hr,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
    Real.rpow_neg (abs_nonneg t), Real.rpow_two, ← ht]
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have hne : |t| ^ 2 ≠ 0 := by positivity
  calc (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c
      = (|t| ^ 2)⁻¹ * ((sLocalNormOneQuotientMeasure ℚ ∅).real univ * (c * t ^ 2)) := by
        rw [ht2]; field_simp
    _ ≤ _ := by gcongr

/-- A left-invariant measure on a group with a continuous surjection onto the positive reals
gives infinite mass to the elements of norm less than one. -/
private theorem sec2bP_measure {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure]
    (N : G →* ℝ≥0ˣ) (hN : Continuous N) (hs : Function.Surjective N) :
    μ {g | ((N g : ℝ≥0) : ℝ) < 1} = ⊤ := by
  obtain ⟨t, ht⟩ := hs (Units.mk0 (2 : ℝ≥0) two_ne_zero)
  obtain ⟨g₀, hg₀⟩ := hs (Units.mk0 (3 / 4 : ℝ≥0) (by norm_num))
  have hcont : Continuous fun g ↦ ((N g : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hN)
  let A : Set G := {g | 1 / 2 < ((N g : ℝ≥0) : ℝ) ∧ ((N g : ℝ≥0) : ℝ) < 1}
  have hAo : IsOpen A :=
    (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
  have hg₀A : g₀ ∈ A := by
    simp only [A, mem_ofPred_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
    norm_num
  have hA0 : μ A ≠ 0 := (hAo.measure_pos μ ⟨g₀, hg₀A⟩).ne'
  let B (k : ℕ) : Set G := (fun g ↦ t ^ k * g) ⁻¹' A
  have hB (k : ℕ) (g : G) : g ∈ B k ↔
      1 / 2 < 2 ^ k * ((N g : ℝ≥0) : ℝ) ∧ 2 ^ k * ((N g : ℝ≥0) : ℝ) < 1 := by
    show (1 / 2 < ((N (t ^ k * g) : ℝ≥0) : ℝ) ∧ ((N (t ^ k * g) : ℝ≥0) : ℝ) < 1) ↔ _
    rw [map_mul, map_pow, ht]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, NNReal.coe_mul,
      NNReal.coe_pow, NNReal.coe_ofNat]
  have hmeas (k : ℕ) : μ (B k) = μ A := measure_preimage_mul μ (t ^ k) A
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    have key (k l : ℕ) (h : k < l) (g : G) (h1 : g ∈ B k) (h2 : g ∈ B l) : False := by
      rw [hB] at h1 h2
      have h2l : (2 : ℝ) * 2 ^ k ≤ 2 ^ l := by
        calc (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) := by ring
          _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) h
      have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      nlinarith
    intro k l hkl
    rw [Function.onFun, Set.disjoint_left]
    intro g h1 h2
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h g h1 h2
    · exact key l k h g h2 h1
  have hsub : (⋃ k, B k) ⊆ {g | ((N g : ℝ≥0) : ℝ) < 1} := by
    intro g hg
    obtain ⟨k, hk⟩ := mem_iUnion.mp hg
    rw [hB] at hk
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ ((N g : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    simp only [mem_ofPred_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0

/-- The weighted theta function of the counterexample is not square integrable. -/
private theorem sec2bP_not_memLp (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (φ : SchwartzMap ℝ ℂ) (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace)))
    (c : ℝ) (hc : 0 < c) (hlow : ∀ t : ℝ, |t| ≤ 1 → c * t ^ 2 ≤ ‖φ t + φ (-t)‖) :
    ¬ MemLp (localTheta(ℚ, ∅, -2, ω, f)) 2 (localMeasure(ℚ, ∅, 0)) := by
  intro hm
  have hμ : localMeasure(ℚ, ∅, 0) = μₛ(ℚ, ∅) := by
    conv_rhs => rw [← withDensity_one (μ := μₛ(ℚ, ∅))]
    congr 1
    funext g
    simp [intervalSobolevDensity]
  rw [hμ] at hm
  let Θ := localTheta(ℚ, ∅, -2, ω, f)
  have hint : Integrable (fun g ↦ ‖Θ g‖ ^ (2 : ℝ)) μₛ(ℚ, ∅) := by
    simpa using hm.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) :=
    (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sec2bP_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  set K := (sLocalNormOneQuotientMeasure ℚ ∅).real univ * c with hK
  have hKpos : 0 < K := mul_pos sec2bP_mass_pos hc
  have hlow' : ∀ g ∈ B, ENNReal.ofReal (K ^ (2 : ℝ)) ≤ ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := sec2bP_lower ω φ f hf c hlow x hg
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hKpos.le h1 (by norm_num))
  have hfin : (∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅)) < ⊤ := hint.hasFiniteIntegral
  have hge : ⊤ ≤ ∫⁻ g, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) :=
    calc (⊤ : ENNReal) = ENNReal.ofReal (K ^ (2 : ℝ)) * μₛ(ℚ, ∅) B := by
          rw [hB, ENNReal.mul_top (by simp; positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (K ^ (2 : ℝ)) ∂μₛ(ℚ, ∅) := (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖Θ g‖ ^ (2 : ℝ)‖ₑ ∂μₛ(ℚ, ∅) := setLIntegral_mono' hBm hlow'
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)

/-- The transition from `∅` to itself is the identity. -/
private theorem sec2bP_transition (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f = f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f
    (Multiplicative.ofAdd (Multiplicative.toAdd x)) = f x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl

/-- The test of the counterexample has compact Fourier support inside the unit ball
at the real place. -/
private theorem sec2bP_inBand (φ : SchwartzMap ℝ ℂ)
    (hts : tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) ⊆ Metric.closedBall 0 1)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      tsupport (sAdeleSchwartzFourier f).val ⊆
        Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
  let r : Multiplicative (SAdeleRing ℚ ∅) → ℝ := fun y ↦
    InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
      ((Multiplicative.toAdd y).1 Rat.infinitePlace)
  have hr : Continuous r :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).continuous.comp
      ((continuous_apply _).comp (continuous_fst.comp continuous_toAdd))
  have hsub : tsupport (sAdeleSchwartzFourier f).val ⊆
      r ⁻¹' tsupport ⇑(FourierTransform.fourier φ : SchwartzMap ℝ ℂ) := by
    refine closure_minimal (fun y hy ↦ ?_) ((isClosed_tsupport _).preimage hr)
    refine subset_tsupport _ ?_
    rw [mem_support] at hy ⊢
    rwa [← sAdeleSchwartzFourier_ratEmpty_apply φ f hf]
  have hsub' : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' {x : SAdeleRing ℚ ∅ | ‖x.1 Rat.infinitePlace‖ ≤ 1} := by
    intro y hy
    have h := hts (hsub hy)
    rw [Metric.mem_closedBall, dist_zero_right] at h
    change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ≤ 1
    rwa [← sec2bP_abs, ← Real.norm_eq_abs]
  refine ⟨?_, hsub'⟩
  refine (isCompact_sLocalPWBox (F := ℚ) (S := ∅) 1).of_isClosed_subset (isClosed_tsupport _)
    (fun y hy ↦ ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩)
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hsub' hy

/-- The test of the counterexample lies in the polar subspace. -/
private theorem sec2bP_polar (φ : SchwartzMap ℝ ℂ) (hφ0 : φ 0 = 0)
    (hFφ0 : (FourierTransform.fourier φ : SchwartzMap ℝ ℂ) 0 = 0)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      φ (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
        (x.1 Rat.infinitePlace))) :
    sAdeleSchwartzTransition ℚ (le_refl (∅ : Finset V(ℚ))) f ∈ sAdelePolarSubspace ℚ ∅ := by
  rw [sec2bP_transition, mem_sAdelePolarSubspace, sAdeleSchwartzFourier_ratEmpty_apply φ f hf, hf]
  exact ⟨by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero, hφ0],
    by rw [show ((0 : SAdeleRing ℚ ∅).1 Rat.infinitePlace) = 0 from rfl, map_zero]; exact hFφ0⟩

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
The absolute local closure presupposes that each weighted class in the §7.3.2 level is in
the ambient Sobolev space, for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalAbsolutePWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalAbsolutePW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), pp. 487–488.
Take F = ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0.
Let H be the inverse Fourier transform of a nonzero nonnegative even smooth bump
supported where 1/8 < |ξ| < 1/4. The test is (H(u) - H(2u)) times the 2-adic
integer indicator. Both zero moments vanish. At the class of (t, 1), the local
theta series telescopes to 2 H(t), up to the positive norm-one Haar mass.
Since H(0) > 0, its squared integral against dt/t diverges at zero. -/
theorem Printed.sLocalAbsolutePWSobolev_memLp_false :
    ¬ Printed.sLocalAbsolutePWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalAbsolutePW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦
    ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩⟩ (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
The invariant local closure presupposes Sobolev membership of the weighted
classes in the §7.3.2 level for every real twist and every nonnegative degree.
Deviation: Express membership on representatives of all classes in the §7.3.2 level. -/
def Printed.sLocalInvariantPWSobolev_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (S : Finset V(F))
    (hω : NormOneCharacterUnramifiedOutside
      (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))) S),
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (Λ a s : ℝ), 0 < Λ → 0 ≤ s →
      let ω := sLocalNormOneCharacter S _ hω
      ∀ f, qₛ(F, S, ω) f ∈ sLocalInvariantPW (S := S) (T := S) le_rfl Λ
          (sAdelePolarSubspace F S) ω →
        MemLp (localTheta(F, S, a, ω, f)) 2 (localMeasure(F, S, s))

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), pp. 488–489.
Use ℚ, S = {∞, 2}, χ = 1, Λ = 1 and a = s = 0. The test
(H(u) - H(2u)) times the 2-adic integer indicator from the absolute-level
counterexample also lies in the invariant region. Its Fourier support satisfies
|ξ∞| ≤ 1 and |ξ₂|₂ ≤ 1. The local theta is proportional to 2 H(t) and is outside L²(dt/t). -/
theorem Printed.sLocalInvariantPWSobolev_memLp_false :
    ¬ Printed.sLocalInvariantPWSobolev_memLp := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  obtain ⟨φ, hφ0, hFφ0, -, hts, c, hc, hlow⟩ := sec2bP_test
  refine sec2bP_not_memLp _ φ (E φ) (hE φ) c hc hlow
    (h ℚ 1 ∅ sec2bP_unramified sec2bP_pic 1 (-2) 0 one_pos le_rfl (E φ) ?_)
  have hb := sec2bP_inBand φ hts (E φ) (hE φ)
  rw [← sec2bP_transition (E φ)]
  refine sLocalInvariantPW_mk_mem _ _ _ _ (E φ) ⟨hb.1, hb.2.trans fun y hy ↦ ?_⟩
    (sec2bP_polar φ hφ0 hFφ0 _ (hE φ))
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  change (∏ w : InfinitePlace ℚ, ‖(Multiplicative.toAdd y).1 w‖ ^ w.mult) *
    (∏ v : (∅ : Finset V(ℚ)), ‖(Multiplicative.toAdd y).2 v‖) ≤ 1
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  change ‖(Multiplicative.toAdd y).1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ 1
  rw [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  exact hy

local notation "GeoIsotype(" F ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) (m𝔽(F))
    (-(0 : ℝ)) 0 _ (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "cutoffConv(" F ", " hs ", " ω ", " a ", " hρ ", " φ ")" =>
  ((GeoIsotype(F, hs, ω)).orthogonalProjectionOnto.comp
    ((geometricTruncatedConvolution (F := F) a (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
      (GeoIsotype(F, hs, ω)).subtypeL))
local notation "aboveOne(" F ", " φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽(F)).val ⊆ {g | 1 ≤ ((m𝔽(F) g).val : ℝ)})
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
For every fixed cutoff, the trace-norm limit of absolute condensation is asserted
to be the uncompressed cutoff geometric convolution.
Deviation: Use the global absolute projector specified by the declared codomain
in (11.2.1.3), with the Fourier box bound X = Λ. -/
def Printed.absolutePWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- A trace-norm limit of right products determines the operator value on a pointwise limit. -/
private theorem absolutePWCondensation_traceNorm_tendsto_false_apply
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (P : ℝ → H →L[ℂ] H) (u v : H)
    (hP : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v))
    (hT : Tendsto (fun Λ ↦ traceNorm
      ((⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ : nuclearEndomorphisms H) - T))
      atTop (𝓝 0)) : T.val v = T.val u := by
  by_cases hu : u = 0
  · subst u
    simp only [map_zero] at hP ⊢
    rw [tendsto_nhds_unique hP tendsto_const_nhds, map_zero]
  let f := innerSL ℂ u
  let A := f.smulRight u
  let D (Λ : ℝ) : nuclearEndomorphisms H :=
    ⟨T.val * P Λ, mul_mem_nuclearEndomorphisms_right (P Λ) T⟩ - T
  have hbound (Λ : ℝ) : ‖f‖ * ‖T.val (P Λ u) - T.val u‖ ≤ ‖A‖ * traceNorm (D Λ) := by
    have hmul : (D Λ).val * A = f.smulRight (T.val (P Λ u) - T.val u) := by
      ext1 x
      simp [D, A, smul_sub]
    rw [← traceNorm_smulRight f (T.val (P Λ u) - T.val u)]
    have hprod : (⟨(D Λ).val * A, mul_mem_nuclearEndomorphisms_right A (D Λ)⟩ :
        nuclearEndomorphisms H) =
        ⟨f.smulRight (T.val (P Λ u) - T.val u), smulRight_mem_nuclearEndomorphisms _ _⟩ :=
      Subtype.ext hmul
    rw [← hprod]
    exact traceNorm_mul_right_le A (D Λ)
  have hLeft : Tendsto (fun Λ ↦ ‖f‖ * ‖T.val (P Λ u) - T.val u‖) atTop
      (𝓝 (‖f‖ * ‖T.val v - T.val u‖)) :=
    tendsto_const_nhds.mul (((T.val.continuous.tendsto v).comp hP).sub tendsto_const_nhds).norm
  have hRight : Tendsto (fun Λ ↦ ‖A‖ * traceNorm (D Λ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hT
  have hle := le_of_tendsto_of_tendsto' hLeft hRight hbound
  have hf : 0 < ‖f‖ := by simpa only [f, innerSL_apply_norm, norm_pos_iff] using hu
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (nonpos_of_mul_nonpos_right hle hf) (norm_nonneg _)))

open scoped nonZeroDivisors in
/-- The rational integers have trivial Picard group. -/
private theorem rational_empty_picTrivial :
    Subsingleton (CommRing.Pic (((∅ : Finset V(ℚ)) : Set V(ℚ)).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The restriction of the trivial rational character is unramified everywhere. -/
private theorem rational_one_unramifiedOutside_empty :
    NormOneCharacterUnramifiedOutside
      ((1 : PontryaginDual C𝔽(ℚ)).comp
        (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) ∅ := by
  refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Expanding smooth cutoffs preserve the nonzero image of a vector under a continuous map. -/
private theorem rational_cutoffConv_cutoff_image_ne_zero
    {G E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace E] [T1Space E] [Zero E]
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (Q : Lp ℂ 2 ν → E) (hQ : Continuous Q)
    (y : Lp ℂ 2 ν) (hy : Q y ≠ 0) :
    ∃ (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ),
      Q (modulatedCutoffOperator m ν hρ y) ≠ 0 := by
  classical
  let ε (R : ℝ) := R⁻¹ ^ 2
  have hcut (R : ℝ) (hR : 3 ≤ R) : ∃ ρ : G → ℝ, IsModulatedCutoff m R (ε R) ρ := by
    have hRpos : 0 < R := by positivity
    have hi : 0 < R⁻¹ := inv_pos.mpr hRpos
    have hie : R⁻¹ ≤ 1 / 3 := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 3) hR
    have he : 0 < ε R := by dsimp [ε]; positivity
    have he' : ε R ≤ R⁻¹ / 3 := by
      dsimp [ε]
      nlinarith [mul_nonneg hi.le (sub_nonneg.mpr hie)]
    have hRight : 1 < R - ε R := by linarith
    have hRightpos : 0 < R - ε R := by linarith
    have hInv : (R - ε R)⁻¹ ≤ R⁻¹ + ε R := by
      rw [← one_div]
      apply (div_le_iff₀ hRightpos).2
      have hRI : R⁻¹ * R = 1 := inv_mul_cancel₀ hRpos.ne'
      have hDifference : 0 ≤ ε R * ((R - ε R) - R⁻¹) :=
        mul_nonneg he.le (by linarith)
      nlinarith only [hDifference, hRI]
    let B : ContDiffBump (0 : ℝ) :=
      ⟨Real.log (R - ε R), Real.log R, Real.log_pos hRight,
        Real.log_lt_log hRightpos (sub_lt_self R he)⟩
    let r (x : G) : ℝ := (m x).val
    have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
    let ρ (x : G) := B (Real.log (r x))
    have h1 : ρ 1 = 1 := by
      apply B.one_of_mem_closedBall
      simp [r, B.rIn_pos.le]
    refine ⟨ρ, hRpos, he, by linarith, by linarith,
      fun _ ↦ B.nonneg, fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
    · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
      simp only [Finset.coe_empty, sdiff_empty]
      exact B.contDiff.comp_contDiffOn
        (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
    · intro x
      change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
    · apply closure_minimal _ (isClosed_Icc.preimage hr)
      intro x hx
      have hmem : Real.log (r x) ∈ support B := hx
      rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      obtain ⟨hl, hu⟩ := abs_lt.mp hmem
      change R⁻¹ ≤ r x ∧ r x ≤ R
      rw [← Real.log_le_log_iff hi (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hRpos]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      change -Real.log (R - ε R) ≤ _ ∧ _ ≤ Real.log (R - ε R)
      rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr hRightpos) (hpos x),
        Real.log_le_log_iff (hpos x) hRightpos]
      change R⁻¹ + ε R ≤ r x ∧ r x ≤ R - ε R at hx
      exact ⟨hInv.trans hx.1, hx.2⟩
  let ρ (R : ℝ) : G → ℝ := if h : 3 ≤ R then (hcut R h).choose else 1
  have hρ : ∀ᶠ R in atTop, IsModulatedCutoff m R (ε R) (ρ R) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    simpa only [ρ, dite_eq_left hR] using (hcut R hR).choose_spec
  let σ (R : ℝ) : G → ℝ := if IsModulatedCutoff m R (ε R) (ρ R) then ρ R else 1
  let P (R : ℝ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
    if h : IsModulatedCutoff m R (ε R) (ρ R) then modulatedCutoffOperator m ν h else 1
  have hσ (R : ℝ) : Measurable (σ R) := by
    dsimp only [σ]
    split_ifs with h
    · exact h.measurable
    · exact measurable_const
  have hσbound (R : ℝ) (x : G) : |σ R x| ≤ 1 := by
    dsimp only [σ]
    split_ifs with h
    · exact h.abs_le_one x
    · simp
  have hP (R : ℝ) : (P R y : G → ℂ) =ᵐ[ν] fun x ↦ (σ R x : ℂ) * y x := by
    dsimp only [P, σ]
    split_ifs with h
    · exact modulatedCutoffOperator_apply m ν h y
    · simp
  have hinv : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have heps : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hinv.pow 2
  have hl : Tendsto (fun R : ℝ ↦ R⁻¹ + ε R) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.add heps
  have hright : Tendsto (fun R : ℝ ↦ R - ε R) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [heps.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      eventually_ge_atTop (b + 1)] with R he hR
    linarith
  have hpoint (x : G) : ∀ᶠ R in atTop, σ R x = 1 := by
    have hx : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    filter_upwards [hρ, hl.eventually (gt_mem_nhds hx), hright.eventually_ge_atTop ((m x).val : ℝ)]
      with R hR hleft hright
    simpa only [σ, ite_eq_left hR, Pi.one_apply] using hR.eq_one ⟨hleft.le, hright⟩
  let d (R : ℝ) (x : G) : ℂ := (σ R x : ℂ) * y x - y x
  have hd (R : ℝ) : AEStronglyMeasurable (d R) ν :=
    (((Complex.measurable_ofReal.comp (hσ R)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable y)).sub (Lp.aestronglyMeasurable y))
  have hbound (R : ℝ) (x : G) : ‖d R x‖ ^ 2 ≤ 4 * ‖y x‖ ^ 2 := by
    have h : ‖d R x‖ ≤ 2 * ‖y x‖ := calc
      ‖d R x‖ ≤ ‖(σ R x : ℂ) * y x‖ + ‖y x‖ := norm_sub_le _ _
      _ = |σ R x| * ‖y x‖ + ‖y x‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := by nlinarith [hσbound R x, norm_nonneg (y x)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ 2 * ‖y x‖ + ‖d R x‖ by positivity)]
  have hint : Integrable (fun x ↦ 4 * ‖y x‖ ^ 2) ν :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y)).const_mul 4
  have hconv : Tendsto (fun R ↦ ∫ x, ‖d R x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℝ))
      (F := fun R x ↦ ‖d R x‖ ^ 2) (f := fun _ : G ↦ (0 : ℝ)) (fun x ↦ 4 * ‖y x‖ ^ 2)
      (.of_forall fun R ↦ (hd R).norm.pow 2) (.of_forall fun R ↦ .of_forall fun x ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbound R x) hint
      (.of_forall fun x ↦ tendsto_const_nhds.congr' ((hpoint x).mono fun R hR ↦ by simp [d, hR]))
    simpa using h
  have heq (R : ℝ) : ‖P R y - y‖ ^ 2 = ∫ x, ‖d R x‖ ^ 2 ∂ν := by
    let v := P R y - y
    have hv : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂ν := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re]
      · exact integral_congr_ae (.of_forall fun x ↦ (norm_sq_eq_re_inner (𝕜 := ℂ) (v x)).symm)
      · exact L2.integrable_inner v v
    rw [hv]
    apply integral_congr_ae
    filter_upwards [hP R, Lp.coeFn_sub (P R y) y] with x hx hsub
    rw [show v x = P R y x - y x from hsub, hx]
  have hP_lim : Tendsto (fun R ↦ P R y) atTop (𝓝 y) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq : Tendsto (fun R ↦ ‖P R y - y‖ ^ 2) atTop (𝓝 0) := by
      simpa only [heq] using hconv
    simpa using hsq.sqrt
  have hlim : Tendsto (fun R ↦ Q (P R y)) atTop (𝓝 (Q y)) := (hQ.tendsto (x := y)).comp hP_lim
  have hne : ∀ᶠ R in atTop, Q (P R y) ≠ 0 := hlim.eventually (isOpen_ne.mem_nhds hy)
  obtain ⟨R, hR, hneR⟩ := (hρ.and hne).exists
  exact ⟨R, ε R, ρ R, hR, by simpa only [P, dite_eq_left hR] using hneR⟩

/-- A smooth function of the logarithmic module is Bruhat smooth. On each
structural quotient, compose the descended positive quasi-character with log. -/
private theorem rational_cutoffConv_bruhatSmooth_logProfile
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f) :
    IsBruhatSmooth (fun x ↦ (f (Real.log ((m x).val : ℝ)) : ℂ)) := by
  let χ : QuasiCharacter G :=
    { toFun := fun x ↦ ((m x).val : ℝ)
      map_one' := by simp
      map_mul' := fun x y ↦ by simp
      continuous_toFun := Complex.continuous_ofReal.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)) }
  intro p
  obtain ⟨k, hk, hinv, hdesc⟩ :=
    (mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ) p
  refine ⟨k, hk, fun h x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hinv h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  have hpos (y : a.quotient) : 0 < (q y).re := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hq]
    exact NNReal.coe_pos.mpr (Units.zero_lt _)
  refine ⟨fun y ↦ (f (Real.log (q y).re) : ℂ),
    fun x ↦ congrArg (fun z : ℂ ↦ (f (Real.log z.re) : ℂ)) (hq x), ?_⟩
  intro e z b
  exact Complex.ofRealCLM.contDiff.comp ((hf.of_le (by simp)).comp
    ((Complex.reCLM.contDiff.comp (hdiff e z b)).log fun x ↦ (hpos _).ne'))

/-- A nonzero projected translate at norm greater than one survives averaging by a
smooth compactly supported function of the log norm. -/
private theorem rational_cutoffConv_positive_test
    {G E H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) (j : ℝ≥0ˣ → G)
    (hj : Continuous j) (hj' : RightInverse j m) (μ : Measure G) [μ.IsHaarMeasure]
    (τ : G →* (E →L[ℂ] E)) (hτ : Continuous (fun p : G × E ↦ τ p.1 p.2))
    (Q : E →L[ℂ] H) (u : E) (hu : ∀ k : m.toMonoidHom.ker, τ k.val u = u)
    (g₀ : G) (hg₀ : 1 < ((m g₀).val : ℝ)) (hne : Q (τ g₀ u) ≠ 0) :
    ∃ φ : BruhatCompactSupport G, tsupport φ.val ⊆ {g | 1 ≤ ((m g).val : ℝ)} ∧
      Q (bruhatRegularizedAction μ τ hτ φ u) ≠ 0 := by
  have hfiber (g : G) : τ g u = τ (j (m g)) u := by
    let t := j (m g)
    let k : m.toMonoidHom.ker := ⟨g / t, by
      change m (g / t) = 1
      rw [map_div, show m t = m g from hj' (m g), div_self']⟩
    have ht : t * k.val = g := by
      rw [mul_comm t k.val]
      exact div_mul_cancel g t
    calc
      τ g u = τ (t * k.val) u := congrArg (fun x ↦ τ x u) ht.symm
      _ = τ t (τ k.val u) := congrArg (fun A : E →L[ℂ] E ↦ A u) (τ.map_mul t k.val)
      _ = τ t u := congrArg (τ t) (hu k)
  let l : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hl (t : ℝ≥0ˣ) : l t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let x₀ := l (m g₀)
  have hx₀ : 0 < x₀ := by
    rw [show x₀ = Real.log ((m g₀).val : ℝ) from hl _]
    exact Real.log_pos hg₀
  let ζ := Q (τ g₀ u)
  let δ : E →L[ℂ] ℂ := (innerSL ℂ ζ).comp Q
  let c (x : ℝ) : ℝ := (δ (τ (j (l.symm x)) u)).re
  have horbit : Continuous (fun g ↦ τ g u) := hτ.comp (continuous_id.prodMk continuous_const)
  have hc : Continuous c := Complex.continuous_re.comp
    (δ.continuous.comp (horbit.comp (hj.comp l.symm.continuous)))
  have hcenter : 0 < c x₀ := by
    change 0 < (δ (τ (j (l.symm (l (m g₀)))) u)).re
    rw [l.symm_apply_apply, ← hfiber g₀]
    change 0 < (innerSL ℂ ζ ζ).re
    rw [innerSL_apply_apply]
    change 0 < RCLike.re (inner ℂ ζ ζ)
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne)
  have hnhds : {x | 0 < c x} ∩ Ioi 0 ∈ 𝓝 x₀ :=
    ((isOpen_lt continuous_const hc).inter isOpen_Ioi).mem_nhds ⟨hcenter, hx₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let b : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let f (g : G) : ℂ := (b (l (m g)) : ℂ)
  have hzero (g : G) (hg : l (m g) ∉ Metric.closedBall x₀ (r / 2)) : f g = 0 := by
    change (b (l (m g)) : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport (f := (b : ℝ → ℝ)) (by simpa only [b.tsupport_eq] using hg), Complex.ofReal_zero]
  have hcomp : HasCompactSupport f :=
    HasCompactSupport.intro ((l.isProperMap.comp hm).isCompact_preimage (isCompact_closedBall x₀ (r / 2))) hzero
  have hbs : IsBruhatSmooth f := by
    simpa only [f, hl] using rational_cutoffConv_bruhatSmooth_logProfile m b.contDiff
  let φ : BruhatCompactSupport G := ⟨f, (mem_bruhatSmoothSubmodule_iff _).mpr hbs, hcomp⟩
  have hsupport : tsupport f ⊆ (l ∘ m) ⁻¹' Metric.closedBall x₀ (r / 2) :=
    closure_minimal (fun g hg ↦ by
      by_contra hn
      exact hg (hzero g hn)) (Metric.isClosed_closedBall.preimage (l.continuous.comp hm.continuous))
  refine ⟨φ, fun g hg ↦ ?_, ?_⟩
  · have hg' := (hball (Metric.closedBall_subset_ball (by linarith) (hsupport hg))).2
    change 0 < l (m g) at hg'
    rw [hl] at hg'
    exact (Real.log_pos_iff (NNReal.coe_nonneg _)).mp hg' |>.le
  · let k (g : G) : ℂ := f g * δ (τ g u)
    have hk : Continuous k := (continuous_of_bruhatSmooth hbs).mul (δ.continuous.comp horbit)
    have hkc : HasCompactSupport k := hcomp.mul_right
    have hreal (g : G) : (k g).re = b (l (m g)) * c (l (m g)) := by
      change ((b (l (m g)) : ℂ) * δ (τ g u)).re = _
      rw [Complex.re_ofReal_mul, hfiber g]
      simp only [c, l.symm_apply_apply]
    have hnonneg : 0 ≤ fun g ↦ (k g).re := by
      intro g
      change 0 ≤ (k g).re
      rw [hreal]
      by_cases hb : b (l (m g)) = 0
      · simp [hb]
      · have hb' : l (m g) ∈ Metric.ball x₀ (r / 2) := by
          rw [← b.support_eq]
          exact hb
        exact mul_nonneg b.nonneg (hball (Metric.ball_subset_ball (by linarith) hb')).1.le
    have hval : (k g₀).re ≠ 0 := by
      rw [hreal]
      change b x₀ * c x₀ ≠ 0
      rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_mul]
      exact hcenter.ne'
    have hpos : 0 < ∫ g, (k g).re ∂μ :=
      (Complex.continuous_re.comp hk).integral_pos_of_hasCompactSupport_nonneg_ne_zero
        (hkc.comp_left Complex.zero_re) hnonneg hval
    have hIntegral : δ (bruhatRegularizedAction μ τ hτ φ u) = ∫ g, k g ∂μ := by
      have h := bruhatRegularizedAction_apply μ τ hτ φ u
      refine (congrArg (fun z : PettisWeakCompletion E ↦
        (show Module.Dual ℂ (StrongDual ℂ E) from z) δ) h.2).trans ?_
      exact integral_congr_ae (.of_forall fun g ↦ δ.map_smul (f g) (τ g u))
    intro heq
    have hδ : δ (bruhatRegularizedAction μ τ hτ φ u) = 0 := by
      change (innerSL ℂ ζ) (Q (bruhatRegularizedAction μ τ hτ φ u)) = 0
      rw [heq, map_zero]
    have hIreal : (∫ g, (k g).re ∂μ) = (∫ g, k g ∂μ).re :=
      integral_re (𝕜 := ℂ) (hk.integrable_of_hasCompactSupport hkc)
    rw [hIreal, ← hIntegral, hδ, Complex.zero_re] at hpos
    exact (lt_irrefl 0) hpos

/-- The action on the trivial isotype fixes vectors along the restricted subgroup. -/
private theorem rational_cutoffConv_fixed
    {G L E : Type*} [Monoid G] [Monoid L] [TopologicalSpace L]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (τ : G →* (E →L[ℂ] E)) (i : L →* G) (ω : PontryaginDual L)
    (hω : ∀ k, (ω k : ℂ) = 1) (u : actionIsotype (τ.comp i) ω) (k : L) :
    τ (i k) u.val = u.val := by
  have h := (mem_actionIsotype (τ.comp i) ω u.val).mp u.property k
  change τ (i k) u.val = (ω k : ℂ) • u.val at h
  rw [hω k, one_smul] at h
  exact h

/-- Bruhat averaging and then cutoff multiplication preserve some nonzero
projected orbit value when the orbit is fixed by the norm-one subgroup. -/
private theorem rational_cutoffConv_of_projected_translate
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsProperMap m) (j : ℝ≥0ˣ → G)
    (hj : Continuous j) (hj' : RightInverse j m) (μ ν : Measure G) [μ.IsHaarMeasure]
    (τ : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν))
    (hτ : Continuous (fun p : G × Lp ℂ 2 ν ↦ τ p.1 p.2))
    (P : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (O : Lp ℂ 2 ν →L[ℂ] H) (u : Lp ℂ 2 ν)
    (hu : ∀ k : m.toMonoidHom.ker, τ k.val u = u) (g : G)
    (hg : 1 < ((m g).val : ℝ)) (hne : O (P (τ g u)) ≠ 0) :
    ∃ (φ : BruhatCompactSupport G), tsupport φ.val ⊆ {g | 1 ≤ ((m g).val : ℝ)} ∧
      ∃ (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ),
        O (modulatedCutoffOperator m ν hρ (P (bruhatRegularizedAction μ τ hτ φ u))) ≠ 0 := by
  obtain ⟨φ, hφ, htest⟩ := rational_cutoffConv_positive_test m hm j hj hj' μ τ hτ (O.comp P) u hu g hg hne
  obtain ⟨R, ε, ρ, hρ, hcut⟩ := rational_cutoffConv_cutoff_image_ne_zero m ν O O.continuous
    (P (bruhatRegularizedAction μ τ hτ φ u)) htest
  exact ⟨φ, hφ, R, ε, ρ, hρ, hcut⟩

/-- For a commutative action, a vector of an isotype killed by a symmetric idempotent
`P` whose translate is not killed satisfies the projected conditions. On the isotype,
`P v` is orthogonal to it only if `⟪P v, v⟫ = ‖P v‖²` vanishes. -/
private theorem rational_cutoffConv_positive_translate_of_projection
    {G L E : Type*} [CommMonoid G] [Monoid L] [TopologicalSpace L]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (τ : G →* (E →L[ℂ] E)) (i : L →* G) (ω : PontryaginDual L)
    (hc : CompleteSpace ↥(actionIsotype (τ.comp i) ω))
    (P : E →L[ℂ] E) (hsymm : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hidem : ∀ x, P (P x) = P x) (r : G → ℝ)
    (h : ∃ (u : E) (g : G), u ∈ actionIsotype (τ.comp i) ω ∧ 1 < r g ∧
      P u = 0 ∧ P (τ g u) ≠ 0) :
    ∃ (v : actionIsotype (τ.comp i) ω) (g : G), 1 < r g ∧
      (actionIsotype (τ.comp i) ω).orthogonalProjectionOnto (P v.val) = 0 ∧
      (actionIsotype (τ.comp i) ω).orthogonalProjectionOnto (P (τ g v.val)) ≠ 0 := by
  obtain ⟨u, g, hu, hr, hPu, hPg⟩ := h
  have hg : τ g u ∈ actionIsotype (τ.comp i) ω := by
    refine (mem_actionIsotype (τ.comp i) ω _).mpr fun k ↦ ?_
    have hk := (mem_actionIsotype (τ.comp i) ω u).mp hu k
    change τ (i k) (τ g u) = (ω k : ℂ) • τ g u
    change τ (i k) u = (ω k : ℂ) • u at hk
    have e : τ (i k) * τ g = τ g * τ (i k) := by rw [← map_mul, ← map_mul, mul_comm]
    calc τ (i k) (τ g u) = (τ (i k) * τ g) u := rfl
      _ = τ g (τ (i k) u) := by rw [e]; rfl
      _ = (ω k : ℂ) • τ g u := by rw [hk, map_smul]
  refine ⟨⟨u, hu⟩, g, hr, ?_, fun h ↦ hPg ?_⟩
  · change (actionIsotype (τ.comp i) ω).orthogonalProjectionOnto (P u) = 0
    rw [hPu, map_zero]
  · have h0 : inner ℂ ((actionIsotype (τ.comp i) ω).orthogonalProjectionOnto (P (τ g u)))
        (⟨τ g u, hg⟩ : actionIsotype (τ.comp i) ω) = 0 := by
      change inner ℂ ((actionIsotype (τ.comp i) ω).orthogonalProjectionOnto
        (P (τ g (⟨u, hu⟩ : actionIsotype (τ.comp i) ω).val))) _ = 0
      rw [h, inner_zero_left]
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right] at h0
    change inner ℂ (P (τ g u)) (τ g u) = 0 at h0
    rw [← hidem (τ g u), hsymm] at h0
    exact inner_self_eq_zero.mp h0

/-- The Riesz vector `exp(-iγx)/(1+x²)` of the log norm `x` is square integrable
for the weight `1+x²` of the compact-interval Sobolev space on `[-0, 0]` with `s = 2`. -/
private theorem rational_cutoffConv_rieszVector_memLp
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hsurj : Surjective m)
    (μ : Measure G) [μ.IsHaarMeasure] (γ : ℝ) :
    MemLp (fun g : G ↦ Complex.exp (-((γ * Real.log ((m g).val : ℝ) : ℝ) : ℂ) * Complex.I) /
        ((1 + Real.log ((m g).val : ℝ) ^ 2 : ℝ) : ℂ)) 2
      (μ.withDensity fun g ↦ ENNReal.ofReal
        (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)))) := by
  have hL : Continuous (fun g : G ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hint := (modulatedSobolev_reciprocal_integrable_iff m μ hm hsurj (s := 2)
    (by norm_num)).mpr (by norm_num)
  have hpos (g : G) : 0 < 1 + Real.log ((m g).val : ℝ) ^ 2 := by positivity
  have hw (g : G) : intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)) =
      1 + Real.log ((m g).val : ℝ) ^ 2 := by
    simp [intervalSobolevDensity]
  have hcont : Continuous (fun g : G ↦
      Complex.exp (-((γ * Real.log ((m g).val : ℝ) : ℝ) : ℂ) * Complex.I) /
        ((1 + Real.log ((m g).val : ℝ) ^ 2 : ℝ) : ℂ)) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun g ↦ ?_
    exact Complex.ofReal_ne_zero.mpr (hpos g).ne'
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable,
    integrable_withDensity_iff (by
      simp only [hw]
      exact ((continuous_const.add (hL.pow 2)).measurable).ennreal_ofReal)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine hint.congr (ae_of_all _ fun g ↦ ?_)
  dsimp only
  rw [hw, ENNReal.toReal_ofReal (hpos g).le, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (hpos g).le, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, sq_abs]
  rw [show (-2 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  field_simp

/-- A function of the log norm is fixed by the Hardy–Sobolev translation by any
element of norm one. -/
private theorem rational_cutoffConv_rieszVector_fixed
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hs : (0 : ℝ) ≤ 2) (f : G → ℂ)
    (hf : MemLp f 2 (μ.withDensity fun g ↦ ENNReal.ofReal
        (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)))))
    (hrad : ∀ k x : G, m k = 1 → f (k⁻¹ * x) = f x) (k : G) (hk : m k = 1) :
    hardySobolevTranslation μ m (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs k
      (hf.toLp f) = hf.toLp f := by
  have hpos (x : G) : 0 < intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m x).val : ℝ)) := by
    simp only [intervalSobolevDensity]
    positivity
  have hac : (μ.withDensity fun g ↦ ENNReal.ofReal
      (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)))) ≪ μ :=
    withDensity_absolutelyContinuous _ _
  have hac' : μ ≪ μ.withDensity fun g ↦ ENNReal.ofReal
      (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ))) := by
    refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun x ↦ ?_)
    · have hL : Continuous (fun g : G ↦ Real.log ((m g).val : ℝ)) :=
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
          fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      have hw (g : G) : intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)) =
          1 + Real.log ((m g).val : ℝ) ^ 2 := by
        simp [intervalSobolevDensity]
      simp only [hw]
      exact ((continuous_const.add (hL.pow 2)).measurable).ennreal_ofReal.aemeasurable
    · exact ENNReal.ofReal_ne_zero_iff.mpr (hpos x)
  have h1 := hardySobolevTranslation_apply μ m (-(0 : ℝ)) 0 2
    (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs k (hf.toLp f)
  have h2 : ((hf.toLp f : _) : G → ℂ) =ᵐ[μ] f := hac'.ae_le (MemLp.coeFn_toLp hf)
  have h3 := (measurePreserving_mul_left μ k⁻¹).quasiMeasurePreserving.ae_eq_comp h2
  apply Lp.ext
  refine hac.ae_le ?_
  filter_upwards [h1, h3, h2] with x e1 e3 e2
  rw [e1]
  change ((hf.toLp f : _) : G → ℂ) (k⁻¹ * x) = _
  rw [show ((hf.toLp f : _) : G → ℂ) (k⁻¹ * x) = f (k⁻¹ * x) from e3, hrad k x hk, e2]

/-- A function of the log norm lies in the trivial isotype of any subgroup of norm-one
elements. -/
private theorem rational_cutoffConv_rieszVector_mem
    {G L : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [Monoid L] [TopologicalSpace L]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hs : (0 : ℝ) ≤ 2) (f : G → ℂ)
    (hf : MemLp f 2 (μ.withDensity fun g ↦ ENNReal.ofReal
        (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log ((m g).val : ℝ)))))
    (hrad : ∀ k x : G, m k = 1 → f (k⁻¹ * x) = f x) (i : L →* G) (hi : ∀ k, m (i k) = 1)
    (ω : PontryaginDual L) (hω : ∀ k, (ω k : ℂ) = 1) :
    hf.toLp f ∈ actionIsotype ((hardySobolevTranslation μ m (-(0 : ℝ)) 0 2
      (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).comp i) ω := by
  refine (mem_actionIsotype _ _ _).mpr fun k ↦ ?_
  rw [hω k, one_smul]
  exact rational_cutoffConv_rieszVector_fixed μ m hs f hf hrad (i k) (hi k)

/-- A rational zeta zero on the critical line has positive finite Hecke order. -/
private theorem rational_cutoffConv_rieszVector_order (γ : ℝ)
    (hγ : riemannZeta (1 / 2 + γ * Complex.I) = 0) :
    0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ)))
      (1 / 2 + γ * Complex.I)).untop₀.toNat := by
  let z : ℂ := 1 / 2 + γ * Complex.I
  have hre : z.re = 1 / 2 := by simp [z]
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  change 0 < (meromorphicOrderAt _ z).untop₀.toNat
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  have hn : meromorphicOrderAt riemannZeta z ≠ ⊤ := by
    refine hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (2 : ℂ))
      (mem_univ z) ?_
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 2 (mem_univ _))).2
      (((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.eventually_ne
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))).filter_mono nhdsWithin_le_nhds)
  have hp : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at hγ
    rw [← hγ]
    exact (differentiableAt_riemannZeta (fun h ↦ by norm_num [h] at hre)).continuousAt.continuousWithinAt
  rw [← Int.pos_iff_toNat_pos]
  exact WithTop.coe_lt_coe.mp (by simpa only [WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_zero] using hp)

/-- The degree-two density on the zero-width strip is positive and measurable. -/
private theorem rational_cutoffConv_weight_two :
    let w (x : C𝔽(ℚ)) := intervalSobolevDensity (-0) 0 2 (logIdeleClassNorm ℚ x)
    Measurable w ∧ ∀ x, 0 < w x := by
  intro w
  have hl : Continuous (logIdeleClassNorm ℚ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽(ℚ)).continuous)).log
      fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hw (x) : w x = 1 + logIdeleClassNorm ℚ x ^ 2 := by simp [w, intervalSobolevDensity]
  rw [funext hw]
  exact ⟨(continuous_const.add (hl.pow 2)).measurable, fun x ↦ by positivity⟩

/-- Base-measure almost-everywhere representatives can be recovered from a strictly positive density. -/
private theorem rational_cutoffConv_haar_ac {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w : X → ℝ} (hm : Measurable w) (hw : ∀ x, 0 < w x) :
    μ ≪ μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) :=
  withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hw x))

/-- The weighted inner product, written with respect to the base measure. -/
private theorem rational_cutoffConv_inner {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (u v : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) :
    Integrable (fun x ↦ (w x : ℂ) * (v x * star (u x))) μ ∧
      inner ℂ u v = ∫ x, (w x : ℂ) * (v x * star (u x)) ∂μ := by
  have hfin := ae_of_all μ (fun x ↦ ENNReal.ofReal_lt_top (r := w x))
  have he (x) : (ENNReal.ofReal (w x)).toReal • inner ℂ (u x) (v x) =
      (w x : ℂ) * (v x * star (u x)) := by
    simp only [ENNReal.toReal_ofReal (hw x), RCLike.inner_apply, starRingEnd_apply, Complex.real_smul]
  refine ⟨((integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal hfin).mp
    (L2.integrable_inner u v)).congr (.of_forall he), ?_⟩
  rw [L2.inner_def, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal hfin]
  exact integral_congr_ae (.of_forall he)

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488 (step of the refutation).
At an ordinate γ of a critical-line zeta zero, the Riesz vector `exp(-iγx)/(1+x²)` of the
log norm `x` is orthogonal to the half-weighted theta closure: its inner product with
`|g|^(1/2) θ_f(g)` is the conjugate of the Mellin transform of `θ_f` at `1/2 + iγ`, which
is a multiple of the completed zeta function there. -/
private theorem rational_cutoffConv_rieszVector_theta_orthogonal (hs : (0 : ℝ) ≤ 2) (γ : ℝ)
    (hγ : riemannZeta (1 / 2 + γ * Complex.I) = 0) :
    geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
      ((rational_cutoffConv_rieszVector_memLp (m𝔽(ℚ))
        ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
        ratIdeleNormSection_class_rightInverse.surjective (ideleClassTamagawaMeasure ℚ)
        γ).toLp _) = 0 := by
  let μ := ideleClassTamagawaMeasure ℚ
  let l := logIdeleClassNorm ℚ
  let w (x : C𝔽(ℚ)) := intervalSobolevDensity (-0) 0 2 (l x)
  have hw (x) : w x = 1 + l x ^ 2 := by simp [w, intervalSobolevDensity]
  obtain ⟨hm, hp⟩ : Measurable w ∧ ∀ x, 0 < w x := rational_cutoffConv_weight_two
  let χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ) := fun _ ↦ 1
  let j : SpectralStripJetIndex χ (1/2) 0 2 := ⟨(1, 0, γ, 0), by
    rw [spectralStripMultiplicity_boundary le_rfl (Or.inr rfl), lt_spectralBoundaryMultiplicity]
    refine ⟨?_, by norm_num⟩
    simpa only [χ, add_zero, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      rational_cutoffConv_rieszVector_order γ hγ⟩
  have hj := spectralStripJet_memLp χ (le_rfl (a := (0 : ℝ))) hs j
  have hf := rational_cutoffConv_rieszVector_memLp (m𝔽(ℚ))
    ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
    ratIdeleNormSection_class_rightInverse.surjective μ γ
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  apply (Submodule.mem_orthogonal' _ _).mpr
  intro y hy
  have hz := spectralStripJet_commonKernel_forward χ le_rfl hs y hy j
  rw [(rational_cutoffConv_inner μ w hm (fun x ↦ (hp x).le) _ y).2]
  refine Eq.trans ?_ hz
  apply integral_congr_ae
  have he := (rational_cutoffConv_haar_ac μ hm hp).ae_eq hf.coeFn_toLp
  have he' := (rational_cutoffConv_haar_ac μ hm.inv (fun x ↦ inv_pos.mpr (hp x))).ae_eq hj.coeFn_toLp
  filter_upwards [he, he'] with x hx hx'
  change (w x : ℂ) * (y x * star ((hf.toLp _) x)) = y x * (hj.toLp _) x
  rw [hx, hx']
  change (w x : ℂ) * (y x * star (Complex.exp (-((γ * l x : ℝ) : ℂ) * Complex.I) /
    ((1 + l x ^ 2 : ℝ) : ℂ))) = y x * spectralZeroJet 1 0 γ 0 x
  rw [hw]
  simp only [spectralZeroJet, pow_zero, mul_one, Complex.ofReal_zero, zero_add]
  change _ = y x * (1 * (((ideleClassNorm ℚ x).val : ℝ) : ℂ) ^ ((γ : ℂ) * Complex.I))
  rw [one_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'), ← Complex.ofReal_log (NNReal.coe_nonneg _)]
  simp only [Complex.star_def, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
    map_neg, Complex.conj_I, neg_mul_neg]
  change ((1 + l x ^ 2 : ℝ) : ℂ) * (y x * (Complex.exp _ / _)) = y x * Complex.exp ((l x : ℂ) * _)
  rw [Complex.ofReal_mul, mul_assoc, mul_left_comm (γ : ℂ)]
  have hn : ((1 + l x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp [hn]

/-- Left invariance transfers a simultaneous translation in the two arguments of the
weighted inner product to a shift of its density. -/
private theorem rational_cutoffConv_shifted_inner {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] (w : G → ℝ)
    (hw : Measurable w) (hp : ∀ x, 0 ≤ w x) (g : G)
    (u v : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))) (U V : G → ℂ)
    (hu : (u : G → ℂ) =ᵐ[μ] fun x ↦ U (g⁻¹ * x))
    (hv : (v : G → ℂ) =ᵐ[μ] fun x ↦ V (g⁻¹ * x)) :
    Integrable (fun x ↦ (w (g * x) : ℂ) * (V x * star (U x))) μ ∧
      inner ℂ u v = ∫ x, (w (g * x) : ℂ) * (V x * star (U x)) ∂μ := by
  let f (x : G) := (w x : ℂ) * (v x * star (u x))
  obtain ⟨hi, he⟩ := rational_cutoffConv_inner μ w hw hp u v
  have ha := measurePreserving_mul_left μ g
  have h : (fun x ↦ f (g * x)) =ᵐ[μ] fun x ↦ (w (g * x) : ℂ) * (V x * star (U x)) := by
    filter_upwards [ha.quasiMeasurePreserving.ae_eq_comp hu, ha.quasiMeasurePreserving.ae_eq_comp hv]
      with x hx hy
    change u (g * x) = U (g⁻¹ * (g * x)) at hx
    change v (g * x) = V (g⁻¹ * (g * x)) at hy
    simp only [f, hx, hy, inv_mul_cancel_left]
  exact ⟨((ha.integrable_comp_emb (measurableEmbedding_mulLeft g)).mpr hi).congr h,
    he.trans ((integral_mul_left_eq_self f g).symm.trans (integral_congr_ae h))⟩

/-- Three equally spaced shifts of the quadratic density recover the unweighted integral. -/
private theorem rational_cutoffConv_second_difference {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (f : X → ℂ)
    (h : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x ↦ ((1 + (t + l x) ^ 2 : ℝ) : ℂ) * f x) μ ∧
      (∫ x, ((1 + (t + l x) ^ 2 : ℝ) : ℂ) * f x ∂μ) = 0) :
    ∫ x, f x ∂μ = 0 := by
  let p (t : ℝ) (x : X) := ((1 + (t + l x) ^ 2 : ℝ) : ℂ) * f x
  have hp (t : ℝ) (ht : 0 ≤ t) : Integrable (p t) μ ∧ ∫ x, p t x ∂μ = 0 := h t ht
  obtain ⟨h₀, e₀⟩ := hp 0 (by norm_num)
  obtain ⟨h₁, e₁⟩ := hp 1 (by norm_num)
  obtain ⟨h₂, e₂⟩ := hp 2 (by norm_num)
  have e (x : X) : 2 * f x = p 2 x - p 1 x - p 1 x + p 0 x := by
    simp only [p]; push_cast; ring
  have hzero : 2 * (∫ x, f x ∂μ) = 0 := by
    have ha := integral_add ((h₂.sub h₁).sub h₁) h₀
    have hb := integral_sub (h₂.sub h₁) h₁
    simp only [Pi.sub_apply] at ha hb
    rw [← integral_const_mul, integral_congr_ae (.of_forall e), ha, hb, integral_sub h₂ h₁,
      e₀, e₁, e₂]
    ring
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- In the width-zero strip at Sobolev order zero, the strict cutoff discards every
jet. Thus the polar-free theta tests are dense for the unweighted norm. -/
private theorem rational_cutoffConv_unweighted_mem
    (u : CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-0) 0 0) :
    u ∈ globalThetaSobolev ℚ (1/2) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) (le_rfl (a := (0 : ℝ))) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  apply (spectralStripJet_commonKernel χ hχ (le_rfl (a := (0 : ℝ))) le_rfl u).mpr
  intro j
  have hb := (SpectralStripJetIndex.mem_strip_order_pos le_rfl j).1
  have hz : j.val.2.1 = 0 := le_antisymm hb.2 (by simpa only [neg_zero] using hb.1)
  have hj := j.property
  simp only [hz, spectralStripMultiplicity_boundary le_rfl (Or.inr rfl),
    lt_spectralBoundaryMultiplicity] at hj
  have hn := Nat.cast_nonneg (α := ℝ) j.val.2.2.2
  linarith [hj.2]

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488 (step of the refutation).
At an ordinate γ of a critical-line zeta zero, some translate of the Riesz vector
`exp(-iγx)/(1+x²)` by an idele class of norm greater than one is not orthogonal to the
half-weighted theta closure. Simultaneously translating a theta test shifts the quadratic
weight in the pairing. At log norms 0, 1 and 2 its second difference recovers twice the
unweighted pairing, and polar-free theta tests are dense in unweighted L². -/
private theorem rational_cutoffConv_rieszVector_translate (hs : (0 : ℝ) ≤ 2) (γ : ℝ)
    (hγ : riemannZeta (1 / 2 + γ * Complex.I) = 0) :
    ∃ g : C𝔽(ℚ), 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
        (hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
          (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs g
          ((rational_cutoffConv_rieszVector_memLp (m𝔽(ℚ))
            ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
            ratIdeleNormSection_class_rightInverse.surjective (ideleClassTamagawaMeasure ℚ)
            γ).toLp _)) ≠ 0 := by
  let μ := ideleClassTamagawaMeasure ℚ
  let l := logIdeleClassNorm ℚ
  let w (s : ℝ) (x : C𝔽(ℚ)) := intervalSobolevDensity (-0) 0 s (l x)
  let W (s : ℝ) := Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w s x)))
  let hl₀ := neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))
  let Θ := globalThetaSobolev ℚ (1/2) hl₀ hs
  let τ := hardySobolevTranslation μ (m𝔽(ℚ)) (-0) 0 2 hl₀ hs
  let U (x : C𝔽(ℚ)) := Complex.exp (-((γ * l x : ℝ) : ℂ) * Complex.I) /
    ((1 + l x ^ 2 : ℝ) : ℂ)
  have hU : MemLp U 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w 2 x))) :=
    rational_cutoffConv_rieszVector_memLp (m𝔽(ℚ))
      ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
      ratIdeleNormSection_class_rightInverse.surjective μ γ
  have hw (x) : w 2 x = 1 + l x ^ 2 := by simp [w, intervalSobolevDensity]
  have hw₀ (x) : w 0 x = 1 := by simp [w, intervalSobolevDensity]
  obtain ⟨hm, hp⟩ : Measurable (w 2) ∧ ∀ x, 0 < w 2 x := rational_cutoffConv_weight_two
  have hm₀ : Measurable (w 0) := by rw [funext hw₀]; exact measurable_const
  have hp₀ (x) : 0 < w 0 x := (hw₀ x).symm ▸ zero_lt_one
  have hU₀ : MemLp U 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (w 0 x))) :=
    hU.mono_measure (withDensity_mono (.of_forall fun x ↦ ENNReal.ofReal_le_ofReal
      (by rw [hw₀, hw]; linarith [sq_nonneg (l x)])))
  let u := hU.toLp U
  let u₀ := hU₀.toLp U
  have hu : (u : C𝔽(ℚ) → ℂ) =ᵐ[μ] U := (rational_cutoffConv_haar_ac μ hm hp).ae_eq hU.coeFn_toLp
  have hu₀ : (u₀ : C𝔽(ℚ) → ℂ) =ᵐ[μ] U := (rational_cutoffConv_haar_ac μ hm₀ hp₀).ae_eq hU₀.coeFn_toLp
  by_contra! h
  have hproj (g : C𝔽(ℚ)) (hg : 1 < ((m𝔽(ℚ) g).val : ℝ)) :
      τ g u ∈ Θ.orthogonal := (Θ.starProjection_apply_eq_zero_iff).mp (h g hg)
  let E (s : ℝ) (hs' : 0 ≤ s) :=
    (existsUnique_globalThetaSobolevEmbedding (F := ℚ) (1/2) (-0) 0 s hl₀ hs').exists.choose
  let L := innerSL ℂ u₀
  -- Compare the two Sobolev embeddings on the same polar-free theta test.
  have hR : (E 0 le_rfl).toLinearMap.range ≤ L.ker := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let V := modulationWeight (m𝔽(ℚ)) (1/2) (adelicTheta f.val)
    let v := E 2 hs (Submodule.Quotient.mk f)
    let v₀ := E 0 le_rfl (Submodule.Quotient.mk f)
    have hv : (v : C𝔽(ℚ) → ℂ) =ᵐ[μ] V :=
      (existsUnique_globalThetaSobolevEmbedding (F := ℚ) (1/2) (-0) 0 2 hl₀ hs).exists.choose_spec.2 f
    have hv₀ : (v₀ : C𝔽(ℚ) → ℂ) =ᵐ[μ] V :=
      (existsUnique_globalThetaSobolevEmbedding (F := ℚ) (1/2) (-0) 0 0 hl₀ le_rfl).exists.choose_spec.2 f
    have hvΘ : v ∈ Θ := Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ _)
    change inner ℂ u₀ v₀ = 0
    rw [(rational_cutoffConv_inner μ (w 0) hm₀ (fun x ↦ (hp₀ x).le) u₀ v₀).2]
    refine (integral_congr_ae (g := fun x ↦ V x * star (U x)) ?_).trans ?_
    · filter_upwards [hu₀, hv₀] with x hx hy
      simp only [hw₀, Complex.ofReal_one, one_mul, hx, hy]
    apply rational_cutoffConv_second_difference μ l
    intro t ht
    obtain ⟨g, hlg, hor⟩ : ∃ g : C𝔽(ℚ), l g = t ∧ τ g u ∈ Θ.orthogonal := by
      rcases ht.eq_or_lt with rfl | ht
      · refine ⟨1, by simp [l, logIdeleClassNorm], ?_⟩
        rw [map_one, one_apply_eq_self]
        exact Θ.starProjection_apply_eq_zero_iff.mp (rational_cutoffConv_rieszVector_theta_orthogonal hs γ hγ)
      · obtain ⟨g, hg⟩ := ratIdeleNormSection_class_rightInverse.surjective
          (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
        have hlg : l g = t := by
          change Real.log ((ideleClassNorm ℚ g).val : ℝ) = t
          rw [← positiveRealLogEquiv_apply, hg, positiveRealLogEquiv.apply_symm_apply]
          rfl
        exact ⟨g, hlg, hproj g ((Real.log_pos_iff (NNReal.coe_nonneg _)).mp (hlg.trans_gt ht))⟩
    have hgw (x) : w 2 (g * x) = 1 + (t + l x) ^ 2 := by
      rw [hw, ← hlg]
      have hmul : l (g * x) = l g + l x := by
        dsimp only [l, logIdeleClassNorm]
        rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
      rw [hmul]
    have hcomp (z : W 2) (Z : C𝔽(ℚ) → ℂ) (hz : (z : C𝔽(ℚ) → ℂ) =ᵐ[μ] Z) :
        (τ g z : C𝔽(ℚ) → ℂ) =ᵐ[μ] fun x ↦ Z (g⁻¹ * x) :=
      (hardySobolevTranslation_apply μ (m𝔽(ℚ)) (-0) 0 2 hl₀ hs g z).trans
        ((measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae_eq_comp hz)
    obtain ⟨hi, he⟩ := rational_cutoffConv_shifted_inner μ (w 2) hm (fun x ↦ (hp x).le)
      g (τ g u) (τ g v) U V (hcomp u U hu) (hcomp v V hv)
    simp only [hgw] at hi he
    have htv : τ g v ∈ Θ := by
      obtain ⟨ρ, hρ, _⟩ := exists_globalThetaSobolevAction (F := ℚ) (1/2) hl₀ hs
      exact hρ g ⟨v, hvΘ⟩ ▸ (ρ g ⟨v, hvΘ⟩).property
    exact ⟨hi, he.symm.trans ((Submodule.mem_orthogonal' _ _).mp hor _ htv)⟩
  have hself := (E 0 le_rfl).toLinearMap.range.topologicalClosure_minimal hR L.isClosed_ker
    (rational_cutoffConv_unweighted_mem u₀)
  have hz : u₀ = 0 := inner_self_eq_zero.mp (show inner ℂ u₀ u₀ = 0 from hself)
  have hae : U =ᵐ[μ] 0 := hu₀.symm.trans (by
    rw [hz]
    exact (rational_cutoffConv_haar_ac μ hm₀ hp₀).ae_eq (Lp.coeFn_zero ..))
  obtain ⟨x, hx⟩ := hae.exists
  exact div_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr (by positivity)) hx

/-- Assemble the witness from a vector of the isotype, its orthogonality and a translate. -/
private theorem rational_cutoffConv_theta_orthogonal_translate_of {E G : Type*} [Zero E]
    (P : E → E) (τ : G → E → E) (K : Set E) (r : G → ℝ) (u : E) (hu : u ∈ K) (h0 : P u = 0)
    (h : ∃ g, 1 < r g ∧ P (τ g u) ≠ 0) :
    ∃ (v : E) (g : G), v ∈ K ∧ 1 < r g ∧ P v = 0 ∧ P (τ g v) ≠ 0 :=
  h.elim fun g hg ↦ ⟨u, g, hu, hg.1, h0, hg.2⟩

/-- Some vector of the rational trivial isotype is orthogonal to the half-weighted
theta closure, while one of its translates by an idele class of norm greater
than one is not: the Riesz vector at the first critical-line zeta zero. -/
private theorem rational_cutoffConv_theta_orthogonal_translate (hs : (0 : ℝ) ≤ 2)
    (ω : PontryaginDual C₁(ℚ))
    (_hω : ω = (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) :
    ∃ (u : CompactIntervalSobolev (ideleClassTamagawaMeasure ℚ)
        (fun g : C𝔽(ℚ) ↦ Real.log (((m𝔽(ℚ)) g).val : ℝ)) (-(0 : ℝ)) 0 2) (g : C𝔽(ℚ)),
      u ∈ GeoIsotype(ℚ, hs, ω) ∧ 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs u = 0 ∧
      geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
        (hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
          (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs g u) ≠ 0 := by
  subst _hω
  obtain ⟨γ, -, hγ⟩ := HardyFirstZero.first_zero_on_line
  have hf := rational_cutoffConv_rieszVector_memLp (m𝔽(ℚ))
    ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
    ratIdeleNormSection_class_rightInverse.surjective (ideleClassTamagawaMeasure ℚ) γ
  have hmem := rational_cutoffConv_rieszVector_mem (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ)) hs _ hf
    (fun k x hk ↦ by simp only [map_mul, map_inv, hk, inv_one, one_mul])
    (ideleClassNorm ℚ).ker.subtype (fun k ↦ k.property)
    ((1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ)))
    (fun _ ↦ rfl)
  exact rational_cutoffConv_theta_orthogonal_translate_of
    (geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs)
    (fun g ↦ hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
          (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs g)
    _ (fun g ↦ ((m𝔽(ℚ) g).val : ℝ)) (hf.toLp _) hmem
    (rational_cutoffConv_rieszVector_theta_orthogonal hs γ hγ)
    (rational_cutoffConv_rieszVector_translate hs γ hγ)

/-- A theta-orthogonal vector in the rational trivial isotype has a translate with
nonzero geometric projection at some norm greater than one."""
 At an ordinate γ of a
critical-line zero, use the Riesz vector `exp(-iγx)/(1+x²)` in log norm. Mellin
factorization gives its orthogonality. The pairing with a nonzero radial theta
profile is a Cauchy convolution with a nowhere-zero Fourier multiplier. Its
nonvanishing somewhere, together with inversion and the conjugate zero, gives
a positive translation. -/
private theorem rational_cutoffConv_positive_translate (hs : (0 : ℝ) ≤ 2)
    (ω : PontryaginDual C₁(ℚ))
    (_hω : ω = (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))) :
    let K := GeoIsotype(ℚ, hs, ω)
    letI : CompleteSpace ↥K :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    let τ := hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
      (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs
    let P := geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
    ∃ (u : K) (g : C𝔽(ℚ)), 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      K.orthogonalProjectionOnto (P u.val) = 0 ∧
      K.orthogonalProjectionOnto (P (τ g u.val)) ≠ 0 :=
  rational_cutoffConv_positive_translate_of_projection
    (hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
      (-(0 : ℝ)) 0 2 (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs)
    (ideleClassNorm ℚ).ker.subtype ω
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
    (geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs)
    (globalThetaSobolev ℚ (1 / 2) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))) |>.trans le_rfl)
      hs).inner_starProjection_left_eq_right
    (fun x ↦ congrArg (fun T ↦ T x)
      (globalThetaSobolev ℚ (1 / 2) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))) |>.trans le_rfl)
        hs).isIdempotentElem_starProjection.eq)
    (fun g ↦ ((m𝔽(ℚ) g).val : ℝ))
    (rational_cutoffConv_theta_orthogonal_translate hs ω _hω)

/-- A fixed-cutoff geometric convolution is nonzero on a vector orthogonal to theta
in the trivial rational isotype. Use a critical-line ordinate γ and the log-norm
vector `exp(-iγx)/(1+x²)`. Pair its translates with the theta vector from
`(3u² - 2πu⁴) exp(-πu²)` and the finite integer indicators. The pairing is analytic,
and the Cauchy kernel has a nonvanishing Fourier multiplier, so it is nonzero at some
positive translation. A bump near that point and a large cutoff preserve the
nonzero geometric output. -/
private theorem rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero :
    let hs : (0 : ℝ) ≤ 2 := by norm_num
    let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
    letI : CompleteSpace ↥(GeoIsotype(ℚ, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    ∃ (φ : BruhatCompactSupport C𝔽(ℚ)), aboveOne(ℚ, φ) ∧
      ∃ (R ε : ℝ) (ρ : C𝔽(ℚ) → ℝ) (hρ : IsModulatedCutoff (m𝔽(ℚ)) R ε ρ)
          (u : GeoIsotype(ℚ, hs, ω)),
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u = 0 ∧
        ((GeoIsotype(ℚ, hs, ω)).orthogonalProjectionOnto.comp
          ((geometricTruncatedConvolution (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs hρ φ).comp
            (GeoIsotype(ℚ, hs, ω)).subtypeL)) u ≠ 0 := by
  intro hs ω
  let K := GeoIsotype(ℚ, hs, ω)
  let : CompleteSpace ↥K :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let μ := ideleClassTamagawaMeasure ℚ
  let τ := hardySobolevTranslation μ (m𝔽(ℚ)) (-(0 : ℝ)) 0 2
    (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs
  let ν := μ.withDensity fun g ↦ ENNReal.ofReal
    (intervalSobolevDensity (-(0 : ℝ)) 0 2 (Real.log (((m𝔽(ℚ)) g).val : ℝ)))
  let W := Lp ℂ 2 ν
  let P : W →L[ℂ] W := geometricProjection (F := ℚ) (1 / 2) (le_rfl (a := (0 : ℝ))) hs
  let O : W →L[ℂ] K := K.orthogonalProjectionOnto
  let j : ℝ≥0ˣ → C𝔽(ℚ) := (QuotientGroup.mk' _).comp ratIdeleNormSection
  have hj : Continuous j := QuotientGroup.continuous_mk.comp ratIdeleNormSection_continuous
  have witness : ∃ (u : ↥K) (g : C𝔽(ℚ)), 1 < ((m𝔽(ℚ) g).val : ℝ) ∧
      O (P u.val) = 0 ∧ O (P (τ g u.val)) ≠ 0 := rational_cutoffConv_positive_translate hs ω rfl
  obtain ⟨u, g, hg, hPu, hPg⟩ := witness
  have hτ : Continuous (fun p : C𝔽(ℚ) × W ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ (m𝔽(ℚ)) (-(0 : ℝ)) 0 2
      (neg_nonpos.mpr (le_rfl (a := (0 : ℝ)))) hs).choose_spec.2
  have hu (k : C₁(ℚ)) : τ k.val u.val = u.val :=
    rational_cutoffConv_fixed (G := C𝔽(ℚ)) (L := C₁(ℚ)) (E := W)
      τ (ideleClassNorm ℚ).ker.subtype ω (fun _ ↦ rfl) u k
  have hcut := rational_cutoffConv_of_projected_translate (G := C𝔽(ℚ)) (H := ↥K)
    (m𝔽(ℚ)) (isProperMap_ideleClassNorm ℚ) j hj ratIdeleNormSection_class_rightInverse
    μ ν τ hτ P O u.val hu g hg hPg
  obtain ⟨φ, hφ, R, ε, ρ, hρ, hρne⟩ := hcut
  exact ⟨φ, hφ, R, ε, ρ, hρ, u, hPu, hρne⟩

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
On the trivial rational component with no finite places, a = 1/2 and s = 2, let γ be
the first positive ordinate of a critical-line zeta zero. The vector
v(x) = exp(-iγx)/(1+x²) is orthogonal to theta by the Mellin zero.
Use the nonzero half-weighted theta profile G of
(3u² - 2πu⁴) exp(-πu²) with integer indicators at finite places.
The inner products of the translates v(x-t) with G cannot vanish for all t > 0.
Up to a phase they convolve G(x) exp(iγx)(1+x²) with 1/(1+x²).
That convolution is real analytic and its Fourier multiplier is nowhere zero.
A nonnegative test bump near a positive t with nonzero inner product still pairs
nontrivially, and a sufficiently large fixed symmetric cutoff preserves a nonzero
part of its geometric projection. Every right PW projection kills v. -/
theorem Printed.absolutePWCondensation_traceNorm_tendsto_false :
    ¬ Printed.absolutePWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := absolutePWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := absolutePWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For every fixed cutoff, the trace-norm limit of invariant condensation is asserted
to be the uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_traceNorm_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ traceNorm
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) - T))
              atTop (𝓝 0)

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
For ℚ with no finite places, the trivial character, a = 1/2 and s = 2, the product
region is the same interval as the absolute box. The zeta-zero vector, positive test bump and
fixed symmetric cutoff of the absolute counterexample also refute this limit. -/
theorem Printed.invariantPWCondensation_traceNorm_tendsto_false :
    ¬ Printed.invariantPWCondensation_traceNorm_tendsto := by
  intro h
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp
    (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁(ℚ) →ₜ* C𝔽(ℚ))
  let H := ↥(GeoIsotype(ℚ, hs, ω))
  let : CompleteSpace H :=
    (instClosedSpectralIsotypeSec2 (F := ℚ) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
      hs ω).completeSpace_coe
  let P (Λ : ℝ) : H →L[ℂ] H := invariantPWProjection (F := ℚ) (S := ∅) hs (1 / 2) ω Λ
  obtain ⟨φ, hφ, R, ε, ρ, hρ, u, hu, hcut⟩ :=
    rational_cutoffConv_ne_zero_of_geometricProjection_eq_zero
  obtain ⟨T, hT, hlim⟩ := h ℚ 1 ∅ (1 / 2) 2 hs
    rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
  have hstrong := invariantPWProjection_tendsto (F := ℚ) (S := ∅) hs (1 / 2) ω
    rational_one_unramifiedOutside_empty rational_empty_picTrivial u
  have hzero : Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 0) :=
    (congrArg (fun v : H ↦ Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 v)) hu).mp hstrong
  have heq : T.val 0 = T.val u :=
    absolutePWCondensation_traceNorm_tendsto_false_apply H T P u 0 hzero hlim
  exact hcut ((congrArg (fun A : H →L[ℂ] H ↦ A u) hT).symm.trans
    (heq.symm.trans (map_zero T.val)))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution.
Deviation: Interpret the absolute projector by the PW codomain of (11.2.1.3)
and take the box parameter X = Λ, as for the operator assertion. -/
def Printed.absolutePWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

section

open scoped FourierTransform ContDiff


section

local notation "logNorm(" F ")" =>
  (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "weight2(" F ")" =>
  (fun g : C𝔽(F) ↦ intervalSobolevDensity 0 0 2 (logNorm(F) g))
local notation "ν(" F ")" =>
  ((μ(F)).withDensity (fun g ↦ ENNReal.ofReal (weight2(F) g)))
local notation "W₂(" F ")" => Lp ℂ 2 (ν(F))
local notation "hs₂" => (show (0 : ℝ) ≤ 2 from zero_le_two)
local notation "τ₂(" F ")" =>
  hardySobolevTranslation (μ(F)) (m𝔽(F)) 0 0 2 (le_rfl (a := (0 : ℝ))) hs₂

private theorem absolutePW_window_density (F : Type) [Field F] [NumberField F]
    (g : C𝔽(F)) : weight2(F) g = 1 + (logNorm(F) g) ^ 2 := by
  norm_num [intervalSobolevDensity]

private theorem absolutePW_window_log_continuous (F : Type) [Field F] [NumberField F] :
    Continuous logNorm(F) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
    (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')

private theorem absolutePW_window_log_mul (F : Type) [Field F] [NumberField F]
    (g x : C𝔽(F)) : logNorm(F) (g * x) = logNorm(F) g + logNorm(F) x := by
  change Real.log (((ideleClassNorm F (g * x)).val : ℝ≥0) : ℝ) = _
  rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']

/-- The squared weighted norm is an integral against the density, as in
`weightedL2_norm_eq` in Ch09 §2. -/
private theorem absolutePW_weighted_norm_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ) (hm : Measurable w) (hw : ∀ x, 0 ≤ w x)
    (u : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) :
    Integrable (fun x ↦ ‖u x‖ ^ 2 * w x) μ ∧
      ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 * w x ∂μ := by
  let ν := μ.withDensity fun x ↦ ENNReal.ofReal (w x)
  have hfinite : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ :=
    .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hint : Integrable (fun x ↦ ‖u x‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  refine ⟨((integrable_withDensity_iff hm.ennreal_ofReal hfinite).1 hint).congr
    (ae_of_all μ fun x ↦ by simp only [ENNReal.toReal_ofReal (hw x)]), ?_⟩
  have hnorm : ‖u‖ ^ 2 = (inner ℂ u u).re := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num [pow_two, Complex.mul_re]
  rw [hnorm, L2.inner_def (f := u) (g := u)]
  change RCLike.re (∫ x, inner ℂ (u x) (u x) ∂ν) = _
  rw [← integral_re (L2.integrable_inner u u)]
  simp_rw [inner_self_eq_norm_sq]
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal hfinite]
  refine integral_congr_ae (ae_of_all μ fun x ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hw x), mul_comm]

private theorem absolutePW_window_norm_sq {F : Type} [Field F] [NumberField F] (u : W₂(F)) :
    Integrable (fun x ↦ ‖u x‖ ^ 2 * weight2(F) x) (μ(F)) ∧
      ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 * weight2(F) x ∂μ(F) :=
  absolutePW_weighted_norm_sq (μ(F)) (weight2(F)) (by
    rw [funext (absolutePW_window_density F)]
    exact (continuous_const.add ((absolutePW_window_log_continuous F).pow 2)).measurable) (fun x ↦ by
      norm_num [intervalSobolevDensity]; positivity) u

/-- Multiplication by a bounded log-window after a distant translation is small
in operator norm on the degree-two weighted space. -/
private theorem absolutePW_window_translate_norm {F : Type} [Field F] [NumberField F]
    (b : C𝔽(F) → ℝ) (hb : Measurable b) (hb₁ : ∀ x, |b x| ≤ 1)
    (R : ℝ) (_hR : 0 ≤ R) (hwin : ∀ x, b x ≠ 0 → |logNorm(F) x| ≤ R)
    (g : C𝔽(F)) (hg : R ≤ logNorm(F) g) :
    ‖(lpCutoffMultiplier (ν(F)) b hb hb₁).comp (τ₂(F) g)‖ ≤
      Real.sqrt ((1 + R ^ 2) / (1 + (logNorm(F) g - R) ^ 2)) := by
  let L := logNorm(F) g
  let c : ℝ := (1 + R ^ 2) / (1 + (L - R) ^ 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hgR : R ≤ L := hg
  let A := (lpCutoffMultiplier (ν(F)) b hb hb₁).comp (τ₂(F) g)
  change ‖A‖ ≤ Real.sqrt c
  apply ContinuousLinearMap.opNorm_le_bound A (Real.sqrt_nonneg c)
  intro u
  have hm : Measurable (weight2(F)) := by
    rw [funext (absolutePW_window_density F)]
    exact (continuous_const.add ((absolutePW_window_log_continuous F).pow 2)).measurable
  have hac : μ(F) ≪ ν(F) := withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (by rw [absolutePW_window_density]; positivity))
  have hrep : (A u : C𝔽(F) → ℂ) =ᵐ[μ(F)] fun x ↦ (b x : ℂ) * u (g⁻¹ * x) := by
    have h1 := hac.ae_eq (lpCutoffMultiplier_apply (ν(F)) b hb hb₁ (τ₂(F) g u))
    have h2 := hardySobolevTranslation_apply (μ(F)) m𝔽(F) 0 0 2 le_rfl hs₂ g u
    filter_upwards [h1, h2] with x hx hy
    change A u x = _
    change A u x = (b x : ℂ) * τ₂(F) g u x at hx
    rw [hx, hy]
  have hcomp : (fun x ↦ A u (g * x)) =ᵐ[μ(F)] fun x ↦ (b (g * x) : ℂ) * u x := by
    have h := (measurePreserving_mul_left (μ(F)) g).quasiMeasurePreserving.ae_eq_comp hrep
    filter_upwards [h] with x hx
    change A u (g * x) = (b (g * x) : ℂ) * u (g⁻¹ * (g * x)) at hx
    rwa [inv_mul_cancel_left] at hx
  have hbot (x : C𝔽(F)) :
      |b (g * x)| ^ 2 * weight2(F) (g * x) ≤ c * weight2(F) x := by
    by_cases hx : b (g * x) = 0
    · rw [hx, abs_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
      exact mul_nonneg hc (by rw [absolutePW_window_density]; positivity)
    have h1 := hwin (g * x) hx
    have hlog := absolutePW_window_log_mul F g x
    have h2 : (L - R) ≤ -(logNorm(F) x) := by
      have h3 := (abs_le.mp h1).2
      rw [hlog] at h3
      change L + logNorm(F) x ≤ R at h3
      linarith
    have h3 : (L - R) ^ 2 ≤ (logNorm(F) x) ^ 2 := by
      rw [← neg_sq (logNorm(F) x)]
      exact pow_le_pow_left₀ (sub_nonneg.mpr hgR) h2 2
    have h4 : (1 + (L - R) ^ 2) ≤ weight2(F) x := by
      rw [absolutePW_window_density]
      linarith
    have h5 : weight2(F) (g * x) ≤ 1 + R ^ 2 := by
      rw [absolutePW_window_density, ← sq_abs]
      exact add_le_add_right (pow_le_pow_left₀ (abs_nonneg _) h1 2) 1
    calc
      _ ≤ 1 * weight2(F) (g * x) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) (hb₁ (g * x)) 2)
          (by rw [absolutePW_window_density]; positivity)
      _ ≤ 1 + R ^ 2 := by simpa only [one_mul] using h5
      _ = c * (1 + (L - R) ^ 2) := by dsimp only [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hc
  have hnorm : ‖A u‖ ^ 2 ≤ c * ‖u‖ ^ 2 := by
    obtain ⟨hAi, hAeq⟩ := absolutePW_window_norm_sq (A u)
    obtain ⟨hui, hueq⟩ := absolutePW_window_norm_sq u
    rw [hAeq, hueq, ← integral_const_mul]
    let f (x : C𝔽(F)) := ‖A u x‖ ^ 2 * weight2(F) x
    rw [← integral_mul_left_eq_self f g]
    refine integral_mono_ae
      (((measurePreserving_mul_left (μ(F)) g).integrable_comp_emb (measurableEmbedding_mulLeft g)).mpr hAi)
      (hui.const_mul c) ?_
    filter_upwards [hcomp] with x hx
    change ‖A u (g * x)‖ ^ 2 * weight2(F) (g * x) ≤ c * (‖u x‖ ^ 2 * weight2(F) x)
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    calc
      _ = ‖u x‖ ^ 2 * (|b (g * x)| ^ 2 * weight2(F) (g * x)) := by ring
      _ ≤ ‖u x‖ ^ 2 * (c * weight2(F) x) := mul_le_mul_of_nonneg_left (hbot x) (sq_nonneg _)
      _ = _ := by ring
  have hsq : (Real.sqrt c * ‖u‖) ^ 2 = c * ‖u‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    (hnorm.trans_eq hsq.symm)

local notation "A₂(" F ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) 0 0 2 (le_rfl (a := (0 : ℝ))) hs₂ φ

private theorem absolutePW_window_ae {F : Type} [Field F] [NumberField F] :
    μ(F) ≪ ν(F) := by
  have hm : Measurable (weight2(F)) := by
    rw [funext (absolutePW_window_density F)]
    exact (continuous_const.add ((absolutePW_window_log_continuous F).pow 2)).measurable
  exact withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (by rw [absolutePW_window_density]; positivity))

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

local notation "νc" => μ.withDensity (fun g : G ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 2 (Real.log ((m g).val : ℝ))))
local notation "τc" => hardySobolevTranslation μ m 0 0 2 le_rfl hs₂
local notation "Ac(" φ ")" => hardySobolevTestAction μ m 0 0 2 le_rfl hs₂ φ

/-- Translating a convolution test is equivalent to translating its input. -/
private theorem absolutePW_translate_action
    (φ ψ : BruhatCompactSupport G) (g : G)
    (hψ : ∀ y, ψ.val y = φ.val (g⁻¹ * y)) :
    Ac(ψ) = (Ac(φ)).comp (τc g) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  filter_upwards [hardySobolevTestAction_apply μ m 0 0 2 le_rfl hs₂ ψ u,
    hardySobolevTestAction_apply μ m 0 0 2 le_rfl hs₂ φ (τc g u)] with x hL hR
  change (Ac(ψ) u) x = (Ac(φ) (τc g u)) x
  rw [hL, hR]
  have hτ := hardySobolevTranslation_apply μ m 0 0 2 le_rfl hs₂ g u
  have hpr : MeasurePreserving (fun y : G ↦ y⁻¹ * x) μ μ :=
    (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
  change (∫ y, ψ.val y * u (y⁻¹ * x) ∂μ) =
    ∫ y, φ.val y * (τc g u) (y⁻¹ * x) ∂μ
  rw [← integral_mul_left_eq_self (fun y ↦ ψ.val y * u (y⁻¹ * x)) g]
  apply integral_congr_ae
  filter_upwards [hpr.quasiMeasurePreserving.ae_eq_comp hτ] with y hy
  change ψ.val (g * y) * u ((g * y)⁻¹ * x) =
    φ.val y * (τc g u) (y⁻¹ * x)
  change (τc g u) (y⁻¹ * x) = u (g⁻¹ * (y⁻¹ * x)) at hy
  rw [hy, hψ, inv_mul_cancel_left]
  congr 2
  simp only [mul_inv_rev, ← mul_assoc, mul_comm y⁻¹ g⁻¹]

/-- When a cutoff acts after convolution, the input can be restricted to a
fixed window containing all differences of points in the output window and
in the test support. -/
private theorem absolutePW_window_localization (hμ : μ ≪ νc)
    (φ : BruhatCompactSupport G)
    (b c : G → ℝ) (hb : Measurable b) (hb₁ : ∀ x, |b x| ≤ 1)
    (hc : Measurable c) (hc₁ : ∀ x, |c x| ≤ 1)
    (hcover : ∀ x y, b x ≠ 0 → φ.val y ≠ 0 → c (y⁻¹ * x) = 1) :
    let M := lpCutoffMultiplier νc b hb hb₁
    let B := lpCutoffMultiplier νc c hc hc₁
    (M.comp (Ac(φ))).comp B = M.comp (Ac(φ)) := by
  intro M B
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ _).ae_eq
  have h1 := hμ.ae_eq
    (lpCutoffMultiplier_apply νc b hb hb₁ (Ac(φ) (B u)))
  have h2 := hμ.ae_eq
    (lpCutoffMultiplier_apply νc b hb hb₁ (Ac(φ) u))
  have h3 := hardySobolevTestAction_apply μ m 0 0 2 le_rfl hs₂ φ (B u)
  have h4 := hardySobolevTestAction_apply μ m 0 0 2 le_rfl hs₂ φ u
  filter_upwards [h1, h2, h3, h4] with x h1x h2x h3x h4x
  change (M (Ac(φ) (B u))) x = (M (Ac(φ) u)) x
  rw [h1x, h2x, h3x, h4x]
  by_cases hx : b x = 0
  · simp [hx]
  congr 1
  have hB := hμ.ae_eq
    (lpCutoffMultiplier_apply νc c hc hc₁ u)
  have hpr : MeasurePreserving (fun y : G ↦ y⁻¹ * x) μ μ :=
    (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
  apply integral_congr_ae
  filter_upwards [hpr.quasiMeasurePreserving.ae_eq_comp hB] with y hy
  change (B u) (y⁻¹ * x) = (c (y⁻¹ * x) : ℂ) * u (y⁻¹ * x) at hy
  change φ.val y * (B u) (y⁻¹ * x) = φ.val y * u (y⁻¹ * x)
  rw [hy]
  by_cases hz : φ.val y = 0
  · simp [hz]
  · simp [hcover x y hx hz]


end

/-- Right composition by a family with a decaying norm sends a fixed nuclear
operator to zero in trace norm. -/
private theorem absolutePW_trace_decay_of_factorization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H)
    (D C : ℝ → H →L[ℂ] H) (heq : ∀ t, D t = T.val * C t)
    (R : ℝ) (hC : ∀ t, R ≤ t → ‖C t‖ ≤ Real.sqrt ((1 + R^2) / (1 + (t-R)^2))) :
    ∃ hn : ∀ t, IsNuclearOperator (D t),
      Tendsto (fun t ↦ traceNorm (⟨D t, hn t⟩ : nuclearEndomorphisms H)) atTop (𝓝 0) := by
  have hn (t : ℝ) : IsNuclearOperator (D t) := by
    rw [heq]
    exact mul_mem_nuclearEndomorphisms_right _ T
  refine ⟨hn, ?_⟩
  have hshift : Tendsto (fun t : ℝ ↦ t - R) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have hsquare := (tendsto_pow_atTop (Nat.succ_ne_zero 1)).comp hshift
  have hden : Tendsto (fun t : ℝ ↦ 1 + (t - R)^2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hsquare
  have hquot : Tendsto (fun t : ℝ ↦ (1 + R^2) / (1 + (t - R)^2)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using (tendsto_inv_atTop_zero.comp hden).const_mul (1 + R^2)
  have hzero : Tendsto (fun t : ℝ ↦ Real.sqrt ((1 + R^2) / (1 + (t - R)^2)) * traceNorm T)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, zero_mul, Function.comp_def] using (Real.continuous_sqrt.tendsto 0 |>.comp hquot).mul_const (traceNorm T)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ (norm_nonneg _).trans (norm_hilbertTrace_le _)) _ hzero
  filter_upwards [eventually_ge_atTop R] with t ht
  have heq' : (⟨D t, hn t⟩ : nuclearEndomorphisms H) =
      ⟨T.val * (C t), mul_mem_nuclearEndomorphisms_right _ T⟩ := Subtype.ext (heq t)
  rw [heq']
  apply (traceNorm_mul_right_le _ T).trans
  apply mul_le_mul_of_nonneg_right _ ((norm_nonneg _).trans (norm_hilbertTrace_le T))
  exact hC t ht

/-- A bounded log window covers all differences between an output point
and a point in the compact support of the convolution test. -/
private theorem absolutePW_exists_difference_window {G : Type*} [CommGroup G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (L : G → ℝ) (hL : Continuous L) (hsub : ∀ x y, L (y⁻¹ * x) = L x - L y)
    (b : G → ℝ) (hbC : HasCompactSupport b)
    (φ : G → ℂ) (hφ : HasCompactSupport φ) :
    ∃ (R : ℝ) (c : G → ℝ), 0 ≤ R ∧ Measurable c ∧ (∀ x, |c x| ≤ 1) ∧
      (∀ x, c x ≠ 0 → |L x| ≤ R) ∧ (∀ x y, b x ≠ 0 → φ y ≠ 0 → c (y⁻¹ * x) = 1) := by
  obtain ⟨B₁, hB₁⟩ := hbC.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨B₂, hB₂⟩ := hφ.exists_bound_of_continuousOn
    hL.continuousOn
  let R := |B₁| + |B₂|
  have hR : 0 ≤ R := by positivity
  let c (x : G) : ℝ := if |L x| ≤ R then 1 else 0
  have hc : Measurable c := Measurable.ite
    (measurableSet_le (continuous_abs.comp hL).measurable measurable_const)
    measurable_const measurable_const
  have hc₁ (x : G) : |c x| ≤ 1 := by
    by_cases h : |L x| ≤ R <;> simp [c, h]
  have hwin (x : G) : c x ≠ 0 → |L x| ≤ R := by
    contrapose!
    intro h
    simp [c, h.not_ge]
  have hcov (x y : G) (hx : b x ≠ 0) (hy : φ y ≠ 0) : c (y⁻¹ * x) = 1 := by
    have hx' := hB₁ x (subset_tsupport _ hx)
    have hy' := hB₂ y (subset_tsupport _ hy)
    rw [Real.norm_eq_abs] at hx' hy'
    have hle := (abs_sub (L x) (L y)).trans (show _ ≤ R by
      dsimp only [R]
      linarith [le_abs_self B₁, le_abs_self B₂])
    change (if |L (y⁻¹ * x)| ≤ R then 1 else 0) = 1
    rw [hsub, ite_eq_left hle]
  exact ⟨R, c, hR, hc, hc₁, hwin, hcov⟩

/-- Restrict the middle variable to the input window in a translated product. -/
private theorem absolutePW_localized_factor {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (M A D B U : H →L[ℂ] H)
    (heq : D = A.comp U) (hloc : (M.comp A).comp B = M.comp A) :
    M.comp D = (M.comp A) * (B.comp U) := by
  rw [heq]
  exact congrArg (fun X : H →L[ℂ] H ↦ X.comp U) hloc.symm

section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

local notation "νc" => μ.withDensity (fun g : G ↦ ENNReal.ofReal
  (intervalSobolevDensity 0 0 2 (Real.log ((m g).val : ℝ))))
local notation "Lc" => (fun g : G ↦ Real.log ((m g).val : ℝ))
local notation "τc" => hardySobolevTranslation μ m 0 0 2 le_rfl hs₂
local notation "Ac(" φ ")" => hardySobolevTestAction μ m 0 0 2 le_rfl hs₂ φ

/-- A fixed cutoff after a shifted test tends to zero in trace norm. -/
private theorem absolutePW_window_trace_decay
    (hμ : μ ≪ νc) (hLc : Continuous Lc) (hsub : ∀ (x y : G), Lc (y⁻¹ * x) = Lc x - Lc y)
    (φ : BruhatCompactSupport G) (ψ : ℝ → BruhatCompactSupport G)
    (g : ℝ → G)
    (hψ : ∀ t x, (ψ t).val x = φ.val ((g t)⁻¹ * x))
    (b : G → ℝ) (hb : Measurable b) (hb₁ : ∀ x, |b x| ≤ 1)
    (hbC : HasCompactSupport b)
    (htrans : ∀ (c : G → ℝ) (hc : Measurable c) (hc₁ : ∀ x, |c x| ≤ 1) (R : ℝ), 0 ≤ R →
      (∀ x, c x ≠ 0 → |Lc x| ≤ R) → ∀ t, R ≤ t →
        ‖(lpCutoffMultiplier νc c hc hc₁).comp (τc (g t))‖ ≤ Real.sqrt ((1 + R^2) / (1 + (t-R)^2))) :
    let M := lpCutoffMultiplier νc b hb hb₁
    IsNuclearOperator (M.comp Ac(φ)) →
      ∃ hA : ∀ t, IsNuclearOperator (M.comp Ac(ψ t)),
        Tendsto (fun t ↦ traceNorm (⟨M.comp Ac(ψ t), hA t⟩ :
          nuclearEndomorphisms (Lp ℂ 2 νc))) atTop (𝓝 0) := by
  intro M hM
  obtain ⟨R, c, hR, hc, hc₁, hwin, hcov⟩ := absolutePW_exists_difference_window
    _ hLc hsub b hbC φ.val φ.property.2
  let B := lpCutoffMultiplier νc c hc hc₁
  let U (t : ℝ) : (Lp ℂ 2 νc) →L[ℂ] (Lp ℂ 2 νc) := τc (g t)
  let T : nuclearEndomorphisms (Lp ℂ 2 νc) := ⟨M.comp Ac(φ), hM⟩
  have hw : (M.comp Ac(φ)).comp B = M.comp Ac(φ) :=
    absolutePW_window_localization μ m hμ φ b c hb hb₁ hc hc₁ hcov
  have heq (t : ℝ) : M.comp Ac(ψ t) = T.val * (B.comp (U t)) :=
    absolutePW_localized_factor M _ _ B (U t)
      (absolutePW_translate_action μ m φ (ψ t) (g t) (hψ t)) hw
  apply absolutePW_trace_decay_of_factorization T _ (fun t ↦ B.comp (U t)) heq R
  intro t ht
  exact htrans c hc hc₁ R hR hwin t ht

end

/-- A fixed cutoff after a shifted test tends to zero in trace norm. -/
private theorem absolutePW_cutoff_shift_trace_decay {F : Type} [Field F] [NumberField F]
    (φ : BruhatCompactSupport C𝔽(F)) (ψ : ℝ → BruhatCompactSupport C𝔽(F))
    (g : ℝ → C𝔽(F)) (hg : ∀ t, logNorm(F) (g t) = t)
    (hψ : ∀ t x, (ψ t).val x = φ.val ((g t)⁻¹ * x))
    (b : C𝔽(F) → ℝ) (hb : Measurable b) (hb₁ : ∀ x, |b x| ≤ 1)
    (hbC : HasCompactSupport b) :
    let M := lpCutoffMultiplier (ν(F)) b hb hb₁
    IsNuclearOperator (M.comp A₂(F, φ)) →
      ∃ hA : ∀ t, IsNuclearOperator (M.comp A₂(F, ψ t)),
        Tendsto (fun t ↦ traceNorm (⟨M.comp A₂(F, ψ t), hA t⟩ :
          nuclearEndomorphisms W₂(F))) atTop (𝓝 0) := by
  intro M hM
  have hsub (x y : C𝔽(F)) : logNorm(F) (y⁻¹ * x) = logNorm(F) x - logNorm(F) y := by
    rw [absolutePW_window_log_mul]
    have hy : logNorm(F) y⁻¹ + logNorm(F) y = 0 := by
      rw [← absolutePW_window_log_mul, inv_mul_cancel]
      change Real.log ((ideleClassNorm F (1 : C𝔽(F))).val : ℝ) = 0
      simp
    linarith
  exact absolutePW_window_trace_decay (μ(F)) m𝔽(F) (absolutePW_window_ae (F := F))
    (absolutePW_window_log_continuous F) hsub φ ψ g hψ b hb hb₁ hbC (fun c hc hc₁ R hR hwin t ht ↦ by
      change ‖(lpCutoffMultiplier (ν(F)) c hc hc₁).comp (τ₂(F) (g t))‖ ≤ _
      exact (absolutePW_window_translate_norm c hc hc₁ R hR hwin (g t) (by simpa only [hg] using ht)).trans_eq
        (congrArg (fun L : ℝ ↦ Real.sqrt ((1 + R^2) / (1 + (L-R)^2))) (hg t))) hM


end

section

section
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any norm-summable rank-one expansion evaluates the Hilbert trace by its
diagonal. The closed-unit-ball normalization is from
`isNuclearOperator_iff_isBanachNuclear` in Appendix C §3. -/
private theorem absolutePW_nuclearTrace_series (A : H →L[ℂ] H) (c : ℕ → ℂ)
    (f : ℕ → StrongDual ℂ H) (v : ℕ → H) (hc : Summable fun n ↦ ‖c n‖)
    (hf : ∃ C, ∀ n, ‖f n‖ ≤ C) {R : ℝ} (hR : 0 < R) (hv : ∀ n, ‖v n‖ ≤ R)
    (hA : ∀ x, HasSum (fun n ↦ (c n * f n x) • v n) (A x)) :
    ∃ hn : IsNuclearOperator A, HasSum (fun n ↦ c n * f n (v n))
      (hilbertTrace (⟨A, hn⟩ : nuclearEndomorphisms H)) := by
  let r : ℂ := R
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hr_norm : ‖r‖ = R := by dsimp [r]; rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  let D := Metric.closedBall (0 : H) 1
  have hvD (n : ℕ) : r⁻¹ • v n ∈ D := by
    change dist (r⁻¹ • v n) 0 ≤ 1
    rw [dist_zero_right, norm_smul, norm_inv, hr_norm, inv_mul_le_iff₀ hR, mul_one]
    exact hv n
  let p : NuclearPresentation A :=
    { coeff := fun n ↦ c n * r
      functional := f
      disc := D
      isBanachDisc := isBanachDisc_closedUnitBall
      vector := fun n ↦ ⟨r⁻¹ • v n, Submodule.subset_span (hvD n)⟩
      vector_mem := hvD
      summable_coeff := by simpa only [norm_mul] using hc.mul_right ‖r‖
      equicontinuous := ((NormedSpace.equicontinuous_tfae f).out 6 1).mp hf
      hasSum := fun x ↦ (hA x).congr_fun fun n ↦ by
        change (c n * r * f n x) • (r⁻¹ • v n) = (c n * f n x) • v n
        rw [smul_smul, mul_right_comm (c n) r, mul_inv_cancel_right₀ hr] }
  have hn := (isNuclearOperator_iff_nonempty_presentation A).mpr ⟨p⟩
  refine ⟨hn, ?_⟩
  rw [hilbertTrace_eq_nuclearTrace]
  have ht := ((exists_nuclearTrace_hasSum hilbert_approximationProperty A hn).exists.choose_spec p).2
  refine ht.congr_fun fun n ↦ ?_
  change c n * f n (v n) = c n * r * f n (r⁻¹ • v n)
  rw [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel_right₀ hr]

/-- The same nuclear expansion computes the traces of both compositions. -/
private theorem absolutePW_cross_trace (A : H →L[ℂ] K) (hA : IsNuclearOperator A)
    (B : K →L[ℂ] H) :
    ∃ (hBA : IsNuclearOperator (B.comp A)) (hAB : IsNuclearOperator (A.comp B)),
      hilbertTrace (⟨B.comp A, hBA⟩ : nuclearEndomorphisms H) =
        hilbertTrace (⟨A.comp B, hAB⟩ : nuclearEndomorphisms K) := by
  obtain ⟨p⟩ := (isNuclearOperator_iff_nonempty_presentation A).mp hA
  obtain ⟨C, hC, hf⟩ := ((NormedSpace.equicontinuous_tfae p.functional).out 1 7).mp p.equicontinuous
  obtain ⟨D, hD⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp p.isBanachDisc.bounded).exists_norm_le
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD (p.vector 0) (p.vector_mem 0))
  let v (n : ℕ) : K := p.vector n
  have hv (n : ℕ) : ‖v n‖ ≤ D := hD _ (p.vector_mem n)
  obtain ⟨hBA, hBAtr⟩ := absolutePW_nuclearTrace_series (B.comp A) p.coeff p.functional
    (B ∘ v) p.summable_coeff ⟨C, hf⟩ (R := ‖B‖ * D + 1) (by positivity)
    (fun n ↦ ((B.le_opNorm (v n)).trans
      (mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _))).trans (by linarith))
    (fun x ↦ by simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, v, map_smul] using B.hasSum (p.hasSum x))
  let f (n : ℕ) : StrongDual ℂ K := (p.functional n).comp B
  obtain ⟨hAB, hABtr⟩ := absolutePW_nuclearTrace_series (A.comp B) p.coeff f v
    p.summable_coeff ⟨C * ‖B‖, fun n ↦ (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _))⟩ (R := D + 1) (by linarith)
    (fun n ↦ (hv n).trans (by linarith)) (fun x ↦ p.hasSum (B x))
  exact ⟨hBA, hAB, hBAtr.unique hABtr⟩

end
private theorem scalarConvolution_tendsto_zero (k : SchwartzMap ℝ ℂ) (G : ℝ → ℂ)
    (hG : Continuous G) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ r, ‖G r‖ ≤ C * (1 + |r|))
    (hlim : Tendsto G atTop (𝓝 0)) :
    Tendsto (fun t : ℝ ↦ ∫ r, k r * G (t - r)) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := eventually_atTop.1
    ((tendsto_zero_iff_norm_tendsto_zero.mp hlim).eventually (gt_mem_nhds one_pos))
  let b := max a 0
  have hb₀ : 0 ≤ b := le_max_right _ _
  let B := 1 + C * (1 + b)
  have hB : 1 ≤ B := by dsimp only [B]; linarith [mul_nonneg hC (by linarith : 0 ≤ 1+b)]
  have hdom (t : ℝ) (ht : b ≤ t) (r : ℝ) : ‖G (t-r)‖ ≤ B + C * |r| := by
    by_cases h : a ≤ t - r
    · exact (ha _ h).le.trans (by linarith [mul_nonneg hC (abs_nonneg r)])
    · have hr : |t-r| ≤ b + |r| := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [le_abs_self r]
        · linarith [abs_nonneg r, le_max_left a 0]
      calc
        _ ≤ C * (1 + |t-r|) := hb _
        _ ≤ C * (1 + (b + |r|)) := by gcongr
        _ ≤ _ := by dsimp [B]; linarith
  have hi : Integrable (fun r ↦ ‖k r‖ * B + C * (|r| * ‖k r‖)) := by
    apply Integrable.add ((k.integrable (μ := volume)).norm.mul_const _)
    simpa only [Real.norm_eq_abs, pow_one] using (k.integrable_pow_mul volume 1).const_mul C
  suffices Tendsto (fun t : ℝ ↦ ∫ r, k r * G (t-r)) atTop (𝓝 (∫ _ : ℝ, (0 : ℂ))) by simpa using this
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (t r : ℝ) ↦ k r * G (t - r)) (f := fun _ ↦ (0 : ℂ))
    (fun r ↦ ‖k r‖ * B + C * (|r| * ‖k r‖))
    (Eventually.of_forall (fun t ↦ (k.continuous.mul
      (hG.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)) ?_ hi ?_
  · filter_upwards [eventually_ge_atTop b] with t ht
    apply ae_of_all
    intro r
    rw [norm_mul]
    calc
      _ ≤ ‖k r‖ * (B + C * |r|) := by gcongr; exact hdom t ht r
      _ = _ := by ring
  · apply ae_of_all
    intro r
    simpa [sub_eq_add_neg] using (tendsto_const_nhds (x := k r)).mul (hlim.comp (tendsto_atTop_add_const_right _ (-r) tendsto_id))

/-- Smooth spectral localization separates one isolated ordinate, in cycles per unit time. -/
private theorem exists_isolatingSchwartzKernel {ι : Type*} (ξ : ι → ℝ) (i : ι) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ j ≠ i, r ≤ dist (ξ j) (ξ i)) :
    ∃ k : SchwartzMap ℝ ℂ, (𝓕 k : SchwartzMap ℝ ℂ) (ξ i) = 1 ∧
      ∀ j ≠ i, (𝓕 k : SchwartzMap ℝ ℂ) (ξ j) = 0 := by
  let b : ContDiffBump (ξ i) := ⟨r/2, r, by positivity, by linarith⟩
  have hc : HasCompactSupport (fun t : ℝ ↦ (b t : ℂ)) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ (b t : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  let ψ := hc.toSchwartzMap hd
  refine ⟨𝓕⁻ ψ, ?_, ?_⟩ <;> rw [FourierTransform.fourier_fourierInv_eq]
  · change ((b (ξ i) : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one]
  · intro j hj
    change ((b (ξ j) : ℝ) : ℂ) = 0
    rw [b.zero_of_le_dist (hsep j hj), Complex.ofReal_zero]

private theorem integrate_isolatedEigenfrequency
    {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (Λ : ι → StrongDual ℂ H) (hBasis : IsSpectralMarkushevichBasis v Λ)
    (D : ℝ → H →L[ℂ] H) (ξ : ι → ℝ) (d : ι → ℂ)
    (hD : ∀ t j x, Λ j (D t x) = (Real.fourierChar (t * ξ j) : ℂ) * d j * Λ j x)
    (i : ι) (k : SchwartzMap ℝ ℂ) (hki : (𝓕 k : SchwartzMap ℝ ℂ) (ξ i) = 1)
    (hk : ∀ j ≠ i, (𝓕 k : SchwartzMap ℝ ℂ) (ξ j) = 0 ∨ d j = 0) (t : ℝ)
    (hi : Integrable (fun r ↦ k r • D (t-r))) :
    (∫ r, k r • D (t-r)) = ((Real.fourierChar (t*ξ i) : ℂ) * d i) • (Λ i).smulRight (v i) := by
  ext x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro ℓ
  suffices e : ContinuousLinearMap.apply ℂ ℂ ((∫ r, k r • D (t-r)) x) =
      ContinuousLinearMap.apply ℂ ℂ ((((Real.fourierChar (t*ξ i) : ℂ) * d i) • (Λ i).smulRight (v i)) x) from
    DFunLike.congr_fun e ℓ
  apply ContinuousLinearMap.ext_on hBasis.2.2.2
  rintro _ ⟨j, rfl⟩
  let L : StrongDual ℂ (H →L[ℂ] H) := (Λ j).comp (ContinuousLinearMap.apply ℂ H x)
  change L (∫ r, k r • D (t-r)) = Λ j _
  rw [← L.integral_comp_comm hi]
  have heq (r : ℝ) : L (k r • D (t-r)) =
      (((Real.fourierChar (-(r*ξ j)) : ℂ) * k r) *
      ((Real.fourierChar (t*ξ j) : ℂ) * d j * Λ j x)) := by
    change Λ j (k r • D (t-r) x) = _
    rw [map_smul, smul_eq_mul, hD, sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [heq]
  rw [integral_mul_const]
  have hF : (∫ r, (Real.fourierChar (-(r*ξ j)) : ℂ) * k r) = (𝓕 k : SchwartzMap ℝ ℂ) (ξ j) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    rfl
  rw [hF]
  change _ = Λ j ((((Real.fourierChar (t*ξ i) : ℂ) * d i) • (Λ i x • v i)))
  simp only [map_smul, smul_eq_mul]
  by_cases e : j = i
  · subst j; rw [hki, hBasis.1 i]; ring
  · rw [hBasis.2.1 i j (Ne.symm e)]
    rcases hk j e with hj | hj <;> rw [hj] <;> ring

private theorem continuous_comp_nuclear_of_stronglyContinuous_bounded
    {X H : Type*} [TopologicalSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (U : X → H →L[ℂ] H) (hU : ∀ x, Continuous (fun t ↦ U t x))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖U t‖ ≤ K) (N : H →L[ℂ] H) (hN : IsNuclearOperator N) :
    Continuous (fun t ↦ (U t).comp N) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hseries⟩ := (isNuclearOperator_iff_isBanachNuclear N).mp hN
  obtain ⟨P, hP, hφP⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
  obtain ⟨Y, hY, hyY⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
  let a (n : ℕ) (t : X) := c n • (φ n).smulRight (U t (y n))
  have ha (n : ℕ) : Continuous (a n) :=
    (((ContinuousLinearMap.smulRightL ℂ H H (φ n)).continuous).comp (hU (y n))).const_smul (c n)
  have hbnd (n : ℕ) (t : X) : ‖a n t‖ ≤ ‖c n‖ * (P * (K * Y)) := by
    simp only [a, norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    gcongr
    · exact hφP _ (mem_range_self n)
    · exact ((U t).le_opNorm _).trans (mul_le_mul (hb t) (hyY _ (mem_range_self n)) (norm_nonneg _) hK)
  have hcont := continuous_tsum ha (hc.mul_right (P * (K * Y))) hbnd
  convert hcont using 1
  funext t
  ext x
  have hs := ((hc.mul_right (P * (K * Y))).of_norm_bounded (fun n ↦ hbnd n t)).hasSum
  have h := (ContinuousLinearMap.apply ℂ H x).hasSum hs
  have h' := (U t).hasSum (hseries x)
  exact HasSum.unique (f := fun n ↦ (c n * φ n x) • U t (y n))
    (by simpa only [map_smul, ContinuousLinearMap.comp_apply] using h') (by
      simpa only [a, ContinuousLinearMap.apply_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_smul] using h)

private theorem continuous_comp_nuclear_of_stronglyContinuous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (hU : ∀ x, Continuous (fun t ↦ U t x))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖U t‖ ≤ C * (1 + |t|))
    (N : H →L[ℂ] H) (hN : IsNuclearOperator N) :
    Continuous (fun t ↦ (U t).comp N) := by
  rw [continuous_iff_continuousAt]
  intro t
  let S := Metric.ball t 1
  have h : Continuous (fun u : S ↦ (U u.val).comp N) :=
    continuous_comp_nuclear_of_stronglyContinuous_bounded _ (fun x ↦ (hU x).comp continuous_subtype_val)
      (K := C * (2 + |t|)) (by positivity) (fun u ↦ (hb _).trans ?_) N hN
  · exact (continuousOn_iff_continuous_domRestrict.mpr h t (Metric.mem_ball_self one_pos)).continuousAt
      (Metric.ball_mem_nhds t one_pos)
  · apply mul_le_mul_of_nonneg_left _ hC
    have hdist : |(u : ℝ) - t| < 1 := Metric.mem_ball.mp u.property
    have hu := abs_add_le ((u : ℝ)-t) t
    rw [sub_add_cancel] at hu
    linarith


/-- The integral of a nuclear orbit has the integrated diagonal trace. -/
private theorem absolutePW_integrate_nuclear_orbit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (hU : ∀ x, Continuous (fun t ↦ U t x))
    {C : ℝ} (hC : 0 ≤ C) (hUb : ∀ t, ‖U t‖ ≤ C * (1 + |t|))
    (N : nuclearEndomorphisms H) (M : H →L[ℂ] H)
    (k : SchwartzMap ℝ ℂ) (t : ℝ)
    (hI : Integrable (fun u ↦ k u • (U (t-u)).comp N.val)) :
    ∃ hn : IsNuclearOperator (M.comp (∫ u, k u • (U (t-u)).comp N.val)),
      hilbertTrace (⟨M.comp (∫ u, k u • (U (t-u)).comp N.val), hn⟩ : nuclearEndomorphisms H) =
        ∫ u, k u * hilbertTrace
          (⟨M * U (t-u) * N.val, mul_mem_nuclearEndomorphisms_left _ N⟩ :
            nuclearEndomorphisms H) := by
  obtain ⟨p⟩ := (isNuclearOperator_iff_nonempty_presentation N.val).mp N.property
  obtain ⟨P, hP, hf⟩ := ((NormedSpace.equicontinuous_tfae p.functional).out 1 7).mp p.equicontinuous
  obtain ⟨Y, hy⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp p.isBanachDisc.bounded).exists_norm_le
  let y (n : ℕ) : H := p.vector n
  have hY : 0 ≤ Y := (norm_nonneg _).trans (hy _ (p.vector_mem 0))
  have hyY (n : ℕ) : ‖y n‖ ≤ Y := hy _ (p.vector_mem n)
  let B (u : ℝ) := ‖k u‖ * (‖M‖ * (C * (1 + |t| + |u|)) * Y)
  have hB (u : ℝ) : 0 ≤ B u := by dsimp only [B]; positivity
  have hBi : Integrable B := by
    have h := (k.integrable (μ := volume)).norm
    have h' := k.integrable_pow_mul volume 1
    convert (h.const_mul (‖M‖ * C * (1 + |t|) * Y)).add
      (h'.const_mul (‖M‖ * C * Y)) using 1
    funext u
    simp only [B, Pi.add_apply, pow_one, Real.norm_eq_abs]
    ring
  let F (n : ℕ) (u : ℝ) := k u • M (U (t-u) (y n))
  have hFc (n : ℕ) : Continuous (F n) :=
    k.continuous.smul (M.continuous.comp ((hU _).comp (continuous_const.sub continuous_id)))
  have hFb (n : ℕ) (u : ℝ) : ‖F n u‖ ≤ B u := by
    have hu : ‖U (t-u) (y n)‖ ≤ (C * (1 + |t| + |u|)) * Y :=
      ((U (t-u)).le_opNorm _).trans (mul_le_mul
        ((hUb _).trans (mul_le_mul_of_nonneg_left (by linarith [abs_sub t u]) hC))
        (hyY n) (norm_nonneg _) (by positivity))
    rw [norm_smul]
    dsimp only [B]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (M.le_opNorm _).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hFi (n : ℕ) : Integrable (F n) :=
    hBi.mono' (hFc n).aestronglyMeasurable (.of_forall (hFb n))
  let z (n : ℕ) := ∫ u, F n u
  have hz (n : ℕ) : ‖z n‖ ≤ ∫ u, B u :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_ae (hFi n).norm hBi (.of_forall (hFb n)))
  have hZ : 0 ≤ ∫ u, B u := integral_nonneg hB
  have hall (u : ℝ) (x : H) : HasSum
      (fun n ↦ (p.coeff n * p.functional n x) • F n u)
      (k u • M (U (t-u) (N.val x))) := by
    have ht := (M.comp (U (t-u))).hasSum (p.hasSum x)
    simpa only [F, ContinuousLinearMap.comp_apply, map_smul, smul_smul, mul_comm (k u)] using
      ht.const_smul (k u)
  have hIseries (x : H) : HasSum
      (fun n ↦ (p.coeff n * p.functional n x) • z n)
      ((M.comp (∫ u, k u • (U (t-u)).comp N.val)) x) := by
    let L := M.comp (ContinuousLinearMap.apply ℂ H x)
    change HasSum _ (L (∫ u, k u • (U (t-u)).comp N.val))
    rw [← L.integral_comp_comm hI]
    have hFi' (n : ℕ) : Integrable (fun u ↦ (p.coeff n * p.functional n x) • F n u) :=
      (hFi n).smul _
    have hsum : Summable (fun n ↦ ∫ u, ‖(p.coeff n * p.functional n x) • F n u‖) := by
      apply (p.summable_coeff.mul_right (P * ‖x‖ * ∫ u, B u)).of_nonneg_of_le
      · intro n; exact integral_nonneg fun _ ↦ norm_nonneg _
      · intro n
        rw [show (fun u ↦ ‖(p.coeff n * p.functional n x) • F n u‖) =
            fun u ↦ ‖p.coeff n * p.functional n x‖ * ‖F n u‖ from funext fun _ ↦ norm_smul _ _,
          integral_const_mul, norm_mul]
        have hn := integral_mono_ae (hFi n).norm hBi (.of_forall (hFb n))
        have hpn := ((p.functional n).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hf n) (norm_nonneg _))
        rw [← mul_assoc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hpn (norm_nonneg _)) hn
          (integral_nonneg fun _ ↦ norm_nonneg _) (by positivity)
    have hi := hasSum_integral_of_summable_integral_norm hFi' hsum
    convert hi using 1
    · funext n; exact (integral_smul _ _).symm
    · apply integral_congr_ae
      exact .of_forall fun u ↦ by
        simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
          smul_apply, map_smul] using (hall u x).tsum_eq.symm
  obtain ⟨hn, htr⟩ := absolutePW_nuclearTrace_series _ p.coeff p.functional z
    p.summable_coeff ⟨P, hf⟩ (R := (∫ u, B u) + 1) (by positivity)
    (fun n ↦ (hz n).trans (by linarith)) hIseries
  refine ⟨hn, ?_⟩
  rw [← htr.tsum_eq]
  let a (n : ℕ) (u : ℝ) := p.coeff n * p.functional n (F n u)
  have hai (n : ℕ) : Integrable (a n) :=
    ((p.functional n).integrable_comp (hFi n)).const_mul _
  have haB (n : ℕ) (u : ℝ) : ‖a n u‖ ≤ (‖p.coeff n‖ * P) * B u := by
    dsimp only [a]
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (((p.functional n).le_opNorm _).trans (mul_le_mul (hf n) (hFb n u) (norm_nonneg _) hP))
      (norm_nonneg _)).trans_eq (by ring)
  have hsa : Summable (fun n ↦ ∫ u, ‖a n u‖) := by
    apply (p.summable_coeff.mul_right (P * ∫ u, B u)).of_nonneg_of_le
    · intro n; exact integral_nonneg fun _ ↦ norm_nonneg _
    · intro n
      have h := integral_mono_ae (hai n).norm (hBi.const_mul (‖p.coeff n‖ * P)) (.of_forall (haB n))
      simpa only [integral_const_mul, mul_assoc] using h
  have hza (n : ℕ) : p.coeff n * p.functional n (z n) = ∫ u, a n u := by
    dsimp only [z]
    rw [← (p.functional n).integral_comp_comm (hFi n), ← integral_const_mul]
  simp_rw [hza]
  rw [integral_tsum_of_summable_integral_norm hai hsa]
  apply integral_congr_ae
  refine .of_forall fun u ↦ ?_
  have hnorm (n : ℕ) : ‖M (U (t-u) (y n))‖ ≤ ‖M‖ * (‖U (t-u)‖ * Y) :=
    (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (((U (t-u)).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hyY n) (norm_nonneg _))) (norm_nonneg _))
  obtain ⟨_, htrace⟩ := absolutePW_nuclearTrace_series (M * U (t-u) * N.val) p.coeff p.functional
    (fun n ↦ M (U (t-u) (y n))) p.summable_coeff ⟨P, hf⟩
    (R := ‖M‖ * (‖U (t-u)‖ * Y) + 1) (by positivity)
    (fun n ↦ (hnorm n).trans (by linarith))
    (fun x ↦ by simpa only [y, mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_smul] using
      (M.comp (U (t-u))).hasSum (p.hasSum x))
  refine ((htrace.mul_left (k u)).congr_fun fun n ↦ ?_).tsum_eq
  dsimp only [a, F]
  rw [map_smul, smul_eq_mul]
  ring


/-- Testing a nuclear translation orbit against a fixed operator detects every
isolated eigenfrequency whose weighted rank-one trace is nonzero. -/
private theorem absolutePW_orbit_trace_not_tendsto_zero
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (Λ : ι → StrongDual ℂ H) (hBasis : IsSpectralMarkushevichBasis v Λ)
    (U : ℝ → H →L[ℂ] H) (hU : ∀ x, Continuous (fun t ↦ U t x))
    {C : ℝ} (hC : 0 ≤ C) (hUb : ∀ t, ‖U t‖ ≤ C * (1 + |t|))
    (N : nuclearEndomorphisms H) (M : H →L[ℂ] H)
    (ξ : ι → ℝ) (d : ι → ℂ)
    (hD : ∀ t j x, Λ j (U t (N.val x)) = (Real.fourierChar (t * ξ j) : ℂ) * d j * Λ j x)
    (i : ι) (hi : d i ≠ 0) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ j ≠ i, r ≤ dist (ξ j) (ξ i) ∨ d j = 0)
    (hM : Λ i (M (v i)) ≠ 0) :
    ¬ Tendsto (fun t ↦ hilbertTrace
        (⟨M * U t * N.val, mul_mem_nuclearEndomorphisms_left _ N⟩ : nuclearEndomorphisms H))
      atTop (𝓝 0) := by
  classical
  let G (t : ℝ) := hilbertTrace
    (⟨M * U t * N.val, mul_mem_nuclearEndomorphisms_left _ N⟩ : nuclearEndomorphisms H)
  change ¬ Tendsto G atTop (𝓝 0)
  intro hlim
  let J := {j : ι // d j ≠ 0}
  let i' : J := ⟨i, hi⟩
  obtain ⟨k, hki, hkj⟩ := exists_isolatingSchwartzKernel (fun j : J ↦ ξ j.val) i' hr
    (fun j hj ↦ (hsep j.val (fun e ↦ hj (Subtype.ext e))).resolve_right j.property)
  have hk (j : ι) (hj : j ≠ i) : (𝓕 k : SchwartzMap ℝ ℂ) (ξ j) = 0 ∨ d j = 0 := by
    by_cases e : d j = 0
    · exact Or.inr e
    · exact Or.inl (hkj ⟨j,e⟩ (fun e ↦ hj (congrArg Subtype.val e)))
  let D (t : ℝ) := (U t).comp N.val
  have hDc : Continuous D := continuous_comp_nuclear_of_stronglyContinuous U hU hC hUb N.val N.property
  have hI (t : ℝ) : Integrable (fun u ↦ k u • D (t-u)) := by
    let K := C * ‖N.val‖
    have hb (s : ℝ) : ‖D s‖ ≤ K * (1 + |s|) := by
      calc
        _ ≤ ‖U s‖ * ‖N.val‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (C * (1 + |s|)) * ‖N.val‖ := mul_le_mul_of_nonneg_right (hUb s) (norm_nonneg _)
        _ = _ := by dsimp [K]; ring
    have hI' : Integrable (fun u ↦ ‖k u‖ * (K * (1 + |t|)) + K * (|u| * ‖k u‖)) := by
      apply Integrable.add ((k.integrable (μ := volume)).norm.mul_const _)
      simpa only [Real.norm_eq_abs, pow_one] using (k.integrable_pow_mul volume 1).const_mul K
    refine hI'.mono' (k.continuous.smul (hDc.comp (continuous_const.sub continuous_id))).aestronglyMeasurable ?_
    apply ae_of_all; intro u
    rw [norm_smul]
    calc
      _ ≤ ‖k u‖ * (K * (1 + |t| + |u|)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (hb _).trans (mul_le_mul_of_nonneg_left (by linarith [abs_sub t u]) (by positivity))
      _ = _ := by ring
  have hnorm (t : ℝ) : ‖G t‖ ≤ (‖M‖ * C * traceNorm N) * (1 + |t|) := by
    have hN : 0 ≤ traceNorm N := (norm_nonneg _).trans (norm_hilbertTrace_le N)
    calc
      _ ≤ ‖M * U t‖ * traceNorm N :=
        (norm_hilbertTrace_le _).trans (traceNorm_mul_left_le _ N)
      _ ≤ (‖M‖ * (C * (1 + |t|))) * traceNorm N :=
        mul_le_mul_of_nonneg_right
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (hUb t) (norm_nonneg _))) hN
      _ = _ := by ring
  have hGc : Continuous G := by
    obtain ⟨p⟩ := (isNuclearOperator_iff_nonempty_presentation N.val).mp N.property
    obtain ⟨P, hP, hf⟩ := ((NormedSpace.equicontinuous_tfae p.functional).out 1 7).mp p.equicontinuous
    obtain ⟨Y, hy⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp p.isBanachDisc.bounded).exists_norm_le
    have hY : 0 ≤ Y := (norm_nonneg _).trans (hy _ (p.vector_mem 0))
    let a (n : ℕ) (t : ℝ) := p.coeff n * p.functional n (M (U t (p.vector n)))
    have htrace (t : ℝ) : G t = ∑' n, a n t := by
      obtain ⟨_, htr⟩ := absolutePW_nuclearTrace_series (M * U t * N.val) p.coeff p.functional
        (fun n ↦ M (U t (p.vector n))) p.summable_coeff ⟨P, hf⟩
        (R := ‖M‖ * (‖U t‖ * Y) + 1) (by positivity)
        (fun n ↦ ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (((U t).le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (hy _ (p.vector_mem n)) (norm_nonneg _))) (norm_nonneg _))).trans (by linarith))
        (fun x ↦ by simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_smul] using
          (M.comp (U t)).hasSum (p.hasSum x))
      exact htr.tsum_eq.symm
    rw [funext htrace, continuous_iff_continuousAt]
    intro t
    let S := Metric.ball t 1
    let b := P * (‖M‖ * ((C * (2 + |t|)) * Y))
    have hcont : Continuous (fun s : S ↦ ∑' n, a n s.val) := by
      refine continuous_tsum (fun n ↦ ?_) (p.summable_coeff.mul_right b) (fun n s ↦ ?_)
      · exact (((p.functional n).continuous.comp (M.continuous.comp
          ((hU _).comp continuous_subtype_val))).const_mul (p.coeff n))
      · have hUs : ‖U (s : ℝ)‖ ≤ C * (2 + |t|) := by
          apply (hUb _).trans
          apply mul_le_mul_of_nonneg_left _ hC
          have hd : |(s : ℝ) - t| < 1 := Metric.mem_ball.mp s.property
          linarith [abs_sub_abs_le_abs_sub (s : ℝ) t]
        dsimp only [a, b]
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply ((p.functional n).le_opNorm _).trans
        exact mul_le_mul (hf n)
          ((M.le_opNorm _).trans (mul_le_mul_of_nonneg_left
            (((U (s : ℝ)).le_opNorm _).trans (mul_le_mul hUs
              (hy _ (p.vector_mem n)) (norm_nonneg _) (by positivity))) (norm_nonneg _)))
          (norm_nonneg _) hP
    exact (continuousOn_iff_continuous_domRestrict.mpr hcont t (Metric.mem_ball_self one_pos)).continuousAt
      (Metric.ball_mem_nhds t one_pos)
  have hlim' := scalarConvolution_tendsto_zero k G hGc (by
    exact mul_nonneg (mul_nonneg (norm_nonneg _) hC) ((norm_nonneg _).trans (norm_hilbertTrace_le N))) hnorm hlim
  have heq (t : ℝ) : (∫ u, k u * G (t-u)) =
      (Real.fourierChar (t * ξ i) : ℂ) * d i * Λ i (M (v i)) := by
    obtain ⟨hn, htrace⟩ := absolutePW_integrate_nuclear_orbit U hU hC hUb N M k t (hI t)
    have eq := integrate_isolatedEigenfrequency v Λ hBasis D ξ d hD i k hki hk t (hI t)
    let c := (Real.fourierChar (t * ξ i) : ℂ) * d i
    have hmap : M.comp (∫ u, k u • (U (t-u)).comp N.val) =
        (Λ i).smulRight (c • M (v i)) := by
      change M.comp (∫ u, k u • D (t-u)) = _
      rw [eq]
      ext x
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_smul]
      exact smul_comm c (Λ i x) (M (v i))
    trans hilbertTrace (⟨_, hn⟩ : nuclearEndomorphisms H)
    · exact htrace.symm
    trans hilbertTrace (⟨(Λ i).smulRight (c • M (v i)), isNuclearOperator_smulRight _ _⟩ :
      nuclearEndomorphisms H)
    · exact congrArg hilbertTrace (Subtype.ext hmap)
    · rw [hilbertTrace_smulRight, map_smul, smul_eq_mul]
  have hn := hlim'.norm
  simp only [heq, norm_zero, norm_mul, Circle.norm_coe, one_mul] at hn
  exact (mul_ne_zero (norm_ne_zero_iff.mpr hi) (norm_ne_zero_iff.mpr hM))
    (tendsto_nhds_unique tendsto_const_nhds hn)

end

section

local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hs" => (show (1 : ℝ) < 2 from one_lt_two)
local notation "hs₂" => (show (0 : ℝ) ≤ 2 from zero_le_two)
local notation "Θ₂(" F ")" => globalThetaSobolev F (1/2) h₀ hs₂
local notation "Q₂(" F ")" => spectralSobolevQuotient F (1/2) h₀ hs₂
local notation "W₂(" F ")" => CompactIntervalSobolev (μ(F))
  (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) 0 0 2
local notation "τ₂(" F ")" => hardySobolevTranslation (μ(F)) (m𝔽(F)) 0 0 2 h₀ hs₂
local notation "A₂(" F ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ φ
local notation "U₂(" F ", " φ ")" => spectralConvolution (F := F) (1/2) h₀ hs₂ φ
local notation "zetaPoint(" t ")" => ((1 : ℂ) / 2 + (t : ℂ) * Complex.I)
local notation "η(" χ ", " j ")" => ideleClassNormTwist (χ (Subtype.val j).1) (((Subtype.val j).2.1 : ℂ) * Complex.I)

/-- The strict Sobolev cutoff at weight two admits only order-zero evaluations. -/
private theorem absolutePW_jet_order_zero {F : Type} [Field F] [NumberField F]
    {χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)}
    (j : SpectralLineJetIndex χ (1/2) 2) : j.val.2.2 = 0 := by
  have h := ((lt_spectralBoundaryMultiplicity _ _ _).mp j.property).2
  by_contra hz
  have hb : 1 ≤ j.val.2.2 := Nat.one_le_iff_ne_zero.mpr hz
  have hb' : (1 : ℝ) ≤ (j.val.2.2 : ℝ) := by exact_mod_cast hb
  linarith

/-- Integrating a test against the exponent gives the eigenvalue on a
zero-order quotient coordinate. The translation calculation follows
`spectralLine_wrongWeight_convolution` from Ch10 §3. -/
private theorem absolutePW_jet_eigen {F : Type} [Field F] [NumberField F]
    {χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)}
    (j : SpectralLineJetIndex χ (1/2) 2) (Λ : StrongDual ℂ Q₂(F))
    (hΛ : spectralSobolevDualEmbedding F (1/2) h₀ hs₂ Λ =
      (spectralLineJet_memLp χ hs j).toLp
        (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)) :
    (∀ k : C𝔽(F), ∀ f : W₂(F),
      Λ ((Θ₂(F)).mkQL (τ₂(F) k f)) = η(χ, j) k * Λ ((Θ₂(F)).mkQL f)) ∧
    ∀ (φ : BruhatCompactSupport C𝔽(F)) (x : Q₂(F)),
      Λ (U₂(F, φ) x) = (∫ g, φ.val g * η(χ, j) g ∂μ(F)) * Λ x := by
  let θ := η(χ, j)
  let L : StrongDual ℂ W₂(F) := Λ.comp (Θ₂(F)).mkQL
  have hΛeval (f : W₂(F)) : L f = ∫ g, f g * θ g ∂μ(F) := by
    have h := (spectralSobolevPairing_dual h₀ hs₂ L f).2
    change L f = spectralSobolevPairing f (spectralSobolevDualEmbedding F (1/2) h₀ hs₂ Λ) at h
    rw [h, hΛ, spectralSobolevPairing]
    have hwd (g : C𝔽(F)) : intervalSobolevDensity 0 0 2
        (Real.log ((ideleClassNorm F g).val : ℝ)) =
        1 + (Real.log ((ideleClassNorm F g).val : ℝ))^2 := by
      norm_num [intervalSobolevDensity]
    have hlog : Continuous (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
      Real.continuousOn_log.comp_continuous
        (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
        (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
    have hac : μ(F) ≪ (μ(F)).withDensity (fun g ↦ ENNReal.ofReal
        ((intervalSobolevDensity 0 0 2 (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)) := by
      simp_rw [hwd]
      exact withDensity_absolutelyContinuous'
        ((continuous_const.add (hlog.pow 2)).measurable.inv.ennreal_ofReal.aemeasurable)
        (.of_forall fun _ ↦ ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
    apply integral_congr_ae
    filter_upwards [hac.ae_le (MemLp.coeFn_toLp (spectralLineJet_memLp χ hs j))] with g hg
    rw [hg]
    simp only [θ, spectralZeroJet, absolutePW_jet_order_zero j, pow_zero, mul_one,
      Complex.ofReal_zero, zero_add]
  have eig (k : C𝔽(F)) (f : W₂(F)) : L (τ₂(F) k f) = θ k * L f := by
    have htr := hardySobolevTranslation_apply (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ k f
    rw [hΛeval, hΛeval, integral_congr_ae (htr.mono fun g hg ↦ congrArg (· * θ g) hg)]
    calc
      _ = ∫ g, f g * θ (k * g) ∂μ(F) := by
        rw [← integral_mul_left_eq_self (fun g ↦ f (k⁻¹ * g) * θ g) k]
        simp only [inv_mul_cancel_left]
      _ = θ k * ∫ g, f g * θ g ∂μ(F) := by
        rw [← integral_const_mul]
        congr with g
        rw [map_mul]
        ring
  refine ⟨eig, fun φ x ↦ ?_⟩
  obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective (Θ₂(F))) x
  rw [spectralConvolution_mkQ]
  let τ := τ₂(F)
  have hp := bruhatRegularizedAction_apply (μ(F)) τ
    (exists_hardySobolevTranslation (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂).choose_spec.2 φ f
  have he := congrArg (fun z : PettisWeakCompletion W₂(F) ↦
    (show Module.Dual ℂ (StrongDual ℂ W₂(F)) from z) L) hp.2
  change L (A₂(F, φ) f) = ∫ g, L (φ.val g • τ g f) ∂μ(F) at he
  change L (A₂(F, φ) f) = (∫ g, φ.val g * θ g ∂μ(F)) * L f
  rw [he, ← integral_mul_const]
  apply integral_congr_ae
  exact .of_forall fun g ↦ by
    change L (φ.val g • τ₂(F) g f) = φ.val g * θ g * L f
    rw [map_smul, eig]
    simp only [smul_eq_mul, mul_assoc]

/-- Thomas Lince’s certified critical-line bracket gives a positive finite order
for the completed Hecke function of the trivial rational character. -/
private theorem absolutePW_critical_line_point :
    ∃ γ : ℝ, 0 < (meromorphicOrderAt
      (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) zetaPoint(γ)).untop₀.toNat := by
  obtain ⟨γ, -, hγ⟩ := HardyFirstZero.first_zero_on_line
  let z : ℂ := zetaPoint(γ)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  refine ⟨γ, ?_⟩
  change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  have hnot (u : ℂ) : meromorphicOrderAt riemannZeta u ≠ ⊤ := by
    refine hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (2 : ℂ))
      (mem_univ u) ?_
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm 2 (mem_univ _))).2
      (((differentiableAt_riemannZeta (by norm_num : (2 : ℂ) ≠ 1)).continuousAt.eventually_ne
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))).filter_mono nhdsWithin_le_nhds)
  have hpos : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at hγ
    rw [← hγ]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  rw [← Int.pos_iff_toNat_pos]
  exact (WithTop.coe_lt_coe.mp (by simpa only [WithTop.coe_untop₀_of_ne_top (hnot z), WithTop.coe_zero] using hpos))


/-- Quotient maps and orthogonal representatives identify the spectral projector. -/
local notation "q₂(" F ")" => (Θ₂(F)).mkQL
local notation "J₂(" F ")" => (Θ₂(F)).orthogonal.subtypeL.comp
  (Θ₂(F)).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap

private theorem absolutePW_quotient_section {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (K : Submodule ℂ V) [IsClosed (K : Set V)] :
    let q := K.mkQL
    let J := K.orthogonal.subtypeL.comp K.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
    q.comp J = 1 ∧ J.comp q = K.orthogonal.starProjection ∧
      K.starProjection + K.orthogonal.starProjection = 1 := by
  intro q J
  let E := K.orthogonal.starProjection
  have hq (x : V) : q (E x) = q x := by
    apply ((Submodule.Quotient.eq K).2 ?_).symm
    rw [show x - E x = K.starProjection x from
      sub_eq_of_eq_add (K.starProjection_add_starProjection_orthogonal x).symm]
    exact K.starProjection_apply_mem x
  have hJ : J.comp q = E := by
    apply ContinuousLinearMap.ext
    intro x
    have h := K.quotientEquivOrthogonal_mk (E x) (K.orthogonal.starProjection_apply_mem x)
    change K.quotientEquivOrthogonal (q (E x)) = _ at h
    rw [hq x] at h
    exact congrArg Subtype.val h
  refine ⟨?_, hJ, ContinuousLinearMap.ext K.starProjection_add_starProjection_orthogonal⟩
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ := K.mkQ_surjective x
  exact (congrArg q (DFunLike.congr_fun hJ u)).trans (hq u)

private theorem absolutePW_quotient_translation {F : Type} [Field F] [NumberField F]
    (g : ℝ → C𝔽(F)) (hgc : Continuous g)
    (hg : ∀ t, Real.log ((ideleClassNorm F (g t)).val : ℝ) = t) :
    let U (t : ℝ) := (q₂(F)).comp ((τ₂(F) (g t)).comp (J₂(F)))
    (∀ x, Continuous (fun t ↦ U t x)) ∧
    (∀ t, ‖U t‖ ≤ (‖q₂(F)‖ * ‖J₂(F)‖) * (1 + |t|)) := by
  intro U
  have hcont := (exists_hardySobolevTranslation (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂).choose_spec.2
  refine ⟨fun x ↦ (q₂(F)).continuous.comp (hcont.comp (hgc.prodMk continuous_const)), fun t ↦ ?_⟩
  have hbt := norm_hardySobolevTranslation_le (μ(F)) m𝔽(F) 0 0 2 h₀ hs₂ (g t)
  change ‖τ₂(F) (g t)‖ ≤ max (Real.exp (0 * Real.log ((ideleClassNorm F (g t)).val : ℝ)))
    (Real.exp (0 * Real.log ((ideleClassNorm F (g t)).val : ℝ))) *
    (1 + |Real.log ((ideleClassNorm F (g t)).val : ℝ)|) ^ ((2 : ℝ) / 2) at hbt
  norm_num [hg] at hbt
  calc
    ‖U t‖ ≤ ‖q₂(F)‖ * (‖τ₂(F) (g t)‖ * ‖J₂(F)‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖q₂(F)‖ * ((1 + |t|) * ‖J₂(F)‖) := by gcongr
    _ = _ := by ring

/-- No other zero of the trivial character approaches this ordinate, with
the scale used by the Fourier transform. -/
private theorem absolutePW_zero_isolated (γ : ℝ)
    (hγ : 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ)))
      zetaPoint(γ)).untop₀.toNat) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, t ≠ γ →
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ)))
        zetaPoint(t)).untop₀.toNat → r ≤ dist (t / (2 * Real.pi)) (γ / (2 * Real.pi)) := by
  let Z := {z : ℂ | 0 < (meromorphicOrderAt (continuedCompletedHeckeL
    (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat}
  have hm := (continuedCompletedHeckeL_spec (1 : PontryaginDual C𝔽(ℚ))).1.meromorphicOn
  have hcod : Zᶜ ∈ Filter.codiscrete ℂ := by
    filter_upwards [hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz
    rcases hz.2 with h | h <;> simp [Z, h]
  have hz := (isDiscrete_iff_nhdsWithin.mp (compl_mem_codiscrete_iff.mp hcod).2) _ hγ
  have he : ∀ᶠ z in 𝓝[Z] zetaPoint(γ), z = zetaPoint(γ) := by rw [hz]; exact eventually_pure.mpr rfl
  rcases Metric.mem_nhdsWithin_iff.mp he with ⟨δ, hδ, hball⟩
  refine ⟨δ / (2 * Real.pi), by positivity, fun t hne ht ↦ ?_⟩
  have hd : dist zetaPoint(t) zetaPoint(γ) = |t - γ| := by
    rw [dist_eq_norm]
    have e : zetaPoint(t) - zetaPoint(γ) = ((t - γ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hdt : δ ≤ |t - γ| := by
    by_contra! hl
    have hz' := hball ⟨Metric.mem_ball.mpr (hd.trans_lt hl), ht⟩
    apply hne
    simpa using congrArg Complex.im hz'
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  gcongr

end

section

local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "CQ₁" => (ideleClassNorm ℚ).ker
local notation "ℓ" => (fun x : CQ ↦ Real.log ((ideleClassNorm ℚ x).val : ℝ))
local notation "μQ" => ideleClassTamagawaMeasure ℚ

/-- Translate a compact smooth radial test along a norm section.  The initial
profile is modulated to be nonzero at the prescribed Mellin frequency. -/
private theorem absolutePW_radial_translates (γ : ℝ) :
    ∃ (σ : Multiplicative ℝ →ₜ* CQ) (ψ : ℝ → BruhatCompactSupport CQ),
      (∀ t, ℓ (σ (Multiplicative.ofAdd t)) = t) ∧
      (∀ t x, (ψ t).val x = (ψ 0).val ((σ (Multiplicative.ofAdd t))⁻¹ * x)) ∧
      (∀ t (k : CQ₁) x, (ψ t).val (k.val⁻¹ * x) = (ψ t).val x) ∧
      (∀ t, 0 ≤ t → tsupport (ψ t).val ⊆ {g | 1 ≤ ((ideleClassNorm ℚ g).val : ℝ)}) ∧
      (∫ g, (ψ 0).val g * ideleClassNormTwist (1 : PontryaginDual CQ)
        ((γ : ℂ) * Complex.I) g ∂μQ) ≠ 0 := by
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* CQ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* CQ := q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  let σ := τ.comp (positiveRealLogEquiv.symm : Multiplicative ℝ →ₜ* ℝ≥0ˣ)
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  have hσ (t : ℝ) : ℓ (σ (Multiplicative.ofAdd t)) = t := by
    dsimp only
    rw [← positiveRealLogEquiv_apply, show ideleClassNorm ℚ (σ (Multiplicative.ofAdd t)) =
      positiveRealLogEquiv.symm (Multiplicative.ofAdd t) from hτ _, positiveRealLogEquiv.apply_symm_apply]
    rfl
  let w := (γ : ℂ) * Complex.I
  let β : ContDiffBump (1 / 2 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  let H (x : ℝ) : ℂ := (β x : ℂ) * Complex.exp (-(w * x))
  have hH : ContDiff ℝ (∞ : ℕ∞ω) H :=
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hC : HasCompactSupport H := (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hneg (x : ℝ) (hx : x ≤ 0) : H x = 0 := by
    have hb : β x = 0 := β.zero_of_le_dist (by
      rw [Real.dist_eq, abs_of_neg (by linarith)]; change (1/4 : ℝ) ≤ _; linarith)
    simp [H, hb]
  let m : CQ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  have hproper : IsProperMap ℓ := by
    have he : (positiveRealLogEquiv ∘ m) = ℓ := funext fun g ↦ positiveRealLogEquiv_apply _
    exact he ▸ positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm ℚ)
  have hcompact {H' : ℝ → ℂ} (h : HasCompactSupport H') : HasCompactSupport (H' ∘ ℓ) :=
    HasCompactSupport.intro (hproper.isCompact_preimage h) (fun _ hx ↦ image_eq_zero_of_notMem_tsupport (f := H') hx)
  let ψ (t : ℝ) : BruhatCompactSupport CQ :=
    (⟨fun x ↦ H (ℓ x - t), (mem_bruhatSmoothSubmodule_iff _).mpr
      (isBruhatSmooth_logProfile m (hH.comp (contDiff_id.sub contDiff_const))),
      hcompact (hC.comp_homeomorph (Homeomorph.subRight t))⟩ : bruhatCompactSupportSubmodule CQ)
  have hψ (t : ℝ) (x : CQ) : (ψ t).val x = H (ℓ x - t) := rfl
  have hlog (a x : CQ) : ℓ (a⁻¹ * x) = ℓ x - ℓ a := by
    simp only [map_mul, map_inv, Units.val_mul, NNReal.coe_mul, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, Real.log_mul (inv_ne_zero (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
        (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', Real.log_inv]
    ring
  refine ⟨σ, ψ, hσ, fun t x ↦ ?_, fun t k x ↦ ?_, fun t ht ↦ ?_, ?_⟩
  · simp only [hψ, sub_zero, hlog, hσ]
  · simp only [hψ, hlog, show ideleClassNorm ℚ k.val = 1 from k.property,
      Units.val_one, NNReal.coe_one, Real.log_one, sub_zero]
  · apply closure_minimal _ (isClosed_le continuous_const (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)))
    intro x hx
    by_contra hn
    apply hx
    rw [hψ]
    apply hneg
    have hx' : (((ideleClassNorm ℚ x).val : ℝ)) < 1 := lt_of_not_ge hn
    have h := Real.log_neg (NNReal.coe_pos.mpr (Units.zero_lt _)) hx'
    linarith
  · have hM (x : CQ) : (ψ 0).val x * ideleClassNormTwist (1 : PontryaginDual CQ) w x =
        (β (ℓ x) : ℂ) := by
      rw [hψ, sub_zero]
      have hx : 0 < ((ideleClassNorm ℚ x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      change ((β (ℓ x) : ℂ) * Complex.exp (-(w * (ℓ x : ℂ)))) *
        (1 * ((((ideleClassNorm ℚ x).val : ℝ) : ℂ) ^ w)) = _
      rw [one_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
        ← Complex.ofReal_log hx.le, mul_comm _ w, mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, mul_one]
    simp_rw [show (γ : ℂ) * Complex.I = w from rfl, hM]
    rw [integral_complex_ofReal]
    apply Complex.ofReal_ne_zero.mpr
    have hβ : HasCompactSupport (fun x : CQ ↦ β (ℓ x)) :=
      HasCompactSupport.intro (hproper.isCompact_preimage β.hasCompactSupport)
        (fun _ hx ↦ image_eq_zero_of_notMem_tsupport hx)
    exact (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μQ)
      (β.continuous.comp hproper.continuous) hβ (fun _ ↦ β.nonneg) (x := σ (Multiplicative.ofAdd (1/2))) (by
        have hb : β (1/2) = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
        exact ((congrArg β (hσ (1/2))).trans hb).trans_ne one_ne_zero)).ne'

/-- Translation multiplies a compact test's Mellin transform by the value of
the quasi-character at the translating class. -/
private theorem absolutePW_translated_mellin {φ ψ : BruhatCompactSupport CQ} {a : CQ}
    (h : ∀ g, ψ.val g = φ.val (a⁻¹ * g)) (c : QuasiCharacter CQ) :
    ∫ g, ψ.val g * c g ∂μQ = c a * ∫ g, φ.val g * c g ∂μQ := by
  rw [← integral_mul_left_eq_self (fun g ↦ ψ.val g * c g) a, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun g ↦ by
    change ψ.val (a * g) * c (a * g) = c a * (φ.val g * c g)
    rw [h, inv_mul_cancel_left, map_mul]; ring)

/-- A radial test has zero Mellin transform in every nontrivial norm-one type. -/
private theorem absolutePW_radial_mellin_vanish (φ : BruhatCompactSupport CQ)
    (hφ : ∀ (k : CQ₁) x, φ.val (k.val⁻¹ * x) = φ.val x)
    (χ : PontryaginDual CQ) (s : ℂ) (hχ : ¬ ∀ k : CQ₁, χ k.val = 1) :
    (∫ g, φ.val g * ideleClassNormTwist χ s g ∂μQ) = 0 := by
  obtain ⟨k, hk⟩ := not_forall.mp hχ
  let c := ideleClassNormTwist χ s
  have hc : c k.val ≠ 1 := by
    change (χ k.val : ℂ) * (((ideleClassNorm ℚ k.val).val : ℝ) : ℂ) ^ s ≠ 1
    rw [show ideleClassNorm ℚ k.val = 1 from k.property]
    simpa using fun (h : (χ k.val : ℂ) = 1) ↦ hk (Circle.ext h)
  have h := absolutePW_translated_mellin (φ := φ) (ψ := φ) (a := k.val)
    (fun g ↦ (hφ k g).symm) c
  let z := ∫ g, φ.val g * c g ∂μQ
  change z = c k.val * z at h
  change z = 0
  exact (mul_eq_zero.mp (show (c k.val - 1) * z = 0 by rw [sub_mul, one_mul, ← h, sub_self])).resolve_left
    (sub_ne_zero.mpr hc)

/-- Convolution by a norm-one invariant test sends every input to the trivial
isotype, before passage to any theta quotient. -/
private theorem absolutePW_radial_convolution_mem (φ : BruhatCompactSupport CQ)
    (hφ : ∀ (k : CQ₁) x, φ.val (k.val⁻¹ * x) = φ.val x) :
    let m : CQ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
    ∀ u, hardySobolevTestAction μQ m 0 0 2 le_rfl zero_le_two φ u ∈
      actionIsotype ((hardySobolevTranslation μQ m 0 0 2 le_rfl zero_le_two).comp
        (ideleClassNorm ℚ).ker.subtype) (1 : PontryaginDual CQ₁) := by
  intro m u
  rw [mem_actionIsotype]
  intro k
  let τ := hardySobolevTranslation μQ m 0 0 2 le_rfl zero_le_two
  let v := hardySobolevTestAction μQ m 0 0 2 le_rfl zero_le_two φ u
  have hv := hardySobolevTestAction_apply μQ m 0 0 2 le_rfl zero_le_two φ u
  change (v : CQ → ℂ) =ᵐ[μQ] _ at hv
  have hv' := (measurePreserving_mul_left μQ k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hv
  have hcv (x : CQ) : lcaConvolution μQ φ.val u (k.val⁻¹ * x) = lcaConvolution μQ φ.val u x := by
    unfold lcaConvolution
    rw [← integral_mul_left_eq_self (fun g ↦ φ.val g * u (g⁻¹ * (k.val⁻¹ * x))) k.val⁻¹]
    exact integral_congr_ae (.of_forall fun g ↦ by
      dsimp only
      rw [hφ k, show (k.val⁻¹ * g)⁻¹ * (k.val⁻¹ * x) = g⁻¹ * x by group])
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, PontryaginDual.one_apply,
    Circle.coe_one, one_smul]
  apply Lp.ext
  apply (withDensity_absolutelyContinuous _ _).ae_eq
  refine (hardySobolevTranslation_apply μQ m 0 0 2 le_rfl zero_le_two k.val v).trans ?_
  filter_upwards [hv', hv] with x hk hx
  exact hk.trans ((hcv x).trans hx.symm)

end

section

local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "nQ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : CQ →ₜ* ℝ≥0ˣ)

/-- Expanding sharp radial cutoffs converge strongly on every weighted L² space. -/
private theorem absolutePW_strong_cutoffs (ν : Measure CQ) :
    ∃ P : ℝ → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν,
      (∀ R, ‖P R‖ ≤ 1) ∧ (∀ u, Tendsto (fun R ↦ P R u) atTop (𝓝 u)) ∧
      ∀ᶠ R in atTop, ∃ (ε : ℝ) (ρ : CQ → ℝ) (hρ : IsModulatedCutoff nQ R ε ρ),
        0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε ∧ P R = modulatedCutoffOperator nQ ν hρ := by
  let ε : ℝ → ℝ := fun R ↦ 1 / (2 * R ^ 2)
  let ρ : ℝ → CQ → ℝ := fun R g ↦ if ((nQ g).val : ℝ) ∈ Icc R⁻¹ R then 1 else 0
  have hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0) := by
    have hEq : (fun R : ℝ ↦ ε R * R) =ᶠ[atTop] fun R ↦ (1/2 : ℝ) * R⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      dsimp [ε]
      field_simp [hR.ne']
    apply Tendsto.congr' hEq.symm
    simpa using tendsto_inv_atTop_zero.const_mul (1/2 : ℝ)
  have hρ : ∀ᶠ R in atTop,
      IsModulatedCutoff nQ R (ε R) (ρ R) ∧ 0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R :=
    (eventually_ge_atTop (2 : ℝ)).mono fun R hR ↦ isModulatedCutoff_closedBand nQ R hR
  obtain ⟨P, hPb, hPl, hPe⟩ :=
    exists_stronglyConvergent_modulatedCutoffOperators CQ nQ ν ε ρ hε hρ
  exact ⟨P, hPb, hPl, hρ.mono fun R hR ↦ ⟨ε R, ρ R, hR.1, hR.2.1, hR.2.2, hPe R hR.1⟩⟩

/-- A norm cutoff preserves the trivial norm-one isotype. -/
private theorem absolutePW_cutoff_mem_trivial (R ε : ℝ) (ρ : CQ → ℝ)
    (hρ : IsModulatedCutoff nQ R ε ρ) :
    let μ := ideleClassTamagawaMeasure ℚ
    let ν := μ.withDensity (fun g : CQ ↦ ENNReal.ofReal
      (intervalSobolevDensity 0 0 2 (Real.log ((nQ g).val : ℝ))))
    let I := actionIsotype ((hardySobolevTranslation μ nQ 0 0 2 le_rfl zero_le_two).comp
      (ideleClassNorm ℚ).ker.subtype) (1 : PontryaginDual (ideleClassNorm ℚ).ker)
    ∀ u ∈ I, modulatedCutoffOperator nQ ν hρ u ∈ I := by
  intro μ ν I u hu
  let τ := hardySobolevTranslation μ nQ 0 0 2 le_rfl zero_le_two
  let M := modulatedCutoffOperator nQ ν hρ
  have hac : μ ≪ ν := by
    apply withDensity_absolutelyContinuous'
    · change AEMeasurable (fun g : CQ ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 2
          (Real.log ((ideleClassNorm ℚ g).val : ℝ)))) μ
      have hw (x : ℝ) : intervalSobolevDensity 0 0 2 x = 1 + x ^ 2 := by
        norm_num [intervalSobolevDensity]
      simp_rw [hw]
      exact (measurable_const.add (((NNReal.continuous_coe.comp (Units.continuous_val.comp
        (isProperMap_ideleClassNorm ℚ).continuous)).measurable.log).pow_const 2)).ennreal_ofReal.aemeasurable
    · exact .of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (by dsimp [intervalSobolevDensity]; positivity)).ne'
  have hca : ν ≪ μ := withDensity_absolutelyContinuous _ _
  obtain ⟨q, -, hq, -⟩ := hρ.profile
  apply (mem_actionIsotype _ _ _).mpr
  intro k
  have hfix := (mem_actionIsotype _ _ _).mp hu k
  simpa only [τ, MonoidHom.comp_apply, Subgroup.subtype_apply, PontryaginDual.one_apply, Circle.coe_one, one_smul] using
    (show τ k.val (M u) = M u from by
      have hfix' : τ k.val u = u := by simpa only [τ, MonoidHom.comp_apply, Subgroup.subtype_apply, PontryaginDual.one_apply, Circle.coe_one, one_smul] using hfix
      have htr := hardySobolevTranslation_apply μ nQ 0 0 2 le_rfl zero_le_two k.val u
      change (τ k.val u : CQ → ℂ) =ᵐ[μ] _ at htr
      rw [hfix'] at htr
      have hm := hac.ae_eq (modulatedCutoffOperator_apply nQ ν hρ u)
      have hmk := (measurePreserving_mul_left μ k.val⁻¹).quasiMeasurePreserving.ae_eq_comp hm
      apply Lp.ext
      apply hca.ae_eq
      refine (hardySobolevTranslation_apply μ nQ 0 0 2 le_rfl zero_le_two k.val (M u)).trans ?_
      filter_upwards [hmk, htr, hm] with g hk hgu hmg
      change (M u) (k.val⁻¹ * g) = _ at hk
      change (M u) (k.val⁻¹ * g) = M u g
      change (M u) g = _ at hmg
      rw [hk, hmg]
      change (ρ (k.val⁻¹*g) : ℂ) * u (k.val⁻¹*g) = (ρ g : ℂ) * u g
      rw [← hgu, hq, hq]
      change (q (((ideleClassNorm ℚ (k.val⁻¹*g)).val : ℝ)) : ℂ) * u g = _
      rw [map_mul, map_inv, show ideleClassNorm ℚ k.val = 1 from k.property, inv_one, one_mul]
      rfl)

end

section

private theorem absolutePW_nuclear_postcomp {H W I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup I] [InnerProductSpace ℂ I] [CompleteSpace I]
    (N : H →L[ℂ] W) (hN : IsNuclearOperator N) (B : W →L[ℂ] I) :
    IsNuclearOperator (B.comp N) := by
  obtain ⟨c, f, y, hc, hf, hy, hs⟩ := (isNuclearOperator_iff_isBanachNuclear N).mp hN
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  exact ⟨c, f, B ∘ y, hc, hf, (B.continuous.tendsto' 0 0 (map_zero B)).comp hy,
    fun x ↦ by simpa only [map_smul, Function.comp_apply, ContinuousLinearMap.comp_apply] using B.hasSum (hs x)⟩

/-- A trace equality for the geometrically projected inputs identifies the
trace of the remaining input component with the compressed quotient trace. -/
private theorem absolutePW_trace_compatibility_split {W H : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I : Submodule ℂ W) [CompleteSpace I]
    (q : W →L[ℂ] H) (J : H →L[ℂ] W) (Q M A : W →L[ℂ] W)
    (N : nuclearEndomorphisms H) (T : nuclearEndomorphisms I)
    (hqJ : ∀ x, q (J x) = x) (hJq : ∀ x, J (q x) = x - Q x)
    (hqA : ∀ x, q (A x) = N.val (q x))
    (hQ : ∀ x ∈ I, Q x ∈ I) (hA : ∀ x, A x ∈ I) (hM : ∀ x ∈ I, M x ∈ I)
    (hT : ∀ x : I, T.val x = I.orthogonalProjectionOnto (M (Q (A x)))) :
    let P := I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL)
    hilbertTrace (⟨T.val * P, mul_mem_nuclearEndomorphisms_right P T⟩ : nuclearEndomorphisms I) =
      hilbertTrace T →
    let B := I.orthogonalProjectionOnto.comp (M.comp (A.comp
      (((ContinuousLinearMap.id ℂ W) - Q).comp I.subtypeL)))
    ∃ hB : IsNuclearOperator B,
      hilbertTrace (⟨(q.comp (M.comp J)) * N.val, mul_mem_nuclearEndomorphisms_left _ N⟩ :
        nuclearEndomorphisms H) = hilbertTrace (⟨B, hB⟩ : nuclearEndomorphisms I) := by
  intro P htr B
  let p := I.orthogonalProjectionOnto
  let X := (p.comp (M.comp J)).comp N.val
  let Y := q.comp I.subtypeL
  have hX := absolutePW_nuclear_postcomp N.val N.property (p.comp (M.comp J))
  obtain ⟨hYX, hXY, hcyc⟩ := absolutePW_cross_trace X hX Y
  have hfix (x : W) (hx : x ∈ I) : (p x : W) = x := I.starProjection_eq_self_iff.mpr hx
  have hJN (x : H) : J (N.val x) ∈ I := by
    have hh := hqA (J x)
    rw [hqJ] at hh
    rw [← hh, hJq]
    exact I.sub_mem (hA _) (hQ _ (hA _))
  have hmap : Y.comp X = (q.comp (M.comp J)) * N.val := by
    ext x
    change q (p (M (J (N.val x)))) = q (M (J (N.val x)))
    rw [hfix _ (hM _ (hJN _))]
  have hP (x : I) : (P x : W) = Q x := hfix _ (hQ _ x.property)
  have hqa (x : W) : q (x - Q x) = q x := (congrArg q (hJq x).symm).trans (hqJ _)
  let TQ : nuclearEndomorphisms I := ⟨T.val * P, mul_mem_nuclearEndomorphisms_right P T⟩
  let S : nuclearEndomorphisms I := ⟨X.comp Y, hXY⟩
  have hB : B = (T - TQ + S).val := by
    apply ContinuousLinearMap.ext
    intro x
    change p (M (A ((x : W) - Q x))) = T.val x - T.val (P x) + p (M (J (N.val (q x))))
    rw [hT, hT, hP]
    have he : J (N.val (q x)) =
        A ((x : W) - Q x) - Q (A ((x : W) - Q x)) := by
      rw [← hJq, hqA, hqa]
    rw [he]
    simp only [map_sub]
    abel
  have hn : IsNuclearOperator B := hB ▸ (T - TQ + S).property
  refine ⟨hn, ?_⟩
  obtain ⟨L, hL⟩ := hilbertTrace_linear (H := I)
  have hTS : L TQ = L T := by simpa [hL] using htr
  calc
    _ = hilbertTrace (⟨Y.comp X, hYX⟩ : nuclearEndomorphisms H) :=
      congrArg hilbertTrace (Subtype.ext hmap.symm)
    _ = hilbertTrace S := hcyc
    _ = L (T - TQ + S) := by rw [map_add, map_sub, hTS, sub_self, zero_add, hL]
    _ = hilbertTrace (⟨B, hn⟩ : nuclearEndomorphisms I) :=
      (hL _).trans (congrArg hilbertTrace (Subtype.ext hB.symm))

/-- Compressing a nuclear map whose whole image is in the closed subspace
preserves its trace. -/
private theorem absolutePW_trace_compression_eq_ambient {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (I : Submodule ℂ W) [CompleteSpace I] (V : W →L[ℂ] W)
    (hV : IsNuclearOperator V) (hI : ∀ x, V x ∈ I) :
    ∃ hB : IsNuclearOperator (I.orthogonalProjectionOnto.comp (V.comp I.subtypeL)),
      hilbertTrace (⟨I.orthogonalProjectionOnto.comp (V.comp I.subtypeL), hB⟩ :
        nuclearEndomorphisms I) = hilbertTrace (⟨V, hV⟩ : nuclearEndomorphisms W) := by
  let U := I.orthogonalProjectionOnto.comp V
  have hU := absolutePW_nuclear_postcomp V hV I.orthogonalProjectionOnto
  obtain ⟨hiU, hUi, htr⟩ := absolutePW_cross_trace U hU I.subtypeL
  have he : I.subtypeL.comp U = V := by
    ext x
    exact I.starProjection_eq_self_iff.mpr (hI x)
  exact ⟨hUi, htr.symm.trans (congrArg hilbertTrace (Subtype.ext he))⟩


/-- A compatible compressed geometric trace leaves exactly the ambient
trace after right restriction to the spectral complement. -/
private theorem absolutePW_trace_compatibility_ambient {W H : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I : Submodule ℂ W) [CompleteSpace I]
    (q : W →L[ℂ] H) (J : H →L[ℂ] W) (Q E M A : W →L[ℂ] W)
    (N : nuclearEndomorphisms H) (T : nuclearEndomorphisms I)
    (hE : (ContinuousLinearMap.id ℂ W) - Q = E)
    (hqJ : ∀ x, q (J x) = x) (hJq : ∀ x, J (q x) = x - Q x)
    (hqA : ∀ x, q (A x) = N.val (q x))
    (hQ : ∀ x ∈ I, Q x ∈ I) (hA : ∀ x, A x ∈ I) (hM : ∀ x ∈ I, M x ∈ I)
    (hT : ∀ x : I, T.val x = I.orthogonalProjectionOnto (M (Q (A x))))
    (htr : hilbertTrace (productTraceClass(T, I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL))) =
      hilbertTrace T) (hV : IsNuclearOperator ((M.comp A).comp E)) :
    hilbertTrace (⟨(q.comp (M.comp J)) * N.val, mul_mem_nuclearEndomorphisms_left _ N⟩ :
      nuclearEndomorphisms H) = hilbertTrace (⟨(M.comp A).comp E, hV⟩ : nuclearEndomorphisms W) := by
  obtain ⟨_, htrace⟩ := absolutePW_trace_compatibility_split I q J Q M A N T
    hqJ hJq hqA hQ hA hM hT htr
  obtain ⟨_, hamb⟩ := absolutePW_trace_compression_eq_ambient I ((M.comp A).comp E) hV
    (fun x ↦ hM _ (hA (E x)))
  refine htrace.trans ?_
  have eComp : I.orthogonalProjectionOnto.comp (M.comp (A.comp
      (((ContinuousLinearMap.id ℂ W) - Q).comp I.subtypeL))) =
      I.orthogonalProjectionOnto.comp (((M.comp A).comp E).comp I.subtypeL) := by
    rw [hE]
    rfl
  exact (congrArg hilbertTrace (Subtype.ext eComp)).trans hamb

private theorem absolutePW_trace_compatibility_of_section {W H : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I : Submodule ℂ W) [CompleteSpace I]
    (q : W →L[ℂ] H) (J : H →L[ℂ] W) (Q E M A : W →L[ℂ] W)
    (N : nuclearEndomorphisms H)
    (hMA : IsNuclearOperator (M.comp A))
    (hsec : q.comp J = 1 ∧ J.comp q = E ∧ Q + E = 1)
    (hqA : ∀ x, q (A x) = N.val (q x))
    (hQ : ∀ x ∈ I, Q x ∈ I) (hA : ∀ x, A x ∈ I) (hM : ∀ x ∈ I, M x ∈ I)
    (hcompat : ∃ T : nuclearEndomorphisms I,
      (∀ x : I, T.val x = I.orthogonalProjectionOnto (M (Q (A x)))) ∧
      hilbertTrace (productTraceClass(T, I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL))) =
        hilbertTrace T) :
    hilbertTrace (productTraceClass((⟨M.comp A, hMA⟩ : nuclearEndomorphisms W), E)) =
      hilbertTrace (⟨(q.comp (M.comp J)) * N.val,
        mul_mem_nuclearEndomorphisms_left _ N⟩ : nuclearEndomorphisms H) := by
  have hqJ : ∀ x, q (J x) = x := DFunLike.congr_fun hsec.1
  have hJq (x : W) : J (q x) = x - Q x :=
    (DFunLike.congr_fun hsec.2.1 x).trans (eq_sub_of_add_eq' (DFunLike.congr_fun hsec.2.2 x))
  have hE : (ContinuousLinearMap.id ℂ W) - Q = E :=
    ContinuousLinearMap.ext fun x ↦ (hJq x).symm.trans (DFunLike.congr_fun hsec.2.1 x)
  obtain ⟨T, hT, htr⟩ := hcompat
  exact (absolutePW_trace_compatibility_ambient I q J Q E M A N T hE hqJ hJq hqA hQ hA hM
    hT htr (mul_mem_nuclearEndomorphisms_right E ⟨_, hMA⟩)).symm

private theorem absolutePW_trace_mul_tendsto_zero {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (B : ℝ → nuclearEndomorphisms W) (E : W →L[ℂ] W)
    (hB : Tendsto (fun t ↦ traceNorm (B t)) atTop (𝓝 0)) :
    Tendsto (fun t ↦ hilbertTrace (productTraceClass(B t, E))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _
    (show Tendsto (fun t ↦ ‖E‖ * traceNorm (B t)) atTop (𝓝 0) from by
      simpa only [mul_zero] using hB.const_mul ‖E‖)
  exact Eventually.of_forall fun t ↦ (norm_hilbertTrace_le _).trans (traceNorm_mul_right_le E (B t))

end

section

/-- Uniformly bounded strong convergence gives convergence of the scalar trace
after multiplication on the right by the converging maps. -/
private theorem absolutePWCondensation_trace_tendsto_strong
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (P : ℝ → H →L[ℂ] H) (Q : H →L[ℂ] H)
    (hP : ∀ u, Tendsto (fun Λ ↦ P Λ u) atTop (𝓝 (Q u)))
    (hbound : ∀ Λ, ‖P Λ‖ ≤ 1) :
    Tendsto (fun Λ ↦ hilbertTrace (productTraceClass(T, P Λ))) atTop
      (𝓝 (hilbertTrace (productTraceClass(T, Q)))) := by
  obtain ⟨p⟩ := (isNuclearOperator_iff_nonempty_presentation T.val).mp T.property
  obtain ⟨C, hC, hfun⟩ := ((NormedSpace.equicontinuous_tfae p.functional).out 1 7).mp
    p.equicontinuous
  obtain ⟨D, hvec⟩ := ((NormedSpace.isVonNBounded_iff ℂ).mp p.isBanachDisc.bounded).exists_norm_le
  have htrace (A : H →L[ℂ] H) : hilbertTrace (productTraceClass(T, A)) =
      ∑' n, p.coeff n * p.functional n (A (p.vector n)) := by
    let r : NuclearPresentation (T.val * A) :=
      { p with
        functional := fun n ↦ (p.functional n).comp A
        equicontinuous := fun U hU ↦ by
          have h := (A.continuous.tendsto' 0 0 (map_zero A)).eventually (p.equicontinuous U hU)
          simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
        hasSum := fun x ↦ p.hasSum (A x) }
    rw [hilbertTrace_eq_nuclearTrace]
    have hsum := ((exists_nuclearTrace_hasSum hilbert_approximationProperty
      (T.val * A) (mul_mem_nuclearEndomorphisms_right A T)).exists.choose_spec r).2
    exact hsum.tsum_eq.symm
  simp_rw [htrace]
  apply tendsto_tsum_of_dominated_convergence (p.summable_coeff.mul_right (C * D))
  · intro n
    exact ((p.functional n).continuous.tendsto _ |>.comp (hP (p.vector n))).const_mul _
  · filter_upwards with Λ n
    have hle := (p.functional n).le_opNorm (P Λ (p.vector n))
    have hx := (P Λ).le_opNorm (p.vector n : H)
    have hx' : ‖P Λ (p.vector n)‖ ≤ D := hx.trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hbound Λ)).trans (hvec _ (p.vector_mem n)))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hle.trans (mul_le_mul (hfun n) hx' (norm_nonneg _) hC)) (norm_nonneg _)

end

section

local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "CQ₁" => (ideleClassNorm ℚ).ker
local notation "mQ" => (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : CQ →ₜ* ℝ≥0ˣ)
local notation "μQ" => ideleClassTamagawaMeasure ℚ
local notation "logQ" => (fun g : CQ ↦ Real.log ((ideleClassNorm ℚ g).val : ℝ))
local notation "νQ" => (μQ).withDensity (fun g : CQ ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logQ g)))
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hs" => (show (1 : ℝ) < 2 from one_lt_two)
local notation "hs₂" => (show (0 : ℝ) ≤ 2 from zero_le_two)
local notation "W" => CompactIntervalSobolev μQ logQ 0 0 2
local notation "Θ" => globalThetaSobolev ℚ (1/2) h₀ hs₂
local notation "H" => spectralSobolevQuotient ℚ (1/2) h₀ hs₂
local notation "τ" => hardySobolevTranslation μQ mQ 0 0 2 h₀ hs₂
local notation "A(" φ ")" => hardySobolevTestAction μQ mQ 0 0 2 h₀ hs₂ φ
local notation "S(" φ ")" => spectralConvolution (F := ℚ) (1/2) h₀ hs₂ φ

/-- Logarithmic coordinates turn a positive real complex power into an exponential. -/
private theorem absolutePW_cpow_exp (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp (z * x) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), mul_comm]

/-- A radial modulated cutoff on the rational classes has compact support by
properness of the norm, as in `IsModulatedCutoff.isCompact_tsupport'` in Ch09 §3. -/
private theorem absolutePW_cutoff_hasCompactSupport {R ε : ℝ} {ρ : CQ → ℝ}
    (hρ : IsModulatedCutoff mQ R ε ρ) : HasCompactSupport ρ := by
  let e := Nonneg.unitsHomeomorphPos ℝ
  have hS : IsCompact ((Subtype.val : Ioi (0:ℝ) → ℝ) ⁻¹' Icc R⁻¹ R) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr fun t (ht : t ∈ Icc R⁻¹ R) ↦
        mem_Ioi.mpr ((inv_pos.mpr hρ.radius_pos).trans_le ht.1)]
    exact isCompact_Icc
  exact ((isProperMap_ideleClassNorm ℚ).isCompact_preimage (e.isCompact_preimage.mpr hS)).of_isClosed_subset
    (isClosed_tsupport ρ) hρ.support_subset

private theorem absolutePW_cutoff_convolution_nuclear
    (φ : BruhatCompactSupport CQ) {R ε : ℝ} {ρ : CQ → ℝ}
    (hρ : IsModulatedCutoff mQ R ε ρ) (hband : 0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε) :
    IsNuclearOperator ((modulatedCutoffOperator mQ νQ hρ).comp A(φ)) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation mQ := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hsur : Function.Surjective mQ := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hT, _, _⟩ := truncatedHardySobolevConvolution_trace μQ mQ 0 0 2 h₀ hs₂ φ.val
    hc.aemeasurable φ.property.2 hb hm hsur hφs hρ hband
  rw [hardySobolevConvolution_eq_testAction μQ mQ 0 0 2 h₀ hs₂ φ hc.aemeasurable hb] at hT
  exact hT


private def absolutePW_rational_isotype (l : ℝ) (hl : l ≤ 0) :
    Submodule ℂ (CompactIntervalSobolev μQ logQ l 0 2) :=
  actionIsotype ((hardySobolevTranslation μQ mQ l 0 2 hl hs₂).comp
    (ideleClassNorm ℚ).ker.subtype) (1 : PontryaginDual CQ₁)

private instance absolutePW_rational_isotype_complete (l : ℝ) (hl : l ≤ 0) :
    CompleteSpace (absolutePW_rational_isotype l hl) :=
  (instClosedSpectralIsotypeSec2 hl hs₂ (1 : PontryaginDual CQ₁)).completeSpace_coe

private def absolutePW_rational_projection_preserves (l : ℝ) (hl : l ≤ 0) : Prop :=
  ∀ x : absolutePW_rational_isotype l hl,
    (globalThetaSobolev ℚ (1/2) hl hs₂).starProjection x.val ∈ absolutePW_rational_isotype l hl

private theorem absolutePW_rational_projection_preserves_zero :
    absolutePW_rational_projection_preserves 0 h₀ := by
  have h : absolutePW_rational_projection_preserves (-(0 : ℝ)) (neg_nonpos.mpr h₀) := by
    intro x
    exact geometricProjection_preserves_normOneIsotype (F := ℚ) hs₂ (1/2)
      (1 : PontryaginDual CQ₁) x
  let P (l : {l : ℝ // l ≤ 0}) := absolutePW_rational_projection_preserves l.val l.property
  have e : (⟨-(0 : ℝ), neg_nonpos.mpr h₀⟩ : {l : ℝ // l ≤ 0}) = ⟨0, h₀⟩ := Subtype.ext neg_zero
  exact (congrArg P e).mp h

private def absolutePW_rational_trace_compatible (l : ℝ) (hl : l ≤ 0) : Prop :=
  let I := absolutePW_rational_isotype l hl
  let Q := (globalThetaSobolev ℚ (1/2) hl hs₂).starProjection
  let P := I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL)
  let ν := (μQ).withDensity (fun g : CQ ↦ ENNReal.ofReal (intervalSobolevDensity l 0 2 (logQ g)))
  ∀ (φ : BruhatCompactSupport CQ), aboveOne(ℚ, φ) →
    ∀ (R ε : ℝ) (ρ : CQ → ℝ) (hρ : IsModulatedCutoff mQ R ε ρ),
    let M := modulatedCutoffOperator mQ ν hρ
    let A := hardySobolevTestAction μQ mQ l 0 2 hl hs₂ φ
    ∃ T : nuclearEndomorphisms I,
      (∀ x : I, T.val x = I.orthogonalProjectionOnto (M (Q (A x)))) ∧
      hilbertTrace (⟨T.val * P, mul_mem_nuclearEndomorphisms_right P T⟩ : nuclearEndomorphisms I) =
        hilbertTrace T

private theorem absolutePW_rational_trace_compatible_of_printed
    (h : Printed.absolutePWCondensation_trace_tendsto) :
    absolutePW_rational_trace_compatible 0 h₀ := by
  have e : (1 : PontryaginDual CQ).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : CQ₁ →ₜ* CQ) = 1 := by
    ext k
    rfl
  have h' : absolutePW_rational_trace_compatible (-(0 : ℝ)) (neg_nonpos.mpr h₀) := by
    intro φ hφ R ε ρ hρ
    let I := absolutePW_rational_isotype (-(0 : ℝ)) (neg_nonpos.mpr h₀)
    let : CompleteSpace I := absolutePW_rational_isotype_complete _ _
    let Q := (globalThetaSobolev ℚ (1/2) (neg_nonpos.mpr h₀) hs₂).starProjection
    let P := I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL)
    have hh := h ℚ 1 ∅ (1/2) 2 hs₂
      rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
    obtain ⟨T, ht, hlim⟩ := hh
    let T' : nuclearEndomorphisms I := T
    let PΛ (Λ : ℝ) : I →L[ℂ] I := absolutePWProjection (F := ℚ) (S := ∅) hs₂ (1/2) (1 : PontryaginDual CQ₁) Λ
    have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual CQ₁) ∅ :=
      e ▸ rational_one_unramifiedOutside_empty
    have hP (x : I) : Tendsto (fun Λ ↦ PΛ Λ x) atTop (𝓝 (P x)) :=
      absolutePWProjection_tendsto (F := ℚ) (S := ∅) hs₂ (1/2) (1 : PontryaginDual CQ₁)
        hu rational_empty_picTrivial x
    have hPb : ∀ Λ, ‖PΛ Λ‖ ≤ 1 := by
      intro Λ
      apply ContinuousLinearMap.opNorm_le_bound (PΛ Λ) zero_le_one
      intro x
      rw [one_mul]
      let K := (globalAbsolutePWSobolev (F := ℚ) (S := ∅) hs₂ (1/2)
        (1 : PontryaginDual CQ₁) Λ).comap I.subtype
      let : IsClosed (K : Set I) :=
        (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
      exact Submodule.norm_starProjection_apply_le K x
    refine ⟨T', fun x ↦ ?_, tendsto_nhds_unique
      (absolutePWCondensation_trace_tendsto_strong I T' PΛ P hP hPb) hlim⟩
    exact DFunLike.congr_fun ht x
  let P (l : {l : ℝ // l ≤ 0}) := absolutePW_rational_trace_compatible l.val l.property
  have he : (⟨-(0 : ℝ), neg_nonpos.mpr h₀⟩ : {l : ℝ // l ≤ 0}) = ⟨0, h₀⟩ := Subtype.ext neg_zero
  exact (congrArg P he).mp h'



local notation "qQ" => (Θ).mkQL
local notation "JQ" => (Θ).orthogonal.subtypeL.comp
  (Θ).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
local notation "EQ" => (Θ).orthogonal.starProjection
local notation "M(" ρ ")" => (modulatedCutoffOperator mQ νQ ρ : W →L[ℂ] W)
local notation "N(" φ ")" => (⟨S(φ), spectralLineConvolution_nuclear (1/2) hs φ⟩ : nuclearEndomorphisms H)

private theorem absolutePW_rational_match_traces
    (hcompat : absolutePW_rational_trace_compatible 0 h₀)
    (φ : BruhatCompactSupport CQ) (hsupport : aboveOne(ℚ, φ))
    (hrad : ∀ (k : CQ₁) x, φ.val (k.val⁻¹ * x) = φ.val x)
    {R ε : ℝ} {ρ : CQ → ℝ} (hρ : IsModulatedCutoff mQ R ε ρ)
    (hA : IsNuclearOperator ((M(hρ)).comp A(φ))) :
    hilbertTrace (productTraceClass((⟨(M(hρ)).comp A(φ), hA⟩ : nuclearEndomorphisms W), EQ)) =
      hilbertTrace (⟨((qQ).comp ((M(hρ)).comp JQ)) * (N(φ)).val,
        mul_mem_nuclearEndomorphisms_left _ N(φ)⟩ : nuclearEndomorphisms H) := by
  exact absolutePW_trace_compatibility_of_section («W» := W) («H» := H)
    (absolutePW_rational_isotype 0 h₀) qQ JQ (Θ).starProjection EQ M(hρ) A(φ) N(φ) hA
    (absolutePW_quotient_section (Θ)) (fun x ↦ (spectralConvolution_mkQ (1/2) h₀ hs₂ φ x).symm)
    (fun x hx ↦ absolutePW_rational_projection_preserves_zero ⟨x, hx⟩)
    (absolutePW_radial_convolution_mem φ hrad) (absolutePW_cutoff_mem_trivial R ε ρ hρ)
    (hcompat φ hsupport R ε ρ hρ)

private theorem absolutePW_rational_shift_analysis
    (ψ : ℝ → BruhatCompactSupport CQ) (g : ℝ → CQ) (hlog : ∀ t, logQ (g t) = t)
    (hshift : ∀ t x, (ψ t).val x = (ψ 0).val ((g t)⁻¹ * x))
    {R ε : ℝ} {ρ : CQ → ℝ} (hρ : IsModulatedCutoff mQ R ε ρ)
    (hband : 0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε) :
    ∃ hA : ∀ t, IsNuclearOperator ((M(hρ)).comp A(ψ t)),
      Tendsto (fun t ↦ traceNorm (⟨(M(hρ)).comp A(ψ t), hA t⟩ :
        nuclearEndomorphisms W)) atTop (𝓝 0) :=
  absolutePW_cutoff_shift_trace_decay (F := ℚ) (ψ 0) ψ g hlog hshift
    ρ hρ.measurable hρ.abs_le_one (absolutePW_cutoff_hasCompactSupport hρ)
    (absolutePW_cutoff_convolution_nuclear (ψ 0) hρ hband)

private theorem absolutePW_rational_traces_decay_of_shift_norm
    (hcompat : absolutePW_rational_trace_compatible 0 h₀) (ψ : ℝ → BruhatCompactSupport CQ)
    (hrad : ∀ t (k : CQ₁) x, (ψ t).val (k.val⁻¹ * x) = (ψ t).val x)
    (hsupport : ∀ t, 0 ≤ t → aboveOne(ℚ, ψ t))
    {R ε : ℝ} {ρ : CQ → ℝ} (hρ : IsModulatedCutoff mQ R ε ρ)
    (hA : ∀ t, IsNuclearOperator ((M(hρ)).comp A(ψ t)))
    (hlim : Tendsto (fun t ↦ traceNorm (⟨(M(hρ)).comp A(ψ t), hA t⟩ :
      nuclearEndomorphisms W)) atTop (𝓝 0)) :
    Tendsto (fun t ↦ hilbertTrace (⟨((qQ).comp ((M(hρ)).comp JQ)) * (N(ψ t)).val,
      mul_mem_nuclearEndomorphisms_left _ N(ψ t)⟩ : nuclearEndomorphisms H)) atTop (𝓝 0) := by
  let B (t : ℝ) : nuclearEndomorphisms W := ⟨(M(hρ)).comp A(ψ t), hA t⟩
  refine (absolutePW_trace_mul_tendsto_zero B EQ hlim).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact absolutePW_rational_match_traces hcompat (ψ t) (hsupport t ht) (hrad t) hρ (hA t)

/-- The printed convergence forces the fixed-cutoff quotient trace of the
translated tests to decay along positive translations. -/
private theorem absolutePW_rational_quotient_trace_decay
    (hcompat : absolutePW_rational_trace_compatible 0 h₀) (ψ : ℝ → BruhatCompactSupport CQ)
    (g : ℝ → CQ) (hlog : ∀ t, logQ (g t) = t)
    (hshift : ∀ t x, (ψ t).val x = (ψ 0).val ((g t)⁻¹ * x))
    (hrad : ∀ t (k : CQ₁) x, (ψ t).val (k.val⁻¹ * x) = (ψ t).val x)
    (hsupport : ∀ t, 0 ≤ t → aboveOne(ℚ, ψ t))
    {R ε : ℝ} {ρ : CQ → ℝ} (hρ : IsModulatedCutoff mQ R ε ρ)
    (hε : 0 < R⁻¹ + ε) (hε' : R⁻¹ + ε < R - ε) :
    Tendsto (fun t ↦ hilbertTrace (⟨((qQ).comp ((M(hρ)).comp JQ)) * (N(ψ t)).val,
      mul_mem_nuclearEndomorphisms_left _ N(ψ t)⟩ : nuclearEndomorphisms H)) atTop (𝓝 0) := by
  exact (absolutePW_rational_shift_analysis ψ g hlog hshift hρ ⟨hε, hε'⟩).elim
    (absolutePW_rational_traces_decay_of_shift_norm hcompat ψ hrad hsupport hρ)


private theorem absolutePW_orbit_eq_of_coordinates {X ι : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    (Λ : ι → StrongDual ℂ X) (hdense : Dense (Submodule.span ℂ (Set.range Λ) : Set (StrongDual ℂ X)))
    (U N A : X →L[ℂ] X) (η d : ι → ℂ)
    (hU : ∀ j x, Λ j (U x) = η j * Λ j x)
    (hN : ∀ j x, Λ j (N x) = d j * Λ j x)
    (hA : ∀ j x, Λ j (A x) = η j * d j * Λ j x) : U * N = A := by
  apply ContinuousLinearMap.ext
  intro x
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (U (N x)) = ContinuousLinearMap.apply ℂ ℂ (A x) := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨j, rfl⟩
    change Λ j (U (N x)) = Λ j (A x)
    rw [hU, hN, hA, mul_assoc]
  exact fun L ↦ DFunLike.congr_fun he L

private theorem absolutePW_trivial_phase (x : CQ) (t γ : ℝ) (hx : logQ x = t) :
    ideleClassNormTwist (1 : PontryaginDual CQ) ((γ : ℂ) * Complex.I) x =
      (Real.fourierChar (t * (γ / (2 * Real.pi))) : ℂ) := by
  have he : Real.exp t = ((ideleClassNorm ℚ x).val : ℝ) :=
    (congrArg Real.exp hx).symm.trans (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _)))
  change (((1 : PontryaginDual CQ) x : Circle) : ℂ) *
    ((((ideleClassNorm ℚ x).val : ℝ) : ℂ) ^ ((γ : ℂ) * Complex.I)) = _
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul, ← he, absolutePW_cpow_exp,
    Real.fourierChar_apply]
  congr 1
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [show 2 * Real.pi * (t * (γ / (2 * Real.pi))) = γ * t from by field_simp, Complex.ofReal_mul]
  ring

private theorem absolutePW_cutoff_detects_pairing
    (L : StrongDual ℂ W) (x : W) (hx : L x ≠ 0) :
    ∃ (R ε : ℝ) (ρ : CQ → ℝ) (hρ : IsModulatedCutoff mQ R ε ρ),
      0 < R⁻¹ + ε ∧ R⁻¹ + ε < R - ε ∧ L (modulatedCutoffOperator mQ νQ hρ x) ≠ 0 := by
  obtain ⟨cut, _, hcut, hcutE⟩ := absolutePW_strong_cutoffs νQ
  have ht : Tendsto (fun R ↦ L (cut R x)) atTop (𝓝 (L x)) :=
    (L.continuous.tendsto x).comp (hcut x)
  have hnz := ht.eventually (isOpen_ne.mem_nhds hx)
  obtain ⟨R, hRn, ε, ρ, hρ, hε, hε', hcut_eq⟩ := (hnz.and hcutE).exists
  exact ⟨R, ε, ρ, hρ, hε, hε', fun h ↦ hRn ((congrArg (fun C : W →L[ℂ] W ↦ L (C x)) hcut_eq).trans h)⟩

private theorem absolutePW_jet_ordinal_sep
    (χ : PontryaginDual CQ₁ → PontryaginDual CQ) (hχ1 : χ 1 = 1)
    (j₀ : SpectralLineJetIndex χ (1/2) 2) (h₀ω : j₀.val.1 = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ (j : SpectralLineJetIndex χ (1/2) 2), j ≠ j₀ → j.val.1 = 1 →
      r ≤ dist (j.val.2.1 / (2 * Real.pi)) (j₀.val.2.1 / (2 * Real.pi)) := by
  have hzero (j : SpectralLineJetIndex χ (1/2) 2) (hj : j.val.1 = 1) :
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual CQ))
        ((1 : ℂ) / 2 + (j.val.2.1 : ℂ) * Complex.I)).untop₀.toNat := by
    have hp := Nat.zero_lt_of_lt ((lt_spectralBoundaryMultiplicity _ _ _).mp j.property).1
    change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1))
      (((1/2 : ℝ) : ℂ) + (j.val.2.1 : ℂ) * Complex.I)).untop₀.toNat at hp
    simpa only [hj, hχ1, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hp
  obtain ⟨r, hr, hsep⟩ := absolutePW_zero_isolated _ (hzero j₀ h₀ω)
  refine ⟨r, hr, fun j hj h ↦ hsep j.val.2.1 (fun he ↦ hj ?_) (hzero j h)⟩
  exact Subtype.ext (Prod.ext (h.trans h₀ω.symm) (Prod.ext he
    ((absolutePW_jet_order_zero j).trans (absolutePW_jet_order_zero j₀).symm)))

/-- The fixed-cutoff trace identity fails for at least one radial translated test. -/
private theorem absolutePW_rational_trace_compatible_false :
    ¬ absolutePW_rational_trace_compatible 0 h₀ := by
  classical
  intro hcompat
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 (1 : PontryaginDual CQ)
  have hχ1 : χ 1 = 1 := Function.update_self ..
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω₁
    by_cases h : ω₁ = 1
    · subst ω₁
      rw [hχ1]
      rfl
    · simpa [χ, Function.update_of_ne h] using hχ₀ ω₁
  obtain ⟨γ, hγ⟩ := absolutePW_critical_line_point
  let ι := SpectralLineJetIndex χ (1 / 2) 2
  let j₀ : ι := ⟨(1, γ, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    refine ⟨?_, by norm_num⟩
    change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ 1))
      (((1/2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).untop₀.toNat
    simpa only [hχ1, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hγ⟩
  obtain ⟨_, v, Λ, hBasis, hΛ⟩ := spectralLineMarkushevichBasis (a := (1 / 2 : ℝ)) χ hχ hs
  obtain ⟨σ, ψ, hlog, hshift, hrad, hsupport, hmult⟩ := absolutePW_radial_translates γ
  let g (t : ℝ) := σ (Multiplicative.ofAdd t)
  have hgc : Continuous g := σ.continuous
  let φ : BruhatCompactSupport CQ := ψ 0
  let q := (Θ).mkQL
  let J := (Θ).orthogonal.subtypeL.comp (Θ).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hqJ : ∀ x, q (J x) = x := DFunLike.congr_fun (absolutePW_quotient_section (Θ)).1
  let U (t : ℝ) := q.comp ((τ (g t)).comp J)
  obtain ⟨hUc, hUb⟩ := absolutePW_quotient_translation g hgc hlog
  let N (t : ℝ) : nuclearEndomorphisms H :=
    ⟨S(ψ t), spectralLineConvolution_nuclear (1/2) hs (ψ t)⟩
  let ξ (j : ι) : ℝ := j.val.2.1 / (2 * Real.pi)
  let η (j : ι) := ideleClassNormTwist (χ j.val.1) ((j.val.2.1 : ℂ) * Complex.I)
  let d (j : ι) := ∫ x, φ.val x * η j x ∂μQ
  have hd₀ : d j₀ ≠ 0 := by
    dsimp only [d, η, φ, j₀]
    rwa [hχ1]
  have hcoeff (j : ι) (t : ℝ) (x : H) :
      Λ j ((N t).val x) = η j (g t) * d j * Λ j x :=
    ((absolutePW_jet_eigen j (Λ j) (hΛ j)).2 (ψ t) x).trans
      (congrArg (· * Λ j x) (absolutePW_translated_mellin (hshift t) (η j)))
  have htrans (t : ℝ) (j : ι) (y : H) : Λ j (U t y) = η j (g t) * Λ j y :=
    ((absolutePW_jet_eigen j (Λ j) (hΛ j)).1 (g t) (J y)).trans
      (congrArg (fun z : H ↦ η j (g t) * Λ j z) (hqJ y))
  have hOrbit (t : ℝ) : U t * (N 0).val = (N t).val :=
    absolutePW_orbit_eq_of_coordinates Λ hBasis.2.2.2 (U t) (N 0).val (N t).val
      (fun j ↦ η j (g t)) d (htrans t)
      (fun j ↦ (absolutePW_jet_eigen j (Λ j) (hΛ j)).2 φ) (fun j ↦ hcoeff j t)
  have hnontriv (j : ι) (hj : j.val.1 ≠ 1) : d j = 0 := by
    apply absolutePW_radial_mellin_vanish φ (hrad 0)
    intro h
    apply hj
    rw [← hχ j.val.1]
    ext k
    exact congrArg Subtype.val (h k)
  have hphase (j : ι) (hj : j.val.1 = 1) (t : ℝ) :
      η j (g t) = (Real.fourierChar (t * ξ j) : ℂ) := by
    have he : χ j.val.1 = 1 := (congrArg χ hj).trans hχ1
    exact (congrArg (fun c ↦ ideleClassNormTwist c ((j.val.2.1 : ℂ) * Complex.I) (g t)) he).trans
      (absolutePW_trivial_phase (g t) t j.val.2.1 (hlog t))
  have hD (t : ℝ) (j : ι) (x : H) :
      Λ j (U t ((N 0).val x)) = (Real.fourierChar (t * ξ j) : ℂ) * d j * Λ j x := by
    have h := (congrArg (fun D : H →L[ℂ] H ↦ Λ j (D x)) (hOrbit t)).trans (hcoeff j t x)
    by_cases hj : j.val.1 = 1
    · exact h.trans (congrArg (fun z ↦ z * d j * Λ j x) (hphase j hj t))
    · change Λ j ((U t * (N 0).val) x) = _
      simpa only [hnontriv j hj, mul_zero, zero_mul] using h
  obtain ⟨r, hr, hsep₀⟩ := absolutePW_jet_ordinal_sep χ hχ1 j₀ rfl
  have hsep (j : ι) (hj : j ≠ j₀) : r ≤ dist (ξ j) (ξ j₀) ∨ d j = 0 := by
    by_cases h : j.val.1 = 1
    · exact Or.inl (hsep₀ j hj h)
    · exact Or.inr (hnontriv j h)
  let L := (Λ j₀).comp q
  have hL : L (J (v j₀)) ≠ 0 :=
    ((congrArg (Λ j₀) (hqJ (v j₀))).trans (hBasis.1 j₀)).trans_ne one_ne_zero
  obtain ⟨R, ε, ρ, hρ, hε, hε', hMq⟩ := absolutePW_cutoff_detects_pairing L (J (v j₀)) hL
  let M : W →L[ℂ] W := modulatedCutoffOperator mQ νQ hρ
  let Mq := q.comp (M.comp J)
  apply absolutePW_orbit_trace_not_tendsto_zero v Λ hBasis U hUc
    (show 0 ≤ ‖q‖ * ‖J‖ by positivity) hUb (N 0) Mq ξ d hD j₀ hd₀ hr hsep hMq
  apply (absolutePW_rational_quotient_trace_decay hcompat ψ g hlog hshift hrad hsupport hρ hε hε').congr'
  filter_upwards with t
  exact congrArg hilbertTrace (Subtype.ext
    ((congrArg (fun D : H →L[ℂ] H ↦ Mq * D) (hOrbit t).symm).trans (mul_assoc _ _ _).symm))

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
Use the trivial rational isotype, no finite places, a = 1/2 and s = 2.
As the radial test translates to positive log-norm, its convolution after a fixed
spatial cutoff has trace norm tending to zero. The claimed scalar convergence
would give the same decay for the cut spectral trace. A Schwartz filter in the
translation parameter isolates a certified critical-line ordinate. Its rank-one
trace has constant nonzero modulus for a suitably large cutoff, contradicting
the decay. -/
theorem Printed.absolutePWCondensation_trace_tendsto_false :
    ¬ Printed.absolutePWCondensation_trace_tendsto := fun hall ↦
  absolutePW_rational_trace_compatible_false (absolutePW_rational_trace_compatible_of_printed hall)

end

end

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces at fixed cutoff are asserted to converge to the trace of the
uncompressed cutoff geometric convolution. -/
def Printed.invariantPWCondensation_trace_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (S : Finset V(F)) (a s : ℝ) (hs : 0 ≤ s),
    let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
    letI : CompleteSpace ↥(GeoIsotype(F, hs, ω)) :=
      (instClosedSpectralIsotypeSec2 (F := F) (neg_nonpos.mpr (le_rfl (a := (0 : ℝ))))
        hs ω).completeSpace_coe
    NormOneCharacterUnramifiedOutside ω S →
    Subsingleton (CommRing.Pic ((S : Set V(F)).integer F)) →
    ∀ (φ : BruhatCompactSupport C𝔽(F)), aboveOne(F, φ) →
      ∀ (R ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff (m𝔽(F)) R ε ρ),
        ∃ T : nuclearEndomorphisms GeoIsotype(F, hs, ω),
          T.val = cutoffConv(F, hs, ω, a, hρ, φ) ∧
            Tendsto (fun Λ ↦ hilbertTrace
              (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ)))
              atTop (𝓝 (hilbertTrace T))

section
local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "CQ₁" => (ideleClassNorm ℚ).ker
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hs₂" => (show (0 : ℝ) ≤ 2 from zero_le_two)

/-- The invariant printed trace convergence gives the same rational scalar trace
compatibility as the absolute one: at the rational data the invariant projections
also converge strongly to the isotypic geometric projection and are contractive,
so the fixed-cutoff trace limit is unchanged. -/
private theorem invariantPW_rational_trace_compatible_of_printed
    (h : Printed.invariantPWCondensation_trace_tendsto) :
    absolutePW_rational_trace_compatible 0 h₀ := by
  have e : (1 : PontryaginDual CQ).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : CQ₁ →ₜ* CQ) = 1 := by
    ext k
    rfl
  have h' : absolutePW_rational_trace_compatible (-(0 : ℝ)) (neg_nonpos.mpr h₀) := by
    intro φ hφ R ε ρ hρ
    let I := absolutePW_rational_isotype (-(0 : ℝ)) (neg_nonpos.mpr h₀)
    let : CompleteSpace I := absolutePW_rational_isotype_complete _ _
    let Q := (globalThetaSobolev ℚ (1/2) (neg_nonpos.mpr h₀) hs₂).starProjection
    let P := I.orthogonalProjectionOnto.comp (Q.comp I.subtypeL)
    have hh := h ℚ 1 ∅ (1/2) 2 hs₂
      rational_one_unramifiedOutside_empty rational_empty_picTrivial φ hφ R ε ρ hρ
    obtain ⟨T, ht, hlim⟩ := hh
    let T' : nuclearEndomorphisms I := T
    let PΛ (Λ : ℝ) : I →L[ℂ] I :=
      invariantPWProjection (F := ℚ) (S := ∅) hs₂ (1/2) (1 : PontryaginDual CQ₁) Λ
    have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual CQ₁) ∅ :=
      e ▸ rational_one_unramifiedOutside_empty
    have hP (x : I) : Tendsto (fun Λ ↦ PΛ Λ x) atTop (𝓝 (P x)) :=
      invariantPWProjection_tendsto (F := ℚ) (S := ∅) hs₂ (1/2) (1 : PontryaginDual CQ₁)
        hu rational_empty_picTrivial x
    have hPb : ∀ Λ, ‖PΛ Λ‖ ≤ 1 := by
      intro Λ
      apply ContinuousLinearMap.opNorm_le_bound (PΛ Λ) zero_le_one
      intro x
      rw [one_mul]
      let K := (globalInvariantPWSobolev (F := ℚ) (S := ∅) hs₂ (1/2)
        (1 : PontryaginDual CQ₁) Λ).comap I.subtype
      let : IsClosed (K : Set I) :=
        (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
      exact Submodule.norm_starProjection_apply_le K x
    refine ⟨T', fun x ↦ ?_, tendsto_nhds_unique
      (absolutePWCondensation_trace_tendsto_strong I T' PΛ P hP hPb) hlim⟩
    exact DFunLike.congr_fun ht x
  let P (l : {l : ℝ // l ≤ 0}) := absolutePW_rational_trace_compatible l.val l.property
  have he : (⟨-(0 : ℝ), neg_nonpos.mpr h₀⟩ : {l : ℝ // l ≤ 0}) = ⟨0, h₀⟩ := Subtype.ext neg_zero
  exact (congrArg P he).mp h'

end

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
For the rational data of the absolute scalar counterexample the
only place in S is real. The product region equals the box at every level,
so both scalar limits have the same discrepancy. -/
theorem Printed.invariantPWCondensation_trace_tendsto_false :
    ¬ Printed.invariantPWCondensation_trace_tendsto := fun hall ↦
  absolutePW_rational_trace_compatible_false (invariantPW_rational_trace_compatible_of_printed hall)

local notation "theta0(" F ", " hs ")" => globalThetaSobolev F 0 (le_rfl (a := (0 : ℝ))) hs
local notation "Sₚ(" F ", " p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Paragraph before (11.2.2.1), p. 489.
The raw principal-value range defining the prime quotient is asserted to be
closed in the zero-line theta isotype.
Deviation: Use the equivalent ambient isotypic model at zero twist. -/
def Printed.primeOrbitalSobolevDenominator_closed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F))
    (p : HeightOneSpectrum (𝓞 ℚ)),
    (∀ v ∈ Sₚ(F, p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
    ∀ (s : ℝ) (hs : 0 ≤ s),
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
      IsClosed {x : Wω(F, hs, ω) | ∃ y : theta0(F, hs), y.val ∈ Wω(F, hs, ω) ∧
        (globalThetaSobolevPrincipalValue F (Sₚ(F, p)) 0 hs y).val = x.val}

private theorem rat_placesAbove_eq_singleton (p : V(ℚ)) :
    (finite_nuclearityPlacesAbove (F := ℚ) p).toFinset = {p} := by
  classical
  ext v
  simp only [Set.Finite.mem_toFinset, mem_ofPred_eq, Finset.mem_singleton]
  rfl

/-- A closed range on a closed submodule gives a lower bound for an injective operator. -/
private theorem norm_le_mul_of_closed_isotype_range {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (E H : Submodule ℂ W) (P : H →L[ℂ] H)
    [CompleteSpace H] (hcE : IsClosed (E : Set W)) (hinj : Injective P)
    (hPres : ∀ y : H, y.val ∈ E → (P y).val ∈ E)
    (hclosed : IsClosed {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val}) :
    ∃ K : ℝ≥0, ∀ z : H, z.val ∈ E → ‖z‖ ≤ (K : ℝ) * ‖P z‖ := by
  let D := E.comap H.subtype
  have hD : IsClosed (D : Set H) := hcE.preimage continuous_subtype_val
  let : CompleteSpace D := hD.completeSpace_coe
  let A := H.subtypeL.comp (P.comp D.subtypeL)
  have hA : range A = Subtype.val '' {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val} := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨(P z.val).val, hPres z.val z.property⟩, ⟨z.val, z.property, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, hEq⟩, rfl⟩
      exact ⟨⟨y, hy⟩, hEq⟩
  have hA_closed : IsClosed (range A) := by
    rw [hA]
    exact hcE.isClosedMap_subtype_val _ hclosed
  have hA_inj : Injective A := Subtype.val_injective.comp (hinj.comp Subtype.val_injective)
  obtain ⟨K, hK⟩ := (A.isClosed_range_iff_antilipschitz_of_injective hA_inj).mp hA_closed
  refine ⟨K, fun z hz ↦ ?_⟩
  have hb := hK.le_mul_dist (⟨z, hz⟩ : D) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at hb
  change ‖z‖ ≤ (K : ℝ) * ‖P z‖ at hb
  exact hb

/-- A continuous linear map commuting with a group action that restricts an ambient
action preserves every ambient isotype. -/
private theorem primePV_mem_actionIsotype_of_commute {K E : Type*} [Monoid K] [TopologicalSpace K]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (ρ : K →* (E →L[ℂ] E))
    (ω : PontryaginDual K) (H : Submodule ℂ E) (R : K → H →L[ℂ] H)
    (hR : ∀ k u, (R k u : E) = ρ k u) (P : H →L[ℂ] H) (hP : ∀ k u, P (R k u) = R k (P u))
    (u : H) (hu : (u : E) ∈ actionIsotype ρ ω) : (P u : E) ∈ actionIsotype ρ ω := by
  rw [mem_actionIsotype] at hu ⊢
  intro k
  have hRk : R k u = (ω k : ℂ) • u := Subtype.ext ((hR k u).trans (hu k))
  rw [← hR, ← hP, hRk, map_smul]
  rfl

private theorem primePV_preserves_trivial_isotype
    (S : Finset V(ℚ)) (hs : (0 : ℝ) ≤ 2) (y : theta0(ℚ, hs))
    (hy : y.val ∈ Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))) :
    (globalThetaSobolevPrincipalValue ℚ S 0 hs y).val ∈
      Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ))) := by
  let P := globalThetaSobolevPrincipalValue ℚ S 0 hs
  let R := (exists_globalThetaSobolevAction (F := ℚ) 0 (le_rfl (a := (0 : ℝ))) hs).choose
  have hR := (exists_globalThetaSobolevAction (F := ℚ) 0 (le_rfl (a := (0 : ℝ))) hs).choose_spec.1
  exact primePV_mem_actionIsotype_of_commute _ _ _ (fun k ↦ R k.val)
    (fun k ↦ hR k.val) P (fun k ↦ globalThetaSobolevPrincipalValue_equivariant (F := ℚ) S 0 hs k)
    y hy

private theorem rat_trivial_unramified (w : V(ℚ)) :
    (ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0).IsUnramifiedAt w := by
  have hone : ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) 0 = 1 := by
    ext a
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  rw [hone, HeckeCharacter.isUnramifiedAt_iff]
  simp

private theorem rat_primeOrbital_range_closed (v : V(ℚ)) (hs : (0 : ℝ) ≤ 2)
    (h : Printed.primeOrbitalSobolevDenominator_closed) :
    let E := Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))
    let H := theta0(ℚ, hs)
    let P := globalThetaSobolevPrincipalValue ℚ {v} 0 hs
    IsClosed {x : E | ∃ y : H, y.val ∈ E ∧ (P y).val = x.val} := by
  classical
  intro E H P
  let χ : PontryaginDual C𝔽(ℚ) := 1
  have hclosed := h ℚ χ v (fun w _ ↦ rat_trivial_unramified w) 2 hs
  rw [rat_placesAbove_eq_singleton] at hclosed
  exact hclosed

/-- Paper: Paragraph before (11.2.2.1), p. 489.
Over ℚ, take the trivial norm-one isotype of degree two and the place over 2.
Log-radial exponentials are approximate invariants under the uniformizer
translation. Their prime principal values contradict the norm lower bound
that closed range would imply on this isotype. -/
theorem Printed.primeOrbitalSobolevDenominator_closed_false :
    ¬ Printed.primeOrbitalSobolevDenominator_closed := by
  intro h
  let v : V(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hs : (0 : ℝ) ≤ 2 := by norm_num
  let E := Wω(ℚ, hs, (1 : PontryaginDual C₁(ℚ)))
  let H := theta0(ℚ, hs)
  let P := globalThetaSobolevPrincipalValue ℚ {v} 0 hs
  let : CompleteSpace H := (globalThetaSobolev_closed_complete_separable (F := ℚ) 0
    (le_rfl (a := (0 : ℝ))) hs).2.1
  have hcE := isClosed_actionIsotype
    ((hardySobolevTranslation (ideleClassTamagawaMeasure ℚ) (m𝔽(ℚ))
      0 0 2 (le_rfl (a := (0 : ℝ))) hs).comp (ideleClassNorm ℚ).ker.subtype) (1 : PontryaginDual C₁(ℚ))
  have hinj : Injective P := globalThetaSobolevPrincipalValue_injective {v} 0 hs
  obtain ⟨K, hK⟩ := norm_le_mul_of_closed_isotype_range E H P hcE hinj
    (primePV_preserves_trivial_isotype {v} hs) (rat_primeOrbital_range_closed v hs h)
  obtain ⟨z, hz, hc⟩ := exists_ratPrimePrincipalValue_small_norm v hs K
  exact hc.not_ge (hK z hz)

end RiemannMasullo
