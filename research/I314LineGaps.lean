module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit
import Mathlib.Analysis.Fourier.Inversion
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec4

/-!
# Zero gaps and the width-zero case of I314

For the actual quotient of Theorem 10.3.2.1(1), pp. 453–455, at width zero and
Sobolev exponent two, give upper and lower bounds on the coordinate projection
norm in terms of same-character zero gaps. On each angular component, the zero
blocks isolated by any inverse polynomial in the height are absolutely summable
after any bounded insertion. For a homogeneous test only its complementary
clustered subseries remains. The estimates use the Cauchy Gram kernel and the
weighted divisor count and Mellin decay from §7.4.
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory Set FourierTransform
open scoped NNReal Topology
namespace RiemannMasullo

private theorem lineCauchy_fourier (t : ℝ) :
    (∫ x : ℝ, Complex.exp (((t*x : ℝ) : ℂ)*Complex.I) * (((1+x^2)⁻¹ : ℝ) : ℂ)) =
      (Real.pi : ℂ) * (Real.exp (-|t|) : ℝ) := by
  let f := halfPlaneAbelTest 1 0
  let q (x : ℝ) := (((1 + x ^ 2)⁻¹ : ℝ) : ℂ)
  have hft (x : ℝ) : 𝓕 f x = (Real.pi : ℂ)⁻¹ * q x := by
    change 𝓕 (halfPlaneAbelTest 1 0) x = _
    rw [fourier_halfPlaneAbelTest (by norm_num : (0 : ℝ) < 1) 0 x]
    change ((ProbabilityTheory.cauchyPDFReal 0 (1 : ℝ≥0) x : ℝ) : ℂ) = _
    rw [ProbabilityTheory.cauchyPDFReal_def]
    simp [q, add_comm]
  have hint : Integrable (𝓕 f) := by
    rw [funext hft]
    exact integrable_inv_one_add_sq.ofReal.const_mul _
  let u := t/(2*Real.pi)
  have hfc : Continuous f := by unfold f halfPlaneAbelTest; fun_prop
  have heq := (halfPlaneAbelTest_mem (by norm_num : (0 : ℝ) < 1) 0).1.fourierInv_fourier_eq hint (hfc.continuousAt (x := u))
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul] at heq
  have hphase (x : ℝ) : (-2 * Real.pi * x * -u) = t*x := by
    dsimp [u]
    field_simp [Real.pi_ne_zero]
  change (∫ x : ℝ, Complex.exp (↑(-2*Real.pi*x* -u : ℝ)*Complex.I) • 𝓕 f x) = f u at heq
  simp only [hphase, smul_eq_mul, hft] at heq
  have heF : f u = (Real.exp (-|t|) : ℝ) := by
    change Complex.exp (↑(-(2*Real.pi*1*|u|) : ℝ) + ↑(2*Real.pi*0*u : ℝ) * Complex.I) = _
    rw [Complex.ofReal_exp]
    congr 1
    simp [u, abs_div, abs_mul, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  rw [heF] at heq
  have hfactor : (Real.pi : ℂ)⁻¹ * ∫ x : ℝ, Complex.exp (↑(t*x) * Complex.I) * q x = (Real.exp (-|t|) : ℝ) := by
    rw [← integral_const_mul]
    convert heq using 1
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    ring
  change _ = _ at hfactor
  calc
    _ = (Real.pi : ℂ) * ((Real.pi : ℂ)⁻¹ * ∫ x : ℝ, Complex.exp (↑(t*x) * Complex.I) * q x) := by
      rw [mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    _ = _ := congrArg ((Real.pi : ℂ) * ·) hfactor

open Filter Function Set Topology MeasureTheory IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)


local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation (G := C𝔽) m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
local notation "ν" => (intervalSobolevMeasure μ𝔽 logNorm (-(0:ℝ)) 0 2 true)
local notation "Hrec" => Lp ℂ 2 ν
private def phase (t x : ℝ) := Complex.exp ((t*x:ℝ)*Complex.I)
private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by simp [phase,Complex.norm_exp]
private def wave (ψ : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) := (ψ g : ℂ) * phase t (logNorm g)
private theorem wave_mem (ψ : PontryaginDual C𝔽) (t : ℝ) : MemLp (wave ψ t) 2 ν := by
  have hc : Continuous (wave ψ t) := (continuous_subtype_val.comp ψ.continuous).mul
    ((by unfold phase; fun_prop : Continuous (phase t)).comp (continuous_logModule' m𝔽))
  have h := spectralLineJet_memLp_of_norm_sq (G := C𝔽) m𝔽 hm𝔽 hms𝔽 μ𝔽 2 0 (by norm_num)
    (wave ψ t) hc (fun g ↦ by simp [wave,phase_norm])
  have hmval (g : C𝔽) : m𝔽 g = ideleClassNorm F g := rfl
  simpa only [hmval,intervalSobolevMeasure,ite_true,neg_zero,intervalSobolevDensity,mul_zero,zero_mul,
    Real.exp_zero,max_self,one_mul,logIdeleClassNorm] using h
private def u (ψ : PontryaginDual C𝔽) (t : ℝ) : Hrec := (wave_mem ψ t).toLp _
variable (F) in
private def lineMass : ℝ :=
  let τ := canonicalModulatedHaar m𝔽 hm𝔽
  let _ : τ.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  (Measure.haarScalarFactor μ𝔽 τ : ℝ) * Real.pi
private theorem lineMass_pos : 0 < lineMass F := by
  let τ := canonicalModulatedHaar m𝔽 hm𝔽
  let : τ.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  apply mul_pos _ Real.pi_pos
  exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 τ)
local notation "prof(" d ", " x ")" => phase d x * (((1 + (x : ℝ)^2)⁻¹ : ℝ) : ℂ)
open scoped InnerProductSpace ComplexConjugate
private theorem wave_pair (χ ψ : PontryaginDual C𝔽) (t v : ℝ) :
    ⟪u χ t, u ψ v⟫_ℂ = ∫ g, ((χ g : ℂ)⁻¹ * (ψ g : ℂ)) * prof(v-t,logNorm g) ∂μ𝔽 := by
  rw [MeasureTheory.L2.inner_def]
  have e : (∫ g, inner ℂ (u χ t g) (u ψ v g) ∂ν) =
      ∫ g, inner ℂ (wave χ t g) (wave ψ v g) ∂ν := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (wave_mem χ t),MemLp.coeFn_toLp (wave_mem ψ v)] with g h k
    change (u χ t) g = _ at h
    change (u ψ v) g = _ at k
    rw [h,k]
  rw [e]
  change (∫ g, _ ∂(L2μ'(-(0:ℝ),0,2))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((symmIntervalSobolevDensity_inv_continuous (F := F) (le_refl (0:ℝ)) 2).measurable.ennreal_ofReal)
    (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (symmIntervalSobolevDensity_pos (le_refl (0:ℝ)) 2 _).le)]
  have hp : conj (phase t (logNorm g)) * phase v (logNorm g) = phase (v-t) (logNorm g) := by
    unfold phase
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp [sub_mul]
    ring
  rw [RCLike.inner_apply',wave,wave,map_mul]
  simp only [intervalSobolevDensity,neg_zero,mul_zero,zero_mul,Real.exp_zero,max_self,one_mul,
    show (2:ℝ)/2 = 1 by norm_num,Real.rpow_one,Complex.real_smul]
  rw [← hp]
  have hχ : conj (χ g : ℂ) = (χ g : ℂ)⁻¹ := (Circle.coe_inv_eq_conj _).symm.trans (Circle.coe_inv _)
  rw [hχ]
  ring
private theorem wave_kernel (χ : PontryaginDual C𝔽) (t v : ℝ) :
    ⟪u χ t, u χ v⟫_ℂ = ((lineMass F * Real.exp (-|v-t|) : ℝ) : ℂ) := by
  rw [wave_pair]
  simp_rw [inv_mul_cancel₀ (Circle.coe_ne_zero _),one_mul]
  let τ := canonicalModulatedHaar m𝔽 hm𝔽
  let : τ.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let q := fun x : ℝ ↦ prof(v-t,x)
  have hmp : MeasurePreserving (fun g : C𝔽 ↦ logNorm g) τ volume := sobolev_log_preserving m𝔽 hm𝔽 hms𝔽
  have hc : Continuous q := by unfold q phase; fun_prop (disch := intro x; positivity)
  have he : ∫ g : C𝔽, q (logNorm g) ∂τ = ∫ x : ℝ, q x := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hc.aestronglyMeasurable]
  change (∫ g : C𝔽, q (logNorm g) ∂μ𝔽) = _
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 τ]
  rw [integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,he]
  dsimp only [q]
  rw [show (∫ x : ℝ, prof(v-t,x)) = _ from lineCauchy_fourier (v-t)]
  simp only [lineMass,Complex.ofReal_mul,τ]
  ring
private theorem wave_orth (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {ω η : PontryaginDual C₁} (hne : η ≠ ω) (t v : ℝ) : ⟪u (χ ω) t, u (χ η) v⟫_ℂ = 0 := by
  rw [wave_pair]
  obtain ⟨k,hk⟩ : ∃ k : C₁, χ ω k.val ≠ χ η k.val := by
    by_contra! he
    apply hne
    rw [← hχ η, ← hχ ω]
    exact DFunLike.ext _ _ fun k ↦ (he k).symm
  apply stripProfile_orthogonality μ𝔽 _ _ k.val hk
  intro x
  change prof(v-t,Real.log ((ideleClassNorm F (k.val*x)).val : ℝ)) = _
  rw [map_mul,k.property,one_mul]
private def atten (h : ℝ) := Real.exp (-h)
private def edge (h : ℝ) := 1 - (atten h)^2
private def kernel (d : ℝ) := Real.exp (-|d|)
private theorem edge_pos {h : ℝ} (hh : 0 < h) : 0 < edge h := by
  have hlt : atten h < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hh)
  have hpos : 0 < atten h := Real.exp_pos _
  dsimp [edge]
  nlinarith [sq_nonneg (1-atten h),mul_pos (sub_pos.mpr hlt) (by linarith : 0 < 1 + atten h)]
private theorem kernel_difference {h d : ℝ} (hh : 0 < h) (hd : h ≤ |d|) :
    (1 + (atten h)^2) * kernel d - atten h * (kernel (d+h) + kernel (d-h)) = 0 := by
  unfold atten kernel
  rcases le_abs.mp hd with hd|hd
  · rw [abs_of_nonneg (by linarith : 0 ≤ d),abs_of_nonneg (by linarith : 0 ≤ d+h),
      abs_of_nonneg (by linarith : 0 ≤ d-h),neg_add,Real.exp_add,neg_sub,
      show h - d = -d+h by ring,Real.exp_add]
    have hcan : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    linear_combination -Real.exp (-d)*hcan
  · rw [abs_of_nonpos (by linarith : d ≤ 0),abs_of_nonpos (by linarith : d+h ≤ 0),
      abs_of_nonpos (by linarith : d-h ≤ 0)]
    simp only [neg_neg,Real.exp_add,sub_eq_add_neg]
    have hcan : Real.exp (-h) * Real.exp h = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
    linear_combination -Real.exp d*hcan
private def guard (ψ : PontryaginDual C𝔽) (t h : ℝ) : Hrec :=
  ((1 + (atten h)^2 : ℝ) : ℂ) • u ψ t - (atten h : ℂ) • (u ψ (t-h) + u ψ (t+h))
private theorem guard_outside (ψ : PontryaginDual C𝔽) {h : ℝ} (hh : 0 < h) (t v : ℝ)
    (hd : h ≤ |v-t|) : ⟪guard ψ t h,u ψ v⟫_ℂ = 0 := by
  simp only [guard,inner_sub_left,inner_smul_left,inner_add_left,Complex.conj_ofReal,wave_kernel]
  have k := kernel_difference hh hd
  unfold kernel at k
  rw [show v-(t-h) = v-t+h by ring,show v-(t+h) = v-t-h by ring]
  push_cast
  exact_mod_cast (by linear_combination lineMass F * k :
    (1+atten h ^2)*(lineMass F*Real.exp (-|v-t|))-atten h*(lineMass F*Real.exp (-|v-t+h|)+lineMass F*Real.exp (-|v-t-h|))=0)
private theorem guard_center (ψ : PontryaginDual C𝔽) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ⟪guard ψ t h,u ψ t⟫_ℂ = ((lineMass F * edge h : ℝ) : ℂ) := by
  simp only [guard,inner_sub_left,inner_smul_left,inner_add_left,Complex.conj_ofReal,wave_kernel]
  simp only [sub_self,abs_zero,neg_zero,Real.exp_zero,mul_one,sub_sub_cancel,sub_add_cancel_left,
    abs_neg,abs_of_pos hh,edge,atten,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_add,
    Complex.ofReal_one,Complex.ofReal_pow]
  ring
private theorem guard_sq (ψ : PontryaginDual C𝔽) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ‖guard ψ t h‖^2 = (1+(atten h)^2)*(lineMass F*edge h) := by
  have hself : ⟪guard ψ t h,guard ψ t h⟫_ℂ = ((1+atten h ^2 : ℝ):ℂ) * ((lineMass F*edge h : ℝ):ℂ) := by
    conv_lhs => rhs; unfold guard
    rw [inner_sub_right,inner_smul_right,inner_smul_right,inner_add_right,guard_center ψ hh,
      guard_outside ψ hh t (t-h) (by simp [abs_of_pos hh]),
      guard_outside ψ hh t (t+h) (by simp [abs_of_pos hh])]
    simp
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hself
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_pow,Complex.ofReal_mul] using hself
private theorem wave_sq (ψ : PontryaginDual C𝔽) (t : ℝ) : ‖u ψ t‖^2 = lineMass F := by
  have e := wave_kernel ψ t t
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at e
  simp only [sub_self,abs_zero,neg_zero,Real.exp_zero,mul_one] at e
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_pow] using e
local notation "J(" χ ", " a ")" => SpectralStripJetIndex (F := F) χ a 0 2
local notation "Q₂(" a ")" => spectralSobolevQuotient F a (show -(0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 2 by norm_num)
local notation "D₂(" a ")" => spectralSobolevDualEmbedding F a (show -(0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 2 by norm_num)
local notation "jetVec(" χ ", " j ")" => (spectralStripJet_memLp χ (le_refl (0:ℝ)) (show (0:ℝ) ≤ 2 by norm_num) j).toLp _
private theorem line_indices (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ} (j : J(χ,a)) :
    j.val.2.1 = 0 ∧ j.val.2.2.2 = 0 := by
  have h := (j.mem_strip_order_pos (le_refl (0:ℝ))).1
  have hb : j.val.2.1 = 0 := by simpa only [neg_zero,Set.Icc_self,Set.mem_singleton_iff] using h
  refine ⟨hb,?_⟩
  have hj := j.property
  simp only [spectralStripMultiplicity,hb,neg_zero,lt_self_iff_false,and_self,ite_false,
    or_self,ite_true] at hj
  have hn := ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2
  have : (j.val.2.2.2:ℝ) < 1 := by linarith
  exact Nat.lt_one_iff.mp (by exact_mod_cast this)
private theorem line_realization (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ} (j : J(χ,a)) :
    jetVec(χ,j) = u (χ j.val.1) j.val.2.2.1 := by
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ (le_refl (0:ℝ)) (by norm_num : (0:ℝ) ≤ 2) j),
    MemLp.coeFn_toLp (wave_mem (χ j.val.1) j.val.2.2.1)] with g h k
  change (jetVec(χ,j)) g = _ at h
  change u (χ j.val.1) j.val.2.2.1 g = _ at k
  rw [h,k,stripProfile_jet,(line_indices χ j).1,(line_indices χ j).2]
  simp only [Complex.ofReal_zero,zero_add,pow_zero,mul_one,wave,phase,Complex.ofReal_mul]
  congr 2
  ring
private theorem line_guard_bound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (i : J(χ,a)) {h : ℝ} (hh : 0 < h)
    (hgap : ∀ j : J(χ,a), j ≠ i → j.val.1 = i.val.1 → h ≤ |j.val.2.2.1-i.val.2.2.1|) :
    ‖x i‖ * ‖L i‖ ≤ Real.sqrt ((1 + atten h ^2)/edge h) := by
  let C := lineMass F
  let g := guard (χ i.val.1) i.val.2.2.1 h
  have hC : 0 < C := lineMass_pos
  have hd := edge_pos hh
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a (show -(0:ℝ) ≤ 0 by norm_num)
    (show (0:ℝ) ≤ 2 by norm_num)).1
  have hn (f : StrongDual ℂ Q₂(a)) : ‖D₂(a) f‖ = ‖f‖ := by
    simpa only [map_zero,dist_eq_norm,sub_zero] using hD.dist_eq f 0
  let D : StrongDual ℂ Q₂(a) →ₗᵢ[ℂ] Hrec := ⟨D₂(a),hn⟩
  have eqF : (innerSL ℂ g).comp D.toContinuousLinearMap =
      ((C*edge h : ℝ) : ℂ) • ContinuousLinearMap.apply ℂ ℂ (x i) := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨j,rfl⟩
    change ⟪g,D₂(a) (L j)⟫_ℂ = ((C*edge h : ℝ) : ℂ) * L j (x i)
    rw [hj,line_realization]
    by_cases he : j = i
    · subst j; rw [hb.1,mul_one]; exact guard_center _ hh _
    rw [hb.2.1 _ _ (Ne.symm he),mul_zero]
    by_cases hω : j.val.1 = i.val.1
    · rw [hω]; exact guard_outside _ hh _ _ (hgap j he hω)
    · simp only [g,guard,inner_sub_left,inner_smul_left,inner_add_left,wave_orth χ hχ hω,
        mul_zero,add_zero,sub_zero]
  obtain ⟨f,hf,he⟩ := exists_dual_vector'' ℂ (x i)
  have p := DFunLike.congr_fun eqF f
  change ⟪g,D₂(a) f⟫_ℂ = ((C*edge h : ℝ) : ℂ) * f (x i) at p
  have bound := norm_inner_le_norm (𝕜 := ℂ) g (D₂(a) f)
  rw [p,he,RCLike.ofReal_eq_complex_ofReal,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC.le hd.le),Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),hn] at bound
  have b := bound.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left hf (norm_nonneg g)) (mul_one _))
  have bg := guard_sq (χ i.val.1) hh i.val.2.2.1
  change ‖g‖^2 = (1+atten h ^2)*(C*edge h) at bg
  have bl : ‖L i‖^2 = C := by rw [← hn,hj,line_realization,wave_sq]
  have b2 := sq_le_sq' (by linarith [norm_nonneg g, mul_nonneg (mul_nonneg hC.le hd.le) (norm_nonneg (x i))] :
    -‖g‖ ≤ C * edge h * ‖x i‖) b
  rw [bg,mul_pow,mul_pow] at b2
  have b3 : ‖x i‖^2 * (C*edge h) ≤ 1+atten h ^2 := by
    apply (le_of_mul_le_mul_right _ (mul_pos hC hd))
    nlinarith only [b2]
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ hd).2
  rw [mul_pow,bl]
  nlinarith only [b3]
local notation "A₂(" a ", " φ ")" => spectralConvolution (F := F) a (show -(0:ℝ) ≤ 0 by norm_num) (show (0:ℝ) ≤ 2 by norm_num) φ
local notation "symbol(" φ ", " ψ ", " t ")" => nuclearityTestMellin (F := F) ψ φ ((t : ℂ)*Complex.I)
local notation "freq(" j ")" => (j).val.2.2.1
local notation "ang(" j ")" => (j).val.1
private theorem line_multiplier (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) (L : J(χ,a) → StrongDual ℂ Q₂(a))
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (φ : BruhatCompactSupport C𝔽)
    (i : J(χ,a)) (v : Q₂(a)) : L i (A₂(a,φ) v) = symbol(φ,χ ang(i),freq(i)) * L i v := by
  let z : {z : PontryaginDual C₁ × ℝ × ℝ // z.2.1 ∈ Icc (-(0:ℝ)) 0 ∧
      0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) ((a+z.2.1:ℝ)+(z.2.2:ℂ)*Complex.I)} :=
    ⟨(ang(i),i.val.2.1,freq(i)),i.mem_strip_order_pos le_rfl⟩
  let m : Fin (spectralStripMultiplicity 0 2 i.val.2.1 (meromorphicOrderAt (continuedCompletedHeckeL (χ ang(i)))
      ((a+i.val.2.1:ℝ)+(freq(i):ℂ)*Complex.I)).untop₀.toNat) := ⟨_,i.property⟩
  have hh := spectralStripConvolution_jet_top (F := F) a (le_refl (0:ℝ)) (by norm_num : (1:ℝ)<2) χ L hj φ z m v
    (fun k hk ↦ False.elim (by have he := (line_indices χ i).2; change k.val < i.val.2.2.2 at hk; omega))
  change L i (A₂(a,φ) v) = _ * L i v at hh
  rw [hh,(spectralConvolution_mellin_integrable _ _ _).2]
  dsimp [z]
  rw [(line_indices χ i).1]
  simp only [Complex.ofReal_zero,zero_add,nuclearityTestMellin]
/-- At width zero and Sobolev exponent two, this bound depends only on the local
isolation radius and the Mellin value of the test at the given surviving zero. -/
theorem spectralLine_compactInsertion_gap_bound (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (φ : BruhatCompactSupport C𝔽)
    (U : Q₂(a) →L[ℂ] Q₂(a)) (i : J(χ,a)) {h : ℝ} (hh : 0 < h)
    (hgap : ∀ j : J(χ,a), j ≠ i → ang(j) = ang(i) → h ≤ |freq(j)-freq(i)|) :
    ‖L i (A₂(a,φ) (U (x i)))‖ ≤
      ‖symbol(φ,χ ang(i),freq(i))‖ * ‖U‖ * Real.sqrt ((1 + Real.exp (-h)^2)/(1 - Real.exp (-h)^2)) := by
  rw [line_multiplier χ a L hj φ,norm_mul,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖L i‖ * (‖U‖ * ‖x i‖) := ((L i).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (U.le_opNorm _) (norm_nonneg _))
    _ = ‖U‖ * (‖x i‖ * ‖L i‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (line_guard_bound χ hχ a x L hb hj i hh hgap) (norm_nonneg _)
/-- A second zero on the same component gives a lower bound of the same inverse
square-root order in the gap. -/
theorem spectralLine_projectionNorm_nearby_lower (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (i j : J(χ,a)) (hne : i ≠ j)
    (hω : ang(j) = ang(i)) :
    1 ≤ (‖x i‖ * ‖L i‖)^2 * (1 - Real.exp (-|freq(j)-freq(i)|)^2) := by
  let p := Real.exp (-|freq(j)-freq(i)|)
  let f : StrongDual ℂ Q₂(a) := L i - (p:ℂ) • L j
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a (show -(0:ℝ) ≤ 0 by norm_num)
    (show (0:ℝ) ≤ 2 by norm_num)).1
  have hn (l : StrongDual ℂ Q₂(a)) : ‖D₂(a) l‖ = ‖l‖ := by
    simpa only [map_zero,dist_eq_norm,sub_zero] using hD.dist_eq l 0
  have hp : 0 < p := Real.exp_pos _
  have hsq : ‖f‖^2 = lineMass F * (1-p^2) := by
    rw [← hn]
    simp only [f,map_sub,map_smul]
    rw [hj i,hj j,line_realization χ i,line_realization χ j,hω]
    rw [norm_sub_sq (𝕜 := ℂ),inner_smul_right,wave_kernel,wave_sq,norm_smul,mul_pow,wave_sq]
    change lineMass F - 2 * ((p:ℂ)*((lineMass F*p:ℝ):ℂ)).re + ‖(p:ℂ)‖^2*lineMass F = _
    rw [← Complex.ofReal_mul,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    ring
  have hl : ‖L i‖^2 = lineMass F := by rw [← hn,hj,line_realization,wave_sq]
  have he : f (x i) = 1 := by simp [f,hb.1,hb.2.1 _ _ hne]
  have h₁ := f.le_opNorm (x i)
  rw [he,norm_one] at h₁
  have h₂ := sq_le_sq' (by nlinarith [mul_nonneg (norm_nonneg f) (norm_nonneg (x i))] :
    -(‖f‖ * ‖x i‖) ≤ 1) h₁
  rw [one_pow,mul_pow,hsq] at h₂
  rw [mul_pow,hl]
  nlinarith only [h₂]
private theorem guard_ratio_le {h : ℝ} (hh : 0 < h) :
    Real.sqrt ((1 + Real.exp (-h)^2)/(1 - Real.exp (-h)^2)) ≤ 1 + 1/h := by
  have hd := edge_pos hh
  change 0 < 1 - Real.exp (-h)^2 at hd
  have hpos : 0 < Real.exp (-h)^2 := by positivity
  have ec : Real.exp (-h)^2 * Real.exp (2*h) = 1 := by
    rw [sq, mul_assoc, ← Real.exp_add, ← Real.exp_add, show -h+(-h+2*h) = 0 by ring,Real.exp_zero]
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*h)) hpos.le
  rw [ec] at he
  have h₁ : (1 + Real.exp (-h)^2)/(1 - Real.exp (-h)^2) ≤ 1 + 1/h := by
    apply (div_le_iff₀ hd).2
    apply (le_of_mul_le_mul_left _ hh)
    field_simp [hh.ne']
    nlinarith only [he]
  have h₂ : 1 ≤ 1 + 1/h := le_add_of_nonneg_right (by positivity)
  exact (Real.sqrt_le_sqrt h₁).trans ((Real.sqrt_le_iff).mpr ⟨by linarith,by nlinarith [h₂]⟩)
local notation "ordZ(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
private theorem weighted_divisor (ψ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽) (a : ℝ) (n : ℕ) :
    Summable (fun z : {r : ℂ // 0 < ordZ(ψ,r)} ↦ (1+|z.val.im|)^n *
      ‖((ordZ(ψ,z.val):ℤ):ℂ)*nuclearityTestMellin ψ φ (z.val-(a:ℂ))‖) := by
  let Z := {r : ℂ // 0 < ordZ(ψ,r)}
  have hstrip (z : Z) := spectralNuclearity_trace_zero_strip ψ z.property
  let e (z : Z) : {w : ℂ // 0 < ordZ(ψ,w) ∧ |w.re-1/2| < 1} := ⟨z.val,z.property,by
    obtain ⟨hl,hu⟩ := hstrip z; exact abs_lt.mpr ⟨by linarith,by linarith⟩⟩
  have he : Injective e := fun _ _ hh ↦ Subtype.ext
    (congrArg (fun r : {w : ℂ // 0 < ordZ(ψ,w) ∧ |w.re-1/2| < 1} ↦ r.val) hh)
  have hn := (spectralNuclearity_trace_zero_count ψ 1).comp_injective he
  have hm (z : Z) : (1:ℝ) ≤ (ordZ(ψ,z.val):ℝ) := by exact_mod_cast (show (1:ℤ) ≤ _ from z.property)
  obtain ⟨C,hC,hf⟩ := spectralNuclearity_trace_vertical_decay ψ φ (-a) (1-a) (by linarith) (n+2) (by omega)
  let f (z : Z) := ((1+|z.val.im| : ℝ):ℂ)^n * nuclearityTestMellin ψ φ (z.val-(a:ℂ))
  have h := spectralNuclearity_trace_summable_of_decay (ι := Z) (fun z ↦ z.val.im)
    (fun z ↦ (ordZ(ψ,z.val):ℝ)) hm hn f (2^n*C) (by positivity) (by
      have ht : ∀ᶠ t : ℝ in comap abs atTop, 1 ≤ |t| := (tendsto_comap.eventually (eventually_ge_atTop 1))
      filter_upwards [hf,ht] with t hMt ht z hz
      have h₁ : (z.val - (a:ℂ)).re ∈ Icc (-a) (1-a) := by
        obtain ⟨hl,hu⟩ := hstrip z
        simp only [Complex.sub_re,Complex.ofReal_re,mem_Icc]
        constructor <;> linarith
      have hM := hMt _ h₁
      have him : (z.val-(a:ℂ)).im = t := by simpa using hz
      rw [← him,Complex.re_add_im,him] at hM
      have hpos : 0 < |t| := by linarith
      have hpow : (1+|t|)^n ≤ 2^n * |t|^n := by rw [← mul_pow]; gcongr; linarith
      simp only [f,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        hz,abs_of_nonneg (by positivity : 0 ≤ 1+|t|)]
      calc
        _ ≤ (2^n * |t|^n) * (C / |t|^(n+2)) := mul_le_mul hpow hM (norm_nonneg _) (by positivity)
        _ = 2^n*C / |t|^2 := by rw [pow_add]; field_simp [hpos.ne'])
  apply h.congr
  intro z
  simp only [f,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1+|z.val.im|),Complex.norm_intCast,
    abs_of_nonneg ((zero_le_one: (0:ℝ)≤1).trans (hm z))]
  ring
/-- Every fixed component has absolutely summable blocks on its polynomially
isolated sites for every Bruhat test and every bounded insertion. -/
theorem spectralLine_polynomiallyIsolatedBlocks_summable (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (φ : BruhatCompactSupport C𝔽)
    (U : Q₂(a) →L[ℂ] Q₂(a)) (ω : PontryaginDual C₁) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    let rad (i : J(χ,a)) := c / (1+|freq(i)|)^n
    let S := {i : J(χ,a) // ang(i) = ω ∧
      ∀ j : J(χ,a), j ≠ i → ang(j) = ang(i) → rad i ≤ |freq(j)-freq(i)|}
    Summable (fun i : S ↦ ‖L i.val (A₂(a,φ) (U (x i.val)))‖) := by
  intro rad S
  let ord (z : ℂ) := MeromorphicOn.divisor (continuedCompletedHeckeL (χ ω)) univ z
  let Z := {z : ℂ // 0 < ord z}
  let z (i : S) := (a:ℂ) + (freq(i.val):ℂ)*Complex.I
  have ho (i : S) : 0 < ord (z i) := by
    rw [show ord (z i) = (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (z i)).untop₀ from
      MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn (mem_univ _)]
    have hi := i.val.property
    rw [spectralStripMultiplicity_boundary (le_refl (0:ℝ)) (Or.inr (line_indices χ i.val).1)] at hi
    have hk := ((lt_spectralBoundaryMultiplicity _ _ _).mp hi).1
    rw [(line_indices χ i.val).1, add_zero, i.property.1] at hk
    change i.val.val.2.2.2 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (z i)).untop₀.toNat at hk
    omega
  let e (i : S) : Z := ⟨z i,ho i⟩
  have he : Injective e := by
    intro i j heq
    have him := congrArg (fun s : Z ↦ s.val.im) heq
    change (z i).im = (z j).im at him
    simp only [z,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at him
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (i.property.1.trans j.property.1.symm) (Prod.ext
      ((line_indices χ i.val).1.trans (line_indices χ j.val).1.symm)
      (Prod.ext him ((line_indices χ i.val).2.trans (line_indices χ j.val).2.symm)))
  have hm := (weighted_divisor (χ ω) φ a n).comp_injective he
  have hs : Summable (fun i : S ↦ (1+|freq(i.val)|)^n * ‖symbol(φ,χ ω,freq(i.val))‖) := by
    apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ hm
    intro i
    change _ ≤ (1+|(z i).im|)^n * ‖((ord (z i):ℤ):ℂ)*nuclearityTestMellin (χ ω) φ (z i-(a:ℂ))‖
    rw [show z i-(a:ℂ) = (freq(i.val):ℂ)*Complex.I by dsimp only [z]; ring,norm_mul,Complex.norm_intCast]
    simp only [z,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add] at *
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hp : (1:ℝ) ≤ (ord (z i):ℝ) := by exact_mod_cast (show (1:ℤ) ≤ _ from ho i)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (ord (z i):ℝ))]
    exact le_mul_of_one_le_left (norm_nonneg _) hp
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _
    ((hs.mul_right ‖U‖).mul_right (1+1/c))
  intro i
  have hrad : 0 < rad i.val := by dsimp [rad]; positivity
  have hg := spectralLine_compactInsertion_gap_bound χ hχ a x L hb hj φ U i.val hrad i.property.2
  rw [i.property.1] at hg
  have ht : 1 ≤ (1+|freq(i.val)|)^n := one_le_pow₀ (by linarith [abs_nonneg (freq(i.val))])
  have hr : Real.sqrt ((1+Real.exp (-(rad i.val))^2)/(1-Real.exp (-(rad i.val))^2)) ≤
      (1+|freq(i.val)|)^n * (1+1/c) := by
    apply (guard_ratio_le hrad).trans
    dsimp only [rad]
    rw [div_div_eq_mul_div]
    field_simp [hc.ne']
    nlinarith only [ht,mul_nonneg hc.le (sub_nonneg.mpr ht)]
  exact hg.trans ((mul_le_mul_of_nonneg_left hr (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring))
/-- On a homogeneous test, the entire width-zero, exponent-two block condition
reduces to the sites in its component having a neighbor closer than the chosen
polynomial isolation radius. -/
private theorem spectralLine_homogeneous_summable_iff_clustered (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (φ : BruhatCompactSupport C𝔽)
    (U : Q₂(a) →L[ℂ] Q₂(a)) (ω : PontryaginDual C₁)
    (hφ : ∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (ω k : ℂ)*φ.val g)
    (n : ℕ) {c : ℝ} (hc : 0 < c) :
    let rad (i : J(χ,a)) := c / (1+|freq(i)|)^n
    let bad := {i : J(χ,a) | ang(i) = ω ∧
      ∃ j : J(χ,a), j ≠ i ∧ ang(j) = ang(i) ∧ |freq(j)-freq(i)| < rad i}
    let term (i : J(χ,a)) := L i (A₂(a,φ) (U (x i)))
    Summable term ↔ Summable (fun i : bad ↦ term i.val) := by
  classical
  intro rad bad term
  let good := {i : J(χ,a) | ang(i) = ω ∧
    ∀ j : J(χ,a), j ≠ i → ang(j) = ang(i) → rad i ≤ |freq(j)-freq(i)|}
  have hgood : Summable (fun i : good ↦ term i.val) :=
    (spectralLine_polynomiallyIsolatedBlocks_summable χ hχ a x L hb hj φ U ω n hc).of_norm
  have hoff (i : J(χ,a)) (h : ang(i) ≠ ω) : term i = 0 := by
    change L i (A₂(a,φ) _) = _
    rw [line_multiplier χ a L hj φ]
    have hm := spectralIsotype_mellin_eq_zero χ hχ h φ hφ ((freq(i):ℂ)*Complex.I)
    rw [(spectralConvolution_mellin_integrable _ _ _).2] at hm
    exact mul_eq_zero_of_left hm _
  let e (i : bad) : ↥(goodᶜ) := ⟨i.val,by
    rintro ⟨_,h⟩
    obtain ⟨j,hne,hw,hlt⟩ := i.property.2
    exact (not_le.mpr hlt) (h j hne hw)⟩
  have he : Injective e := fun _ _ eq ↦ Subtype.ext (congrArg (fun r : ↥(goodᶜ) ↦ r.val) eq)
  have hz (i : ↥(goodᶜ)) (hi : i ∉ Set.range e) : term i.val = 0 := by
    apply hoff
    intro hω
    have hng := i.property
    change ¬(_ ∧ _) at hng
    push Not at hng
    obtain ⟨j,hne,hw,hlt⟩ := hng hω
    exact hi ⟨⟨i.val,hω,j,hne,hw,hlt⟩,rfl⟩
  exact hgood.summable_compl_iff.symm.trans (he.summable_iff hz).symm
local notation "Z₂(" χ ", " a ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-(0:ℝ)) 0 ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1))
    ((a+z.2.1:ℝ)+(z.2.2:ℂ)*Complex.I)}
local notation "N₂(" χ ", " a ", " z ")" => spectralStripMultiplicity 0 2 (z).val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (χ (z).val.1)) ((a+(z).val.2.1:ℝ)+((z).val.2.2:ℂ)*Complex.I)).untop₀.toNat
private theorem line_block_sum_iff (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a : ℝ)
    (term : J(χ,a) → ℂ) :
    let jet (z : Z₂(χ,a)) (m : Fin (N₂(χ,a,z))) : J(χ,a) := ⟨(z.val.1,z.val.2.1,z.val.2.2,m.val),m.isLt⟩
    Summable (fun z : Z₂(χ,a) ↦ ∑ m, term (jet z m)) ↔ Summable term := by
  intro jet
  let e (i : J(χ,a)) : Z₂(χ,a) := ⟨(ang(i),i.val.2.1,freq(i)),i.mem_strip_order_pos le_rfl⟩
  have he : Injective e := by
    intro i j heq
    have e₁ := congrArg (fun z : Z₂(χ,a) ↦ z.val.1) heq
    have e₂ := congrArg (fun z : Z₂(χ,a) ↦ z.val.2.1) heq
    have e₃ := congrArg (fun z : Z₂(χ,a) ↦ z.val.2.2) heq
    exact Subtype.ext (Prod.ext e₁ (Prod.ext e₂ (Prod.ext e₃ ((line_indices χ i).2.trans (line_indices χ j).2.symm))))
  have hzero (z : Z₂(χ,a)) (hz : z ∉ range e) : ∑ m, term (jet z m) = 0 := by
    apply Finset.sum_eq_zero
    intro m _
    exact (hz ⟨jet z m,rfl⟩).elim
  have hval (i : J(χ,a)) : ∑ m, term (jet (e i) m) = term i := by
    let k : Fin (N₂(χ,a,e i)) := ⟨i.val.2.2.2,i.property⟩
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    intro m _ hm
    exact (hm (Fin.ext (((line_indices χ (jet (e i) m)).2).trans ((line_indices χ i).2).symm))).elim
  have e₀ := he.summable_iff hzero
  simpa only [comp_def,hval] using e₀.symm
/-- The full zero-block sum in #7241 for a homogeneous test at this width and
exponent is equivalent to the sum restricted to polynomially clustered sites
in the active angular component. -/
theorem spectralLine_homogeneous_blocks_iff_clustered (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (a : ℝ) (x : J(χ,a) → Q₂(a))
    (L : J(χ,a) → StrongDual ℂ Q₂(a)) (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, D₂(a) (L j) = jetVec(χ,j)) (φ : BruhatCompactSupport C𝔽)
    (U : Q₂(a) →L[ℂ] Q₂(a)) (ω : PontryaginDual C₁)
    (hφ : ∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (ω k : ℂ)*φ.val g)
    (n : ℕ) {c : ℝ} (hc : 0 < c) :
    let rad (i : J(χ,a)) := c / (1+|freq(i)|)^n
    let bad := {i : J(χ,a) | ang(i) = ω ∧
      ∃ j : J(χ,a), j ≠ i ∧ ang(j) = ang(i) ∧ |freq(j)-freq(i)| < rad i}
    let term (i : J(χ,a)) := L i (A₂(a,φ) (U (x i)))
    let jet (z : Z₂(χ,a)) (m : Fin (N₂(χ,a,z))) : J(χ,a) := ⟨(z.val.1,z.val.2.1,z.val.2.2,m.val),m.isLt⟩
    Summable (fun z : Z₂(χ,a) ↦ ∑ m, term (jet z m)) ↔ Summable (fun i : bad ↦ term i.val) := by
  intro rad bad term jet
  exact (line_block_sum_iff χ a term).trans (spectralLine_homogeneous_summable_iff_clustered χ hχ a x L hb hj φ U ω hφ n hc)

#print axioms spectralLine_compactInsertion_gap_bound
#print axioms spectralLine_projectionNorm_nearby_lower
#print axioms spectralLine_polynomiallyIsolatedBlocks_summable
#print axioms spectralLine_homogeneous_blocks_iff_clustered

end RiemannMasullo
