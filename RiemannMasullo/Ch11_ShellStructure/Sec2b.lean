module

public import RiemannMasullo.Ch11_ShellStructure.Sec2a
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppA_AlgebraicNT.Sec1
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import RiemannMasullo.Ch09_HardySobolev.Sec3

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b

/-! # Sobolev Paley–Wiener levels and orbital nuclearity

Masullo, §§11.2.1–11.2.2, pp. 487–491. The stage parameter lists the finite
places, with every archimedean place included implicitly.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "mₛ(" S ")" =>
  (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "logNorm(" m ")" => (fun g ↦ Real.log (((m) g).val : ℝ))
local notation "h₀" => (le_rfl (a := (0 : ℝ)))
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) 0 0 s
local notation "Wω(" hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 _ h₀ hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "ω(" χ ")" =>
  (χ : PontryaginDual C𝔽).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "A(" hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 0 0 _ h₀ hs φ
local notation "supportedAboveOne(" φ ")" =>
  (tsupport (φ : BruhatCompactSupport C𝔽).val ⊆ {g | 1 ≤ ((m𝔽 g).val : ℝ)})

section Levels

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ} (hs : 0 ≤ s)

-- Use the base [-0, 0] of §10.4 for its geometric projection and cutoff.
local notation "hGeo" => (neg_nonpos.mpr h₀ |>.trans h₀)
local notation "GeoIsotype(" ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs).comp
    (ideleClassNorm F).ker.subtype) ω
local notation "geoAction(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs φ

local notation "Zₛ" => sAdelePolarSubspace F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "band(" K ")" =>
  ({f : Zₛ | f.val ∈ sLocalPWTests (S := S) (T := S) le_rfl K} : Set Zₛ)
local notation "localWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight (mₛ(S)) a (sLocalHomogeneousAdelicThetaLinearMap F S ω (f : Zₛ).val)
local notation "globalWeightedTheta(" a ", " ω ", " f ")" =>
  modulationWeight m𝔽 a (homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S (f : Zₛ).val))

local notation "localWMeasure" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logNorm(mₛ(S)) g)))
local notation "globalWMeasure" => (μ𝔽).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-(0 : ℝ)) 0 s (logNorm(m𝔽) g)))
local notation "GeoW" => Lp ℂ 2 globalWMeasure
local notation "LocalW" => Lp ℂ 2 localWMeasure

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Local polar-free tests yield Sobolev vectors at positive twist.
Deviation: Use the positive range of the local Sobolev embedding from §10.1. -/
theorem sLocalPWTheta_memLp {a : ℝ} (_ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    MemLp (localWeightedTheta(a, ω, f)) 2 localWMeasure := by
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  let μ := sLocalQuotientTamagawaMeasure F S
  let r (g : SIdeleQuotient F S) : ℝ := (mₛ(S) g).val
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f.val
  let t := max s 0
  let b := a / 2
  have hb : 0 < b := half_pos _ha
  have hbb : b + b = a := add_halves a
  have hr (g) : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hc : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp (mₛ(S)).continuous)
  obtain ⟨j, -, -, hj⟩ := exists_sLocalHomogeneousThetaSobolevInclusion (F := F) (S := S)
    hb (le_refl b) (show 0 ≤ t from le_max_right _ _) hb ω
  let u := (j (Submodule.Quotient.mk f.val)).val.val
  have hi := (globalThetaSobolev_norm_aux μ r hr hc.measurable b b b t θ u (hj f.val).2).1
  rw [hbb] at hi
  let d (g : SIdeleQuotient F S) := intervalSobolevDensity 0 0 t (Real.log (r g))
  have hd (g) : 0 ≤ d g := by dsimp [d, intervalSobolevDensity]; positivity
  have hm : Measurable d := by dsimp [d, intervalSobolevDensity]; fun_prop
  let Z (g : SIdeleQuotient F S) : ℂ := ((r g ^ a : ℝ) : ℂ) * θ g
  have hZ : Continuous Z := (Complex.continuous_ofReal.comp (hc.rpow_const fun g ↦ Or.inl (hr g).ne')).mul θ.continuous
  have mem : MemLp Z 2 (μ.withDensity fun g ↦ ENNReal.ofReal (d g)) := by
    apply (memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).2
    apply (integrable_withDensity_iff_integrable_smul' (ENNReal.measurable_ofReal.comp hm)
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).2
    refine hi.congr (.of_forall fun g ↦ ?_)
    change ‖θ g‖ ^ 2 * intervalSobolevDensity a a t (Real.log (r g)) =
      (ENNReal.ofReal (d g)).toReal • ‖Z g‖ ^ 2
    rw [ENNReal.toReal_ofReal (hd g), smul_eq_mul]
    simp only [Z, d, norm_mul, mul_pow, Complex.norm_real,
      Real.rpow_def_of_pos (hr g), Real.norm_of_nonneg (Real.exp_pos _).le]
    have he := globalThetaSobolev_norm_density a 0 0 t (Real.log (r g))
    simp only [add_zero] at he
    rw [← he, mul_comm (Real.log (r g)) a]
    ring
  apply mem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold d intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (r g))])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
Send a local polar-free test to its weighted homogeneous theta class.
Deviation: Use the positive local twist of the Sobolev embedding. -/
def sLocalPWThetaSobolevMap {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁)
    (f : Zₛ) :=
  MemLp.toLp (localWeightedTheta(a, ω, f))
    (sLocalPWTheta_memLp (F := F) (S := S) (s := s) ha ω f)

private theorem sLocalPWThetaSobolevMap_apply_ae_of_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w : α → ℝ} (hm : AEMeasurable w μ) (hw : ∀ x, 0 < w x) {P : α → Prop}
    (h : ∀ᵐ x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)), P x) : ∀ᵐ x ∂μ, P x := by
  have := (withDensity_absolutelyContinuous' (μ := μ) (f := fun x ↦ ENNReal.ofReal (w x))
    hm.ennreal_ofReal (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.2 (hw x)).ne'))
  exact this.ae_le h

private theorem sLocalPWThetaSobolevMap_apply_dens_pos (a b s t : ℝ) :
    0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem sLocalPWThetaSobolevMap_apply_dens_meas (a b s : ℝ) :
    Measurable (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  fun_prop

/-- Paper: (11.2.1.1) and (11.2.1.6), pp. 487–488.
The local Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem sLocalPWThetaSobolevMap_apply {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (f : Zₛ) :
    (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f : SIdeleQuotient F S → ℂ) =ᵐ[sLocalQuotientTamagawaMeasure F S]
      localWeightedTheta(a, ω, f) := by
  have : OpensMeasurableSpace (SIdeleQuotient F S) := ⟨le_of_eq rfl⟩
  have hm : Measurable (fun g : SIdeleQuotient F S ↦ Real.log (((mₛ(S)) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (mₛ(S)).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas 0 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Globalized polar-free tests yield weighted Sobolev vectors.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
theorem globalPWTheta_memLp (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    MemLp (globalWeightedTheta(a, ω, f)) 2 globalWMeasure := by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo (le_max_right s 0) ω
  have he := (hj f₀ x rfl).2
  have hv := (Lp.memLp (j x).val.val).ae_eq ((withDensity_absolutelyContinuous _ _).ae_le he)
  apply hv.mono_measure (withDensity_mono (Filter.Eventually.of_forall fun g ↦ ?_))
  apply ENNReal.ofReal_le_ofReal
  unfold intervalSobolevDensity
  apply mul_le_mul_of_nonneg_left _ (le_trans (Real.exp_pos _).le (le_max_left _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (logNorm(m𝔽) g)])
    (div_le_div_of_nonneg_right (le_max_left s 0) (by norm_num))

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
Insert a local polar-free test and take its weighted global homogeneous theta class.
Deviation: Use direct integer-indicator insertion as in the repaired §7.3.2. -/
def globalPWThetaSobolevMap (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :=
  MemLp.toLp (globalWeightedTheta(a, ω, f))
    (globalPWTheta_memLp (F := F) (S := S) (s := s) a ω f)

/-- Paper: (11.2.1.2) and (11.2.1.7), pp. 487–488.
The global Sobolev map is represented almost everywhere by the weighted homogeneous theta. -/
theorem globalPWThetaSobolevMap_apply (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    (globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f : C𝔽 → ℂ) =ᵐ[μ𝔽]
      globalWeightedTheta(a, ω, f) := by
  have hm : Measurable (fun g : C𝔽 ↦ Real.log (((m𝔽) g).val : ℝ)) :=
    Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
      ((Units.continuous_val.comp (m𝔽).continuous).measurable))
  exact sLocalPWThetaSobolevMap_apply_ae_of_withDensity
    ((sLocalPWThetaSobolevMap_apply_dens_meas (-(0 : ℝ)) 0 s).comp hm).aemeasurable
    (fun _ ↦ sLocalPWThetaSobolevMap_apply_dens_pos _ _ _ _) (MemLp.coeFn_toLp _)

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
The local absolute level is the weighted Sobolev closure of homogeneous theta
from zero-moment tests whose Fourier transforms lie in the box of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalAbsolutePWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.1), p. 487.
A box-limited polar-free test gives its weighted homogeneous theta vector in the local level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalAbsolutePWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalAbsolutePWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

-- TODO(paper-gap): (11.2.1.2) leaves X free. The box parameter here is Λ,
-- as indicated by the comparison with Λ^|S| in the proof on p. 489.

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
The global absolute level is the Sobolev closure of the weighted homogeneous
theta image of the box-limited polar-free tests.
Deviation: Use X = Λ as in the comparison on p. 489. Insert directly from S
with the integer indicators of §7.3.2. Factoring this insertion at S′
gives the same global tests and preserves the two zero moments. -/
def globalAbsolutePWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWBox S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.1(1) and (11.2.1.2), p. 487.
An inserted box-limited polar-free test gives its weighted homogeneous theta
vector in the global level.
Deviation: Use X = Λ and the direct integer-indicator insertion. -/
theorem globalAbsolutePWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWBox S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "ambientGeom(" a ")" => geometricProjection (F := F) a h₀ hs
local notation "onIsotype(" ω ", " T ")" =>
  (GeoIsotype(ω)).orthogonalProjectionOnto.comp ((T).comp (GeoIsotype(ω)).subtypeL)
local notation "absLevel(" a ", " ω ", " Λ ")" =>
  (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

-- TODO(paper-gap): (11.2.1.3) gives the PW level as the codomain but
-- describes the projection using the undefined HS_{Λ₀}. The definition
-- below follows the declared codomain and the proof of Theorem 11.2.1.2.

/-- Paper: Definition 11.2.1.1(2) and (11.2.1.3), p. 488.
The absolute truncation is the orthogonal projection onto the global absolute level.
Deviation: Use the level of (11.2.1.2) for the undefined HS symbol and include
the projected vector back into the ambient isotype. -/
def absolutePWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (absLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.1(2), p. 488.
The absolute projection fixes vectors in the absolute level. -/
theorem absolutePWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (absLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.1(3), p. 488.
Absolute condensation first projects onto the absolute level, then convolves
and projects onto the weighted theta subspace. -/
def absolutePWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (absolutePWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.1(3), p. 488.
On the absolute level, condensation acts by convolution followed by the geometric projection. -/
theorem absolutePWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ absLevel(a, ω, Λ)) :
    absolutePWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := absolutePWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [absolutePWCondensation, ContinuousLinearMap.comp_apply, h]

local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "Pgeom(" a ", " ω ")" => onIsotype(ω, ambientGeom(a))

/-- Monotone closed levels inside `I`, whose closed union is `K ∩ I`, have compressed projection
limit when the projection onto `K` preserves `I`. -/
private theorem absolutePWProjection_tendsto_limit
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)] (hmono : Monotone levels)
    (hK : ∀ u : I, K.starProjection (u : H) ∈ I)
    (hle : ∀ i, levels i ≤ K.comap I.subtype)
    (hdense : K.comap I.subtype ≤ (⨆ i, levels i).topologicalClosure) (u : I) :
    Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
  have hKc : IsClosed (K : Set H) := (completeSpace_coe_iff_isComplete.mp ‹CompleteSpace K›).isClosed
  have hclosed : IsClosed (K.comap I.subtype : Set I) := hKc.preimage continuous_subtype_val
  have hsub : (⨆ i, levels i).topologicalClosure ≤ K.comap I.subtype :=
    Submodule.topologicalClosure_minimal _ (iSup_le hle) hclosed
  haveI : CompleteSpace ((⨆ i, levels i).topologicalClosure) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have h := Submodule.starProjection_tendsto_closure_iSup levels hmono u
  let v : I := ⟨K.starProjection (u : H), hK u⟩
  have hvm : v ∈ (⨆ i, levels i).topologicalClosure :=
    hdense (Submodule.mem_comap.mpr (K.starProjection_apply_mem (u : H)))
  have hvo : ∀ w ∈ (⨆ i, levels i).topologicalClosure, inner ℂ ((u : I) - v) w = 0 := by
    intro w hw
    rw [Submodule.coe_inner, Submodule.coe_sub]
    exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_comap.mp (hsub hw))
      (K.sub_starProjection_mem_orthogonal (u : H))
  have hp : (⨆ i, levels i).topologicalClosure.starProjection u =
      I.orthogonalProjectionOnto (K.starProjection u) := by
    rw [show K.starProjection (u : H) = (v : H) from rfl,
      I.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hvm hvo
  rw [hp] at h
  exact h

/-- The global absolute levels increase with the box size. -/
private theorem absolutePWProjection_tendsto_mono (a : ℝ) (ω : PontryaginDual C₁) {Λ Λ' : ℝ}
    (h : Λ ≤ Λ') :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ' := by
  have hbox : sLocalPWBox S Λ ⊆ sLocalPWBox S Λ' := fun _ hx ↦
    ⟨fun w ↦ (hx.1 w).trans h, fun v ↦ (hx.2 v).trans h⟩
  have htests : sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ) ≤
      sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ') :=
    Submodule.map_mono (Submodule.span_mono fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩)
  apply Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.val, htests f.2⟩, rfl⟩

/-- An orthogonal projection commutes with an invertible contraction whose inverse is a
contraction, when both preserve the subspace. -/
private theorem absolutePWProjection_tendsto_commute
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] (U W : H →L[ℂ] H)
    (hWU : ∀ x, W (U x) = x) (hUW : ∀ x, U (W x) = x)
    (hU : ∀ x, ‖U x‖ ≤ ‖x‖) (hW : ∀ x, ‖W x‖ ≤ ‖x‖)
    (hUK : ∀ x ∈ K, U x ∈ K) (hWK : ∀ x ∈ K, W x ∈ K) (x : H) :
    K.starProjection (U x) = U (K.starProjection x) := by
  have hiso (y : H) : ‖U y‖ = ‖y‖ := by
    refine le_antisymm (hU y) ?_
    have h := hW (U y)
    rwa [hWU] at h
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := U.toLinearMap, norm_map' := hiso }
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hUK _ (K.starProjection_apply_mem x))
  intro w hw
  have h2 : L (x - K.starProjection x) = U x - U (K.starProjection x) := map_sub U _ _
  have h3 : L (W w) = w := hUW w
  rw [← h2, ← h3, L.inner_map_map]
  exact Submodule.inner_left_of_mem_orthogonal (hWK w hw) (K.sub_starProjection_mem_orthogonal x)

/-- A closed subspace preserved by a unitary group action is preserved by its orthogonal
projection, so the projection preserves every isotype of the action. -/
private theorem absolutePWProjection_tendsto_isotype
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Type*) [CommGroup G] [TopologicalSpace G] (ρ : G →* (H →L[ℂ] H))
    (K : Submodule ℂ H) [CompleteSpace K]
    (hK : ∀ g x, x ∈ K → ρ g x ∈ K)
    (hU : ∀ g x, ‖ρ g x‖ ≤ ‖x‖) (ω : PontryaginDual G) (u : actionIsotype ρ ω) :
    K.starProjection (u : H) ∈ actionIsotype ρ ω := by
  have hinv (g : G) (x : H) : ρ g⁻¹ (ρ g x) = x := by
    show (ρ g⁻¹ * ρ g) x = x
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have hinv' (g : G) (x : H) : ρ g (ρ g⁻¹ x) = x := by
    show (ρ g * ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [mem_actionIsotype]
  intro g
  have hu : ρ g (u : H) = (ω g : ℂ) • (u : H) := (mem_actionIsotype ρ ω (u : H)).mp u.property g
  have hc := absolutePWProjection_tendsto_commute H K (ρ g) (ρ g⁻¹) (hinv g) (hinv' g)
    (hU g) (hU g⁻¹) (hK g) (hK g⁻¹) u
  change ρ g (K.starProjection (u : H)) = (ω g : ℂ) • K.starProjection (u : H)
  rw [← hc, hu, map_smul]

/-- Translation by a norm-one idele class has operator norm at most one. -/
private theorem absolutePWProjection_tendsto_norm (g : C₁) (x : GeoW) :
    ‖hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽) x‖ ≤ ‖x‖ := by
  have h1 : ideleClassNorm F (g : C𝔽) = 1 := MonoidHom.mem_ker.mp g.property
  have hlog : Real.log ((((m𝔽) (g : C𝔽)).val : ℝ)) = 0 := by
    rw [show (m𝔽) (g : C𝔽) = 1 from h1]
    simp
  have hb := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽)
  simp only [hlog, neg_zero, zero_mul, mul_zero, Real.exp_zero, max_self, abs_zero,
    add_zero, Real.one_rpow, one_mul] at hb
  exact ((hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs (g : C𝔽)).le_of_opNorm_le hb x).trans_eq
    (one_mul _)

/-- The ambient translation preserves the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_action (a : ℝ) (g : C𝔽) (x : GeoW)
    (hx : x ∈ globalThetaSobolev F a hGeo hs) :
    hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs g x ∈ globalThetaSobolev F a hGeo hs := by
  obtain ⟨ρ, hρ, -, -⟩ := exists_globalThetaSobolevAction (F := F) a hGeo hs
  have h := (ρ g ⟨x, hx⟩).property
  rw [hρ] at h
  exact h

/-- The geometric projection maps the chosen isotype into itself, because norm-one
translations are unitary and preserve the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_preservesIsotype (a : ℝ) (ω : PontryaginDual C₁)
    (u : GeoIsotype(ω)) :
    ((ambientGeom(a)).comp (GeoIsotype(ω)).subtypeL) u ∈ GeoIsotype(ω) := by
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-(0 : ℝ)) 0 s hGeo hs
  let ρ := τ.comp (ideleClassNorm F).ker.subtype
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hK (g : C₁) (x : GeoW) (hx : x ∈ K) : ρ g x ∈ K :=
    absolutePWProjection_tendsto_action (F := F) hs a g x hx
  have hmem := absolutePWProjection_tendsto_isotype GeoW C₁ ρ K hK
    (fun g x ↦ absolutePWProjection_tendsto_norm (F := F) hs g x) ω u
  with_unfolding_all exact hmem

/-- The geometric projection preserves each norm-one isotype on the line. -/
theorem geometricProjection_preserves_normOneIsotype (a : ℝ) (ω : PontryaginDual C₁)
    (u : GeoIsotype(ω)) :
    ((ambientGeom(a)).comp (GeoIsotype(ω)).subtypeL) u ∈ GeoIsotype(ω) :=
  absolutePWProjection_tendsto_preservesIsotype (F := F) hs a ω u

/-- A polar-free homogeneous theta function agrees in the weighted space with the image of
its class under the inclusion of §10.1. -/
private theorem absolutePWProjection_tendsto_theta (a : ℝ) (ω : PontryaginDual C₁) (f : Zₛ) :
    ∃ u : GeoW, u ∈ globalThetaSobolev F a hGeo hs ∧
      (u : C𝔽 → ℂ) =ᵐ[μ𝔽] globalWeightedTheta(a, ω, f) := by
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo hs ω
  have he := (hj f₀ x rfl).2
  exact ⟨(j x).val.val, (j x).val.property, he⟩

/-- The global absolute levels lie in the weighted theta subspace. -/
private theorem absolutePWProjection_tendsto_le_theta (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  obtain ⟨u, hu, he⟩ := absolutePWProjection_tendsto_theta (F := F) (S := S) hs a ω f.val
  have heq : globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val = u := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((globalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) a ω f.val).trans he.symm)
  change globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val ∈
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW)
  rw [heq]
  exact hu

section AbsoluteLevelDensity

local notation "LocalChar(" ω ", " hω ")" => sLocalNormOneCharacter S ω hω
local notation "LocalH(" η ")" => SLocalHomogeneousThetaSpace F S η
local notation "GlobalH(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "qLocal(" η ")" => (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ
local notation "qGlobal(" ω ")" => (LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)).mkQ
local notation "PolarH(" ω ")" => globalPolarFreeThetaSubmodule (F := F) ω

section

open scoped WithZero

local notation "Cℓ(" v ")" => (v : V).adicCompletion F
local notation "Qℓ(" v ")" => Cℓ(v)ˣ ⧸ ((v : V).adicCompletionIntegers F).units

/-- The relative local presentation of a trivial Picard group clears every finite valuation
outside the original stage by multiplying by the inverse of a single principal idele. -/
private theorem absLevel_idele_unit_outside (S : Finset V)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (g : IdeleGroup (𝓞 F) F) :
    ∃ x : Fˣ, ∀ v : V, v ∉ S →
      Valued.v ((g * IdeleGroup.unitEmbedding (𝓞 F) F x⁻¹).val.2 v) = (1 : ℤᵐ⁰) := by
  classical
  have hg : {v : V | Valued.v (g.val.2 v) ≠ (1 : ℤᵐ⁰)}.Finite :=
    eventually_cofinite.mp (AdeleRing.isUnit_iff.mp g.isUnit).2.2
  obtain ⟨T, hT, hPicT⟩ := (picard_uniformization F (S ∪ hg.toFinset)).1
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  let D := T \ S
  let I (v : V) : IdeleGroup (𝓞 F) F →* Cℓ(v)ˣ :=
    Units.map (((RestrictedProduct.evalRingHom (fun w : V ↦ Cℓ(w)) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom)
  let u : (v : D) → Qℓ(v.val) := fun v ↦ QuotientGroup.mk (I v.val g)
  obtain ⟨e, -⟩ := (picard_uniformization F S).2.1 T hST hPicT
  have he : (QuotientGroup.mk u : _ ⧸ (sUnitLocalClasses F T D).range) = 1 :=
    e.injective (hPic.elim _ _)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff (N := (sUnitLocalClasses F T D).range) u).mp he
  refine ⟨x.val, fun v hv ↦ ?_⟩
  have hmul : I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹) =
      I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹ := by
    rw [map_mul, ← map_inv]
    rfl
  change Valued.v (I v (g * IdeleGroup.unitEmbedding (𝓞 F) F x.val⁻¹)).val = 1
  rw [hmul]
  by_cases hvT : v ∈ T
  · let w : D := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hv⟩⟩
    have h := congrFun hx w
    change (QuotientGroup.mk (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val) : Qℓ(v)) =
      QuotientGroup.mk (I v g) at h
    have hmem : I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹ ∈
        (v.adicCompletionIntegers F).units := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (v.adicCompletionIntegers F).units)
        (I v g * (Units.map (algebraMap F Cℓ(v)).toMonoidHom x.val)⁻¹) = 1
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr h.symm
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hmem
  · have hg' : Valued.v (g.val.2 v) = (1 : ℤᵐ⁰) := by
      by_contra h
      exact hvT (hT (Finset.mem_union_right _ (hg.mem_toFinset.mpr h)))
    have hx' : Valued.v ((x.val : F) : Cℓ(v)) = (1 : ℤᵐ⁰) := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact x.property v hvT
    rw [Units.val_mul, Units.val_inv_eq_inv_val]

    change Valued.v (g.val.2 v * (((x.val : F) : Cℓ(v))⁻¹)) = 1
    rw [map_mul, map_inv₀, hg', hx', inv_one, one_mul]

end

/-- A character unramified outside S is determined by its local restriction when
the S-integer Picard group is trivial. -/
private theorem absLevel_character_eq_one (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    (h : LocalChar(ω, hω) = 1) : ω = 1 := by
  apply PontryaginDual.ext
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.val
  obtain ⟨a, ha⟩ := absLevel_idele_unit_outside S hPic g
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let t := g * d a⁻¹
  have ht : (QuotientGroup.mk t : C𝔽) = x.val := by
    have hd : (QuotientGroup.mk (d a⁻¹) : C𝔽) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨a⁻¹, rfl⟩
    change (QuotientGroup.mk' _) (g * d a⁻¹) = x.val
    rw [map_mul]
    change (QuotientGroup.mk g : C𝔽) * QuotientGroup.mk (d a⁻¹) = x.val
    rw [hd, mul_one, hg]
  have htu : t ∈ range (integralIdeleInsertion F S) := by
    apply (mem_range_integralIdeleInsertion F S t).mpr
    intro v hv
    have h1 : t.val.2 v * t.inv.2 v = 1 :=
      congrArg (fun z : AdeleRing (𝓞 F) F ↦ z.2 v) t.val_inv
    have hval : Valued.v (t.inv.2 v) = 1 := by
      have hvp := congrArg Valued.v h1
      rw [map_mul, ha v hv, one_mul, map_one] at hvp
      exact hvp
    exact ⟨(ha v hv).le, hval.le⟩
  obtain ⟨u, hu⟩ := htu
  let y₀ := Units.map (adeleProjection F S).toMonoidHom t
  have hy : sIdeleQuotientNorm F S (QuotientGroup.mk y₀) = 1 := by
    rw [sIdeleQuotientNorm_mk]
    have hh := (sIdeleNorm_spec F S).1 u
    change ideleNorm F (integralIdeleInsertion F S u) =
      sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (integralIdeleInsertion F S u)) at hh
    rw [hu] at hh
    change ideleClassNorm F (QuotientGroup.mk t) = sIdeleNorm F S y₀ at hh
    rw [ht, MonoidHom.mem_ker.mp x.property] at hh
    exact hh.symm
  let y : J₁ := ⟨QuotientGroup.mk y₀, hy⟩
  have hh := sLocalNormOneCharacter_apply ω hω u x y (by rw [hu, ht])
    (by rw [hu])
  rw [h] at hh
  exact hh.symm

/-- The polar-free homogeneous quotient is closed in the unrestricted quotient. -/
private theorem absLevel_isClosed_polar (ω : PontryaginDual C₁) :
    IsClosed (PolarH(ω) : Set (GlobalH(ω))) := by
  by_cases h : ω = 1
  · subst ω
    obtain ⟨R, -, hR, -, -⟩ := globalConverse_normTwist_exact (F := F)
    rw [← hR]
    exact R.isClosed_ker
  · have hsurj := (globalConverse_nontrivial_exact (F := F) ω h).surjective
    have ht : PolarH(ω) = ⊤ := by
      apply Submodule.eq_top_iff'.mpr
      intro x
      obtain ⟨f, hf⟩ := hsurj x
      exact Submodule.mem_map.mpr ⟨f.val, f.property, hf⟩
    rw [ht, Submodule.top_coe]
    exact isClosed_univ

/-- Integer-indicator insertion is surjective on the polar-free homogeneous quotient. -/
private theorem absLevel_exists_local_polar (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial) (x : PolarH(ω)) :
    ∃ f : Zₛ, qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val) = x.val := by
  let η := LocalChar(ω, hω)
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  let y := e.symm x.val
  have hin (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      e (qLocal(η) f) = qGlobal(ω) (sAdeleSchwartzToGlobal F S f) :=
    (LinearMap.congr_fun he (qLocal(η) f)).trans (sLocalHomogeneousThetaToGlobal_mk hω f)
  by_cases hw : ω = 1
  · subst ω
    obtain ⟨f, hf⟩ := (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S η)).mkQ_surjective y
    have hrep : qGlobal((1 : PontryaginDual C₁)) (sAdeleSchwartzToGlobal F S f) = x.val :=
      (hin f).symm.trans ((congrArg e hf).trans (e.apply_symm_apply x.val))
    obtain ⟨R, hR, hker, -, -⟩ := globalConverse_normTwist_exact (F := F)
    have hx : R x.val = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact x.property
    have hre := hR (sAdeleSchwartzToGlobal F S f)
    rw [hrep, hx] at hre
    let μ := normOneIdeleClassTamagawaMeasure F
    let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
    let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
    have hm : ((μ univ).toReal : ℂ) ≠ 0 := by
      exact_mod_cast (measureReal_univ_pos (μ := μ)).ne'
    have hpol : sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F := by
      apply (mem_adelePolarSubspace _).mpr
      exact ⟨(mul_eq_zero.mp (congrArg Prod.fst hre.symm)).resolve_left (neg_ne_zero.mpr hm),
        (mul_eq_zero.mp (congrArg Prod.snd hre.symm)).resolve_left hm⟩
    exact ⟨⟨f, (mem_sAdelePolarSubspace f).mpr
      ((sAdeleSchwartzToGlobal_mem_polarSubspace_iff S f).mp hpol)⟩, hrep⟩
  · have hη : η ≠ 1 := fun h ↦ hw (absLevel_character_eq_one ω hω hPic h)
    have hy : y ∈ (sAdelePolarSubspace F S).map (qLocal(η)) := by
      rw [sLocalZeroMomentTheta_eq_top η hη]
      exact Submodule.mem_top
    obtain ⟨f, hf, hq⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨f, hf⟩, (hin f).symm.trans ((congrArg e hq).trans (e.apply_symm_apply x.val))⟩

/-- An action on a submodule has the ambient isotype whenever its inclusion
intertwines the two actions. -/
private theorem absLevel_mem_isotype_of_submodule {W G : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [Group G] [TopologicalSpace G]
    (K : Submodule ℂ W) (ρ : G →* (K →L[ℂ] K)) (σ : G →* (W →L[ℂ] W))
    (hρ : ∀ g u, (ρ g u).val = σ g u.val) (ω : PontryaginDual G) (u : K) :
    u ∈ actionIsotype ρ ω ↔ u.val ∈ actionIsotype σ ω := by
  constructor
  · intro h
    apply (mem_actionIsotype σ ω u.val).mpr
    intro g
    exact (hρ g u).symm.trans
      (congrArg Subtype.val ((mem_actionIsotype ρ ω u).mp h g))
  · intro h
    apply (mem_actionIsotype ρ ω u).mpr
    intro g
    exact Subtype.ext ((hρ g u).trans ((mem_actionIsotype σ ω u.val).mp h g))

/-- The isotype action inside the theta subspace agrees with the ambient action. -/
private theorem absLevel_isotype_agree (a : ℝ) (ω : PontryaginDual C₁)
    (u : globalThetaSobolev F a hGeo hs) :
    u ∈ actionIsotype ((exists_globalThetaSobolevAction (F := F) a hGeo hs).choose.comp
      (ideleClassNorm F).ker.subtype) ω ↔ u.val ∈ GeoIsotype(ω) :=
  absLevel_mem_isotype_of_submodule _ _ _
    (fun g u ↦ (exists_globalThetaSobolevAction (F := F) a hGeo hs).choose_spec.1 g.val u) ω u

/-- Use the closed preimage of the desired Sobolev subspace to pass first through
each level closure and then through the sequentially dense union. -/
private theorem absLevel_dense_polar_image (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial)
    {Y : Type*} [TopologicalSpace Y] (J : PolarH(ω) → Y) (hJ : Continuous J)
    (C : Set Y) (hC : IsClosed C)
    (hgen : ∀ (f : Zₛ) (Λ : ℝ)
      (_hf : f.val ∈ sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ)),
      J ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
        Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩ ∈ C) :
    ∀ x : PolarH(ω), J x ∈ C := by
  classical
  let η := LocalChar(ω, hω)
  obtain ⟨e, he⟩ := sLocalHomogeneousThetaToGlobal_equiv_of_unramified (F := F) (S := S) hPic hω
  let D := e ⁻¹' ((Subtype.val : PolarH(ω) → GlobalH(ω)) '' (J ⁻¹' C))
  have hD : IsClosed D :=
    ((absLevel_isClosed_polar ω).isClosedEmbedding_subtypeVal.isClosedMap _
      (hC.preimage hJ)).preimage e.continuous
  have hlevel (Λ : ℝ) :
      (sLocalAbsolutePW (F := F) (S := S) (T := S) le_rfl Λ (sAdelePolarSubspace F S) η :
        Set (LocalH(η))) ⊆ D := by
    change _ ⊆ D
    rw [sLocalAbsolutePW, Submodule.topologicalClosure_coe]
    apply closure_minimal _ hD
    rintro z ⟨f, hf, rfl⟩
    refine ⟨⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f),
      Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace
        (⟨f, hf.2⟩ : Zₛ), rfl⟩⟩, hgen ⟨f, hf.2⟩ Λ hf.1, ?_⟩
    exact ((LinearMap.congr_fun he (qLocal(η) f)).trans
      (sLocalHomogeneousThetaToGlobal_mk hω f)).symm
  intro x
  obtain ⟨f, hrep⟩ := absLevel_exists_local_polar ω hω hPic x
  have hseq := sLocalAbsolutePW_seqDense (F := F) (S := S) (T := S) (S₀ := ∅)
    le_rfl (Finset.union_empty S).symm (Finset.disjoint_empty_right S) isSaturatedPlaceSet_empty
    hPic ω hω η rfl (sAdelePolarSubspace F S) (Or.inr rfl) (qLocal(η) f.val)
    (Submodule.mem_map_of_mem f.property)
  obtain ⟨u, hu, hlim⟩ := hseq
  have hz : qLocal(η) f.val ∈ D := hD.mem_of_tendsto hlim (.of_forall fun n ↦ by
    obtain ⟨Λ, -, hΛ⟩ := hu n
    exact hlevel Λ hΛ)
  obtain ⟨z, hz, hz'⟩ := hz
  have heq : e (qLocal(η) f.val) = x.val :=
    ((LinearMap.congr_fun he (qLocal(η) f.val)).trans
      (sLocalHomogeneousThetaToGlobal_mk hω f.val)).trans hrep
  rwa [show z = x from Subtype.ext (hz'.trans heq)] at hz

/-- A dense family in a submodule is dense in its image under inclusion. -/
private theorem absLevel_dense_submodule_inclusion {W X : Type*}
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [TopologicalSpace X]
    (I K : Submodule ℂ W) (H : Submodule ℂ K)
    (hH : ∀ u : K, u ∈ H ↔ u.val ∈ I) (j : X → H)
    (hj : Continuous j) (hjd : DenseRange j) :
    ∃ J : X → I, Continuous J ∧ (∀ x, (J x).val = (j x).val.val) ∧
      ∀ (C : Set I), IsClosed C → (∀ x, J x ∈ C) → ∀ u : I, u.val ∈ K → u ∈ C := by
  let i (u : H) : I := ⟨u.val.val, (hH u.val).mp u.property⟩
  have hi : Continuous i :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  refine ⟨i ∘ j, hi.comp hj, fun x ↦ rfl, fun C hC hd u hu ↦ ?_⟩
  let v : H := ⟨⟨u.val, hu⟩, (hH ⟨u.val, hu⟩).mpr u.property⟩
  have hc : IsClosed (i ⁻¹' C) := hC.preimage hi
  have hv : i v ∈ C := hc.closure_subset_iff.mpr (Set.range_subset_iff.mpr hd) (hjd v)
  exact hv

/-- The dense homogeneous inclusion, viewed in the ambient isotype, agrees with
the level generator on every inserted polar-free test. -/
private theorem absLevel_exists_sobolev_image (a : ℝ) (ω : PontryaginDual C₁) :
    let I : Submodule ℂ GeoW := GeoIsotype(ω)
    let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
    ∃ J : PolarH(ω) → I, Continuous J ∧
      (∀ f : Zₛ, (J ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
        Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩).val =
          globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f) ∧
      ∀ (C : Set I), IsClosed C → (∀ x, J x ∈ C) →
        ∀ u : I, u.val ∈ K → u ∈ C := by
  intro I K
  let hInc := exists_globalHomogeneousThetaSobolevInclusion (F := F)
    (a := a) (α := -(0 : ℝ)) (β := 0) (s := s) hGeo hs ω
  let j := hInc.choose
  have hjd := hInc.choose_spec.2.1
  have hj := hInc.choose_spec.2.2
  let ρ := (exists_globalThetaSobolevAction (F := F) a hGeo hs).choose.comp
    (ideleClassNorm F).ker.subtype
  let H : Submodule ℂ K := actionIsotype ρ ω
  have hH (u : K) : u ∈ H ↔ u.val ∈ I := absLevel_isotype_agree (F := F) hs a ω u
  obtain ⟨J, hJ, hJv, hJd⟩ := absLevel_dense_submodule_inclusion I K H hH j j.continuous hjd
  refine ⟨J, hJ, fun f ↦ ?_, hJd⟩
  let F₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f⟩
  let x : PolarH(ω) := ⟨qGlobal(ω) F₀.val, Submodule.mem_map.mpr ⟨_, F₀.property, rfl⟩⟩
  change (J x).val = _
  refine (hJv x).trans ?_
  apply Lp.ext
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((hj F₀ x rfl).2.trans (globalPWThetaSobolevMap_apply (s := s) a ω f).symm)

private theorem absLevel_density (a : ℝ) (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (hPic : PicTrivial) :
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW).comap (GeoIsotype(ω)).subtype ≤
      (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure := by
  let hImage := absLevel_exists_sobolev_image (F := F) (S := S) hs a ω
  let J := hImage.choose
  have hJ := hImage.choose_spec.1
  have hJv := hImage.choose_spec.2.1
  have hJd := hImage.choose_spec.2.2
  let C : Submodule ℂ GeoIsotype(ω) := (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure
  have hC : IsClosed (C : Set GeoIsotype(ω)) := Submodule.isClosed_topologicalClosure _
  have hd : ∀ x : PolarH(ω), J x ∈ C := by
    apply absLevel_dense_polar_image ω hω hPic J hJ (C : Set GeoIsotype(ω)) hC
    intro f Λ hf
    let x : PolarH(ω) := ⟨qGlobal(ω) (sAdeleSchwartzToGlobal F S f.val),
      Submodule.mem_map.mpr ⟨_, sAdeleSchwartzToGlobal_mem_polarSubspace f, rfl⟩⟩
    have hmem : J x ∈ absLevel(a, ω, Λ) := by
      change (J x).val ∈ globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ
      have he := hJv f
      change (J x).val = _ at he
      rw [he]
      exact globalAbsolutePWSobolev_mem hs a ω Λ f hf
    exact Submodule.le_topologicalClosure _ ((le_iSup (fun r ↦ absLevel(a, ω, r)) Λ) hmem)
  intro u hu
  exact hJd (C : Set GeoIsotype(ω)) hC hd u hu

end AbsoluteLevelDensity

/-- Paper: Theorem 11.2.1.2(1) and Proposition 7.3.2.2(1), pp. 352, 488.
Every vector of the isotype lying in the weighted theta subspace is a limit of vectors
of the absolute levels.
Deviation: Use X = Λ and the direct integer-indicator insertion. The printed density of
Proposition 7.3.2.2(1) uses unit insertion and is refuted (ERRATA F123). -/
theorem globalThetaSobolev_isotype_le_closure_absLevel (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) :
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW).comap (GeoIsotype(ω)).subtype ≤
      (⨆ Λ : ℝ, absLevel(a, ω, Λ)).topologicalClosure :=
  absLevel_density (F := F) (S := S) hs a ω _hω _hPic

/-- Paper: Theorem 11.2.1.2(1), p. 488.
The absolute projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem absolutePWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ absolutePWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) := by
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := absLevel(a, ω, Λ)
  haveI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  haveI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hmono : Monotone levels := fun _ _ h ↦
    Submodule.comap_mono (absolutePWProjection_tendsto_mono (F := F) (S := S) hs a ω h)
  have hK (v : I) : K.starProjection (v : GeoW) ∈ I :=
    absolutePWProjection_tendsto_preservesIsotype (F := F) hs a ω v
  have hle (Λ : ℝ) : levels Λ ≤ K.comap I.subtype := fun _ hw ↦
    absolutePWProjection_tendsto_le_theta (F := F) (S := S) hs a ω Λ hw
  have hdense : K.comap I.subtype ≤ (⨆ Λ, levels Λ).topologicalClosure :=
    globalThetaSobolev_isotype_le_closure_absLevel (F := F) (S := S) hs a ω _hω _hPic
  with_unfolding_all exact absolutePWProjection_tendsto_limit GeoW I K levels hmono hK hle hdense u

variable {R ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

local notation "cutoffConv(" a ", " ω ", " hρ ", " φ ")" =>
  onIsotype(ω, geometricTruncatedConvolution (F := F) a h₀ hs hρ φ)
local notation "productTraceClass(" T ", " P ")" =>
  (⟨(T).val * (P), mul_mem_nuclearEndomorphisms_right (P) (T)⟩ : nuclearEndomorphisms _)

-- At a fixed cutoff the uncompressed operator may have a different trace.
-- On theta inputs Q A Q = A Q, so cutoff condensation only needs the
-- trace class of Mρ A Q. Cutoff convolution Mρ A is already trace class
-- by §9.3.3 (a larger smooth cutoff can be chosen to cover tsupport ρ).

/-- Every cutoff is absorbed by a larger cutoff satisfying the inner-band condition. -/
private theorem exists_nuclear_geometricPWRestriction_cover
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (R ε : ℝ) (ρ : G → ℝ) (hρ : IsModulatedCutoff m R ε ρ) :
    ∃ (L d : ℝ) (χ : G → ℝ), IsModulatedCutoff m L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
  let L := R + 2
  let d := L⁻¹ / 4
  have hL : 2 < L := by dsimp [L]; linarith [hρ.radius_pos]
  have hLp : 0 < L := by linarith
  have hd : 0 < d := by dsimp [d]; positivity
  have hdlt : d < L⁻¹ := by dsimp [d]; nlinarith [inv_pos.mpr hLp]
  have hinv : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdsmall : d < 1 / 2 := by dsimp [d]; linarith
  have hplateau : 1 < L - d := by linarith
  have hprod : 1 ≤ (L⁻¹ + d) * (L - d) := by
    have hh := mul_nonneg hd.le (show 0 ≤ L - L⁻¹ - d by linarith)
    nlinarith [inv_mul_cancel₀ hLp.ne']
  let B : ContDiffBump (0 : ℝ) :=
    ⟨Real.log (L - d), Real.log L, Real.log_pos hplateau,
      Real.log_lt_log (by linarith) (by linarith)⟩
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let χ (x : G) := B (Real.log (r x))
  have h1 : χ 1 = 1 := by
    apply B.one_of_mem_closedBall
    simp [r, B.rIn_pos.le]
  have hcut : IsModulatedCutoff m L d χ := by
    refine ⟨hLp, hd, by linarith, by linarith, fun _ ↦ B.nonneg,
      fun x ↦ (abs_of_nonneg (B.nonneg (x := Real.log (r x)))) ▸ B.le_one,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact IsGreatest.csSup_eq ⟨⟨1, h1⟩, forall_mem_range.mpr fun _ ↦ B.le_one⟩
    · refine ⟨fun t ↦ B (Real.log t), ∅, fun _ ↦ rfl, by simp, ?_, by simp⟩
      simp only [Finset.coe_empty, sdiff_empty]
      exact B.contDiff.comp_contDiffOn (fun x hx ↦ (Real.contDiffAt_log.mpr (mem_Ioi.mp hx).ne').contDiffWithinAt)
    · intro x
      change B (Real.log ((m x).val : ℝ)) = B (Real.log ((m x⁻¹).val : ℝ))
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, B.neg]
    · apply closure_minimal _ (isClosed_Icc.preimage hr)
      intro x hx
      have hmem : Real.log (r x) ∈ support B := hx
      rw [B.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
      obtain ⟨hl, hu⟩ := abs_lt.mp hmem
      change L⁻¹ ≤ r x ∧ r x ≤ L
      rw [← Real.log_le_log_iff (inv_pos.mpr hLp) (hpos x), Real.log_inv,
        ← Real.log_le_log_iff (hpos x) hLp]
      exact ⟨hl.le, hu.le⟩
    · intro x hx
      apply B.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
      rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
        Real.log_le_log_iff (hpos x) (by linarith)]
      change L⁻¹ + d ≤ r x ∧ r x ≤ L - d at hx
      exact ⟨((inv_le_iff_one_le_mul₀ (by linarith : 0 < L - d)).mpr hprod).trans hx.1, hx.2⟩
  refine ⟨L, d, χ, hcut, ⟨by positivity, by linarith⟩, ?_⟩
  intro x
  by_cases hx : ρ x = 0
  · simp [hx]
  have hband := hρ.support_subset (subset_tsupport ρ (mem_support.mpr hx))
  have hR : R ≤ L - d := by dsimp [L] at *; linarith
  have hχ : χ x = 1 := by
    apply B.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    change -Real.log (L - d) ≤ _ ∧ _ ≤ Real.log (L - d)
    rw [← Real.log_inv, Real.log_le_log_iff (inv_pos.mpr (by linarith)) (hpos x),
      Real.log_le_log_iff (hpos x) (by linarith)]
    exact ⟨(inv_anti₀ hρ.radius_pos hR).trans hband.1, hband.2.trans hR⟩
  rw [hχ, mul_one]
/-- Pointwise absorption of cutoff symbols gives absorption of their L² multipliers. -/
private theorem exists_nuclear_geometricPWRestriction_absorb
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (ν : Measure G) (R ε L d : ℝ) (ρ χ : G → ℝ)
    (hρ : IsModulatedCutoff m R ε ρ) (hχ : IsModulatedCutoff m L d χ)
    (hprod : ∀ x, ρ x * χ x = ρ x) :
    (modulatedCutoffOperator m ν hρ).comp (modulatedCutoffOperator m ν hχ) =
      modulatedCutoffOperator m ν hρ := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [modulatedCutoffOperator_apply m ν hρ (modulatedCutoffOperator m ν hχ u),
    modulatedCutoffOperator_apply m ν hχ u, modulatedCutoffOperator_apply m ν hρ u] with x hx hx' hy
  change modulatedCutoffOperator m ν hρ (modulatedCutoffOperator m ν hχ u) x = modulatedCutoffOperator m ν hρ u x
  rw [hx, hx', hy, ← mul_assoc, ← Complex.ofReal_mul, hprod]
/-- An admissible cutoff followed by Hardy–Sobolev convolution is nuclear. -/
private theorem exists_nuclear_geometricPWRestriction_admissible
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (φ : BruhatCompactSupport G)
    (L d : ℝ) (χ : G → ℝ) (hχ : IsModulatedCutoff m L d χ)
    (hband : 0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) :
    IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp
      (hardySobolevTestAction μ m a b s hab hs φ)) := by
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  obtain ⟨hbig, _, _⟩ := truncatedHardySobolevConvolution_trace μ m a b s hab hs φ.val
    hc.aemeasurable φ.property.2 hb hm hms hφs hχ hband
  have hconv := hardySobolevConvolution_eq_testAction μ m a b s hab hs φ hc.aemeasurable hb
  exact (congrArg (fun U ↦ IsNuclearOperator ((modulatedCutoffOperator m
      (μ.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))) hχ).comp U)) hconv).mp hbig

/-- Bounded precomposition and postcomposition preserve nuclearity between Hilbert spaces. -/
private theorem exists_nuclear_geometricPWRestriction_compress
    (H J : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
    (A : H →L[ℂ] H) (hA : IsNuclearOperator A) (S : J →L[ℂ] H) (R : H →L[ℂ] J) :
    IsNuclearOperator (R.comp (A.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  let pre := (ContinuousLinearMap.compL ℂ J H ℂ).flip S
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, (fun n ↦ (φ n).comp S), R ∘ y, hc, ?_, ?_, ?_⟩
  · exact (pre.continuous.tendsto' 0 0 (map_zero pre)).comp hφ
  · exact (R.continuous.tendsto' 0 0 (map_zero R)).comp hy
  · intro x
    simpa only [map_smul, Function.comp_apply, ContinuousLinearMap.comp_apply] using R.hasSum (hsum (S x))
/-- A vector fixed by a compressed orthogonal projector is fixed by the ambient projector. -/
private theorem exists_nuclear_geometricPWRestriction_fixed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K] (u : I)
    (hu : I.orthogonalProjectionOnto (K.starProjection (u : H)) = u) :
    K.starProjection (u : H) = u := by
  have hi := congrArg (fun v : I ↦ RCLike.re (inner ℂ v u)) hu
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    K.re_inner_starProjection_eq_normSq] at hi
  have hnorm : ‖K.starProjection (u : H)‖ = ‖(u : H)‖ := by
    have hs : ‖K.starProjection (u : H)‖ ^ 2 = ‖(u : H)‖ ^ 2 := by
      simpa only [Submodule.starProjection_apply, Submodule.norm_coe, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re] using hi
    nlinarith [norm_nonneg (K.starProjection (u : H)), norm_nonneg (u : H)]
  exact K.starProjection_eq_self_iff.mpr ((K.mem_iff_norm_starProjection (u : H)).mpr hnorm)
/-- The two cutoff composition orders agree on inputs fixed by the compressed geometric projector. -/
private theorem exists_nuclear_geometricPWRestriction_agree
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (M A : H →L[ℂ] H)
    (hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection)
    (P : I →L[ℂ] I)
    (hP : (I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)) * P = P) :
    (I.orthogonalProjectionOnto.comp (M.comp (A.comp (K.starProjection.comp I.subtypeL)))) * P =
      (I.orthogonalProjectionOnto.comp (M.comp (K.starProjection.comp (A.comp I.subtypeL)))) * P := by
  apply ContinuousLinearMap.ext
  intro u
  have hfix := congrArg (fun U : I →L[ℂ] I ↦ U u) hP
  have hp : K.starProjection (P u : H) = P u := exists_nuclear_geometricPWRestriction_fixed H I K (P u) hfix
  have ha := congrArg (fun U : H →L[ℂ] H ↦ U (P u)) hAK
  change K.starProjection (A (K.starProjection (P u : H))) = A (K.starProjection (P u : H)) at ha
  rw [hp] at ha
  change I.orthogonalProjectionOnto (M (A (K.starProjection (P u : H)))) = I.orthogonalProjectionOnto (M (K.starProjection (A (P u : H))))
  rw [hp, ha]


/-- Paper: Theorems 11.2.1.2(2) and 11.2.1.4(2), pp. 488–489.
The cutoff geometric restriction is trace class on the chosen isotype.
It agrees with cutoff geometric convolution after any map into theta.
Deviation: Use the right-compressed operator for the corrected limits. -/
theorem exists_nuclear_geometricPWRestriction (a : ℝ) (ω : PontryaginDual C₁)
    (φ : BruhatCompactSupport C𝔽) (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    ∃ T : nuclearEndomorphisms GeoIsotype(ω),
      T.val = onIsotype(ω, geometricRestriction (F := F) a h₀ hs hρ φ) ∧
      ∀ P : GeoIsotype(ω) →L[ℂ] GeoIsotype(ω), Pgeom(a, ω) * P = P →
        T.val * P = cutoffConv(a, ω, hρ, φ) * P := by
  have hcover : ∃ (L d : ℝ) (χ : C𝔽 → ℝ), IsModulatedCutoff m𝔽 L d χ ∧
      (0 < L⁻¹ + d ∧ L⁻¹ + d < L - d) ∧ ∀ x, ρ x * χ x = ρ x := by
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_cover C𝔽 m𝔽 R ε ρ hρ
  obtain ⟨L, d, χ, hχ, hband, hprod⟩ := hcover
  let H := GeoW
  let I : Submodule ℂ H := GeoIsotype(ω)
  let K : Submodule ℂ H := globalThetaSobolev F a hGeo hs
  let M : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hρ
  let A : H →L[ℂ] H := by with_unfolding_all exact geoAction(φ)
  letI : CompleteSpace I := by with_unfolding_all exact (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  let N : H →L[ℂ] H := by with_unfolding_all exact modulatedCutoffOperator m𝔽 globalWMeasure hχ
  have hn : IsNuclearOperator (N.comp A) := by
    with_unfolding_all
      exact exists_nuclear_geometricPWRestriction_admissible C𝔽 μ𝔽 m𝔽
        ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1 (-(0 : ℝ)) 0 s hGeo hs φ L d χ hχ hband
  have habsorb : M.comp N = M := exists_nuclear_geometricPWRestriction_absorb C𝔽 m𝔽 globalWMeasure R ε L d ρ χ hρ hχ hprod
  have hsmall : IsNuclearOperator (M.comp A) := by
    have hh := mul_mem_nuclearEndomorphisms_left M (⟨N.comp A, hn⟩ : nuclearEndomorphisms H)
    change IsNuclearOperator (M.comp (N.comp A)) at hh
    rwa [← ContinuousLinearMap.comp_assoc, habsorb] at hh
  let U : H →L[ℂ] H := M.comp (A.comp K.starProjection)
  have hU : IsNuclearOperator U := mul_mem_nuclearEndomorphisms_right K.starProjection
    (⟨M.comp A, hsmall⟩ : nuclearEndomorphisms H)
  have hnI := exists_nuclear_geometricPWRestriction_compress H I U hU I.subtypeL I.orthogonalProjectionOnto
  let T : nuclearEndomorphisms I := ⟨I.orthogonalProjectionOnto.comp (U.comp I.subtypeL), hnI⟩
  refine ⟨T, ?_, ?_⟩
  · with_unfolding_all rfl
  · intro P hP
    have hAK : K.starProjection.comp (A.comp K.starProjection) = A.comp K.starProjection := by
      with_unfolding_all exact geometricProjection_convolution_geometricProjection (F := F) a h₀ hs φ
    with_unfolding_all exact exists_nuclear_geometricPWRestriction_agree H I K M A hAK P hP

local notation "nuclearRestriction(" a ", " ω ", " hρ ", " φ ")" =>
  (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose

/-- Uniformly bounded self-adjoint strongly null families kill nuclear operators on the right in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_null
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Q : ℝ → H →L[ℂ] H) (hQ : ∀ x, Tendsto (fun i ↦ Q i x) atTop (𝓝 0))
    (hQa : ∀ i, (Q i).adjoint = Q i) (hQc : ∀ i x, ‖Q i x‖ ≤ 2 * ‖x‖)
    (T : nuclearEndomorphisms H) :
    Tendsto (fun i ↦ traceNorm ⟨T.val * Q i, mul_mem_nuclearEndomorphisms_right (Q i) T⟩)
      atTop (𝓝 0) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hT⟩ := (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
  let u (n : ℕ) := (InnerProductSpace.toDual ℂ H).symm (φ n)
  have hu (n : ℕ) : ‖u n‖ = ‖φ n‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map _
  let cost (i : ℝ) (n : ℕ) := ‖c n‖ * (‖Q i (u n)‖ * ‖y n‖)
  let bound (n : ℕ) := 2 * (‖c n‖ * (‖φ n‖ * ‖y n‖))
  have hcost_nonneg (i : ℝ) (n : ℕ) : 0 ≤ cost i n := by dsimp [cost]; positivity
  have hbound (i : ℝ) (n : ℕ) : ‖cost i n‖ ≤ bound n := by
    rw [Real.norm_of_nonneg (hcost_nonneg i n)]
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ((hQc i (u n)).trans_eq (congrArg (2 * ·) (hu n))) (norm_nonneg (y n)))
      (norm_nonneg (c n))
    dsimp only [cost, bound]
    nlinarith
  have hs : Summable bound := by
    obtain ⟨C, hC, hφC⟩ := (Metric.isBounded_range_of_tendsto φ hφ).exists_pos_norm_le
    obtain ⟨D, _, hyD⟩ := (Metric.isBounded_range_of_tendsto y hy).exists_pos_norm_le
    apply Summable.mul_left 2
    refine (hc.mul_right (C * D)).of_norm_bounded fun n ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hφC _ (mem_range_self n)) (hyD _ (mem_range_self n))
        (norm_nonneg _) hC.le) (norm_nonneg _)
  have hlim : Tendsto (fun i ↦ ∑' n, cost i n) atTop (𝓝 0) := by
    have hterm (n : ℕ) : Tendsto (fun i ↦ cost i n) atTop (𝓝 0) := by
      simpa [cost] using ((hQ (u n)).norm.mul_const ‖y n‖).const_mul ‖c n‖
    simpa only [tsum_zero] using
      tendsto_tsum_of_dominated_convergence hs hterm (Eventually.of_forall hbound)
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  refine squeeze_zero (fun _ ↦ (traceNorm_normedSpaceCore (H := H)).toCore.norm_nonneg _)
    ?_ hlim
  intro i
  let ψ (n : ℕ) : StrongDual ℂ H := c n • innerSL ℂ (Q i (u n))
  have hψ (n : ℕ) : ‖ψ n‖ * ‖y n‖ = cost i n := by
    simp only [ψ, cost, norm_smul, innerSL_apply_norm, mul_assoc]
  simp_rw [← hψ]
  refine traceNorm_le_of_rankOne_series _ ψ y
    ((hs.of_norm_bounded (hbound i)).congr fun n ↦ (hψ n).symm) fun x ↦ ?_
  have heval (n : ℕ) : ψ n x = c n * φ n (Q i x) := by
    have hinner := (Q i).adjoint_inner_left x (u n)
    rw [hQa] at hinner
    simp only [ψ, smul_apply, smul_eq_mul, innerSL_apply_apply, hinner, u, InnerProductSpace.toDual_symm_apply]
  simpa [heval, mul_apply_eq_comp] using hT (Q i x)
/-- A compressed ambient projection preserves the compressing subspace if it is a strong limit of orthogonal projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_preserves
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u)))) (u : I) :
    K.starProjection u ∈ I := by
  let w := K.starProjection (u : H)
  let z := I.orthogonalProjectionOnto w
  have hiC : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection u) u) atTop (𝓝 (inner ℂ z u)) :=
    (hlim u).inner tendsto_const_nhds
  have hi := (RCLike.continuous_re.tendsto _).comp hiC
  have heq (i : ℝ) : RCLike.re (inner ℂ ((levels i).starProjection u) u) = ‖(levels i).starProjection u‖ ^ 2 := by
    with_unfolding_all simpa only [Submodule.starProjection_apply, Submodule.norm_coe] using (levels i).re_inner_starProjection_eq_normSq u
  have hn : Tendsto (fun i ↦ RCLike.re (inner ℂ ((levels i).starProjection u) u)) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [heq] using (hlim u).norm.pow 2
  have hz : RCLike.re (inner ℂ z u) = ‖z‖ ^ 2 := tendsto_nhds_unique hi hn
  have hw : RCLike.re (inner ℂ w (u : H)) = ‖w‖ ^ 2 := by
    with_unfolding_all simpa only [w, Submodule.starProjection_apply, Submodule.norm_coe] using K.re_inner_starProjection_eq_normSq (u : H)
  have hnorm : ‖I.starProjection w‖ = ‖w‖ := by
    have hh : RCLike.re (inner ℂ z u) = RCLike.re (inner ℂ w (u : H)) := by
      rw [show z = I.orthogonalProjectionOnto w from rfl, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    have hsq : ‖I.starProjection w‖ ^ 2 = ‖w‖ ^ 2 := by
      change ‖z‖ ^ 2 = ‖w‖ ^ 2
      linarith
    nlinarith [norm_nonneg (I.starProjection w), norm_nonneg w]
  exact (I.mem_iff_norm_starProjection w).mpr hnorm
/-- Strong convergence of orthogonal projections preserves a right-supported nuclear operator in trace norm. -/
private theorem absolutePWCondensation_traceNorm_tendsto_projection
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (levels : ℝ → Submodule ℂ H) [∀ i, CompleteSpace (levels i)] (R : H →L[ℂ] H)
    (hlim : ∀ u, Tendsto (fun i ↦ (levels i).starProjection u) atTop (𝓝 (R u)))
    (T : nuclearEndomorphisms H) (hTR : T.val * R = T.val) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  have hRa : R.adjoint = R := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hl : Tendsto (fun i ↦ inner ℂ x ((levels i).starProjection y)) atTop (𝓝 (inner ℂ x (R y))) := tendsto_const_nhds.inner (hlim y)
    have hr : Tendsto (fun i ↦ inner ℂ ((levels i).starProjection x) y) atTop (𝓝 (inner ℂ (R x) y)) := (hlim x).inner tendsto_const_nhds
    have heq : (fun i ↦ inner ℂ x ((levels i).starProjection y)) = (fun i ↦ inner ℂ ((levels i).starProjection x) y) := by
      funext i
      exact (Submodule.inner_starProjection_left_eq_right (levels i) x y).symm
    rw [heq] at hl
    exact tendsto_nhds_unique hl hr
  have hR (x : H) : ‖R x‖ ≤ ‖x‖ :=
    le_of_tendsto' ((hlim x).norm) (fun i ↦ (levels i).norm_starProjection_apply_le x)
  let Q (i : ℝ) := (levels i).starProjection - R
  have hQ (x : H) : Tendsto (fun i ↦ Q i x) atTop (𝓝 0) := by
    simpa [Q] using (hlim x).sub (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ R x) atTop (𝓝 (R x)))
  have hQa (i : ℝ) : (Q i).adjoint = Q i := by
    simp only [Q, map_sub, (isSelfAdjoint_starProjection (levels i)).adjoint_eq, hRa]
  have hQc (i : ℝ) (x : H) : ‖Q i x‖ ≤ 2 * ‖x‖ := by
    exact (norm_sub_le ((levels i).starProjection x) (R x)).trans (by linarith [(levels i).norm_starProjection_apply_le x, hR x])
  have hh := absolutePWCondensation_traceNorm_tendsto_null H Q hQ hQa hQc T
  apply hh.congr'
  filter_upwards with i
  apply congrArg traceNorm
  apply Subtype.ext
  change T.val * ((levels i).starProjection - R) = T.val * (levels i).starProjection - T.val
  rw [mul_sub, hTR]
/-- The right-compressed nuclear operator is recovered by strongly convergent compressed projections. -/
private theorem absolutePWCondensation_traceNorm_tendsto_compressed
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A : H →L[ℂ] H) (levels : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (levels i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (levels i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (T : nuclearEndomorphisms I)
    (hTval : T.val = I.orthogonalProjectionOnto.comp (A.comp (K.starProjection.comp I.subtypeL))) :
    Tendsto (fun i ↦ traceNorm
      (⟨T.val * (levels i).starProjection, mul_mem_nuclearEndomorphisms_right (levels i).starProjection T⟩ - T))
      atTop (𝓝 0) := by
  let R : I →L[ℂ] I := I.orthogonalProjectionOnto.comp (K.starProjection.comp I.subtypeL)
  apply absolutePWCondensation_traceNorm_tendsto_projection I levels R hlim T
  rw [hTval]
  apply ContinuousLinearMap.ext
  intro u
  change I.orthogonalProjectionOnto (A (K.starProjection (I.starProjection (K.starProjection (u : H))))) = I.orthogonalProjectionOnto (A (K.starProjection (u : H)))
  rw [I.starProjection_eq_self_iff.mpr (absolutePWCondensation_traceNorm_tendsto_preserves H I K levels hlim u),
    K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem (u : H))]


/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.4), p. 488.
Right multiplication of cutoff geometric convolution by the absolute projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem absolutePWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.2(2) and (11.2.1.5), p. 488.
The traces of the cutoff absolute condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem absolutePWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, absolutePWProjection (F := F) (S := S) hs a ω r))
    (absolutePWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
The local invariant level completes the weighted theta image of zero-moment
tests with compact Fourier support in the product-norm region of size Λ.
Deviation: Use a positive local twist so the weighted theta functions belong to L². -/
def sLocalInvariantPWSobolev (_hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ) :
    Submodule ℂ LocalW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
A polar-free test band-limited by product norm gives its weighted homogeneous
theta vector in the local invariant level.
Deviation: Use the positive local twist of the repaired definition. -/
theorem sLocalInvariantPWSobolev_mem {a : ℝ} (ha : 0 < a) (ω : PontryaginDual J₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
The global invariant level completes the weighted homogeneous theta image
of the inserted polar-free tests with compact Fourier support in the product region.
Deviation: Use the integer-indicator insertion of §7.3.2 directly from S. -/
def globalInvariantPWSobolev (_hs : 0 ≤ s) (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    Submodule ℂ GeoW :=
  (Submodule.span ℂ (range fun f : band(sLocalPWProductRegion S Λ) ↦
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val)).topologicalClosure

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.7), p. 488.
An inserted polar-free test band-limited by product norm gives its weighted
homogeneous theta vector in the global invariant level.
Deviation: Use the direct integer-indicator insertion. -/
theorem globalInvariantPWSobolev_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (f : Zₛ) (_hf : f ∈ band(sLocalPWProductRegion S Λ)) :
    globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f ∈ globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨f, _hf⟩, rfl⟩)

local notation "invLevel(" a ", " ω ", " Λ ")" =>
  (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap (GeoIsotype(ω)).subtype

/-- Paper: Definition 11.2.1.3(2) and (11.2.1.8), p. 489.
The invariant truncation is the orthogonal projection onto the global invariant level.
Deviation: Include the projected vector back into the ambient isotype. -/
def invariantPWProjection (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  (invLevel(a, ω, Λ)).starProjection

/-- Paper: Definition 11.2.1.3(2), p. 489.
The invariant projection fixes vectors in the invariant level. -/
theorem invariantPWProjection_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWProjection (F := F) (S := S) hs a ω Λ u = u := by
  letI : IsClosed (invLevel(a, ω, Λ) : Set GeoIsotype(ω)) :=
    (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val
  exact Submodule.starProjection_eq_self_iff.mpr _hu

/-- Paper: Definition 11.2.1.3(3), p. 489.
Invariant condensation first projects onto the invariant level, then convolves
and projects onto the weighted theta subspace. -/
def invariantPWCondensation (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ)) :
    GeoIsotype(ω) →L[ℂ] GeoIsotype(ω) :=
  (onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ)))).comp
    (invariantPWProjection (F := F) (S := S) hs a ω Λ)

/-- Paper: Definition 11.2.1.3(3), p. 489.
On the invariant level, condensation acts by convolution followed by the geometric projection. -/
theorem invariantPWCondensation_apply_of_mem (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ)
    (φ : BruhatCompactSupport C𝔽) (hφ : supportedAboveOne(φ))
    (u : GeoIsotype(ω)) (_hu : u ∈ invLevel(a, ω, Λ)) :
    invariantPWCondensation (F := F) (S := S) hs a ω Λ φ hφ u =
      onIsotype(ω, (ambientGeom(a)).comp (geoAction(φ))) u := by
  have h := invariantPWProjection_apply_of_mem (F := F) (S := S) hs a ω Λ u _hu
  simp only [invariantPWCondensation, ContinuousLinearMap.comp_apply, h]

/-- Projections onto levels squeezed between convergent levels and the target range converge. -/
private theorem invariantPWProjection_tendsto_squeeze
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (I K : Submodule ℂ H) [CompleteSpace I] [CompleteSpace K]
    (A B : ℝ → Submodule ℂ I) [∀ i, CompleteSpace (A i)] [∀ i, CompleteSpace (B i)]
    (hlim : ∀ u : I, Tendsto (fun i ↦ (A i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))))
    (g : ℝ → ℝ) (hg : Tendsto g atTop atTop) (hAB : ∀ᶠ i in atTop, A (g i) ≤ B i)
    (hBK : ∀ (i : ℝ) (w : I), w ∈ B i → (w : H) ∈ K) (u : I) :
    Tendsto (fun i ↦ (B i).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
  have horth (i : ℝ) (w : I) (hw : w ∈ B i) :
      inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) w = 0 := by
    have h1 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H))) w =
        inner ℂ (u : H) (w : H) := by
      rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
        Submodule.inner_starProjection_left_eq_right, K.starProjection_eq_self_iff.mpr (hBK i w hw)]
    rw [inner_sub_left, h1, Submodule.coe_inner, sub_self]
  have hle (i : ℝ) (hi : A (g i) ≤ B i) :
      ‖(B i).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ ≤
        ‖(A (g i)).starProjection u - I.orthogonalProjectionOnto (K.starProjection (u : H))‖ := by
    have hb : (B i).starProjection u ∈ B i := (B i).starProjection_apply_mem u
    have ha : (A (g i)).starProjection u ∈ B i := hi ((A (g i)).starProjection_apply_mem u)
    have hw : (B i).starProjection u - (A (g i)).starProjection u ∈ B i := (B i).sub_mem hb ha
    have h0 : inner ℂ (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u)
        ((B i).starProjection u - (A (g i)).starProjection u) = 0 := by
      rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u =
          (I.orthogonalProjectionOnto (K.starProjection (u : H)) - u) + (u - (B i).starProjection u)
          by abel, inner_add_left, horth i _ hw,
        Submodule.starProjection_inner_eq_zero (K := B i) u _ hw, add_zero]
    have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [show I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u +
        ((B i).starProjection u - (A (g i)).starProjection u) =
        I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u
        by abel] at hp
    rw [norm_sub_rev ((B i).starProjection u), norm_sub_rev ((A (g i)).starProjection u)]
    nlinarith [norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (A (g i)).starProjection u),
      norm_nonneg (I.orthogonalProjectionOnto (K.starProjection (u : H)) - (B i).starProjection u),
      norm_nonneg ((B i).starProjection u - (A (g i)).starProjection u)]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_iff_norm_sub_tendsto_zero.mp ((hlim u).comp hg))
  filter_upwards [hAB] with i hi using hle i hi

/-- Raising the level to the reciprocal of the place count tends to infinity and stays below it. -/
private theorem invariantPWProjection_tendsto_root (c : ℕ) :
    let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
    Tendsto g atTop atTop ∧ ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := by
  intro g
  let d : ℝ := (c : ℝ) + 1
  have hd : 0 < d := by positivity
  refine ⟨tendsto_rpow_atTop (one_div_pos.mpr hd), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hg : 0 < g Λ := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < Λ) _
  refine ⟨hg, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  calc Λ ^ (1 / d * c) ≤ Λ ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hΛ (by
          rw [div_mul_eq_mul_div, one_mul, div_le_one hd]
          exact le_add_of_nonneg_right zero_le_one)
    _ = Λ := Real.rpow_one Λ

/-- A box of size Λ lies in every product region of size at least Λ to the number of places. -/
private theorem invariantPWProjection_tendsto_abs_le (a : ℝ) (ω : PontryaginDual C₁) {Λ Y : ℝ}
    (hΛ : 0 < Λ) (hY : Λ ^ (Fintype.card (InfinitePlace F) + S.card) ≤ Y) :
    globalAbsolutePWSobolev (F := F) (S := S) hs a ω Λ ≤
      globalInvariantPWSobolev (F := F) (S := S) hs a ω Y := by
  have hbox : sLocalPWBox S Λ ⊆ sLocalPWProductRegion S Y := by
    intro x hx
    have ha : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ Λ ^ Fintype.card (InfinitePlace F) := by
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : InfinitePlace F ↦ Λ)
          (fun w _ ↦ pow_nonneg (norm_nonneg (x.1 w)) w.mult) (fun w _ ↦ hx.1 w))
    have hf : (∏ v : S, ‖x.2 v‖) ≤ Λ ^ S.card := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using
        (Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : S ↦ Λ)
          (fun v _ ↦ norm_nonneg (x.2 v)) (fun v _ ↦ hx.2 v))
    change _ * _ ≤ Y
    refine le_trans ?_ hY
    rw [pow_add]
    exact mul_le_mul ha hf (Finset.prod_nonneg fun v _ ↦ norm_nonneg (x.2 v))
      (pow_nonneg hΛ.le _)
  have htests : sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWBox S Λ) ≤
      sLocalPWTests (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y) :=
    Submodule.map_mono (Submodule.span_mono fun _ hf ↦ ⟨hf.1, hf.2.trans (Set.preimage_mono hbox)⟩)
  refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨f.val, htests f.property⟩, rfl⟩

/-- The global invariant levels lie in the weighted theta subspace. -/
private theorem invariantPWProjection_tendsto_le_theta (a : ℝ) (ω : PontryaginDual C₁) (Λ : ℝ) :
    globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ ≤
      (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW) := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  let f₀ : adelePolarSubspace F := ⟨sAdeleSchwartzToGlobal F S f.val.val,
    sAdeleSchwartzToGlobal_mem_polarSubspace f.val⟩
  let x : globalPolarFreeThetaSubmodule (F := F) ω :=
    ⟨Submodule.Quotient.mk f₀.val, ⟨f₀.val, f₀.property, rfl⟩⟩
  obtain ⟨j, -, -, hj⟩ := exists_globalHomogeneousThetaSobolevInclusion
    (F := F) (a := a) hGeo hs ω
  have he := (hj f₀ x rfl).2
  have heq : globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val = (j x).val.val := by
    apply Lp.ext
    exact (withDensity_absolutelyContinuous _ _).ae_le
      ((globalPWThetaSobolevMap_apply (F := F) (S := S) (s := s) a ω f.val).trans he.symm)
  change globalPWThetaSobolevMap (F := F) (S := S) (s := s) a ω f.val ∈
    (globalThetaSobolev F a hGeo hs : Submodule ℂ GeoW)
  rw [heq]
  exact (j x).val.property

/-- Paper: Theorem 11.2.1.4(1), p. 489.
The invariant projections converge strongly to the isotypic geometric projection.
Deviation: The support assumption on the test function is used in part (2). -/
theorem invariantPWProjection_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial) (u : GeoIsotype(ω)) :
    Tendsto (fun Λ ↦ invariantPWProjection (F := F) (S := S) hs a ω Λ u) atTop (𝓝 (Pgeom(a, ω) u)) := by
  let c : ℕ := Fintype.card (InfinitePlace F) + S.card
  let g : ℝ → ℝ := fun Λ ↦ Λ ^ (1 / ((c : ℝ) + 1))
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let A (Λ : ℝ) : Submodule ℂ I := absLevel(a, ω, Λ)
  let B (Λ : ℝ) : Submodule ℂ I := invLevel(a, ω, Λ)
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (A Λ) := fun Λ ↦
    (show IsClosed (A Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (B Λ) := fun Λ ↦
    (show IsClosed (B Λ : Set I) from
      (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hpow : ∀ᶠ Λ in atTop, 0 < g Λ ∧ g Λ ^ c ≤ Λ := (invariantPWProjection_tendsto_root c).2
  have hAB : ∀ᶠ Λ in atTop, A (g Λ) ≤ B Λ := by
    filter_upwards [hpow] with Λ hΛ
    exact Submodule.comap_mono
      (invariantPWProjection_tendsto_abs_le (F := F) (S := S) hs a ω hΛ.1 hΛ.2)
  have hBK (Λ : ℝ) (w : I) (hw : w ∈ B Λ) : (w : GeoW) ∈ K :=
    invariantPWProjection_tendsto_le_theta (F := F) (S := S) hs a ω Λ hw
  have hlim (v : I) : Tendsto (fun Λ ↦ (A Λ).starProjection v) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection v))) := by
    with_unfolding_all exact absolutePWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic v
  with_unfolding_all
    exact invariantPWProjection_tendsto_squeeze GeoW I K A B hlim g
      (invariantPWProjection_tendsto_root c).1 hAB hBK u

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.9), p. 489.
Right multiplication of cutoff geometric convolution by the invariant projections
converges in trace norm.
Deviation: For the fixed cutoff keep the right geometric projection in the
limit. Use the trace class of cutoff convolution on the geometric range. -/
theorem invariantPWCondensation_traceNorm_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ traceNorm
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ) -
        T)) atTop (𝓝 0) := by
  intro T
  let I : Submodule ℂ GeoW := GeoIsotype(ω)
  let K : Submodule ℂ GeoW := globalThetaSobolev F a hGeo hs
  let levels (Λ : ℝ) : Submodule ℂ I := (globalInvariantPWSobolev (F := F) (S := S) hs a ω Λ).comap I.subtype
  letI : CompleteSpace I := (instClosedSpectralIsotypeSec2 (F := F) hGeo hs ω).completeSpace_coe
  letI : ∀ Λ, CompleteSpace (levels Λ) := fun Λ ↦
    (show IsClosed (levels Λ : Set I) from (Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val).completeSpace_coe
  have hlim (u : I) : Tendsto (fun Λ ↦ (levels Λ).starProjection u) atTop
      (𝓝 (I.orthogonalProjectionOnto (K.starProjection u))) := by
    with_unfolding_all exact invariantPWProjection_tendsto (F := F) (S := S) hs a ω _hω _hPic u
  have hTval : T.val = I.orthogonalProjectionOnto.comp
      (((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))).comp (K.starProjection.comp I.subtypeL)) := by
    with_unfolding_all exact (exists_nuclear_geometricPWRestriction (F := F) hs a ω φ hρ).choose_spec.1
  with_unfolding_all
    exact absolutePWCondensation_traceNorm_tendsto_compressed GeoW I K
      ((modulatedCutoffOperator m𝔽 globalWMeasure hρ).comp (geoAction(φ))) levels hlim T hTval

/-- Paper: Theorem 11.2.1.4(2) and (11.2.1.10), p. 489.
The traces of the cutoff invariant condensations converge to the trace of the
cutoff operator composed on the right with the geometric projection.
Deviation: Keep the right geometric projection at the fixed cutoff. -/
theorem invariantPWCondensation_trace_tendsto (a : ℝ) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (_hPic : PicTrivial)
    (φ : BruhatCompactSupport C𝔽) (_hφ : supportedAboveOne(φ))
    (hρ : IsModulatedCutoff m𝔽 R ε ρ) :
    let T := nuclearRestriction(a, ω, hρ, φ)
    Tendsto (fun Λ ↦ hilbertTrace
      (productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω Λ))) atTop
      (𝓝 (hilbertTrace T)) := by
  have limit {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (T : nuclearEndomorphisms H) (A : ℝ → nuclearEndomorphisms H)
      (h : Tendsto (fun r ↦ traceNorm (A r - T)) atTop (𝓝 0)) :
      Tendsto (fun r ↦ hilbertTrace (A r)) atTop (𝓝 (hilbertTrace T)) := by
    obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub]
    simp only [htr]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_hilbertTrace_le _) h
  let T := nuclearRestriction(a, ω, hρ, φ)
  exact limit (H := ↥(GeoIsotype(ω))) T
    (fun r ↦ productTraceClass(T, invariantPWProjection (F := F) (S := S) hs a ω r))
    (invariantPWCondensation_traceNorm_tendsto (F := F) (S := S) hs a ω _hω _hPic φ _hφ hρ)

end Levels

section Orbital

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "N(" p ", " hs ", " ω ")" => orbitalSobolevSubmodule F (Sₚ(p)) hs ω

variable (F) in
/-- Paper: (11.2.2.1), p. 489. The prime-indexed Sobolev quotient divides the
zero-line isotype by the closed principal-value subspace.
Deviation: Use the closure of the principal-value image from §11.2.0.
Zero-line theta density identifies the completed theta isotype with the ambient one.

A `def`, not an `abbrev` (#6264): its normed and inner product structures are the instances
below, declared once, so that every statement sees the same instance path. -/
def PrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : Type _ :=
  ↥(Wω(hs, ω)) ⧸ N(p, hs, ω)

local notation "Q(" p ", " hs ", " ω ")" => PrimeOrbitalSobolevQuotient F p hs ω

/-- The quotient norm: the denominator is closed (`instClosedOrbitalSobolevSubmoduleSec2a`). -/
instance instNormedAddCommGroupPrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) : NormedAddCommGroup Q(p, hs, ω) :=
  inferInstanceAs (NormedAddCommGroup (↥(Wω(hs, ω)) ⧸ N(p, hs, ω)))

/-- The quotient inner product, transported from the orthogonal complement of the closed
denominator in the complete isotype. -/
instance instInnerProductSpacePrimeOrbitalSobolevQuotient (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) : InnerProductSpace ℂ Q(p, hs, ω) :=
  letI : CompleteSpace ↥(Wω(hs, ω)) :=
    (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
  letI : CompleteSpace ↥(N(p, hs, ω)) :=
    (instClosedOrbitalSobolevSubmoduleSec2a (F := F) (Sₚ(p)) hs ω).completeSpace_coe
  inferInstanceAs (InnerProductSpace ℂ (↥(Wω(hs, ω)) ⧸ N(p, hs, ω)))

/-- Paper: (11.2.2.1), p. 489. In the prime quotient a representative has
zero class exactly when it belongs to the closed principal-value subspace.
Deviation: Use the closed image from §11.2.0. -/
theorem primeOrbitalSobolevQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (u : Wω(hs, ω)) :
    ((N(p, hs, ω)).mkQ u : Q(p, hs, ω)) = 0 ↔ u ∈ N(p, hs, ω) :=
  Submodule.Quotient.mk_eq_zero _

/-- Paper: (11.2.2.1), p. 489. The prime quotient is separable in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_separable (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    TopologicalSpace.SeparableSpace Q(p, hs, ω) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology W(s) := Lp.SecondCountableTopology
  exact (N(p, hs, ω)).isQuotientMap_mkQL.separableSpace

/-- Paper: (11.2.2.1), p. 489. The prime quotient is complete in the quotient norm.
Deviation: Use the closed principal-value denominator. -/
theorem primeOrbitalSobolevQuotient_complete (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (ω : PontryaginDual C₁) :
    CompleteSpace Q(p, hs, ω) := by
  let : CompleteSpace ↥(Wω(hs, ω)) :=
    (instClosedSpectralIsotypeSec2 (F := F) h₀ hs ω).completeSpace_coe
  exact Submodule.Quotient.completeSpace (N(p, hs, ω))

attribute [instance] primeOrbitalSobolevQuotient_complete

/-! The restriction `ω(χ)` of a character of `C𝔽` is a `C₁ →ₜ* Circle`, not syntactically a
`PontryaginDual C₁`, and instance search does not unfold `PontryaginDual`. The three instances
below restate the ones above at such an argument, so that `Q(p, hs, ω(χ))` finds them. -/

instance instNormedAddCommGroupPrimeOrbitalSobolevQuotientRestrict (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) : NormedAddCommGroup Q(p, hs, ω(χ)) :=
  instNormedAddCommGroupPrimeOrbitalSobolevQuotient p hs (ω(χ))

instance instInnerProductSpacePrimeOrbitalSobolevQuotientRestrict (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) : InnerProductSpace ℂ Q(p, hs, ω(χ)) :=
  instInnerProductSpacePrimeOrbitalSobolevQuotient p hs (ω(χ))

instance instCompleteSpacePrimeOrbitalSobolevQuotientRestrict (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) : CompleteSpace Q(p, hs, ω(χ)) :=
  primeOrbitalSobolevQuotient_complete p hs (ω(χ))

local notation "P" => adelePolarSubspace F
local notation "testQuot(" χ ")" =>
  (LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P))
local notation "weightedTest(" hs ", " χ ", " f ")" =>
  ((existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
    (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk (f : P)))).val

/-- A dense map and a dense image of the denominator give the quotient seminorm
by taking the distance to representatives in the test denominator. -/
private theorem primeOrbitalSobolevQuotient_completion_norm
    {X W : Type*} [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (i : X →ₗ[ℂ] W) (D : Submodule ℂ X) (N : Submodule ℂ W)
    (hi : DenseRange i) (hN : (D.map i).topologicalClosure = N) :
    ∃ j : (X ⧸ D) →ₗ[ℂ] W ⧸ N, (∀ x, j (D.mkQ x) = N.mkQ (i x)) ∧
      (∀ x, ‖j (D.mkQ x)‖ = ⨅ v : D, ‖i x - i v.val‖) ∧ DenseRange j := by
  have hle : D.map i ≤ N := hN ▸ Submodule.le_topologicalClosure _
  let j := D.liftQ (N.mkQ.comp i) (fun x hx ↦ (Submodule.Quotient.mk_eq_zero N).2
    (hle (Submodule.mem_map_of_mem hx)))
  refine ⟨j, fun _ ↦ rfl, fun x ↦ ?_, ?_⟩
  · change ‖(Submodule.Quotient.mk (i x) : W ⧸ N)‖ = _
    rw [show ‖(Submodule.Quotient.mk (i x) : W ⧸ N)‖ = Metric.infDist (i x) (N : Set W) from
      QuotientAddGroup.norm_mk _]
    rw [← hN, Submodule.topologicalClosure_coe, Metric.infDist_closure, Metric.infDist_eq_iInf]
    change sInf (range fun y : D.map i ↦ dist (i x) y.val) = _
    apply congrArg sInf
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨v, hv, he⟩ := y.property
      exact ⟨⟨v, hv⟩, by change ‖i x - i v‖ = dist (i x) y.val; rw [he, dist_eq_norm]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨i v.val, Submodule.mem_map_of_mem v.property⟩, dist_eq_norm _ _⟩
  · have hd := N.mkQ_surjective.denseRange.comp hi N.mkQL.continuous
    exact hd.mono (by rintro _ ⟨x, rfl⟩; exact ⟨D.mkQ x, rfl⟩)

/-- A continuous averaging map which is scalar multiplication on its isotype
takes a dense family in an invariant subspace onto a family spanning a dense
subspace of the isotypic intersection. -/
private theorem primeOrbitalSobolevQuotient_completion_projection
    {X W Y : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (I : Y →L[ℂ] W) (π : W →L[ℂ] Y)
    (c : ℂ) (hc : c ≠ 0) (hfix : ∀ y, π (I y) = c • y)
    (A : Submodule ℂ W) (hA : IsClosed (A : Set W)) (z : X → W)
    (hz : closure (range z) = (A : Set W)) (hin : ∀ x, I (π (z x)) ∈ A) :
    (Submodule.span ℂ (range fun x ↦ π (z x))).topologicalClosure = A.comap I.toLinearMap := by
  let D := Submodule.span ℂ (range fun x ↦ π (z x))
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ _ (hA.preimage I.continuous)
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact hin x)
  · intro y hy
    have hm : I y ∈ closure (range z) := hz.symm ▸ hy
    have him : π (I y) ∈ D.topologicalClosure := by
      exact closure_minimal (s := range z) (t := π ⁻¹' (D.topologicalClosure : Set Y))
        (fun _ ⟨x, he⟩ ↦ he ▸ D.le_topologicalClosure (Submodule.subset_span ⟨x, rfl⟩))
        (D.isClosed_topologicalClosure.preimage π.continuous) hm
    have h := D.topologicalClosure.smul_mem c⁻¹ him
    simpa only [hfix, smul_smul, inv_mul_cancel₀ hc, one_smul] using h

/-- Scalar tests of the Pettis average give both its value on an isotype and
its commutation with any operator intertwining the compact group action. -/
private theorem primeOrbitalSobolevQuotient_completion_average
    {G E : Type*} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (μ : Measure G) [IsFiniteMeasure μ]
    (ω : PontryaginDual G) (ρ : G →* (E →L[ℂ] E))
    (A : E →L[ℂ] actionIsotype ρ ω)
    (hA : IsPettisIsotypicAverageOn μ univ ρ ω ((actionIsotype ρ ω).subtypeL.comp A))
    (M : E →L[ℂ] E) (hM : ∀ g x, M (ρ g x) = ρ g (M x)) :
    (∀ y : actionIsotype ρ ω, A y.val = (μ.real univ : ℂ) • y) ∧
      ∀ x, (A (M x)).val = M (A x).val := by
  have hcoeff (x : E) (f : StrongDual ℂ E) :
      f (A x).val = ∫ g, star (ω g : ℂ) * f (ρ g x) ∂μ := by
    obtain ⟨_, hv⟩ := hA x
    have h := LinearMap.congr_fun hv f
    change f (A x).val = ∫ g, f (star (ω g : ℂ) • ρ g x) ∂μ.restrict univ at h
    simpa only [Measure.restrict_univ, map_smul, smul_eq_mul] using h
  constructor
  · intro y
    apply Subtype.ext
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro f
    rw [hcoeff]
    simp [(mem_actionIsotype ..).1 y.property, ← Circle.coe_inv_eq_conj, Complex.real_smul]
  · intro x
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro f
    rw [hcoeff]
    have h := hcoeff x (f.comp M)
    simpa only [ContinuousLinearMap.comp_apply, hM] using h.symm

/-- Projecting a dense family of tests descends to the test quotient. Commutation of
the projection and the principal-value operator identifies the closed denominator. -/
private theorem primeOrbitalSobolevQuotient_completion_assemble
    {G Z W : Type*} [Monoid G] [TopologicalSpace G] [AddCommGroup Z] [Module ℂ Z]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (U : Submodule ℂ W) (hV : ∀ w, w ∈ U)
    (ρ : G →* (U →L[ℂ] U)) (σ : G →* (W →L[ℂ] W)) (ω : PontryaginDual G)
    (hρ : ∀ g (u : U), (ρ g u).val = σ g u.val)
    (A : U →L[ℂ] actionIsotype ρ ω) (M : U →L[ℂ] U)
    (c : ℂ) (hc : c ≠ 0) (hfix : ∀ y : actionIsotype ρ ω, A y.val = c • y)
    (hcomm : ∀ x, (A (M x)).val = M (A x).val)
    (T : Z →ₗ[ℂ] U) (hd : DenseRange T) (K : Submodule ℂ Z) (hk : ∀ z ∈ K, A (T z) = 0)
    (m : Z → Z) (hm : ∀ z, M (T z) = T (m z)) (D : Submodule ℂ (Z ⧸ K))
    (hD : D = Submodule.span ℂ (range fun z ↦ K.mkQ (m z))) (N : Submodule ℂ (actionIsotype σ ω))
    (hNdef : N = ((U.subtype.comp M.toLinearMap).range.topologicalClosure).comap (actionIsotype σ ω).subtype) :
    ∃ (i : (Z ⧸ K) →ₗ[ℂ] actionIsotype σ ω) (j : ((Z ⧸ K) ⧸ D) →ₗ[ℂ] (actionIsotype σ ω ⧸ N)),
      (∀ z, (i (K.mkQ z)).val = (A (T z)).val.val) ∧
      (∀ z, j (D.mkQ (K.mkQ z)) = N.mkQ (i (K.mkQ z))) ∧
      (∀ u, ‖j (D.mkQ u)‖ = ⨅ v : D, ‖i u - i v.val‖) ∧ DenseRange j := by
  let localIso := actionIsotype ρ ω
  let ambientIso := actionIsotype σ ω
  let up : localIso →L[ℂ] ambientIso :=
    (U.subtypeL.comp localIso.subtypeL).codRestrict ambientIso fun u ↦ by
      apply (mem_actionIsotype ..).2
      intro g
      change σ g u.val.val = _
      rw [← hρ g u.val, (mem_actionIsotype ..).1 u.property g]
      rfl
  let down : W →L[ℂ] U := (ContinuousLinearMap.id ℂ W).codRestrict U hV
  let proj := up.comp (A.comp down)
  have hidentity (y : ambientIso) : proj y.val = c • y := by
    let y' : localIso := ⟨down y.val, (mem_actionIsotype ..).2 fun g ↦ Subtype.ext (by
      change (ρ g (down y.val)).val = (ω g : ℂ) • y.val
      rw [hρ]; exact (mem_actionIsotype ..).1 y.property g)⟩
    change up (A y'.val) = c • y
    rw [hfix, map_smul]
    rfl
  let i := K.liftQ (up.toLinearMap.comp (A.toLinearMap.comp T)) fun z hz ↦ by
    change up (A (T z)) = 0
    rw [hk z hz, map_zero]
  have hsurj : Surjective (up.comp A) := by
    intro y
    refine ⟨c⁻¹ • down y.val, ?_⟩
    rw [map_smul]
    change c⁻¹ • proj y.val = y
    rw [hidentity, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hi : DenseRange i := (hsurj.denseRange.comp hd (up.comp A).continuous).mono
    (by rintro _ ⟨z, rfl⟩; exact ⟨K.mkQ z, rfl⟩)
  let R := (U.subtype.comp M.toLinearMap).range
  let f := U.subtypeL.comp M
  let z := fun z ↦ f (T z)
  have hz : closure (range z) = (R.topologicalClosure : Set W) := by
    change closure (range (f ∘ T)) = closure (range f)
    rw [Set.range_comp]
    exact le_antisymm (closure_mono (image_subset_range _ _))
      (closure_minimal (f.continuous.range_subset_closure_image_dense hd) isClosed_closure)
  have hN : (D.map i).topologicalClosure = N := by
    have hspan : D.map i = Submodule.span ℂ (range fun x ↦ proj (z x)) := by
      rw [hD, Submodule.map_span, ← Set.range_comp]
      apply congrArg (Submodule.span ℂ)
      apply congrArg range
      funext x
      change up (A (T (m x))) = up (A (M (T x)))
      rw [hm]
    rw [hspan, hNdef]
    apply primeOrbitalSobolevQuotient_completion_projection ambientIso.subtypeL proj c hc hidentity
      R.topologicalClosure R.isClosed_topologicalClosure z hz
    intro x
    apply R.le_topologicalClosure
    exact ⟨(A (T x)).val, (congrArg Subtype.val (hcomm (T x))).symm⟩
  obtain ⟨j, hj, hjnorm, hjdense⟩ := primeOrbitalSobolevQuotient_completion_norm i D N hi hN
  exact ⟨i, j, fun _ ↦ rfl, fun z ↦ hj (K.mkQ z), hjnorm, hjdense⟩

/-- On a test in the restricted homogeneous theta kernel the weighted average vanishes,
since its homogeneous class is the zero polar-free class. -/
private theorem primeOrbitalSobolevQuotient_completion_kernel (χ : PontryaginDual C𝔽)
    {s : ℝ} (hs : 0 ≤ s) (f : P) (hf : f ∈ testQuot(χ)) :
    (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
      (globalThetaSobolevInclusion F 0 h₀ hs (Submodule.Quotient.mk f)) = 0 := by
  let h := exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) h₀ hs (ω(χ))
  have he : (Submodule.Quotient.mk f.val : _ ⧸ (homogeneousAdelicThetaLinearMap F (ω(χ))).ker) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 hf
  have hv := (h.choose_spec.2.2 f 0 he.symm).1
  exact hv.symm.trans h.choose.map_zero


/-- Paper: Paragraph after (11.2.2.1), p. 490.
The §7.4 test quotient maps densely into the Sobolev quotient. Its pulled-back norm
is the quotient seminorm of the weighted tests modulo the test principal-value image.
Deviation: Take the separated completion for the potentially degenerate seminorm. -/
theorem primeOrbitalSobolevQuotient_completion (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s) :
    ∃ (i : (P ⧸ testQuot(χ)) →ₗ[ℂ] Wω(hs, ω(χ)))
      (j : FiniteNuclearityQuotient χ p →ₗ[ℂ] Q(p, hs, ω(χ))),
      (∀ f : P, ((i ((testQuot(χ)).mkQ f)) : W(s)) = weightedTest(hs, χ, f)) ∧
      (∀ f : P,
        j ((finiteNuclearityDenominator χ p).mkQ ((testQuot(χ)).mkQ f)) =
          (N(p, hs, ω(χ))).mkQ (i ((testQuot(χ)).mkQ f))) ∧
      (∀ u : P ⧸ testQuot(χ),
        ‖j ((finiteNuclearityDenominator χ p).mkQ u)‖ =
          ⨅ v : finiteNuclearityDenominator χ p, ‖i u - i v.val‖) ∧ DenseRange j := by
  let U := globalThetaSobolev F 0 h₀ hs
  let J := globalThetaSobolevInclusion F 0 h₀ hs
  let K₀ := (LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype
  let T := J.toLinearMap.comp K₀.mkQ
  let R := (exists_globalThetaSobolevAction (F := F) 0 h₀ hs).choose
  let ρ := R.comp (ideleClassNorm F).ker.subtype
  let σ := (hardySobolevTranslation μ𝔽 m𝔽 0 0 s h₀ hs).comp (ideleClassNorm F).ker.subtype
  let A := (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose
  let M := globalThetaSobolevPrincipalValue F (Sₚ(p)) 0 hs
  let m (f : P) : P := ⟨adelePrincipalValue F (Sₚ(p)) f.val, nuclearityPrincipalValue_mem_polar p f⟩
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hmass : (μ₁.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos.ne')
  have hA : IsPettisIsotypicAverageOn μ₁ univ ρ (ω(χ)) ((actionIsotype ρ (ω(χ))).subtypeL.comp A) :=
    (existsUnique_globalThetaSobolevAverage (F := F) (a := 0) h₀ hs (ω(χ))).exists.choose_spec.1
  have hM (g : C₁) (y : U) : M (ρ g y) = ρ g (M y) :=
    globalThetaSobolevPrincipalValue_equivariant (Sₚ(p)) 0 hs g y
  have hraw := primeOrbitalSobolevQuotient_completion_average (G := C₁) (E := ↥U) μ₁ (ω(χ)) ρ A hA M hM
  have hU (w : W(s)) : w ∈ U := by
    exact closure_minimal (s := range fun x : GlobalPolarFreeThetaSpace F ↦ (J x).val)
      (t := (U : Set W(s))) (by rintro _ ⟨x, rfl⟩; exact (J x).property)
      (globalThetaSobolev_closed_complete_separable (F := F) 0 h₀ hs).1
      (denseRange_globalTheta_zeroLine (F := F) hs w)
  have hρ (g : C₁) (y : U) : (ρ g y).val = σ g y.val :=
    (exists_globalThetaSobolevAction (F := F) 0 h₀ hs).choose_spec.1 g.val y
  have hd : DenseRange T := (globalThetaSobolev_dense (F := F) 0 h₀ hs).comp
    K₀.mkQ_surjective.denseRange J.continuous
  have hm (f : P) : M (T f) = T (m f) :=
    globalThetaSobolevPrincipalValue_apply (Sₚ(p)) 0 hs f
  have hk (f : P) (hf : f ∈ testQuot(χ)) : A (T f) = 0 := by
    dsimp only [A, T, J, K₀, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.mkQ_apply]
    exact primeOrbitalSobolevQuotient_completion_kernel χ hs f hf
  have hD : finiteNuclearityDenominator χ p =
      Submodule.span ℂ (range fun z : P ↦ (testQuot(χ)).mkQ (m z)) := by
    unfold finiteNuclearityDenominator
    simp only [m, Submodule.mkQ_apply]
  have hN : N(p, hs, ω(χ)) =
      ((U.subtype.comp M.toLinearMap).range.topologicalClosure).comap (actionIsotype σ (ω(χ))).subtype := by
    unfold orbitalSobolevSubmodule
    dsimp only [U, M, σ]
  have hresult := primeOrbitalSobolevQuotient_completion_assemble (G := C₁) (Z := ↥P) (W := W(s))
    U hU ρ σ (ω(χ)) hρ A M _ hmass hraw.1 hraw.2 T hd (testQuot(χ)) hk m hm
    (finiteNuclearityDenominator χ p) hD (N(p, hs, ω(χ))) hN
  obtain ⟨i, j, hi, hj, hnorm, hjdense⟩ := hresult
  let toTestQuotient : FiniteNuclearityQuotient χ p →ₗ[ℂ]
      ((P ⧸ testQuot(χ)) ⧸ finiteNuclearityDenominator χ p) :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine ⟨i, j.comp toTestQuotient, ?_, ?_, ?_, ?_⟩
  · exact hi
  · exact hj
  · exact hnorm
  · exact hjdense

variable (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
  (ω : PontryaginDual (ideleClassNorm F).ker)

local notation "Aω(" φ ")" => ContinuousLinearMap.restrict (A(hs, φ))
  (hardySobolevTestAction_preserves_spectralIsotype (F := F) h₀ hs ω φ)

/-- Paper: (11.2.2.1)–(11.2.2.3), pp. 489–490.
Convolution preserves the closed principal-value subspace of the zero-line isotype.
Deviation: Use the closure of the principal-value image. -/
theorem primeOrbitalSobolevSubmodule_convolution_invariant (φ : BruhatCompactSupport C𝔽) :
    N(p, hs, ω) ≤ ((N(p, hs, ω)).mkQL.comp (Aω(φ))).ker := by sorry

/-- An operator whose composite with the quotient map kills the denominator descends uniquely. -/
private theorem existsUnique_primeOrbitalSobolevConvolution_lift
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (N : Submodule ℂ E) (A : E →L[ℂ] E)
    (hN : N ≤ (N.mkQL.comp A).ker) :
    ∃! C : (E ⧸ N) →L[ℂ] (E ⧸ N),
      ∀ u : E, C (N.mkQ u) = N.mkQ (A u) := by
  let C : (E ⧸ N) →L[ℂ] (E ⧸ N) := N.liftQL (N.mkQL.comp A) hN
  refine ⟨C, fun u ↦ rfl, ?_⟩
  intro D hD
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨u, rfl⟩ := N.mkQ_surjective q
  exact hD u

/-- Paper: (11.2.2.3), p. 490.
The action on representatives determines a unique continuous linear map on the prime quotient.
Deviation: Use the closed principal-value denominator. -/
theorem existsUnique_primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :
    ∃! C : Q(p, hs, ω) →L[ℂ] Q(p, hs, ω), ∀ u : Wω(hs, ω),
      C ((N(p, hs, ω)).mkQ u) = (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact existsUnique_primeOrbitalSobolevConvolution_lift
    (N(p, hs, ω)) (Aω(φ))
    (primeOrbitalSobolevSubmodule_convolution_invariant (F := F) p hs ω φ)

/-- Paper: (11.2.2.3), p. 490.
The prime orbital action is the convolution operator descended to the zero-line quotient.
Deviation: Use the closed principal-value denominator. -/
def primeOrbitalSobolevConvolution (φ : BruhatCompactSupport C𝔽) :=
  (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose

/-- Paper: (11.2.2.3), p. 490.
The orbital convolution of a quotient class is the class of the representative's convolution. -/
theorem primeOrbitalSobolevConvolution_mkQ (φ : BruhatCompactSupport C𝔽) (u : Wω(hs, ω)) :
    primeOrbitalSobolevConvolution (F := F) p hs ω φ ((N(p, hs, ω)).mkQ u) =
      (N(p, hs, ω)).mkQ (Aω(φ) u) := by
  exact (existsUnique_primeOrbitalSobolevConvolution (F := F) p hs ω φ).exists.choose_spec u

-- TODO(paper-gap): Corollary 11.2.0.5 bounds the jets but gives no upper
-- bound on their biorthogonals. The single-prime trace proof needs its own
-- estimate. For the §11.2.0 basis at one prime, multiplication by
-- |g|^(2πi / log p) shifts the jets unitarily and permutes their
-- biorthogonals. There are only finitely many orbits, including jet order.
-- In (11.2.2.12) the displayed summands act on the primal quotient. For
-- the transpose the input is a functional ℓ and each term is ℓ(ψⱼ) A'ηⱼ.
-- Page 496 invokes this expansion on PW levels and needs a common level
-- for its chosen representatives as well as the kernel comparison.

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
variable (h₁ : 1 < s) (_hdeg : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
variable (_hχ : ∀ v ∈ (finite_nuclearityPlacesAbove (F := F) p).toFinset,
  (ideleClassNormTwist χ 0).IsUnramifiedAt v)

include _hdeg _hχ

local notation "hs₁" => (zero_lt_one.trans h₁).le
local notation "OrbQ" => Q(p, hs₁, ω(χ))
local notation "OrbA(" φ ")" => primeOrbitalSobolevConvolution (F := F) p hs₁ (ω(χ)) φ

namespace PrimeOrbitalTraceProof

omit _hdeg _hχ

open Filter Function Set NumberField MeasureTheory IsDedekindDomain
open scoped NNReal NumberField.AdeleRing Topology
local notation "frec(" t ")" => ((t:ℝ):ℂ)*Complex.I
local notation "period(" p ")" => 2 * Real.pi / Real.log ((HeightOneSpectrum.asIdeal p).absNorm:ℝ)

private theorem orbital_prime_factor_period (p : HeightOneSpectrum (𝓞 ℚ)) (v : V)
    (hv : v.under (𝓞 ℚ) = p) :
    ((v.asIdeal.absNorm : ℕ) : ℂ) ^ (-frec(period(p))) = 1 := by
  have : v.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩
  let d := v.asIdeal.inertiaDeg (𝓞 ℚ)
  have hq : v.asIdeal.absNorm = p.asIdeal.absNorm ^ d :=
    (Ideal.absNorm_pow_inertiaDeg p.asIdeal v.asIdeal).symm
  have hpos : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  have hh : 0 < Real.log (p.asIdeal.absNorm : ℝ) :=
    Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p)
  rw [show (v.asIdeal.absNorm:ℂ) = ((v.asIdeal.absNorm:ℝ):ℂ) by norm_cast,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),← Complex.ofReal_log hpos.le]
  rw [hq,Nat.cast_pow,Real.log_pow]
  apply (Complex.exp_eq_one_iff).mpr
  refine ⟨-(d : ℤ),?_⟩
  have hc : Complex.log (p.asIdeal.absNorm:ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast,← Complex.ofReal_log (by positivity)]
    exact Complex.ofReal_ne_zero.mpr hh.ne'
  push_cast
  field_simp [hc]

/-- A common period preserves every local Euler factor, including at collisions. -/
private theorem orbital_prime_mult_periodic (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ)) :
    Function.Periodic (fun t : ℝ ↦ orbitalEulerMultiplicity χ (Sₚ(p)) (frec(t))) (period(p)) := by
  classical
  intro t
  dsimp only
  rw [orbitalEulerMultiplicity_eq_card,orbitalEulerMultiplicity_eq_card]
  congr 1
  apply Finset.filter_congr
  intro v hv
  have hv' : v.under (𝓞 ℚ) = p := (Set.Finite.mem_toFinset _).mp hv
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos.ne'
  have he : (v.asIdeal.absNorm:ℂ)^(-frec(t+period(p))) = (v.asIdeal.absNorm:ℂ)^(-frec(t)) := by
    rw [show (-frec(t+period(p))) = -frec(t) + -frec(period(p)) by push_cast; ring,
      Complex.cpow_add _ _ hq,orbital_prime_factor_period p v hv',mul_one]
  simp only [finiteHeckeEulerFactor]
  simp_rw [he]

private theorem orbital_product_analytic (χ : PontryaginDual C𝔽) (S : Finset V)
    (z : ℂ) : AnalyticAt ℂ (reciprocalPartialHeckeEulerProduct χ S) z := by
  have h : ∀ v ∈ S, AnalyticAt ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) z := by
    intro v _
    have hq : (Ideal.absNorm v.asIdeal : ℂ) ∈ Complex.slitPlane :=
      Complex.natCast_mem_slitPlane.mpr ((Ideal.absNorm_eq_zero_iff).not.mpr v.ne_bot)
    classical
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun s ↦
          1 - (ideleClassNormTwist χ 0).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv]
      rw [this]
      have hn : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := Complex.slitPlane_ne_zero hq
      simp_rw [Complex.cpow_def_of_ne_zero hn]
      exact analyticAt_const.sub (analyticAt_const.mul (analyticAt_const.mul analyticAt_id.neg).cexp')
    · have : (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) = fun _ ↦ 1 := by
        funext s
        rw [finiteHeckeEulerFactor, ite_eq_right hv, inv_one]
      rw [this]
      exact analyticAt_const
  have := Finset.analyticAt_prod S h
  convert this using 1
  funext s
  simp [reciprocalPartialHeckeEulerProduct]

private theorem orbital_jet_compact_finite (χ : PontryaginDual C𝔽) (S : Finset V) (s D : ℝ) :
    {j : OrbitalJetIndex χ S s | j.val.1 ∈ Icc 0 D}.Finite := by
  classical
  let Z := reciprocalPartialHeckeEulerProduct χ S
  let E := {z : ℂ | meromorphicOrderAt Z z = 0 ∨ meromorphicOrderAt Z z = ⊤}
  let I := (fun t : ℝ ↦ frec(t)) '' Icc 0 D
  have hI : IsCompact I := isCompact_Icc.image (Complex.continuous_ofReal.mul continuous_const)
  have hm : MeromorphicOn Z univ := fun z _ ↦ (orbital_product_analytic χ S z).meromorphicAt
  have hc : E ∈ codiscreteWithin I := (codiscreteWithin_mono (subset_univ I)) (by
    simpa [E] using hm.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top)
  have hZ := hI.finite_sdiff_of_mem_codiscreteWithin hc
  have ht : {t : ℝ | t ∈ Icc 0 D ∧ 0 < orbitalEulerMultiplicity χ S (frec(t))}.Finite := by
    apply Set.Finite.of_finite_image (f := fun t : ℝ ↦ frec(t)) (hi := fun x _ y _ h ↦ by simpa using congrArg Complex.im h)
    apply hZ.subset
    rintro _ ⟨t,⟨hv,hn⟩,rfl⟩
    refine ⟨⟨t,hv,rfl⟩,fun H ↦ ?_⟩
    change 0 < (meromorphicOrderAt Z _).untop₀.toNat at hn
    rcases H with h | h <;> simp [h] at hn
  apply Set.Finite.of_finite_image (f := Subtype.val) (hi := Subtype.val_injective.injOn)
  apply (ht.prod (Finset.range (Nat.ceil ((s-1)/2))).finite_toSet).subset
  rintro _ ⟨j,hj,rfl⟩
  have hlt := j.property
  rw [spectralBoundaryMultiplicity,lt_min_iff] at hlt
  exact ⟨⟨hj,Nat.zero_lt_of_lt hlt.1⟩,Finset.mem_range.mpr hlt.2⟩

/-- Every jet is translated into one finite set by an injective shift of the
entire fixed-character index type, preserving each log-power order. -/
private theorem orbital_prime_finite_orbits (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ)) (s : ℝ) :
    let J := OrbitalJetIndex χ (Sₚ(p)) s
    ∃ S : Finset J, ∀ j : J, ∃ r : ℝ, ∃ σ : J ↪ J, σ j ∈ S ∧
      ∀ i : J, (σ i).val = (i.val.1+r,i.val.2) := by
  classical
  intro J
  let D := period(p)
  have hD : 0 < D := div_pos Real.two_pi_pos (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p))
  let S := (orbital_jet_compact_finite χ (Sₚ(p)) s D).toFinset
  refine ⟨S,fun j ↦ ?_⟩
  let k : ℤ := ⌊j.val.1/D⌋
  let r : ℝ := -(k:ℝ)*D
  have per : Function.Periodic (fun t : ℝ ↦ orbitalEulerMultiplicity χ (Sₚ(p)) (frec(t))) r := by
    simpa only [Int.cast_neg,r,D] using (orbital_prime_mult_periodic χ p).int_mul (-k)
  let σ (i : J) : J := ⟨(i.val.1 + r,i.val.2),by
    change i.val.2 < spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ (Sₚ(p)) (frec(i.val.1+r)))
    exact (congrArg (fun m ↦ i.val.2 < spectralBoundaryMultiplicity s m) (per i.val.1)).mpr i.property⟩
  have hσ : Injective σ := by
    intro x y h
    have ht := congrArg (fun j : J ↦ j.val.1) h
    have hn := congrArg (fun j : J ↦ j.val.2) h
    exact Subtype.ext (Prod.ext (add_right_cancel ht) hn)
  refine ⟨r,⟨σ,hσ⟩, ?_,fun _ ↦ rfl⟩
  apply (Set.Finite.mem_toFinset _).mpr
  change j.val.1 + r ∈ Icc 0 D
  rw [show j.val.1+r = j.val.1 - (k:ℝ)*D by dsimp [r]; ring]
  exact ⟨Int.sub_floor_div_mul_nonneg _ hD,(Int.sub_floor_div_mul_lt _ hD).le⟩

/-- An isometry on finite combinations of the dual labels transports primal norms by duality. -/
private theorem primal_transport {J H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (σ : J → J) (hσ : Injective σ)
    (hshift : ∀ (S : Finset J) (c : J → ℂ),
      ‖∑ i ∈ S, c i • Λ (σ i)‖ ≤ ‖∑ i ∈ S, c i • Λ i‖) (j : J) :
    ‖x j‖ ≤ ‖x (σ j)‖ := by
  apply NormedSpace.norm_le_dual_bound ℂ (x j) (norm_nonneg _)
  intro v
  refine hb.2.2.2.induction («P» := fun f : StrongDual ℂ H ↦ ‖f (x j)‖ ≤ ‖x (σ j)‖ * ‖f‖) ?_ ?_ v
  · intro f hf
    obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
    let A (i : J) := c i • Λ i
    let A' (i : J) := c i • Λ (σ i)
    have hpoint (i : J) : A i (x j) = A' i (x (σ j)) := by
      change c i • Λ i (x j) = c i • Λ (σ i) (x (σ j))
      by_cases he : j = i
      · subst i
        rw [hb.1,hb.1]
      · rw [hb.2.1 j i he,hb.2.1 (σ j) (σ i) (fun hh ↦ he (hσ hh))]
    have he : (∑ i ∈ c.support, A i) (x j) = (∑ i ∈ c.support, A' i) (x (σ j)) := by
      simp only [sum_apply,hpoint]
    change ‖(∑ i ∈ c.support, A i) (x j)‖ ≤ _
    rw [he]
    exact ((∑ i ∈ c.support, A' i).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (hshift c.support c) (norm_nonneg _)).trans_eq (mul_comm _ _))
  · exact isClosed_le ((ContinuousLinearMap.apply ℂ ℂ (x j)).continuous.norm)
      (continuous_const.mul continuous_norm)

/-- Transport in the isometric dual model and the finite representative set bound the primal family. -/
private theorem primal_bound_of_dual_orbits {J H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (x : J → H) (Λ : J → StrongDual ℂ H)
    (hB : IsSpectralMarkushevichBasis x Λ) (y : J → Y)
    (hD : ∃ D : StrongDual ℂ H →ₗᵢ[ℂ] Y, ∀ j, D (Λ j) = y j)
    (hS : ∃ S : Finset J, ∀ j, ∃ σ : J ↪ J, σ j ∈ S ∧ ∃ A : Y →ₗᵢ[ℂ] Y, ∀ k, A (y k) = y (σ k)) :
    ∃ C ≥ (0:ℝ), ∀ j, ‖x j‖ ≤ C := by
  classical
  obtain ⟨D,hD⟩ := hD
  obtain ⟨S,hS⟩ := hS
  refine ⟨∑ k ∈ S, ‖x k‖,Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _),fun j ↦ ?_⟩
  obtain ⟨σ,hmem,A,hA⟩ := hS j
  apply (primal_transport x Λ hB σ σ.injective ?_ j).trans (Finset.single_le_sum (f := fun k ↦ ‖x k‖) (fun _ _ ↦ norm_nonneg _) hmem)
  intro T c
  rw [← D.norm_map,← D.norm_map (∑ i ∈ T, c i • Λ i),← A.norm_map (D (∑ i ∈ T, c i • Λ i))]
  apply le_of_eq
  congr 1
  simp only [map_sum,map_smul,hD,hA]
/-- Identify each quotient functional with its model vector by testing on quotient representatives. -/
private theorem realize_dual_labels {J W H Y : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [SeminormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (q : W →ₗ[ℂ] H) (hq : Surjective q) (Λ : J → StrongDual ℂ H) (y : J → Y)
    (B : W → Y → ℂ) (isModelJet : Y → Prop) (N : Submodule ℂ W) (h0 : ∀ v ∈ N, q v = 0)
    (hΛ : ∀ j v, Λ j (q v) = B v (y j)) (hP : ∀ j, isModelJet (y j))
    (hrange : ∃ D : StrongDual ℂ H →ₗᵢ[ℂ] Y,
      range D = {u | isModelJet u ∧ ∀ v ∈ N, B v u = 0} ∧ ∀ ℓ v, B v (D ℓ) = ℓ (q v)) :
    ∃ D : StrongDual ℂ H →ₗᵢ[ℂ] Y, ∀ j, D (Λ j) = y j := by
  obtain ⟨D,hr,hB⟩ := hrange
  refine ⟨D,fun j ↦ ?_⟩
  have hy : y j ∈ range D := by
    rw [hr]
    exact ⟨hP j,fun v hv ↦ (hΛ j v).symm.trans ((congrArg (Λ j) (h0 v hv)).trans (map_zero _))⟩
  obtain ⟨ℓ,hℓ⟩ := hy
  have he : ℓ = Λ j := by
    apply ContinuousLinearMap.ext; intro v; obtain ⟨u,rfl⟩ := hq v
    exact (hB ℓ u).symm.trans ((congrArg (B u) hℓ).trans (hΛ j u).symm)
  exact (congrArg D he.symm).trans hℓ

/-- Multiplication by a unimodular weight is an isometry on the reciprocal Sobolev model. -/
private theorem exists_unitLpMul {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (v : X → ℂ) (hv : AEStronglyMeasurable v μ) (hunit : ∀ x, ‖v x‖ = 1) :
    ∃ U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ, ∀ y, ⇑(U y) =ᵐ[μ] fun a ↦ v a * y a := by
  let f (y : Lp ℂ 2 μ) := fun x ↦ v x * y x
  have h (y : Lp ℂ 2 μ) : MemLp (f y) 2 μ := (Lp.memLp y).congr_norm
    (hv.mul (Lp.stronglyMeasurable y).aestronglyMeasurable) (Eventually.of_forall fun x ↦ by
      simp [f,hunit])
  let A (y : Lp ℂ 2 μ) := (h y).toLp (f y)
  refine ⟨{toFun := A, map_add' := ?_, map_smul' := ?_, norm_map' := ?_}, fun y ↦ MemLp.coeFn_toLp (h y)⟩
  · intro y z
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (h (y+z)),Lp.coeFn_add y z,Lp.coeFn_add (A y) (A z),
      MemLp.coeFn_toLp (h y),MemLp.coeFn_toLp (h z)] with a hbase h₁ h₂ h₃ h₄
    change A (y+z) a = (A y + A z) a
    rw [show A (y+z) a = v a * (y+z) a from hbase,h₂]
    change v a * (y+z) a = A y a + A z a
    rw [show A y a = v a * y a from h₃,show A z a = v a * z a from h₄]
    rw [h₁]; exact mul_add _ _ _
  · intro c y
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (h (c • y)),Lp.coeFn_smul c y,Lp.coeFn_smul c (A y),
      MemLp.coeFn_toLp (h y)] with a hbase h₁ h₂ h₃
    change A (c • y) a = (c • A y) a
    rw [show A (c • y) a = v a * (c • y) a from hbase,h₂]
    change v a * (c • y) a = c * A y a
    rw [show A y a = v a * y a from h₃]
    rw [h₁]; change v a * (c * y a) = _; ring
  · intro y
    change ‖(h y).toLp (f y)‖ = ‖y‖
    rw [Lp.norm_toLp,Lp.norm_def]
    congr 1
    exact eLpNorm_congr_norm_ae (hv.mul (Lp.stronglyMeasurable y).aestronglyMeasurable) (Lp.stronglyMeasurable y).aestronglyMeasurable (Eventually.of_forall fun x ↦ by simp [f,hunit])

section Analytic
open scoped InnerProductSpace
open ContinuousLinearMap
/-- Uniform trace-norm bounds pass to limits in operator norm by testing finite positive diagonals. -/
private theorem mem_trace_bound_of_limit {H Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {l : Filter Z} [NeBot l] (maps : Z → nuclearEndomorphisms H)
    (A : H →L[ℂ] H) (M : ℝ) (hV : Tendsto (fun z ↦ (maps z).val) l (𝓝 A))
    (hM : ∀ᶠ z in l, traceNorm (maps z) ≤ M) :
    A ∈ nuclearEndomorphisms H ∧ ∀ T : nuclearEndomorphisms H, T.val = A → traceNorm T ≤ M := by
  classical
  obtain ⟨ι,b,-⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H)
  let diag (B : H →L[ℂ] H) (i : ι) := (⟪b i,B (b i)⟫_ℂ).re
  have hd (X : nuclearEndomorphisms H) : HasSum (diag (CFC.abs X.val)) (traceNorm X) :=
    hasSum_traceNorm_diagonal b X
  have h0 (B : H →L[ℂ] H) (i : ι) : 0 ≤ diag (CFC.abs B) i :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.abs_nonneg B)).re_inner_nonneg_right _
  have h (t : Finset ι) : ∑ i ∈ t, diag (CFC.abs A) i ≤ M := by
    have hc : Continuous (fun B : H →L[ℂ] H ↦ ∑ i ∈ t, diag B i) := by unfold diag; fun_prop
    apply le_of_tendsto ((hc.tendsto _).comp ((CFC.continuous_abs.tendsto A).comp hV))
    exact hM.mono fun z hz ↦ (sum_le_hasSum t (fun i _ ↦ h0 _ i) (hd (maps z))).trans hz
  exact ⟨(isNuclearOperator_iff_summable_traceNorm_diagonal b A).mpr (summable_of_sum_le (h0 A) h),
    fun T ht ↦ le_of_tendsto' (hd T) (fun s ↦ ht ▸ h s)⟩

/-- The uniformly bounded primal vectors reconstruct the operator when the norms of its rows are summable. -/
private theorem sum_rankOne_of_primal_bound {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x Λ) (C : ℝ) (hC : ∀ i, ‖x i‖ ≤ C)
    (hs : Summable (fun i ↦ ‖(Λ i).comp A‖)) :
    let R (i : J) : nuclearEndomorphisms H :=
      ⟨((Λ i).comp A).smulRight (x i),smulRight_mem_nuclearEndomorphisms _ _⟩
    HasSum (fun i ↦ (R i).val) A ∧ Summable (fun i ↦ traceNorm (R i)) := by
  classical
  intro R
  have hcost : Summable (fun i ↦ ‖(Λ i).comp A‖*‖x i‖) := Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun i ↦ mul_le_mul_of_nonneg_left (hC i) (norm_nonneg _)) (hs.mul_right C)
  have hR : Summable (fun i ↦ ‖(R i).val‖) := by simpa only [R, norm_smulRight_apply] using hcost
  have hsum := hR.of_norm.hasSum
  refine ⟨?_,by simpa only [R,traceNorm_smulRight] using hcost⟩
  convert hsum using 1
  ext w
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have he : ContinuousLinearMap.apply ℂ ℂ (A w) =
      ContinuousLinearMap.apply ℂ ℂ ((∑' i, (R i).val) w) := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨j,rfl⟩
    let ev := (ContinuousLinearMap.apply ℂ H) w
    have ht := ((Λ j).comp ev).hasSum hsum
    refine (hasSum_ite_eq j (Λ j (A w))).unique <| ht.congr_fun (fun i ↦ ?_)
    change (if i = j then _ else _) = Λ j (((Λ i).comp A w) • x i)
    rw [map_smul]
    by_cases hij : i=j
    · subst i; simp [hb.1]
    · simp [hij,hb.2.1 i j hij]
  exact fun f ↦ DFunLike.congr_fun he f

private theorem trace_bound_of_series {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : J → nuclearEndomorphisms H) (A : H →L[ℂ] H)
    (hs : HasSum (fun i ↦ (R i).val) A) (hc : Summable (fun i ↦ traceNorm (R i))) :
    A ∈ nuclearEndomorphisms H ∧ ∀ T : nuclearEndomorphisms H, T.val = A →
      traceNorm T ≤ ∑' i, traceNorm (R i) := by
  classical
  apply mem_trace_bound_of_limit (l := atTop) (fun s : Finset J ↦ ∑ i ∈ s, R i) A
    (∑' i, traceNorm (R i)) (by simpa only [HasSum,Submodule.coe_sum, SummationFilter.unconditional_filter] using hs)
  apply Eventually.of_forall; intro s
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have core := traceNorm_normedSpaceCore (H := H)
  have h0 : traceNorm (0 : nuclearEndomorphisms H) = 0 := (core.norm_eq_zero_iff 0).mpr rfl
  exact (s.le_sum_of_subadditive traceNorm h0.le core.toCore.norm_triangle R).trans
    (hc.sum_le_tsum s (fun i _ ↦ core.norm_nonneg _))

/-- The finite triangular jet expansion bounds the sum of row norms by the sums of its sampled moments. -/
private theorem sum_functionals_norm {J H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : J → StrongDual ℂ H) (A : H →L[ℂ] H) (m : J → ℕ)
    (down : (j : J) → Fin (m j + 1) → J) (M : J → ℕ → ℂ)
    (hA : ∀ j, (Φ j).comp A = ∑ n : Fin (m j + 1),
      ((m j).choose n : ℂ) • (M j (m j-n) • Φ (down j n)))
    (B : ℕ) (hm : ∀ j, m j ≤ B) (C : ℝ) (hC : 0 ≤ C) (hΦ : ∀ j, ‖Φ j‖ ≤ C)
    (hM : ∀ k : ℕ, Summable (fun j ↦ ‖M j k‖)) :
    Summable (fun j ↦ ‖(Φ j).comp A‖) := by
  classical
  let F (j : J) := ∑ k ∈ Finset.range (B+1), ‖M j k‖
  have hF : Summable F := summable_sum fun k _ ↦ hM k
  have hFpos j : 0 ≤ F j := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun j ↦ ?_)
    ((hF.mul_left ((2:ℝ)^B*C)).mul_left (B+1:ℝ))
  rw [hA]
  apply (norm_sum_le _ _).trans
  calc _ ≤ ∑ _n : Fin (m j + 1), ((2:ℝ)^B*C)*F j := by
             apply Finset.sum_le_sum; intro n _
             rw [norm_smul,norm_smul,Complex.norm_natCast,mul_left_comm,← mul_assoc]
             have hc : ((m j).choose n : ℝ) ≤ (2:ℝ)^B := by
               exact_mod_cast (Nat.choose_le_two_pow _ _).trans
                 (Nat.pow_le_pow_right (by decide) (hm j))
             have hM' : ‖M j (m j - n)‖ ≤ F j := Finset.single_le_sum
               (fun k (_ : k ∈ Finset.range (B+1)) ↦ norm_nonneg (M j k))
               (Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le ..).trans (hm j))))
             grw [hc,hΦ,hM']; ring_nf; exact le_rfl
    _ ≤ (B+1:ℝ)*(((2:ℝ)^B*C)*F j) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      gcongr
      exact_mod_cast Nat.succ_le_succ (hm j)

end Analytic
section JetModel
local notation "orbitalLogNorm" => (logIdeleClassNorm F)
local notation "W'(" s ")" => CompactIntervalSobolev μ𝔽 orbitalLogNorm 0 0 s true
local notation "μ'(" s ")" => intervalSobolevMeasure μ𝔽 orbitalLogNorm 0 0 (s) true
local notation "hI" => (le_rfl (a := (0 : ℝ)))
local notation "orbitalN(" S ", " hs ", " ω ")" => orbitalSobolevSubmodule F S hs ω
local notation "orbitalQ(" S ", " hs ", " ω ")" => (↥(Wω(hs, ω)) ⧸ orbitalN(S, hs, ω))
local notation "J(" χ ", " S ", " s ")" => OrbitalJetIndex χ S s
local notation "jet(" χ ", " t ", " m ")" => spectralZeroJet χ 0 t m
local notation "jetLp(" χ ", " S ", " hs ", " j ")" =>
  (orbitalJet_memLp (F := F) χ S hs j).toLp (jet(χ, (j).val.1, (j).val.2))

private theorem orbital_jet_basis_embedding (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (Λ : J(χ,S,s) → StrongDual ℂ orbitalQ(S,hs,ω(χ)))
    (hΛ : ∀ j (f : Wω(hs,ω(χ))), Λ j ((orbitalN(S,hs,ω(χ))).mkQ f) = spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s) f.val (jetLp(χ,S,hs,j))) :
    ∃ D : StrongDual ℂ orbitalQ(S,hs,ω(χ)) →ₗᵢ[ℂ] W'(s), ∀ j, D (Λ j) = jetLp(χ,S,hs,j) := by
  let N := orbitalN(S,hs,ω(χ))
  exact realize_dual_labels N.mkQ N.mkQ_surjective Λ (fun j ↦ jetLp(χ,S,hs,j))
    (fun v u ↦ spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s) v.val u) _ N
    (fun v hv ↦ (Submodule.Quotient.mk_eq_zero N).mpr hv) hΛ
    (fun j k ↦ orbitalJet_isotype (F := F) χ S hs j k)
    (orbitalQuotientDual_isometry_range (F := F) S hs (ω(χ)))

/-- A norm twist multiplies every model jet by the same unimodular character and preserves its derivative order. -/
private theorem orbital_jet_permute (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (r : ℝ) (σ : J(χ,S,s) ↪ J(χ,S,s)) (hσ : ∀ i, (σ i).val = (i.val.1+r,i.val.2)) :
    ∃ A : W'(s) →ₗᵢ[ℂ] W'(s), ∀ j, A (jetLp(χ,S,hs,j)) = jetLp(χ,S,hs,σ j) := by
  let η := ideleClassNormTwist (1 : PontryaginDual C𝔽) (frec(r))
  have hu (g : C𝔽) : ‖η g‖ = 1 := by
    change ‖(↑((1 : PontryaginDual C𝔽) g) : ℂ) * (((ideleClassNorm F g).val:ℝ):ℂ) ^ (frec(r))‖ = 1
    rw [norm_mul,Circle.norm_coe,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  obtain ⟨A,hA⟩ := exists_unitLpMul (μ'(s)) η η.continuous.aestronglyMeasurable hu
  refine ⟨A,fun j ↦ ?_⟩
  apply Lp.ext
  filter_upwards [hA (jetLp(χ,S,hs,j)),
    MemLp.coeFn_toLp (orbitalJet_memLp (F := F) χ S hs j),MemLp.coeFn_toLp (orbitalJet_memLp (F := F) χ S hs (σ j))]
    with g hg h₁ h₂
  rw [show A (jetLp(χ,S,hs,j)) g = η g * (jetLp(χ,S,hs,j)) g from hg,h₁,h₂]
  have hn : (((ideleClassNorm F g).val:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  rw [show (σ j).val.1 = j.val.1+r from by rw [hσ],
    show (σ j).val.2 = j.val.2 from by rw [hσ]]
  let R : ℂ := ((ideleClassNorm F g).val:ℝ)
  change ((↑((1 : PontryaginDual C𝔽) g) : ℂ) * R ^ (frec(r))) *
    ((χ g : ℂ) * R ^ ((0:ℂ)+frec(j.val.1)) * (orbitalLogNorm g:ℂ)^j.val.2) =
    (χ g : ℂ) * R ^ ((0:ℂ)+frec(j.val.1+r)) * (orbitalLogNorm g:ℂ)^j.val.2
  rw [PontryaginDual.one_apply,Circle.coe_one,one_mul,zero_add,zero_add,
    Complex.ofReal_add,add_mul,Complex.cpow_add _ _ hn]
  ring

private theorem orbital_prime_primal_norm_bounded
    (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ)) {s : ℝ} (hs : 0 ≤ s)
    [hN : IsClosed (orbitalN(Sₚ(p),hs,ω(χ)) : Set Wω(hs,ω(χ)))]
    (x : J(χ,Sₚ(p),s) → orbitalQ(Sₚ(p),hs,ω(χ))) (Λ : J(χ,Sₚ(p),s) → StrongDual ℂ orbitalQ(Sₚ(p),hs,ω(χ)))
    (hB : IsSpectralMarkushevichBasis (E := orbitalQ(Sₚ(p),hs,ω(χ))) x Λ)
    (hΛ : ∀ j (f : Wω(hs,ω(χ))), Λ j ((orbitalN(Sₚ(p),hs,ω(χ))).mkQ f) = spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s) f.val (jetLp(χ,Sₚ(p),hs,j))) :
    ∃ C ≥ (0:ℝ), ∀ j, ‖x j‖ ≤ C := by
  apply primal_bound_of_dual_orbits x Λ hB (fun i ↦ jetLp(χ,Sₚ(p),hs,i))
    (orbital_jet_basis_embedding (F := F) χ (Sₚ(p)) hs Λ hΛ)
  let B := orbital_prime_finite_orbits (F := F) χ p s
  refine ⟨B.choose,fun j ↦ ?_⟩
  let r := (B.choose_spec j).choose
  let σ := (B.choose_spec j).choose_spec.choose
  have h := (B.choose_spec j).choose_spec.choose_spec
  exact ⟨σ,h.1,orbital_jet_permute (F := F) χ (Sₚ(p)) hs r σ h.2⟩

local notation "τ(" hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 _ hI hs
local notation "act(" hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 0 0 _ hI hs φ
local notation "sample(" φ ", " χ ", " t ", " k ")" =>
  (∫ g : C𝔽, (φ : BruhatCompactSupport C𝔽).val g * spectralZeroJet χ 0 t k g ∂μ𝔽)
local notation "moment(" v ", " χ ", " t ", " k ")" =>
  (∫ g : C𝔽, (v : W(_)) g * spectralZeroJet χ 0 t k g ∂μ𝔽)

private theorem orbitalJet_continuous (χ : PontryaginDual C𝔽) (t : ℝ) (k : ℕ) :
    Continuous (spectralZeroJet χ 0 t k) := by
  have h : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    Real.continuousOn_log.comp_continuous (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
      fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  exact (ideleClassNormTwist χ ((0 : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp h).pow k)

/-- The reciprocal Sobolev density is positive, so its null sets are Haar-null. -/
private theorem orbital_jet_ae {s : ℝ} {p : C𝔽 → Prop} (h : ∀ᵐ g ∂(μ'(s)), p g) : ∀ᵐ g ∂μ𝔽, p g := by
  have hn : Measurable orbitalLogNorm := Real.measurable_log.comp ((measurable_coe_nnreal_real).comp
    ((Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous).measurable))
  have hd : Measurable (intervalSobolevDensity 0 0 s) := by unfold intervalSobolevDensity; fun_prop
  apply (withDensity_absolutelyContinuous' (μ := μ𝔽) ((hd.comp hn).inv.ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr ?_)).ne')).ae_le h
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

private theorem orbital_jet_ambient (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (j : J(χ,S,s)) : ∃ L : StrongDual ℂ W(s), ∀ v : W(s),
    Integrable (fun g ↦ v g * jet(χ,j.val.1,j.val.2) g) μ𝔽 ∧
    L v = moment(v,χ,j.val.1,j.val.2) ∧
    L v = spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s) v (jetLp(χ,S,hs,j)) := by
  let hM : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let T := (modulatedIntervalSobolev_dual m𝔽 hM μ𝔽 0 0 s hI hs).exists.choose
  let L := T.symm (jetLp(χ,S,hs,j))
  have he : T L = jetLp(χ,S,hs,j) := T.apply_symm_apply _
  have hae : ⇑(T L) =ᵐ[μ𝔽] jet(χ,j.val.1,j.val.2) := he ▸ orbital_jet_ae (MemLp.coeFn_toLp _)
  refine ⟨L,fun v ↦ ?_⟩
  have hv := (modulatedIntervalSobolev_dual m𝔽 hM μ𝔽 0 0 s hI hs).exists.choose_spec L v
  change Integrable (fun g ↦ v g * T L g) μ𝔽 ∧ L v = ∫ g, v g * T L g ∂μ𝔽 at hv
  have heq := hae.mono fun g hg ↦ congrArg (v g * ·) hg
  exact ⟨hv.1.congr heq,hv.2.trans (integral_congr_ae heq),he ▸ hv.2⟩

private theorem orbital_jet_translated_moment (χ : PontryaginDual C𝔽) {s : ℝ} (hs : 0 ≤ s)
    (t : ℝ) (m : ℕ) (v : W(s)) (hint : ∀ k ≤ m, Integrable (fun x ↦ v x * jet(χ,t,k) x) μ𝔽)
    (g : C𝔽) :
    moment(τ(hs) g v,χ,t,m) =
      ∑ k : Fin (m+1), ((m.choose k : ℂ)*jet(χ,t,m-k) g)*moment(v,χ,t,k) := by
  let T := ideleClassNormTwist χ ((0:ℂ)+frec(t))
  let L (y : C𝔽) : ℂ := orbitalLogNorm y
  let c (i : ℕ) := (m.choose i : ℂ)*(T g * L g^(m-i))
  have hl (y : C𝔽) : L (g*y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul,Units.val_mul,NNReal.coe_mul,Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero) (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero),
      Complex.ofReal_add,add_comm]
  have hsum (y : C𝔽) : v y * jet(χ,t,m) (g*y) =
      ∑ i ∈ Finset.range (m+1), c i * (v y * jet(χ,t,i) y) := by
    change v y * (T (g*y) * L (g*y)^m) = _
    rw [map_mul,hl,add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    change v y * (T g * T y * (L y ^ i * L g ^ (m-i) * (m.choose i :ℂ))) =
      ((m.choose i : ℂ)*(T g* L g^(m-i))) * (v y*(T y*L y^i))
    ring
  let H (y : C𝔽) := v (g⁻¹*y) * jet(χ,t,m) y
  calc _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
             ((hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s hI hs g v).mono fun y hy ↦ congrArg (· * jet(χ,t,m) y) hy)
       _ = ∫ y, H (g*y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
       _ = ∫ y, v y * jet(χ,t,m) (g*y) ∂μ𝔽 := by simp only [H,inv_mul_cancel_left]
       _ = ∑ i ∈ Finset.range (m+1), c i * moment(v,χ,t,i) := by
         simp_rw [hsum]
         rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
         simp_rw [integral_const_mul]
       _ = _ := (Fin.sum_univ_eq_sum_range (fun i ↦ c i * moment(v,χ,t,i)) _).symm

/-- Translation expands each logarithmic jet into the lower jets over the same ordinate. -/
private theorem orbital_jet_action (χ : PontryaginDual C𝔽) (S : Finset V) {s : ℝ} (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (v : W(s)) (j : J(χ,S,s)) :
    moment(act(hs,φ) v,χ,j.val.1,j.val.2) =
      ∑ n : Fin (j.val.2+1), ((j.val.2.choose n : ℂ) * sample(φ,χ,j.val.1,j.val.2-n)) *
        moment(v,χ,j.val.1,n) := by
  obtain ⟨L,hL⟩ := orbital_jet_ambient (F := F) χ S hs j
  have hi (n : ℕ) (hn : n ≤ j.val.2) : Integrable (fun g ↦ v g * jet(χ,j.val.1,n) g) μ𝔽 :=
    ((orbital_jet_ambient (F := F) χ S hs ⟨(j.val.1,n),hn.trans_lt j.property⟩).choose_spec v).1
  let τ := τ(hs)
  have hP := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 m𝔽 0 0 s hI hs).choose_spec.2 φ v
  have he := congrArg (fun q : PettisWeakCompletion W(s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(s)) from q) L) hP.2
  change L (act(hs,φ) v) = ∫ g, L (φ.val g • τ g v) ∂μ𝔽 at he
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hj (k : ℕ) : Integrable (fun g ↦ φ.val g * jet(χ,j.val.1,k) g) μ𝔽 :=
    (hφ.mul (orbitalJet_continuous (F := F) χ j.val.1 k)).integrable_of_hasCompactSupport φ.property.2.mul_right
  let z (n : Fin (j.val.2+1)) := (j.val.2.choose n : ℂ)*moment(v,χ,j.val.1,n)
  rw [← (hL _).2.1,he]
  calc
    _ = ∫ g, ∑ n : Fin (j.val.2+1), z n * (φ.val g * jet(χ,j.val.1,j.val.2-n) g) ∂μ𝔽 := by
      apply integral_congr_ae; filter_upwards with g
      rw [map_smul,(hL _).2.1,orbital_jet_translated_moment (F := F) χ hs j.val.1 j.val.2 v hi g,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro n _; dsimp only [z]; ring
    _ = _ := by
      rw [integral_finsetSum _ fun n _ ↦ (hj _).const_mul (z n)]
      simp_rw [integral_const_mul]
      apply Finset.sum_congr rfl; intro n _; dsimp only [z]; ring

private theorem comp_quotient_rows {J E H W : Type*} [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    (q : E → H) (hq : Surjective q) (i : E → W) (L : J → StrongDual ℂ H)
    (A : H →L[ℂ] H) (a : E → E) (b : W → W) (hA : ∀ w, A (q w) = q (a w))
    (ha : ∀ w, i (a w) = b (i w)) (M : J → W → ℂ) (hM : ∀ j w, L j (q w) = M j (i w))
    (m : J → ℕ) (down : (j : J) → Fin (m j+1) → J) (c : (j : J) → Fin (m j+1) → ℂ)
    (hrow : ∀ j w, M j (b w) = ∑ k : Fin (m j+1), ((m j).choose k : ℂ) * c j k * M (down j k) w) :
    ∀ j, (L j).comp A = ∑ k : Fin (m j+1), ((m j).choose k : ℂ) • (c j k • L (down j k)) := by
  intro j
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := hq v
  rw [ContinuousLinearMap.comp_apply,hA,hM,ha,hrow]
  simp only [sum_apply,smul_apply,smul_eq_mul,hM,mul_assoc]
local notation "downJet[" j ", " k "]" =>
  ⟨((j).val.1,(k).val),(Nat.le_of_lt_succ (k).isLt).trans_lt (j).property⟩

private theorem orbital_jet_action_descend (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (Λ : J(χ,Sₚ(p),s) → StrongDual ℂ orbitalQ(Sₚ(p),hs,ω(χ)))
    (hΛ : ∀ j (f : Wω(hs,ω(χ))), Λ j ((orbitalN(Sₚ(p),hs,ω(χ))).mkQ f) =
      spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s) f.val (jetLp(χ,Sₚ(p),hs,j))) :
    ∀ j, (Λ j).comp (primeOrbitalSobolevConvolution (F := F) p hs (ω(χ)) φ) =
      ∑ k : Fin (j.val.2+1), (j.val.2.choose k : ℂ) •
        (sample(φ,χ,j.val.1,j.val.2-k) • Λ (downJet[j,k])) := by
  let S := Sₚ(p)
  let α := ω(χ)
  let q := (orbitalN(S,hs,α)).mkQ
  refine comp_quotient_rows q (orbitalN(S,hs,α)).mkQ_surjective (fun v : Wω(hs,α) ↦ v.val) Λ
    (primeOrbitalSobolevConvolution (F := F) p hs α φ) _ (act(hs,φ))
    (primeOrbitalSobolevConvolution_mkQ (F := F) p hs α φ) (fun _ ↦ rfl)
    (fun (j : J(χ,S,s)) (w : W(s)) ↦ moment(w,χ,j.val.1,j.val.2)) ?_ _ (fun j k ↦ downJet[j,k]) _ ?_
  · intro j w
    apply (hΛ j w).trans
    apply integral_congr_ae
    exact (orbital_jet_ae (MemLp.coeFn_toLp (orbitalJet_memLp (F := F) χ S hs j))).mono fun g hg ↦ congrArg (w.val g * ·) hg
  · intro j w
    exact orbital_jet_action (F := F) χ S hs φ w j

open scoped SchwartzMap FourierTransform
local notation "𝒟" => BruhatCompactSupport C𝔽
local notation "normSection(" r ")" =>
  (QuotientGroup.mk (canonicalIdeleNormSection F (Units.mk0 (Real.exp (r)).toNNReal (by positivity))) : C𝔽)

private theorem orbitalNormSection_norm (r : ℝ) :
    ideleClassNorm F (normSection(r)) =
      Units.mk0 (Real.exp r).toNNReal (by positivity) :=
  canonicalIdeleNormSection_rightInverse F _

private theorem orbitalNormSection_mul_norm (r : ℝ) (h : C₁) :
    (((ideleClassNorm F (normSection(r) * h.val)).val : ℝ≥0) : ℝ) = Real.exp r := by
  rw [map_mul, show ideleClassNorm F h.val = 1 from h.property, mul_one, orbitalNormSection_norm,
    Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos r).le]

private theorem orbitalCompactSupport_mem_schwartz (φ : 𝒟) :
    φ.val ∈ schwartzBruhatSubmodule C𝔽 := by
  obtain ⟨m, _, hm, hms⟩ := exists_ideleClassModulation F
  have hf := bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms φ.property
  rwa [modulatedExponentialDecaySubmodule_singleton_zero] at hf

private theorem orbitalLogSchwartz {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (d : G ≃ₜ* ℝ≥0ˣ) (f : SchwartzBruhat G) :
    ∃ b : 𝓢(ℝ, ℂ), ∀ x : G, b (Real.log ((d x).val : ℝ)) = f x := by
  let m : G →ₜ* ℝ≥0ˣ := ⟨d.toMulEquiv.toMonoidHom, d.continuous⟩
  let s : ℝ≥0ˣ →ₜ* G := ⟨d.symm.toMulEquiv.toMonoidHom, d.symm.continuous⟩
  have hm : IsModulation m := ⟨d.toHomeomorph.isProperMap, by
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨d.symm t, fun h ↦ ht ((d.apply_symm_apply t).symm.trans h)⟩⟩
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SecondCountableTopology G := d.toHomeomorph.isEmbedding.secondCountableTopology
  let K := m.toMonoidHom.ker
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ : Measure K := Measure.haar
  let projector := schwartzBruhatIsotypicProjector m hm μ 1
  have hPf (u : SchwartzBruhat G) : projector u = u := by
    apply schwartzBruhatIsotypicProjector_apply_isotype
    apply (mem_actionIsotype _ _ _).2
    intro k
    have hk : (k : G) = 1 := d.injective (k.property.trans d.map_one.symm)
    change schwartzBruhatTranslationAction (G := G) (k : G) u = ((1 : PontryaginDual K) k : ℂ) • u
    rw [hk, map_one, PontryaginDual.one_apply, Circle.coe_one, one_smul]
    rfl
  obtain ⟨w, e, hw, he⟩ := schwartzBruhat_positiveReal_isotype_equiv m hm μ s d.apply_symm_apply 1
  let v := e.symm (projector.ker.mkQ f)
  have h : projector.ker.mkQ (w v) = projector.ker.mkQ f := (he v).symm.trans (e.apply_symm_apply _)
  have hmem := (Submodule.Quotient.eq _).mp h
  change projector (w v - f) = 0 at hmem
  have hwv : w v = f := sub_eq_zero.mp ((hPf _).symm.trans hmem)
  have hv (x : G) : v (d x) = f x := by
    have hh := hw v 1 (d x)
    change w v (1 * d.symm (d x)) = _ at hh
    simpa [hwv] using hh.symm
  let I : Set ℝ := {0}
  let idm := ContinuousMonoidHom.id ℝ≥0ˣ
  let u : ModulatedExponentialDecay idm I := ⟨v.val, by
    change v.val ∈ modulatedExponentialDecaySubmodule idm {0}
    rw [modulatedExponentialDecaySubmodule_singleton_zero]
    exact v.property⟩
  obtain ⟨L,hL⟩ := identityModulationExponentialDecay_equiv I (ordConnected_singleton)
    (singleton_nonempty 0)
  let z := L.symm u
  let a : I := ⟨0, rfl⟩
  refine ⟨logExponentialDecayTwist I a z, fun x ↦ ?_⟩
  refine (logExponentialDecayTwist_apply I a z _).trans ?_
  change (Real.exp (0 * _) : ℂ) * z.val _ = _
  simp only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
  exact (hL z (d x)).symm.trans ((congrArg (fun t : ModulatedExponentialDecay idm I ↦ t.val (d x))
    (L.apply_symm_apply u)).trans (hv x))

/-- Averaging a character-weighted Bruhat test over the norm-one kernel gives a Schwartz profile on the real log-norm line. -/
private theorem orbitalCharacterAverage_schwartz (χ : PontryaginDual C𝔽) (φ : 𝒟) :
    ∃ b : 𝓢(ℝ,ℂ), ∀ x : ℝ, b x = ∫ h : C₁,
      (χ (normSection(x) * h.val) : ℂ) * φ.val (normSection(x) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let c : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hc : Continuous c :=
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hcr : RightInverse c (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  let e : (C𝔽 ⧸ C₁) ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) c hcr with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hc }
  let f₀ : SchwartzBruhat C𝔽 := ⟨φ.val, orbitalCompactSupport_mem_schwartz φ⟩
  obtain ⟨twistOperator, hP⟩ := schwartzBruhat_mul_unitaryCharacter χ
  have hK : IsCompact (C₁ : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : (normOneIdeleClassTamagawaMeasure F).Regular :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.2.1
  let f₁ := schwartzBruhatCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (twistOperator f₀)
  let : CommGroup (C𝔽 ⧸ C₁) := QuotientGroup.Quotient.commGroup C₁
  let : T2Space (C𝔽 ⧸ C₁) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (C𝔽 ⧸ C₁) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨b, hb⟩ := orbitalLogSchwartz e f₁
  refine ⟨b, fun x ↦ ?_⟩
  let q : C𝔽 ⧸ C₁ := QuotientGroup.mk (normSection(x))
  have hq : Real.log ((e q).val : ℝ) = x := by
    change Real.log ((ideleClassNorm F (normSection(x))).val : ℝ) = x
    rw [orbitalNormSection_norm, Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  calc
      b x = f₁ q := (congrArg b hq.symm).trans (hb q)
      _ = ∫ h : C₁, (twistOperator f₀) (normSection(x) * h.val) ∂normOneIdeleClassTamagawaMeasure F :=
        schwartzBruhatCosetIntegral_mk C₁ (normOneIdeleClassTamagawaMeasure F) hK.isClosed (twistOperator f₀) _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        exact hP f₀ (normSection(x) * h.val)

private theorem orbitalEulerSum_logNorm_integral (σ : ℝ≥0ˣ → C𝔽) (hσ : Continuous σ)
    (hσnorm : RightInverse σ (ideleClassNorm F)) (f : C𝔽 → ℂ)
    (hfc : Continuous f) (hf : Integrable f (ideleClassTamagawaMeasure F)) :
    (∫ g, f g ∂ideleClassTamagawaMeasure F) = ∫ y : ℝ,
      ∫ h : C₁, f (σ (Units.mk0 (Real.exp y).toNNReal (by positivity)) * h.val)
        ∂normOneIdeleClassTamagawaMeasure F := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : MeasurableSpace (C𝔽 ⧸ C₁) := borel _
  let : BorelSpace (C𝔽 ⧸ C₁) := ⟨rfl⟩
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let d : C𝔽 ⧸ C₁ ≃ₜ* ℝ≥0ˣ :=
    { QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) σ hσnorm with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (isProperMap_ideleClassNorm F).continuous
      continuous_invFun := QuotientGroup.continuous_mk.comp hσ }
  let D := d.toHomeomorph.toMeasurableEquiv
  let ν := positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))
  have hν : positiveRealHaar.map D.symm = ν := D.map_symm
  have hWeil := normOneIdeleClassTamagawaMeasure_isWeil F
  have havg := weilQuotientIntegral_L1 C₁
    (isClosed_singleton.preimage (isProperMap_ideleClassNorm F).continuous)
    (ideleClassTamagawaMeasure F) (normOneIdeleClassTamagawaMeasure F) ν hWeil hf
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have he (y : ℝ) : e y = Units.mk0 (Real.exp y).toNNReal (by positivity) :=
    Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le).symm)
  have hE : positiveRealHaar = volume.map e := by
    unfold positiveRealHaar
    congr 1
    exact funext fun y ↦ (he y).symm
  rw [havg.2.2, ← hν, integral_map_equiv, hE]
  change (∫ t, lcaCosetIntegral C₁ (normOneIdeleClassTamagawaMeasure F) f (D.symm t)
    ∂volume.map e) = _
  rw [show (⇑e) = ⇑e.toMeasurableEquiv from rfl, integral_map_equiv]
  apply integral_congr_ae
  filter_upwards with y
  change lcaCosetIntegral C₁ _ f (D.symm (e y)) = _
  rw [he]
  change lcaCosetIntegral C₁ _ f (QuotientGroup.mk (σ _)) = _
  apply lcaCosetIntegral_mk
  exact (hfc.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Every fixed logarithmic moment of a compact Bruhat test is Schwartz along the unitary line. -/
private theorem orbital_schwartz_sample (χ : PontryaginDual C𝔽) (φ : 𝒟) (k : ℕ) :
    ∃ b : 𝓢(ℝ,ℂ), ∀ t : ℝ, sample(φ,χ,t,k) = b (-t/(2*Real.pi)) := by
  obtain ⟨f,hf⟩ := orbitalCharacterAverage_schwartz χ φ
  let h (y : ℝ) : ℂ := (y:ℂ)^k
  have hp : h.HasTemperateGrowth := by dsimp [h]; fun_prop
  let v := SchwartzMap.smulLeftCLM ℂ h f
  refine ⟨𝓕 v,fun t ↦ ?_⟩
  let σ : ℝ≥0ˣ → C𝔽 := fun u ↦ QuotientGroup.mk (canonicalIdeleNormSection F u)
  have hσ : Continuous σ := QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)
  have hcont : Continuous (fun g ↦ φ.val g * spectralZeroJet χ 0 t k g) :=
    (continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)).mul
      (orbitalJet_continuous (F := F) χ t k)
  have hi := hcont.integrable_of_hasCompactSupport (μ := μ𝔽) φ.property.2.mul_right
  rw [orbitalEulerSum_logNorm_integral σ hσ (canonicalIdeleNormSection_rightInverse F) _ hcont hi]
  rw [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with y
  rw [show v y = h y * f y from SchwartzMap.smulLeftCLM_apply_apply hp f y,hf]
  simp only [smul_eq_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with g
  let w := normSection(y) * g.val
  change φ.val w * (((χ w : ℂ) * ((((ideleClassNorm F w).val:ℝ):ℂ)^((0:ℂ)+frec(t)))) *
      (Real.log ((ideleClassNorm F w).val:ℝ):ℂ)^k) = _
  rw [show ((ideleClassNorm F w).val:ℝ) = Real.exp y from orbitalNormSection_mul_norm y g,
    zero_add,Real.log_exp,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos y).ne'),
    ←Complex.ofReal_log (Real.exp_pos y).le,Real.log_exp]
  have he : (↑(-2 * Real.pi * y * (-t / (2 * Real.pi))) : ℂ) * Complex.I = (y:ℂ) * frec(t) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [he]; dsimp only [w,h]; ring

private theorem orbital_schwartz_affine_summable (f : 𝓢(ℝ,ℂ)) (a b : ℝ) (hb : b ≠ 0) :
    Summable (fun n : ℤ ↦ ‖f (a + (n:ℝ)*b)‖) := by
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ b hb).toContinuousLinearEquiv
  let u := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (SchwartzMap.compSubConstCLM ℂ (-a) f)
  have hs : Summable (fun n : ℤ ↦ u (n:ℝ)) := summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    ((u.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  exact hs.norm.congr (fun n ↦ by change ‖f (b*(n:ℝ) - -a)‖ = _; rw [sub_neg_eq_add,mul_comm,add_comm])

/-- The full prime jet set embeds into the finite set of labels in one period times ℤ. -/
private theorem orbital_prime_sample_summable_direct (χ : PontryaginDual C𝔽)
    (p : HeightOneSpectrum (𝓞 ℚ)) (s : ℝ) (φ : 𝒟) (k : ℕ) :
    Summable (fun j : OrbitalJetIndex χ (Sₚ(p)) s ↦ ‖sample(φ,χ,j.val.1,k)‖) := by
  classical
  let J := OrbitalJetIndex χ (Sₚ(p)) s
  let D := period(p)
  have hD : 0 < D := div_pos Real.two_pi_pos (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm p))
  let T := (orbital_jet_compact_finite χ (Sₚ(p)) s D).toFinset
  let n (j : J) : ℤ := ⌊j.val.1/D⌋
  let a (j : J) := j.val.1 - (n j : ℝ)*D
  have hj (j : J) : j.val.2 < spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ (Sₚ(p)) (frec(a j))) := by
    have hp := (orbital_prime_mult_periodic χ p).int_mul (-(n j)) j.val.1
    change orbitalEulerMultiplicity χ (Sₚ(p)) (frec(j.val.1+((-(n j):ℤ):ℝ)*D)) = _ at hp
    have he : j.val.1+((-(n j):ℤ):ℝ)*D = a j := by dsimp [a]; push_cast; ring
    rw [he] at hp
    exact (congrArg (fun q ↦ j.val.2 < spectralBoundaryMultiplicity s q) hp).mpr j.property
  let idx (j : J) : J := ⟨(a j,j.val.2),hj j⟩
  have hidx (j : J) : idx j ∈ T := (Set.Finite.mem_toFinset _).mpr
    ⟨Int.sub_floor_div_mul_nonneg j.val.1 hD,(Int.sub_floor_div_mul_lt j.val.1 hD).le⟩
  let e (j : J) : T × ℤ := (⟨idx j,hidx j⟩,n j)
  have hinj : Injective e := by
    intro i j h
    have hbase : a i = a j := congrArg (fun z : T × ℤ ↦ z.1.val.val.1) h
    have h₁ : i.val.2 = j.val.2 := congrArg (fun z : T × ℤ ↦ z.1.val.val.2) h
    have h₂ : n i = n j := congrArg Prod.snd h
    dsimp only [a] at hbase
    rw [h₂] at hbase
    exact Subtype.ext (Prod.ext (sub_left_inj.mp hbase) h₁)
  obtain ⟨f,hf⟩ := orbital_schwartz_sample χ φ k
  let c (z : T) := -z.val.val.1 / (2*Real.pi)
  let b := -D/(2*Real.pi)
  have hb : b ≠ 0 := div_ne_zero (neg_ne_zero.mpr hD.ne') Real.two_pi_pos.ne'
  let weights (z : T × ℤ) := ‖f (c z.1 + (z.2:ℝ)*b)‖
  have hsum : Summable weights := (summable_prod_of_nonneg (fun z ↦ norm_nonneg _)).mpr
    ⟨fun r ↦ orbital_schwartz_affine_summable f (c r) b hb,(hasSum_fintype _).summable⟩
  refine (hsum.comp_injective hinj).congr fun j ↦ ?_
  rw [hf]
  change ‖f (-(j.val.1-(n j:ℝ)*D)/(2*Real.pi)+(n j:ℝ)*(-D/(2*Real.pi)))‖ = _
  congr 2
  ring

private theorem orbital_prime_card_deg (p : HeightOneSpectrum (𝓞 ℚ)) :
    (Sₚ(p)).card ≤ Module.finrank ℚ F := by
  classical
  let S := Sₚ(p)
  let e (v : S) : p.asIdeal.primesOver (𝓞 F) :=
    ⟨v.val.asIdeal, v.val.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal
      (show v.val.under (𝓞 ℚ) = p from (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp v.property)).symm⟩⟩
  have hi : Function.Injective e := fun v w h ↦
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  have hs : ∑ q : p.asIdeal.primesOver (𝓞 F), q.1.ramificationIdx (𝓞 ℚ) * q.1.inertiaDeg (𝓞 ℚ) =
      Module.finrank ℚ F := by
    rw [Ideal.sum_ramification_inertia_eq_finrank,IsFractionRing.finrank_eq (𝓞 ℚ) ℚ (𝓞 F) F]
  have hb : Fintype.card (p.asIdeal.primesOver (𝓞 F)) ≤ Module.finrank ℚ F := by
    rw [←hs, Fintype.card_eq_sum_ones]
    apply Finset.sum_le_sum; intro q _
    have := q.2.1
    have := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos (𝓞 ℚ) q.1).ne' (Ideal.inertiaDeg_pos q.1 (𝓞 ℚ)).ne')
  simpa only [Fintype.card_coe] using (Fintype.card_le_of_injective e hi).trans hb

private theorem orbital_sample_zero_mellin (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽) (t : ℝ) :
    (∫ g : C𝔽, φ.val g * spectralZeroJet χ 0 t 0 g ∂μ𝔽) = nuclearityTestMellin χ φ (((t : ℂ) * Complex.I)) := by
  apply integral_congr_ae
  filter_upwards with x
  change φ.val x * (((χ x : ℂ) * ((((ideleClassNorm F x).val:ℝ):ℂ)^((0:ℂ)+((t : ℂ) * Complex.I)))) *
      (Real.log ((ideleClassNorm F x).val:ℝ):ℂ)^0) = _
  simp only [zero_add,pow_zero,mul_one]
  rfl

open ContinuousLinearMap in
private theorem trace_tends_of_series {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (R : J → nuclearEndomorphisms H) (T : nuclearEndomorphisms H)
    (hs : HasSum (fun i ↦ (R i).val) T.val) (hc : Summable (fun i ↦ traceNorm (R i))) :
    Tendsto (fun I : Finset J ↦ traceNorm (T - ∑ j ∈ I, R j)) atTop (𝓝 0) := by
  classical
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have core := traceNorm_normedSpaceCore (H := H)
  apply squeeze_zero (fun s ↦ core.norm_nonneg _) (fun s ↦ ?_) (tendsto_tsum_compl_atTop_zero (fun i ↦ traceNorm (R i)))
  let A := T-∑ j ∈ s, R j
  have h : HasSum (fun j : {i // i ∉ s} ↦ (R j.val).val) A.val := by
    have hnc := (hs.summable.subtype (fun i ↦ i ∉ s)).hasSum
    have he : A.val = ∑' j : {i // i ∉ s}, (R j.val).val := by
      simp only [A,Submodule.coe_sub,Submodule.coe_sum]
      apply sub_eq_of_eq_add
      rw [←hs.tsum_eq,add_comm]
      exact (hs.summable.sum_add_tsum_compl (s := s)).symm
    rw [he]
    exact hnc
  exact (trace_bound_of_series (fun j : {i // i ∉ s} ↦ R j.val) A.val h
    (hc.subtype (fun i ↦ i ∉ s))).2 A rfl

open ContinuousLinearMap in
private theorem diagonal_of_triangular_rows {J H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (m : J → ℕ) (down : (j : J) → Fin (m j+1) → J) (M : J → ℕ → ℂ)
    (hd : ∀ j k, m (down j k) = k) (he : ∀ j, down j ⟨m j,Nat.lt_succ_self _⟩ = j)
    (hA : ∀ j, (Λ j).comp A = ∑ n : Fin (m j+1), ((m j).choose n : ℂ) • (M j (m j-n) • Λ (down j n))) :
    ∀ j, Λ j (A (x j)) = M j 0 := by
  classical
  intro j
  let last : Fin (m j+1) := ⟨m j,Nat.lt_succ_self _⟩
  have h := DFunLike.congr_fun (hA j) (x j)
  change Λ j (A (x j)) = _ at h
  rw [h]
  simp only [sum_apply,smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single last]
  · simp [last,he,hb.1]
  · intro k _ hk
    have hne : j ≠ down j k := fun hz ↦ hk (Fin.ext ((hd j k).symm.trans (congrArg m hz.symm)))
    rw [hb.2.1 j (down j k) hne,mul_zero,mul_zero]
  · simp

/-- A uniformly bounded biorthogonal family and summable triangular rows give both nuclearity
and convergence in trace norm to the same operator. -/
private theorem operator_of_sampled_coordinates {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →L[ℂ] H) (coordinatesMatch : (J → StrongDual ℂ H) → Prop) (m : J → ℕ)
    (down : (j : J) → Fin (m j+1) → J) (M : J → ℕ → ℂ)
    (hB : ∃ (x : J → H) (Λ : J → StrongDual ℂ H),
        IsSpectralMarkushevichBasis x Λ ∧ IsNormalizedSpectralFamily Λ ∧ coordinatesMatch Λ)
    (hP : ∀ (x : J → H) (Λ : J → StrongDual ℂ H), IsSpectralMarkushevichBasis x Λ → coordinatesMatch Λ →
        ∃ C ≥ (0:ℝ), ∀ j, ‖x j‖ ≤ C)
    (hA : ∀ Λ, coordinatesMatch Λ → ∀ j, (Λ j).comp A = ∑ n : Fin (m j+1),
       ((m j).choose n : ℂ) • (M j (m j - n) • Λ (down j n)))
    (B : ℕ) (hm : ∀ j, m j ≤ B) (hM : ∀ k, Summable (fun j ↦ ‖M j k‖))
    (hd : ∀ j k, m (down j k) = k) (he : ∀ j, down j ⟨m j,Nat.lt_succ_self _⟩=j)
    (M₀ : J → ℂ) (hM₀ : ∀ j, M j 0 = M₀ j) :
    A ∈ nuclearEndomorphisms H ∧
    ∃ (x : J → H) (Λ : J → StrongDual ℂ H),
      (∀ j, Λ j (A (x j)) = M₀ j) ∧ ∀ T : nuclearEndomorphisms H, T.val = A →
      Tendsto (fun I : Finset J ↦ traceNorm (T - ∑ j ∈ I,
        (⟨((Λ j).comp A).smulRight (x j),smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms H)))
          atTop (𝓝 0) := by
  obtain ⟨x,Λ,hb,hn,hcoords⟩ := hB
  obtain ⟨D,_,hD⟩ := hP x Λ hb hcoords
  obtain ⟨C,hC⟩ := hn.1
  have hrows := hA Λ hcoords
  have hs := sum_functionals_norm Λ A m down M hrows B hm (max C 0)
    (le_max_right _ _) (fun j ↦ (hC j).trans (le_max_left _ _)) hM
  have h := sum_rankOne_of_primal_bound A x Λ hb D hD hs
  refine ⟨(trace_bound_of_series _ A h.1 h.2).1, x, Λ, fun j ↦
    (diagonal_of_triangular_rows A x Λ hb m down M hd he hrows j).trans (hM₀ j), ?_⟩
  intro T he
  exact trace_tends_of_series _ T (he ▸ h.1) h.2

/- Elaborate the trace-norm expression over an abstract Hilbert space before applying it to
the prime quotient, whose canonical instances are supplied by the surrounding section. -/
local notation "jetOperatorConclusion" =>
  (fun (ι : Type _) (K : Type _) [n : NormedAddCommGroup K] [ip : InnerProductSpace ℂ K]
    [c : CompleteSpace K] (B : K →L[ℂ] K) (M : ι → ℂ) ↦
    B ∈ nuclearEndomorphisms K ∧ ∃ (x : ι → K) (Λ : ι → StrongDual ℂ K),
      (∀ j, Λ j (B (x j)) = M j) ∧
        ∀ T : nuclearEndomorphisms K, T.val = B →
          Tendsto (fun I : Finset ι ↦ traceNorm (T - ∑ j ∈ I,
            (⟨((Λ j).comp B).smulRight (x j), smulRight_mem_nuclearEndomorphisms _ _⟩ :
              nuclearEndomorphisms K))) atTop (𝓝 0))

/-- The prime quotient satisfies both operator conclusions with its canonical Hilbert instances. -/
private theorem orbital_prime_operator (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ))
    {s : ℝ} (hs : 1 < s) (hd : 2 * (Module.finrank ℚ F : ℝ) ≤ s)
    (hχ : ∀ v ∈ Sₚ(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v) (φ : BruhatCompactSupport C𝔽) :
    let h := (zero_lt_one.trans hs).le
    jetOperatorConclusion (J(χ,Sₚ(p),s)) (PrimeOrbitalSobolevQuotient F p h (ω(χ)))
      (primeOrbitalSobolevConvolution (F := F) p h (ω(χ)) φ)
      (fun j ↦ nuclearityTestMellin χ φ (frec(j.val.1))) := by
  intro h
  let S := Sₚ(p)
  let H := PrimeOrbitalSobolevQuotient F p h (ω(χ))
  let J := J(χ,S,s)
  have hc : 2 * (S.card : ℝ) ≤ s := le_trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast orbital_prime_card_deg (F := F) p) zero_le_two) hd
  let coordinatesMatch (Λ : J → StrongDual ℂ H) := ∀ (j : J) (f : Wω(h,ω(χ))),
    Λ j ((orbitalN(S,h,ω(χ))).mkQ f) = spectralSobolevPairing (F := F) (l := 0) (r := 0) (s := s)
      f.val (jetLp(χ,S,h,j))
  exact operator_of_sampled_coordinates (H := H) (J := J)
    (primeOrbitalSobolevConvolution (F := F) p h (ω(χ)) φ) coordinatesMatch (fun j ↦ j.val.2)
    (fun j k ↦ downJet[j,k]) (fun j k ↦ sample(φ,χ,j.val.1,k))
    (orbitalMarkushevichBasis_normalized (F := F) χ S hs hc hχ)
    (orbital_prime_primal_norm_bounded (F := F) χ p h
      (hN := instClosedOrbitalSobolevSubmoduleSec2a (F := F) S h (ω(χ))))
    (orbital_jet_action_descend (F := F) χ p h φ)
    (Nat.ceil ((s-1)/2)) (fun j ↦ (lt_min_iff.mp j.property).2.le)
    (orbital_prime_sample_summable_direct (F := F) χ p s φ)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun j ↦ nuclearityTestMellin χ φ (frec(j.val.1)))
    (fun j ↦ orbital_sample_zero_mellin (F := F) χ φ j.val.1)

end JetModel

end PrimeOrbitalTraceProof

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490. Convolution by a compactly supported
Bruhat test is a nuclear operator on the prime quotient. This is the pointwise half of the
theorem; the trace-norm continuity of the linear lift follows from it by lower
semicontinuity of the trace norm on the Fréchet stages of the test space. The printed proof
expands the transpose along the orbital Markushevich basis, (11.2.2.12), and needs a bound
on the biorthogonal vectors. For a single prime, the common period gives that bound.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_mem_nuclearEndomorphisms (φ : BruhatCompactSupport C𝔽) :
    OrbA(φ) ∈ nuclearEndomorphisms OrbQ :=
  (PrimeOrbitalTraceProof.orbital_prime_operator (F := F) χ p h₁ _hdeg _hχ φ).1

omit _hdeg _hχ in
/-- Descending a continuous linear family of endomorphisms, first to an invariant
submodule and then to its quotient, preserves linear dependence and operator-norm continuity. -/
private theorem primeOrbitalSobolevConvolution_traceNorm_continuous_descend
    {X E : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Submodule ℂ E) (N : Submodule ℂ D)
    (A : X →ₗ[ℂ] E →L[ℂ] E) (hA : Continuous A) (R : X → D →L[ℂ] D)
    (hR : ∀ x (u : D), (R x u).val = A x u.val)
    (B : X → (D ⧸ N) →L[ℂ] (D ⧸ N))
    (hB : ∀ x (u : D), B x (N.mkQ u) = N.mkQ (R x u)) :
    IsLinearMap ℂ B ∧ Continuous B := by
  have hlin : IsLinearMap ℂ B := by
    constructor
    · intro x y
      apply ContinuousLinearMap.ext
      intro q
      obtain ⟨u, rfl⟩ := N.mkQ_surjective q
      simp only [add_apply, hB, ← map_add N.mkQ]
      exact congrArg N.mkQ (Subtype.ext (by simp [hR]))
    · intro c x
      apply ContinuousLinearMap.ext
      intro q
      obtain ⟨u, rfl⟩ := N.mkQ_surjective q
      simp only [smul_apply, hB, ← map_smul N.mkQ]
      exact congrArg N.mkQ (Subtype.ext (by simp [hR]))
  refine ⟨hlin, continuous_of_continuousAt_zero (hlin.mk' B) ?_⟩
  have hbound (x : X) : ‖B x‖ ≤ ‖A x‖ := by
    refine (B x).opNorm_le_bound (norm_nonneg _) fun q ↦ ?_
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨u, hu, hnorm⟩ := Submodule.Quotient.norm_mk_lt (S := N) q
      (div_pos hε (show 0 < ‖A x‖ + 1 by positivity))
    calc
      ‖B x q‖ = ‖N.mkQ (R x u)‖ := by rw [← hu]; exact congrArg norm (hB x u)
      _ ≤ ‖(R x u).val‖ := Submodule.Quotient.norm_mk_le N _
      _ = ‖A x u.val‖ := by rw [hR]
      _ ≤ ‖A x‖ * (‖q‖ + ε / (‖A x‖ + 1)) :=
        ((A x).le_opNorm u.val).trans (mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg _))
      _ ≤ ‖A x‖ * ‖q‖ + ε := by
        have hn : ‖A x‖ / (‖A x‖ + 1) ≤ 1 :=
          (div_le_one (by positivity)).2 (le_add_of_nonneg_right zero_le_one)
        calc
          _ = ‖A x‖ * ‖q‖ + ε * (‖A x‖ / (‖A x‖ + 1)) := by ring
          _ ≤ _ := by gcongr; exact mul_le_of_le_one_right hε.le hn
  change Tendsto B (𝓝 0) (𝓝 (B 0))
  rw [hlin.map_zero]
  apply squeeze_zero_norm hbound
  simpa using hA.continuousAt.norm.tendsto (x := 0)

omit _hdeg _hχ in
/-- The trace norm of a nuclear family is lower semicontinuous in the operator norm
because it is the supremum of the finite sums of its approximation numbers. -/
private theorem primeOrbitalSobolevConvolution_traceNorm_continuous_lsc
    {X H : Type*} [TopologicalSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : X → nuclearEndomorphisms H) (h : Continuous fun x ↦ (T x).val) :
    LowerSemicontinuous (fun x ↦ traceNorm (T x)) := by
  let p (I : Finset ℕ) (x : X) := ∑ n ∈ I, approximationNumber (T x).val n
  have nn (x : X) (n : ℕ) : 0 ≤ approximationNumber (T x).val n :=
    Real.sInf_nonneg fun _ ⟨_, _, he⟩ ↦ he ▸ norm_nonneg _
  have hs (x : X) : HasSum (approximationNumber (T x).val) (traceNorm (T x)) := by
    have hmem := (mem_traceClassOperators_iff_isNuclearOperator (T x).val).2 (T x).property
    have hsum : Summable (approximationNumber (T x).val) := by simpa using hmem.2
    have he := schattenNorm_one_eq_traceNorm (T x)
    simp only [schattenNorm, Real.rpow_one, div_one] at he
    exact he ▸ hsum.hasSum
  have hle (I : Finset ℕ) (x : X) : p I x ≤ traceNorm (T x) :=
    ((hs x).summable.sum_le_tsum I (fun n _ ↦ nn x n)).trans_eq (hs x).tsum_eq
  have hbound (x : X) : BddAbove (range fun I ↦ p I x) :=
    ⟨traceNorm (T x), fun z ⟨I, he⟩ ↦ he ▸ hle I x⟩
  have he (x : X) : traceNorm (T x) = ⨆ I, p I x := by
    apply le_antisymm ?_ (ciSup_le (hle · x))
    exact le_of_tendsto (hs x) (.of_forall (fun I ↦ le_ciSup (hbound x) I))
  simp_rw [he]
  refine lowerSemicontinuous_ciSup hbound fun I ↦ Continuous.lowerSemicontinuous ?_
  apply continuous_finsetSum _ fun n _ ↦ ?_
  have hc : Continuous (fun D : H →L[ℂ] H ↦ approximationNumber D n) :=
    (LipschitzWith.of_dist_le' (K := 1) (fun D E ↦ by
      simpa only [dist_eq_norm, Real.norm_eq_abs, one_mul] using abs_approximationNumber_sub_le D E n)).continuous
  exact hc.comp h

omit _hdeg _hχ in
/-- On the strict LF test space the trace-norm seminorm is continuous on each
Fréchet stage and hence on their locally convex inductive limit. -/
private theorem primeOrbitalSobolevConvolution_traceNorm_continuous_lift
    {X H : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (hX : IsStrictLFSpace X)
    (B : X → H →L[ℂ] H) (hB : IsLinearMap ℂ B ∧ Continuous B)
    (hn : ∀ x, B x ∈ nuclearEndomorphisms H) :
    ∃ L : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (L x).val = B x) ∧
      Tendsto (fun x ↦ traceNorm (L x)) (𝓝 0) (𝓝 0) := by
  let L := (hB.1.mk' B).codRestrict (nuclearEndomorphisms H) hn
  refine ⟨L, fun _ ↦ rfl, ?_⟩
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let c := traceNorm_normedSpaceCore (H := H)
  let p : Seminorm ℂ X :=
    { toFun := fun x ↦ traceNorm (L x)
      map_zero' := by rw [map_zero]; exact (c.norm_eq_zero_iff _).2 rfl
      add_le' := fun x y ↦ by rw [map_add]; exact c.norm_triangle _ _
      neg' := fun x ↦ by simpa only [map_neg, ← neg_one_smul ℂ (L x), norm_neg, norm_one, one_mul]
          using c.norm_smul (-1 : ℂ) (L x)
      smul' := fun k x ↦ by rw [map_smul]; exact c.norm_smul _ _ }
  have hl : LowerSemicontinuous p :=
    primeOrbitalSobolevConvolution_traceNorm_continuous_lsc (fun x ↦ L x) hB.2
  obtain ⟨_, S, _, hS, _, ht⟩ := hX
  have hT : WithSeminorms
      (Subtype.val : {q : Seminorm ℂ X // ∀ k, Continuous (q ∘ (S k).subtype)} → Seminorm ℂ X) := ⟨ht⟩
  have hc : Continuous p := hT.continuous_seminorm ⟨p, fun k ↦ by
    let : BarrelledSpace ℂ (S k) := isFrechetTVS_barrelled (hS k)
    exact (p.comp (S k).subtype).continuous_of_lowerSemicontinuous
      (hl.comp (S k).subtypeL.continuous)⟩
  exact hc.tendsto' 0 0 p.map_zero'


/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
The convolution action lifts linearly to the trace class and is continuous in trace norm.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_traceNorm_continuous :
    ∃ L : BruhatCompactSupport C𝔽 →ₗ[ℂ] nuclearEndomorphisms OrbQ,
      (∀ φ, (L φ).val = OrbA(φ)) ∧ Tendsto (fun φ ↦ traceNorm (L φ)) (𝓝 0) (𝓝 0) := by
  have hn := primeOrbitalSobolevConvolution_mem_nuclearEndomorphisms (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  apply primeOrbitalSobolevConvolution_traceNorm_continuous_lift (X := BruhatCompactSupport C𝔽)
    (H := OrbQ) bruhatCompactSupport_strictLF (fun φ ↦ OrbA(φ))
  · exact primeOrbitalSobolevConvolution_traceNorm_continuous_descend
      (X := BruhatCompactSupport C𝔽) (E := W(s)) Wω(hs₁, ω(χ)) N(p, hs₁, ω(χ))
      (hardySobolevTestAction μ𝔽 m𝔽 0 0 s h₀ hs₁)
      (continuous_hardySobolevTestAction μ𝔽 m𝔽 0 0 s h₀ hs₁)
      (fun φ ↦ ContinuousLinearMap.restrict (A(hs₁, φ))
        (hardySobolevTestAction_preserves_spectralIsotype (F := F) h₀ hs₁ (ω(χ)) φ))
      (fun _ _ ↦ rfl) (fun φ ↦ OrbA(φ))
      (fun φ u ↦ primeOrbitalSobolevConvolution_mkQ (F := F) p hs₁ (ω(χ)) φ u)
  · exact fun φ ↦ hn φ

section PrimeOrbitalNuclearHelpers

omit _hdeg _hχ

/-- Polynormable structures with the same topology have only proof fields. -/
private theorem primeOrbitalSobolevConvolution_nuclear_polynormable_independent
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (p₁ p₂ : PolynormableSpace ℂ H) (A : H →L[ℂ] H) :
    @IsNuclearOperator H H _ _ _ p₁ _ _ _ A ↔ @IsNuclearOperator H H _ _ _ p₂ _ _ _ A := by
  have hp : p₁ = p₂ := by cases p₁; cases p₂; rfl
  cases hp
  rfl

/-- Extract nuclearity before specializing to the quotient instance tower. -/
private theorem primeOrbitalSobolevConvolution_nuclear_of_lift
    (H X : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (A : X → H →L[ℂ] H)
    (h : ∃ L : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (L x).val = A x) ∧
      Tendsto (fun x ↦ traceNorm (L x)) (𝓝 0) (𝓝 0)) (x : X) :
    letI : PolynormableSpace ℂ H := (norm_withSeminorms ℂ H).toPolynormableSpace
    IsNuclearOperator (A x) := by
  obtain ⟨L, hL, _⟩ := h
  have hn := (L x).property
  rw [hL x] at hn
  exact (primeOrbitalSobolevConvolution_nuclear_polynormable_independent H
    (inferInstance : PolynormableSpace ℂ H)
    ((norm_withSeminorms ℂ H).toPolynormableSpace) (A x)).mp hn

end PrimeOrbitalNuclearHelpers

/-- Paper: Theorem 11.2.2.1 and (11.2.2.3), p. 490.
Convolution by any compactly supported Bruhat test on the prime quotient is trace class.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_nuclear (φ : BruhatCompactSupport C𝔽) :
    letI : PolynormableSpace ℂ OrbQ := (norm_withSeminorms ℂ OrbQ).toPolynormableSpace
    IsNuclearOperator (OrbA(φ)) := by
  have hn := primeOrbitalSobolevConvolution_traceNorm_continuous (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  exact primeOrbitalSobolevConvolution_nuclear_of_lift OrbQ (BruhatCompactSupport C𝔽)
    (fun ψ ↦ OrbA(ψ)) hn φ

/-- Paper: Theorem 11.2.2.1, p. 490.
Taking the trace of prime orbital convolution gives a distribution on the compactly
supported Bruhat test space.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_distribution :
    ∃ D : StrongDual ℂ (BruhatCompactSupport C𝔽),
      ∀ (φ : BruhatCompactSupport C𝔽) (T : nuclearEndomorphisms OrbQ),
        T.val = OrbA(φ) → D φ = hilbertTrace T := by
  have traceDistribution {X : Type _} {H : Type _} [AddCommGroup X] [Module ℂ X]
      [TopologicalSpace X] [IsTopologicalAddGroup X] [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H] (A : X → H →L[ℂ] H)
      (h : ∃ T : X →ₗ[ℂ] nuclearEndomorphisms H, (∀ x, (T x).val = A x) ∧
        Tendsto (fun x : X ↦ traceNorm (H := H) (T x)) (𝓝 0) (𝓝 0)) :
      ∃ D : StrongDual ℂ X, ∀ (x : X) (U : nuclearEndomorphisms H),
        U.val = A x → D x = hilbertTrace U := by
    obtain ⟨T, hT, ht⟩ := h
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    let D : X →ₗ[ℂ] ℂ := L.comp T
    have hb (x : X) : ‖D x‖ ≤ traceNorm (T x) :=
      (congrArg (fun c : ℂ ↦ ‖c‖) (hL (T x))).le.trans (norm_hilbertTrace_le (T x))
    have hd : Continuous D := continuous_of_continuousAt_zero D <| by
      change Tendsto D (𝓝 0) (𝓝 (D 0))
      rw [D.map_zero]
      exact squeeze_zero_norm hb ht
    refine ⟨⟨D, hd⟩, fun x U hU ↦ ?_⟩
    have heq : T x = U := Subtype.ext ((hT x).trans hU.symm)
    exact (hL (T x)).trans (congrArg (hilbertTrace (H := H)) heq)
  have hn := primeOrbitalSobolevConvolution_traceNorm_continuous (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ)
  exact traceDistribution (X := BruhatCompactSupport C𝔽) (H := OrbQ) (fun φ ↦ OrbA(φ)) hn

local notation "zeros" => {z : ℂ // reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0}
local notation "mult(" z ")" => orbitalEulerMultiplicity χ (Sₚ(p)) z

omit _hdeg _hχ in
/-- Summing a function of the ordinate over the admitted jets is summing over the zeros with
the truncated multiplicity as weight. -/
private theorem primeOrbitalSobolevConvolution_trace_hasSum_reindex
    (χ : PontryaginDual C𝔽) (S : Finset V) (s : ℝ) (M : ℂ → ℂ) (a : ℂ)
    (hre : ∀ z, reciprocalPartialHeckeEulerProduct χ S z = 0 → z.re = 0)
    (h : HasSum (fun j : OrbitalJetIndex χ S s ↦ M ((j.val.1 : ℂ) * Complex.I)) a) :
    HasSum (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ S z = 0} ↦
      (spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ S z.val) : ℂ) * M z.val) a := by
  let Z := {z : ℂ // reciprocalPartialHeckeEulerProduct χ S z = 0}
  let N (z : Z) : ℕ := spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ S z.val)
  have hfreq (z : Z) : ((z.val.im : ℝ) : ℂ) * Complex.I = z.val := by
    apply Complex.ext <;> simp [hre z.val z.property]
  let toJ (p : Σ z : Z, Fin (N z)) : OrbitalJetIndex χ S s :=
    ⟨(p.1.val.im, p.2.val), by
      change p.2.val < spectralBoundaryMultiplicity s
        (orbitalEulerMultiplicity χ S (((p.1.val.im : ℝ) : ℂ) * Complex.I))
      rw [hfreq]; exact p.2.isLt⟩
  let ofJ (j : OrbitalJetIndex χ S s) : Σ z : Z, Fin (N z) :=
    ⟨⟨(j.val.1 : ℂ) * Complex.I, OrbitalJetIndex.isZero j⟩, ⟨j.val.2, j.property⟩⟩
  let e : (Σ z : Z, Fin (N z)) ≃ OrbitalJetIndex χ S s :=
    { toFun := toJ
      invFun := ofJ
      left_inv := fun p ↦ by
        refine Sigma.ext (Subtype.ext ?_) ?_
        · exact hfreq p.1
        · exact (Fin.heq_ext_iff (congrArg N (Subtype.ext (hfreq p.1)))).mpr rfl
      right_inv := fun j ↦ by
        apply Subtype.ext
        change ((((j.val.1 : ℂ) * Complex.I).im : ℝ), j.val.2) = j.val
        simp }
  have h' : HasSum (fun p : Σ z : Z, Fin (N z) ↦ M ((((toJ p).val.1 : ℝ) : ℂ) * Complex.I)) a :=
    (e.hasSum_iff).mpr h
  refine h'.sigma fun z ↦ ?_
  have hfin : HasSum (fun k : Fin (N z) ↦ M (((toJ ⟨z, k⟩).val.1 : ℂ) * Complex.I))
      (∑ k : Fin (N z), M (((toJ ⟨z, k⟩).val.1 : ℂ) * Complex.I)) := hasSum_fintype _
  convert hfin using 1
  simp only [toJ, hfreq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl

omit _hdeg _hχ in
/-- On every periodic jet row the Mellin samples are absolutely summable. Grouping by
ordinate counts each zero with its admitted multiplicity. -/
private theorem primeOrbitalSobolevConvolution_trace_summable_of_finite
    (χ : PontryaginDual C𝔽) (p : HeightOneSpectrum (𝓞 ℚ)) (s : ℝ)
    (φ : BruhatCompactSupport C𝔽) :
    Summable (fun z : {z : ℂ // reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0} ↦
      ‖(spectralBoundaryMultiplicity s (orbitalEulerMultiplicity χ (Sₚ(p)) z.val) : ℂ) *
        nuclearityTestMellin χ φ z.val‖) := by
  classical
  have hre (z : ℂ) (hz : reciprocalPartialHeckeEulerProduct χ (Sₚ(p)) z = 0) : z.re = 0 := by
    obtain ⟨v, _, hv⟩ := Finset.prod_eq_zero_iff.mp hz
    by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
    · exact orbitalEulerZero_re_eq_zero χ {v} (by simpa using hu)
        (by simpa [reciprocalPartialHeckeEulerProduct] using hv)
    · simp [finiteHeckeEulerFactor, hu] at hv
  have hj : Summable (fun j : OrbitalJetIndex χ (Sₚ(p)) s ↦
      nuclearityTestMellin χ φ ((j.val.1 : ℂ) * Complex.I)) := by
    apply Summable.of_norm
    exact (PrimeOrbitalTraceProof.orbital_prime_sample_summable_direct (F := F) χ p s φ 0).congr
      fun j ↦ congrArg norm (PrimeOrbitalTraceProof.orbital_sample_zero_mellin (F := F) χ φ j.val.1)
  exact (primeOrbitalSobolevConvolution_trace_hasSum_reindex χ (Sₚ(p)) s
    (nuclearityTestMellin χ φ) _ hre hj.hasSum).summable.norm

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490. The Mellin values of the
test at the zeros of the reciprocal partial Euler product over the places above p, weighted
by the admissible multiplicity, form an absolutely summable family. -/
theorem primeOrbitalSobolevConvolution_trace_summable (φ : BruhatCompactSupport C𝔽) :
    ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
      let term (z : zeros) :=
        (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
      Summable (fun z ↦ ‖term z‖) := by
  intro T _
  exact primeOrbitalSobolevConvolution_trace_summable_of_finite χ p s φ

/-- Paper: Theorem 11.2.2.1 and (11.2.2.6)–(11.2.2.12), pp. 490–491. The orbital
convolution expands along the admitted jets: there are vectors `x` and functionals `Λ`
indexed by the jets such that the rank-one series `∑ (Λ j ∘ A(φ)) ⊗ x j` converges to `A(φ)`
in trace norm, and the diagonal entry at a jet is the Mellin value of the test at the
ordinate of the jet, since the matrix of the transpose on the jets over one zero is
triangular with that constant diagonal, (11.2.2.6)–(11.2.2.11). For fixed `p`, `χ` and `s`, the rank-one estimate needs
a bound `∃ C, ∀ j, ‖x j‖ ≤ C`. The period `2π / log N(p)` preserves each Euler order. Multiplying
by the corresponding norm character preserves the norm-one isotype and the norms of finite
linear combinations of model jets. Biorthogonality and density then bound each primal norm by the
norm at its representative, and only finitely many representatives lie in one period.
Deviation: Use the quotient by the closed principal-value image and the strict cutoff. -/
theorem primeOrbitalSobolevConvolution_trace_jetExpansion (φ : BruhatCompactSupport C𝔽) :
    ∃ (x : OrbitalJetIndex χ (Sₚ(p)) s → OrbQ)
      (Λ : OrbitalJetIndex χ (Sₚ(p)) s → StrongDual ℂ OrbQ),
      (∀ j, Λ j (OrbA(φ) (x j)) = nuclearityTestMellin χ φ ((j.val.1 : ℂ) * Complex.I)) ∧
      ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
        Tendsto (fun I : Finset (OrbitalJetIndex χ (Sₚ(p)) s) ↦ traceNorm (T - ∑ j ∈ I,
          (⟨((Λ j).comp OrbA(φ)).smulRight (x j),
            smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms OrbQ)))
          atTop (𝓝 0) :=
  (PrimeOrbitalTraceProof.orbital_prime_operator (F := F) χ p h₁ _hdeg _hχ φ).2

omit _hdeg _hχ in
/-- A rank-one expansion that converges in trace norm has trace equal to the sum of its
diagonal entries. -/
private theorem primeOrbitalSobolevConvolution_trace_hasSum_of_expansion
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (x : ι → H) (Λ : ι → StrongDual ℂ H)
    (h : Tendsto (fun I : Finset ι ↦ traceNorm (T - ∑ j ∈ I,
      (⟨(Λ j).smulRight (x j), smulRight_mem_nuclearEndomorphisms (Λ j) (x j)⟩ :
        nuclearEndomorphisms H))) atTop (𝓝 0)) :
    HasSum (fun j ↦ Λ j (x j)) (hilbertTrace T) := by
  obtain ⟨f, hf⟩ := hilbertTrace_linear (H := H)
  have hsum (I : Finset ι) : ∑ j ∈ I, Λ j (x j) = hilbertTrace (∑ j ∈ I,
      (⟨(Λ j).smulRight (x j), smulRight_mem_nuclearEndomorphisms (Λ j) (x j)⟩ :
        nuclearEndomorphisms H)) := by
    rw [← hf, map_sum]
    simp_rw [hf, hilbertTrace_smulRight]
  change Tendsto (fun I : Finset ι ↦ ∑ j ∈ I, Λ j (x j)) atTop (𝓝 (hilbertTrace T))
  simp_rw [hsum]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun I ↦ ?_) h
  rw [← hf, ← hf, ← map_sub, ← neg_sub, map_neg, norm_neg, hf]
  exact norm_hilbertTrace_le _



/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490. The sum of those weighted
Mellin values is the trace of the convolution, for any nuclear presentation of it. -/
theorem primeOrbitalSobolevConvolution_trace_hasSum (φ : BruhatCompactSupport C𝔽) :
    ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
      let term (z : zeros) :=
        (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
      HasSum term (hilbertTrace T) := by
  have hexp := primeOrbitalSobolevConvolution_trace_jetExpansion (F := F) (p := p)
    (χ := χ) (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ) φ
  intro T hT
  obtain ⟨x, Λ, hdiag, hconv⟩ := hexp
  have h1 := primeOrbitalSobolevConvolution_trace_hasSum_of_expansion T x
    (fun j ↦ (Λ j).comp OrbA(φ)) (hconv T hT)
  have h2 := h1.congr_fun (g := fun j : OrbitalJetIndex χ (Sₚ(p)) s ↦
    nuclearityTestMellin χ φ ((j.val.1 : ℂ) * Complex.I)) fun j ↦ (hdiag j).symm
  exact primeOrbitalSobolevConvolution_trace_hasSum_reindex χ (Sₚ(p)) s
    (nuclearityTestMellin χ φ) _ (fun z hz ↦ orbitalEulerZero_re_eq_zero χ (Sₚ(p)) _hχ hz) h2

/-- Paper: Theorem 11.2.2.1 and (11.2.2.4)–(11.2.2.5), p. 490.
The trace is the absolutely convergent sum of Mellin values at the zeros of the
reciprocal Euler product over the places above p, weighted by admissible multiplicity.
Deviation: Use the closed denominator and the strict boundary cutoff of §11.2.0.
Under the stated degree bound this cutoff agrees with the printed one. -/
theorem primeOrbitalSobolevConvolution_trace (φ : BruhatCompactSupport C𝔽) :
    ∀ (T : nuclearEndomorphisms OrbQ), T.val = OrbA(φ) →
      let term (z : zeros) :=
        (spectralBoundaryMultiplicity s (mult(z.val)) : ℂ) * nuclearityTestMellin χ φ z.val
      Summable (fun z ↦ ‖term z‖) ∧ HasSum term (hilbertTrace T) :=
  fun T hT => And.intro
    (primeOrbitalSobolevConvolution_trace_summable (F := F) (p := p) (s := s) (χ := χ)
      (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ) φ T hT)
    (primeOrbitalSobolevConvolution_trace_hasSum (F := F) (p := p) (s := s) (χ := χ)
      (h₁ := h₁) (_hdeg := _hdeg) (_hχ := _hχ) φ T hT)

include h₁ in
/-- Paper: Remark 11.2.2.2, p. 491.
The degree bound admits all jet orders below the multiplicity of a prime Euler zero.
The strict integrability cutoff then leaves that multiplicity unchanged. -/
theorem primeOrbitalMultiplicity_saturates (z : zeros) :
    spectralBoundaryMultiplicity s (mult(z.val)) = mult(z.val) := by
  classical
  let S := Sₚ(p)
  have hcard : S.card ≤ Module.finrank ℚ F := by
    let e (v : S) : p.asIdeal.primesOver (𝓞 F) :=
      ⟨v.val.asIdeal, v.val.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal
        (show v.val.under (𝓞 ℚ) = p from (finite_nuclearityPlacesAbove (F := F) p).mem_toFinset.mp v.property)).symm⟩⟩
    have hi : Function.Injective e := fun v w h ↦
      Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    simpa only [Fintype.card_coe] using (Fintype.card_le_of_injective e hi).trans
      (reciprocalEulerProduct_over_prime_order_le_card_le (F := F) p)
  have hm : mult(z.val) ≤ Module.finrank ℚ F := by
    rw [orbitalEulerMultiplicity_eq_card]
    exact (Finset.card_filter_le _ _).trans hcard
  apply Nat.le_antisymm (min_le_left _ _)
  by_contra! hlt
  have hk : (spectralBoundaryMultiplicity s (mult(z.val)) : ℝ) + 1 ≤ Module.finrank ℚ F := by
    exact_mod_cast (Nat.succ_le_of_lt hlt).trans hm
  have himp := (lt_spectralBoundaryMultiplicity s (mult(z.val))
    (spectralBoundaryMultiplicity s (mult(z.val)))).mpr ⟨hlt, by linarith only [hk, _hdeg]⟩
  exact (lt_irrefl _ himp)

/-- Paper: Remark 11.2.2.2 and (11.2.2.13), p. 491.
The prime orbital convolution trace is independent of the Sobolev degree
once both degrees satisfy the two lower bounds.
Deviation: Use the quotient by the closed principal-value image. -/
theorem primeOrbitalSobolevConvolution_trace_eq_of_degree {s' : ℝ} (h₁' : 1 < s')
    (_hdeg' : 2 * (Module.finrank ℚ F : ℝ) ≤ s') (φ : BruhatCompactSupport C𝔽) :
    let hs' := (zero_lt_one.trans h₁').le
    ∀ (T : nuclearEndomorphisms OrbQ) (T' : nuclearEndomorphisms Q(p, hs', ω(χ))),
      T.val = OrbA(φ) →
      T'.val = primeOrbitalSobolevConvolution (F := F) p hs' (ω(χ)) φ →
      hilbertTrace T = hilbertTrace T' := by
  dsimp only
  intro T T' hT hT'
  have hsum := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁ _hdeg _hχ φ T hT).2
  have hsum' := (primeOrbitalSobolevConvolution_trace (F := F) p χ h₁' _hdeg' _hχ φ T' hT').2
  apply hsum.unique
  apply hsum'.congr_fun
  intro z
  rw [primeOrbitalMultiplicity_saturates (F := F) p χ h₁ _hdeg _hχ z,
    primeOrbitalMultiplicity_saturates (F := F) p χ h₁' _hdeg' _hχ z]

end Orbital

end RiemannMasullo
