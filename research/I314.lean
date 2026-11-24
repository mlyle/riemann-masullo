module
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
/-!
# Compact Fourier windows on a positive-width idele-class Sobolev strip

Theorem 10.3.2.1(1), pp. 453–455, refers back to the physical Fourier windows
in the proof of Theorem 10.3.1.1(1), pp. 449–450. This checks the positive-width
obstruction recorded under I314 against the actual Plancherel transform and
the actual spectral Sobolev quotient.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instDualMeasurableSpaceSec3 instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "W(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s
local notation "res𝔽" => (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "hms𝔽" => (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1

open Complex in
private theorem countable_zeros_on_strip_line {a b σ : ℝ} (hσ : σ ∈ Ioo a b)
    {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F (re ⁻¹' Ioo a b))
    (hne : ∃ z ∈ re ⁻¹' Ioo a b, F z ≠ 0) :
    {t : ℝ | F ((σ : ℂ) + (t : ℂ) * I) = 0}.Countable := by
  let U : Set ℂ := re ⁻¹' Ioo a b
  let L (t : ℝ) : ℂ := σ + (t : ℂ) * I
  obtain ⟨z, hz, hne⟩ := hne
  have hc : IsConnected U := ⟨⟨z, hz⟩, ((convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt b)).isPreconnected⟩
  have hd : IsDiscrete (F ⁻¹' {0} ∩ U) :=
    isDiscrete_of_codiscreteWithin (hF.preimage_zero_mem_codiscreteWithin hne hz hc)
  have hzcount : (F ⁻¹' {0} ∩ U).Countable := IsLindelof.of_coe.countable_of_isDiscrete hd
  have hi : Function.Injective L := fun x y h ↦ by simpa [L] using congrArg im h
  apply (hzcount.preimage hi).mono
  intro t ht
  exact ⟨ht, by simpa [U, L] using hσ⟩

private theorem stripBand_moments {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (χ : PontryaginDual C𝔽) (f : W(-α, α, s)) {σ : ℝ} (hσ : σ ∈ Ioo (-α) α) (n : ℕ) :
    Integrable (fun g ↦ f g * (logNorm g : ℂ) ^ n * ideleClassNormTwist χ (σ : ℂ) g) μ𝔽 := by
  let ρ (g : C𝔽) := intervalSobolevDensity (-α) α s (logNorm g)
  have hρ : Continuous ρ := (continuous_intervalSobolevDensity' _ _ _).comp (continuous_logModule' m𝔽)
  have hp (g : C𝔽) : 0 < ρ g := intervalSobolevDensity_pos _ _ _ _
  let w := spectralZeroJet χ σ 0 n
  have hw : Continuous w := spectralZeroJet_continuous χ σ 0 n
  have hi : Integrable (fun g : C𝔽 ↦ ‖w g‖ ^ 2 * (ρ g)⁻¹) μ𝔽 := by
    have h := stripTheta_log_integrable (F := F) (spectralStripJet_integrable hα.le hs (k := n) (Or.inl hσ))
    exact h.congr (.of_forall fun g ↦ by
      dsimp only [w, ρ]
      rw [spectralZeroJet_norm_sq, stripJet_integrand_eq hα.le])
  obtain ⟨_, hL⟩ := weightedL2_pairing μ𝔽 hρ.measurable hp hw.aestronglyMeasurable hi
  apply ((hL f).1).congr (.of_forall fun g ↦ ?_)
  simp only [w, spectralZeroJet, Complex.ofReal_zero, zero_mul, add_zero]
  ring

private theorem stripBand_analytic {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (χ : PontryaginDual C𝔽) (f : W(-α, α, s)) :
    AnalyticOnNhd ℂ (fun z ↦ ∫ g, f g * ideleClassNormTwist χ z g ∂μ𝔽)
      (Complex.re ⁻¹' Ioo (-α) α) := by
  intro z hz
  let χ' : QuasiCharacter C𝔽 := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  exact (iteratedDeriv_normTwist_moment m𝔽 μ𝔽 χ'
    (fun σ hσ n ↦ stripBand_moments hα hs χ f hσ n) 0 hz).1

private theorem stripBand_frequency_line (χ : PontryaginDual C𝔽) :
    ∃ γ : ℝ → PontryaginDual C𝔽, Topology.IsClosedEmbedding γ ∧
      ∀ t g, γ t g = (χ g)⁻¹ * Circle.exp (-t * logNorm g) := by
  obtain ⟨e, he⟩ := exists_frequency_line m𝔽 hm𝔽 hms𝔽
  have hclosed : IsClosed (lcaAnnihilator (m𝔽).toMonoidHom.ker : Set (PontryaginDual C𝔽)) := by
    have hset : (lcaAnnihilator (m𝔽).toMonoidHom.ker : Set (PontryaginDual C𝔽)) =
        ⋂ g : (m𝔽).ker, {ψ | ψ g.val = 1} := by
      ext ψ
      simp [mem_lcaAnnihilator_iff]
      rfl
    rw [hset]
    exact isClosed_iInter fun g ↦ isClosed_eq
      (continuous_eval_const (F := ContinuousMonoidHom C𝔽 Circle) g.val) continuous_const
  let γ (t : ℝ) := χ⁻¹ * (e (Multiplicative.ofAdd (-t))).val
  refine ⟨γ, (Homeomorph.mulLeft χ⁻¹).isClosedEmbedding.comp
    (hclosed.isClosedEmbedding_subtypeVal.comp (e.toHomeomorph.isClosedEmbedding.comp
      (Homeomorph.ofAdd.isClosedEmbedding.comp (Homeomorph.neg ℝ).isClosedEmbedding))), ?_⟩
  exact fun t g ↦ congrArg ((χ g)⁻¹ * ·) (he (-t) g)

private theorem isOpen_character_restriction_fiber (ψ : PontryaginDual C𝔽) :
    IsOpen {η : PontryaginDual C𝔽 | η.comp res𝔽 = ψ.comp res𝔽} := by
  have he : {η : PontryaginDual C𝔽 | η.comp res𝔽 = ψ.comp res𝔽} =
      (fun η : PontryaginDual C𝔽 ↦ ψ⁻¹ * η) ⁻¹' (lcaAnnihilator (m𝔽).toMonoidHom.ker : Set _) := by
    ext η
    constructor
    · intro h
      apply (mem_lcaAnnihilator_iff ..).2
      intro g
      change (ψ g.val)⁻¹ * η g.val = 1
      rw [show η g.val = ψ g.val from DFunLike.congr_fun h g, inv_mul_cancel]
    · intro h
      apply ContinuousMonoidHom.ext
      intro g
      have hval := (mem_lcaAnnihilator_iff ..).1 h g
      change (ψ g.val)⁻¹ * η g.val = 1 at hval
      exact (inv_mul_eq_one.mp hval).symm
  rw [he]
  exact (isOpen_lcaAnnihilator _ (IsModulation.isCompact_ker (m := m𝔽) hm𝔽)).preimage (continuous_const.mul continuous_id)

private theorem fourier_eq_zero_of_compact_support {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (f : W(-α, α, s)) (hband : ∀ ψ : PontryaginDual C𝔽, ∃ K : Set (PontryaginDual C𝔽),
      IsCompact K ∧ ∀ η : PontryaginDual C𝔽, η.comp res𝔽 = ψ.comp res𝔽 →
        η ∉ K → lcaFourier μ𝔽 f η = 0) :
    ∀ ψ, lcaFourier μ𝔽 f ψ = 0 := by
  intro ψ
  let χ := ψ⁻¹
  obtain ⟨γ, hγ, hγval⟩ := stripBand_frequency_line χ
  obtain ⟨K, hK, hwin⟩ := hband ψ
  have hres (t : ℝ) : (γ t).comp res𝔽 = ψ.comp res𝔽 := by
    apply ContinuousMonoidHom.ext
    intro g
    exact (hγval t g.val).trans (by
      change ((ψ g.val)⁻¹)⁻¹ * Circle.exp (-t * Real.log ((ideleClassNorm F g.val).val : ℝ)) = ψ g.val
      rw [show ideleClassNorm F g.val = 1 from g.property]
      simp)
  obtain ⟨B, hB⟩ := (hγ.isCompact_preimage hK).bddAbove
  let M (z : ℂ) := ∫ g, f g * ideleClassNormTwist χ z g ∂μ𝔽
  have hphase (t : ℝ) : lcaFourier μ𝔽 f (γ t) = M ((t : ℂ) * Complex.I) := by
    apply integral_congr_ae (.of_forall fun g ↦ ?_)
    have hc : γ t g = (χ g * Circle.exp (t * logNorm g))⁻¹ := by
      rw [hγval, neg_mul, Circle.exp_neg, mul_inv]
    have hstar : star (γ t g : ℂ) = (χ g : ℂ) * Complex.exp (((t * logNorm g : ℝ) : ℂ) * Complex.I) := by
      rw [hc, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star, Circle.coe_mul, Circle.coe_exp]
    change f g * star (γ t g : ℂ) = f g * _
    rw [hstar]
    congr 2
    change _ = (((m𝔽 g).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'),
      ← Complex.ofReal_log (NNReal.coe_pos.mpr (Units.zero_lt _)).le, Complex.ofReal_mul]
    congr 1
    change _ = ((logNorm g : ℝ) : ℂ) * _
    ring
  have hz : γ 0 = ψ := by
    apply ContinuousMonoidHom.ext
    intro g
    exact (hγval 0 g).trans (by
      change ((ψ g)⁻¹)⁻¹ * _ = ψ g
      simp)
  by_contra hψ
  have h0 : M 0 ≠ 0 := by
    intro h
    apply hψ
    simpa [hz, h] using hphase 0
  have hσ : (0 : ℝ) ∈ Ioo (-α) α := ⟨neg_lt_zero.mpr hα, hα⟩
  have hcount := countable_zeros_on_strip_line hσ (stripBand_analytic hα hs χ f)
    ⟨0, by simpa using hσ, h0⟩
  have him : (Ioi B).Countable := hcount.mono fun t ht ↦ by
    have hγK : γ t ∉ K := fun h ↦ (not_le_of_gt ht) (hB h)
    simpa only [Set.mem_ofPred_eq, Complex.ofReal_zero, zero_add] using
      (hphase t).symm.trans (hwin _ (hres t) hγK)
  exact (isOpen_Ioi.measure_pos (volume : Measure ℝ) (nonempty_Ioi (a := B))).ne' (him.measure_zero volume)

/-- The compact window may depend arbitrarily on the norm-one character. -/
theorem positiveStrip_eq_zero_of_componentwise_compact_support {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν)
    (f : W(-α, α, s)) (u : Lp ℂ 2 μ𝔽) (huf : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f : C𝔽 → ℂ))
    (hband : ∀ ω : PontryaginDual C₁, ∃ K : Set (PontryaginDual C𝔽), IsCompact K ∧
      ∀ᵐ ψ ∂ν, ψ.comp res𝔽 = ω → ψ ∉ K → (lcaFourier_unitary μ𝔽 ν hν).exists.choose u ψ = 0) :
    f = 0 := by
  let : BorelSpace (PontryaginDual C𝔽) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  have hf : Integrable (f : C𝔽 → ℂ) μ𝔽 := by
    have hm := stripBand_moments hα hs (1 : PontryaginDual C𝔽) f
      (show (0 : ℝ) ∈ Ioo (-α) α from ⟨neg_lt_zero.mpr hα, hα⟩) 0
    apply hm.congr (.of_forall fun g ↦ ?_)
    simp only [pow_zero, mul_one, Complex.ofReal_zero]
    change f g * ((1 : ℂ) * _ ^ (0 : ℂ)) = f g
    simp
  let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
  have hU : (U u : PontryaginDual C𝔽 → ℂ) =ᵐ[ν] lcaFourier μ𝔽 f := by
    have heq := (lcaFourier_unitary μ𝔽 ν hν).exists.choose_spec (u : C𝔽 → ℂ)
      (hf.congr huf.symm) (Lp.memLp u)
    rw [Lp.toLp_coeFn] at heq
    exact heq.trans (.of_forall fun ψ ↦ integral_congr_ae (huf.mul EventuallyEq.rfl))
  obtain ⟨G, hG⟩ := lcaFourier_zeroAtInfty μ𝔽 hf
  have hc : Continuous (lcaFourier μ𝔽 f) := (funext hG) ▸ G.continuous
  have hz := fourier_eq_zero_of_compact_support hα hs f (fun ψ ↦ by
    obtain ⟨K, hK, hb⟩ := hband (ψ.comp res𝔽)
    refine ⟨K, hK, fun η hη hout ↦ ?_⟩
    let V := {ξ : PontryaginDual C𝔽 | ξ.comp res𝔽 = ψ.comp res𝔽} ∩ Kᶜ
    have hv : IsOpen V := (isOpen_character_restriction_fiber ψ).inter hK.isClosed.isOpen_compl
    have ho : EqOn (lcaFourier μ𝔽 f) 0 V := by
      refine Measure.eqOn_open_of_ae_eq (μ := ν) ?_ hv hc.continuousOn continuousOn_const
      apply (ae_restrict_iff' hv.measurableSet).2
      filter_upwards [hU, hb] with ξ hξ hwin hV
      exact hξ.symm.trans (hwin hV.1 hV.2)
    exact ho ⟨hη, hout⟩)
  have hu : U u = 0 := Lp.ext ((hU.trans (.of_forall hz)).trans (Lp.coeFn_zero ℂ 2 ν).symm)
  have hu0 : u = 0 := U.injective (hu.trans (map_zero U).symm)
  have hf0 : (f : C𝔽 → ℂ) =ᵐ[μ𝔽] 0 := huf.symm.trans (hu0 ▸ Lp.coeFn_zero ℂ 2 μ𝔽)
  exact Lp.ext ((withDensity_absolutelyContinuous _ _).ae_eq hf0 |>.trans (Lp.coeFn_zero ℂ 2 _).symm)

/-- On a positive-width strip, only the zero physical vector has compactly
supported Plancherel transform. The support condition is almost everywhere. -/
theorem positiveStrip_eq_zero_of_plancherel_compact_support {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν)
    (K : Set (PontryaginDual C𝔽)) (hK : IsCompact K)
    (f : W(-α, α, s)) (u : Lp ℂ 2 μ𝔽)
    (huf : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f : C𝔽 → ℂ))
    (hband : ∀ᵐ ψ ∂ν, ψ ∉ K → (lcaFourier_unitary μ𝔽 ν hν).exists.choose u ψ = 0) :
    f = 0 := by
  apply positiveStrip_eq_zero_of_componentwise_compact_support hα hs ν hν f u huf
  intro ω
  exact ⟨K, hK, hband.mono fun ψ hp _ ↦ hp⟩

private theorem positiveStrip_window_union_zero
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν)
    (l r : PontryaginDual C₁ → ℝ) (f : W(-α, α, s)) (u : Lp ℂ 2 μ𝔽)
    (huf : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f : C𝔽 → ℂ))
    (hband : ∀ᵐ ψ ∂ν, ψ ∉ ⋃ ω, modulatedFrequencyBand m𝔽 (χ ω) (l ω) (r ω) →
      (lcaFourier_unitary μ𝔽 ν hν).exists.choose u ψ = 0) : f = 0 := by
  apply positiveStrip_eq_zero_of_componentwise_compact_support hα hs ν hν f u huf
  intro ω
  obtain ⟨e, he⟩ := exists_frequency_line m𝔽 hm𝔽 hms𝔽
  refine ⟨modulatedFrequencyBand m𝔽 (χ ω) (l ω) (r ω), ?_, ?_⟩
  · rw [frequencyBand_eq_image m𝔽 (χ ω) e he]
    exact isCompact_Icc.image (continuous_const.mul (continuous_subtype_val.comp e.continuous))
  · filter_upwards [hband] with ψ hp hres hout
    apply hp
    intro h
    obtain ⟨η, t, ht, hphase⟩ := mem_iUnion.mp h
    have hη : ψ.comp res𝔽 = (χ η).comp res𝔽 := by
      apply ContinuousMonoidHom.ext
      intro g
      exact (hphase g.val).trans (by
        change χ η g.val * Circle.exp (t * Real.log ((ideleClassNorm F g.val).val : ℝ)) = χ η g.val
        rw [show ideleClassNorm F g.val = 1 from g.property]
        simp)
    have hηω : η = ω := (hη.trans (hχ η)).symm.trans hres
    subst η
    exact hout ⟨t, ht, hphase⟩

private theorem quotientWindows_not_dense_of_retained_jet
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) (i : SpectralStripJetIndex χ a α s)
    (ν : Measure (PontryaginDual C𝔽)) (hν : IsLCAPlancherelMeasure μ𝔽 ν) :
    let Θ := globalThetaSobolev F a ((neg_nonpos.mpr hα.le).trans hα.le) hs
    let U := (lcaFourier_unitary μ𝔽 ν hν).exists.choose
    ¬ Dense {q : spectralSobolevQuotient F a ((neg_nonpos.mpr hα.le).trans hα.le) hs |
      ∃ (l r : PontryaginDual C₁ → ℝ)
        (f : W(-α, α, s)) (u : Lp ℂ 2 μ𝔽), q = Θ.mkQ f ∧
          (u : C𝔽 → ℂ) =ᵐ[μ𝔽] (f : C𝔽 → ℂ) ∧ ∀ᵐ ψ ∂ν, ψ ∉ ⋃ ω, modulatedFrequencyBand m𝔽 (χ ω) (l ω) (r ω) → U u ψ = 0} := by
  classical
  intro Θ U hD
  obtain ⟨y, hy⟩ := spectralStripJet_singleInterpolant χ hχ hα.le hs i
  have hn : Θ.mkQ y ≠ 0 := by
    intro h
    have hzero := spectralStripJet_commonKernel_forward χ hα.le hs y ((Submodule.Quotient.mk_eq_zero Θ).mp h) i
    simp [hy i] at hzero
  apply hn
  refine closure_minimal (t := ({0} : Set (spectralSobolevQuotient F a ((neg_nonpos.mpr hα.le).trans hα.le) hs))) ?_ isClosed_singleton (hD (Θ.mkQ y))
  rintro q ⟨l, r, f, u, rfl, huf, hb⟩
  rw [positiveStrip_window_union_zero χ hχ hα hs ν hν l r f u huf hb, map_zero]
  rfl

/-- Every finite union of the windows of pp. 449–450 is compact. -/
theorem isCompact_finite_modulatedFrequencyBands {ι : Type*} [Finite ι]
    (χ : ι → PontryaginDual C𝔽) (l r : ι → ℝ) :
    IsCompact (⋃ i, modulatedFrequencyBand m𝔽 (χ i) (l i) (r i)) := by
  obtain ⟨e, he⟩ := exists_frequency_line m𝔽 hm𝔽 hms𝔽
  apply isCompact_iUnion
  intro i
  rw [frequencyBand_eq_image m𝔽 (χ i) e he]
  exact isCompact_Icc.image (continuous_const.mul (continuous_subtype_val.comp e.continuous))

local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ

private theorem stripBand_rational_index {α s : ℝ} (hα : 0 < α) :
    ∃ χ : PontryaginDual (ideleClassNorm ℚ).ker → PontryaginDual CQ,
      IsSpectralBasepointChoice χ ∧ Nonempty (SpectralStripJetIndex χ (1/2) α s) := by
  classical
  obtain ⟨t, -, ht⟩ := HardyFirstZero.first_zero_on_line
  let z : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hre : z.re = 1/2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hz : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at ht
    rw [← ht]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [htwo]; simp)
  have horder := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual CQ)
    hm (fun w ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta w.property])
    (s := z) (by rw [hre]; norm_num)
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 (1 : PontryaginDual CQ)
  have hχ1 : χ 1 = 1 := Function.update_self ..
  refine ⟨χ, fun ω ↦ ?_, ⟨⟨(1, 0, t, 0), ?_⟩⟩⟩
  · by_cases h : ω = 1
    · subst ω
      rw [hχ1]
      rfl
    · simpa [χ, h] using hχ₀ ω
  · change 0 < spectralStripMultiplicity α s 0 (meromorphicOrderAt (continuedCompletedHeckeL (χ 1)) _).untop₀.toNat
    rw [spectralStripMultiplicity_interior ⟨neg_lt_zero.mpr hα, hα⟩, hχ1]
    have hn : 0 < (meromorphicOrderAt riemannZeta z).untop₀.toNat := by
      rw [← WithTop.coe_untop₀_of_ne_top hfin] at hz
      have hi : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hz
      omega
    rw [horder] at hn
    push_cast
    simpa [z] using hn

/-- At the rational critical line, all quotient vectors represented using the
bounded window in each angular component of p. 450 fail to exhaust the quotient.
This includes infinitely many components with no common bound on their windows. -/
theorem rationalPositiveStrip_boundedFourierWindows_not_dense {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (ν : Measure (PontryaginDual CQ)) (hν : IsLCAPlancherelMeasure (ideleClassTamagawaMeasure ℚ) ν) :
    let μ := ideleClassTamagawaMeasure ℚ
    let Θ := globalThetaSobolev ℚ (1/2) ((neg_nonpos.mpr hα.le).trans hα.le) hs
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    ∃ χ : PontryaginDual (ideleClassNorm ℚ).ker → PontryaginDual CQ, IsSpectralBasepointChoice χ ∧
    ¬ Dense {q : spectralSobolevQuotient ℚ (1/2) ((neg_nonpos.mpr hα.le).trans hα.le) hs |
      ∃ (l r : PontryaginDual (ideleClassNorm ℚ).ker → ℝ)
        (f : CompactIntervalSobolev μ (logIdeleClassNorm ℚ) (-α) α s) (u : Lp ℂ 2 μ),
        q = Θ.mkQ f ∧ (u : CQ → ℂ) =ᵐ[μ] (f : CQ → ℂ) ∧ ∀ᵐ ψ ∂ν,
          ψ ∉ ⋃ ω, modulatedFrequencyBand
            (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : CQ →ₜ* ℝ≥0ˣ)
            (χ ω) (l ω) (r ω) → U u ψ = 0} := by
  obtain ⟨χ, hχ, ⟨i⟩⟩ := stripBand_rational_index (s := s) hα
  exact ⟨χ, hχ, quotientWindows_not_dense_of_retained_jet χ hχ hα hs i ν hν⟩

#print axioms rationalPositiveStrip_boundedFourierWindows_not_dense
#print axioms positiveStrip_eq_zero_of_componentwise_compact_support
#print axioms isCompact_finite_modulatedFrequencyBands
#print axioms positiveStrip_eq_zero_of_plancherel_compact_support
end RiemannMasullo
