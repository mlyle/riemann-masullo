module
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
public import RiemannMasullo.Ch10_TraceSpectral.Sec2_WidthRestriction

/-! # Signed width comparison at a finite physical cutoff

A compact physical cutoff allows a narrow convolution output to be lifted back to the
wider weighted space. Cyclicity then identifies the signed difference of the genuine
projected traces with a single operator through the narrow theta component.
-/
@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo

private theorem thetaMask_strengthen {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (hν : ν ≪ μ) {S : Set X} (hS : MeasurableSet S) {c : ℝ≥0∞}
    (hc : c ≠ ∞) (hbound : ν.restrict S ≤ c • μ) :
    ∃ M : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν, ∀ q, (M q : X → ℂ) =ᵐ[ν] S.indicator (q : X → ℂ) := by
  let h (q : Lp ℂ 2 μ) : MemLp (S.indicator (q : X → ℂ)) 2 ν :=
    (memLp_indicator_iff_restrict hS.nullMeasurableSet).mpr ((Lp.memLp q).of_measure_le_smul hc hbound)
  let T (q : Lp ℂ 2 μ) := (h q).toLp (S.indicator (q : X → ℂ))
  have ht (q : Lp ℂ 2 μ) : (T q : X → ℂ) =ᵐ[ν] S.indicator (q : X → ℂ) := (h q).coeFn_toLp
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := T
      map_add' := fun q p ↦ by
        apply Lp.ext
        filter_upwards [ht (q+p), ht q, ht p, hν.ae_eq (Lp.coeFn_add q p), Lp.coeFn_add (T q) (T p)]
          with x h₁ h₂ h₃ h₄ h₅
        change (q+p) x = q x+p x at h₄
        simp only [Pi.add_apply] at h₅
        rw [h₁, h₅, h₂, h₃]
        by_cases hx : x ∈ S
        · simpa only [Set.indicator_of_mem hx] using h₄
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun a q ↦ by
        apply Lp.ext
        filter_upwards [ht (a • q), ht q, hν.ae_eq (Lp.coeFn_smul a q), Lp.coeFn_smul a (T q)]
          with x h₁ h₂ h₃ h₄
        by_cases hx : x ∈ S <;> simpa [hx, h₁, h₂, h₃, Pi.smul_apply] using h₄.symm }
  refine ⟨L.mkContinuous (c.toReal ^ ((1/(2 : ℝ≥0∞)).toReal)) (fun q ↦ ?_), ht⟩
  change ‖(h q).toLp _‖ ≤ _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hS.nullMeasurableSet, Lp.norm_def]
  have he := eLpNorm_le_of_measure_le_smul (f := (q : X → ℂ)) (p := 2) hbound
  simpa only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_rpow] using
    (ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp [hc]) (Lp.eLpNorm_ne_top q)) he)

private theorem thetaMask_change_density {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) (d e : X → ℝ) (hd : Continuous d)
    (hp : ∀ x, 0 < d x) {S : Set X} (hS : MeasurableSet S)
    (hC : BddAbove ((fun x ↦ e x / d x) '' S)) :
    ∃ M : Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (d x))) →L[ℂ]
        Lp ℂ 2 (μ.withDensity (fun x ↦ ENNReal.ofReal (e x))),
      ∀ q, (M q : X → ℂ) =ᵐ[μ.withDensity (fun x ↦ ENNReal.ofReal (e x))] S.indicator (q : X → ℂ) := by
  obtain ⟨B,hB⟩ := hC
  let c := ENNReal.ofReal (max B 0)
  have hac : μ ≪ μ.withDensity (fun x ↦ ENNReal.ofReal (d x)) :=
    withDensity_absolutelyContinuous' hd.measurable.ennreal_ofReal.aemeasurable
      (.of_forall fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp x))
  apply thetaMask_strengthen _ _ ((withDensity_absolutelyContinuous _ _).trans hac) hS
    (c := c) ENNReal.ofReal_ne_top
  rw [restrict_withDensity hS, ← withDensity_indicator hS, ← withDensity_smul' _
    _ ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards with x
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx, Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (le_max_right B 0)]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (hp x)).mp ((hB (mem_image_of_mem _ hx)).trans (le_max_left B 0)))
  · simp [hx]

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "x𝔽" => logIdeleClassNorm F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 x𝔽 (-α) α s
local notation "ν(" α ", " s ")" => intervalSobolevMeasure μ𝔽 x𝔽 (-α) α s
local notation "mask(" b ", " s ", " h ")" => modulatedCutoffOperator m𝔽 ν(b,s) h
local notation "act(" h ", " hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (neg_le_self h) hs φ

private theorem thetaMask_density_data (b s : ℝ) : Continuous (intervalSobolevDensity (-b) b s) ∧
    ∀ x, 0 < intervalSobolevDensity (-b) b s x := by
  unfold intervalSobolevDensity
  refine ⟨?_, fun x ↦ mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)⟩
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const (p := s/2) (fun _ ↦ Or.inl (by dsimp; positivity)))

private theorem thetaMask_haar_ac (b s : ℝ) : μ𝔽 ≪ ν(b,s) := by
  have hx : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  obtain ⟨hc, hp⟩ := thetaMask_density_data b s
  exact withDensity_absolutelyContinuous' (hc.comp hx).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp (x𝔽 g)))

private theorem thetaMask_support_lift {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsModulatedCutoff m𝔽 Λ ε ρ)
    (α β s : ℝ) : ∃ M : W(α,s) →L[ℂ] W(β,s), ∀ q, (M q : C𝔽 → ℂ) =ᵐ[μ𝔽]
      (tsupport ρ).indicator (q : C𝔽 → ℂ) := by
  let d := intervalSobolevDensity (-α) α s
  let e := intervalSobolevDensity (-β) β s
  have hx : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  obtain ⟨hd,hp⟩ := thetaMask_density_data α s
  obtain ⟨he,_⟩ := thetaMask_density_data β s
  have hC : BddAbove ((fun g : C𝔽 ↦ e (x𝔽 g) / d (x𝔽 g)) '' tsupport ρ) := by
    have hc : Continuous (fun z ↦ e z / d z) := he.div hd fun z ↦ (hp z).ne'
    apply (isCompact_Icc (a := Real.log Λ⁻¹) (b := Real.log Λ)).bddAbove_image hc.continuousOn |>.mono
    rintro _ ⟨g,hg,rfl⟩
    have h := hρ.support_subset hg
    refine ⟨x𝔽 g, ⟨Real.log_le_log (inv_pos.mpr hρ.radius_pos) h.1,
      Real.log_le_log (NNReal.coe_pos.mpr (Units.zero_lt _)) h.2⟩, rfl⟩
  obtain ⟨M,hM⟩ := thetaMask_change_density μ𝔽 (fun g ↦ d (x𝔽 g)) (fun g ↦ e (x𝔽 g))
    (hd.comp hx) (fun g ↦ hp (x𝔽 g)) (isClosed_tsupport ρ).measurableSet hC
  exact ⟨M,fun q ↦ (thetaMask_haar_ac β s).ae_eq (hM q)⟩

private theorem thetaMask_nuclear_composition {E G H K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (A : G →L[ℂ] H) (hA : IsNuclearOperator A) (S : E →L[ℂ] G) (T : H →L[ℂ] K) :
    IsNuclearOperator (T.comp (A.comp S)) := by
  obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ := (isNuclearOperator_iff_isBanachNuclear A).mp hA
  let pre := (ContinuousLinearMap.compL ℂ E G ℂ).flip S
  apply (isNuclearOperator_iff_isBanachNuclear _).mpr
  refine ⟨c, fun n ↦ (φ n).comp S, T ∘ y, hc, ?_, ?_, ?_⟩
  · exact (pre.continuous.tendsto' 0 0 (map_zero pre)).comp hφ
  · simpa only [map_zero] using (T.continuous.tendsto 0).comp hy
  · intro x
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, map_smul] using T.hasSum (hsum (S x))

/-- Paper: Theorems 9.3.3.5 and 10.4.2.1, pp. 429 and 459. At each finite
admissible cutoff the actual masked convolution strengthens the output to any
strip width and remains nuclear, for an arbitrary idèle-class Bruhat test. -/
theorem exists_maskedConvolution_changeWidth {Λ ε : ℝ} {ρ : C𝔽 → ℝ}
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (β : ℝ) (φ : BruhatCompactSupport C𝔽) :
    ∃ C : W(α,s) →L[ℂ] W(β,s), IsNuclearOperator C ∧
      ∀ q, (C q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ (ρ g : ℂ) * lcaConvolution μ𝔽 φ.val q g := by
  obtain ⟨M,hM⟩ := thetaMask_support_lift hρ α β s
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hc := continuous_of_bruhatSmooth hφs
  have hb := hc.bounded_above_of_compact_support (show HasCompactSupport φ.val from φ.property.2)
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsur : Surjective m𝔽 := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
  obtain ⟨hn, _, _⟩ := truncatedHardySobolevConvolution_trace μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs
    φ.val hc.aemeasurable φ.property.2 hb hm hsur hφs hρ hband
  have he := hardySobolevConvolution_eq_testAction μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ hc.aemeasurable hb
  let A := act(hα,hs,φ)
  let D : W(α,s) →L[ℂ] W(α,s) := (mask(α,s,hρ)).comp A
  have hD : IsNuclearOperator D := (congrArg (fun T ↦ IsNuclearOperator ((mask(α,s,hρ)).comp T)) he).mp hn
  refine ⟨M.comp D, ?_, fun q ↦ ?_⟩
  · exact thetaMask_nuclear_composition D hD (ContinuousLinearMap.id ℂ _) M
  · have ha := hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ q
    have hd := (thetaMask_haar_ac α s).ae_eq (modulatedCutoffOperator_apply m𝔽 ν(α,s) hρ (A q))
    filter_upwards [hM (D q), hd, ha] with g hg hdg hag
    change M (D q) g = _
    rw [hg]
    by_cases h : g ∈ tsupport ρ
    · rw [Set.indicator_of_mem h]
      exact hdg.trans (congrArg ((ρ g : ℂ) * ·) hag)
    · have hz : ρ g = 0 := image_eq_zero_of_notMem_tsupport h
      simp [h, hz]

private theorem thetaMask_conjugate {Λ ε : ℝ} {ρ : C𝔽 → ℝ} (hρ : IsModulatedCutoff m𝔽 Λ ε ρ)
    {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (I : W(β,s) →L[ℂ] W(α,s)) (hI : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[μ𝔽] q)
    (C : W(α,s) →L[ℂ] W(β,s))
    (hC : ∀ q, (C q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ (ρ g : ℂ) * lcaConvolution μ𝔽 φ.val q g) :
    I.comp C = (mask(α,s,hρ)).comp (act(hα,hs,φ)) ∧
      C.comp I = (mask(β,s,hρ)).comp (act(hβ,hs,φ)) := by
  have hconv (q : W(β,s)) (g : C𝔽) : lcaConvolution μ𝔽 φ.val (I q) g = lcaConvolution μ𝔽 φ.val q g := by
    have ht := ((measurePreserving_mul_right μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)).quasiMeasurePreserving
    apply integral_congr_ae
    filter_upwards [(hI q).comp_tendsto ht.tendsto_ae] with y hy
    exact congrArg (φ.val y * ·) hy
  constructor
  · apply ContinuousLinearMap.ext
    intro q
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have ha := hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs φ q
    have hm := (thetaMask_haar_ac α s).ae_eq (modulatedCutoffOperator_apply m𝔽 ν(α,s) hρ ((act(hα,hs,φ)) q))
    filter_upwards [hI (C q), hC q, ha, hm] with g hg₀ hg₁ hg₂ hg₃
    exact (hg₀.trans hg₁).trans ((congrArg ((ρ g : ℂ) * ·) hg₂.symm).trans hg₃.symm)
  · apply ContinuousLinearMap.ext
    intro q
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    have ha := hardySobolevTestAction_apply μ𝔽 m𝔽 (-β) β s (neg_le_self hβ) hs φ q
    have hm := (thetaMask_haar_ac β s).ae_eq (modulatedCutoffOperator_apply m𝔽 ν(β,s) hρ ((act(hβ,hs,φ)) q))
    filter_upwards [hC (I q), ha, hm] with g hg₁ hg₂ hg₃
    exact (hg₁.trans (congrArg ((ρ g : ℂ) * ·) (hconv q g))).trans
      ((congrArg ((ρ g : ℂ) * ·) hg₂.symm).trans hg₃.symm)


private theorem thetaMask_signed_trace {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [PolynormableSpace ℂ H] [PolynormableSpace ℂ K]
    (I : H →L[ℂ] K) (hi : Injective I) (C : K →L[ℂ] H) (hC : IsNuclearOperator C)
    (P : H →L[ℂ] H) (Q G : K →L[ℂ] K)
    (hcross : I.comp P - Q.comp I = G.comp (I.comp P)) :
    ∃ (hW : IsNuclearOperator (C.comp (I.comp P))) (hN : IsNuclearOperator (I.comp (C.comp Q)))
      (hD : IsNuclearOperator (C.comp (G.comp (I.comp P)))),
      hilbertTrace ⟨_, hW⟩ - hilbertTrace ⟨_, hN⟩ = hilbertTrace ⟨_, hD⟩ := by
  have hCQ : IsNuclearOperator (C.comp Q) := thetaMask_nuclear_composition C hC Q (ContinuousLinearMap.id ℂ _)
  have hn := isNuclearOperator_factor_comps I hi (C.comp Q) hCQ
  have hc : hilbertTrace ⟨_, hn.2⟩ = hilbertTrace ⟨_, hn.1⟩ := by
    rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
    exact (nuclearTrace_factor_comps (hilbert_approximationProperty (H := H))
      (hilbert_approximationProperty (H := K)) I hi (C.comp Q) hCQ).symm
  have hW : IsNuclearOperator (C.comp (I.comp P)) :=
    thetaMask_nuclear_composition C hC (I.comp P) (ContinuousLinearMap.id ℂ _)
  let T : nuclearEndomorphisms H := ⟨_, hW⟩
  let S : nuclearEndomorphisms H := ⟨_, hn.1⟩
  have heq : (T - S).val = C.comp (G.comp (I.comp P)) := by
    ext x
    change C (I (P x)) - C (Q (I x)) = C (G (I (P x)))
    rw [← map_sub]
    exact congrArg C (DFunLike.congr_fun hcross x)
  refine ⟨hW, hn.2, heq ▸ (T - S).property, ?_⟩
  rw [hc]
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H := H)
  calc
    hilbertTrace T - hilbertTrace S = hilbertTrace (T-S) := by rw [← htr T, ← htr S, ← map_sub, htr]
    _ = _ := congrArg hilbertTrace (Subtype.ext heq)


local notation "Θ(" a ", " h ", " hs ")" => globalThetaSobolev F a (neg_le_self h) hs
local notation "Ps(" a ", " h ", " hs ")" => spectralProjection (F := F) a h hs
local notation "Pg(" a ", " h ", " hs ")" => geometricProjection (F := F) a h hs

private theorem thetaMask_width_projection (a : ℝ) {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (I : W(β,s) →L[ℂ] W(α,s)) (hi : MapsTo I (Θ(a,hβ,hs) : Set _) (Θ(a,hα,hs) : Set _)) :
    I.comp (Ps(a,hβ,hs)) - (Ps(a,hα,hs)).comp I = (Pg(a,hα,hs)).comp (I.comp (Ps(a,hβ,hs))) := by
  apply ContinuousLinearMap.ext
  intro x
  have hdiff : x - (Ps(a,hβ,hs)) x = (Θ(a,hβ,hs)).starProjection x :=
    sub_eq_of_eq_add ((Θ(a,hβ,hs)).starProjection_add_starProjection_orthogonal x).symm
  have hg : I (x - (Ps(a,hβ,hs)) x) ∈ Θ(a,hα,hs) := hi (hdiff ▸ (Θ(a,hβ,hs)).starProjection_apply_mem x)
  have hzero : (Ps(a,hα,hs)) (I (x - (Ps(a,hβ,hs)) x)) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff (K := (Θ(a,hα,hs)).orthogonal)).mpr ((Θ(a,hα,hs)).le_orthogonal_orthogonal hg)
  rw [map_sub, map_sub, sub_eq_zero] at hzero
  change I ((Ps(a,hβ,hs)) x) - (Ps(a,hα,hs)) (I x) = (Pg(a,hα,hs)) (I ((Ps(a,hβ,hs)) x))
  rw [hzero]
  exact sub_eq_of_eq_add ((Θ(a,hα,hs)).starProjection_add_starProjection_orthogonal _).symm


/-- Paper: Definition 10.4.1.5 and Theorem 10.4.2.8, pp. 458 and 464. For a common
finite admissible physical cutoff, the spectral restriction trace at width `β`
minus the trace at width `α ≤ β` is exactly the trace of masked convolution after
wide spectral projection, restriction of physical representatives and narrow geometric
projection, in that order. This identity holds for every idèle-class Bruhat test. -/
theorem spectralRestriction_sub_trace_changeWidth (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hab : α ≤ β) (hs : 0 ≤ s) {Λ ε : ℝ} {ρ : C𝔽 → ℝ}
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε)
    (φ : BruhatCompactSupport C𝔽) :
    let hβ := hα.trans hab
    ∃ (I : W(β,s) →L[ℂ] W(α,s)) (C : W(α,s) →L[ℂ] W(β,s)),
      (∀ q, (I q : C𝔽 → ℂ) =ᵐ[μ𝔽] q) ∧ IsNuclearOperator C ∧
      (∀ q, (C q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ (ρ g : ℂ) * lcaConvolution μ𝔽 φ.val q g) ∧
      ∃ (hW : IsNuclearOperator (spectralRestriction a hβ hs hρ φ))
        (hN : IsNuclearOperator (spectralRestriction a hα hs hρ φ))
        (hD : IsNuclearOperator (C.comp ((Pg(a,hα,hs)).comp (I.comp (Ps(a,hβ,hs)))))),
        hilbertTrace ⟨_, hW⟩ - hilbertTrace ⟨_, hN⟩ = hilbertTrace ⟨_, hD⟩ := by
  intro hβ
  obtain ⟨I, _, hrep, _, _, himage, _⟩ := exists_spectralSobolevQuotient_widthRestriction (F := F) a hα hab hs
  have hI (q : W(β,s)) : (I q : C𝔽 → ℂ) =ᵐ[μ𝔽] q := (thetaMask_haar_ac α s).ae_eq (hrep q)
  have hi : Injective I := by
    intro q p heq
    apply Lp.ext
    apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
    exact (hI q).symm.trans (heq ▸ hI p)
  have hm : MapsTo I (Θ(a,hβ,hs) : Set _) (Θ(a,hα,hs) : Set _) := by
    intro q hq
    rw [← himage]
    exact subset_closure (mem_image_of_mem I hq)
  obtain ⟨C,hn,hC⟩ := exists_maskedConvolution_changeWidth hρ hband hα hs β φ
  obtain ⟨hIC,hCI⟩ := thetaMask_conjugate hρ hα hβ hs φ I hI C hC
  have hw : spectralRestriction a hβ hs hρ φ = C.comp (I.comp (Ps(a,hβ,hs))) :=
    ContinuousLinearMap.ext fun x ↦ (DFunLike.congr_fun hCI ((Ps(a,hβ,hs)) x)).symm
  have hnarrow : spectralRestriction a hα hs hρ φ = I.comp (C.comp (Ps(a,hα,hs))) :=
    ContinuousLinearMap.ext fun x ↦ (DFunLike.congr_fun hIC ((Ps(a,hα,hs)) x)).symm
  refine ⟨I,C,hI,hn,hC,?_⟩
  rw [hw,hnarrow]
  exact thetaMask_signed_trace I hi C hn (Ps(a,hβ,hs)) (Ps(a,hα,hs)) (Pg(a,hα,hs))
    (thetaMask_width_projection a hα hβ hs I hm)


attribute [local instance] instSpectralQuotientPolynormableSec3
local notation "Q(" a ", " h ", " hs ")" => spectralSobolevQuotient F a (neg_le_self h) hs
local notation "Aq(" a ", " h ", " hs ", " φ ")" => spectralConvolution (F := F) a (neg_le_self h) hs φ

/-- Paper: Theorem 10.4.2.8, pp. 463–464. For a fixed test and two nuclear
quotient convolutions, exhausting the physical cutoff recovers the difference
of their quotient traces from the mixed geometric block. -/
theorem spectralRestriction_changeWidth_trace_tendsto (a : ℝ) {α β s : ℝ}
    (hα : 0 ≤ α) (hab : α ≤ β) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (hWide : IsNuclearOperator (Aq(a,hα.trans hab,hs,φ)))
    (hNarrow : IsNuclearOperator (Aq(a,hα,hs,φ))) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ t : ℝ → ℂ, (∀ᶠ R in atTop, ∃ (I : W(β,s) →L[ℂ] W(α,s)) (C : W(α,s) →L[ℂ] W(β,s)),
      (∀ q, (I q : C𝔽 → ℂ) =ᵐ[μ𝔽] q) ∧ IsNuclearOperator C ∧
      (∀ q, (C q : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ (ρ R g : ℂ) * lcaConvolution μ𝔽 φ.val q g) ∧
      ∃ hD : IsNuclearOperator (C.comp ((Pg(a,hα,hs)).comp (I.comp (Ps(a,hα.trans hab,hs))))),
        t R = hilbertTrace ⟨_,hD⟩) ∧
      Tendsto t atTop (𝓝 (hilbertTrace (H := Q(a,hα.trans hab,hs)) ⟨Aq(a,hα.trans hab,hs,φ), hWide⟩ -
        hilbertTrace (H := Q(a,hα,hs)) ⟨Aq(a,hα,hs,φ), hNarrow⟩)) := by
  have wide := spectralRestriction_trace_tendsto (F := F) a (hα.trans hab) hs φ hWide ε ρ hε hρ
  have narrow := spectralRestriction_trace_tendsto (F := F) a hα hs φ hNarrow ε ρ hε hρ
  refine ⟨fun R ↦ wide.choose R - narrow.choose R, ?_, wide.choose_spec.2.sub narrow.choose_spec.2⟩
  filter_upwards [wide.choose_spec.1, narrow.choose_spec.1, hρ] with R hwR hnR hR
  obtain ⟨_, _, hew⟩ := hwR
  obtain ⟨_, _, hen⟩ := hnR
  obtain ⟨I,C,hI,hnC,hC,_,_,hD,ht⟩ := spectralRestriction_sub_trace_changeWidth
    a hα hab hs hR.1 hR.2 φ
  exact ⟨I,C,hI,hnC,hC,hD, (congrArg₂ (· - ·) hew hen).trans ht⟩


end RiemannMasullo
