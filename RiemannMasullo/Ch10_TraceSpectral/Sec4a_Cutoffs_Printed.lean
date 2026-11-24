module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

/-!
# Printed cutoff and spectral lift claims in §§10.4.1–10.4.2

The corresponding truncation and lift declarations are in `Sec4a.lean`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Classical NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "μ[" F "]" => ideleClassTamagawaMeasure F
local notation "logNorm[" F "]" => (logIdeleClassNorm F)

/-- Paper: §10.4, introduction, p. 455. As printed: on the symmetric
interval Sobolev space, multiplication by a smooth cutoff has closed range.
The multiplier used in `spectralTruncation` is bounded (ERRATA F186). -/
def Printed.smoothCutoffMultiplier_isClosedRange : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α s : ℝ), 0 ≤ α → 1 < s →
    ∀ (Λ ε : ℝ) (ρ : C[F] → ℝ) (hρ : IsSmoothModulatedCutoff m[F] Λ ε ρ),
      let ν := (μ[F]).withDensity (fun g ↦
        ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm[F] g)))
      IsClosed (range (modulatedCutoffOperator m[F] ν hρ.1))

private theorem sec4a_not_isClosed_range_of_small_images {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hclosed : IsClosed (Set.range T))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ u : E, ‖u‖ ≠ 0 ∧ ‖T u‖ ≤ δ * ‖u‖ ∧
      ∀ x : E, T x = T u → ‖u‖ ≤ ‖x‖) : False := by
  have hclosed' : IsClosed (LinearMap.range (T : E →ₗ[ℂ] E) : Set E) := by
    simpa only [LinearMap.coe_range, ContinuousLinearMap.coe_coe] using hclosed
  have : CompleteSpace (LinearMap.range (T : E →ₗ[ℂ] E)) := hclosed'.completeSpace_coe
  let S : E →L[ℂ] LinearMap.range (T : E →ₗ[ℂ] E) :=
    T.codRestrict (LinearMap.range (T : E →ₗ[ℂ] E)) fun x ↦ ⟨x, rfl⟩
  have hsurj : Function.Surjective S := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨C, hCpos, hC⟩ := S.exists_preimage_norm_le hsurj
  obtain ⟨u, hu_ne, hu_img, hu_min⟩ := hsmall (1 / (2 * C)) (by positivity)
  obtain ⟨x, hx_eq, hx_norm⟩ := hC (S u)
  have hTx : T x = T u := congrArg Subtype.val hx_eq
  have hu_le_x : ‖u‖ ≤ ‖x‖ := hu_min x hTx
  have hx_le : ‖x‖ ≤ C * ‖T u‖ := hx_norm
  have hu_le : ‖u‖ ≤ (1 / 2 : ℝ) * ‖u‖ := by
    calc ‖u‖ ≤ ‖x‖ := hu_le_x
      _ ≤ C * ‖T u‖ := hx_le
      _ ≤ C * ((1 / (2 * C)) * ‖u‖) := mul_le_mul_of_nonneg_left hu_img hCpos.le
      _ = (1 / 2 : ℝ) * ‖u‖ := by field_simp [hCpos.ne']
  have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) hu_ne.symm
  linarith

private theorem sec4a_small_cutoff_measure {ρ : C[ℚ] → ℝ}
    (hρ : IsSmoothModulatedCutoff m[ℚ] 2 (1 / 4) ρ) (δ : ℝ) (hδ : 0 < δ) :
    let ν := (μ[ℚ]).withDensity (fun g ↦
      ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)))
    let U := ρ ⁻¹' Ioo 0 δ
    MeasurableSet U ∧ 0 < ν U ∧ ν U < ⊤ := by
  intro ν U
  have hUopen : IsOpen U := isOpen_Ioo.preimage hρ.continuous
  have hUmeas : MeasurableSet U := hUopen.measurableSet
  let uReal : ℝ → ℝ≥0ˣ := fun t ↦
    ⟨⟨max t (2⁻¹ : ℝ), by positivity⟩, ⟨(max t (2⁻¹ : ℝ))⁻¹, by positivity⟩,
      Subtype.ext (mul_inv_cancel₀ (by positivity)),
      Subtype.ext (inv_mul_cancel₀ (by positivity))⟩
  have huReal : Continuous uReal := by
    rw [Units.continuous_iff]
    exact ⟨(continuous_id.max continuous_const).subtype_mk _,
      ((continuous_id.max continuous_const).inv₀ fun _ ↦ by positivity).subtype_mk _⟩
  let σ : ℝ → C[ℚ] := fun t ↦
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) (ratIdeleNormSection (uReal t))
  have hσ : Continuous σ :=
    QuotientGroup.continuous_mk.comp (ratIdeleNormSection_continuous.comp huReal)
  have hσm (t : ℝ) (ht : (2⁻¹ : ℝ) ≤ t) : ((m[ℚ] (σ t)).val : ℝ) = t := by
    change ((ideleClassNorm ℚ (σ t)).val : ℝ) = t
    rw [show ideleClassNorm ℚ (σ t) = uReal t from ratIdeleNormSection_class_rightInverse (uReal t)]
    exact max_eq_left ht
  have hUne : U.Nonempty := by
    have hρ1 : ρ (σ 1) = 1 := hρ.1.eq_one (by
      change ((m[ℚ] (σ 1)).val : ℝ) ∈ Icc ((2 : ℝ)⁻¹ + 1 / 4) (2 - 1 / 4)
      rw [hσm 1 (by norm_num)]
      norm_num)
    have hρ3 : ρ (σ 3) = 0 := by
      by_contra hne
      have hsub := hρ.1.support_subset (subset_closure (Function.mem_support.mpr hne))
      change ((m[ℚ] (σ 3)).val : ℝ) ∈ Icc (2⁻¹ : ℝ) 2 at hsub
      rw [hσm 3 (by norm_num)] at hsub
      linarith [hsub.2]
    let δ₀ : ℝ := min (δ / 2) (1 / 2)
    have hδ₀_mem : δ₀ ∈ Icc (ρ (σ 3)) (ρ (σ 1)) := by
      rw [hρ3, hρ1]
      exact ⟨le_min (by linarith) (by norm_num), min_le_of_right_le (by norm_num)⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc' (show (1 : ℝ) ≤ 3 by norm_num)
      (hρ.continuous.comp hσ).continuousOn hδ₀_mem
    refine ⟨σ t, ?_⟩
    have ht' : ρ (σ t) = δ₀ := ht
    change ρ (σ t) ∈ Ioo 0 δ
    rw [ht']
    exact ⟨lt_min (by linarith) (by norm_num), (min_le_left _ _).trans_lt (by linarith)⟩
  have hHaar : (μ[ℚ]).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hμpos : 0 < μ[ℚ] U := hUopen.measure_pos (μ[ℚ]) hUne
  have hw_ge (g : C[ℚ]) :
      (1 : ENNReal) ≤ ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    dsimp [intervalSobolevDensity]
    norm_num
    exact sq_nonneg _
  have hνpos : 0 < ν U := by
    refine hμpos.trans_le ?_
    rw [withDensity_apply _ hUmeas]
    calc μ[ℚ] U = ∫⁻ _ in U, (1 : ENNReal) ∂μ[ℚ] := by simp
      _ ≤ ∫⁻ g in U, ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ∂μ[ℚ] :=
        setLIntegral_mono' hUmeas fun g _ ↦ hw_ge g
  let K' : Set ℝ≥0ˣ := uReal '' Icc (2⁻¹ : ℝ) 2
  have hK'compact : IsCompact K' := isCompact_Icc.image huReal
  let K : Set C[ℚ] := m[ℚ] ⁻¹' K'
  have hKcompact : IsCompact K := (isProperMap_ideleClassNorm ℚ).isCompact_preimage hK'compact
  have hKmeas : MeasurableSet K := (hK'compact.isClosed.preimage m[ℚ].continuous).measurableSet
  have hμK_lt_top : μ[ℚ] K < ⊤ := hKcompact.measure_lt_top
  have hUK : U ⊆ K := by
    intro g hg
    have hsupp := hρ.1.support_subset (subset_closure (Function.mem_support.mpr hg.1.ne'))
    change ((m[ℚ] g).val : ℝ) ∈ Icc (2⁻¹ : ℝ) 2 at hsupp
    refine ⟨((m[ℚ] g).val : ℝ), hsupp, ?_⟩
    apply Units.ext
    ext
    exact max_eq_left hsupp.1
  have hw_le (g : C[ℚ]) (hg : g ∈ K) :
      ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ≤
        ENNReal.ofReal (1 + (Real.log 2) ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨r, hr, hrg⟩ := hg
    have hmr : ((ideleClassNorm ℚ g).val : ℝ) = r := by
      have : (m[ℚ] g).val = (uReal r).val := congrArg Units.val hrg.symm
      exact (congrArg NNReal.toReal this).trans (max_eq_left hr.1)
    have hlog_le : |Real.log r| ≤ Real.log 2 := by
      rw [abs_le, ← Real.log_inv]
      have hrpos : 0 < r := by linarith [hr.1]
      exact ⟨(Real.log_le_log_iff (by norm_num) hrpos).mpr hr.1,
        (Real.log_le_log_iff hrpos (by norm_num)).mpr hr.2⟩
    have hsq : (Real.log ((ideleClassNorm ℚ g).val : ℝ)) ^ 2 ≤ (Real.log 2) ^ 2 := by
      rw [hmr, ← sq_abs (Real.log r)]
      exact pow_le_pow_left₀ (abs_nonneg _) hlog_le 2
    dsimp [intervalSobolevDensity]
    norm_num
    linarith [hsq]
  have hνfin : ν U < ⊤ := by
    calc ν U ≤ ν K := measure_mono hUK
      _ = ∫⁻ g in K, ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)) ∂μ[ℚ] :=
        withDensity_apply _ hKmeas
      _ ≤ ∫⁻ _ in K, ENNReal.ofReal (1 + (Real.log 2) ^ 2) ∂μ[ℚ] :=
        setLIntegral_mono' hKmeas hw_le
      _ = ENNReal.ofReal (1 + (Real.log 2) ^ 2) * μ[ℚ] K := setLIntegral_const K _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK_lt_top
  exact ⟨hUmeas, hνpos, hνfin⟩

/-- Paper: §10.4, introduction, p. 455. Use `F = ℚ`, `α = 0`, `s = 2`,
`Λ = 2` and `ε = 1/4`. In log norm choose an even smooth cutoff equal to
one on `|x| ≤ log(7/4)`, strictly tapering on `log(7/4) < |x| < log 2`,
and zero on `|x| ≥ log 2`. The normalized indicators of `0 < ρ < 1/n`
are unit vectors perpendicular to the kernel and their images have norm at
most `1/n`, contradicting the lower bound for an operator with closed range. -/
theorem Printed.smoothCutoffMultiplier_isClosedRange_false :
    ¬ Printed.smoothCutoffMultiplier_isClosedRange := by
  intro h
  have hmℚ : IsModulation m[ℚ] := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hmsℚ : Function.Surjective m[ℚ] := ratIdeleNormSection_class_rightInverse.surjective
  obtain ⟨ρ, hρ⟩ := exists_smoothModulatedCutoff_radius_two m[ℚ] hmℚ hmsℚ
  let ν := (μ[ℚ]).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm[ℚ] g)))
  let ν₀ := (μ[ℚ]).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity (-(0 : ℝ)) 0 2 (logNorm[ℚ] g)))
  have hνeq : ν₀ = ν := by dsimp only [ν₀, ν]; simp only [neg_zero]
  let T := modulatedCutoffOperator m[ℚ] ν hρ.1
  have hclosed0 : IsClosed (Set.range (modulatedCutoffOperator m[ℚ] ν₀ hρ.1)) :=
    h ℚ 0 2 (by norm_num) (by norm_num) 2 (1 / 4) ρ hρ
  have hclosed : IsClosed (Set.range T) := by
    dsimp only [T]
    rw [← hνeq]
    exact hclosed0
  refine sec4a_not_isClosed_range_of_small_images T hclosed fun δ hδ ↦ ?_
  obtain ⟨hUmeas, hUpos, hUfin⟩ := sec4a_small_cutoff_measure hρ δ hδ
  let U : Set C[ℚ] := ρ ⁻¹' Ioo 0 δ
  let u : Lp ℂ 2 ν := indicatorConstLp 2 hUmeas hUfin.ne (1 : ℂ)
  refine ⟨u, ?_, ?_, ?_⟩
  · have hnorm : ‖u‖ = ‖(1 : ℂ)‖ * ν.real U ^ (1 / (2 : ENNReal).toReal) :=
      norm_indicatorConstLp (by norm_num) (by norm_num)
    have hreal : 0 < ν.real U := ENNReal.toReal_pos hUpos.ne' hUfin.ne
    have hpos : 0 < ‖u‖ := by
      rw [hnorm, norm_one, one_mul]
      exact Real.rpow_pos_of_pos hreal _
    exact hpos.ne'
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [modulatedCutoffOperator_apply m[ℚ] ν hρ.1 u,
      indicatorConstLp_coeFn (p := 2) (hs := hUmeas) (hμs := hUfin.ne) (c := (1 : ℂ))] with g hTg hug
    change ‖T u g‖ ≤ δ * ‖u g‖
    rw [hTg, norm_mul, Complex.norm_real]
    by_cases hg : g ∈ U
    · have hρ_abs : |ρ g| ≤ δ := by
        have hmem : ρ g ∈ Ioo 0 δ := hg
        rw [abs_of_pos hmem.1]
        exact hmem.2.le
      exact mul_le_mul_of_nonneg_right hρ_abs (norm_nonneg _)
    · have hu0 : u g = 0 := hug.trans (indicator_of_notMem hg _)
      simp [hu0]
  · intro x hTx
    apply Lp.norm_le_norm_of_ae_le
    have hEq : (T x : C[ℚ] → ℂ) =ᵐ[ν] (T u : C[ℚ] → ℂ) := by rw [hTx]
    filter_upwards [hEq, modulatedCutoffOperator_apply m[ℚ] ν hρ.1 x,
      modulatedCutoffOperator_apply m[ℚ] ν hρ.1 u,
      indicatorConstLp_coeFn (p := 2) (hs := hUmeas) (hμs := hUfin.ne) (c := (1 : ℂ))]
      with g hgg hx hu hug
    by_cases hg : g ∈ U
    · have hρne : (ρ g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show ρ g ≠ 0 from hg.1.ne')
      have hmul : (ρ g : ℂ) * x g = (ρ g : ℂ) * u g := by
        rw [← hx, ← hu]
        exact hgg
      have hux : u g = x g := (mul_left_cancel₀ hρne hmul).symm
      rw [hux]
    · have hu0 : u g = 0 := hug.trans (indicator_of_notMem hg _)
      simp [hu0]

/-- Paper: Remark 10.4.2.3, p. 460. As printed: at each admissible radius
the cutoff is continuous on the idele class group. This is the continuity
clause following (10.4.2.10). The cutoff hypotheses of
`spectralTruncatedConvolution_trace_tendsto` allow piecewise smooth profiles (ERRATA F188). -/
def Printed.spectralCutoffFamily_continuous : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ε : ℝ → ℝ) (ρ : ℝ → C[F] → ℝ),
    Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) →
    let admissible := fun Λ ↦ IsModulatedCutoff m[F] Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ
    (∀ᶠ Λ in atTop, admissible Λ) → ∀ Λ, admissible Λ → Continuous (ρ Λ)

private theorem sec4a_ideleClassNorm_rat_surjective :
    Function.Surjective (ideleClassNorm ℚ) :=
  ratIdeleNormSection_class_rightInverse.surjective

/-- Paper: Remark 10.4.2.3, p. 460. Over ℚ take `ε(Λ) = 1/(2Λ²)` and
let `ρ(Λ)` be the indicator of `Λ⁻¹ ≤ |g|_F ≤ Λ`. For `Λ > 2`
these are admissible cutoffs. Each jumps at both endpoints along the
continuous positive-real section of the idelic norm. -/
theorem Printed.spectralCutoffFamily_continuous_false :
    ¬ Printed.spectralCutoffFamily_continuous := by
  intro h
  let ε : ℝ → ℝ := fun Λ ↦ 1 / (2 * Λ ^ 2)
  let ρ : ℝ → C[ℚ] → ℝ := fun Λ g ↦
    if ((m[ℚ] g).val : ℝ) ∈ Icc Λ⁻¹ Λ then 1 else 0
  have hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0) := by
    have hEq : (fun Λ : ℝ ↦ ε Λ * Λ) =ᶠ[atTop] fun Λ ↦ (1 / 2 : ℝ) * Λ⁻¹ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with Λ hΛ
      dsimp [ε]
      field_simp [hΛ.ne']
    refine Tendsto.congr' hEq.symm ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul
      (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hcont : Continuous (ρ 2) :=
    h ℚ ε ρ hε ((eventually_ge_atTop 2).mono fun Λ hΛ ↦ isModulatedCutoff_closedBand m[ℚ] Λ hΛ)
      2 (isModulatedCutoff_closedBand m[ℚ] 2 le_rfl)
  let u : Ioi (0 : ℝ) → ℝ≥0ˣ := fun t ↦
    ⟨⟨t.1, t.2.le⟩, ⟨t.1⁻¹, (inv_pos.mpr t.2).le⟩,
      Subtype.ext (mul_inv_cancel₀ t.2.ne'), Subtype.ext (inv_mul_cancel₀ t.2.ne')⟩
  have hu : Continuous u := by
    rw [Units.continuous_iff]
    exact ⟨continuous_subtype_val.subtype_mk _,
      (continuous_subtype_val.inv₀ fun t ↦ t.2.ne').subtype_mk _⟩
  let σ : Ioi (0 : ℝ) → C[ℚ] := fun t ↦
    QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ) (ratIdeleNormSection (u t))
  have hσ : Continuous σ :=
    QuotientGroup.continuous_mk.comp (ratIdeleNormSection_continuous.comp hu)
  have hσm (t : Ioi (0 : ℝ)) : ((m[ℚ] (σ t)).val : ℝ) = t.1 := by
    change ((ideleClassNorm ℚ (σ t)).val : ℝ) = t.1
    rw [show ideleClassNorm ℚ (σ t) = u t from ratIdeleNormSection_class_rightInverse (u t)]
    rfl
  have hcomp : Continuous (fun t : Ioi (0 : ℝ) ↦ ρ 2 (σ t)) := hcont.comp hσ
  let x₀ : Ioi (0 : ℝ) := ⟨2, by norm_num⟩
  let seq : ℕ → Ioi (0 : ℝ) := fun n ↦ ⟨2 + 1 / ((n : ℝ) + 1), mem_Ioi.mpr (by positivity)⟩
  have hseq : Tendsto seq atTop (𝓝 x₀) := by
    rw [tendsto_subtype_rng]
    have hLim : Tendsto (fun n : ℕ ↦ (2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 2) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (2 : ℝ))).add
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact hLim
  have h1 : Tendsto (fun n ↦ ρ 2 (σ (seq n))) atTop (𝓝 1) := by
    have hx₀ : ρ 2 (σ x₀) = 1 := by
      dsimp [ρ]
      rw [hσm x₀]
      split_ifs with hmem
      · rfl
      · exact False.elim (hmem ⟨by norm_num, by norm_num⟩)
    simpa only [hx₀, Function.comp_def] using (hcomp.continuousAt.tendsto).comp hseq
  have h0 : (fun n ↦ ρ 2 (σ (seq n))) = fun _ ↦ 0 := by
    funext n
    dsimp [ρ]
    rw [hσm (seq n)]
    split_ifs with hmem
    · exfalso
      have : 2 < (seq n).1 := by
        dsimp [seq]
        linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
      linarith [hmem.2]
    · rfl
  rw [h0] at h1
  exact one_ne_zero (tendsto_nhds_unique (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 1) from h1)
    (tendsto_const_nhds (x := (0 : ℝ))))

local notation "W[" F ", " α ", " s "]" =>
  CompactIntervalSobolev μ[F] logNorm[F] (-α) α s
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. As printed:
ambient biorthogonal lifts of the strip basis can be chosen with a common
upper bound `C + ε`. The indices and the pullback of the coefficient
functionals use `s + b + it` from (10.4.2.21) and `a + b + it` from
(10.4.2.22), respectively, with the full multiplicity displayed there.
The basis vectors belong to the quotient isotype of the fixed character.
Their coefficients pull back to Haar integration, and their ambient lifts
satisfy the upper half of (10.4.2.24) for each permitted ε.
The lemma `exists_biorthogonalBasisLift` assumes a collar for the quotient
vectors (ERRATA F191). -/
def Printed.spectralStripBasisLift_uniformUpperBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (a α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s),
    let hI := (neg_nonpos.mpr hα).trans hα
    let N := globalThetaSobolev F a hI hs
    let Q := spectralSobolevQuotient F a hI hs
    let res : (ideleClassNorm F).ker →ₜ* C[F] :=
      ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    letI := instClosedSpectralIsotypeThetaSec2 (F := F) a hI hs (χ.comp res)
    let B := spectralSobolevIsotypeQuotient F a hI hs (χ.comp res)
    let incl : B →ₗ[ℂ] Q := Submodule.mapQ _ N (Submodule.subtype _) le_rfl
    let J := {j : ℝ × ℝ × ℕ // j.1 ∈ Icc (-α) α ∧ j.2.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) (shift(s + j.1, j.2.1))).untop₀.toNat}
    let η := fun i : J ↦ spectralZeroJet χ (a + i.val.1) i.val.2.1 i.val.2.2
    ∃ (ψ : J → B) (d : J → StrongDual ℂ B) (D : J → StrongDual ℂ Q) (C : ℝ), 0 < C ∧
      IsSpectralMarkushevichBasis ψ d ∧ (∀ i y, d i y = D i (incl y)) ∧
      (∀ (i : J) (v : W[F, α, s]), Integrable (fun g ↦ v g * η i g) μ[F] ∧
        D i (N.mkQ v) = ∫ g, v g * η i g ∂μ[F]) ∧
      ∀ ε : ℝ, 0 < ε → ε < C⁻¹ → ∃ u : J → W[F, α, s],
        ∀ j, N.mkQ (u j) = incl (ψ j) ∧ ‖u j‖ < C + ε

/-- The class logarithmic norm pushes Haar measure forward to a positive multiple
of Lebesgue measure. This uses the proper quotient map as in
`exists_map_logClassNorm_eq_smul_volume` in Appendix B. -/
private theorem sec4a_basisLift_radialIntegrable_iff {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable (f ∘ logNorm[ℚ]) μ[ℚ] ↔ Integrable f volume := by
  let μ := μ[ℚ]
  let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := ℚ)).1
  let : ν.IsHaarMeasure := by
    have : IsFiniteMeasureOnCompacts ν :=
      inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    have : Measure.IsOpenPosMeasure ν :=
      inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    have : ν.IsMulLeftInvariant :=
      ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
    constructor
  let e : ℝ≥0ˣ ≃ₜ ℝ :=
    (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let m : C[ℚ] →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (e (ideleClassNorm ℚ g))
      map_one' := by
        change e (ideleClassNorm ℚ 1) = 0
        simp [he]
      map_mul' := fun g h ↦ by
        change e (ideleClassNorm ℚ (g * h)) = e (ideleClassNorm ℚ g) + e (ideleClassNorm ℚ h)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
          (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' }
  have hm : IsProperMap m := e.isProperMap.comp (isProperMap_ideleClassNorm ℚ)
  have hsurj : Function.Surjective m := e.surjective.comp sec4a_ideleClassNorm_rat_surjective
  let : (μ.map m).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ m hm.continuous hsurj (isProperMap_iff_tendsto_cocompact.mp hm).2
  have hFun : (m : C[ℚ] → ℝ) = logNorm[ℚ] := funext fun g ↦ he (ideleClassNorm ℚ g)
  have hmap := Measure.isMulLeftInvariant_eq_smul (μ.map m) ν
  let c := Measure.haarScalarFactor (μ.map m) ν
  have hpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hρ : Measure.map logNorm[ℚ] μ = c • (volume : Measure ℝ) := by
    rw [← hFun]
    exact hmap
  have hmeas : Measurable logNorm[ℚ] := hFun ▸ hm.continuous.measurable
  rw [← integrable_map_measure hf.aestronglyMeasurable hmeas.aemeasurable, hρ]
  exact integrable_smul_measure (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top

/-- In degree zero, the boundary jet has a divergent pairing with a weighted L²
test whose logarithmic profile is exp(−x)/x on x > 1. -/
private theorem sec4a_basisLift_boundary_not_integrable (t : ℝ) :
    ∃ v : W[ℚ, (1 : ℝ), (0 : ℝ)],
      ¬ Integrable (fun g ↦ v g * spectralZeroJet (1 : PontryaginDual C[ℚ]) 1 t 0 g) μ[ℚ] := by
  let μ := μ[ℚ]
  let L := logNorm[ℚ]
  let w := intervalSobolevDensity (-1) 1 0
  let d (g : C[ℚ]) := ENNReal.ofReal (w (L g))
  let η := spectralZeroJet (1 : PontryaginDual C[ℚ]) 1 t 0
  let f : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x ↦ ((Real.exp (-x) * x⁻¹ : ℝ) : ℂ))
  let p : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun x ↦ x⁻¹)
  let q : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (fun x ↦ (x⁻¹) ^ 2)
  have hL : Measurable L := Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (m[ℚ]).continuous)).measurable
  have hw (x : ℝ) : w x = max (Real.exp (-2 * x)) (Real.exp (2 * x)) := by
    simp only [w, intervalSobolevDensity, zero_div, Real.rpow_zero, mul_one]
    congr 2
    ring
  have hwp (x : ℝ) : 0 < w x := by rw [hw]; exact (Real.exp_pos _).trans_le (le_max_right _ _)
  have hwr {x : ℝ} (hx : 1 < x) : w x = Real.exp (2 * x) := by
    rw [hw, max_eq_right (Real.exp_le_exp.mpr (by linarith))]
  have hwm : Measurable w := by
    rw [show w = fun x ↦ max (Real.exp (-2 * x)) (Real.exp (2 * x)) from funext hw]
    fun_prop
  have hd : Measurable d := (hwm.comp hL).ennreal_ofReal
  have hq : Measurable q := (measurable_inv.pow_const 2).indicator measurableSet_Ioi
  have hp : Measurable p := measurable_inv.indicator measurableSet_Ioi
  have hf : Measurable f :=
    (Complex.continuous_ofReal.measurable.comp ((by fun_prop : Measurable (fun x : ℝ ↦
      Real.exp (-x))).mul measurable_inv)).indicator measurableSet_Ioi
  have hqint : Integrable q volume := by
    rw [show q = (Ioi (1 : ℝ)).indicator (fun x ↦ (x⁻¹) ^ 2) from rfl,
      integrable_indicator_iff measurableSet_Ioi]
    simpa only [← inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow, Nat.cast_ofNat]
      using (integrableOn_Ioi_rpow_of_lt (a := -2) (c := 1) (by norm_num) zero_lt_one)
  have hqnorm (x : ℝ) : ‖f x‖ ^ 2 * w x = q x := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · have hx' : 1 < x := hx
      rw [show f x = ((Real.exp (-x) * x⁻¹ : ℝ) : ℂ) from indicator_of_mem hx _,
        show q x = (x⁻¹) ^ 2 from indicator_of_mem hx _, hwr hx', Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (by linarith))),
        Real.exp_neg, show Real.exp (2 * x) = Real.exp x ^ 2 by
          rw [two_mul, Real.exp_add, pow_two]]
      field_simp [Real.exp_ne_zero]
    · simp only [f, q, indicator_of_notMem hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul]
  have hmem : MemLp (f ∘ L) 2 (μ.withDensity d) := by
    apply (memLp_two_iff_integrable_sq_norm (hf.comp hL).aestronglyMeasurable).mpr
    apply (integrable_withDensity_iff hd (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    refine (sec4a_basisLift_radialIntegrable_iff hq |>.mpr hqint).congr
      (ae_of_all μ fun g ↦ ?_)
    change q (L g) = ‖f (L g)‖ ^ 2 * (ENNReal.ofReal (w (L g))).toReal
    rw [ENNReal.toReal_ofReal (hwp _).le, hqnorm]
  let v : W[ℚ, (1 : ℝ), (0 : ℝ)] := hmem.toLp _
  refine ⟨v, fun hv ↦ ?_⟩
  have hμν : μ ≪ μ.withDensity d := withDensity_absolutelyContinuous' hd.aemeasurable
    (ae_of_all μ fun g ↦ (ENNReal.ofReal_pos.mpr (hwp (L g))).ne')
  have hcoe : (v : C[ℚ] → ℂ) =ᵐ[μ] f ∘ L :=
    (MemLp.coeFn_toLp hmem).filter_mono hμν.ae_le
  have hjet (g : C[ℚ]) : ‖η g‖ = Real.exp (L g) := by
    change ‖spectralZeroJet (1 : PontryaginDual C[ℚ]) 1 t 0 g‖ = _
    unfold spectralZeroJet
    rw [pow_zero, mul_one]
    change ‖((1 : PontryaginDual C[ℚ]) g : ℂ) *
      (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ shift((1 : ℝ), t)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    have ht : (shift((1 : ℝ), t)).re = 1 := by norm_num [Complex.mul_re]
    rw [ht, Real.rpow_one]
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  have hnorm (x : ℝ) : ‖f x‖ * Real.exp x = p x := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · have hx' : 1 < x := hx
      rw [show f x = ((Real.exp (-x) * x⁻¹ : ℝ) : ℂ) from indicator_of_mem hx _,
        show p x = x⁻¹ from indicator_of_mem hx _, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (inv_nonneg.mpr (by linarith))),
        Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    · simp [f, p, hx]
  have hprod : Integrable (p ∘ L) μ := by
    refine hv.norm.congr ?_
    filter_upwards [hcoe] with g hg
    change ‖v g * η g‖ = p (L g)
    rw [norm_mul, hg, Function.comp_apply, hjet, hnorm]
  have hbad := (sec4a_basisLift_radialIntegrable_iff hp).mp hprod
  exact not_integrableOn_Ioi_inv
    ((integrable_indicator_iff measurableSet_Ioi).mp hbad)

private theorem sec4a_basisLift_false_of_zero (t : ℝ)
    (ht : 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C[ℚ]))
      (shift((1 / 2 : ℝ), t))).untop₀.toNat) :
    ¬ Printed.spectralStripBasisLift_uniformUpperBound := by
  intro hall
  obtain ⟨_, _, _, _, _, _, _, hpair, _⟩ :=
    hall ℚ (1 : PontryaginDual C[ℚ]) (1 / 2) 1 0 (by norm_num) (by norm_num)
  let j : { j : ℝ × ℝ × ℕ // j.1 ∈ Icc (-1) 1 ∧ j.2.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C[ℚ]))
        (shift((0 : ℝ) + j.1, j.2.1))).untop₀.toNat } :=
    ⟨(1 / 2, t, 0), by norm_num, by simpa only [zero_add] using ht⟩
  obtain ⟨v, hv⟩ := sec4a_basisLift_boundary_not_integrable t
  apply hv
  have hi := (hpair j v).1
  change Integrable (fun g ↦ v g *
    spectralZeroJet (1 : PontryaginDual C[ℚ]) ((1 / 2 : ℝ) + 1 / 2) t 0 g) μ[ℚ] at hi
  simpa only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using hi

/-- A certified critical-line zero supplies an index for the rational
trivial-character strip. The order comparison follows the rational zero
argument in Chapter 13. -/
private theorem sec4a_basisLift_rational_zero :
    ∃ t : ℝ, 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C[ℚ]))
      (shift((1 / 2 : ℝ), t))).untop₀.toNat := by
  obtain ⟨t, _, ht⟩ := HardyFirstZero.first_zero_on_line
  let z := shift((1 / 2 : ℝ), t)
  have hne : z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [z] at this
  have ha := analyticOn_riemannZeta z hne
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C[ℚ])
    hm (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by norm_num [z])
  have hz2 : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 := by
    have h := analyticOn_riemannZeta 2 (by norm_num : (2 : ℂ) ≠ 1)
    rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
    rfl
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [hz2]; simp)
  have hpos : analyticOrderAt riemannZeta z ≠ 0 :=
    ha.analyticOrderAt_ne_zero.mpr (by simpa [z, Complex.ofReal_div] using ht)
  refine ⟨t, ?_⟩
  change 0 < (meromorphicOrderAt _ z).untop₀.toNat
  rw [← he, ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hfin
  generalize analyticOrderAt riemannZeta z = k at hfin hpos ⊢
  cases k using ENat.recTopCoe with
  | top => simp at hfin
  | coe n =>
    have hn : n ≠ 0 := by simpa using hpos
    simpa using Nat.pos_of_ne_zero hn

/-- Paper: Theorem 10.4.2.8, proof, (10.4.2.24), p. 463. In the printed
formulation the coefficient functionals must be given by integrable pairings
on the ambient Sobolev space. For the rational trivial character, take
`a = 1/2`, `α = 1`, and `s = 0`. The `b = 1/2` index from a certified
critical-line zero places the order-zero jet on the Sobolev boundary, where
the pairing diverges on a weighted L² test. -/
theorem Printed.spectralStripBasisLift_uniformUpperBound_false :
    ¬ Printed.spectralStripBasisLift_uniformUpperBound := by
  obtain ⟨t, ht⟩ := sec4a_basisLift_rational_zero
  exact sec4a_basisLift_false_of_zero t ht

end RiemannMasullo
