module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

/-! # §10.1 assertions that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing

namespace RiemannMasullo

local instance instSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (SIdeleQuotient F S) := borel _

local instance instIdeleClassMeasurableSpaceSec1Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

local instance instNormOneSIdeleQuotientMeasurableSpaceSec1Printed
    (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (sIdeleQuotientNorm F S).ker := borel _

/-- Paper: Before (10.1.1.2), p. 434. The interval norm is finite on every
weighted global polar-free theta function for every closed interval with interior. -/
def Printed.globalThetaSobolev_closedIntervals_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 ≤ s →
    ∀ I : Set ℝ, IsClosed I → OrdConnected I → (interior I).Nonempty →
    ∀ f : adelePolarSubspace F,
      let m := (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
        IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (ideleClassTamagawaMeasure F) (fun g ↦ Real.log ((m g).val : ℝ))
        I s (modulationWeight m a (adelicTheta f.val)) ≠ ⊤

/-- If the interval contains the nonnegative half-line, a nonzero value
at positive log norm forces the supremum of the weighted L² norms to be infinite. -/
private theorem intervalSobolevENorm_eq_top_of_positive_logNorm
    {G : Type*} [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (μ : Measure G) [μ.IsOpenPosMeasure]
    (I : Set ℝ) (hI : Ici 0 ⊆ I) (r : G → ℝ) (hr : Continuous r) (θ : G → ℂ) (hθ : Continuous θ)
    (g : G) (hrg : 0 < r g) (hθg : θ g ≠ 0) :
    intervalSobolevENorm μ r I 0 θ = ⊤ := by
  let c := ‖θ g‖ / 2
  have hc : 0 < c := half_pos (norm_pos_iff.mpr hθg)
  have hcg : c < ‖θ g‖ := half_lt_self (norm_pos_iff.mpr hθg)
  let U := {x | c < ‖θ x‖} ∩ {x | r g / 2 < r x}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hθ.norm).inter (isOpen_lt continuous_const hr)
  have hgU : g ∈ U := ⟨hcg, half_lt_self hrg⟩
  have hUpos : μ U ≠ 0 := (hUo.measure_pos μ ⟨g, hgU⟩).ne'
  have hε : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hbound : ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * r g)) * μ U ≤
      (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        intervalSobolevENorm μ r I 0 θ ^ (2 : ℝ≥0∞).toReal := by
    intro σ hσ
    have hle : eLpNorm θ 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) ≤
        intervalSobolevENorm μ r I 0 θ := by
      unfold intervalSobolevENorm
      exact le_iSup₂_of_le (⟨0, hI le_rfl⟩ : I) (⟨σ, hI hσ⟩ : I) le_rfl
    have hdens : ∀ x ∈ U, ENNReal.ofReal (Real.exp (σ * r g)) ≤
        ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      have he : Real.exp (σ * r g) ≤ Real.exp (2 * σ * r x) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx.2.le hσ])
      simpa only [intervalSobolevDensity, zero_div, Real.rpow_zero, mul_one] using
        he.trans (le_max_right (Real.exp (2 * 0 * r x)) _)
    calc ENNReal.ofReal (Real.exp (σ * r g)) * μ U
        = ∫⁻ _ in U, ENNReal.ofReal (Real.exp (σ * r g)) ∂μ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)) ∂μ :=
          setLIntegral_mono' hUo.measurableSet hdens
      _ = (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) U :=
          (withDensity_apply _ hUo.measurableSet).symm
      _ ≤ (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x)))
            {x | ENNReal.ofReal c ≤ ‖θ x‖ₑ} := measure_mono fun x hx ↦ by
          rw [mem_ofPred_eq, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hx.1.le
      _ ≤ (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal * eLpNorm θ 2 (μ.withDensity fun x ↦
            ENNReal.ofReal (intervalSobolevDensity 0 σ 0 (r x))) ^ (2 : ℝ≥0∞).toReal :=
          meas_ge_le_mul_pow_eLpNorm_eNorm _ two_ne_zero ENNReal.ofNat_ne_top hε
            fun h ↦ absurd h ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  by_contra htop
  have hBtop : (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
      intervalSobolevENorm μ r I 0 θ ^ (2 : ℝ≥0∞).toReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) (ENNReal.inv_ne_top.mpr hε))
      (ENNReal.rpow_ne_top_of_nonneg (by simp) htop)
  obtain ⟨K, hK, hKle⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ σ : ℝ, 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * r g)) ≤ K :=
    ⟨_, ENNReal.div_ne_top hBtop hUpos, fun σ hσ ↦
      (ENNReal.le_div_iff_mul_le (Or.inl hUpos) (Or.inr hBtop)).mpr (hbound σ hσ)⟩
  have hlt : K.toReal < Real.exp (max 0 (K.toReal / r g) * r g) := by
    have h := (div_le_iff₀ hrg).mp (le_max_right 0 (K.toReal / r g))
    linarith [Real.add_one_le_exp (max 0 (K.toReal / r g) * r g)]
  exact absurd (hKle _ (le_max_left _ _))
    (not_le.mpr ((ENNReal.lt_ofReal_iff_toReal_lt hK).mpr hlt))

open scoped Classical in
/-- A nonnegative archimedean bump at one, times the indicator of the finite
integers, vanishes at zero and has nonzero theta at one. -/
private theorem globalTheta_zero_eval_theta_one (F : Type) [Field F] [NumberField F] :
    ∃ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)),
      f (Multiplicative.ofAdd 0) = 0 ∧ adelicTheta f (1 : IdeleClassGroup (𝓞 F) F) ≠ 0 := by
  let D := dist (0 : mixedEmbedding.mixedSpace F) 1
  have hD : 0 < D := dist_pos.mpr zero_ne_one
  let b : ContDiffBump (1 : mixedEmbedding.mixedSpace F) :=
    ⟨D / 4, D / 2, by positivity, by linarith⟩
  let bs : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ :=
    HasCompactSupport.toSchwartzMap (f := fun x ↦ ((b x : ℝ) : ℂ))
      (b.hasCompactSupport.comp_left Complex.ofReal_zero)
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨fun x ↦ bs (InfiniteAdeleRing.ringEquiv_mixedSpace F x.toAdd),
      (mem_archimedeanSchwartzBruhat_iff _).mpr ⟨bs, fun _ ↦ rfl⟩⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F (∅ : Finset (HeightOneSpectrum (𝓞 F)))
  let gg : ∀ w : (∅ : Finset (HeightOneSpectrum (𝓞 F))),
      SchwartzBruhat (Multiplicative (w.val.adicCompletion F)) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  let f := sAdeleSchwartzToGlobal F ∅ (e (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, gg w)))
  have hf : ∀ x : AdeleRing (𝓞 F) F, f (Multiplicative.ofAdd x) =
      if ∀ v : HeightOneSpectrum (𝓞 F), x.2 v ∈ v.adicCompletionIntegers F then
        ((b (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) : ℝ) : ℂ) else 0 := by
    intro x
    rw [sAdeleSchwartzToGlobal_apply, he]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, Finset.notMem_empty,
      not_false_eq_true, forall_const]
    split_ifs <;> rfl
  have hzero : f (Multiplicative.ofAdd 0) = 0 := by
    rw [hf]
    split_ifs
    · rw [Prod.fst_zero, map_zero, b.zero_of_le_dist (show D / 2 ≤ D by linarith),
        Complex.ofReal_zero]
    · rfl
  let T : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd
    (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (1 : IdeleGroup (𝓞 F) F).val))
  have hT : ∀ ξ, T ξ = ((‖T ξ‖ : ℝ) : ℂ) := by
    intro ξ
    change f _ = ((‖f _‖ : ℝ) : ℂ)
    rw [hf]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg b.nonneg]
    · simp
  have hT1 : ‖T 1‖ = 1 := by
    change ‖f _‖ = 1
    rw [Units.val_one, map_one, Units.val_one, mul_one, hf, ite_eq_left (fun v ↦ by
      change (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact one_mem _), Prod.fst_one, map_one, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le),
      Complex.ofReal_one, norm_one]
  have hs : Summable fun ξ ↦ ‖T ξ‖ := by
    have := (adelicAverage_summableUniformlyOn f _
      (isCompact_singleton (x := ((1 : IdeleGroup (𝓞 F) F), (0 : AdeleRing (𝓞 F) F))))).summable
      (Set.mem_singleton _)
    simpa only [T, add_zero, mul_comm] using this
  refine ⟨f, hzero, ?_⟩
  change adelicTheta f (QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F) 1) ≠ 0
  rw [adelicTheta_mk]
  change ∑' ξ, T ξ ≠ 0
  rw [tsum_congr hT, ← Complex.ofReal_tsum]
  have hpos : 0 < ∑' ξ, ‖T ξ‖ :=
    lt_of_lt_of_le (by rw [hT1]; exact one_pos) (hs.le_tsum 1 (fun _ _ ↦ norm_nonneg _))
  exact_mod_cast hpos.ne'

/-- Additive Haar scaling for a unit translate, as in the norm-twist
counterexample in `Ch06_LocalGlobal/Sec3_Printed.lean`. -/
private theorem globalThetaSobolev_translate_integral
    (u : IdeleGroup (𝓞 ℚ) ℚ) (k : 𝔸[ℚ] → ℂ) :
    ∫ x, k ((↑u⁻¹ : 𝔸[ℚ]) * x) ∂additiveTamagawaMeasure ℚ =
      (((ideleNorm ℚ u).val : ℝ) : ℂ) * ∫ x, k x ∂additiveTamagawaMeasure ℚ := by
  let : MeasurableSpace 𝔸[ℚ] := borel _
  let : BorelSpace 𝔸[ℚ] := ⟨rfl⟩
  let : (additiveTamagawaMeasure ℚ).IsAddHaarMeasure :=
    (additiveTamagawaMeasure_existsUnique ℚ).exists.choose_spec.1
  let d : 𝔸[ℚ] ≃ₜ 𝔸[ℚ] := Homeomorph.smul (u⁻¹ : IdeleGroup (𝓞 ℚ) ℚ)
  have hset (s : Set 𝔸[ℚ]) :
      d ⁻¹' s = (fun a : 𝔸[ℚ] ↦ (u : 𝔸[ℚ]) * a) '' s := by
    ext y
    constructor
    · intro hy
      exact ⟨(↑u⁻¹ : 𝔸[ℚ]) * y, hy, Units.mul_inv_cancel_left u y⟩
    · rintro ⟨a, ha, rfl⟩
      change (↑u⁻¹ : 𝔸[ℚ]) * ((u : 𝔸[ℚ]) * a) ∈ s
      rwa [Units.inv_mul_cancel_left]
  have hmap : (additiveTamagawaMeasure ℚ).map d =
      ((ideleNorm ℚ u).val : ENNReal) • additiveTamagawaMeasure ℚ := by
    refine Measure.ext fun s hs ↦ ?_
    rw [Measure.map_apply d.continuous.measurable hs, hset s]
    exact adeleHaar_mul_image ℚ (additiveTamagawaMeasure ℚ) u s hs
  have hi := (integral_map_equiv (μ := additiveTamagawaMeasure ℚ) d.toMeasurableEquiv k).symm
  have hmap' : (additiveTamagawaMeasure ℚ).map d.toMeasurableEquiv =
      ((ideleNorm ℚ u).val : ENNReal) • additiveTamagawaMeasure ℚ := hmap
  rw [hmap', integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul] at hi
  exact hi

/-- A rapidly decaying sequence with nonzero first value cannot have every
term twice its successor. -/
private theorem globalThetaSobolev_exists_difference_ne_zero (A : ℕ → ℂ)
    (hA : A 0 ≠ 0) (C : ℝ) (hbound : ∀ n, ‖A n‖ ≤ C * (((2 : ℝ) ^ n) ^ 2)⁻¹) :
    ∃ n, A n - 2 * A (n + 1) ≠ 0 := by
  by_contra! h
  have hc (n : ℕ) : (2 : ℂ) ^ n * A n = A 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_assoc, ← sub_eq_zero.mp (h n)]
      exact ih
  have hb (n : ℕ) : ‖(2 : ℂ) ^ n * A n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    refine (mul_le_mul_of_nonneg_left (hbound n) (by positivity)).trans_eq ?_
    rw [one_div, inv_pow]
    field_simp
  have hlim : Tendsto (fun n : ℕ ↦ (2 : ℂ) ^ n * A n) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hb (by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (x := (1 / 2 : ℝ)) (by norm_num)).const_mul C)
  exact hA (tendsto_nhds_unique (by simpa only [hc] using hlim) tendsto_const_nhds).symm

/-- A polar-free test with nonzero theta at positive log norm. Start with a bump that
vanishes at zero and use one dilation difference to cancel its Fourier value there. -/
private theorem globalThetaSobolev_positive_logNorm_witness :
    ∃ (f : adelePolarSubspace ℚ) (g : IdeleClassGroup (𝓞 ℚ) ℚ),
      1 < ((ideleClassNorm ℚ g).val : ℝ) ∧ adelicTheta f.val g ≠ 0 := by
  obtain ⟨E, hE₀, hEθ⟩ := globalTheta_zero_eval_theta_one ℚ
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let u := canonicalIdeleNormSection ℚ t
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)
  let T := schwartzBruhatUnitTranslate u
  let d := T E - (2 : ℂ) • E
  have hu : ideleNorm ℚ u = t := canonicalIdeleNormSection_rightInverse ℚ t
  have hu₂ : (((ideleNorm ℚ u).val : ℝ) : ℂ) = 2 := by rw [hu]; rfl
  have hd : d ∈ adelePolarSubspace ℚ := by
    change adelePolarValues d = 0
    have hT : adelePolarValues (T E) = (0, 2 * (adelePolarValues E).2) := by
      apply Prod.ext
      · change E (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[ℚ]) * 0)) = 0
        simpa only [mul_zero] using hE₀
      · change adeleSchwartzFourier _ _ = _ * adeleSchwartzFourier E _
        rw [(adeleSchwartzFourier_apply_zero _).2, (adeleSchwartzFourier_apply_zero E).2, ← hu₂]
        exact globalThetaSobolev_translate_integral u _
    rw [show d = T E - (2 : ℂ) • E from rfl, map_sub, map_smul, hT]
    refine Prod.ext ?_ (by simp [smul_eq_mul])
    have hEval : (adelePolarValues E).1 = 0 := hE₀
    change (0 : ℂ) - (2 : ℂ) • (adelePolarValues E).1 = 0
    rw [hEval, smul_zero, sub_zero]
  let A (n : ℕ) := adelicTheta E (q (u ^ n))
  have hnorm (n : ℕ) : ((ideleNorm ℚ (u ^ n)).val : ℝ) = 2 ^ n := by
    rw [map_pow, hu, Units.val_pow_eq_pow_val, NNReal.coe_pow]
    rfl
  obtain ⟨C, _, hdecay⟩ := adelicTheta_normSum_decay_large E 2
  have hA (n : ℕ) : ‖A n‖ ≤ C * (((2 : ℝ) ^ n) ^ 2)⁻¹ := by
    have hb := hdecay (u ^ n) (by rw [hnorm]; exact one_le_pow₀ (by norm_num))
    rw [hnorm] at hb
    have hs : Summable fun ξ : ℚˣ ↦ ‖E (Multiplicative.ofAdd
        (algebraMap ℚ 𝔸[ℚ] (ξ : ℚ) * (u ^ n).val))‖ := by
      simpa only [add_zero, mul_comm] using
        ((adelicAverage_summableUniformlyOn E {((u ^ n), (0 : 𝔸[ℚ]))}
          isCompact_singleton).summable rfl)
    change ‖adelicTheta E (QuotientGroup.mk (u ^ n))‖ ≤ _
    rw [adelicTheta_mk]
    exact (norm_tsum_le_tsum_norm hs).trans (by simpa only [mul_comm] using hb)
  have hA₀ : A 0 ≠ 0 := by simpa only [A, pow_zero, map_one] using hEθ
  obtain ⟨n, hn⟩ := globalThetaSobolev_exists_difference_ne_zero A hA₀ C hA
  have hgt : 1 < ((ideleClassNorm ℚ (q (u ^ (n + 1)))).val : ℝ) := by
    change 1 < ((ideleNorm ℚ (u ^ (n + 1))).val : ℝ)
    rw [hnorm]
    exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero _)
  have hθ : adelicTheta (T E) (q (u ^ (n + 1))) = A n := by
    change adelicTheta (T E) (QuotientGroup.mk (u ^ (n + 1))) =
      adelicTheta E (QuotientGroup.mk (u ^ n))
    rw [adelicTheta_mk, adelicTheta_mk]
    apply tsum_congr
    intro ξ
    have hu' : u⁻¹ * u ^ (n + 1) = u ^ n := by
      rw [pow_succ', ← mul_assoc, inv_mul_cancel, one_mul]
    change E (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[ℚ]) *
      (algebraMap ℚ 𝔸[ℚ] (ξ : ℚ) * (u ^ (n + 1)).val))) = _
    rw [mul_left_comm (↑u⁻¹ : 𝔸[ℚ]), ← Units.val_mul, hu']
  refine ⟨⟨d, hd⟩, q (u ^ (n + 1)), hgt, ?_⟩
  change (adelicThetaLinearMap ℚ (T E - (2 : ℂ) • E)) (q (u ^ (n + 1))) ≠ 0
  rw [map_sub, map_smul]
  change adelicTheta (T E) (q (u ^ (n + 1))) - 2 * A (n + 1) ≠ 0
  rwa [hθ]

/-- Paper: Before (10.1.1.2), p. 434. At zero weight and order, take the
closed half-line [0,∞). A norm-two dilation difference of a bump near the
archimedean identity is polar-free and has nonzero theta at some positive
log norm. The endpoint weights on [0,b] force the Sobolev norm to be infinite. -/
theorem Printed.globalThetaSobolev_closedIntervals_finite_false :
    ¬ Printed.globalThetaSobolev_closedIntervals_finite := by
  intro h
  let C := IdeleClassGroup (𝓞 ℚ) ℚ
  let m : C →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let r : C → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  obtain ⟨f, g, hg, hθg⟩ := globalThetaSobolev_positive_logNorm_witness
  have hr : Continuous r :=
    Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous))
      (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  let : BorelSpace C := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  have htop := intervalSobolevENorm_eq_top_of_positive_logNorm (ideleClassTamagawaMeasure ℚ)
    (Ici 0) Subset.rfl r hr (adelicTheta f.val) (adelicTheta f.val).continuous g
    (Real.log_pos hg) hθg
  have hi : (interior (Ici (0 : ℝ))).Nonempty := by
    rw [interior_Ici]
    exact nonempty_Ioi
  have hf := h ℚ 0 0 le_rfl (Ici 0) isClosed_Ici ordConnected_Ici hi f
  exact hf (by simpa only [m, r, modulationWeight_zero] using htop)

/-- Paper: Before Lemma 10.1.1.4, p. 435. A positive twist of every local theta
test is asserted to belong to the Sobolev space for the whole half-line (-a,∞). -/
def Printed.sLocalThetaSobolev_openHalfLine_finite : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ), 0 < a → 0 ≤ s → ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      let m := (⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ :
        SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
      intervalSobolevENorm (sLocalQuotientTamagawaMeasure F S)
        (fun g ↦ Real.log ((m g).val : ℝ)) (Ioi (-a)) s
        (modulationWeight m a (sLocalAdelicThetaOnClasses F S f)) ≠ ⊤

/-- Paper: Before Lemma 10.1.1.4, p. 435.
The Gaussian theta dominates its term at the identity S-unit. -/
private theorem sLocalThetaSobolev_openHalfLine_finite_false_theta_lower
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) ≤
      ‖sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x)‖ := by
  have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f {x} isCompact_singleton).hasSum
    rfl).summable
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  simp only [hf] at hs ⊢
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have hr := Complex.summable_ofReal.mp hs
  refine le_trans (le_of_eq ?_) (hr.le_tsum 1 fun _ _ ↦ (Real.exp_pos _).le)
  simp

/-- Paper: Before Lemma 10.1.1.4, p. 435.
The rational Gaussian has nonzero theta at a class of norm two. -/
private theorem sLocalThetaSobolev_openHalfLine_finite_false_witness :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      ∃ g : SIdeleQuotient ℚ ∅,
        1 < ((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) ∧
        sLocalAdelicThetaOnClasses ℚ ∅ f g ≠ 0 := by
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hf : ∀ x : SAdeleRing ℚ ∅, E φ (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [hE]
    have hn (z : Rat.infinitePlace.Completion) : ‖InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace z‖ = ‖z‖ := by
      rw [← dist_zero_right, ← dist_zero_right z,
        ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).dist_eq z 0
    have hφ (y : ℝ) : φ y = ((Real.exp (-‖y‖ ^ 2) : ℝ) : ℂ) := by
      change Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos y) = _
      rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, neg_mul, one_mul]
    rw [hφ, hn]
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  let u : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  let g : SIdeleQuotient ℚ ∅ := σ u
  have hg : 1 < ((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) := by
    rw [show sIdeleQuotientNorm ℚ ∅ g = u from hσ u]
    norm_num [u]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective g
  have hpos := sLocalThetaSobolev_openHalfLine_finite_false_theta_lower (E φ) hf x
  refine ⟨E φ, g, hg, ?_⟩
  rw [← hx]
  exact norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) hpos)

/-- Paper: Before Lemma 10.1.1.4, p. 435. For ℚ, S = {∞}, a = 1, s = 0,
and the real Gaussian, the weighted theta is positive throughout [2,3].
Already the intervals [0,b] give unbounded norms as b tends to infinity. -/
theorem Printed.sLocalThetaSobolev_openHalfLine_finite_false :
    ¬ Printed.sLocalThetaSobolev_openHalfLine_finite := by
  intro h
  obtain ⟨f, g, hg, hθg⟩ := sLocalThetaSobolev_openHalfLine_finite_false_witness
  let m : SIdeleQuotient ℚ ∅ →ₜ* ℝ≥0ˣ :=
    ⟨sIdeleQuotientNorm ℚ ∅, (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous⟩
  let r : SIdeleQuotient ℚ ∅ → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  let θ := modulationWeight m 1 (sLocalAdelicThetaOnClasses ℚ ∅ f)
  have hr : Continuous r := by
    exact Real.continuousOn_log.comp_continuous
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous))
      (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')
  have hθ : Continuous θ := by
    dsimp [θ, modulationWeight]
    fun_prop
  have hrg : 0 < r g := Real.log_pos hg
  have hθg' : θ g ≠ 0 := by
    dsimp [θ, modulationWeight]
    exact mul_ne_zero (by exact_mod_cast (pow_ne_zero 1 (Units.ne_zero (m g)))) hθg
  have hHaar : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure :=
    (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1
  have hOpen : (sLocalQuotientTamagawaMeasure ℚ ∅).IsOpenPosMeasure :=
    hHaar.toIsOpenPosMeasure
  let : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have htop := @intervalSobolevENorm_eq_top_of_positive_logNorm
    (SIdeleQuotient ℚ ∅) inferInstance inferInstance inferInstance
    (sLocalQuotientTamagawaMeasure ℚ ∅) hOpen (Ioi (-1))
    (fun _ hx ↦ lt_of_lt_of_le (by norm_num) hx) r hr θ hθ g hrg hθg'
  have hfin := h ℚ ∅ 1 0 one_pos le_rfl f
  exact hfin htop


/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434. As printed,
the integral defining the local norm is finite at every positive weight and
every compact nonempty interval. -/
def Printed.sLocalThetaSobolev_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      Integrable (fun g : SIdeleQuotient F S ↦ ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((sIdeleQuotientNorm F S g).val : ℝ))) (sLocalQuotientTamagawaMeasure F S)

private theorem sLocalThetaSobolev_integrable_false_measure {G : Type*} [Group G]
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
    simp only [A, mem_setOf_eq, hg₀, Units.val_mk0, NNReal.coe_div, NNReal.coe_ofNat]
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
    simp only [mem_setOf_eq]
    nlinarith
  refine eq_top_mono (measure_mono hsub) ?_
  rw [measure_iUnion hdisj (fun k ↦ (measurable_const_mul (t ^ k)) hAo.measurableSet)]
  simp only [hmeas]
  exact ENNReal.tsum_const_eq_top_of_ne_zero hA0


private theorem sLocalThetaSobolev_integrable_false_norm (x : (SAdeleRing ℚ ∅)ˣ) :
    ((sIdeleNorm ℚ ∅ x : ℝ≥0) : ℝ) = ‖x.val.1 Rat.infinitePlace‖ := by
  simp [sIdeleNorm]
  rw [Unique.eq_default Rat.infinitePlace]

private theorem sLocalThetaSobolev_integrable_false_theta
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ x : SAdeleRing ℚ ∅, f (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ))
    (x : (SAdeleRing ℚ ∅)ˣ) :
    Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) ≤
      ‖sLocalAdelicThetaOnClasses ℚ ∅ f (QuotientGroup.mk x)‖ := by
  have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f {x} isCompact_singleton).hasSum
    rfl).summable
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  simp only [hf] at hs ⊢
  rw [← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs]
  refine le_trans ?_ (le_abs_self _)
  have hr := Complex.summable_ofReal.mp hs
  refine le_trans (le_of_eq ?_) (hr.le_tsum 1 fun _ _ ↦ (Real.exp_pos _).le)
  simp

/-- Paper: Definition 10.1.1.1(2) and Remark 10.1.1.2, p. 434.
For ℚ with S consisting of the real place, take f(x) = exp(-πx²), a = 1,
I = {-1} and s = 0. The two S-units give theta(t) = 2 exp(-πt²), whose
square is not integrable near zero against dt/t. -/
theorem Printed.sLocalThetaSobolev_integrable_false :
    ¬ Printed.sLocalThetaSobolev_integrable := by
  intro h
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  let φ : SchwartzMap ℝ ℂ := (SchwartzMap.gaussian 1 one_pos).postcompCLM Complex.ofRealCLM
  have hf : ∀ x : SAdeleRing ℚ ∅, E φ (Multiplicative.ofAdd x) =
      ((Real.exp (-‖x.1 Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
    intro x
    rw [hE]
    have hn (z : Rat.infinitePlace.Completion) : ‖InfinitePlace.Completion.ringEquivRealOfIsReal
        Rat.isReal_infinitePlace z‖ = ‖z‖ := by
      rw [← dist_zero_right, ← dist_zero_right z,
        ← map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)]
      exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
        Rat.isReal_infinitePlace).dist_eq z 0
    have hφ (y : ℝ) : φ y = ((Real.exp (-‖y‖ ^ 2) : ℝ) : ℂ) := by
      change Complex.ofRealCLM (SchwartzMap.gaussian 1 one_pos y) = _
      rw [SchwartzMap.gaussian_apply, Complex.ofRealCLM_apply, neg_mul, one_mul]
    rw [hφ, hn]
  have hint := h ℚ ∅ 1 (-1) (-1) 0 one_pos le_rfl le_rfl (E φ)
  let θ := sLocalAdelicThetaOnClasses ℚ ∅ (E φ)
  have hint' : Integrable (fun g ↦ ‖θ g‖ ^ 2) (sLocalQuotientTamagawaMeasure ℚ ∅) :=
    hint.congr (Eventually.of_forall fun g ↦ by simp only [θ]; norm_num [intervalSobolevDensity])
  have : BorelSpace (SIdeleQuotient ℚ ∅) := ⟨rfl⟩
  have hW := sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)
  have : (sLocalQuotientTamagawaMeasure ℚ ∅).IsHaarMeasure := hW.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  have hNc : Continuous (sIdeleQuotientNorm ℚ ∅) := (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
  have hB := sLocalThetaSobolev_integrable_false_measure (sLocalQuotientTamagawaMeasure ℚ ∅)
    (sIdeleQuotientNorm ℚ ∅) hNc hσ.surjective
  let B := {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1}
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  have hlow : ∀ g ∈ B, ENNReal.ofReal (Real.exp (-1) ^ 2) ≤ ‖‖θ g‖ ^ 2‖ₑ := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have hx : ‖x.val.1 Rat.infinitePlace‖ < 1 := by
      rw [← sLocalThetaSobolev_integrable_false_norm]
      exact hg
    have h1 := sLocalThetaSobolev_integrable_false_theta (E φ) hf x
    have h2 : Real.exp (-1) ≤ Real.exp (-‖x.val.1 Rat.infinitePlace‖ ^ 2) := by
      gcongr
      nlinarith [norm_nonneg (x.val.1 Rat.infinitePlace)]
    rw [Real.eNorm_eq_ofReal (by positivity)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (Real.exp_pos _).le (h2.trans h1) 2)
  have hfin : (∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅) < ⊤ :=
    hint'.hasFiniteIntegral
  have hBdef : B = {g : SIdeleQuotient ℚ ∅ | ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ) < 1} := rfl
  have hge : ⊤ ≤ ∫⁻ g, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
    calc (⊤ : ℝ≥0∞) = ENNReal.ofReal (Real.exp (-1) ^ 2) * sLocalQuotientTamagawaMeasure ℚ ∅ B := by
          rw [hBdef, hB, ENNReal.mul_top (by positivity)]
      _ = ∫⁻ _ in B, ENNReal.ofReal (Real.exp (-1) ^ 2) ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖θ g‖ ^ 2‖ₑ ∂sLocalQuotientTamagawaMeasure ℚ ∅ :=
          setLIntegral_mono' hBm hlow
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. As printed, the density of
the weighted S-idele measure vanishes at infinity. -/
def Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (α β s : ℝ), α ≤ β → 0 ≤ s →
    Tendsto (fun g : (SAdeleRing F S)ˣ ↦
      intervalSobolevDensity α β s (Real.log ((sIdeleNorm F S g).val : ℝ)))
      (cocompact _) (nhds 0)

private theorem sIdeleNorm_vanishesAtInfinity_false_cont (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (sIdeleNorm F S) := by
  suffices H : Continuous (fun g ↦ sIdeleNorm F S g) from H
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply]
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ ↦ ?_
    refine Continuous.pow ?_ _
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply w).comp continuous_fst).units_map _))
  · refine continuous_finsetProd _ fun v _ ↦ ?_
    exact (continuous_nnNorm.units_map _).comp
      ((((continuous_apply v).comp continuous_snd).units_map _))

private theorem sIdeleNorm_vanishesAtInfinity_false_diag :
    ((sIdeleNorm ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero))).val : ℝ) = 2 := by
  simp only [sIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [Units.coe_prod, NNReal.coe_prod]
  have h2 := InfinitePlace.prod_eq_abs_norm (K := ℚ) 2
  rw [show (|(Algebra.norm ℚ) (2:ℚ)| : ℚ) = 2 by simp [Algebra.norm_self]] at h2
  rw [← (by norm_num : (((2:ℚ)) : ℝ) = 2), ← h2]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Units.val_pow_eq_pow_val, NNReal.coe_pow]
  congr 1
  change ‖(algebraMap ℚ (InfiniteAdeleRing ℚ) 2) w‖ = _
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (2 : WithAbs w.1)

private theorem sIdeleNorm_vanishesAtInfinity_false_noncompact :
    ¬ CompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ := by
  intro hc
  let u := Units.map ((algebraMap ℚ (InfiniteAdeleRing ℚ)).prod
        (RingHom.pi fun v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) ↦
          algebraMap ℚ (v.val.adicCompletion ℚ))).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero)
  have hu := sIdeleNorm_vanishesAtInfinity_false_diag
  have hcont : Continuous fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      ((sIdeleNorm ℚ ∅ g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (sIdeleNorm_vanishesAtInfinity_false_cont ℚ ∅))
  obtain ⟨C, hC⟩ := (isCompact_range hcont).isBounded.subset_closedBall 0
  have hn : ∀ n : ℕ, ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) = 2 ^ n := fun n ↦ by
    rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, hu]
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt C (by norm_num : (1 : ℝ) < 2)
  have : ((sIdeleNorm ℚ ∅ (u ^ n)).val : ℝ) ∈ Metric.closedBall 0 C := hC ⟨u ^ n, rfl⟩
  rw [hn n] at this
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 ^ n)] at this
  linarith


/-- Paper: Proof of Lemma 10.1.1.4(1), p. 436. For ℚ with S the real place,
I = {1} and s = 0, the density is t² on the positive ideles t, so it
grows without bound as t tends to infinity. -/
theorem Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity_false :
    ¬ Printed.sIdeleIntervalSobolevDensity_vanishesAtInfinity := by
  intro h
  have h1 := h ℚ ∅ 0 0 0 le_rfl le_rfl
  have hconst : (fun g : (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ ↦
      intervalSobolevDensity 0 0 0 (Real.log ((sIdeleNorm ℚ ∅ g).val : ℝ))) = fun _ ↦ 1 := by
    funext g
    simp [intervalSobolevDensity]
  rw [hconst] at h1
  have : NoncompactSpace (SAdeleRing ℚ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))))ˣ :=
    not_compactSpace_iff.mp sIdeleNorm_vanishesAtInfinity_false_noncompact
  exact one_ne_zero (tendsto_nhds_unique h1 tendsto_const_nhds).symm

/-- Paper: Proposition 10.1.1.5, pp. 436–437. As printed, the global Sobolev
completion in the proposition uses theta functions of all Schwartz–Bruhat tests.
The proposed completion requires their weighted square integrability. -/
def Printed.globalThetaSobolev_allTests_integrable : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    ∀ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)),
      Integrable (fun g : IdeleClassGroup (𝓞 F) F ↦ ‖adelicTheta f g‖ ^ 2 *
        intervalSobolevDensity (a + α) (a + β) s
          (Real.log ((ideleClassNorm F g).val : ℝ))) (ideleClassTamagawaMeasure F)

/-- Paper: Proposition 10.1.1.5, pp. 436–437. A test with vanishing value
at zero and Fourier value one has theta bounded below near norm zero. -/
private theorem globalThetaSobolev_allTests_integrable_false_lower_bound :
    ∃ f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 ℚ) ℚ)), ∃ ε : ℝ,
      0 < ε ∧ ∀ g : IdeleClassGroup (𝓞 ℚ) ℚ,
        ((ideleClassNorm ℚ g).val : ℝ) < ε → 1 ≤ ‖adelicTheta f g‖ := by
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := ℚ) (0, 1)
  let z : Multiplicative (AdeleRing (𝓞 ℚ) ℚ) := Multiplicative.ofAdd 0
  let t (g : IdeleClassGroup (𝓞 ℚ) ℚ) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  have hf₀ : f z = 0 := congrArg Prod.fst hf
  have hF₀ : adeleSchwartzFourier f z = 1 := congrArg Prod.snd hf
  obtain ⟨C, T, hC, hT, hsmall⟩ := adelicTheta_decay_small f 0
  refine ⟨f, min T (1 / (C + 1)), lt_min hT (by positivity), ?_⟩
  intro g hg
  have ht : 0 < t g := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hgt : t g < T := lt_of_lt_of_le hg (min_le_left _ _)
  have hgc : t g < 1 / (C + 1) := lt_of_lt_of_le hg (min_le_right _ _)
  have hbound : ‖adelicTheta f g - (t g)⁻¹ • (1 : ℂ)‖ ≤ C := by
    simpa only [t, z, hf₀, hF₀, add_zero, pow_zero, mul_one] using hsmall g hgt
  have hnorm : ‖(t g)⁻¹ • (1 : ℂ)‖ = (t g)⁻¹ := by
    simp only [norm_smul, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
  have htri : ‖(t g)⁻¹ • (1 : ℂ)‖ ≤
      ‖adelicTheta f g‖ + ‖adelicTheta f g - (t g)⁻¹ • (1 : ℂ)‖ := by
    exact norm_le_norm_add_norm_sub _ _
  have hC1 : 0 < C + 1 := by linarith
  have hinv : C + 1 < (t g)⁻¹ := by
    exact (lt_inv_comm₀ ht hC1).mp (by simpa only [one_div] using hgc)
  rw [hnorm] at htri
  linarith

/-- Paper: Proposition 10.1.1.5, pp. 436–437. Every positive radius has
an infinite-measure small-norm region in the idele class group of ℚ. -/
private theorem globalThetaSobolev_allTests_integrable_false_small_norm_measure
    (ε : ℝ) (hε : 0 < ε) :
    ideleClassTamagawaMeasure ℚ
      {g : IdeleClassGroup (𝓞 ℚ) ℚ | ((ideleClassNorm ℚ g).val : ℝ) < ε} = ⊤ := by
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure :=
    (ideleClassTamagawaMeasure_isWeil ℚ).1
  have hNc : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hs : Function.Surjective (ideleClassNorm ℚ) := by
    intro t
    refine ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ t), ?_⟩
    exact canonicalIdeleNormSection_rightInverse ℚ t
  have hB := sLocalThetaSobolev_integrable_false_measure
    (ideleClassTamagawaMeasure ℚ) (ideleClassNorm ℚ) hNc hs
  have hε0 : (⟨ε, hε.le⟩ : ℝ≥0) ≠ 0 := by
    intro h
    exact hε.ne' (by simpa using congrArg Subtype.val h)
  let t : ℝ≥0ˣ := Units.mk0 ⟨ε, hε.le⟩ hε0
  let u : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hu : ideleClassNorm ℚ u = t := canonicalIdeleNormSection_rightInverse ℚ t
  have hset : {g : IdeleClassGroup (𝓞 ℚ) ℚ |
      ((ideleClassNorm ℚ g).val : ℝ) < ε} =
      (fun g ↦ u⁻¹ * g) ⁻¹' {g | ((ideleClassNorm ℚ g).val : ℝ) < 1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul, map_inv, hu,
      Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv]
    change ((ideleClassNorm ℚ g).val : ℝ) < ε ↔
      ε⁻¹ * ((ideleClassNorm ℚ g).val : ℝ) < 1
    simpa only [mul_one] using
      ((inv_mul_lt_iff₀ hε).symm :
        ((ideleClassNorm ℚ g).val : ℝ) < ε * 1 ↔
          ε⁻¹ * ((ideleClassNorm ℚ g).val : ℝ) < 1)
  rw [hset, measure_preimage_mul (ideleClassTamagawaMeasure ℚ) u⁻¹, hB]

/-- Paper: Proposition 10.1.1.5, pp. 436–437. For ℚ, set a = s = 0
and I = {0}. The real Gaussian times the characteristic functions of the finite
integer rings has theta(t) = Σ_{n ≠ 0} exp(-πn²t²), asymptotic to 1/t at zero
on each norm-one fibre, so its square is not integrable. -/
theorem Printed.globalThetaSobolev_allTests_integrable_false :
    ¬ Printed.globalThetaSobolev_allTests_integrable := by
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  intro h
  obtain ⟨f, ε, hε, hθ⟩ := globalThetaSobolev_allTests_integrable_false_lower_bound
  have hint := h ℚ 0 0 0 0 le_rfl le_rfl f
  have hint' : Integrable (fun g : IdeleClassGroup (𝓞 ℚ) ℚ ↦ ‖adelicTheta f g‖ ^ 2)
      (ideleClassTamagawaMeasure ℚ) :=
    hint.congr (Eventually.of_forall fun g ↦ by norm_num [intervalSobolevDensity])
  let B := {g : IdeleClassGroup (𝓞 ℚ) ℚ | ((ideleClassNorm ℚ g).val : ℝ) < ε}
  have hNc : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hBm : MeasurableSet B :=
    (isOpen_lt (NNReal.continuous_coe.comp (Units.continuous_val.comp hNc))
      continuous_const).measurableSet
  have hlow : ∀ g ∈ B, (1 : ℝ≥0∞) ≤ ‖‖adelicTheta f g‖ ^ 2‖ₑ := by
    intro g hg
    have hsq : (1 : ℝ) ≤ ‖adelicTheta f g‖ ^ 2 := by
      nlinarith [hθ g hg]
    rw [Real.eNorm_eq_ofReal (sq_nonneg _)]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq
  have hfin : (∫⁻ g, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ) < ⊤ :=
    hint'.hasFiniteIntegral
  have hB : ideleClassTamagawaMeasure ℚ B = ⊤ :=
    globalThetaSobolev_allTests_integrable_false_small_norm_measure ε hε
  have hge : ⊤ ≤ ∫⁻ g, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ :=
    calc (⊤ : ℝ≥0∞) = (1 : ℝ≥0∞) * ideleClassTamagawaMeasure ℚ B := by rw [hB]; simp
      _ = ∫⁻ _ in B, (1 : ℝ≥0∞) ∂ideleClassTamagawaMeasure ℚ :=
          (setLIntegral_const B _).symm
      _ ≤ ∫⁻ g in B, ‖‖adelicTheta f g‖ ^ 2‖ₑ ∂ideleClassTamagawaMeasure ℚ :=
          setLIntegral_mono' hBm hlow
      _ ≤ _ := setLIntegral_le_lintegral B _
  exact absurd (lt_of_le_of_lt hge hfin) (lt_irrefl _)

/-- A test quotient completes in its weighted function norm when its evaluation on
representatives gives an injective dense map to a closed subspace of the ambient L². -/
def Printed.IsFunctionCompletionMap {G B X W : Type*} [MeasurableSpace G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (H : Submodule ℂ W)
    (q : B → X) (θ : B → G → ℂ) (j : X →L[ℂ] H) : Prop :=
  IsClosed (H : Set W) ∧ Function.Injective j ∧ DenseRange j ∧
    ∀ f, rep (j (q f)).val =ᵐ[μ] θ f

/-- The product of the test quotient maps extends to a continuous injection of
the function-norm completions and factors through a surjective Hilbert-sum isometry.
The completions are quantified so the statement also makes sense when a proposed
test function fails to belong to the ambient L². -/
def Printed.HasHomogeneousSobolevFactorization {G B X W Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (μ : Measure G) (rep : W → G → ℂ) (q : B → X) (qω : ∀ i, B → Y i)
    (θ : B → G → ℂ) (θω : Ω → B → G → ℂ) : Prop :=
  ∃ (H : Submodule ℂ W) (K : Ω → Submodule ℂ W)
    (j : X →L[ℂ] H) (k : ∀ i, Y i →L[ℂ] K i)
    (Q : H →L[ℂ] (∀ i, K i)) (T : H ≃ₗᵢ[ℂ] lp (fun i ↦ ↥(K i)) 2),
    Printed.IsFunctionCompletionMap μ rep H q θ j ∧
    (∀ i, Printed.IsFunctionCompletionMap μ rep (K i) (qω i) (θω i) (k i)) ∧
    Function.Injective Q ∧ (∀ f i, Q (j (q f)) i = k i (qω i f)) ∧
    ∀ u i, Q u i = T u i

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.14). The product of the
global homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.globalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α β s : ℝ), α ≤ β → 0 ≤ s →
    let G := IdeleClassGroup (𝓞 F) F
    let m : G →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := GlobalAdelicThetaSpace F)
      (Y := GlobalHomogeneousThetaSpace F) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (adelicTheta f))
      (fun ω f ↦ modulationWeight m a (homogeneousAdelicTheta ω f))

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_orth {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (ω₁ ω₂ : PontryaginDual K) (h : ω₁ ≠ ω₂) :
    ∫ x, (ω₁ x : ℂ) * conj (ω₂ x : ℂ) ∂ν = 0 := by
  obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp h
  set I := ∫ x, (ω₁ x : ℂ) * conj (ω₂ x : ℂ) ∂ν
  have hinv : ∫ x, (ω₁ (c * x) : ℂ) * conj (ω₂ (c * x) : ℂ) ∂ν = I :=
    integral_mul_left_eq_self (fun x ↦ (ω₁ x : ℂ) * conj (ω₂ x : ℂ)) c
  have hsplit : ∫ x, (ω₁ (c * x) : ℂ) * conj (ω₂ (c * x) : ℂ) ∂ν =
      ((ω₁ c : ℂ) * conj (ω₂ c : ℂ)) * I := by
    rw [← integral_const_mul]
    congr 1; funext x
    simp only [map_mul, Circle.coe_mul, map_mul]; ring
  have hl : (ω₁ c : ℂ) * conj (ω₂ c : ℂ) ≠ 1 := by
    intro h1
    apply hc
    have h2 : (ω₂ c : ℂ) * conj (ω₂ c : ℂ) = 1 := by
      rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
    have : (ω₁ c : ℂ) = (ω₂ c : ℂ) := by
      have hne : conj (ω₂ c : ℂ) ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    exact Subtype.ext this
  have : ((ω₁ c : ℂ) * conj (ω₂ c : ℂ) - 1) * I = 0 := by
    rw [sub_mul, one_mul, ← hsplit, hinv, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hl)

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_bessel {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (φ : C(K, ℂ)) (s : Finset (PontryaginDual K)) :
    ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2 ≤
      (ν univ).toReal * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2 := by
  set V := (ν univ).toReal with hVdef
  have hV : 0 < V := ENNReal.toReal_pos (NeZero.ne _) (measure_ne_top _ _)
  let χ : PontryaginDual K → C(K, ℂ) := fun ω ↦
    ⟨fun x ↦ conj (ω x : ℂ), Complex.continuous_conj.comp (continuous_subtype_val.comp ω.continuous)⟩
  let c : ℝ := (Real.sqrt V)⁻¹
  let v : PontryaginDual K → Lp ℂ 2 ν := fun ω ↦ (c : ℂ) • ContinuousMap.toLp (E := ℂ) 2 ν ℂ (χ ω)
  have hc2 : c * c * V = 1 := by
    simp only [c]
    rw [← mul_inv, Real.mul_self_sqrt hV.le, inv_mul_cancel₀ hV.ne']
  have hv : Orthonormal ℂ v := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, inner_smul_left, inner_smul_right, ContinuousMap.inner_toLp, Complex.conj_ofReal]
    change (c : ℂ) * ((c : ℂ) * ∫ x, conj (j x : ℂ) * conj (conj (i x : ℂ)) ∂ν) = _
    simp only [Complex.conj_conj]
    split_ifs with hij
    · subst hij
      have h1 : ∀ x, conj (i x : ℂ) * (i x : ℂ) = 1 := fun x ↦ by
        rw [mul_comm, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]
      simp only [h1, integral_const]
      rw [← mul_assoc, ← Complex.ofReal_mul]
      simp only [Measure.real, Complex.real_smul, mul_one]
      exact_mod_cast hc2
    · have h0 := Printed.rawIsotype_orth ν i j hij
      have : ∫ x, conj (j x : ℂ) * (i x : ℂ) ∂ν = 0 := by
        rw [← h0]; congr 1; funext x; ring
      rw [this, mul_zero, mul_zero]
  have key := hv.sum_inner_products_le (x := ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ) (s := s)
  have hin : ∀ ω, ⟪v ω, ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ⟫_ℂ =
      (c : ℂ) * ∫ x, φ x * (ω x : ℂ) ∂ν := by
    intro ω
    simp only [v, inner_smul_left, ContinuousMap.inner_toLp, Complex.conj_ofReal]
    change (c : ℂ) * ∫ x, φ x * conj (conj (ω x : ℂ)) ∂ν = _
    simp only [Complex.conj_conj]
  simp only [hin, norm_mul, Complex.norm_real, mul_pow] at key
  rw [← Finset.mul_sum] at key
  have hcn : ‖c‖ ^ 2 * V = 1 := by
    rw [Real.norm_eq_abs, sq_abs, sq]; exact hc2
  calc ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2
      = V * (‖c‖ ^ 2 * ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2) := by
        rw [← mul_assoc, mul_comm V, hcn, one_mul]
    _ ≤ V * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2 := by gcongr

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_besselENN {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (φ : C(K, ℂ)) :
    ∑' ω : PontryaginDual K, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ₑ ^ 2 ≤ ν univ * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
  have hL : ENNReal.ofReal (‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2) =
      ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
    rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
      eLpNorm_congr_ae (φ.coeFn_toLp (p := 2) (𝕜 := ℂ) ν)]
    have := eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (f := ⇑φ) (p := 2) two_ne_zero
      φ.continuous.aestronglyMeasurable
    simpa using this
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hb := Printed.rawIsotype_bessel ν φ s
  calc ∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ₑ ^ 2
      = ENNReal.ofReal (∑ ω ∈ s, ‖∫ x, φ x * (ω x : ℂ) ∂ν‖ ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal ((ν univ).toReal * ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ φ‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal hb
    _ = ν univ * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _), hL]

open scoped ENNReal ComplexConjugate InnerProductSpace in
private theorem Printed.rawIsotype_integrated {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (K : Subgroup C) [CompactSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (μ : Measure C) [μ.IsMulLeftInvariant] [SFinite μ]
    (θ : C → ℂ) (hθ : Continuous θ) (Θ : PontryaginDual K → C → ℂ)
    (hΘc : ∀ ω, Continuous (Θ ω))
    (hΘ : ∀ ω g, Θ ω g = ∫ h, θ (h.val * g) * (ω h : ℂ) ∂ν) :
    ∑' ω, ∫⁻ g, ‖Θ ω g‖ₑ ^ 2 ∂μ ≤ ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := by
  have hpt : ∀ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ≤ ν univ * ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν := by
    intro g
    simp only [hΘ]
    exact Printed.rawIsotype_besselENN ν ⟨fun h : K ↦ θ (h.val * g),
      hθ.comp (continuous_subtype_val.mul continuous_const)⟩
  have hmain : ∫⁻ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ∂μ ≤ ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := calc
    ∫⁻ g, ∑' ω, ‖Θ ω g‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ g, ν univ * ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν univ * ∫⁻ g, ∫⁻ h, ‖θ (h.val * g)‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ (measure_ne_top _ _)
    _ = ν univ * ∫⁻ h, ∫⁻ g, ‖θ (h.val * g)‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap]
        exact ((hθ.comp ((continuous_subtype_val.comp continuous_snd).mul
          continuous_fst)).measurable.enorm.pow_const 2).aemeasurable
    _ = ν univ * ∫⁻ h, ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ ∂ν := by
        congr 1
        refine lintegral_congr fun h ↦ ?_
        exact lintegral_mul_left_eq_self (fun g ↦ ‖θ g‖ₑ ^ 2) h.val
    _ = ν univ ^ 2 * ∫⁻ g, ‖θ g‖ₑ ^ 2 ∂μ := by rw [lintegral_const, sq, mul_assoc, mul_comm (∫⁻ _, _ ∂μ)]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ le_trans ?_ hmain
  rw [← lintegral_finsetSum' s (fun ω _ ↦ ((hΘc ω).measurable.enorm.pow_const 2).aemeasurable)]
  exact lintegral_mono fun g ↦ ENNReal.sum_le_tsum s

/-- Squared L² seminorm of a continuous function as a lower integral. -/
private theorem Printed.rawIsotype_eLpNorm_sq {C : Type*} [TopologicalSpace C]
    [MeasurableSpace C] [OpensMeasurableSpace C] [SecondCountableTopology C]
    (μ : Measure C) (φ : C → ℂ) (hφ : Continuous φ) :
    eLpNorm φ 2 μ ^ 2 = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := φ) (p := 2) two_ne_zero
    hφ.aestronglyMeasurable
  simpa using this

/-- A Hilbert-sum factorization of quotient maps equates the squared norm of
each total function with the sum of the squared norms of its components. -/
private theorem Printed.rawIsotype_factorization_norm {G B X Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    {μ μ' : Measure G} {q : B → X} {qω : ∀ i, B → Y i}
    {θ : B → G → ℂ} {θω : Ω → B → G → ℂ}
    (h : Printed.HasHomogeneousSobolevFactorization (W := Lp ℂ 2 μ') μ (fun u ↦ ⇑u)
      q qω θ θω) (hμ : μ' = μ) (f : B) :
    eLpNorm (θ f) 2 μ < ⊤ ∧ ∑' i, eLpNorm (θω i f) 2 μ ^ 2 = eLpNorm (θ f) 2 μ ^ 2 := by
  subst hμ
  obtain ⟨H, K, j, k, Q, T, hj, hk, -, hQ, hT⟩ := h
  have e0 : eLpNorm (θ f) 2 μ' = eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ' :=
    eLpNorm_congr_ae (hj.2.2.2 f).symm
  have ei : ∀ i, eLpNorm (θω i f) 2 μ' =
      eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ' := by
    intro i
    rw [← hT, hQ f i]
    exact eLpNorm_congr_ae ((hk i).2.2.2 f).symm
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (T (j (q f)))
  rw [T.norm_map] at hs
  have hs' : HasSum (fun i ↦ (eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2)
      ((eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2) := by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    exact hs
  refine ⟨e0 ▸ Lp.eLpNorm_lt_top _, ?_⟩
  have hsq : ∀ w : Lp ℂ 2 μ', eLpNorm w 2 μ' ^ 2 = ENNReal.ofReal ((eLpNorm w 2 μ').toReal ^ 2) :=
    fun w ↦ by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp only [ei, e0, hsq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs'.summable, hs'.tsum_eq]

/-- If the Hilbert-sum norm identity holds for one nonzero continuous theta function,
the norm-one group has mass at least one: Bessel bounds the components by the mass squared. -/
private theorem Printed.rawIsotype_contra {C : Type*} [CommGroup C] [TopologicalSpace C]
    [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (K : Subgroup C) [CompactSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (μ : Measure C) [μ.IsMulLeftInvariant] [SFinite μ] [μ.IsOpenPosMeasure]
    (θ : C → ℂ) (hθ : Continuous θ) (Θ : PontryaginDual K → C → ℂ)
    (hΘc : ∀ ω, Continuous (Θ ω))
    (hΘ : ∀ ω g, Θ ω g = ∫ h, θ (h.val * g) * (ω h : ℂ) ∂ν)
    (hvol : ν univ < 1) (g0 : C) (hg0 : θ g0 ≠ 0)
    (hfin : eLpNorm θ 2 μ < ⊤) (heq : ∑' ω, eLpNorm (Θ ω) 2 μ ^ 2 = eLpNorm θ 2 μ ^ 2) :
    False := by
  have hb := Printed.rawIsotype_integrated K ν μ θ hθ Θ hΘc hΘ
  have hω : ∀ ω, ∫⁻ g, ‖Θ ω g‖ₑ ^ 2 ∂μ = eLpNorm (Θ ω) 2 μ ^ 2 :=
    fun ω ↦ (Printed.rawIsotype_eLpNorm_sq μ _ (hΘc ω)).symm
  simp only [hω] at hb
  rw [heq, ← Printed.rawIsotype_eLpNorm_sq μ θ hθ] at hb
  have he : eLpNorm θ 2 μ ^ 2 = 0 := by
    by_contra hne
    have hfin2 : eLpNorm θ 2 μ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hfin.ne
    have h1 : 1 ≤ ν univ ^ 2 := by
      exact (ENNReal.mul_le_mul_iff_left (a := 1) (b := ν univ ^ 2) hne hfin2).mp
        (by rwa [one_mul])
    exact absurd h1 (not_le.mpr (pow_lt_one₀ bot_le hvol two_ne_zero))
  have h0 : θ =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).mp (pow_eq_zero_iff two_ne_zero |>.mp he)
  exact hg0 (congrFun ((hθ.ae_eq_iff_eq μ continuous_const).mp h0) g0)

/-- The norm-one idele classes of ℚ(ζ₃) have Tamagawa mass π/(3√3) < 1. -/
private theorem Printed.rawIsotype_volume_lt_one :
    normOneIdeleClassTamagawaMeasure (CyclotomicField 3 ℚ) univ < 1 := by
  rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.ofReal_lt_one]
  have : IsCyclotomicExtension {(3:ℕ)} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hh : NumberField.classNumber (CyclotomicField 3 ℚ) = 1 :=
    classNumber_eq_one_iff.mpr (IsCyclotomicExtension.Rat.three_pid _)
  have ht : Units.torsionOrder (CyclotomicField 3 ℚ) = 6 := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := 3)]; decide
  have hd : NumberField.discr (CyclotomicField 3 ℚ) = -3 := by
    rw [IsCyclotomicExtension.Rat.discr_prime 3 (CyclotomicField 3 ℚ)]
    norm_num
  have h1 : InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) _ (by norm_num)
  have h2 : InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3]; decide
  have hR : Units.regulator (CyclotomicField 3 ℚ) = 1 := by
    have hc : Fintype.card (InfinitePlace (CyclotomicField 3 ℚ)) = 1 := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]
    have hall : ∀ a b : InfinitePlace (CyclotomicField 3 ℚ), a = b :=
      Fintype.card_le_one_iff.mp hc.le
    classical
    rw [Units.regulator_eq_det', Matrix.det_eq_one_of_card_eq_zero
      (Fintype.card_eq_zero_iff.mpr ⟨fun w ↦ w.2 (hall _ _)⟩), abs_one]
  rw [hh, ht, hd, h1, h2, hR]
  have hs : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hpi := Real.pi_lt_d2
  rw [div_lt_one (by positivity)]
  norm_num
  nlinarith

/-- The global statement fails over ℚ(ζ₃) with a = α = β = s = 0. -/
private theorem Printed.rawIsotype_global_aux (F : Type) [Field F] [NumberField F]
    (hvol : normOneIdeleClassTamagawaMeasure F univ < 1)
    (h : Printed.HasHomogeneousSobolevFactorization (X := GlobalAdelicThetaSpace F)
      (Y := GlobalHomogeneousThetaSpace F) (ideleClassTamagawaMeasure F)
      (fun u : CompactIntervalSobolev (ideleClassTamagawaMeasure F)
          (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) 0 0 0 ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
          IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ) 0 (adelicTheta f))
      (fun ω f ↦ modulationWeight (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ :
          IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ) 0 (homogeneousAdelicTheta ω f))) : False := by
  obtain ⟨f, _, hg0⟩ := globalTheta_zero_eval_theta_one F
  have hF := Printed.rawIsotype_factorization_norm h
    (by simp [intervalSobolevMeasure, intervalSobolevDensity]) f
  simp only [modulationWeight_zero] at hF
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let : T2Space (IdeleClassGroup (𝓞 F) F) := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 F) F) := by
    let := idele_secondCountable F
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact Printed.rawIsotype_contra (ideleClassNorm F).ker (normOneIdeleClassTamagawaMeasure F)
    (ideleClassTamagawaMeasure F) (adelicTheta f) (adelicTheta f).continuous
    (fun ω ↦ homogeneousAdelicTheta ω f) (fun ω ↦ (homogeneousAdelicTheta ω f).continuous)
    (fun _ _ ↦ rfl) hvol 1 hg0 hF.1 hF.2

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(ζ₃), a = s = 0 and I = {0}, so the
weight is one. The isometry gives ‖θ‖² = Σ_ω ‖θ_ω‖² for every test function. By Bessel's
inequality for the characters of the norm-one classes, the right side is at most
vol(C¹)²‖θ‖², and vol(C¹) = π/(3√3) < 1. So every theta function would vanish, but a
nonnegative archimedean bump times the indicator of the finite integers has nonzero theta.
(The printed counterexample over ℚ(i), with norm-one mass π/4, works the same way.) -/
theorem Printed.globalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.globalThetaSobolev_rawIsotypeDecomposition := fun h ↦
  Printed.rawIsotype_global_aux (CyclotomicField 3 ℚ) Printed.rawIsotype_volume_lt_one
    (h (CyclotomicField 3 ℚ) 0 0 0 0 le_rfl le_rfl)

/-- Paper: Proposition 10.1.1.5(2), p. 437, (10.1.1.15). The product of the
S-local homogeneous quotient maps factors isometrically through the Hilbert sum.
The factors carry the norm of their weighted homogeneous functions. -/
def Printed.sLocalThetaSobolev_rawIsotypeDecomposition : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a α β s : ℝ), 0 < a → α ≤ β → 0 ≤ s → 0 < α →
    let G := SIdeleQuotient F S
    let m : G →ₜ* ℝ≥0ˣ := ⟨sIdeleQuotientNorm F S, (isProperMap_sIdeleQuotientNorm F S).continuous⟩
    let μ := sLocalQuotientTamagawaMeasure F S
    let W := CompactIntervalSobolev μ (fun g ↦ Real.log ((m g).val : ℝ)) α β s
    Printed.HasHomogeneousSobolevFactorization (X := SLocalAdelicThetaSpace F S)
      (Y := SLocalHomogeneousThetaSpace F S) μ (fun u : W ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight m a (sLocalAdelicThetaOnClasses F S f))
      (fun ω f ↦ modulationWeight m a (sLocalHomogeneousAdelicThetaLinearMap F S ω f))

/-- `rawIsotype_factorization_norm` for a weighted measure `μ' ≪ μ`: the Hilbert-sum
factorization equates the squared weighted norm of each total function with the sum of the
squared weighted norms of its components. -/
private theorem Printed.rawIsotype_factorization_norm' {G B X Ω : Type*} {Y : Ω → Type*}
    [MeasurableSpace G] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    {μ μ' : Measure G} {q : B → X} {qω : ∀ i, B → Y i}
    {θ : B → G → ℂ} {θω : Ω → B → G → ℂ}
    (h : Printed.HasHomogeneousSobolevFactorization (W := Lp ℂ 2 μ') μ (fun u ↦ ⇑u)
      q qω θ θω) (hμ : μ' ≪ μ) (f : B) :
    eLpNorm (θ f) 2 μ' < ⊤ ∧ ∑' i, eLpNorm (θω i f) 2 μ' ^ 2 = eLpNorm (θ f) 2 μ' ^ 2 := by
  obtain ⟨H, K, j, k, Q, T, hj, hk, -, hQ, hT⟩ := h
  have e0 : eLpNorm (θ f) 2 μ' = eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ' :=
    eLpNorm_congr_ae (hμ.ae_eq (hj.2.2.2 f)).symm
  have ei : ∀ i, eLpNorm (θω i f) 2 μ' =
      eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ' := by
    intro i
    rw [← hT, hQ f i]
    exact eLpNorm_congr_ae (hμ.ae_eq ((hk i).2.2.2 f)).symm
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (T (j (q f)))
  rw [T.norm_map] at hs
  have hs' : HasSum (fun i ↦ (eLpNorm (((T (j (q f)) i : K i) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2)
      ((eLpNorm (((j (q f) : H) : Lp ℂ 2 μ')) 2 μ').toReal ^ 2) := by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    exact hs
  refine ⟨e0 ▸ Lp.eLpNorm_lt_top _, ?_⟩
  have hsq : ∀ w : Lp ℂ 2 μ', eLpNorm w 2 μ' ^ 2 = ENNReal.ofReal ((eLpNorm w 2 μ').toReal ^ 2) :=
    fun w ↦ by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  simp only [ei, e0, hsq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hs'.summable, hs'.tsum_eq]

/-- For S = ∅ and finitely many units, the theta function of a test that depends only on
the idelic norm is the number of units times the same profile of the class norm. -/
private theorem Printed.rawIsotype_sLocal_theta (F : Type) [Field F] [NumberField F]
    [Finite ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ)]
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F ∅))) (φ : ℝ → ℂ)
    (hf : ∀ g : (SAdeleRing F ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      φ ((sIdeleNorm F ∅ g).val : ℝ)) (x : SIdeleQuotient F ∅) :
    sLocalAdelicThetaOnClasses F ∅ f x =
      (Nat.card ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
        Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) : ℂ) *
        φ ((sIdeleQuotientNorm F ∅ x).val : ℝ) := by
  refine Quotient.inductionOn x fun y ↦ ?_
  refine (sLocalAdelicThetaOnClasses_mk F ∅ f y).trans ((sLocalAdelicTheta_apply F ∅ f y).trans ?_)
  calc
    _ = ∑' _ : ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
        Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ), φ ((sIdeleNorm F ∅ y).val : ℝ) := by
      apply tsum_congr
      intro u
      refine (hf (_ * y)).trans (congrArg (fun t : ℝ≥0ˣ ↦ φ (t.val : ℝ)) ?_)
      rw [map_mul, MonoidHom.comp_apply,
        show sIdeleNorm F ∅ _ = 1 from (sIdeleNorm_spec F ∅).2 ⟨u, rfl⟩, one_mul]
    _ = _ := by
      rw [tsum_const, nsmul_eq_mul, sIdeleQuotientNorm_mk]

/-- One Hilbert-sum coordinate equal to `r • v` with `‖r‖ > 1` contradicts the norm
identity `Σ ‖Θ_j‖² = ‖v‖²` for `0 < ‖v‖ < ∞`. -/
private theorem Printed.rawIsotype_sLocal_contra {G Ω : Type*} [MeasurableSpace G]
    (μ' : Measure G) (v : G → ℂ) (Θ : Ω → G → ℂ) (i : Ω) (r : ℂ) (hr : 1 < ‖r‖ₑ)
    (hΘ : Θ i = r • v) (hfin : eLpNorm v 2 μ' < ⊤) (hne : eLpNorm v 2 μ' ≠ 0)
    (heq : ∑' j, eLpNorm (Θ j) 2 μ' ^ 2 = eLpNorm v 2 μ' ^ 2) : False := by
  have hle := le_tsum (fun j ↦ eLpNorm (Θ j) 2 μ' ^ 2) i
  simp only [heq, hΘ, eLpNorm_const_smul, mul_pow] at hle
  have hfin2 : eLpNorm v 2 μ' ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hfin.ne
  have hne2 : eLpNorm v 2 μ' ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have h1 : ‖r‖ₑ ^ 2 ≤ 1 :=
    (ENNReal.mul_le_mul_iff_left (a := ‖r‖ₑ ^ 2) (b := 1) hne2 hfin2).mp (by rwa [one_mul])
  exact absurd h1 (not_le.mpr (one_lt_pow₀ hr two_ne_zero))

/-- A continuous function that is nonzero somewhere has nonzero L² norm for a measure with
everywhere positive density against an open-positive measure. -/
private theorem Printed.rawIsotype_sLocal_eLpNorm_ne_zero {G : Type*} [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [μ.IsOpenPosMeasure]
    (d : G → ℝ≥0∞) (hd : Measurable d) (hd0 : ∀ x, d x ≠ 0) (v : G → ℂ) (hv : Continuous v)
    (g0 : G) (hg0 : v g0 ≠ 0) : eLpNorm v 2 (μ.withDensity d) ≠ 0 := by
  intro h0
  have h1 : v =ᵐ[μ.withDensity d] 0 := (eLpNorm_eq_zero_iff two_ne_zero).mp h0
  have h2 : v =ᵐ[μ] 0 :=
    (withDensity_absolutelyContinuous' hd.aemeasurable (.of_forall hd0)).ae_eq h1
  exact hg0 (congrFun ((hv.ae_eq_iff_eq μ continuous_const).mp h2) g0)

/-- The S-local statement with a = α = β = 1, s = 0 fails as soon as the norm-one mass
exceeds one and some nonzero theta function depends only on the norm: its trivial-character
average is the mass times itself. -/
private theorem Printed.rawIsotype_sLocal_aux (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hvol : 1 < sLocalNormOneQuotientMeasure F S univ)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hrad : ∀ x y, sIdeleQuotientNorm F S x = sIdeleQuotientNorm F S y →
      sLocalAdelicThetaOnClasses F S f x = sLocalAdelicThetaOnClasses F S f y)
    (g0 : SIdeleQuotient F S) (hg0 : sLocalAdelicThetaOnClasses F S f g0 ≠ 0)
    (h : Printed.HasHomogeneousSobolevFactorization (X := SLocalAdelicThetaSpace F S)
      (Y := SLocalHomogeneousThetaSpace F S) (sLocalQuotientTamagawaMeasure F S)
      (fun u : CompactIntervalSobolev (sLocalQuotientTamagawaMeasure F S)
          (fun g ↦ Real.log ((sIdeleQuotientNorm F S g).val : ℝ)) 1 1 0 ↦ ⇑u)
      Submodule.Quotient.mk (fun _ ↦ Submodule.Quotient.mk)
      (fun f ↦ modulationWeight (⟨sIdeleQuotientNorm F S,
          (isProperMap_sIdeleQuotientNorm F S).continuous⟩ : SIdeleQuotient F S →ₜ* ℝ≥0ˣ) 1
            (sLocalAdelicThetaOnClasses F S f))
      (fun ω f ↦ modulationWeight (⟨sIdeleQuotientNorm F S,
          (isProperMap_sIdeleQuotientNorm F S).continuous⟩ : SIdeleQuotient F S →ₜ* ℝ≥0ˣ) 1
            (sLocalHomogeneousAdelicThetaLinearMap F S ω f))) : False := by
  have hF := Printed.rawIsotype_factorization_norm' h (withDensity_absolutelyContinuous _ _) f
  have : CompactSpace (sIdeleQuotientNorm F S).ker := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  have : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have : IsFiniteMeasure (sLocalNormOneQuotientMeasure F S) := CompactSpace.isFiniteMeasure
  have hone : (sLocalHomogeneousAdelicThetaLinearMap F S 1 f : SIdeleQuotient F S → ℂ) =
      ((sLocalNormOneQuotientMeasure F S).real univ : ℂ) •
        (sLocalAdelicThetaOnClasses F S f : SIdeleQuotient F S → ℂ) := by
    funext g
    rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
    have hker (k : (sIdeleQuotientNorm F S).ker) :
        sLocalAdelicThetaOnClasses F S f (g * k.val) = sLocalAdelicThetaOnClasses F S f g :=
      hrad _ _ (by rw [map_mul, k.property, mul_one])
    simp only [hker, PontryaginDual.one_apply, Circle.coe_one, mul_one, integral_const,
      Complex.real_smul, Pi.smul_apply, smul_eq_mul]
  let : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  have : (sLocalQuotientTamagawaMeasure F S).IsHaarMeasure :=
    (sLocalQuotientTamagawaMeasure_isWeil (F := F) (S := S)).1
  have hmc : Continuous fun g : SIdeleQuotient F S ↦ ((sIdeleQuotientNorm F S g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_sIdeleQuotientNorm F S).continuous)
  have hvc : Continuous (modulationWeight (⟨sIdeleQuotientNorm F S,
      (isProperMap_sIdeleQuotientNorm F S).continuous⟩ : SIdeleQuotient F S →ₜ* ℝ≥0ˣ) 1
        (sLocalAdelicThetaOnClasses F S f)) := by
    change Continuous fun g ↦ ((((sIdeleQuotientNorm F S g).val : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) *
      sLocalAdelicThetaOnClasses F S f g
    exact (Complex.continuous_ofReal.comp (hmc.rpow_const fun _ ↦ Or.inr zero_le_one)).mul
      (sLocalAdelicThetaOnClasses F S f).continuous
  have hpos : ∀ g : SIdeleQuotient F S, 0 < ((sIdeleQuotientNorm F S g).val : ℝ) :=
    fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _)
  have hne := Printed.rawIsotype_sLocal_eLpNorm_ne_zero (sLocalQuotientTamagawaMeasure F S)
    (fun g ↦ ENNReal.ofReal (if (false : Bool) then
      (intervalSobolevDensity 1 1 0 (Real.log ((sIdeleQuotientNorm F S g).val : ℝ)))⁻¹ else
      intervalSobolevDensity 1 1 0 (Real.log ((sIdeleQuotientNorm F S g).val : ℝ))))
    (by
      refine ENNReal.measurable_ofReal.comp ?_
      simp only [Bool.false_eq_true, ite_false, intervalSobolevDensity, zero_div, Real.rpow_zero,
        mul_one, max_self]
      exact (measurable_const.mul (Real.measurable_log.comp hmc.measurable)).exp)
    (fun g ↦ by
      simp only [Bool.false_eq_true, ite_false, intervalSobolevDensity, ne_eq,
        ENNReal.ofReal_eq_zero, not_le]
      positivity)
    _ hvc g0 (by
      change ((((sIdeleQuotientNorm F S g0).val : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) *
        sLocalAdelicThetaOnClasses F S f g0 ≠ 0
      exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (hpos g0) 1).ne') hg0)
  refine Printed.rawIsotype_sLocal_contra _ _ _ 1
    ((sLocalNormOneQuotientMeasure F S).real univ : ℂ) ?_ ?_ hF.1 hne hF.2
  · rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
      Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact hvol
  · rw [hone, map_smul]

/-- ℚ(ζ₃) has exactly one infinite place, and it is complex. -/
private theorem Printed.rawIsotype_sLocal_place :
    Nonempty (Unique (InfinitePlace (CyclotomicField 3 ℚ))) ∧
      ∀ w : InfinitePlace (CyclotomicField 3 ℚ), w.IsComplex := by
  have : IsCyclotomicExtension {(3:ℕ)} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have h1 : InfinitePlace.nrRealPlaces (CyclotomicField 3 ℚ) = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 3) _ (by norm_num)
  have h2 : InfinitePlace.nrComplexPlaces (CyclotomicField 3 ℚ) = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 3]; decide
  have hc : Fintype.card (InfinitePlace (CyclotomicField 3 ℚ)) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h1, h2]
  refine ⟨Fintype.card_eq_one_iff_nonempty_unique.mp hc, fun w ↦ ?_⟩
  exact (IsCyclotomicExtension.Rat.isTotallyComplex (n := 3) (CyclotomicField 3 ℚ)
    (by norm_num)).isComplex w

/-- The units of ℚ(ζ₃) integral at every finite place (S = ∅) are finite, at most six. -/
private theorem Printed.rawIsotype_sLocal_units :
    Finite ((((∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)))) :
      Set (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)))).integer (CyclotomicField 3 ℚ))ˣ) ∧
    Nat.card ((((∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)))) :
      Set (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)))).integer (CyclotomicField 3 ℚ))ˣ) ≤ 6 := by
  classical
  have : IsCyclotomicExtension {(3:ℕ)} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  let η : (𝓞 (CyclotomicField 3 ℚ))ˣ :=
    (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
  let L : List (𝓞 (CyclotomicField 3 ℚ))ˣ := [1, -1, η, -η, η ^ 2, -η ^ 2]
  have hmem : ∀ u : (𝓞 (CyclotomicField 3 ℚ))ˣ, u ∈ L.toFinset := fun u ↦
    List.mem_toFinset.mpr (IsCyclotomicExtension.Rat.Three.Units.mem hζ u)
  let ι : (𝓞 (CyclotomicField 3 ℚ))ˣ → L.toFinset := fun u ↦ ⟨u, hmem u⟩
  have hι : Function.Injective ι := fun a b h ↦ by simpa [ι] using congrArg Subtype.val h
  have hfin : Finite (𝓞 (CyclotomicField 3 ℚ))ˣ := Finite.of_injective ι hι
  have hcard : Nat.card (𝓞 (CyclotomicField 3 ℚ))ˣ ≤ 6 :=
    (Nat.card_le_card_of_injective ι hι).trans (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (List.toFinset_card_le L).trans (by simp [L]))
  rw [Finset.coe_empty, integer_empty]
  let a := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 (CyclotomicField 3 ℚ))
    (CyclotomicField 3 ℚ))
  let e := (Units.mapEquiv a.toRingEquiv.toMulEquiv).toEquiv
  exact ⟨Finite.of_equiv _ e.symm, (Nat.card_congr e).le.trans hcard⟩

/-- Over ℚ(ζ₃) with S = ∅, the Gaussian exp(−|z|²) in the complex coordinate is a test
function equal to exp(−|g|) on every S-idele g (the idelic norm is |z|²). -/
private theorem Printed.rawIsotype_sLocal_gaussian
    (hU : Nonempty (Unique (InfinitePlace (CyclotomicField 3 ℚ))))
    (hC : ∀ w : InfinitePlace (CyclotomicField 3 ℚ), w.IsComplex) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing (CyclotomicField 3 ℚ) ∅)),
      ∀ g : (SAdeleRing (CyclotomicField 3 ℚ) ∅)ˣ, f (Multiplicative.ofAdd g.val) =
        (Real.exp (-((sIdeleNorm (CyclotomicField 3 ℚ) ∅ g).val : ℝ)) : ℂ) := by
  classical
  obtain ⟨hU⟩ := hU
  let w0 : InfinitePlace (CyclotomicField 3 ℚ) := default
  let wc : {w : InfinitePlace (CyclotomicField 3 ℚ) // w.IsComplex} := ⟨w0, hC w0⟩
  have : IsEmpty {w : InfinitePlace (CyclotomicField 3 ℚ) // w.IsReal} :=
    ⟨fun w ↦ InfinitePlace.not_isReal_iff_isComplex.mpr (hC w.1) w.2⟩
  let : Unique {w : InfinitePlace (CyclotomicField 3 ℚ) // w.IsComplex} :=
    { default := wc, uniq := fun w ↦ Subtype.ext (Unique.eq_default w.1) }
  let L : mixedEmbedding.mixedSpace (CyclotomicField 3 ℚ) ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.uniqueProd ℝ _ _).trans
      (ContinuousLinearEquiv.funUnique {w : InfinitePlace (CyclotomicField 3 ℚ) // w.IsComplex} ℝ ℂ)
  obtain ⟨γ, hγ⟩ := exists_gaussian_schwartz (E := ℂ) 1 one_pos
  let bs : SchwartzMap (mixedEmbedding.mixedSpace (CyclotomicField 3 ℚ)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L γ
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing (CyclotomicField 3 ℚ))) :=
    ⟨fun x ↦ bs (InfiniteAdeleRing.ringEquiv_mixedSpace (CyclotomicField 3 ℚ) x.toAdd),
      (mem_archimedeanSchwartzBruhat_iff _).mpr ⟨bs, fun _ ↦ rfl⟩⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv (CyclotomicField 3 ℚ)
    (∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ))))
  let gg : ∀ w : (∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ)))),
      SchwartzBruhat (Multiplicative (w.val.adicCompletion (CyclotomicField 3 ℚ))) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  refine ⟨e (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, gg w)), fun g ↦ ?_⟩
  rw [he]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  change γ (L (InfiniteAdeleRing.ringEquiv_mixedSpace (CyclotomicField 3 ℚ) g.val.1)) = _
  rw [hγ]
  have hL : L (InfiniteAdeleRing.ringEquiv_mixedSpace (CyclotomicField 3 ℚ) g.val.1) =
      InfinitePlace.Completion.extensionEmbedding w0 (g.val.1 w0) := rfl
  rw [hL, (InfinitePlace.Completion.isometry_extensionEmbedding w0).norm_map_of_map_zero
    (map_zero _)]
  rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ))))),
    Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w0,
    (hC w0).mult_eq_two]
  simp only [neg_mul, one_mul]
  rfl

/-- At a complex place, the multiplicative Tamagawa measure of the annulus 1 ≤ |x|² ≤ T is
at least 2π(T − 1)/T: the density 1/|x|² is at least 1/T and the measure is twice Lebesgue. -/
private theorem Printed.rawIsotype_sLocal_annulus_local (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (T : ℝ) (hT : 1 ≤ T) :
    ENNReal.ofReal (2 * Real.pi * (T - 1) / T) ≤ infiniteLocalMultiplicativeTamagawaMeasure F w
      {x | ((‖x.val‖₊ ^ w.mult : ℝ≥0) : ℝ) ∈ Icc 1 T} := by
  let : MeasurableSpace w.Completion := borel _
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let e := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hnorm (x : w.Completion) : ‖e x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)) x
  have hnorm' (z : ℂ) : ‖e.symm z‖ = ‖z‖ := by
    rw [← hnorm, e.apply_symm_apply]
  let A : Set ℂ := Metric.closedBall 0 (√T) \ Metric.ball 0 1
  have hA : MeasurableSet A := measurableSet_closedBall.diff measurableSet_ball
  have hsub : e ⁻¹' A ⊆ range (Units.val : w.Completionˣ → w.Completion) := by
    intro x hx
    have hx1 : ¬ ‖e x‖ < 1 := by simpa [A] using hx.2
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [hnorm, norm_zero] at hx1
      exact hx1 zero_lt_one
    exact ⟨Units.mk0 x hx0, rfl⟩
  have hset : {x : w.Completionˣ | ((‖x.val‖₊ ^ w.mult : ℝ≥0) : ℝ) ∈ Icc 1 T} =
      Units.val ⁻¹' (e ⁻¹' A) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, A, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
      dist_zero_right, hnorm, hw.mult_eq_two, NNReal.coe_pow, coe_nnNorm, mem_Icc, not_lt]
    have h0 := norm_nonneg (x.val)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨Real.le_sqrt_of_sq_le h2, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by nlinarith, ?_⟩
      calc ‖x.val‖ ^ 2 ≤ (√T) ^ 2 := by gcongr
        _ = T := Real.sq_sqrt (by linarith)
  rw [hset, infiniteLocalMultiplicativeTamagawaMeasure, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ (e.measurable hA),
    infiniteLocalAdditiveTamagawaMeasure, dif_neg (InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
  change _ ≤ ∫⁻ x in e ⁻¹' A, (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂(Measure.map e.symm (2 • volume))
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map, e.symm_preimage_preimage]
  have hT0 : 0 < T := by linarith
  have hvol : (volume : Measure ℂ) A = ENNReal.ofReal (Real.pi * (T - 1)) := by
    show volume (Metric.closedBall (0 : ℂ) √T \ Metric.ball 0 1) = _
    rw [measure_sdiff (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
        (Real.le_sqrt_of_sq_le (by simpa using hT)))) measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne, Complex.volume_closedBall, Complex.volume_ball,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hT0.le, ENNReal.ofReal_one, one_pow,
      one_mul, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ← ENNReal.ofReal_mul hT0.le,
      ← ENNReal.ofReal_sub _ Real.pi_pos.le]
    congr 1; ring
  calc ENNReal.ofReal (2 * Real.pi * (T - 1) / T)
      = ∫⁻ _ in A, ENNReal.ofReal T⁻¹ ∂(2 • (volume : Measure ℂ)) := by
        rw [setLIntegral_const, smul_apply, hvol, nsmul_eq_mul, Nat.cast_ofNat, ← ENNReal.ofReal_ofNat,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ ∫⁻ z in A, (↑(‖e.symm z‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂(2 • (volume : Measure ℂ)) := by
        refine setLIntegral_mono ?_ fun z hz ↦ ?_
        · exact ((e.symm.measurable.nnNorm.pow_const _).coe_nnreal_ennreal).inv
        · rw [ENNReal.ofReal_inv_of_pos hT0, ENNReal.inv_le_inv, hw.mult_eq_two,
            ← ENNReal.ofReal_coe_nnreal, NNReal.coe_pow, coe_nnNorm, hnorm']
          refine ENNReal.ofReal_le_ofReal ?_
          have hz1 : ‖z‖ ≤ √T := by simpa [A] using hz.1
          calc ‖z‖ ^ 2 ≤ (√T) ^ 2 := by gcongr
            _ = T := Real.sq_sqrt hT0.le

/-- Over ℚ(ζ₃) with S = ∅, the S-ideles of norm in [1, T] have mass at least 2π(T − 1)/T. -/
private theorem Printed.rawIsotype_sLocal_annulus
    (hU : Nonempty (Unique (InfinitePlace (CyclotomicField 3 ℚ))))
    (hC : ∀ w : InfinitePlace (CyclotomicField 3 ℚ), w.IsComplex) (T : ℝ) (hT : 1 ≤ T) :
    ENNReal.ofReal (2 * Real.pi * (T - 1) / T) ≤
      sMultiplicativeTamagawaMeasure (CyclotomicField 3 ℚ) ∅
        {g | ((sIdeleNorm (CyclotomicField 3 ℚ) ∅ g).val : ℝ) ∈ Icc 1 T} := by
  obtain ⟨hU⟩ := hU
  let w0 : InfinitePlace (CyclotomicField 3 ℚ) := default
  let : ∀ w : InfinitePlace (CyclotomicField 3 ℚ), MeasurableSpace w.Completion := fun _ ↦ borel _
  let : ∀ w : InfinitePlace (CyclotomicField 3 ℚ), BorelSpace w.Completion := fun _ ↦ ⟨rfl⟩
  let : ∀ w : InfinitePlace (CyclotomicField 3 ℚ), BorelSpace w.Completionˣ :=
    fun _ ↦ borelSpace_units_of_continuousInv₀ _
  let B : (w : InfinitePlace (CyclotomicField 3 ℚ)) → Set w.Completionˣ :=
    fun w ↦ {x | ((‖x.val‖₊ ^ w.mult : ℝ≥0) : ℝ) ∈ Icc 1 T}
  have hB : ∀ w, MeasurableSet (B w) := fun w ↦
    ((NNReal.continuous_coe.comp ((continuous_nnNorm.comp Units.continuous_val).pow _)).measurable)
      measurableSet_Icc
  have key := sMultiplicativeTamagawaMeasure_integerUnits (CyclotomicField 3 ℚ) ∅ B hB
  rw [Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ))))),
    Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w0] at key
  refine (Printed.rawIsotype_sLocal_annulus_local _ w0 (hC w0) T hT).trans (le_of_eq_of_le key.symm
    (measure_mono fun g hg ↦ ?_))
  have h1 := hg.1 w0
  simp only [B, mem_ofPred_eq] at h1 ⊢
  rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 (CyclotomicField 3 ℚ))))),
    Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w0]
  exact h1

/-- Weil's formula with counting measure on a finite closed subgroup of at most n elements:
the preimage of a set of cosets has at most n times its quotient mass. -/
private theorem Printed.rawIsotype_weil_band {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) [Finite H] (n : ℕ) (hn : Nat.card H ≤ n)
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [(Measure.count : Measure H).IsHaarMeasure]
    [(Measure.count : Measure H).Regular] [SigmaFinite μ]
    (ν : @Measure (G ⧸ H) (borel (G ⧸ H))) (hν : IsWeilQuotientMeasure H μ Measure.count ν)
    (B : Set (G ⧸ H)) (hB : @MeasurableSet _ (borel (G ⧸ H)) B) :
    μ (QuotientGroup.mk ⁻¹' B) ≤ n * ν B := by
  classical
  let : MeasurableSpace (G ⧸ H) := borel _
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hE : MeasurableSet (QuotientGroup.mk ⁻¹' B : Set G) :=
    QuotientGroup.continuous_mk.measurable hB
  obtain ⟨hκ, hμ⟩ := weilMeasure_eq_bind H hH μ Measure.count ν hν
  rw [← hμ, Measure.bind_apply hE hκ.aemeasurable, ← lintegral_indicator_const hB]
  refine lintegral_mono fun q ↦ ?_
  have ht : Measurable (fun h : H ↦ q.out * (h : G)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  dsimp only
  rw [Measure.map_apply ht hE]
  have hpre : (fun h : H ↦ q.out * (h : G)) ⁻¹' (QuotientGroup.mk ⁻¹' B) =
      if q ∈ B then univ else ∅ := by
    ext h
    have hq : (QuotientGroup.mk (q.out * (h : G)) : G ⧸ H) = q := by
      rw [QuotientGroup.mk_mul, QuotientGroup.eq_one_iff (h : G) |>.mpr h.2, mul_one]
      exact QuotientGroup.out_eq' q
    simp only [mem_preimage, hq]
    split_ifs with hqB <;> simp [hqB]
  rw [hpre]
  split_ifs with hqB
  · rw [indicator_of_mem hqB, Measure.count_univ]
    have : ENat.card H ≤ n := by
      rw [ENat.card_eq_coe_natCard H]
      exact_mod_cast hn
    exact_mod_cast this
  · simp

/-- The S-idele classes of norm in [1, T] have quotient mass vol(J₁) · log T. -/
private theorem Printed.rawIsotype_sLocal_bandMass (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (T : ℝ) (hT : 1 ≤ T) :
    sLocalQuotientTamagawaMeasure F S {x | ((sIdeleQuotientNorm F S x).val : ℝ) ∈ Icc 1 T} =
      sLocalNormOneQuotientMeasure F S univ * ENNReal.ofReal (Real.log T) := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : BorelSpace (SIdeleQuotient F S) := ⟨rfl⟩
  have : BorelSpace (sIdeleQuotientNorm F S).ker := ⟨rfl⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ :=
    ⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩
  have hτ : Function.RightInverse τ (sIdeleNorm F S) := by
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
  have hJ := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  let Sb : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 T}
  let B : Set (SIdeleQuotient F S) := {x | ((sIdeleQuotientNorm F S x).val : ℝ) ∈ Icc 1 T}
  have hBm : MeasurableSet B :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_sIdeleQuotientNorm F S).continuous)).measurable measurableSet_Icc
  have hφ : Continuous fun x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ ↦
      (x.1 : SIdeleQuotient F S) * QuotientGroup.mk (τ x.2) := by
    fun_prop
  change sLocalQuotientTamagawaMeasure F S B = _
  rw [← hJ, Measure.map_apply hφ.measurable hBm]
  have hpre : (fun x : (sIdeleQuotientNorm F S).ker × ℝ≥0ˣ ↦
      (x.1 : SIdeleQuotient F S) * QuotientGroup.mk (τ x.2)) ⁻¹' B = univ ×ˢ Sb := by
    ext ⟨k, t⟩
    simp only [mem_preimage, mem_prod, mem_univ, true_and, B, Sb, mem_ofPred_eq]
    rw [map_mul, k.property, one_mul, sIdeleQuotientNorm_mk, hτ t]
  have hT0 : (⟨T, by linarith⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' : T = 0 := congrArg Subtype.val h
    linarith
  have hPR := positiveRealHaar_interval (Units.mk0 ⟨T, by linarith⟩ hT0) hT
  rw [hpre, Measure.prod_prod]
  exact congrArg _ hPR

/-- For S = ∅ and at most n units, the S-ideles of norm in [1, T] have mass at most
n · vol(J₁) · log T. -/
private theorem Printed.rawIsotype_sLocal_band (F : Type) [Field F] [NumberField F]
    (hU : Finite ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
      Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ))
    (n : ℕ) (hn : Nat.card ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
      Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) ≤ n) (T : ℝ) (hT : 1 ≤ T) :
    sMultiplicativeTamagawaMeasure F ∅
        {g | ((sIdeleNorm F ∅ g).val : ℝ) ∈ Icc 1 T} ≤
      n * (sLocalNormOneQuotientMeasure F ∅ univ * ENNReal.ofReal (Real.log T)) := by
  let : MeasurableSpace (SAdeleRing F ∅) := instMeasurableSpaceSAdeleRing F ∅
  let : T2Space (SAdeleRing F ∅)ˣ := (sIdeleGroup_description F ∅).2.1
  let : LocallyCompactSpace (SAdeleRing F ∅)ˣ := (sIdeleGroup_description F ∅).2.2.1
  let : BorelSpace (SAdeleRing F ∅)ˣ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := ∅)
  let := sMultiplicativeTamagawaMeasure_regular (F := F) (S := ∅)
  let D : Subgroup (SAdeleRing F ∅)ˣ :=
    Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F ∅)
      (Subring.subtype (integralAdelesOutside F ∅)))))
      (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F ∅))))
  let : DiscreteTopology D := discreteTopology_sProjectedDiagonal
  let : (Measure.count : Measure D).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure D).Regular := count_regular_of_discreteTopology
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  have hind := (sIdeleGroup_description F ∅).1
  let : SecondCountableTopology (SAdeleRing F ∅) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : (∅ : Finset (HeightOneSpectrum (𝓞 F)))) →
      v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F ∅)ˣ := hind.secondCountableTopology
  let : SigmaFinite (sMultiplicativeTamagawaMeasure F ∅) := inferInstance
  let ψ : ((((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
      Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ) → D := fun u ↦
    ⟨_, Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨u, rfl⟩)⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, ⟨y, ⟨u, rfl⟩, rfl⟩⟩
    exact ⟨u, rfl⟩
  have : Finite D := Finite.of_surjective ψ hψ
  have hD : Nat.card D ≤ n := (Nat.card_le_card_of_surjective ψ hψ).trans hn
  let : BorelSpace (SIdeleQuotient F ∅) := ⟨rfl⟩
  have key := Printed.rawIsotype_weil_band D isClosed_sProjectedDiagonal n hD
    (sMultiplicativeTamagawaMeasure F ∅) (sLocalQuotientTamagawaMeasure F ∅)
    sLocalQuotientTamagawaMeasure_isWeil
    {x | ((sIdeleQuotientNorm F ∅ x).val : ℝ) ∈ Icc 1 T}
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_sIdeleQuotientNorm F ∅).continuous)).measurable measurableSet_Icc)
  rw [Printed.rawIsotype_sLocal_bandMass F ∅ T hT] at key
  exact key

/-- The norm-one quotient of ℚ(ζ₃) with S = ∅ has mass above one (it is π/3): at T = 26/25
the two bounds on the annulus give 2π/26 ≤ 6 · vol(J₁)/25. -/
private theorem Printed.rawIsotype_sLocal_mass :
    1 < sLocalNormOneQuotientMeasure (CyclotomicField 3 ℚ) ∅ univ := by
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨hU, hC⟩ := Printed.rawIsotype_sLocal_place
  obtain ⟨hfin, hcard⟩ := Printed.rawIsotype_sLocal_units
  have h3 := Printed.rawIsotype_sLocal_annulus hU hC (26 / 25) (by norm_num)
  have h4 := Printed.rawIsotype_sLocal_band (CyclotomicField 3 ℚ) hfin 6 hcard (26 / 25)
    (by norm_num)
  have hlog : Real.log (26 / 25) ≤ 1 / 25 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 26 / 25 by norm_num)
    linarith
  have h5 : ENNReal.ofReal (2 * Real.pi * (26 / 25 - 1) / (26 / 25)) ≤
      ENNReal.ofReal (6 * (1 / 25)) := by
    refine (h3.trans h4).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_ofNat]
    gcongr
    calc _ ≤ 1 * ENNReal.ofReal (Real.log (26 / 25)) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact ENNReal.ofReal_le_ofReal hlog
  rw [ENNReal.ofReal_le_ofReal_iff (by norm_num)] at h5
  have := Real.pi_gt_d2
  linarith

/-- Paper: Proposition 10.1.1.5(2), p. 437. Take ℚ(ζ₃), S empty (only the
complex place), a = 1, I = {1}, and s = 0. The Gaussian exp(−|g|) in the complex
coordinate gives a nonzero theta function that depends only on the norm, so its
trivial-character average is vol(J₁) times itself. The Hilbert sum norm is therefore at
least vol(J₁) times the norm, and vol(J₁) = π/3 > 1. Only vol(J₁) > 1 is proved: the
idelic annulus 1 ≤ |g| ≤ 26/25 has mass at least 2π(T − 1)/T and at most
6 vol(J₁) log T (six units), which forces vol(J₁) > 1.
(The printed counterexample over ℚ(i), with factor π/2, works the same way.) -/
theorem Printed.sLocalThetaSobolev_rawIsotypeDecomposition_false :
    ¬ Printed.sLocalThetaSobolev_rawIsotypeDecomposition := by
  intro h
  obtain ⟨hU, hC⟩ := Printed.rawIsotype_sLocal_place
  obtain ⟨f, hf⟩ := Printed.rawIsotype_sLocal_gaussian hU hC
  have := Printed.rawIsotype_sLocal_units.1
  have hθ := Printed.rawIsotype_sLocal_theta (CyclotomicField 3 ℚ) f
    (fun t ↦ (Real.exp (-t) : ℂ)) hf
  refine Printed.rawIsotype_sLocal_aux (CyclotomicField 3 ℚ) ∅ Printed.rawIsotype_sLocal_mass f
    (fun x y hxy ↦ by rw [hθ, hθ, hxy]) 1 ?_
    (h (CyclotomicField 3 ℚ) ∅ 1 1 1 0 one_pos le_rfl le_rfl one_pos)
  rw [hθ]
  refine mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne') ?_
  exact_mod_cast (Real.exp_pos _).ne'

/-- Paper: Theorem 10.1.2.1, p. 437. As printed, inversion in the idele class
group defines a continuous linear automorphism of the same ambient Sobolev space
for every compact nonempty interval. -/
def Printed.ideleClassSobolev_inversion_automorphism : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (α β s : ℝ), α ≤ β → 0 ≤ s →
    let μ := ideleClassTamagawaMeasure F
    let W := CompactIntervalSobolev μ
      (fun g ↦ Real.log ((ideleClassNorm F g).val : ℝ)) α β s
    ∃ J : W ≃L[ℂ] W, ∀ u : W,
      (J u : IdeleClassGroup (𝓞 F) F → ℂ) =ᵐ[μ] fun g ↦ u g⁻¹

open scoped ENNReal in
/-- On the weighted L² space with weight |x|² (I = {1}, s = 0) over a commutative group with a
module taking a value above one, inversion is not a bounded automorphism. It would conjugate
translation by g⁻¹ into translation by g, so its norm would be at most |g|⁻² times itself. -/
private theorem Printed.ideleClassSobolev_inversion_automorphism_false_aux {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ) (g : G) (hg : 1 < ((m g).val : ℝ))
    (J : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 ≃L[ℂ]
      CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[μ] fun x ↦ u x⁻¹) : False := by
  set d : G → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (if (false : Bool) then (intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)))⁻¹
     else intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ))) with hd_def
  have hνμ : μ.withDensity d ≪ μ := withDensity_absolutelyContinuous μ d
  let T := hardySobolevTranslation μ m 1 1 0 le_rfl le_rfl
  have hinv : QuasiMeasurePreserving (Inv.inv : G → G) μ μ :=
    quasiMeasurePreserving_inv μ
  have hmul : QuasiMeasurePreserving (fun x : G ↦ g * x) μ μ :=
    (measurePreserving_mul_left μ g).quasiMeasurePreserving
  -- Inversion turns translation by g⁻¹ into translation by g.
  have hconj (u : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0) :
      J u = T g⁻¹ (J (T g⁻¹ u)) := by
    apply Lp.ext
    apply hνμ.ae_eq
    have h1 : (T g⁻¹ (J (T g⁻¹ u)) : G → ℂ) =ᵐ[μ] fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x) := by
      simpa only [inv_inv] using hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ _
    have h2 : (fun x ↦ (J (T g⁻¹ u) : G → ℂ) (g * x)) =ᵐ[μ]
        fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹ :=
      hmul.ae_eq_comp (hJ _)
    have h3 : (fun x ↦ (T g⁻¹ u : G → ℂ) (g * x)⁻¹) =ᵐ[μ]
        fun x ↦ (u : G → ℂ) (g * (g * x)⁻¹) := by
      have h := hardySobolevTranslation_apply μ m 1 1 0 le_rfl le_rfl g⁻¹ u
      simp only [inv_inv] at h
      exact (hinv.comp hmul).ae_eq_comp h
    filter_upwards [hJ u, h1, h2, h3] with x hx h1 h2 h3
    rw [hx, h1, h2, h3, mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  -- Translation by g⁻¹ has norm at most |g|⁻¹ < 1.
  set L := Real.log ((m g).val : ℝ)
  have hL : 0 < L := Real.log_pos hg
  have hTnorm : ‖T g⁻¹‖ ≤ Real.exp (-L) := by
    have h := norm_hardySobolevTranslation_le μ m 1 1 0 le_rfl le_rfl g⁻¹
    have hlog : Real.log ((m g⁻¹).val : ℝ) = -L := by
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
    simpa only [hlog, one_mul, max_self, zero_div, Real.rpow_zero, mul_one] using h
  have hq : Real.exp (-L) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_lt_zero.mpr hL)
  have hq0 : 0 ≤ Real.exp (-L) := (Real.exp_pos _).le
  have hJop : J.toContinuousLinearMap = (T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹)) :=
    ContinuousLinearMap.ext hconj
  have hJn : ‖J.toContinuousLinearMap‖ ≤ Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by
    calc ‖J.toContinuousLinearMap‖ = ‖(T g⁻¹).comp (J.toContinuousLinearMap.comp (T g⁻¹))‖ :=
          congrArg norm hJop
      _ ≤ ‖T g⁻¹‖ * (‖J.toContinuousLinearMap‖ * ‖T g⁻¹‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ Real.exp (-L) * (‖J.toContinuousLinearMap‖ * Real.exp (-L)) := by
          gcongr
      _ = Real.exp (-L) ^ 2 * ‖J.toContinuousLinearMap‖ := by ring
  have hJ0 : ‖J.toContinuousLinearMap‖ = 0 := by
    have hq2 : Real.exp (-L) ^ 2 < 1 := by nlinarith
    by_contra hne
    have hpos := lt_of_le_of_ne (norm_nonneg J.toContinuousLinearMap) (Ne.symm hne)
    nlinarith [mul_pos hpos (sub_pos.mpr hq2)]
  -- The space is nonzero: the indicator of a compact neighbourhood of 1 has positive norm.
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hKm : MeasurableSet K := hKc.measurableSet
  have hdc : Continuous fun x : G ↦ intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    have hl : Continuous fun x : G ↦ Real.log ((m x).val : ℝ) :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
        fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    unfold intervalSobolevDensity
    fun_prop
  have hdpos (x : G) : 0 < intervalSobolevDensity 1 1 0 (Real.log ((m x).val : ℝ)) := by
    unfold intervalSobolevDensity
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have : IsLocallyFiniteMeasure (μ.withDensity d) := by
    simp only [hd_def, Bool.false_eq_true, ite_false]
    exact IsLocallyFiniteMeasure.withDensity_ofReal hdc
  have hfin : μ.withDensity d K ≠ ⊤ := hKc.measure_lt_top.ne
  have hpos : μ.withDensity d K ≠ 0 := by
    intro h0
    have hμν : μ ≪ μ.withDensity d := by
      refine withDensity_absolutelyContinuous' ?_ (.of_forall fun x ↦ ?_)
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact hdc.measurable.ennreal_ofReal.aemeasurable
      · simp only [hd_def, Bool.false_eq_true, ite_false]
        exact (ENNReal.ofReal_pos.mpr (hdpos x)).ne'
    exact (Measure.measure_pos_of_mem_nhds μ hK1).ne' (hμν h0)
  let v : CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 1 1 0 :=
    indicatorConstLp 2 hKm hfin (1 : ℂ)
  have hv : v ≠ 0 := by
    intro h
    have hn := congrArg norm h
    rw [norm_zero, norm_indicatorConstLp' (by norm_num) hpos, norm_one, one_mul] at hn
    exact (Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos hfin) _).ne' hn
  apply hv
  have hJv : J v = 0 := by
    rw [← norm_eq_zero]
    refine le_antisymm ?_ (norm_nonneg _)
    calc ‖J v‖ = ‖J.toContinuousLinearMap v‖ := rfl
      _ ≤ ‖J.toContinuousLinearMap‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ = 0 := by rw [hJ0, zero_mul]
  have h := congrArg J.symm hJv
  rwa [ContinuousLinearEquiv.symm_apply_apply, map_zero] at h

/-- Paper: Theorem 10.1.2.1, p. 437. Take ℚ, I = {1} and s = 0. The indicator
of |g| < 1 is square integrable for t² dt/t in the norm coordinate t, while its
inverse pullback is the indicator of |g| > 1, which has infinite squared integral. -/
theorem Printed.ideleClassSobolev_inversion_automorphism_false :
    ¬ Printed.ideleClassSobolev_inversion_automorphism := by
  intro h
  obtain ⟨J, hJ⟩ := h ℚ 1 1 0 le_rfl le_rfl
  let : BorelSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  let : T2Space (IdeleClassGroup (𝓞 ℚ) ℚ) := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.1
  let : SecondCountableTopology (IdeleClassGroup (𝓞 ℚ) ℚ) := by
    let := idele_secondCountable ℚ
    exact inferInstanceAs (SecondCountableTopology
      (IdeleGroup (𝓞 ℚ) ℚ ⧸ IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ))
  let : (ideleClassTamagawaMeasure ℚ).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil ℚ).1
  let m : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  let t : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  let g : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hg : m g = t := canonicalIdeleNormSection_rightInverse ℚ t
  exact Printed.ideleClassSobolev_inversion_automorphism_false_aux
    (ideleClassTamagawaMeasure ℚ) m g (by rw [hg]; norm_num [t]) J hJ

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. In the a-line
notation the local Fourier transform extends at precisely the half weight. -/
def Printed.sLocalThetaSobolev_fourier_on_line : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a s : ℝ) (ha : 0 < a) (hs : 0 ≤ s),
    let hp : 0 < a + 0 := by simpa using ha
    let H := ↥(sLocalThetaSobolev F S ha (le_refl (0 : ℝ)) hs hp)
    let j := sLocalThetaSobolevInclusion F S ha (le_refl (0 : ℝ)) hs hp
    (∃ T : H →L[ℂ] H, ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      T (j (Submodule.Quotient.mk f)) =
        j (Submodule.Quotient.mk (sAdeleSchwartzFourier (F := F) (S := S) f))) ↔ a = 1 / 2

section LocalFourierOnLine

set_option quotPrecheck false

local notation "J" => SIdeleQuotient ℚ ∅
local notation "A" => SAdeleRing ℚ ∅
local notation "B" => SchwartzBruhat (Multiplicative A)
local notation "μJ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "m" =>
  (⟨sIdeleQuotientNorm ℚ ∅, (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous⟩ : J →ₜ* ℝ≥0ˣ)
local notation "r" => (fun g : J ↦ ((m g).val : ℝ))
local notation "ρ" => (fun g : J ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (r g))))
local notation "HF" => ↥(sLocalThetaSobolev ℚ ∅
  (show (0 : ℝ) < 1 / 2 by norm_num) (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ 2 by norm_num)
  (show (0 : ℝ) < 1 / 2 + 0 by norm_num))
local notation "j" => sLocalThetaSobolevInclusion ℚ ∅
  (show (0 : ℝ) < 1 / 2 by norm_num) (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ 2 by norm_num)
  (show (0 : ℝ) < 1 / 2 + 0 by norm_num)
local notation "θ(" f ")" => sLocalAdelicThetaOnClasses ℚ ∅ f
local notation "Fₛ" => sAdeleSchwartzFourier (F := ℚ) (S := ∅)
private def localFourierOnLine_class (f : B) : HF := j (Submodule.Quotient.mk f)

local notation "v(" f ")" => localFourierOnLine_class f

private theorem localFourierOnLine_continuous_norm : Continuous r :=
  NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)

private theorem localFourierOnLine_density (g : J) :
    intervalSobolevDensity 0 0 2 (Real.log (r g)) = 1 + Real.log (r g) ^ 2 := by
  norm_num [intervalSobolevDensity]

private def localFourierOnLine_energy (f : B) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (r g * (1 + Real.log (r g) ^ 2)) * ‖θ(f) g‖ₑ ^ 2 ∂μJ

private theorem localFourierOnLine_norm_sq (f : B) :
    ‖v(f)‖ₑ ^ 2 = localFourierOnLine_energy f := by
  unfold localFourierOnLine_energy
  let ν : Measure J := (μJ).withDensity ρ
  have hJ : BorelSpace J := ⟨rfl⟩
  let : SecondCountableTopology J := by
    let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology (InfiniteAdeleRing ℚ) := inferInstanceAs
      (SecondCountableTopology ((w : InfinitePlace ℚ) → w.Completion))
    let : SecondCountableTopology A := inferInstanceAs
      (SecondCountableTopology (InfiniteAdeleRing ℚ ×
        ((v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ)))
    let : SecondCountableTopology Aˣ := (sIdeleGroup_description ℚ ∅).1.secondCountableTopology
    exact inferInstanceAs (SecondCountableTopology (Aˣ ⧸ _))
  let u : Lp ℂ 2 ν := (v(f)).val
  have hu : (u : J → ℂ) =ᵐ[μJ] modulationWeight m (1/2) (θ(f)) :=
    (existsUnique_sLocalThetaSobolevEmbedding (F := ℚ) (S := ∅) (1/2) 0 0 2
      (by norm_num) le_rfl (by norm_num) (by norm_num)).exists.choose_spec.2 f
  have hν : Continuous ρ := by
    simp_rw [localFourierOnLine_density]
    have hl := localFourierOnLine_continuous_norm.log
      (fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (m g))).ne')
    exact ENNReal.continuous_ofReal.comp (continuous_const.add (hl.pow 2))
  have hW : Continuous (modulationWeight m (1 / 2) (θ(f))) := by
    apply Continuous.mul _ (θ(f)).continuous
    exact Complex.continuous_ofReal.comp
      (localFourierOnLine_continuous_norm.rpow_const fun g ↦
        Or.inl (NNReal.coe_pos.mpr (Units.zero_lt (m g))).ne')
  change ‖u‖ₑ ^ 2 = _
  rw [Lp.eNorm_def, eLpNorm_congr_ae ((withDensity_absolutelyContinuous μJ ρ).ae_eq hu)]
  have hsq := eLpNorm_nnreal_pow_eq_lintegral (μ := ν) (f := modulationWeight m (1/2) (θ(f)))
    (p := 2) two_ne_zero hW.aestronglyMeasurable
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at hsq
  change eLpNorm (modulationWeight m (1 / 2) (θ(f))) 2 ν ^ 2 = _
  have hsq' : eLpNorm (modulationWeight m (1 / 2) (θ(f))) 2 ν ^ 2 =
      ∫⁻ x, ‖modulationWeight m (1 / 2) (θ(f)) x‖ₑ ^ 2 ∂ν := hsq
  rw [hsq', lintegral_withDensity_eq_lintegral_mul _ hν.measurable (hW.measurable.eNorm.pow_const 2)]
  apply lintegral_congr
  intro g
  have hn : 0 < r g := NNReal.coe_pos.mpr (Units.zero_lt (m g))
  change ρ g * ‖(((r g ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * θ(f) g‖ₑ ^ 2 = _
  rw [eNorm_mul, mul_pow, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg
    (Real.rpow_nonneg hn.le _), ← ENNReal.ofReal_pow (Real.rpow_nonneg hn.le _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num,
    Real.rpow_one, ← mul_assoc, ← ENNReal.ofReal_mul (by
      rw [localFourierOnLine_density]; positivity), localFourierOnLine_density, mul_comm (1 + _ ^ 2)]

private theorem localFourierOnLine_norm_band (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    positiveRealHaar {u | (u.val : ℝ) ∈ Icc a b} = ENNReal.ofReal (Real.log b - Real.log a) := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {u : ℝ≥0ˣ | (u.val : ℝ) ∈ Icc a b} :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  have hpre : e ⁻¹' {u | (u.val : ℝ) ∈ Icc a b} = Icc (Real.log a) (Real.log b) := by
    ext x
    change (a ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) ≤ b) ↔ _
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, ← Real.le_log_iff_exp_le (ha.trans_le hab),
      ← Real.log_le_iff_le_exp ha]
    rfl
  rw [hpre, Real.volume_Icc]

private theorem localFourierOnLine_radial_mass :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : ℝ, 0 < a → a ≤ b →
      μJ {g | r g ∈ Icc a b} = ENNReal.ofReal (d * (Real.log b - Real.log a)) := by
  let : BorelSpace J := ⟨rfl⟩
  let : (μJ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let : LocallyCompactSpace J := by
    let : LocallyCompactSpace Aˣ := (sIdeleGroup_description ℚ ∅).2.2.1
    let : IsClosed (_ : Set Aˣ) := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
    exact inferInstanceAs (LocallyCompactSpace (Aˣ ⧸ _))
  have hsec := (sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)).choose_spec
  have hproper := isProperMap_sIdeleQuotientNorm ℚ ∅
  let ζ := (μJ).map m
  let : ζ.IsHaarMeasure := Measure.isHaarMeasure_map μJ (m).toMonoidHom (m).continuous
    hsec.surjective ((isProperMap_iff_tendsto_cocompact.mp hproper).2)
  let d := Measure.haarScalarFactor ζ positiveRealHaar
  have hζ : ζ = d • positiveRealHaar := Measure.isMulLeftInvariant_eq_smul _ _
  have hd : 0 < d := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  refine ⟨d, by exact_mod_cast hd, fun a b ha hab ↦ ?_⟩
  let S := {u : ℝ≥0ˣ | (u.val : ℝ) ∈ Icc a b}
  have hSm : MeasurableSet S :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  have hm : Measurable (m : J → ℝ≥0ˣ) := (m).continuous.measurable
  change μJ (m ⁻¹' S) = _
  calc
    μJ (m ⁻¹' S) = ζ S := (Measure.map_apply hm hSm).symm
    _ = ENNReal.ofReal (d * (Real.log b - Real.log a)) := by
      rw [hζ, smul_apply, ENNReal.smul_def, smul_eq_mul, localFourierOnLine_norm_band a b ha hab,
        ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]

private theorem localFourierOnLine_norm_le_twice_of_sq {V : Type*} [NormedAddCommGroup V]
    (v₁ v₀ : V) (h : ‖v₁‖ₑ ^ 2 ≤ 4 * ‖v₀‖ₑ ^ 2) : ‖v₁‖ ≤ 2 * ‖v₀‖ := by
  have hn := ENNReal.toReal_mono (by finiteness : 4 * ‖v₀‖ₑ ^ 2 ≠ ∞) h
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow] at hn
  simp only [toReal_eNorm, ENNReal.toReal_ofNat] at hn
  nlinarith [norm_nonneg v₁, norm_nonneg v₀]

private theorem localFourierOnLine_weighted_norm_bound (f f₀ : B)
    (h : ∀ g : J, ‖θ(f) g‖ ≤ 2 * ‖θ(f₀) g‖) :
    ‖v(f)‖ ≤ 2 * ‖v(f₀)‖ := by
  apply localFourierOnLine_norm_le_twice_of_sq
  have hsq : localFourierOnLine_energy f ≤ 4 * localFourierOnLine_energy f₀ := by
    unfold localFourierOnLine_energy
    rw [← lintegral_const_mul' _ _ (by norm_num)]
    apply lintegral_mono
    intro g
    have hₑ : ‖θ(f) g‖ₑ ≤ 2 * ‖θ(f₀) g‖ₑ := by
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
        ofReal_norm] using ENNReal.ofReal_le_ofReal (h g)
    have hs := pow_le_pow_left' hₑ 2
    rw [mul_pow, show (2 : ℝ≥0∞) ^ 2 = 4 by norm_num] at hs
    let weight := ENNReal.ofReal (r g * (1 + Real.log (r g) ^ 2))
    change weight * ‖θ(f) g‖ₑ ^ 2 ≤ 4 * (weight * ‖θ(f₀) g‖ₑ ^ 2)
    calc
      _ ≤ weight * (4 * ‖θ(f₀) g‖ₑ ^ 2) := mul_le_mul' le_rfl hs
      _ = _ := by ac_rfl
  exact (localFourierOnLine_norm_sq f).le.trans
    (hsq.trans (mul_le_mul' le_rfl (localFourierOnLine_norm_sq f₀).ge))

private theorem localFourierOnLine_log_lower (q : ℝ) (hq : 1 ≤ q) :
    1 / 2 ≤ q * (Real.log (q + 1) - Real.log q) := by
  have hp : 0 < q := zero_lt_one.trans_le hq
  have h₁ : 0 < q + 1 := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hp h₁)
  rw [Real.log_div hp.ne' h₁.ne'] at h
  have he : q / (q + 1) - 1 = -1 / (q + 1) := by field_simp; ring
  rw [he] at h
  have h₂ : 1 / (q + 1) ≤ Real.log (q + 1) - Real.log q := by
    have heq : -1 / (q + 1) = -(1 / (q + 1)) := neg_div _ _
    rw [heq] at h
    linarith
  have hh : 1 / 2 ≤ q * (1 / (q + 1)) := by
    rw [mul_one_div, le_div_iff₀ h₁]
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_left h₂ hp.le)

private theorem localFourierOnLine_ofReal_norm_sq {V : Type*} [NormedAddCommGroup V] (x : V) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg x), ofReal_norm]

private theorem localFourierOnLine_weighted_norm_lower
    (d k : ℝ) (hd : 0 < d) (hk : 0 < k) (q : ℝ) (hq : 1 ≤ q) (f : B)
    (hmass : μJ {g | r g ∈ Icc q (q + 1)} = ENNReal.ofReal (d * (Real.log (q + 1) - Real.log q)))
    (hf : ∀ g : J, r g ∈ Icc q (q + 1) → k ≤ ‖θ(f) g‖) :
    d * k ^ 2 / 2 * Real.log q ^ 2 ≤ ‖v(f)‖ ^ 2 := by
  let : BorelSpace J := ⟨rfl⟩
  let S : Set J := r ⁻¹' (Icc q (q + 1))
  have hSm : MeasurableSet S := measurableSet_Icc.preimage localFourierOnLine_continuous_norm.measurable
  let c : ℝ := (q * Real.log q ^ 2) * k ^ 2
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hl : (ENNReal.ofReal c) * μJ S ≤ localFourierOnLine_energy f := by
    unfold localFourierOnLine_energy
    rw [← Measure.restrict_apply_univ S,
      ← lintegral_const, ← lintegral_indicator hSm]
    apply lintegral_mono
    intro g
    by_cases hg : g ∈ S
    · rw [indicator_of_mem hg, ENNReal.ofReal_mul (by positivity : 0 ≤ q * Real.log q ^ 2),
        ENNReal.ofReal_pow hk.le]
      have hqg : q ≤ r g := hg.1
      have hlogg : Real.log q ≤ Real.log (r g) := Real.log_le_log hqpos hqg
      have hn : Real.log q ^ 2 ≤ 1 + Real.log (r g) ^ 2 := by
        have := sq_le_sq' (by linarith [Real.log_nonneg hq]) hlogg
        linarith
      apply mul_le_mul'
      · apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul hqg hn (sq_nonneg _) (hqpos.le.trans hqg)
      · exact pow_le_pow_left' (by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal (hf g hg)) 2
    · rw [indicator_of_notMem hg]
      exact bot_le
  have hupper : localFourierOnLine_energy f = ENNReal.ofReal (‖v(f)‖ ^ 2) :=
    (localFourierOnLine_norm_sq f).symm.trans
      (localFourierOnLine_ofReal_norm_sq (v(f))).symm
  rw [show μJ S = _ from hmass, ← ENNReal.ofReal_mul hc, hupper] at hl
  have hL' := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖v(f)‖)).mp hl
  calc
    _ = (1 / 2) * (d * k ^ 2 * Real.log q ^ 2) := by ring
    _ ≤ (q * (Real.log (q + 1) - Real.log q)) * (d * k ^ 2 * Real.log q ^ 2) :=
      mul_le_mul_of_nonneg_right (localFourierOnLine_log_lower q hq) (by positivity)
    _ = c * (d * (Real.log (q + 1) - Real.log q)) := by dsimp [c]; ring
    _ ≤ _ := hL'

set_option maxHeartbeats 1500000 in
private theorem localFourierOnLine_contra (f₀ : B) (k : ℝ) (hk : 0 < k)
    (hpeak : ∀ q : ℝ, 1 ≤ q → ∃ f : B,
      (∀ g : J, ‖θ(f) g‖ ≤ 2 * ‖θ(f₀) g‖) ∧
      (∀ g : J, r g ∈ Icc q (q + 1) → k ≤ ‖θ(Fₛ f) g‖)) :
    ¬ Printed.sLocalThetaSobolev_fourier_on_line := by
  intro hall
  obtain ⟨T, hT⟩ := (hall ℚ ∅ (1 / 2) 2 (by norm_num) (by norm_num)).mpr rfl
  obtain ⟨d, hd, hm⟩ := localFourierOnLine_radial_mass
  let M := 2 * ‖T‖ * ‖v(f₀)‖
  let C := d * k ^ 2 / 2
  have hC : 0 < C := by dsimp [C]; positivity
  let x := 1 + M ^ 2 / C
  have hx : 1 ≤ x := le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hC.le)
  let q := Real.exp x
  have hq : 1 ≤ q := Real.one_le_exp_iff.mpr (zero_le_one.trans hx)
  obtain ⟨f, hf, hg⟩ := hpeak q hq
  have hupper : ‖v(Fₛ f)‖ ≤ M := by
    have ht : T (v(f)) = v(Fₛ f) := hT f
    calc
      ‖v(Fₛ f)‖ = ‖T (v(f))‖ := congrArg (norm : HF → ℝ) ht.symm
      _ ≤ ‖T‖ * ‖v(f)‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (2 * ‖v(f₀)‖) :=
        mul_le_mul_of_nonneg_left (localFourierOnLine_weighted_norm_bound f f₀ hf) (norm_nonneg _)
      _ = M := by dsimp [M]; ring
  have hlow := localFourierOnLine_weighted_norm_lower d k hd hk q hq (Fₛ f)
    (hm q (q + 1) (zero_lt_one.trans_le hq) (by linarith)) hg
  change C * Real.log q ^ 2 ≤ ‖v(Fₛ f)‖ ^ 2 at hlow
  have hCx : C * x = C + M ^ 2 := by dsimp [x]; field_simp [hC.ne']
  have hx₁ : x ≤ x ^ 2 := by nlinarith
  rw [show Real.log q = x from Real.log_exp x] at hlow
  have hM : C + M ^ 2 ≤ M ^ 2 := calc
    _ = C * x := hCx.symm
    _ ≤ C * x ^ 2 := mul_le_mul_of_nonneg_left hx₁ hC.le
    _ ≤ ‖v(Fₛ f)‖ ^ 2 := hlow
    _ ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hupper _
  linarith

open scoped FourierTransform

private def localFourierOnLine_gaussian : SchwartzMap ℝ ℂ :=
  (SchwartzMap.gaussian Real.pi Real.pi_pos).postcompCLM Complex.ofRealCLM

private theorem localFourierOnLine_gaussian_apply (x : ℝ) :
    localFourierOnLine_gaussian x = (Real.exp (-Real.pi * x ^ 2) : ℝ) := by
  rw [localFourierOnLine_gaussian, SchwartzMap.postcompCLM_apply, SchwartzMap.gaussian_apply,
    Complex.ofRealCLM_apply, Real.norm_eq_abs, sq_abs]

private theorem localFourierOnLine_gaussian_fourier :
    𝓕 localFourierOnLine_gaussian = localFourierOnLine_gaussian := by
  ext x
  have hg : (⇑localFourierOnLine_gaussian) =
      fun x : ℝ ↦ Complex.exp (-Real.pi * (1 : ℂ) * (x : ℂ) ^ 2) := by
    funext t
    rw [localFourierOnLine_gaussian_apply]
    push_cast
    simp only [mul_one]
  rw [SchwartzMap.fourier_coe, hg, fourier_gaussian_pi (by norm_num)]
  simp only [Complex.one_cpow, div_one, one_mul, mul_one]

private def localFourierOnLine_peaks (q : ℝ) : SchwartzMap ℝ ℂ :=
  localFourierOnLine_gaussian.compSubConstCLM ℂ q +
    localFourierOnLine_gaussian.compSubConstCLM ℂ (-q)

private theorem localFourierOnLine_peaks_apply (q x : ℝ) :
    localFourierOnLine_peaks q x = ((Real.exp (-Real.pi * (x - q) ^ 2) +
      Real.exp (-Real.pi * (x + q) ^ 2) : ℝ) : ℂ) := by
  simp only [localFourierOnLine_peaks, add_apply, SchwartzMap.compSubConstCLM_apply,
    localFourierOnLine_gaussian_apply, Complex.ofReal_add, sub_neg_eq_add]

private theorem localFourierOnLine_shift_norm (q x : ℝ) :
    ‖(𝓕⁻ (localFourierOnLine_gaussian.compSubConstCLM ℂ q)) x‖ =
      Real.exp (-Real.pi * x ^ 2) := by
  simp only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
  let f : ℝ → ℂ := localFourierOnLine_gaussian
  have heq : (⇑(localFourierOnLine_gaussian.compSubConstCLM ℂ q)) = f ∘ fun v ↦ v + -q := by
    funext v
    simp [f, sub_eq_add_neg]
  have hFT (g : ℝ → ℂ) (y : ℝ) :
      𝓕 g y = Fourier.fourierIntegral Real.fourierChar volume g y := by
    rw [Real.fourier_real_eq, Fourier.fourierIntegral_def]
  rw [heq, hFT, Fourier.fourierIntegral_comp_add_right]
  dsimp only
  rw [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, ← hFT]
  have he := congrArg (fun g : SchwartzMap ℝ ℂ ↦ g (-x)) localFourierOnLine_gaussian_fourier
  change (𝓕 f) (-x) = localFourierOnLine_gaussian (-x) at he
  rw [he, localFourierOnLine_gaussian_apply, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, neg_sq]

private theorem localFourierOnLine_inv_peak_bound (q x : ℝ) :
    ‖(𝓕⁻ (localFourierOnLine_peaks q)) x‖ ≤ 2 * Real.exp (-Real.pi * x ^ 2) := by
  simp only [localFourierOnLine_peaks, FourierTransform.fourierInv_add, add_apply]
  refine (norm_add_le _ _).trans ?_
  rw [localFourierOnLine_shift_norm, localFourierOnLine_shift_norm, two_mul]

private theorem localFourierOnLine_peaks_lower {q x : ℝ} (hx : |x| ∈ Icc q (q + 1)) :
    Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * (x - q) ^ 2) +
      Real.exp (-Real.pi * (x + q) ^ 2) := by
  rcases le_total 0 x with hp | hn
  · rw [abs_of_nonneg hp] at hx
    obtain ⟨hlo, hhi⟩ := hx
    have hs : (x - q) ^ 2 ≤ 1 := by
      have h := sq_le_sq' (a := x - q) (b := (1 : ℝ)) (by linarith) (by linarith)
      norm_num at h ⊢
      exact h
    exact (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs)])).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [abs_of_nonpos hn] at hx
    obtain ⟨hlo, hhi⟩ := hx
    have hs : (x + q) ^ 2 ≤ 1 := by
      have h := sq_le_sq' (a := x + q) (b := (1 : ℝ)) (by linarith) (by linarith)
      norm_num at h ⊢
      exact h
    exact (Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs)])).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)

local notation "coord" => (fun x : A ↦
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (x.1 Rat.infinitePlace))
local notation "U₀" =>
  (Set.integer ((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ ∅)
    (Subring.subtype (integralAdelesOutside ℚ ∅)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ ∅)))

private theorem localFourierOnLine_theta_dominated (f f₀ : B)
    (w : A → ℝ) (h₀ : ∀ x, f₀ (Multiplicative.ofAdd x) = (w x : ℂ))
    (hw : ∀ x, 0 ≤ w x) (h : ∀ x, ‖f (Multiplicative.ofAdd x)‖ ≤ 2 * w x) :
    ∀ g : J, ‖θ(f) g‖ ≤ 2 * ‖θ(f₀) g‖ := by
  intro g
  obtain ⟨x, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective (QuotientGroup.mk : Aˣ → J)) g
  let z (u : U₀) : A := (unitAtS u * x).val
  have hsum : Summable (fun u ↦ w (z u)) := by
    apply Complex.summable_ofReal.mp
    have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ f₀ {x}
      isCompact_singleton).hasSum rfl).summable
    simpa only [h₀] using hs
  have habs : Summable (fun u ↦ ‖f (Multiplicative.ofAdd (z u))‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun u ↦ h (z u)) (hsum.mul_left 2)
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply,
    sLocalAdelicTheta_apply]
  change ‖∑' u, f (Multiplicative.ofAdd (z u))‖ ≤ 2 * ‖∑' u, f₀ (Multiplicative.ofAdd (z u))‖
  simp_rw [h₀, ← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_of_nonneg (tsum_nonneg fun u ↦ hw (z u))]
  exact (norm_tsum_le_tsum_norm habs).trans
    ((habs.tsum_mono (hsum.mul_left 2) (fun u ↦ h (z u))).trans_eq tsum_mul_left)

private theorem localFourierOnLine_theta_peak (f : B) (q : ℝ)
    (hf : ∀ y : A, Fₛ f (Multiplicative.ofAdd y) = localFourierOnLine_peaks q (coord y))
    (g : J) (hg : r g ∈ Icc q (q + 1)) :
    Real.exp (-Real.pi) ≤ ‖θ(Fₛ f) g‖ := by
  obtain ⟨x, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective (QuotientGroup.mk : Aˣ → J)) g
  let z (u : U₀) : A := (unitAtS u * x).val
  let w (u : U₀) := Real.exp (-Real.pi * (coord (z u) - q) ^ 2) +
    Real.exp (-Real.pi * (coord (z u) + q) ^ 2)
  have hw (u : U₀) : Fₛ f (Multiplicative.ofAdd (z u)) = (w u : ℂ) :=
    (hf _).trans (localFourierOnLine_peaks_apply _ _)
  have hsum : Summable w := by
    apply Complex.summable_ofReal.mp
    have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ ∅ (Fₛ f) {x}
      isCompact_singleton).hasSum rfl).summable
    change Summable (fun u : U₀ ↦ Fₛ f (Multiplicative.ofAdd (z u))) at hs
    simpa only [hw] using hs
  have hp : |coord x.val| ∈ Icc q (q + 1) := by
    have he : |coord x.val| = r (QuotientGroup.mk x) := by
      rw [← Real.norm_eq_abs]
      let e := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
      have hh : ‖e (x.val.1 Rat.infinitePlace)‖ = ‖x.val.1 Rat.infinitePlace‖ :=
        e.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)) _
      exact hh.trans (sLocalThetaSobolev_integrable_false_norm x).symm
    rwa [he]
  have hk : Real.exp (-Real.pi) ≤ w 1 := by
    have h1 : z 1 = x.val := by simp [z]
    simpa only [w, h1] using localFourierOnLine_peaks_lower hp
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  change Real.exp (-Real.pi) ≤ ‖∑' u, Fₛ f (Multiplicative.ofAdd (z u))‖
  simp_rw [hw, ← Complex.ofReal_tsum, Complex.norm_real]
  exact hk.trans ((hsum.le_tsum 1 fun u _ ↦ by dsimp [w]; positivity).trans (le_abs_self _))

private theorem localFourierOnLine_exists_peaks :
    ∃ f₀ : B, ∀ q : ℝ, 1 ≤ q → ∃ f : B,
      (∀ g : J, ‖θ(f) g‖ ≤ 2 * ‖θ(f₀) g‖) ∧
      (∀ g : J, r g ∈ Icc q (q + 1) → Real.exp (-Real.pi) ≤ ‖θ(Fₛ f) g‖) := by
  obtain ⟨E, hE⟩ := ratTrivialHomogeneousTheta_quotient_realEquiv
  refine ⟨E localFourierOnLine_gaussian, ?_⟩
  intro q _
  let φ : SchwartzMap ℝ ℂ := 𝓕⁻ (localFourierOnLine_peaks q)
  refine ⟨E φ, ?_, ?_⟩
  · apply localFourierOnLine_theta_dominated (E φ) (E localFourierOnLine_gaussian)
      (fun x ↦ Real.exp (-Real.pi * (coord x) ^ 2))
    · intro x
      rw [hE, localFourierOnLine_gaussian_apply]
    · exact fun _ ↦ (Real.exp_pos _).le
    · intro x
      rw [hE]
      exact localFourierOnLine_inv_peak_bound q _
  · apply localFourierOnLine_theta_peak (E φ) q
    intro y
    rw [sAdeleSchwartzFourier_ratEmpty_apply φ (E φ) (hE φ), show 𝓕 φ = localFourierOnLine_peaks q from
      FourierTransform.fourier_fourierInv_eq _]

/-- Paper: Announcement before Lemma 10.1.1.3, p. 435. Over ℚ with no finite
places in S, the inverse real Fourier transform of two shifted Gaussian peaks
gives inputs with uniformly bounded degree-two norms. The logarithmic Sobolev
weight makes the norms of their Fourier transforms unbounded at a = 1/2. -/
theorem Printed.sLocalThetaSobolev_fourier_on_line_false :
    ¬ Printed.sLocalThetaSobolev_fourier_on_line := by
  obtain ⟨f₀, hf₀⟩ := localFourierOnLine_exists_peaks
  exact localFourierOnLine_contra f₀ (Real.exp (-Real.pi)) (Real.exp_pos _) hf₀

end LocalFourierOnLine

end RiemannMasullo
