module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Chapter 12.1.1: statements that are false as printed
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Theorem 12.1.1.2(2), p. 499. For every compactly supported continuous
multiplier in the target variable, smoothening the multiplied kernel gives the
pointwise product of the multiplier with the smoothened kernel. -/
def Printed.dSequenceKernelSmoothening_mul_continuous : Prop :=
  ∀ {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
    (U : ℕ → Set G) (f : G → ℝ≥0),
    IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
    Continuous f → (∀ x, 0 < f x) → ν = μ.withDensity (fun x ↦ ↑(f x)) →
    ∀ (k : Lp ℂ 2 (ν.prod ν)), IsNuclearOperator (integralKernelOperator ν k).val →
    ∀ (κ : G × G → ℂ), κ =ᵐ[ν.prod ν] k →
    ∀ (ρ : G → ℂ), Continuous ρ → HasCompactSupport ρ →
    dSequenceKernelSmoothening μ U (fun p ↦ ρ p.1 * κ p) =
      fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p

section Counterexample

open Filter Topology
open scoped ENNReal Pointwise InnerProductSpace

local notation "𝔾" => Multiplicative ℝ

/-- Shrinking symmetric intervals form a D′-sequence for Lebesgue measure. -/
private theorem realInterval_isDPrimeSequence (r : ℕ → ℝ) (hpos : ∀ n, 0 < r n)
    (hanti : Antitone r) (hlim : Tendsto r atTop (𝓝 0)) :
    IsDPrimeSequence (show Measure 𝔾 from (volume : Measure ℝ))
      (fun n ↦ Multiplicative.toAdd ⁻¹' Icc (-r n) (r n)) := by
  let μ : Measure 𝔾 := (volume : Measure ℝ)
  let U (n : ℕ) : Set 𝔾 := Multiplicative.toAdd ⁻¹' Icc (-r n) (r n)
  have hvol (n : ℕ) : μ (U n) = ENNReal.ofReal (2 * r n) := by
    change volume (Icc (-r n) (r n)) = _
    rw [Real.volume_Icc]
    congr 1
    ring
  refine ⟨⟨fun n ↦ ?_, fun i j hij ↦ ?_, 3, by norm_num, fun n ↦ ?_⟩, fun W hW ↦ ?_⟩
  · refine ⟨⟨neg_nonpos.mpr (hpos n).le, (hpos n).le⟩,
      (measurableSet_Icc.preimage MeasurableEquiv.multiplicative.symm.measurable).nullMeasurableSet,
      ?_, ?_⟩
    · exact (hvol n).symm ▸ ENNReal.ofReal_pos.mpr (by linarith [hpos n])
    · exact (hvol n).symm ▸ ENNReal.ofReal_lt_top
  · exact preimage_mono (Icc_subset_Icc (neg_le_neg (hanti hij)) (hanti hij))
  · have hn : -r n ≤ r n := (neg_nonpos.mpr (hpos n).le).trans (hpos n).le
    have hdiff : μ (U n * (U n)⁻¹) = ENNReal.ofReal (4 * r n) := by
      change volume (Icc (-r n) (r n) + -Icc (-r n) (r n)) = _
      rw [← sub_eq_add_neg, Icc_sub_Icc hn hn, Real.volume_Icc]
      congr 1
      ring
    change 0 < μ (U n * (U n)⁻¹) ∧ μ (U n * (U n)⁻¹) < ENNReal.ofReal 3 * μ (U n)
    rw [hdiff, hvol, ← ENNReal.ofReal_mul (by norm_num)]
    exact ⟨ENNReal.ofReal_pos.mpr (by linarith [hpos n]),
      ENNReal.ofReal_lt_ofReal_iff (by linarith [hpos n]) |>.mpr (by linarith [hpos n])⟩
  · change W ∈ 𝓝 (0 : ℝ) at hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨n, fun x hx ↦ hball ?_⟩
    change dist x.toAdd (0 : ℝ) < ε
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr hx).trans_lt hn

/-- The square of the truncated singular factor has the integrable exponent `-1/2`. -/
private theorem truncated_quarterPower_memLp :
    MemLp ((Icc (-1 : ℝ) 1).indicator (fun t ↦ (↑(|t| ^ (-(1 / 4 : ℝ))) : ℂ))) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have hm : Measurable (fun t : ℝ ↦ (↑(|t| ^ (-(1 / 4 : ℝ))) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (continuous_abs.measurable.pow_const _)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  have hpow (t : ℝ) : ‖(↑(|t| ^ (-(1 / 4 : ℝ))) : ℂ)‖ ^ 2 = |t| ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul_natCast (abs_nonneg _)]
    norm_num
  simp only [hpow]
  apply LocallyIntegrable.integrableOn_isCompact _ isCompact_Icc
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1 / 2) (by simp) (by norm_num)
    _ (continuous_abs.measurable.pow_const _).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), one_mul,
      le_refl]

/-- An outer product of two square-integrable functions represents a nuclear kernel. -/
-- The rank-one identification is from integralKernelOperator_outerProduct in AppC_LCTVS/Sec3b.
private theorem exists_nuclear_outerProduct {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.InnerRegular] (a b : X → ℂ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∃ k : Lp ℂ 2 (μ.prod μ), IsNuclearOperator (integralKernelOperator μ k).val ∧
      (fun p : X × X ↦ inner ℂ (b p.2) (a p.1)) =ᵐ[μ.prod μ] k := by
  let u := ha.toLp a
  let v := hb.toLp b
  obtain ⟨k, hk, -⟩ := L2.exists_outerProduct u v
  have hop : (integralKernelOperator μ k).val = (innerSL ℂ v).smulRight u := by
    ext f : 1
    apply Lp.ext
    filter_upwards [integralKernelOperator_apply μ k f, Measure.ae_ae_of_ae_prod hk,
      Lp.coeFn_smul ⟪v, f⟫_ℂ u] with x hx hxy hsmul
    have h : (fun y ↦ k (x, y) * f y) =ᵐ[μ] fun y ↦ u x * ⟪v y, f y⟫_ℂ := by
      filter_upwards [hxy] with y hy
      rw [show k (x, y) = ⟪v y, u x⟫_ℂ from hy, RCLike.inner_apply, RCLike.inner_apply]
      ring
    change (integralKernelOperator μ k).val f x = (⟪v, f⟫_ℂ • u : Lp ℂ 2 μ) x
    rw [hx.2, integral_congr_ae h, integral_const_mul, hsmul]
    change u x * (∫ y, ⟪v y, f y⟫_ℂ ∂μ) = ⟪v, f⟫_ℂ * u x
    rw [L2.inner_def, mul_comm]
  refine ⟨k, hop ▸ isNuclearOperator_smulRight _ _, ?_⟩
  filter_upwards [hk, Measure.quasiMeasurePreserving_fst.ae ha.coeFn_toLp,
    Measure.quasiMeasurePreserving_snd.ae hb.coeFn_toLp] with p hp hpa hpb
  exact (congrArg₂ (inner ℂ) hpb hpa).symm.trans hp.symm

/-- Paper: Theorem 12.1.1.2(2), p. 499. On the additive real line with Lebesgue measure,
take the rank-one kernel `k(t,u) = |t|^(-1/4)` on `[-1,1]²`, extended by zero outside.
The multiplier is `c(t) * |t|^(1/4)`, where the continuous compactly supported cutoff `c`
equals one on `[-1,1]`. On every square of radius `1/(n+1)` about the origin, the multiplied
kernel is one off the null line `t = 0`, so its average is one. At the origin the multiplier
vanishes, giving zero on the right-hand side of the printed identity. -/
private theorem dSequenceKernelSmoothening_mul_continuous_counterexample :
    ∃ (G : Type) (_ : CommGroup G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : T2Space G) (_ : LocallyCompactSpace G) (_ : SecondCountableTopology G)
      (_ : MeasurableSpace G) (_ : BorelSpace G)
      (μ ν : Measure G) (_ : μ.IsHaarMeasure) (_ : IsFiniteMeasureOnCompacts ν)
      (_ : ν.InnerRegular) (U : ℕ → Set G) (f : G → ℝ≥0),
      IsDPrimeSequence μ U ∧ (∀ n, MeasurableSet (U n)) ∧ Continuous f ∧ (∀ x, 0 < f x) ∧
        ν = μ.withDensity (fun x ↦ ↑(f x)) ∧
        (∃ (k : Lp ℂ 2 (ν.prod ν)), IsNuclearOperator (integralKernelOperator ν k).val ∧
          ∃ (κ : G × G → ℂ), κ =ᵐ[ν.prod ν] k ∧
            ∃ (ρ : G → ℂ), Continuous ρ ∧ HasCompactSupport ρ ∧
              dSequenceKernelSmoothening μ U (fun p ↦ ρ p.1 * κ p) ≠
                fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) := by
  classical
  let μ : Measure 𝔾 := (volume : Measure ℝ)
  have : μ.IsHaarMeasure := {
    toIsFiniteMeasureOnCompacts := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
    toIsOpenPosMeasure := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
    map_mul_left_eq_self := fun x ↦
      Measure.IsAddLeftInvariant.map_add_left_eq_self (μ := (volume : Measure ℝ)) x.toAdd }
  have : μ.InnerRegular := inferInstanceAs (volume : Measure ℝ).InnerRegular
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let U (n : ℕ) : Set 𝔾 := Multiplicative.toAdd ⁻¹' Icc (-r n) (r n)
  have hanti : Antitone r := fun _ _ h ↦ one_div_le_one_div_of_le (by positivity)
    (add_le_add_left (Nat.cast_le.mpr h) 1)
  have hD : IsDPrimeSequence μ U := realInterval_isDPrimeSequence r (fun n ↦ by positivity)
    hanti tendsto_one_div_add_atTop_nhds_zero_nat
  have hmeas (n : ℕ) : MeasurableSet (U n) :=
    measurableSet_Icc.preimage MeasurableEquiv.multiplicative.symm.measurable
  let I := Icc (-1 : ℝ) 1
  let a : 𝔾 → ℂ := fun x ↦ I.indicator (fun t ↦ (↑(|t| ^ (-(1 / 4 : ℝ))) : ℂ)) x.toAdd
  let b : 𝔾 → ℂ := fun y ↦ I.indicator (fun _ ↦ (1 : ℂ)) y.toAdd
  have ha : MemLp a 2 μ := truncated_quarterPower_memLp
  have hb : MemLp b 2 μ := memLp_indicator_const (μ := (volume : Measure ℝ)) 2
    measurableSet_Icc.nullMeasurableSet 1 (Or.inr isCompact_Icc.measure_lt_top.ne)
  let κ (p : 𝔾 × 𝔾) := inner ℂ (b p.2) (a p.1)
  obtain ⟨k, hk, hκ⟩ := exists_nuclear_outerProduct μ a b ha hb
  obtain ⟨c, hc, hcK, -, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_Icc : IsCompact I) isOpen_univ I.subset_univ
  let ρ : 𝔾 → ℂ := fun x ↦ ↑(c x.toAdd * |x.toAdd| ^ (1 / 4 : ℝ))
  have hρ : Continuous ρ := Complex.continuous_ofReal.comp ((c.continuous.mul
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).comp continuous_abs)).comp
    continuous_toAdd)
  have hρK : HasCompactSupport ρ := by
    change HasCompactSupport (fun t : ℝ ↦ (↑(c t * |t| ^ (1 / 4 : ℝ)) : ℂ))
    exact (show HasCompactSupport (fun t : ℝ ↦ c t * |t| ^ (1 / 4 : ℝ)) from
      HasCompactSupport.mul_right hcK).comp_left Complex.ofReal_zero
  refine ⟨𝔾, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, μ, μ, inferInstance, inferInstance,
    inferInstance, U, fun _ ↦ 1, hD, hmeas, continuous_const, fun _ ↦ zero_lt_one, by simp,
    k, hk, κ, hκ, ρ, hρ, hρK, ?_⟩
  -- On every averaging square the two powers cancel off the null line t = 0.
  let F (p : 𝔾 × 𝔾) := ρ p.1 * κ p
  have hnonzero : ∀ᵐ x : 𝔾 ∂μ, x.toAdd ≠ 0 := by
    change ∀ᵐ t : ℝ ∂volume, t ≠ 0
    simp [ae_iff]
  have hsubset (n : ℕ) {x : 𝔾} (hx : x ∈ U n) : x.toAdd ∈ I := by
    have hr : r n ≤ 1 := by simpa [r] using hanti (Nat.zero_le n)
    exact Icc_subset_Icc (neg_le_neg hr) hr hx
  have havg (n : ℕ) : dSequenceAverage (μ.prod μ) (U n ×ˢ U n) F 1 = 1 := by
    rw [dSequenceAverage, one_smul]
    calc
      _ = ⨍ _ in U n ×ˢ U n, (1 : ℂ) ∂(μ.prod μ) := by
        apply setAverage_congr_fun ((hmeas n).prod (hmeas n))
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hnonzero] with p hp
        intro hmem
        have hx := hsubset n hmem.1
        have hy := hsubset n hmem.2
        have hcx : c p.1.toAdd = 1 := hc hx
        have hpow : |p.1.toAdd| ^ (1 / 4 : ℝ) ≠ 0 :=
          (Real.rpow_pos_of_pos (abs_pos.mpr hp) _).ne'
        simp [F, ρ, κ, a, b, indicator_of_mem hx, indicator_of_mem hy, hcx, RCLike.inner_apply,
          Real.rpow_neg (abs_nonneg _)]
        exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (by simpa only [one_div] using hpow))
      _ = 1 := by
        obtain ⟨-, -, hpos, hfin⟩ := hD.1.1 n
        apply setAverage_const <;> rw [Measure.prod_prod]
        · exact mul_ne_zero hpos.ne' hpos.ne'
        · exact ENNReal.mul_ne_top hfin.ne hfin.ne
  have ht : Tendsto (fun n ↦ dSequenceAverage (μ.prod μ) (U n ×ˢ U n) F 1) atTop (𝓝 1) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1))
  have hreg : 1 ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) F := ⟨1, ht⟩
  have hs : dSequenceKernelSmoothening μ U F 1 = 1 := by
    simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
      dSequenceSmoothening] using ht.limUnder_eq
  intro heq
  have hρ0 : ρ 1 = 0 := by norm_num [ρ]
  exact one_ne_zero (hs.symm.trans ((congrFun heq 1).trans (by simp [hρ0])))

end Counterexample

/-- Paper: Theorem 12.1.1.2(2), p. 499. The pointwise identity is refuted by the
counterexample above: at the identity the two sides are one and zero. -/
theorem Printed.dSequenceKernelSmoothening_mul_continuous_false :
    ¬ Printed.dSequenceKernelSmoothening_mul_continuous := by
  rintro h
  obtain ⟨G, hG₁, hG₂, hG₃, hG₄, hG₅, hG₆, hG₇, hG₈, μ, ν, hμ, hν, hν', U, f,
    hD, hmeas, hcont, hpos, hdens, k, hk, κ, hκ, ρ, hρ, hρc, hne⟩ :=
    dSequenceKernelSmoothening_mul_continuous_counterexample
  exact hne (h (G := G) (μ := μ) (ν := ν) (U := U) (f := f)
    hD hmeas hcont hpos hdens k hk κ hκ ρ hρ hρc)

end RiemannMasullo
