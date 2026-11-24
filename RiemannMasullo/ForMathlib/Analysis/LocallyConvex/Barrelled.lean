module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integration of pointwise bounded families on a barrelled space -/

@[expose] public noncomputable section

open Filter Set Topology

namespace RiemannMasullo

/-- On an open set, every derivative of a pointwise holomorphic family of continuous
linear forms on a barrelled space is again a continuous linear form. -/
theorem exists_continuousLinearMap_iteratedDeriv_of_analytic
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    (heval : ∀ y ∈ U, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f y) (n : ℕ) :
    ∀ y ∈ U, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) y := by
  classical
  have analyticDeriv (f : E) {x : ℂ} (hx : x ∈ U) (n : ℕ) : AnalyticAt ℂ (iteratedDeriv n (Φ f)) x := by
    induction n with
    | zero => simpa only [iteratedDeriv_zero] using hΦ f x hx
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  induction n with
  | zero => exact fun y hy ↦ by simp only [iteratedDeriv_zero]; exact heval y hy
  | succ n ih =>
    intro x hx
    let A (y : ℂ) : E →L[ℂ] ℂ := if hy : y ∈ U then (ih y hy).choose else 0
    have hA {y : ℂ} (hy : y ∈ U) (f : E) : A y f = iteratedDeriv n (Φ f) y := by
      simpa only [A, dite_eq_left hy] using (ih y hy).choose_spec f
    let D (y : ℂ) := (y - x)⁻¹ • (A y - A x)
    have hlim : Tendsto (fun y f ↦ D y f) (𝓝[≠] x) (𝓝 fun f ↦ iteratedDeriv (n + 1) (Φ f) x) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      have hd := analyticDeriv f hx n
      rw [iteratedDeriv_succ]
      refine hd.differentiableAt.hasDerivAt.tendsto_slope.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)] with y hy
      simp only [D, smul_apply, sub_apply, hA hy, hA hx, slope, vsub_eq_sub]
    exact ⟨continuousLinearMapOfTendsto D hlim, fun _ ↦ rfl⟩

/-- A pointwise holomorphic family of functionals on a barrelled space consists of continuous
linear functionals throughout a connected open set if it does so in a neighborhood of one point. -/
theorem exists_continuousLinearMap_of_analytic_continuation
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (Φ : E → ℂ → ℂ) {U : Set ℂ}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hΦ : ∀ f, AnalyticOnNhd ℂ (Φ f) U)
    {b : ℂ} (hb : b ∈ U) (hbase : ∀ᶠ z in 𝓝 b, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z)
    {z : ℂ} (hz : z ∈ U) : ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z := by
  classical
  let P := {z : ℂ | ∃ L : E →L[ℂ] ℂ, ∀ f, L f = Φ f z}
  let V := interior P ∩ U
  have hV : IsOpen V := isOpen_interior.inter hU
  have hcoeff (n : ℕ) : ∀ y ∈ V, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = iteratedDeriv n (Φ f) y :=
    exists_continuousLinearMap_iteratedDeriv_of_analytic Φ hV (fun f y hy ↦ hΦ f y hy.2)
      (fun _ hy ↦ interior_subset hy.1) n
  -- The Taylor series propagates continuity across every ball contained in the domain.
  have hball (y : ℂ) (hy : y ∈ V) {r : ℝ} (hr : Metric.ball y r ⊆ U) : Metric.ball y r ⊆ P := by
    choose A hA using fun n ↦ hcoeff n y hy
    intro x hx
    let T (s : Finset ℕ) : E →L[ℂ] ℂ := ∑ n ∈ s, (n.factorial : ℂ)⁻¹ • (x - y) ^ n • A n
    have hlim : Tendsto (fun s f ↦ T s f) atTop (𝓝 fun f ↦ Φ f x) := by
      refine tendsto_pi_nhds.mpr fun f ↦ ?_
      have h := Complex.hasSum_taylorSeries_on_ball ((hΦ f).differentiableOn.mono hr) hx
      simp only [T, sum_apply, smul_apply, hA]
      exact h
    exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩
  apply interior_subset (s := P)
  suffices h : U ⊆ V from (h hz).1
  refine hconn.subset_of_closure_inter_subset hV ⟨b, hb, mem_interior_iff_mem_nhds.mpr hbase, hb⟩ ?_
  rintro x ⟨hx, hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (r / 2) (half_pos hr)
  have hballU : Metric.ball y (r / 2) ⊆ U := (Metric.ball_subset_ball' (by
    rw [dist_comm y x]; linarith : r / 2 + dist y x ≤ r)).trans hsub
  exact ⟨interior_maximal (hball y hy hballU) Metric.isOpen_ball hxy, hxU⟩

/-- For linear maps from a barrelled space into continuous functions with the compact-open
topology, continuity of all point evaluations implies continuity of the map. -/
theorem continuous_of_continuous_eval_barrelled
    {E X : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] [TopologicalSpace X] (T : E → C(X, ℂ))
    (heval : ∀ x, ∃ L : E →L[ℂ] ℂ, ∀ f, L f = T f x) : Continuous T := by
  choose L hL using heval
  refine continuous_iff_continuousAt.mpr fun f ↦ ?_
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let A (x : K) := L x.val
  have hbound (g : E) : Bornology.IsVonNBounded ℂ (range fun x : K ↦ A x g) := by
    have hc : Continuous (fun x : K ↦ T g x.val) := (T g).continuous.comp continuous_subtype_val
    simpa only [A, hL] using (isCompact_range hc).isVonNBounded ℂ
  have he := (PolynormableSpace.banach_steinhaus hbound).equicontinuous f
  intro u hu
  filter_upwards [he u hu] with g hg
  intro x hx
  simpa only [Function.comp_apply, A, hL] using hg (⟨x, hx⟩ : K)

end RiemannMasullo

public section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace RiemannMasullo

/-- Integrating a pointwise bounded family of continuous linear forms against a
continuous weight gives a continuous linear form whenever each integral converges.
On compact subsets the supremum of the evaluation seminorms bounds the integral.
Banach–Steinhaus then gives continuity of the limit along a compact exhaustion. -/
theorem exists_continuousLinearMap_integral_mul {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (v : X → E →ₗ[ℂ] ℂ)
    (hv : ∀ x, Continuous (fun e ↦ ‖v x e‖)) (hb : ∀ e, ∃ B : ℝ, ∀ x, ‖v x e‖ ≤ B)
    (w : X → ℂ) (hw : Continuous w) (hi : ∀ e, Integrable (fun x ↦ v x e * w x) μ) :
    ∃ Z : E →L[ℂ] ℂ, ∀ e, Z e = ∫ x, v x e * w x ∂μ := by
  let q (x : X) := (normSeminorm ℂ ℂ).comp (v x)
  have hq : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun e ↦ by
    obtain ⟨B, hB⟩ := hb e
    exact ⟨B, forall_mem_range.mpr hB⟩
  let p : Seminorm ℂ E := ⨆ x, q x
  have hp : Continuous p := by
    rw [show (p : E → ℝ) = ⨆ x, (q x : E → ℝ) from Seminorm.coe_iSup_eq hq]
    exact Seminorm.continuous_iSup q hv hq
  have hle (e : E) (x : X) : ‖v x e‖ ≤ p e := (le_ciSup hq x : q x ≤ p) e
  let K := compactCovering X
  have hK (n : ℕ) : IsCompact (K n) := isCompact_compactCovering X n
  let L (n : ℕ) : E →ₗ[ℂ] ℂ :=
    { toFun := fun e ↦ ∫ x in K n, v x e * w x ∂μ
      map_add' := fun a b ↦ by
        simp_rw [map_add, add_mul]
        exact integral_add (hi a).integrableOn (hi b).integrableOn
      map_smul' := fun z e ↦ by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, integral_const_mul] }
  have hc (n : ℕ) : Continuous (L n) := by
    let B := ∫ x in K n, ‖w x‖ ∂μ
    let b : ℝ≥0 := ⟨B, integral_nonneg fun _ ↦ norm_nonneg _⟩
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp (L n)
    intro _
    apply Seminorm.continuous_of_le (q := b • p) (hp.const_smul b)
    intro e
    change ‖∫ x in K n, v x e * w x ∂μ‖ ≤ B * p e
    rw [mul_comm B, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
      (hi e).norm.integrableOn ((hw.norm.continuousOn.integrableOn_compact (hK n)).const_mul _)
      (hK n).measurableSet fun x _ ↦ ?_)
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hle e x) (norm_nonneg _))
  let T (n : ℕ) : E →L[ℂ] ℂ := ⟨L n, hc n⟩
  have hlim : Tendsto (fun n e ↦ T n e) atTop (𝓝 (fun e ↦ ∫ x, v x e * w x ∂μ)) := by
    apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun n ↦ ∫ x in K n, v x e * w x ∂μ) atTop (𝓝 _)
    simpa only [K, iUnion_compactCovering, setIntegral_univ] using
      (tendsto_setIntegral_of_monotone (fun n ↦ (hK n).measurableSet)
        (fun _ _ h ↦ compactCovering_subset X h) (hi e).integrableOn)
  exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩

end RiemannMasullo
