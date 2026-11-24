module

public import Mathlib.Analysis.Distribution.Support
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Finite-order distributions on a coordinate plane

A compactly supported distribution supported on the plane is bounded by the restrictions
of the coordinate derivatives through its order. Hahn–Banach then represents it by
compactly supported order-zero functionals on the individual traces.

For the estimate, first cut off in a shrinking tube to annihilate functions flat to the
required order. To handle nonzero traces, extend a tangential function `g` by averaging
`g (y + L x)` over linear maps `L` with a smooth compactly supported density. Integration
by parts in `L` trades a normal linear factor for one derivative. After subtracting this
extension, integration along the normal ray factors the remainder through the normal
coordinates. Induction gives the estimate all the way down to the flat remainder. -/

noncomputable section

open Filter Function Set TopologicalSpace Topology
open scoped BoundedContinuousFunction Distributions ContDiff BigOperators

namespace RiemannMasullo

open scoped Manifold in
/-- A finite partition of unity splits a test supported off the distributional support
into tests on which the distribution vanishes. -/
public theorem testFunction_vanishes_off_dsupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : StrongDual ℂ 𝓓((⊤ : Opens E), ℂ)) (f : 𝓓((⊤ : Opens E), ℂ))
    (hf : ∀ x ∈ tsupport (f : E → ℂ), x ∉ Distribution.dsupport (⇑A)) : A f = 0 := by
  classical
  let K := tsupport (f : E → ℂ)
  choose U hv ho hm using fun x : K ↦ (Distribution.notMem_dsupport_iff x.val).mp (hf x.val x.2)
  obtain ⟨s, hs⟩ := f.hasCompactSupport.elim_finite_subcover U ho
    fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hm _⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E)
    (isClosed_tsupport (f : E → ℂ)) (fun i : s ↦ U i.val) (fun i ↦ ho i.val)
    (by simpa only [iUnion_subtype] using hs)
  let g (i : s) : 𝓓((⊤ : Opens E), ℂ) :=
    ⟨fun x ↦ ρ i x • f x, (contMDiff_iff_contDiff.mp (ρ i).contMDiff).smul f.contDiff,
      f.hasCompactSupport.smul_left (f := (ρ i : E → ℝ)), fun _ _ ↦ trivial⟩
  have hz (i : s) : A (g i) = 0 :=
    hv i.val (g i) ((tsupport_smul_subset_left _ _).trans (hρ i))
  have he : f = ∑ i : s, g i := by
    ext x
    let ev : 𝓓((⊤ : Opens E), ℂ) →+ ℂ :=
      { toFun := fun h ↦ h x, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    change f x = ev (∑ i : s, g i)
    rw [map_sum]
    change f x = ∑ i : s, ρ i x • f x
    rw [← Finset.sum_smul]
    by_cases h : x ∈ K
    · rw [← finsum_eq_sum_of_fintype, ρ.sum_eq_one h, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport h, smul_zero]
  rw [he, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hz i

namespace CoordinatePlane

set_option quotPrecheck false

local notation "orderBound(" T ", " E ", " n ")" =>
  ∀ K : Compacts E, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (f : 𝓓((⊤ : Opens E), ℂ)), tsupport (f : E → ℂ) ⊆ (K : Set E) →
      ∀ B : ℝ, 0 ≤ B → (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (f : E → ℂ) x‖ ≤ B) →
        ‖T f‖ ≤ C * B

/-- Factor through the range of the trace map, then extend by complex Hahn–Banach. -/
private theorem exists_factor_of_trace_bound {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (J : X →ₗ[ℂ] Y) (T : X →ₗ[ℂ] ℂ)
    (C : ℝ) (h : ∀ x, ‖T x‖ ≤ C * ‖J x‖) :
    ∃ L : Y →L[ℂ] ℂ, ∀ x, L (J x) = T x := by
  obtain ⟨s, hs⟩ := J.rangeRestrict.exists_rightInverse_of_surjective J.range_rangeRestrict
  have he (y : J.range) : J (s y) = y := congrArg Subtype.val (LinearMap.congr_fun hs y)
  let l : J.range →L[ℂ] ℂ := (T.comp s).mkContinuous C fun y ↦ (h (s y)).trans_eq (by rw [he]; rfl)
  obtain ⟨L, hL, -⟩ := exists_extension_norm_eq J.range l
  refine ⟨L, fun x ↦ ?_⟩
  have hk := h (s (J.rangeRestrict x) - x)
  rw [map_sub J, he, show (J.rangeRestrict x).val = J x from rfl, sub_self, norm_zero, mul_zero,
    norm_le_zero_iff, map_sub, sub_eq_zero] at hk
  exact (hL (J.rangeRestrict x)).trans hk

/-- Recover the coordinate functionals from a bounded functional on a finite product. -/
private theorem distribution_of_compact_trace_bound {E X I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup X] [Module ℂ X] [Fintype I]
    (K : Compacts E) (J : I → X →ₗ[ℂ] 𝓓((⊤ : Opens E), ℂ)) (T : X →ₗ[ℂ] ℂ)
    (C : ℝ) (h : ∀ x B, 0 ≤ B → (∀ i (y : K), ‖J i x y.val‖ ≤ B) → ‖T x‖ ≤ C * B) :
    ∃ A : I → StrongDual ℂ 𝓓((⊤ : Opens E), ℂ),
      (∀ i, (orderBound(A i, E, 0)) ∧ Distribution.dsupport (⇑(A i)) ⊆ K) ∧
      ∀ x, T x = ∑ i, A i (J i x) := by
  classical
  let evalK := (BoundedContinuousFunction.compContinuousCLM ℂ ℂ (⟨Subtype.val, continuous_subtype_val⟩ : C(K, E))).comp
    (TestFunction.toBoundedContinuousFunctionCLM ℂ : 𝓓((⊤ : Opens E), ℂ) →L[ℂ] E →ᵇ ℂ)
  let R : X →ₗ[ℂ] (I → K →ᵇ ℂ) := LinearMap.pi fun i ↦ evalK.toLinearMap.comp (J i)
  have hR (x : X) : ‖T x‖ ≤ C * ‖R x‖ := h x _ (norm_nonneg _) fun i y ↦
    ((R x i).norm_coe_le_norm y).trans (norm_le_pi_norm _ i)
  obtain ⟨L, hL⟩ := exists_factor_of_trace_bound R T C hR
  let A (i : I) := L.comp ((ContinuousLinearMap.single ℂ (fun _ : I ↦ K →ᵇ ℂ) i).comp evalK)
  refine ⟨A, fun i ↦ ⟨?_, ?_⟩, fun x ↦ ?_⟩
  · intro K'
    refine ⟨‖L.comp (ContinuousLinearMap.single ℂ (fun _ : I ↦ K →ᵇ ℂ) i)‖, norm_nonneg _, fun f _ B hB hf ↦ ?_⟩
    apply ((L.comp (ContinuousLinearMap.single ℂ (fun _ : I ↦ K →ᵇ ℂ) i)).le_opNorm (evalK f)).trans
    gcongr
    apply (BoundedContinuousFunction.norm_le hB).mpr
    intro y
    change ‖f y.val‖ ≤ B
    simpa only [norm_iteratedFDeriv_zero] using hf 0 le_rfl y.val
  · intro x hx
    by_contra hn
    apply (Distribution.notMem_dsupport_iff x).mpr ⟨(K : Set E)ᶜ, ?_, K.isCompact.isClosed.isOpen_compl, hn⟩ hx
    intro f hf
    have hz : evalK f = 0 := by
      ext y
      change f y.val = 0
      exact image_eq_zero_of_notMem_tsupport fun hy ↦ hf hy y.property
    change L ((ContinuousLinearMap.single ℂ (fun _ : I ↦ K →ᵇ ℂ) i) (evalK f)) = 0
    rw [hz, map_zero, map_zero]
  · rw [← hL]
    change L (R x) = ∑ i, L (Pi.single i (R x i))
    rw [← map_sum, Finset.univ_sum_single]

section FlatSupport

open scoped SchwartzMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Iterating the mean-value bound gives one power of the distance per vanishing derivative. -/
private theorem flat_jet_bound (f : 𝓢(X, ℂ)) (p : X) (ε : ℝ) (hε : 0 ≤ ε)
    (j d : ℕ) (hjet : ∀ i < d, iteratedFDeriv ℝ (j + i) (f : X → ℂ) p = 0)
    (x : X) (hx : ‖x - p‖ ≤ ε) :
    ‖iteratedFDeriv ℝ j (f : X → ℂ) x‖ ≤ ε ^ d * SchwartzMap.seminorm ℂ 0 (j + d) f := by
  induction d generalizing j x with
  | zero => simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f j x
  | succ d ih =>
    let K := Metric.closedBall p ε
    have hz : iteratedFDeriv ℝ j (f : X → ℂ) p = 0 := by simpa using hjet 0 d.succ_pos
    have hstep (y : X) (hy : y ∈ K) :
        ‖fderiv ℝ (iteratedFDeriv ℝ j (f : X → ℂ)) y‖ ≤
          ε ^ d * SchwartzMap.seminorm ℂ 0 (j + (d + 1)) f := by
      rw [norm_fderiv_iteratedFDeriv]
      simpa only [Nat.succ_add, Nat.add_succ] using ih (j + 1)
        (fun i hi ↦ by rw [show j + 1 + i = j + (i + 1) by omega]; exact hjet _ (Nat.succ_lt_succ hi))
        y (by simpa only [K, Metric.mem_closedBall, dist_eq_norm] using hy)
    have hd := (convex_closedBall p ε).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ ↦ ((f.smooth (j + 1 : ℕ)).differentiable_iteratedFDeriv
        (by exact_mod_cast Nat.lt_succ_self j)).differentiableAt)
      hstep (Metric.mem_closedBall_self hε) (show x ∈ K by simpa [K, dist_eq_norm] using hx)
    rw [hz, sub_zero] at hd
    calc _ ≤ _ := hd
         _ ≤ (ε ^ d * SchwartzMap.seminorm ℂ 0 (j + (d + 1)) f) * ε :=
           mul_le_mul_of_nonneg_left hx (mul_nonneg (pow_nonneg hε _) (apply_nonneg _ _))
         _ = _ := by rw [pow_succ]; ring

/-- In the tube, Taylor bounds for the test offset the inverse powers from the cutoff. -/
private theorem trace_normal_cutoff_bound (b : 𝓢(X, ℝ)) (f : 𝓢(X, ℂ))
    (hb : tsupport (b : X → ℝ) ⊆ Metric.closedBall 0 1)
    (P : X →L[ℝ] X) (N m : ℕ) (hm : m ≤ N)
    (hjet : ∀ (p : X) j, j ≤ N → iteratedFDeriv ℝ j (f : X → ℂ) (P p) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ m (fun y ↦ b (ε⁻¹ • (y - P y)) • f y) x‖ ≤ ε * C := by
  let L := ContinuousLinearMap.id ℝ X - P
  let A := SchwartzMap.seminorm ℂ 0 (N + 1) f
  let B (i : ℕ) := SchwartzMap.seminorm ℝ 0 i b * ‖L‖ ^ i
  have hA : 0 ≤ A := apply_nonneg _ _
  have hB (i : ℕ) : 0 ≤ B i := mul_nonneg (apply_nonneg _ _) (pow_nonneg (norm_nonneg _) _)
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B i * A, by positivity, ?_⟩
  intro ε hε hε1 x
  let S := ε⁻¹ • L
  let bε := (b : X → ℝ) ∘ S
  change ‖iteratedFDeriv ℝ m (fun y ↦ bε y • f y) x‖ ≤ _
  by_cases hx : ‖x - P x‖ ≤ ε
  · have hprod := norm_iteratedFDeriv_smul_le ((b.smooth m).comp S.contDiff) (f.smooth m) x
        (show (m : ℕ∞ω) ≤ m from le_rfl)
    apply hprod.trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have him := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    let j := m - i
    let d := N + 1 - j
    have hjd : j + d = N + 1 := by dsimp [j, d]; omega
    have hdi : i < d := by dsimp [d, j]; omega
    have hf : ‖iteratedFDeriv ℝ j (f : X → ℂ) x‖ ≤ ε ^ d * A := by
      simpa only [hjd, A] using flat_jet_bound f (P x) ε hε.le j d
        (fun k hk ↦ hjet x _ (by omega)) x hx
    have hbnd : ‖iteratedFDeriv ℝ i bε x‖ ≤ ε⁻¹ ^ i * B i := by
      rw [show bε = (b : X → ℝ) ∘ S from rfl, S.iteratedFDeriv_comp_right (b.smooth i) x le_rfl]
      apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hS : ‖S‖ = ε⁻¹ * ‖L‖ := by simp only [S, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
      rw [hS, mul_pow]
      calc _ ≤ SchwartzMap.seminorm ℝ 0 i b * (ε⁻¹ ^ i * ‖L‖ ^ i) := by
                 gcongr; exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ b i _
           _ = _ := by dsimp [B]; ring
    have hp : ε⁻¹ ^ i * ε ^ d ≤ ε := by
      rw [← pow_sub_mul_pow ε hdi.le, mul_left_comm, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, mul_one]
      simpa using pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ d - i by omega)
    calc _ ≤ ((m.choose i : ℝ) * (ε⁻¹ ^ i * B i)) * (ε ^ d * A) := by gcongr
         _ = (ε⁻¹ ^ i * ε ^ d) * ((m.choose i : ℝ) * B i * A) := by ring
         _ ≤ _ := by gcongr
  · have hout : S x ∉ tsupport (b : X → ℝ) := by
      intro h
      have hh := hb h
      change ε⁻¹ • (x - P x) ∈ Metric.closedBall (0 : X) 1 at hh
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le),
        inv_mul_le_iff₀ hε, mul_one] at hh
      exact hx hh
    have heq : (fun y ↦ bε y • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [S.continuous.continuousAt (notMem_tsupport_iff_eventuallyEq.mp hout)] with y hy
      change b (S y) • f y = 0
      rw [show b (S y) = 0 from hy, zero_smul]
    have hz : iteratedFDeriv ℝ m (fun y ↦ bε y • f y) x = 0 :=
      by_contra fun hn ↦ (notMem_tsupport_iff_eventuallyEq.mpr heq) (support_iteratedFDeriv_subset m hn)
    rw [hz, norm_zero]
    positivity

private def tubeCutoff [FiniteDimensional ℝ X] (χ : ContDiffBump (0 : X)) (S : X →L[ℝ] X)
    (f : 𝓓((⊤ : Opens X), ℂ)) : 𝓓((⊤ : Opens X), ℂ) :=
  ⟨fun y ↦ χ (S y) • f y, (χ.contDiff.comp S.contDiff).smul f.contDiff,
    f.hasCompactSupport.smul_left (f := fun y ↦ χ (S y)), fun _ _ ↦ trivial⟩

private theorem trace_vanishes_of_flat_plane [FiniteDimensional ℝ X]
    (T : StrongDual ℂ 𝓓((⊤ : Opens X), ℂ)) (N : ℕ) (hN : orderBound(T, X, N))
    (P : X →L[ℝ] X) (hP : ∀ x ∈ Distribution.dsupport (⇑T), P x = x)
    (f : 𝓓((⊤ : Opens X), ℂ))
    (hjet : ∀ (p : X) j, j ≤ N → iteratedFDeriv ℝ j (f : X → ℂ) (P p) = 0) : T f = 0 := by
  let χ : ContDiffBump (0 : X) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let b := χ.hasCompactSupport.toSchwartzMap χ.contDiff
  have hb : tsupport (b : X → ℝ) ⊆ Metric.closedBall 0 1 := by
    change tsupport (χ : X → ℝ) ⊆ _
    rw [χ.tsupport_eq]
  let F := f.hasCompactSupport.toSchwartzMap f.contDiff
  obtain ⟨C, hC, h⟩ := hN ⟨_, f.hasCompactSupport⟩
  choose D hD hD' using fun j : Fin (N + 1) ↦
    trace_normal_cutoff_bound b F hb P N j (Nat.le_of_lt_succ j.isLt) hjet
  let M := ∑ j, D j
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ ↦ hD i)
  suffices hz : ‖T f‖ ≤ 0 by exact norm_le_zero_iff.mp hz
  have bound (ε : ℝ) (he : 0 < ε) (he1 : ε ≤ 1) : ‖T f‖ ≤ C * (ε * M) := by
    let S := ε⁻¹ • (ContinuousLinearMap.id ℝ X - P)
    let g := tubeCutoff χ S f
    have heq : T f = T g := by
      rw [← sub_eq_zero, ← map_sub]
      apply testFunction_vanishes_off_dsupport
      intro x hx hx'
      apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
      have hS : S x = 0 := by change ε⁻¹ • (x - P x) = 0; rw [hP x hx', sub_self, smul_zero]
      have hb : (χ : X → ℝ) =ᶠ[𝓝 (S x)] 1 := by rw [hS]; exact χ.eventuallyEq_one
      have he := S.continuous.continuousAt.eventually hb
      filter_upwards [he] with y hy
      change f y - χ (S y) • f y = 0
      rw [show χ (S y) = 1 from hy, one_smul, sub_self]
    rw [heq]
    apply h g (tsupport_smul_subset_right _ _) _ (mul_nonneg he.le hM)
    intro j hj x
    let i : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have hle : D i ≤ M := Finset.single_le_sum (fun k _ ↦ hD k) (Finset.mem_univ i)
    exact (hD' i ε he he1 x).trans (mul_le_mul_of_nonneg_left hle he.le)
  have ht : Tendsto (fun ε : ℝ ↦ C * (ε * M)) (𝓝[>] 0) (𝓝 (C * (0 * M))) :=
    (continuous_const.mul (continuous_id.mul continuous_const)).continuousAt.mono_left nhdsWithin_le_nhds
  simpa using le_of_tendsto_of_tendsto (tendsto_const_nhds (x := ‖T f‖)) ht
    (show ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖T f‖ ≤ C * (ε * M) from by
      filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)),
        mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with ε hε hε1
      exact bound ε hε hε1)

end FlatSupport

section RegularFamilies

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every compact set has a common bound for the entire family. -/
private def boundedOnCompacts (F : I → X → ℂ) :=
  ∀ K : Compacts X, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ K → ‖F i x‖ ≤ C

private def directional (v : X) (f : X → ℂ) (x : X) := fderiv ℝ f x v

/-- Local uniform bounds for each fixed directional derivative through order `n`. -/
private def boundedDerivs (F : I → X → ℂ) : ℕ → Prop
  | 0 => boundedOnCompacts F
  | n + 1 => boundedOnCompacts F ∧ ∀ v : X, boundedDerivs (fun i ↦ directional v (F i)) n

private theorem directional_smooth {f : X → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : X) :
    ContDiff ℝ (⊤ : ℕ∞) (directional v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem boundedDerivs_loc {F : I → X → ℂ} {n : ℕ} (h : boundedDerivs F n) : boundedOnCompacts F := by
  cases n with
  | zero => exact h
  | succ n => exact h.1

private theorem boundedDerivs_mono {F : I → X → ℂ} {n m : ℕ} (h : boundedDerivs F n) (hm : m ≤ n) : boundedDerivs F m := by
  induction m generalizing n F with
  | zero => exact boundedDerivs_loc h
  | succ m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨h.1, fun v ↦ ih (h.2 v) (by omega)⟩

private theorem boundedOnCompacts_add {F G : I → X → ℂ} (f : boundedOnCompacts F) (g : boundedOnCompacts G) :
    boundedOnCompacts (fun i x ↦ F i x + G i x) := by
  intro K
  obtain ⟨A, hA, a⟩ := f K
  obtain ⟨B, hB, b⟩ := g K
  exact ⟨_, add_nonneg hA hB, fun i x hx ↦ (norm_add_le _ _).trans (add_le_add (a i x hx) (b i x hx))⟩

private theorem boundedOnCompacts_mul_fixed {F : I → X → ℂ} (f : boundedOnCompacts F) (c : X → ℝ) (hc : Continuous c) :
    boundedOnCompacts (fun i x ↦ c x • F i x) := by
  intro K
  obtain ⟨A, hA, a⟩ := f K
  obtain ⟨B, b⟩ := K.isCompact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max B 0 * A, by positivity, fun i x hx ↦ ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((b _ hx).trans (le_max_left _ _)) (a i x hx) (norm_nonneg _) (le_max_right _ _)

private theorem boundedDerivs_zero (n : ℕ) : boundedDerivs (fun (_ : I) (_ : X) ↦ (0 : ℂ)) n := by
  have hz : boundedOnCompacts (fun (_ : I) (_ : X) ↦ (0 : ℂ)) := fun K ↦ ⟨0, le_rfl, by simp⟩
  induction n with
  | zero => exact hz
  | succ n ih =>
    refine ⟨hz, fun v ↦ ?_⟩
    have he : directional v (fun _ : X ↦ (0 : ℂ)) = 0 := funext fun x ↦ by simp [directional]
    change boundedDerivs (fun _ : I ↦ directional v (fun _ : X ↦ (0 : ℂ))) n
    rw [he]
    exact ih

private theorem boundedDerivs_add {F G : I → X → ℂ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i))
    (n : ℕ) (hF : boundedDerivs F n) (hG : boundedDerivs G n) : boundedDerivs (fun i x ↦ F i x + G i x) n := by
  induction n generalizing F G with
  | zero => exact boundedOnCompacts_add hF hG
  | succ n ih =>
    refine ⟨boundedOnCompacts_add hF.1 hG.1, fun v ↦ ?_⟩
    have eqn (i : I) : directional v (fun x ↦ F i x + G i x) = fun x ↦ directional v (F i) x + directional v (G i) x := by
      funext x; simp only [directional, fderiv_fun_add ((hf i).differentiable (by simp)).differentiableAt
        ((hg i).differentiable (by simp)).differentiableAt, add_apply]
    simp only [eqn]
    exact ih (fun i ↦ directional_smooth (hf i) v) (fun i ↦ directional_smooth (hg i) v) (hF.2 v) (hG.2 v)

private theorem boundedDerivs_fixed_smul {F : I → X → ℂ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (c : X → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (n : ℕ) (hF : boundedDerivs F n) :
    boundedDerivs (fun i x ↦ c x • F i x) n := by
  induction n generalizing F c with
  | zero => exact boundedOnCompacts_mul_fixed hF c hc.continuous
  | succ n ih =>
    refine ⟨boundedOnCompacts_mul_fixed hF.1 c hc.continuous, fun v ↦ ?_⟩
    let c' x := fderiv ℝ c x v
    have hc' : ContDiff ℝ (⊤ : ℕ∞) c' := (hc.fderiv_right (by simp)).clm_apply contDiff_const
    have eqn (i : I) : directional v (fun x ↦ c x • F i x) = fun x ↦ c x • directional v (F i) x + c' x • F i x := by
      funext x
      exact congrArg (fun L : X →L[ℝ] ℂ ↦ L v) (((hc.differentiable (by simp)).differentiableAt.hasFDerivAt.smul
        ((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv)
    simp only [eqn]
    exact boundedDerivs_add (fun i ↦ hc.smul (directional_smooth (hf i) v)) (fun i ↦ hc'.smul (hf i)) _
      (ih (fun i ↦ directional_smooth (hf i) v) c hc (hF.2 v)) (ih hf c' hc' (boundedDerivs_mono hF n.le_succ))

private theorem boundedDerivs_finsum {α : Type*} (s : Finset α) (F : α → I → X → ℂ) (n : ℕ)
    (hf : ∀ a, ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F a i)) (h : ∀ a, boundedDerivs (F a) n) :
    boundedDerivs (fun i x ↦ ∑ a ∈ s, F a i x) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using boundedDerivs_zero (I := I) (X := X) n
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact boundedDerivs_add (hf a) (fun i ↦ ContDiff.sum fun a _ ↦ hf a i) n (h a) ih

private theorem boundedDerivs_iterated_eval {F : I → X → ℂ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (n : ℕ)
    (h : boundedDerivs F n) (v : Fin n → X) :
    boundedOnCompacts (fun i x ↦ iteratedFDeriv ℝ n (F i) x v) := by
  induction n generalizing F with
  | zero => exact h
  | succ n ih =>
    have hev (i : I) (x : X) : iteratedFDeriv ℝ (n + 1) (F i) x v =
        iteratedFDeriv ℝ n (directional (v (Fin.last n)) (F i)) x (Fin.init v) := by
      rw [iteratedFDeriv_succ_apply_right]
      let L := ContinuousLinearMap.apply ℝ ℂ (v (Fin.last n))
      have he : directional (v (Fin.last n)) (F i) = L ∘ fderiv ℝ (F i) := rfl
      have hh : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (F i)) := (hf i).fderiv_right (by simp)
      rw [he, L.iteratedFDeriv_comp_left hh.contDiffAt (show (n : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)]
      rfl
    simp only [hev]
    exact ih (fun i ↦ directional_smooth (hf i) _) (h.2 _) _

/-- Evaluate on tuples of basis vectors to bound the norm of the full multilinear derivative. -/
private theorem boundedDerivs_iterated_norm [FiniteDimensional ℝ X] {F : I → X → ℂ}
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (n : ℕ) (h : boundedDerivs F n) (K : Compacts X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ K → ‖iteratedFDeriv ℝ n (F i) x‖ ≤ C := by
  classical
  let b := Module.finBasis ℝ X
  let α := Fin n → Fin (Module.finrank ℝ X)
  let L : (X [×n]→L[ℝ] ℂ) →ₗ[ℝ] (α → ℂ) :=
    { toFun := fun f s ↦ f (fun j ↦ b (s j))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hinj : Function.Injective L := by
    intro f g he
    have eqn : f.toMultilinearMap = g.toMultilinearMap :=
      Module.Basis.ext_multilinear (fun _ : Fin n ↦ b) fun s ↦ congrFun he s
    exact ContinuousMultilinearMap.toMultilinearMap_injective eqn
  let R := (LinearEquiv.ofInjective L hinj).symm.toLinearMap.toContinuousLinearMap
  choose C hC hC' using fun s : α ↦ boundedDerivs_iterated_eval hf n h (fun j ↦ b (s j)) K
  let B := ∑ s, C s
  have hB : 0 ≤ B := Finset.sum_nonneg fun s _ ↦ hC s
  refine ⟨‖R‖ * B, mul_nonneg (norm_nonneg _) hB, fun i x hx ↦ ?_⟩
  let f := iteratedFDeriv ℝ n (F i) x
  calc ‖f‖ = ‖R (L.rangeRestrict f)‖ := congrArg norm ((LinearEquiv.ofInjective L hinj).symm_apply_apply f).symm
       _ ≤ ‖R‖ * ‖L.rangeRestrict f‖ := R.le_opNorm _
       _ ≤ _ := mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg hB).2 fun s ↦
         (hC' s i x hx).trans (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ s))) (norm_nonneg _)

end RegularFamilies

section TraceAveraging
open MeasureTheory

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "M" => X →L[ℝ] Y

variable [MeasurableSpace (X →L[ℝ] Y)]

/-- Extend a tangential function off the plane by averaging along linear shears. -/
private def shearAverage (μ : Measure M) (ψ : M → ℝ) (g : Y → ℂ) (z : X × Y) :=
  ∫ L, ψ L • g (z.2 + L z.1) ∂μ

variable [BorelSpace (X →L[ℝ] Y)] (μ : Measure (X →L[ℝ] Y))
    [IsFiniteMeasureOnCompacts μ]

private theorem shearAverage_smooth (ψ : M → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hK : HasCompactSupport ψ) (g : Y → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (shearAverage μ ψ g) := by
  let K := tsupport ψ
  let F (z : X × Y) (L : M) := ψ L • g (z.2 + L z.1)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F.uncurry := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun v : (X × Y) × M ↦ ψ v.2 • g (v.1.2 + v.2 v.1.1))
    fun_prop
  have he : shearAverage μ ψ g = fun z ↦ ∫ L in K, F z L ∂μ := by
    funext z
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun L h ↦
      by simp [image_eq_zero_of_notMem_tsupport h]).symm
  rw [he]
  exact hF.parametric_integral hK Subset.rfl hK.measure_ne_top

omit [IsFiniteMeasureOnCompacts μ] in
/-- The rank-one direction `c.smulRight v` differentiates the argument of `g` by `c x • v`. -/
private theorem shearAverage_integrationByParts [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [μ.IsAddHaarMeasure]
    (ψ : M → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hK : HasCompactSupport ψ)
    (g : Y → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : X →L[ℝ] ℝ) (v : Y) (z : X × Y) :
    c z.1 • shearAverage μ ψ (fun y ↦ fderiv ℝ g y v) z =
      -shearAverage μ (fun L ↦ fderiv ℝ ψ L (c.smulRight v)) g z := by
  let d : M := c.smulRight v
  let eval : M →L[ℝ] Y := ContinuousLinearMap.apply ℝ Y z.1
  let h (L : M) := g (z.2 + L z.1)
  have hs (L : M) : HasFDerivAt h ((fderiv ℝ g (z.2 + L z.1)).comp eval) L :=
    ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp L
      (eval.hasFDerivAt.const_add z.2)
  have hhd (L : M) : fderiv ℝ h L d = c z.1 • fderiv ℝ g (z.2 + L z.1) v := by
    rw [(hs L).fderiv]; exact (fderiv ℝ g (z.2 + L z.1)).map_smul (c z.1) v
  have dh : ContDiff ℝ (⊤ : ℕ∞) h := hg.comp (contDiff_const.add eval.contDiff)
  have cont (f : M → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
      (u : M → ℂ) (hu : Continuous u) : Integrable (fun x ↦ f x • u x) μ :=
    (hf.smul hu).integrable_of_hasCompactSupport (hc.smul_right (f' := u))
  have hi := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ) (𝕜 := ℝ)
    (f := ψ) (g := h) (v := d)
    (cont _ ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hK.fderiv_apply ℝ d) _ dh.continuous)
    (cont ψ hψ.continuous hK _ ((dh.continuous_fderiv (by simp)).clm_apply continuous_const))
    (cont ψ hψ.continuous hK _ dh.continuous)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (dh.differentiable (by simp)).differentiableAt)
  refine Eq.trans ?_ hi
  rw [shearAverage, ← integral_smul]
  exact integral_congr_ae (ae_of_all μ fun L ↦ by
    change c z.1 • ψ L • _ = ψ L • fderiv ℝ h L d
    rw [hhd, smul_comm])

variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

private def shearProjection (L : M) : X × Y →L[ℝ] Y :=
  ContinuousLinearMap.snd ℝ X Y + L.comp (ContinuousLinearMap.fst ℝ X Y)

private theorem shearAverage_deriv (ψ : M → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hK : HasCompactSupport ψ) (g : Y → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v z : X × Y) :
    fderiv ℝ (shearAverage μ ψ g) z v =
      ∫ L, ψ L • fderiv ℝ g (z.2 + L z.1) (v.2 + L v.1) ∂μ := by
  let K := tsupport ψ
  let F (w : X × Y) (L : M) := ψ L • g (shearProjection L w)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F.uncurry := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun w : (X × Y) × M ↦ ψ w.2 • g (w.1.2 + w.2 w.1.1))
    fun_prop
  have hes : shearAverage μ ψ g = fun w ↦ ∫ L in K, F w L ∂μ := by
    funext w
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun L h ↦
      by simp [image_eq_zero_of_notMem_tsupport h]).symm
  have dF (L : M) : HasFDerivAt (fun w ↦ F w L)
      (ψ L • (fderiv ℝ g (shearProjection L z)).comp (shearProjection L)) z :=
    (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
      (shearProjection L).hasFDerivAt).const_smul (ψ L)
  have diff := hasFDerivAt_integral_of_contDiffOn (μ := μ)
    (s := K) (x₀ := z) (f := F) univ_mem hK hK.measure_ne_top Subset.rfl
    (hF.of_le (by simp)).contDiffOn
  rw [hes, diff.fderiv, ContinuousLinearMap.integral_apply]
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
      (f := fun L : M ↦ ψ L • fderiv ℝ g (z.2 + L z.1) (v.2 + L v.1)) (μ := μ)
      (fun L h ↦ by simp [image_eq_zero_of_notMem_tsupport h])]
    exact setIntegral_congr_fun hK.measurableSet fun L _ ↦ by rw [(dF L).fderiv]; rfl
  · have cont : Continuous (fun L : M ↦ fderiv ℝ (F · L) z) := by
      have hj : Continuous (fun L : M ↦ ψ L • (fderiv ℝ g (z.2 + L z.1)).comp (shearProjection L)) := by
        have hproj : Continuous (fun L : M ↦ shearProjection L) := by
          unfold shearProjection
          fun_prop
        exact hψ.continuous.smul (((hg.continuous_fderiv (by simp)).comp
          (continuous_const.add (ContinuousLinearMap.apply ℝ Y z.1).continuous)).clm_comp hproj)
      exact hj.congr fun L ↦ (dF L).fderiv.symm
    exact cont.continuousOn.integrableOn_compact hK

end TraceAveraging

section TraceWeights
open MeasureTheory

variable {I X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
local notation "M" => X →L[ℝ] Y
local notation "W" => 𝓓((⊤ : Opens M), ℝ)
variable [MeasurableSpace (X →L[ℝ] Y)] [BorelSpace (X →L[ℝ] Y)] (μ : Measure (X →L[ℝ] Y)) [IsFiniteMeasureOnCompacts μ]

private def weightMul (ψ : W) (c : M → ℝ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) : W :=
  ⟨fun L ↦ ψ L * c L, ψ.contDiff.mul hc, ψ.hasCompactSupport.mul_right, fun _ _ ↦ trivial⟩

private def weightDerivative (ψ : W) (v : M) : W :=
  ⟨fun L ↦ fderiv ℝ (ψ : M → ℝ) L v, (ψ.contDiff.fderiv_right (by simp)).clm_apply contDiff_const,
   ψ.hasCompactSupport.fderiv_apply ℝ v, fun _ _ ↦ trivial⟩

private theorem shearAverage_loc {g : I → Y → ℂ}
    (h : boundedOnCompacts g) (ψ : W) : boundedOnCompacts (fun i ↦ shearAverage μ ψ (g i)) := by
  intro K
  let H : Compacts M := ⟨_, ψ.hasCompactSupport⟩
  let B : Compacts Y := ⟨_, (K.isCompact.prod H.isCompact).image
    (show Continuous (fun p : (X × Y) × M ↦ p.1.2 + p.2 p.1.1) by fun_prop)⟩
  obtain ⟨C, hC, hC'⟩ := h B
  refine ⟨(∫ L, ‖ψ L‖ ∂μ) * C, mul_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) hC, ?_⟩
  intro i z hz
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le ((ψ.contDiff.continuous.norm.integrable_of_hasCompactSupport
    ψ.hasCompactSupport.norm).mul_const C)
  filter_upwards with L
  rw [norm_smul]
  by_cases hL : L ∈ H
  · exact mul_le_mul_of_nonneg_left (hC' i _ ⟨(z, L), ⟨hz, hL⟩, rfl⟩) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hL, norm_zero, zero_mul, zero_mul]

private def shearCoordinateWeight (b : Module.Basis (Fin (Module.finrank ℝ Y)) ℝ Y) (j : Fin (Module.finrank ℝ Y))
    (v : X × Y) (ψ : W) : W :=
  weightMul ψ (fun L ↦ (b.coord j).toContinuousLinearMap (v.2 + L v.1)) (by fun_prop)

private theorem shearAverage_direction (b : Module.Basis (Fin (Module.finrank ℝ Y)) ℝ Y)
    (ψ : W) (g : Y → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v z : X × Y) :
    directional v (shearAverage μ ψ g) z =
      ∑ j, shearAverage μ (shearCoordinateWeight b j v ψ) (directional (b j) g) z := by
  classical
  rw [directional, shearAverage_deriv μ ψ ψ.contDiff ψ.hasCompactSupport g hg]
  unfold shearAverage
  rw [← integral_finsetSum]
  · apply integral_congr_ae (ae_of_all μ fun L ↦ ?_)
    let w := v.2 + L v.1
    calc ψ L • fderiv ℝ g (z.2 + L z.1) w =
        ψ L • fderiv ℝ g (z.2 + L z.1) (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
      _ = _ := by
        rw [map_sum, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]; exact (mul_smul _ _ _).symm
  · intro j _
    exact ((shearCoordinateWeight b j v ψ).contDiff.continuous.smul ((directional_smooth hg (b j)).continuous.comp
      (show Continuous (fun L : M ↦ z.2 + L z.1) by fun_prop))).integrable_of_hasCompactSupport
      (shearCoordinateWeight b j v ψ).hasCompactSupport.smul_right

private theorem shearAverage_boundedDerivs {g : I → Y → ℂ} (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i))
    (ψ : W) (k : ℕ) (h : boundedDerivs g k) : boundedDerivs (fun i ↦ shearAverage μ ψ (g i)) k := by
  induction k generalizing ψ g with
  | zero => exact shearAverage_loc μ h ψ
  | succ k ih =>
    let b := Module.finBasis ℝ Y
    refine ⟨shearAverage_loc μ h.1 ψ, fun v ↦ ?_⟩
    have eqn (i : I) : directional v (shearAverage μ ψ (g i)) =
        fun z ↦ ∑ j, shearAverage μ (shearCoordinateWeight b j v ψ) (directional (b j) (g i)) z :=
      funext (shearAverage_direction μ b ψ (g i) (hg i) v)
    simp only [eqn]
    exact boundedDerivs_finsum Finset.univ _ k (fun j i ↦ shearAverage_smooth μ _ (shearCoordinateWeight b j v ψ).contDiff
      (shearCoordinateWeight b j v ψ).hasCompactSupport _ (directional_smooth (hg i) _))
      (fun j ↦ ih (fun i ↦ directional_smooth (hg i) _) _ (h.2 (b j)))

private def normalMonomial (l : List (X →L[ℝ] ℝ)) (z : X × Y) : ℝ := (l.map fun c ↦ c z.1).prod

private theorem normalMonomial_cons (a : X →L[ℝ] ℝ) (l) (z : X × Y) :
    normalMonomial (a :: l) z = a z.1 * normalMonomial l z := rfl

private theorem normalMonomial_smooth (l : List (X →L[ℝ] ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (normalMonomial (Y := Y) l) := by
  induction l with
  | nil => exact contDiff_const
  | cons a l ih => exact (a.contDiff.comp contDiff_fst).mul ih

private def normalMonomialTerms (v : X) : List (X →L[ℝ] ℝ) → List (ℝ × List (X →L[ℝ] ℝ))
  | [] => []
  | a :: l => (a v, l) :: (normalMonomialTerms v l).map (fun p ↦ (p.1, a :: p.2))

private theorem normalMonomialTerms_length (v : X) (l : List (X →L[ℝ] ℝ)) :
    ∀ t ∈ normalMonomialTerms v l, t.2.length + 1 = l.length := by
  induction l with
  | nil => simp [normalMonomialTerms]
  | cons a l ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rfl
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      simp [ih u hu]

private theorem normalMonomial_deriv (l : List (X →L[ℝ] ℝ)) (v z : X × Y) :
    fderiv ℝ (normalMonomial l) z v =
      ((normalMonomialTerms v.1 l).map (fun t ↦ t.1 * normalMonomial t.2 z)).sum := by
  induction l with
  | nil => change (fderiv ℝ (fun _ : X × Y ↦ (1 : ℝ)) z) v = 0; simp
  | cons a l ih =>
    have h := (((a.comp (ContinuousLinearMap.fst ℝ X Y)).hasFDerivAt (x := z)).mul
      (normalMonomial_smooth (Y := Y) l |>.differentiable (by simp) |>.differentiableAt.hasFDerivAt)).fderiv
    change fderiv ℝ (fun z : X × Y ↦ a z.1 * normalMonomial l z) z v = _
    refine (congrArg (fun L : (X × Y) →L[ℝ] ℝ ↦ L v) h).trans ?_
    simp only [normalMonomialTerms, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      normalMonomial_cons]
    change a z.1 * fderiv ℝ (normalMonomial l) z v + normalMonomial l z * a v.1 = _
    rw [ih, add_comm, mul_comm (normalMonomial l z), ← List.sum_map_mul_left]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro u _
    ring

private theorem boundedDerivs_list {α : Type*} (l : List α) (F : α → I → X → ℂ) (n : ℕ)
    (hf : ∀ a ∈ l, ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F a i)) (h : ∀ a ∈ l, boundedDerivs (F a) n) :
    boundedDerivs (fun i x ↦ (l.map fun a ↦ F a i x).sum) n := by
  induction l with
  | nil => simpa using boundedDerivs_zero (I := I) (X := X) n
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hh (i : I) : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (l.map fun a ↦ F a i x).sum) := by
      have hs : ∀ (q : List α), (∀ u ∈ q, ContDiff ℝ (⊤ : ℕ∞) (F u i)) →
          ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (q.map fun a ↦ F a i x).sum) := by
        intro q
        induction q with
        | nil => exact fun _ ↦ contDiff_const
        | cons u q ih => exact fun hu ↦ (hu _ (by simp)).add (ih (fun t ht ↦ hu _ (by simp [ht])))
      exact hs l (fun u hu ↦ hf u (by simp [hu]) i)
    exact boundedDerivs_add (hf a (by simp)) hh n (h a (by simp)) (ih (fun u hu ↦ hf u (by simp [hu]))
      (fun u hu ↦ h u (by simp [hu])))

omit [IsFiniteMeasureOnCompacts μ] in
/-- Each normal factor can absorb one tangential derivative by integration by parts. -/
private theorem boundedDerivs_weighted_shearAverage [μ.IsAddHaarMeasure] (g : I → Y → ℂ)
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i)) (k : ℕ) (h : boundedDerivs g k)
    (l : List (X →L[ℝ] ℝ)) (ψ : W) :
    boundedDerivs (fun i z ↦ normalMonomial l z • shearAverage μ ψ (g i) z) (k + l.length) := by
  classical
  suffices all : ∀ m, ∀ l : List (X →L[ℝ] ℝ), l.length = m → ∀ ψ : W,
      boundedDerivs (fun i z ↦ normalMonomial l z • shearAverage μ ψ (g i) z) (k + m) from all _ l rfl ψ
  intro m
  induction m with
  | zero =>
    intro l hl ψ
    obtain rfl := List.length_eq_zero_iff.mp hl
    simpa [normalMonomial] using shearAverage_boundedDerivs μ hg ψ k h
  | succ m ih =>
    rintro (_ | ⟨a, l⟩) hl ψ
    · simp at hl
    have hlen : l.length = m := Nat.succ.inj hl
    let b := Module.finBasis ℝ Y
    let S := fun i ↦ shearAverage μ ψ (g i)
    have hS (i : I) := shearAverage_smooth μ ψ ψ.contDiff ψ.hasCompactSupport (g i) (hg i)
    refine ⟨boundedOnCompacts_mul_fixed (shearAverage_loc μ (boundedDerivs_loc h) ψ) (normalMonomial (a :: l))
      (normalMonomial_smooth _).continuous, fun v ↦ ?_⟩
    let terms := normalMonomialTerms v.1 (a :: l)
    let F (t : ℝ × List (X →L[ℝ] ℝ)) i (z : X × Y) := t.1 • (normalMonomial t.2 z • S i z)
    let G (j : Fin (Module.finrank ℝ Y)) i (z : X × Y) := (-1 : ℝ) • (normalMonomial l z •
      shearAverage μ (weightDerivative (shearCoordinateWeight b j v ψ) (a.smulRight (b j))) (g i) z)
    have hterms : boundedDerivs (fun i z ↦ (terms.map fun t ↦ F t i z).sum) (k + m) := by
      apply boundedDerivs_list terms F
      · exact fun t _ i ↦ ((normalMonomial_smooth t.2).smul (hS i)).const_smul t.1
      · intro t ht
        apply boundedDerivs_fixed_smul (fun i ↦ (normalMonomial_smooth _).smul (hS i)) (fun _ ↦ t.1) contDiff_const
        exact ih t.2 (by have := normalMonomialTerms_length v.1 (a :: l) t ht; omega) ψ
    let ψ' (j) := weightDerivative (shearCoordinateWeight b j v ψ) (a.smulRight (b j))
    have hs' (j) (i : I) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ normalMonomial l z • shearAverage μ (ψ' j) (g i) z) :=
      (normalMonomial_smooth l).smul (shearAverage_smooth μ _ (ψ' j).contDiff (ψ' j).hasCompactSupport _ (hg i))
    have hG (j) (i : I) : ContDiff ℝ (⊤ : ℕ∞) (G j i) := (hs' j i).const_smul (-1 : ℝ)
    have hgs (j) : boundedDerivs (G j) (k + m) := boundedDerivs_fixed_smul (hs' j) (fun _ ↦ (-1 : ℝ)) contDiff_const _
      (ih l hlen (ψ' j))
    have htermsSmooth (i : I) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (terms.map fun t ↦ F t i z).sum) := by
      induction terms with
      | nil => exact contDiff_const
      | cons t ts ih => exact (((normalMonomial_smooth t.2).smul (hS i)).const_smul t.1).add ih
    have hh := boundedDerivs_add htermsSmooth (fun i ↦ ContDiff.sum fun j _ ↦ hG j i) _
      hterms (boundedDerivs_finsum Finset.univ G _ hG hgs)
    convert hh using 1
    funext i z
    let p := normalMonomial (Y := Y) (a :: l)
    have d := (((normalMonomial_smooth (Y := Y) (a :: l)).differentiable (by simp)).differentiableAt.hasFDerivAt.smul
      (((hS i).differentiable (by simp)) z).hasFDerivAt).fderiv
    change fderiv ℝ (fun z ↦ p z • S i z) z v = _
    refine (congrArg (fun L : (X × Y) →L[ℝ] ℂ ↦ L v) d).trans ?_
    change p z • directional v (S i) z + fderiv ℝ p z v • S i z = _
    rw [add_comm, normalMonomial_deriv, List.sum_smul, shearAverage_direction μ b ψ (g i) (hg i), Finset.smul_sum]
    congr 1
    · simp only [List.map_map, Function.comp_def, F, terms, mul_smul]
    · apply Finset.sum_congr rfl
      intro j _
      change (a z.1 * normalMonomial l z) • _ = _
      rw [mul_comm, mul_smul]
      refine (congrArg (fun w : ℂ ↦ normalMonomial l z • w)
        (shearAverage_integrationByParts μ (shearCoordinateWeight b j v ψ) (shearCoordinateWeight b j v ψ).contDiff
          (shearCoordinateWeight b j v ψ).hasCompactSupport (g i) (hg i) a (b j) z)).trans ?_
      simp only [neg_one_smul, smul_neg]
      rfl

end TraceWeights

section TraceHadamard

open MeasureTheory

variable {I X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local notation "Z" => X × Y

/-- Bounds of all ambient directional derivatives, evaluated only on the plane. -/
private def boundedPlaneJet (F : I → Z → ℂ) : ℕ → Prop
  | 0 => boundedOnCompacts (fun i y ↦ F i (0, y))
  | n + 1 => boundedOnCompacts (fun i y ↦ F i (0, y)) ∧ ∀ v : Z, boundedPlaneJet (fun i ↦ directional v (F i)) n

private theorem boundedPlaneJet_loc {F : I → Z → ℂ} {n : ℕ} (h : boundedPlaneJet F n) :
    boundedOnCompacts (fun i y ↦ F i (0, y)) := by cases n with | zero => exact h | succ n => exact h.1

private theorem boundedPlaneJet_mono {F : I → Z → ℂ} {m n : ℕ} (h : boundedPlaneJet F n) (hm : m ≤ n) : boundedPlaneJet F m := by
  induction m generalizing n F with
  | zero => exact boundedPlaneJet_loc h
  | succ m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨h.1, fun v ↦ ih (h.2 v) (by omega)⟩

private theorem boundedPlaneJet_of_boundedDerivs {F : I → Z → ℂ} {n : ℕ} (h : boundedDerivs F n) : boundedPlaneJet F n := by
  have loc {G : I → Z → ℂ} (hg : boundedOnCompacts G) : boundedOnCompacts (fun i y ↦ G i (0, y)) := by
    intro K
    obtain ⟨C, hC, hb⟩ := hg ⟨_, K.isCompact.image (continuous_const.prodMk continuous_id)⟩
    exact ⟨C, hC, fun i y hy ↦ hb i _ ⟨y, hy, rfl⟩⟩
  induction n generalizing F with
  | zero => exact loc h
  | succ n ih => exact ⟨loc h.1, fun v ↦ ih (h.2 v)⟩

private theorem boundedOnCompacts_sub {F G : I → Y → ℂ} (hf : boundedOnCompacts F) (hg : boundedOnCompacts G) :
    boundedOnCompacts (fun i y ↦ F i y - G i y) := by
  intro K
  obtain ⟨C, hC, hc⟩ := hf K
  obtain ⟨D, hD, hd⟩ := hg K
  exact ⟨_, add_nonneg hC hD, fun i y hy ↦ (norm_sub_le _ _).trans (add_le_add (hc i y hy) (hd i y hy))⟩

private theorem boundedPlaneJet_sub (F G : I → Z → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (n : ℕ) (hF : boundedPlaneJet F n) (hG : boundedPlaneJet G n) :
    boundedPlaneJet (fun i z ↦ F i z - G i z) n := by
  induction n generalizing F G with
  | zero => exact boundedOnCompacts_sub hF hG
  | succ n ih =>
    refine ⟨boundedOnCompacts_sub hF.1 hG.1, fun v ↦ ?_⟩
    have he (i : I) : directional v (fun z ↦ F i z - G i z) = directional v (F i) - directional v (G i) := by
      funext z; exact congrArg (fun L : Z →L[ℝ] ℂ ↦ L v)
        (((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt.sub
          ((hg i).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    simp only [he]
    exact ih _ _ (fun i ↦ directional_smooth (hf i) _) (fun i ↦ directional_smooth (hg i) _)
      (hF.2 v) (hG.2 v)

private theorem boundedPlaneJet_add (F G : I → Z → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (G i)) (n : ℕ) (hF : boundedPlaneJet F n) (hG : boundedPlaneJet G n) :
    boundedPlaneJet (fun i z ↦ F i z + G i z) n := by
  induction n generalizing F G with
  | zero => exact boundedOnCompacts_add hF hG
  | succ n ih =>
    refine ⟨boundedOnCompacts_add hF.1 hG.1, fun v ↦ ?_⟩
    have he (i : I) : directional v (fun z ↦ F i z + G i z) = directional v (F i) + directional v (G i) := by
      funext z; exact congrArg (fun L : Z →L[ℝ] ℂ ↦ L v)
        (((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt.add
          ((hg i).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv
    simp only [he]
    exact ih _ _ (fun i ↦ directional_smooth (hf i) _) (fun i ↦ directional_smooth (hg i) _)
      (hF.2 v) (hG.2 v)

private theorem boundedPlaneJet_smul_const (c : ℝ) (F : I → Z → ℂ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (n : ℕ) (h : boundedPlaneJet F n) : boundedPlaneJet (fun i z ↦ c • F i z) n := by
  induction n generalizing F with
  | zero => exact boundedOnCompacts_mul_fixed h (fun _ ↦ c) continuous_const
  | succ n ih =>
    refine ⟨boundedOnCompacts_mul_fixed h.1 (fun _ ↦ c) continuous_const, fun v ↦ ?_⟩
    have he (i : I) : directional v (fun z ↦ c • F i z) = fun z ↦ c • directional v (F i) z := by
      funext z
      exact congrArg (fun m : Z →L[ℝ] ℂ ↦ m v)
        (((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt.const_smul c).fderiv
    simp only [he]
    exact ih _ (fun i ↦ directional_smooth (hf i) _) (h.2 v)

private theorem boundedPlaneJet_sum {α : Type*} (s : Finset α) (F : α → I → Z → ℂ) (n : ℕ)
    (hf : ∀ a i, ContDiff ℝ (⊤ : ℕ∞) (F a i)) (h : ∀ a, boundedPlaneJet (F a) n) :
    boundedPlaneJet (fun i z ↦ ∑ a ∈ s, F a i z) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using boundedPlaneJet_of_boundedDerivs (boundedDerivs_zero (I := I) (X := Z) n)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact boundedPlaneJet_add _ _ (hf a) (fun i ↦ ContDiff.sum fun a _ ↦ hf a i) n (h a) ih

private theorem boundedPlaneJet_restrict (F : I → Z → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (n : ℕ) (h : boundedPlaneJet F n) : boundedDerivs (fun i y ↦ F i (0, y)) n := by
  induction n generalizing F with
  | zero => exact h
  | succ n ih =>
    refine ⟨h.1, fun v ↦ ?_⟩
    have he (i : I) : directional v (fun y ↦ F i (0, y)) = fun y ↦ directional (0, v) (F i) (0, y) := by
      funext y
      have hh := (((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
        (ContinuousLinearMap.inr ℝ X Y).hasFDerivAt).fderiv
      exact congrArg (fun L : Y →L[ℝ] ℂ ↦ L v) hh
    simp only [he]
    exact ih _ (fun i ↦ directional_smooth (hf i) _) (h.2 (0, v))

private def scaleNormal (t : ℝ) : Z →L[ℝ] Z :=
  (t • ContinuousLinearMap.fst ℝ X Y).prod (ContinuousLinearMap.snd ℝ X Y)

private def radialAverage (w : ℝ → ℝ) (g : Z → ℂ) (z : Z) :=
  ∫ t in Ioc (0 : ℝ) 1, w t • g (scaleNormal t z)

private theorem radialAverage_smooth (w : ℝ → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (g : Z → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (radialAverage w g) := by
  apply ContDiff.parametric_integral (k := Icc (0 : ℝ) 1) isCompact_Icc Ioc_subset_Icc_self (by simp)
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Z × ℝ ↦ w p.2 • g (p.2 • p.1.1, p.1.2))
  fun_prop

private theorem trace_interval_direction {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) F.uncurry) (z v : V)
    (L : ℝ → V →L[ℝ] ℂ) (hL : Continuous L) (dL : ∀ t, HasFDerivAt (F · t) (L t) z) :
    fderiv ℝ (fun x ↦ ∫ t in Ioc (0 : ℝ) 1, F x t) z v = ∫ t in Ioc (0 : ℝ) 1, L t v := by
  have h := hasFDerivAt_integral_of_contDiffOn (μ := volume) (s := Ioc (0 : ℝ) 1) (x₀ := z)
    (f := F) univ_mem isCompact_Icc (by simp) Ioc_subset_Icc_self (hf.of_le (by simp)).contDiffOn
  have eqn : (fun t ↦ fderiv ℝ (F · t) z) = L := funext fun t ↦ (dL t).fderiv
  have hi : IntegrableOn L (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hL.intervalIntegrable 0 1)
  rw [h.fderiv, eqn, ContinuousLinearMap.integral_apply hi]

private theorem radialAverage_integral_deriv (w : ℝ → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (g : Z → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v z : Z) : directional v (radialAverage w g) z =
      ∫ t in Ioc (0 : ℝ) 1, w t • fderiv ℝ g (scaleNormal t z) (scaleNormal t v) := by
  let F (u : Z) (t : ℝ) := w t • g (scaleNormal t u)
  let L (t : ℝ) := w t • (fderiv ℝ g (scaleNormal t z)).comp (scaleNormal t)
  apply trace_interval_direction F _ z v L
  · have hs : Continuous (fun t : ℝ ↦ scaleNormal (X := X) (Y := Y) t) := by
      let A := (ContinuousLinearMap.inl ℝ X Y).comp (ContinuousLinearMap.fst ℝ X Y)
      let B := (ContinuousLinearMap.inr ℝ X Y).comp (ContinuousLinearMap.snd ℝ X Y)
      apply (continuous_id.smul continuous_const |>.add continuous_const : Continuous (fun t : ℝ ↦ t • A + B)).congr
      intro t
      ext z <;> simp [B, scaleNormal]
    exact hw.continuous.smul (((hg.continuous_fderiv (by simp)).comp (hs.clm_apply continuous_const)).clm_comp hs)
  · intro t
    exact (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
      (scaleNormal t).hasFDerivAt).const_smul (w t)
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : Z × ℝ ↦ w p.2 • g (p.2 • p.1.1, p.1.2))
    fun_prop

private theorem radialAverage_directional (w : ℝ → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (g : Z → ℂ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Z) :
    directional v (radialAverage w g) = fun z ↦ radialAverage (fun t ↦ t * w t) (directional (v.1, 0) g) z +
      radialAverage w (directional (0, v.2) g) z := by
  funext z
  have hi (c : ℝ → ℝ) (hc : Continuous c) (u : Z) :
      IntegrableOn (fun t ↦ c t • directional u g (scaleNormal t z)) (Ioc (0 : ℝ) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    apply Continuous.intervalIntegrable
    exact hc.smul ((directional_smooth hg u).continuous.comp
      (show Continuous (fun t : ℝ ↦ (t • z.1, z.2)) by fun_prop))
  rw [radialAverage_integral_deriv w hw g hg]
  unfold radialAverage
  refine Eq.trans ?_ (integral_add (hi (fun t ↦ t * w t) (continuous_id.mul hw.continuous) (v.1, 0)) (hi w hw.continuous (0, v.2)))
  apply setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
  have hv : scaleNormal t v = t • (v.1, (0:Y)) + (0, v.2) := by ext <;> simp [scaleNormal]
  change w t • fderiv ℝ g (scaleNormal t z) (scaleNormal t v) = _
  rw [hv, map_add, map_smul, smul_add, mul_smul, smul_comm]
  rfl

private theorem radialAverage_loc (F : I → Z → ℂ) (w : ℝ → ℝ)
    (h : boundedOnCompacts (fun i y ↦ F i (0, y))) : boundedOnCompacts (fun i y ↦ radialAverage w (F i) (0, y)) := by
  have eqn (i : I) (y : Y) : radialAverage w (F i) (0, y) =
        (∫ t in Ioc (0 : ℝ) 1, w t) • F i (0, y) := by
      unfold radialAverage
      simp only [show ∀ t, scaleNormal t ((0:X), y) = (0, y) from fun t ↦ Prod.ext (smul_zero _) rfl]
      exact integral_smul_const _ _
  simp only [eqn]
  exact boundedOnCompacts_mul_fixed h (fun _ ↦ ∫ t in Ioc (0 : ℝ) 1, w t) continuous_const

private theorem boundedPlaneJet_radial (F : I → Z → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i))
    (w : ℝ → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (n : ℕ) (hF : boundedPlaneJet F n) :
    boundedPlaneJet (fun i ↦ radialAverage w (F i)) n := by
  induction n generalizing F w with
  | zero => exact radialAverage_loc F w hF
  | succ n ih =>
    refine ⟨radialAverage_loc F w hF.1, fun v ↦ ?_⟩
    simp only [fun i ↦ radialAverage_directional w hw (F i) (hf i) v]
    have H (u : Z) (e : ℝ → ℝ) (he : ContDiff ℝ (⊤ : ℕ∞) e) :=
      ih (fun i ↦ directional u (F i)) (fun i ↦ directional_smooth (hf i) u) e he (hF.2 u)
    exact boundedPlaneJet_add _ _ (fun i ↦ radialAverage_smooth _ (contDiff_id.mul hw) _ (directional_smooth (hf i) _))
      (fun i ↦ radialAverage_smooth _ hw _ (directional_smooth (hf i) _)) _ (H _ _ (contDiff_id.mul hw)) (H _ w hw)

/-- The fundamental theorem of calculus along the normal segment, in basis coordinates. -/
private theorem trace_radial_eq_sub [FiniteDimensional ℝ X] (g : Z → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (z : Z) : g z - g (0, z.2) = ∑ j,
      (Module.finBasis ℝ X).repr z.1 j • radialAverage (fun _ ↦ 1) (directional ((Module.finBasis ℝ X) j, 0) g) z := by
  let b := Module.finBasis ℝ X
  let u (t : ℝ) := (t • z.1, z.2)
  have hd (t : ℝ) : HasDerivAt (fun t ↦ g (u t)) (directional (z.1, 0) g (u t)) t := by
    have hu : HasDerivAt u (z.1, 0) t := by
      simpa [u] using ((hasDerivAt_id t).smul_const z.1).prodMk (hasDerivAt_const t z.2)
    exact ((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt t hu
  have eqn := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ ↦ hd t)
    (((directional_smooth hg _).continuous.comp (by dsimp [u]; fun_prop)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at eqn
  simp only [u, one_smul, zero_smul, Prod.mk.eta] at eqn
  rw [← eqn]
  simp only [radialAverage, one_smul, ← integral_smul]
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    let L := (fderiv ℝ g (u t)).comp (ContinuousLinearMap.inl ℝ X Y)
    exact congrArg L (b.sum_repr z.1).symm |>.trans (by rw [map_sum]; simp only [map_smul]; rfl)
  · intro j _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp ((continuous_const.smul ((directional_smooth hg _).continuous.comp
      (show Continuous u by dsimp [u]; fun_prop))).intervalIntegrable 0 1)

end TraceHadamard

private def smoothScalar (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Submodule ℝ (V → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  zero_mem' := by change ContDiff ℝ (⊤ : ℕ∞) (fun _ : V ↦ (0 : ℂ)); exact contDiff_const
  add_mem' := by intro f g hf hg; exact (show ContDiff ℝ (⊤ : ℕ∞) f from hf).add (show ContDiff ℝ (⊤ : ℕ∞) g from hg)
  smul_mem' := by intro c f hf; exact (show ContDiff ℝ (⊤ : ℕ∞) f from hf).const_smul c

private theorem smoothScalar_contDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : smoothScalar V) :
    ContDiff ℝ (⊤ : ℕ∞) f.val := f.property

section TraceInduction

open MeasureTheory

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
local notation "Z" => X × Y
local notation "M" => X →L[ℝ] Y

private def mulNormalMonomial (l : List (X →L[ℝ] ℝ)) (f : smoothScalar Z) : smoothScalar Z :=
  ⟨fun z ↦ normalMonomial l z • f.val z, (normalMonomial_smooth _).smul (smoothScalar_contDiff f)⟩

private def planeRestriction (f : smoothScalar Z) : smoothScalar Y :=
  ⟨fun y ↦ f.val (0, y), (smoothScalar_contDiff f).comp (contDiff_const.prodMk contDiff_id)⟩

/-- Subtract the averaged trace, factor the remainder in normal coordinates, and iterate. -/
private theorem bounded_action_of_boundedPlaneJet (S : smoothScalar Z →ₗ[ℝ] ℂ) (N : ℕ)
    (bounded : ∀ F : ℕ → smoothScalar Z, boundedDerivs (fun i ↦ (F i).val) N →
      ∃ C : ℝ, ∀ i, ‖S (F i)‖ ≤ C)
    (hz : ∀ (l : List (X →L[ℝ] ℝ)) (f : smoothScalar Z), l.length = N + 1 → S (mulNormalMonomial l f) = 0)
    (F : ℕ → smoothScalar Z) (h : boundedPlaneJet (fun i ↦ (F i).val) N) : ∃ C : ℝ, ∀ i, ‖S (F i)‖ ≤ C := by
  classical
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let μ := (Measure.addHaar : Measure M)
  let b := Module.finBasis ℝ X
  let ρ : ContDiffBump (0 : M) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let ψ : 𝓓((⊤ : Opens M), ℝ) := ⟨ρ.normed μ, ρ.contDiff_normed, ρ.hasCompactSupport_normed, fun _ _ ↦ trivial⟩
  have mass : ∫ L, ψ L ∂μ = 1 := ρ.integral_normed
  let A (f : smoothScalar Z) : smoothScalar Z := ⟨shearAverage μ ψ (planeRestriction f).val,
    shearAverage_smooth μ ψ ψ.contDiff ψ.hasCompactSupport _ (smoothScalar_contDiff (planeRestriction f))⟩
  have eqA (f : smoothScalar Z) (y : Y) : (A f).val (0, y) = f.val (0, y) := by
    change (∫ L : M, ψ L • f.val (0, y + L 0) ∂μ) = _
    simp only [map_zero, add_zero, integral_smul_const, mass, one_smul]
  let H (j : Fin (Module.finrank ℝ X)) (f : smoothScalar Z) : smoothScalar Z :=
    ⟨radialAverage (fun _ ↦ 1) (directional (b j, 0) ((f - A f).val)),
      radialAverage_smooth _ contDiff_const _ (directional_smooth (smoothScalar_contDiff (f - A f)) _)⟩
  let c (j : Fin (Module.finrank ℝ X)) := (b.coord j).toContinuousLinearMap
  have expand (l : List (X →L[ℝ] ℝ)) (f : smoothScalar Z) :
      mulNormalMonomial l f = mulNormalMonomial l (A f) +
        ∑ j, mulNormalMonomial (c j :: l) (H j f) := by
    apply Subtype.ext
    funext z
    have he := trace_radial_eq_sub (f - A f).val (smoothScalar_contDiff (f - A f)) z
    change f.val z - (A f).val z - (f.val (0, z.2) - (A f).val (0, z.2)) = _ at he
    rw [eqA, sub_self, sub_zero] at he
    let ev : smoothScalar Z →ₗ[ℝ] ℂ := (LinearMap.proj z).comp (smoothScalar Z).subtype
    change normalMonomial l z • f.val z = normalMonomial l z • (A f).val z +
      ev (∑ j, mulNormalMonomial (c j :: l) (H j f))
    rw [map_sum, ← sub_eq_iff_eq_add', ← smul_sub, he, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change normalMonomial l z • (c j z.1 • (H j f).val z) = (c j z.1 * normalMonomial l z) • (H j f).val z
    rw [mul_smul, smul_comm]
  have step (k : ℕ) : ∀ (l : List (X →L[ℝ] ℝ)) (G : ℕ → smoothScalar Z),
      k + l.length = N + 1 → (∀ j < k, boundedPlaneJet (fun i ↦ (G i).val) j) →
      ∃ C : ℝ, ∀ i, ‖S (mulNormalMonomial l (G i))‖ ≤ C := by
    induction k with
    | zero =>
      intro l G hl _
      exact ⟨0, fun i ↦ by rw [hz l _ (by omega), norm_zero]⟩
    | succ k ih =>
      intro l G hl hd
      have hG := hd k (Nat.lt_succ_self k)
      have hrest := boundedPlaneJet_restrict (fun i ↦ (G i).val) (fun i ↦ (smoothScalar_contDiff (G i))) k hG
      obtain ⟨D, hD⟩ := bounded (fun i ↦ mulNormalMonomial l (A (G i))) (by
        have hh := boundedDerivs_weighted_shearAverage μ (fun i ↦ (planeRestriction (G i)).val)
          (fun i ↦ (smoothScalar_contDiff (planeRestriction (G i)))) k hrest l ψ
        exact (show k + l.length = N by omega) ▸ hh)
      have hAG := boundedPlaneJet_of_boundedDerivs (shearAverage_boundedDerivs μ
        (fun i ↦ smoothScalar_contDiff (planeRestriction (G i))) ψ k hrest)
      have hR := boundedPlaneJet_sub _ _ (fun i ↦ smoothScalar_contDiff (G i))
        (fun i ↦ smoothScalar_contDiff (A (G i))) k hG hAG
      have child (j : Fin (Module.finrank ℝ X)) (d : ℕ) (hd : d < k) :
          boundedPlaneJet (fun i ↦ (H j (G i)).val) d := by
        apply boundedPlaneJet_radial (fun i ↦ directional (b j, 0) ((G i - A (G i)).val))
          (fun i ↦ directional_smooth (smoothScalar_contDiff (G i - A (G i))) _) (fun _ ↦ 1) contDiff_const
        exact (boundedPlaneJet_mono hR (show d + 1 ≤ k by omega)).2 _
      choose B hB using fun j ↦ ih (c j :: l) (fun i ↦ H j (G i)) (by simp; omega) (child j)
      refine ⟨D + ∑ j, B j, fun i ↦ ?_⟩
      rw [expand l (G i), map_add, map_sum]
      exact (norm_add_le _ _).trans (add_le_add (hD i)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ ↦ hB j i))))
  obtain ⟨C, hC⟩ := step (N + 1) [] F (by simp) (fun j hj ↦ boundedPlaneJet_mono h (by omega))
  exact ⟨C, fun i ↦ by simpa [mulNormalMonomial, normalMonomial] using hC i⟩

end TraceInduction

section TraceAction
variable {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
local notation "Z" => X × Y

private theorem vanishing_product_jet (l : List (V → ℝ)) (g : V → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : V) (hl : ∀ u ∈ l, ContDiff ℝ (⊤ : ℕ∞) u ∧ u p = 0) (j : ℕ) (hj : j < l.length) :
    iteratedFDeriv ℝ j (fun z ↦ (l.map fun u ↦ u z).prod • g z) p = 0 := by
  have hprod : ∀ q : List (V → ℝ), (∀ u ∈ q, ContDiff ℝ (⊤ : ℕ∞) u) →
      ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (q.map fun u ↦ u z).prod) := by
    intro q
    induction q with
    | nil => exact fun _ ↦ contDiff_const
    | cons a q ih => exact fun h ↦ (h a (by simp)).mul (ih fun u hu ↦ h u (by simp [hu]))
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    let r (z : V) := (l.map fun u ↦ u z).prod • g z
    have he : (fun z ↦ ((a :: l).map fun u ↦ u z).prod • g z) = fun z ↦ a z • r z := by
      funext z; exact mul_smul _ _ _
    rw [he, ← norm_le_zero_iff]
    apply (norm_iteratedFDeriv_smul_le (hl a (by simp)).1 ((hprod l
      (fun u hu ↦ (hl u (by simp [hu])).1)).smul hg) p (show (j : ℕ∞ω) ≤ (⊤ : ℕ∞) by simp)).trans
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    have hij := Finset.mem_range.mp hi
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [norm_iteratedFDeriv_zero, (hl a (by simp)).2]
    · have he := ih (fun u hu ↦ hl u (by simp [hu])) (j - i) (by simp at hj; omega)
      change iteratedFDeriv ℝ (j - i) r p = 0 at he
      change _ * ‖iteratedFDeriv ℝ (j - i) r p‖ = 0
      rw [he, norm_zero, mul_zero]

private theorem boundedDerivs_comp_linear {U V I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : U →L[ℝ] V) (F : I → V → ℂ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (n : ℕ) (h : boundedDerivs F n) : boundedDerivs (fun i ↦ F i ∘ L) n := by
  have loc {G : I → V → ℂ} (hG : boundedOnCompacts G) : boundedOnCompacts (fun i ↦ G i ∘ L) := by
    intro K
    obtain ⟨C, hC, hB⟩ := hG ⟨_, K.isCompact.image L.continuous⟩
    exact ⟨C, hC, fun i x hx ↦ hB i _ ⟨x, hx, rfl⟩⟩
  induction n generalizing F with
  | zero => exact loc h
  | succ n ih =>
    refine ⟨loc h.1, fun v ↦ ?_⟩
    have eqn (i : I) : directional v (F i ∘ L) = directional (L v) (F i) ∘ L := by
      funext x
      exact congrArg (fun m : U →L[ℝ] ℂ ↦ m v) ((((hf i).differentiable (by simp)).differentiableAt.hasFDerivAt.comp
        x L.hasFDerivAt).fderiv)
    simp only [eqn]
    exact ih _ (fun i ↦ directional_smooth (hf i) _) (h.2 _)

private def traceCutTest (χ : 𝓓((⊤ : Opens V), ℝ)) (e : V ≃L[ℝ] Z) :
    smoothScalar Z →ₗ[ℝ] 𝓓((⊤ : Opens V), ℂ) where
  toFun f := ⟨fun x ↦ χ x • f.val (e x), χ.contDiff.smul ((smoothScalar_contDiff f).comp e.contDiff),
    χ.hasCompactSupport.smul_right, fun _ _ ↦ trivial⟩
  map_add' f g := TestFunction.ext fun x ↦ smul_add (χ x) (f.val (e x)) (g.val (e x))
  map_smul' c f := TestFunction.ext fun x ↦ smul_comm (χ x) c (f.val (e x))

open scoped Manifold in
/-- Localize to one compact set before applying the estimate for smooth families. -/
private theorem distribution_bounded_on_sequence (e : V ≃L[ℝ] Z)
    (T : StrongDual ℂ 𝓓((⊤ : Opens V), ℂ)) (N : ℕ) (hN : orderBound(T, V, N))
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hp : ∀ x ∈ Distribution.dsupport (⇑T), (e x).1 = 0)
    (F : ℕ → 𝓓((⊤ : Opens V), ℂ)) (hF : boundedPlaneJet (fun i z ↦ F i (e.symm z)) N) :
    ∃ B : ℝ, ∀ i, ‖T (F i)‖ ≤ B := by
  obtain ⟨K, hk, hsub⟩ := exists_compact_superset hK
  obtain ⟨b, hb, h0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, V)
    (n := ⊤) Distribution.isClosed_dsupport hsub
  have hbK : tsupport (b : V → ℝ) ⊆ K := hk.isClosed.closure_subset_iff.mpr
    fun x hx ↦ by_contra fun h ↦ hx (h0 x h)
  let χ : 𝓓((⊤ : Opens V), ℝ) := ⟨b, contMDiff_iff_contDiff.mp b.contMDiff,
    hk.of_isClosed_subset (isClosed_tsupport _) hbK, fun _ _ ↦ trivial⟩
  let S := (T.restrictScalars ℝ).toLinearMap.comp (traceCutTest χ e)
  let L := (ContinuousLinearMap.inr ℝ X Y).comp (ContinuousLinearMap.snd ℝ X Y)
  let P := e.symm.toContinuousLinearMap.comp (L.comp e.toContinuousLinearMap)
  have hP : ∀ x ∈ Distribution.dsupport (⇑T), P x = x := by
    intro x hx
    apply e.injective
    change e (e.symm (0, (e x).2)) = e x
    rw [e.apply_symm_apply]; exact Prod.ext (hp x hx).symm rfl
  let F' (i : ℕ) : smoothScalar Z := ⟨(F i) ∘ e.symm, (F i).contDiff.comp e.symm.contDiff⟩
  have bound (G : ℕ → smoothScalar Z) (hG : boundedDerivs (fun i ↦ (G i).val) N) : ∃ C : ℝ, ∀ i, ‖S (G i)‖ ≤ C := by
    have h := boundedDerivs_fixed_smul (fun i ↦ (smoothScalar_contDiff (G i)).comp e.contDiff) (χ : V → ℝ) χ.contDiff _
        (boundedDerivs_comp_linear e.toContinuousLinearMap (fun i ↦ (G i).val) (fun i ↦ (smoothScalar_contDiff (G i))) N hG)
    let H (i : ℕ) := traceCutTest χ e (G i)
    let K' : Compacts V := ⟨_, χ.hasCompactSupport⟩
    obtain ⟨B, hB, bound⟩ := hN K'
    choose D hD hi using fun j : Fin (N + 1) ↦ boundedDerivs_iterated_norm
      (F := fun i ↦ (H i : V → ℂ)) (fun i ↦ (H i).contDiff) j (boundedDerivs_mono h (Nat.le_of_lt_succ j.isLt)) K'
    let D' := ∑ j, D j
    have hpos : 0 ≤ D' := Finset.sum_nonneg fun j _ ↦ hD j
    refine ⟨B * D', fun i ↦ bound (H i) (tsupport_smul_subset_left _ _) D' hpos fun j hj x ↦ ?_⟩
    by_cases hx : x ∈ K'
    · let k : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
      exact (hi k i x hx).trans (Finset.single_le_sum (fun u _ ↦ hD u) (Finset.mem_univ k))
    · have hx' : x ∉ tsupport ((H i) : V → ℂ) := fun h ↦ hx (tsupport_smul_subset_left _ _ h)
      have he : iteratedFDeriv ℝ j (H i : V → ℂ) x = 0 :=
        by_contra fun hn ↦ hx' (support_iteratedFDeriv_subset j hn)
      simpa only [he, norm_zero] using hpos
  have vanish (l : List (X →L[ℝ] ℝ)) (f : smoothScalar Z) (hl : l.length = N + 1) : S (mulNormalMonomial l f) = 0 := by
    apply trace_vanishes_of_flat_plane T N hN P hP
    intro p j hj
    let l' := l.map (fun a : X →L[ℝ] ℝ ↦ fun z : V ↦ a (e z).1)
    have hval : ((traceCutTest χ e (mulNormalMonomial l f)) : V → ℂ) =
        fun z ↦ (l'.map fun u ↦ u z).prod • (χ z • f.val (e z)) := by
      funext z; change χ z • ((l.map fun a ↦ a (e z).1).prod • f.val (e z)) = _
      simp only [l', List.map_map, Function.comp_def]
      exact smul_comm _ _ _
    rw [hval]
    apply vanishing_product_jet l' _ (χ.contDiff.smul ((smoothScalar_contDiff f).comp e.contDiff))
      (P p) _ j (by simpa [l', hl] using Nat.lt_succ_of_le hj)
    intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    refine ⟨a.contDiff.comp (contDiff_fst.comp e.contDiff), ?_⟩
    change a (e (e.symm (0, (e p).2))).1 = 0
    rw [e.apply_symm_apply, map_zero]
  obtain ⟨C, hC⟩ := bounded_action_of_boundedPlaneJet S N bound vanish F' hF
  refine ⟨C, fun i ↦ (le_of_eq (congrArg norm ?_)).trans (hC i)⟩
  change T (F i) = T ((traceCutTest χ e) (F' i))
  rw [← sub_eq_zero, ← map_sub]
  apply testFunction_vanishes_off_dsupport
  intro x hx hx'
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
  filter_upwards [hb.filter_mono (nhds_le_nhdsSet hx')] with y hy
  change F i y - b y • (F i) (e.symm (e y)) = 0
  rw [hy, one_smul, e.symm_apply_apply, sub_self]

end TraceAction

/-- Exhaust by balls and rescale a putative sequence of counterexamples to the compact bound. -/
private theorem compact_trace_estimate_of_sequences {X E I : Type*}
    [AddCommGroup X] [Module ℂ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T : X →ₗ[ℂ] ℂ) (J : I → X →ₗ[ℂ] 𝓓((⊤ : Opens E), ℂ))
    (bound : ∀ f : ℕ → X, (∀ i, boundedOnCompacts (fun n y ↦ J i (f n) y)) → ∃ D : ℝ, ∀ n, ‖T (f n)‖ ≤ D) :
    ∃ (K : Compacts E) (C : ℝ), ∀ x B, 0 ≤ B → (∀ i (y : K), ‖J i x y.val‖ ≤ B) →
      ‖T x‖ ≤ C * B := by
  classical
  by_contra! bad
  let K (n : ℕ) : Compacts E := ⟨Metric.closedBall 0 n, isCompact_closedBall _ _⟩
  choose f b hb hJ hT using fun n : ℕ ↦ bad (K n) ((n:ℝ) + 1)
  have hpos (n : ℕ) : 0 < ‖T (f n)‖ := (mul_nonneg (by positivity) (hb n)).trans_lt (hT n)
  let c (n : ℕ) : ℝ := ((n:ℝ) + 1) / ‖T (f n)‖
  have hc (n : ℕ) : 0 ≤ c n := div_nonneg (by positivity) (hpos n).le
  let g (n : ℕ) := (c n : ℂ) • f n
  have hnorm (n : ℕ) : ‖T (g n)‖ = n + 1 := by
    dsimp only [g]
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hc n)]
    exact div_mul_cancel₀ _ (hpos n).ne'
  have ht (n : ℕ) (i : I) (y : E) (hy : y ∈ K n) : ‖J i (g n) y‖ ≤ 1 := by
    dsimp only [g]
    rw [map_smul, IsSMulApply.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg (hc n)]
    apply (mul_le_mul_of_nonneg_left (hJ n i ⟨y, hy⟩) (hc n)).trans
    change ((n:ℝ) + 1) / ‖T (f n)‖ * b n ≤ 1
    rw [div_mul_eq_mul_div, div_le_one (hpos n)]
    exact (hT n).le
  obtain ⟨D, hD⟩ := bound g (fun i H ↦ by
    obtain ⟨r, hr⟩ := H.isCompact.isBounded.subset_closedBall (0 : E)
    obtain ⟨N, hN⟩ := exists_nat_ge r
    choose A ha using fun n : ℕ ↦ H.isCompact.exists_bound_of_continuousOn (J i (g n)).contDiff.continuous.continuousOn
    let M := ∑ n ∈ Finset.range N, max 0 (A n)
    have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _)
    refine ⟨M + 1, by positivity, fun n y hy ↦ ?_⟩
    by_cases hn : n < N
    · exact (ha n y hy).trans ((le_max_right _ _).trans ((Finset.single_le_sum
        (fun k _ ↦ le_max_left 0 (A k)) (Finset.mem_range.mpr hn)).trans (by linarith)))
    · exact (ht n i y (hr.trans (Metric.closedBall_subset_closedBall
        (hN.trans (by exact_mod_cast (Nat.le_of_not_gt hn)))) hy)).trans (by linarith))
  obtain ⟨n, hn⟩ := exists_nat_gt D
  have := hD n
  rw [hnorm] at this
  linarith

section TraceCoords
open scoped Classical

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "V(" J ")" => EuclideanSpace ℝ J
local notation "W" => V(ι ⊕ κ)
local notation "D" => 𝓓((⊤ : Opens W),ℂ)
local notation "Dop" => fun i : ι ⊕ κ ↦ (LineDeriv.lineDerivOpCLM ℂ D
  (EuclideanSpace.single i (1 : ℝ)) : D →L[ℂ] D)
local notation "Ix(" N ")" => {α : (ι ⊕ κ) → Fin (N + 1) // ∑ i, (α i : ℕ) ≤ N}
local notation "projY" y => (WithLp.toLp 2 (Sum.elim (fun _ : ι ↦ (0 : ℝ)) (fun j : κ ↦ y j)) : W)

private def splitCoordinates : W ≃L[ℝ] V(ι) × V(κ) := by
  let L := PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℝ) 2 (fun _ : ι ⊕ κ ↦ ℝ)
  let e := WithLp.homeomorphProd 2 V(ι) V(κ)
  exact { L.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ _) with
    continuous_toFun := e.continuous.comp L.continuous
    continuous_invFun := L.symm.continuous.comp e.symm.continuous }

private theorem trace_coord_direction (e : W ≃L[ℝ] V(ι) × V(κ)) (f : D) (v : V(ι) × V(κ)) :
    directional v ((f : W → ℂ) ∘ e.symm) = fun z ↦ ∑ j : ι ⊕ κ, e.symm v j • (Dop j f) (e.symm z) := by
  funext z
  have hd (j) (x : W) : Dop j f x = fderiv ℝ (f : W → ℂ) x (EuclideanSpace.single j (1 : ℝ)) := by
    change ((LineDeriv.lineDerivOpCLM ℂ D (EuclideanSpace.single j (1 : ℝ)) : D →L[ℂ] D) f) x = _
    rw [TestFunction.lineDerivOpCLM_eq_lineDerivCLM, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le f le_top]
  change fderiv ℝ ((f : W → ℂ) ∘ e.symm) z v = _
  rw [fderiv_comp _ (f.contDiff.differentiable (by simp)).differentiableAt e.symm.differentiableAt,
    e.symm.fderiv, ContinuousLinearMap.comp_apply]
  have sum (w : W) : (∑ j, (w j) • EuclideanSpace.single j (1 : ℝ)) = w := by
    ext k
    let ev := PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι ⊕ κ ↦ ℝ) k
    change ev (∑ j, w j • _) = w k
    rw [map_sum]; simp [map_smul, ev, PiLp.single_apply]
  calc _ = (fderiv ℝ (f : W → ℂ) (e.symm z)) (∑ j, e.symm v j • EuclideanSpace.single j (1 : ℝ)) :=
          congrArg _ (sum (e.symm v)).symm
       _ = _ := by rw [map_sum]; simp only [hd, map_smul]

private theorem boundedPlaneJet_of_coordinate_bounds (N : ℕ) (e : W ≃L[ℝ] V(ι) × V(κ)) (he : ∀ y, e.symm (0, y) = projY y)
    (M : ((ι ⊕ κ) → ℕ) → D →L[ℂ] D)
    (hzero : M 0 = 1) (hinc : ∀ a j, M (a + Pi.single j 1) = (Dop j) * M a)
    (R : D →L[ℂ] 𝓓((⊤ : Opens V(κ)), ℂ)) (hR : ∀ f y, R f y = f (projY y))
    (f : ℕ → D) (hd : ∀ α : Ix(N), boundedOnCompacts (fun n y ↦
      R (M (fun i ↦ (α.val i).val) (f n)) y)) : boundedPlaneJet (fun n z ↦ f n (e.symm z)) N := by
  classical
  let G (a : (ι ⊕ κ) → ℕ) (n : ℕ) := M a (f n)
  have hbase (a : (ι ⊕ κ) → ℕ) (ha : ∑ j, a j ≤ N) : boundedOnCompacts (fun n y ↦ G a n (e.symm (0, y))) := by
    let α : Ix(N) := ⟨fun i ↦ ⟨a i, Nat.lt_succ_of_le ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a j))
      (Finset.mem_univ i)).trans ha)⟩, ha⟩
    have h := hd α
    simpa only [he, hR, G, α] using h
  have H (k : ℕ) : ∀ a : (ι ⊕ κ) → ℕ, k + (∑ j, a j) ≤ N →
      boundedPlaneJet (fun n z ↦ G a n (e.symm z)) k := by
    induction k with
    | zero => exact fun a ha ↦ hbase a (by omega)
    | succ k ih =>
      intro a ha
      refine ⟨hbase a (by omega), fun v ↦ ?_⟩
      change boundedPlaneJet (fun n ↦ directional v (((G a n) : W → ℂ) ∘ e.symm)) k
      simp only [fun n ↦ trace_coord_direction e (G a n) v]
      apply boundedPlaneJet_sum
      · exact fun j n ↦ ((Dop j (G a n)).contDiff.comp e.symm.contDiff).const_smul (e.symm v j)
      · intro j
        apply boundedPlaneJet_smul_const _ _ (fun n ↦ (Dop j (G a n)).contDiff.comp e.symm.contDiff)
        have hh := ih (a + Pi.single j 1) (by
          simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
            ite_true]; omega)
        have hh' := hinc a j
        dsimp only [G] at hh ⊢
        exact (congrArg (fun L : D →L[ℂ] D ↦ boundedPlaneJet (fun n z ↦ L (f n) (e.symm z)) k) hh').mp hh
  simpa [G, hzero] using H N 0 (by simp)

/-- A finite-order distribution supported on a compact part of a Euclidean coordinate plane
factors through its restricted coordinate derivatives. The coefficient distributions have
order zero and a common compact support bound. The higher derivative and restriction operators
are specified by their recurrence and their action on point evaluations. -/
public theorem exists_orderZero_coefficients (T : StrongDual ℂ D) (N : ℕ) (hN : orderBound(T, W, N))
    (hK : IsCompact (Distribution.dsupport (⇑T)))
    (hp : Distribution.dsupport (⇑T) ⊆ Set.range (fun y : V(κ) ↦ projY y))
    (M : ((ι ⊕ κ) → ℕ) → D →L[ℂ] D)
    (hzero : M 0 = 1) (hinc : ∀ a j, M (a + Pi.single j 1) = (Dop j) * M a)
    (R : D →L[ℂ] 𝓓((⊤ : Opens V(κ)), ℂ)) (hR : ∀ f y, R f y = f (projY y)) :
    ∃ (K : Compacts V(κ)) (A : Ix(N) → StrongDual ℂ 𝓓((⊤ : Opens V(κ)), ℂ)),
      (∀ α, (orderBound(A α, V(κ), 0)) ∧ Distribution.dsupport (⇑(A α)) ⊆ K) ∧
      ∀ f, T f = ∑ α, A α (R (M (fun i ↦ (α.val i).val) f)) := by
  let e := splitCoordinates (ι := ι) (κ := κ)
  have eY (y : V(κ)) : e.symm (0, y) = projY y := by ext i; cases i <;> rfl
  let J (α : Ix(N)) := R.comp (M (fun i ↦ (α.val i).val))
  obtain ⟨K, C, hb⟩ := compact_trace_estimate_of_sequences T.toLinearMap (fun α ↦ (J α).toLinearMap)
    (fun f hf ↦ distribution_bounded_on_sequence e T N hN hK (fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hp hx
      exact congrArg Prod.fst ((congrArg e (eY y)).symm.trans (e.apply_symm_apply _))) f
      (boundedPlaneJet_of_coordinate_bounds N e eY M hzero hinc R hR f hf))
  exact ⟨K, distribution_of_compact_trace_bound K (fun α ↦ (J α).toLinearMap) T.toLinearMap C hb⟩

end TraceCoords
end CoordinatePlane
end RiemannMasullo
