module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! # Absolute summability for a defining family of seminorms -/

public section

open Filter Topology

namespace RiemannMasullo

/-- In a complete locally convex space it suffices to sum each defining
seminorm. This is the finite-tail argument used in Ch05_ThetaZSpaces/Sec3a. -/
theorem summable_of_summable_seminorms {𝕜 X ι κ : Type*} [NormedField 𝕜] [AddCommGroup X]
    [Module 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X]
    {p : SeminormFamily 𝕜 X ι} (hp : WithSeminorms p) (f : κ → X)
    (hs : ∀ i, Summable fun j ↦ p i (f j)) : Summable f := by
  classical
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_sum_vanishing]
  intro e he
  obtain ⟨⟨I, t⟩, ht, hsub⟩ := hp.hasBasis_zero_ball.mem_iff.mp he
  have hv (i : ι) : ∃ s : Finset κ, ∀ a : Finset κ, Disjoint a s → ∑ j ∈ a, p i (f j) < t := by
    obtain ⟨s, hs⟩ := (hs i).vanishing (Metric.ball_mem_nhds (0 : ℝ) ht)
    refine ⟨s, fun a ha ↦ ?_⟩
    have h := hs a ha
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans_lt h
  choose s hs using hv
  refine ⟨I.biUnion s, fun a ha ↦ hsub ?_⟩
  rw [Seminorm.mem_ball_zero]
  refine Seminorm.finset_sup_apply_lt ht fun i hi ↦ ?_
  exact (Finset.le_sum_of_subadditive (p i) (map_zero _).le (map_add_le_add _) _ _).trans_lt
    (hs i a (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem s hi) ha))

end RiemannMasullo
