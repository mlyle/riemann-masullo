module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.Analysis.PSeries

/-!
# Trace class by finite sets of surviving moments

Finite moment support bounds the dimension of the range of a cutoff. Summable
approximation errors weighted by the dimension of the next cutoff then imply
trace class. The cutoffs can omit whole zero blocks simultaneously.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped Topology

namespace RiemannMasullo.StripNuclearity

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- If the moments separate points on the range of an operator, the number of
potentially nonzero moments bounds its rank. -/
theorem rank_le_of_finite_moments (Λ : ι → StrongDual ℂ H)
    (K : Finset ι) (B : H →L[ℂ] H)
    (hsep : ∀ v ∈ B.toLinearMap.range, (∀ j, Λ j v = 0) → v = 0)
    (hB : ∀ j ∉ K, ∀ v, Λ j (B v) = 0) :
    Module.rank ℂ B.toLinearMap.range ≤ (K.card : Cardinal) := by
  let V := B.toLinearMap.range
  let e : V →ₗ[ℂ] (K → ℂ) := LinearMap.pi fun j ↦ (Λ j.val).toLinearMap.comp V.subtype
  have he : Injective e := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro v hv
    apply Subtype.ext
    apply hsep v.val v.property
    intro j
    by_cases hj : j ∈ K
    · exact congrFun hv ⟨j, hj⟩
    · obtain ⟨x, hx⟩ := v.property
      rw [← hx]
      exact hB j hj x))
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective e he
  have h := LinearMap.finrank_le_finrank_of_injective he
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  change Module.rank ℂ V ≤ _
  rw [← Module.finrank_eq_rank]
  exact_mod_cast h

/-- Rank-bounded approximants with errors summable after multiplication by the
next rank bound plus one give a trace-class operator. The rank bounds may grow
at an irregular rate or eventually stabilize. -/
theorem nuclear_of_rank_cutoffs (A : H →L[ℂ] H) (B : ℕ → H →L[ℂ] H)
    (r : ℕ → ℕ) (hr : Monotone r)
    (hrank : ∀ n, Module.rank ℂ (B n).toLinearMap.range ≤ (r n : Cardinal))
    (herr : Summable fun n : ℕ ↦ ((r (n + 1) : ℝ) + 1) * ‖B n - A‖) :
    IsNuclearOperator A := by
  let errors (n : ℕ) : Set ℝ := {x | ∃ S : H →L[ℂ] H,
    Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ x = ‖S - A‖}
  have below (n : ℕ) : BddBelow (errors n) :=
    ⟨0, by rintro _ ⟨S, -, rfl⟩; exact norm_nonneg _⟩
  have nonempty (n : ℕ) : (errors n).Nonempty := ⟨_, 0, by simp, rfl⟩
  have mono : Antitone (approximationNumber A) := by
    intro n k h
    apply csInf_le_csInf (below k) (nonempty n)
    rintro x ⟨S, hS, hx⟩
    exact ⟨S, hS.trans (by exact_mod_cast h), hx⟩
  have hn (n : ℕ) : 0 ≤ approximationNumber A n :=
    Real.sInf_nonneg (by rintro _ ⟨S, -, rfl⟩; exact norm_nonneg _)
  have he (n : ℕ) : approximationNumber A (r n) ≤ ‖B n - A‖ :=
    csInf_le (below _) ⟨B n, hrank n, rfl⟩
  have hnorm : Summable fun n ↦ ‖B n - A‖ :=
    herr.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦
      le_mul_of_one_le_left (norm_nonneg _) (by linarith [Nat.cast_nonneg (α := ℝ) (r (n + 1))]))
  have hc : IsCompactOperator A := by
    apply isCompactOperator_of_tendsto (tendsto_iff_norm_sub_tendsto_zero.mpr hnorm.tendsto_atTop_zero)
    apply Eventually.of_forall
    intro n
    let V := (B n).toLinearMap.range
    let : FiniteDimensional ℂ V :=
      Module.rank_lt_aleph0_iff.mp ((hrank n).trans_lt Cardinal.natCast_lt_aleph0)
    let : ProperSpace V := FiniteDimensional.proper_rclike ℂ V
    let S : H →L[ℂ] V := (B n).codRestrict V fun x ↦ LinearMap.mem_range_self _ x
    exact (isCompactOperator_of_locallyCompactSpace_dom S).continuous_comp continuous_subtype_val
  apply (mem_traceClassOperators_iff_isNuclearOperator A).mp
  refine ⟨hc, ?_⟩
  simp only [Real.rpow_one]
  let u (n : ℕ) := r n + n + 1
  have hu : Monotone u := fun m n h ↦ by dsimp [u]; have := hr h; omega
  have hinc (k : ℕ) : u (k + 1) - u k ≤ r (k + 1) + 1 := by dsimp [u]; omega
  have hstep (k : ℕ) : (u (k + 1) - u k) • approximationNumber A (u k) ≤
      ((r (k + 1) : ℝ) + 1) * ‖B k - A‖ := by
    rw [nsmul_eq_mul]
    exact mul_le_mul (by exact_mod_cast hinc k)
      ((mono (by dsimp [u]; omega : r k ≤ u k)).trans (he k)) (hn _) (by positivity)
  apply summable_of_sum_range_le hn
    (c := (∑ k ∈ Finset.range (u 0), approximationNumber A k) +
      ∑' n, ((r (n + 1) : ℝ) + 1) * ‖B n - A‖)
  intro n
  calc
    _ ≤ ∑ k ∈ Finset.range (u n), approximationNumber A k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by dsimp [u]; omega))
        (fun k _ _ ↦ hn k)
    _ ≤ _ := Finset.le_sum_schlomilch (fun _ _ _ h ↦ mono h) (fun k ↦ by dsimp [u]; omega) hu n
    _ ≤ _ := add_le_add_right ((Finset.sum_le_sum (fun k _ ↦ hstep k)).trans
      (herr.sum_le_tsum (Finset.range n) (fun k _ ↦ by positivity))) _

/-- A finite rank bound also bounds the rank of the Hilbert adjoint, by factoring
the operator and its adjoint through the range of the original operator. -/
theorem rank_adjoint_le_of_rank_le (B : H →L[ℂ] H) {r : ℕ}
    (hr : Module.rank ℂ B.toLinearMap.range ≤ (r : Cardinal)) :
    Module.rank ℂ B.adjoint.toLinearMap.range ≤ (r : Cardinal) := by
  let V := B.toLinearMap.range
  let : FiniteDimensional ℂ V :=
    Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.natCast_lt_aleph0)
  let : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  have hf : V.subtypeL.comp B.rangeRestrict = B := rfl
  rw [show B.adjoint = B.rangeRestrict.adjoint.comp V.subtypeL.adjoint by
    rw [← ContinuousLinearMap.adjoint_comp, hf]]
  exact (LinearMap.rank_comp_le_left _ _).trans (B.rangeRestrict.adjoint.toLinearMap.rank_le_domain.trans hr)

/-- Cut off moments of the adjoint before estimating the operator on the right
of a projection. Moment separation is only needed on the projection range. -/
theorem nuclear_comp_projection_of_moment_cutoffs (A P : H →L[ℂ] H) (hP : IsSelfAdjoint P)
    (Λ : ι → StrongDual ℂ H)
    (hsep : ∀ v ∈ P.toLinearMap.range, (∀ j, Λ j v = 0) → v = 0)
    (U : ℕ → H →L[ℂ] H) (K : ℕ → Finset ι) (hK : Monotone K)
    (hvan : ∀ n j, j ∉ K n → ∀ v, Λ j (P (U n v)) = 0)
    (herr : Summable fun n : ℕ ↦ (((K (n + 1)).card : ℝ) + 1) *
      ‖(U n - ContinuousLinearMap.id ℂ H).comp A.adjoint‖) :
    IsNuclearOperator (A.comp P) := by
  let B (n : ℕ) := (P.comp ((U n).comp A.adjoint)).adjoint
  apply nuclear_of_rank_cutoffs (A.comp P) B (fun n ↦ (K n).card)
    (fun m n h ↦ Finset.card_le_card (hK h))
  · intro n
    apply rank_adjoint_le_of_rank_le
    apply rank_le_of_finite_moments Λ (K n) _
    · rintro v ⟨x, rfl⟩ h
      exact hsep _ (LinearMap.mem_range_self _ _) h
    · exact fun j hj x ↦ hvan n j hj (A.adjoint x)
  · refine (herr.mul_left ‖P‖).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
    have hdiff : B n - A.comp P = (P.comp ((U n - ContinuousLinearMap.id ℂ H).comp A.adjoint)).adjoint := by
      simp [B, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.adjoint_comp, hP.adjoint_eq]
    rw [hdiff, LinearIsometryEquiv.norm_map, ← mul_left_comm]
    exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (by positivity)

end RiemannMasullo.StripNuclearity
