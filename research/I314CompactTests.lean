module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

@[expose] public noncomputable section

/-!
# Compact insertions and finite jet tests in I314

The main equivalence, `spectralStripCompacts_iff_finite_jet_inequality`, uses the
actual strip quotient and zero blocks of Theorem 10.3.2.1(1), pp. 453–455.
The right-hand side involves only finite collections of the quotient jet
functionals, arbitrary quotient vectors and convolution. No estimate of its
constant is assumed in the proof of the equivalence.
-/

open Set Function NormedSpace
open scoped BigOperators

namespace RiemannMasullo

variable {E J Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem signedBlock_eval (A : E →L[ℂ] E) (x : J → E) (L : J → StrongDual ℂ E)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) (K : Finset Z) (c : Z → ℂ)
    (v : E) (g : StrongDual ℂ E) :
    g ((∑ z ∈ K, c z • spectralConvolutionFiniteSum A x L {z} N jet) v) =
      ∑ z ∈ K, c z * ∑ m, L (jet z m) (A (g (x (jet z m)) • v)) := by
  simp [spectralConvolutionFiniteSum, Finset.smul_sum, smul_eq_mul, mul_comm, Finset.mul_sum]

/-- Scalar block traces against every rank-one operator are summable exactly when the
finite sums of complete zero blocks, with arbitrary scalar coefficients of modulus at most
one, are uniformly bounded in operator norm. -/
theorem spectralBlocks_rankOne_summable_iff [CompleteSpace E] (A : E →L[ℂ] E)
    (x : J → E) (L : J → StrongDual ℂ E) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    (∀ (v : E) (g : StrongDual ℂ E),
      Summable (fun z ↦ ∑ m, L (jet z m) (A ((g.smulRight v) (x (jet z m)))))) ↔
    ∃ C : ℝ, ∀ (K : Finset Z) (c : Z → ℂ), (∀ z, ‖c z‖ ≤ 1) →
      ‖∑ z ∈ K, c z • spectralConvolutionFiniteSum A x L {z} N jet‖ ≤ C := by
  classical
  let b (v : E) (g : StrongDual ℂ E) (z : Z) := ∑ m, L (jet z m) (A (g (x (jet z m)) • v))
  let P := Finset Z × {c : Z → ℂ // ∀ z, ‖c z‖ ≤ 1}
  let T (p : P) := ∑ z ∈ p.1, p.2.val z • spectralConvolutionFiniteSum A x L {z} N jet
  have heval (p : P) (v : E) (g : StrongDual ℂ E) :
      g (T p v) = ∑ z ∈ p.1, p.2.val z * b v g z :=
    signedBlock_eval A x L N jet p.1 p.2.val v g
  constructor
  · intro h
    have hpoint (v : E) : ∃ C, ∀ p : P, ‖T p v‖ ≤ C := by
      let G (p : P) := inclusionInDoubleDual ℂ E (T p v)
      obtain ⟨C, hC⟩ := banach_steinhaus (g := G) (fun g ↦ by
        refine ⟨∑' z, ‖b v g z‖, fun p ↦ ?_⟩
        change ‖g (T p v)‖ ≤ _
        rw [heval]
        refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z _ ↦ ?_).trans
          ((h v g).norm.sum_le_tsum p.1 (fun _ _ ↦ norm_nonneg _)))
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (p.2.property z))
      exact ⟨C, fun p ↦ ((inclusionInDoubleDualLi ℂ).norm_map (T p v)).ge.trans (hC p)⟩
    obtain ⟨C, hC⟩ := banach_steinhaus (g := T) hpoint
    exact ⟨C, fun K c hc ↦ hC (K, ⟨c, hc⟩)⟩
  · rintro ⟨C, hC⟩ v g
    let c (z : Z) : ℂ := if b v g z = 0 then 0 else (‖b v g z‖ : ℂ) / b v g z
    have hc (z : Z) : ‖c z‖ ≤ 1 := by
      by_cases hz : b v g z = 0 <;> simp [c, hz]
    have hphase (z : Z) : c z * b v g z = ‖b v g z‖ := by
      by_cases hz : b v g z = 0 <;> simp [c, hz]
    apply Summable.of_norm
    apply summable_of_sum_le (fun _ ↦ norm_nonneg _) (c := ‖g‖ * (C * ‖v‖))
    intro K
    let p : P := (K, ⟨c, hc⟩)
    have hp : ‖g (T p v)‖ = ∑ z ∈ K, ‖b v g z‖ := by
      rw [heval]
      change ‖∑ z ∈ K, c z * b v g z‖ = _
      simp only [hphase, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    change ∑ z ∈ K, ‖b v g z‖ ≤ _
    exact hp ▸ (g.le_opNorm (T p v)).trans (mul_le_mul_of_nonneg_left
      (((T p).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hC K c hc) (norm_nonneg _))) (norm_nonneg _))

#print axioms spectralBlocks_rankOne_summable_iff

open Classical in
private theorem signedBlock_coordinate (A : E →L[ℂ] E) (x : J → E) (L : J → StrongDual ℂ E)
    (hb : IsSpectralMarkushevichBasis x L) (N : Z → ℕ) (e : ((z : Z) × Fin (N z)) ≃ J)
    (K : Finset Z) (c : Z → ℂ) (i : J) :
    (L i).comp (∑ z ∈ K, c z • spectralConvolutionFiniteSum A x L {z} N (fun z m ↦ e ⟨z,m⟩)) =
      (if (e.symm i).1 ∈ K then c (e.symm i).1 else 0) • (L i).comp A := by
  obtain ⟨⟨w,n⟩,rfl⟩ := e.surjective i
  ext v
  have hcoord (z : Z) : L (e ⟨w,n⟩) (spectralConvolutionFiniteSum A x L {z} N (fun z m ↦ e ⟨z,m⟩) v)
      = if w = z then L (e ⟨w,n⟩) (A v) else 0 := by
    simp only [spectralConvolutionFiniteSum, Finset.sum_singleton, sum_apply, map_sum,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
    by_cases hz : w = z
    · subst z
      rw [ite_eq_left rfl, Finset.sum_eq_single n]
      · rw [hb.1, mul_one]
      · intro k _ hk
        rw [hb.2.1 _ _ (fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (e.injective h)).2)), mul_zero]
      · simp
    · rw [ite_eq_right hz]
      apply Finset.sum_eq_zero
      intro k _
      rw [hb.2.1 _ _ (fun h ↦ hz (congrArg Sigma.fst (e.injective h)).symm), mul_zero]
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum, map_smul, smul_apply, hcoord,
    e.symm_apply_apply, smul_eq_mul]
  simp [mul_ite, Finset.sum_ite_eq, ite_mul]

open Classical in
/-- Uniform finite-jet inequalities equivalent to the absence of a rank-one witness.
The inequality uses only the realized dual jets and their convolutions. -/
theorem spectralBlocks_rankOne_iff_dualJet_bound [CompleteSpace E] (A : E →L[ℂ] E)
    (x : J → E) (L : J → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x L)
    (N : Z → ℕ) (e : ((z : Z) × Fin (N z)) ≃ J) :
    (∀ (v : E) (g : StrongDual ℂ E),
      Summable (fun z ↦ ∑ m, L (e ⟨z,m⟩) (A ((g.smulRight v) (x (e ⟨z,m⟩)))))) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Finset Z) (c : Z → ℂ), (∀ z, ‖c z‖ ≤ 1) →
      ∀ (I : Finset J) (d : J → ℂ),
        ‖∑ i ∈ I, (d i * (if (e.symm i).1 ∈ K then c (e.symm i).1 else 0)) • (L i).comp A‖ ≤
          C * ‖∑ i ∈ I, d i • L i‖ := by
  classical
  rw [spectralBlocks_rankOne_summable_iff]
  let T (K : Finset Z) (c : Z → ℂ) := ∑ z ∈ K, c z • spectralConvolutionFiniteSum A x L {z} N (fun z m ↦ e ⟨z,m⟩)
  have hsum (K : Finset Z) (c : Z → ℂ) (I : Finset J) (d : J → ℂ) :
      (∑ i ∈ I, d i • L i).comp (T K c) =
        ∑ i ∈ I, (d i * (if (e.symm i).1 ∈ K then c (e.symm i).1 else 0)) • (L i).comp A := by
    let pre : StrongDual ℂ E →L[ℂ] StrongDual ℂ E := (T K c).precomp ℂ
    change pre _ = _
    simp only [map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro i hi
    change d i • (L i).comp (T K c) = _
    rw [signedBlock_coordinate A x L hb N e, smul_smul]
  constructor
  · rintro ⟨C, hC⟩
    have hzero := hC ∅ (fun _ ↦ (0 : ℂ)) (fun _ ↦ by simp)
    refine ⟨C, by simpa using hzero, fun K c hc I d ↦ ?_⟩
    rw [← hsum]
    calc
      _ ≤ ‖∑ i ∈ I, d i • L i‖ * ‖T K c‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖∑ i ∈ I, d i • L i‖ * C := mul_le_mul_of_nonneg_left (hC K c hc) (norm_nonneg _)
      _ = _ := mul_comm _ _
  · rintro ⟨C, hC, h⟩
    refine ⟨C, fun K c hc ↦ ?_⟩
    have hd (g : StrongDual ℂ E) : ‖g.comp (T K c)‖ ≤ C * ‖g‖ := by
      let V := {g : StrongDual ℂ E | ‖g.comp (T K c)‖ ≤ C * ‖g‖}
      have hclosed : IsClosed V :=
        isClosed_le ((T K c).precomp (τ := RingHom.id ℂ) ℂ).continuous.norm (continuous_const.mul continuous_norm)
      apply closure_minimal (t := V) ?_ hclosed (hb.2.2.2 g)
      intro G hG
      obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
      change ‖(∑ i ∈ d.support, d i • L i).comp (T K c)‖ ≤ _
      rw [hsum]
      exact h K c hc d.support d
    apply (T K c).opNorm_le_bound hC
    intro v
    apply norm_le_dual_bound ℂ _ (mul_nonneg hC (norm_nonneg _))
    intro g
    calc
      _ ≤ ‖g.comp (T K c)‖ * ‖v‖ := (g.comp (T K c)).le_opNorm _
      _ ≤ (C * ‖g‖) * ‖v‖ := mul_le_mul_of_nonneg_right (hd g) (norm_nonneg _)
      _ = _ := by ring

#print axioms spectralBlocks_rankOne_iff_dualJet_bound

/-- Every compact insertion has an absolutely summable zero-block trace exactly when all
bounded insertions obey a single variation bound, with the operator norm on the right. -/
theorem spectralBlocks_compact_iff_bounded_variation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    (∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z ↦ ∑ m, L (jet z m) (A (U.val (x (jet z m)))))) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : H →L[ℂ] H) (K : Finset Z),
      ∑ z ∈ K, ‖∑ m, L (jet z m) (A (U (x (jet z m))))‖ ≤ C * ‖U‖ := by
  classical
  let b (U : H →L[ℂ] H) (z : Z) := ∑ m, L (jet z m) (A (U (x (jet z m))))
  let D := compactOperator (RingHom.id ℂ) H H
  constructor
  · intro h
    let : CompleteSpace D := (show IsClosed (D : Set (H →L[ℂ] H)) from
      isClosed_setOfPred_isCompactOperator).completeSpace_coe
    let ev (j : J) := ((L j).comp A).comp ((ContinuousLinearMap.apply ℂ H (x j)).comp D.subtypeL)
    let P := Finset Z × {c : Z → ℂ // ∀ z, ‖c z‖ ≤ 1}
    let B (p : P) := ∑ z ∈ p.1, p.2.val z • ∑ m, ev (jet z m)
    have hB (p : P) (U : D) : B p U = ∑ z ∈ p.1, p.2.val z * b U.val z := by
      simp only [B, ev, sum_apply, smul_apply]
      rfl
    obtain ⟨C, hC⟩ := banach_steinhaus (g := B) (fun U ↦ by
      refine ⟨∑' z, ‖b U.val z‖, fun p ↦ ?_⟩
      rw [hB]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun z _ ↦ ?_).trans
        ((h U).norm.sum_le_tsum p.1 (fun _ _ ↦ norm_nonneg _)))
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (p.2.property z))
    let p₀ : P := (∅, ⟨fun _ ↦ 0, fun _ ↦ by simp⟩)
    have hC₀ : 0 ≤ C := (norm_nonneg (B p₀)).trans (hC p₀)
    refine ⟨C, hC₀, fun U K ↦ ?_⟩
    let i := (z : K) × Fin (N z.val)
    let v (j : i) := x (jet j.1.val j.2)
    let W := Submodule.span ℂ (range v)
    let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (finite_range v)
    let U' : D := ⟨U.comp W.starProjection,
      (isCompactOperator_of_locallyCompactSpace_rng (U.comp W.subtypeL)).comp_clm W.orthogonalProjectionOnto⟩
    have hnorm : ‖U'‖ ≤ ‖U‖ := (U.opNorm_comp_le W.starProjection).trans
      (mul_le_of_le_one_right (norm_nonneg _) W.starProjection_norm_le)
    have hb (z : Z) (hz : z ∈ K) : b U'.val z = b U z := by
      apply Finset.sum_congr rfl
      intro m hm
      have hw : x (jet z m) ∈ W := Submodule.subset_span ⟨⟨⟨z, hz⟩, m⟩, rfl⟩
      change L _ (A (U (W.starProjection (x (jet z m))))) = _
      rw [Submodule.starProjection_eq_self_iff.mpr hw]
    let c (z : Z) : ℂ := if b U z = 0 then 0 else (‖b U z‖ : ℂ) / b U z
    have hc (z : Z) : ‖c z‖ ≤ 1 := by by_cases hz : b U z = 0 <;> simp [c, hz]
    let p : P := (K, ⟨c, hc⟩)
    have heq : ‖B p U'‖ = ∑ z ∈ K, ‖b U z‖ := by
      rw [hB]
      change ‖∑ z ∈ K, c z * b U'.val z‖ = _
      have hs : ∑ z ∈ K, c z * b U'.val z = ∑ z ∈ K, (‖b U z‖ : ℂ) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hb z hz]
        by_cases hzero : b U z = 0 <;> simp [c, hzero]
      rw [hs, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    change ∑ z ∈ K, ‖b U z‖ ≤ _
    rw [← heq]
    exact ((B p).le_opNorm U').trans (mul_le_mul (hC p) hnorm (norm_nonneg _) hC₀)
  · rintro ⟨C, _, h⟩ U
    exact (summable_of_sum_le (fun z ↦ norm_nonneg (b U.val z)) (h U.val)).of_norm

#print axioms spectralBlocks_compact_iff_bounded_variation


open Classical in
/-- A finite inequality involving only the realized dual jets is equivalent to summability
after every compact insertion. Indices in the same zero block are added before taking a
norm. Each right-hand operator is an explicit finite sum of rank-one operators. -/
theorem spectralBlocks_compact_iff_finite_dualJet_inequality
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x L)
    (N : Z → ℕ) (e : ((z : Z) × Fin (N z)) ≃ J) :
    (∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z ↦ ∑ m, L (e ⟨z,m⟩) (A (U.val (x (e ⟨z,m⟩)))))) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Finset Z) (I : Finset (J × H)) (d : J × H → ℂ),
      ∑ z ∈ K, ‖∑ p ∈ I, d p * (if (e.symm p.1).1 = z then L p.1 (A p.2) else 0)‖ ≤
        C * ‖∑ p ∈ I, d p • (L p.1).smulRight p.2‖ := by
  classical
  let jet (z : Z) (m : Fin (N z)) := e ⟨z,m⟩
  let b (z : Z) : (H →L[ℂ] H) →L[ℂ] ℂ := ∑ m : Fin (N z), ((L (jet z m)).comp A).comp
    (ContinuousLinearMap.apply ℂ H (x (jet z m)))
  let t (p : J × H) := (L p.1).smulRight p.2
  have hbval (z : Z) (U : H →L[ℂ] H) : b z U = ∑ m, L (jet z m) (A (U (x (jet z m)))) := by
    simp only [b, sum_apply]
    rfl
  have hterm (z : Z) (p : J × H) : b z (t p) = if (e.symm p.1).1 = z then L p.1 (A p.2) else 0 := by
    have h := signedBlock_eval A x L N jet {z} (fun _ ↦ 1) p.2 (L p.1)
    have g := congrArg (fun f : StrongDual ℂ H ↦ f p.2) (signedBlock_coordinate A x L hb N e {z} (fun _ ↦ 1) p.1)
    simp only [Finset.sum_singleton, one_smul, one_mul] at h
    rw [hbval]
    change (∑ m, L (jet z m) (A (L p.1 (x (jet z m)) • p.2))) = _
    rw [← h]
    by_cases hrow : (e.symm p.1).1 = z <;> simpa [jet, hrow] using g
  rw [spectralBlocks_compact_iff_bounded_variation]
  have heval (I : Finset (J × H)) (d : J × H → ℂ) (z : Z) :
      b z (∑ p ∈ I, d p • t p) = ∑ p ∈ I, d p * (if (e.symm p.1).1 = z then L p.1 (A p.2) else 0) := by
    simp only [map_sum, map_smul, smul_eq_mul, hterm]
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun K I d ↦ ?_⟩
    simpa only [← heval, hbval] using h (∑ p ∈ I, d p • t p) K
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun U K ↦ ?_⟩
    let V := Submodule.span ℂ (range t)
    let Y := V.topologicalClosure
    have hfinite (T : H →L[ℂ] H) (hT : T ∈ Y) : ∑ z ∈ K, ‖b z T‖ ≤ C * ‖T‖ := by
      let S := {T : H →L[ℂ] H | ∑ z ∈ K, ‖b z T‖ ≤ C*‖T‖}
      have hclosed : IsClosed S := isClosed_le
        (continuous_finsetSum K fun z _ ↦ (b z).continuous.norm) (continuous_const.mul continuous_norm)
      apply closure_minimal (t := S) ?_ hclosed hT
      intro T hT
      obtain ⟨d, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hT
      change ∑ z ∈ K, ‖b z (∑ p ∈ d.support, d p • t p)‖ ≤ _
      simpa only [heval, Finsupp.sum, t] using h K d.support d
    have hrank (g : StrongDual ℂ H) (y : H) : g.smulRight y ∈ Y := by
      let B : StrongDual ℂ H →L[ℂ] (H →L[ℂ] H) := (ContinuousLinearMap.smulRightL ℂ H H).flip y
      have hspan : Submodule.span ℂ (range L) ≤ V.comap B.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        exact Submodule.subset_span ⟨(j,y),rfl⟩
      have hclosed : IsClosed (B ⁻¹' (Y : Set (H →L[ℂ] H))) := V.isClosed_topologicalClosure.preimage B.continuous
      have hsub : (Submodule.span ℂ (range L) : Set (StrongDual ℂ H)) ⊆ B ⁻¹' (Y : Set (H →L[ℂ] H)) :=
        fun f hf ↦ V.le_topologicalClosure (hspan hf)
      exact closure_minimal hsub hclosed (hb.2.2.2 g)
    let i := (z : K) × Fin (N z.val)
    let w (p : i) := x (jet p.1.val p.2)
    let W := Submodule.span ℂ (range w)
    let : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (finite_range w)
    let T := U.comp W.starProjection
    have hT : T ∈ Y := by
      let basis := Module.finBasis ℂ W
      let g (k : Fin (Module.finrank ℂ W)) := (basis.coord k).toContinuousLinearMap.comp W.orthogonalProjectionOnto
      let y (k : Fin (Module.finrank ℂ W)) := U (basis k)
      have he : T = ∑ k, (g k).smulRight (y k) := by
        ext v
        change U (W.orthogonalProjectionOnto v).val = _
        have h := congrArg (fun z : W ↦ U z.val) (basis.sum_repr (W.orthogonalProjectionOnto v))
        simpa only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, sum_apply,
          ContinuousLinearMap.smulRight_apply, g, y, ContinuousLinearMap.comp_apply,
          LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply] using h.symm
      rw [he]
      exact Y.sum_mem fun k _ ↦ hrank (g k) (y k)
    have hw (z : Z) (hz : z ∈ K) : b z T = b z U := by
      rw [hbval, hbval]
      apply Finset.sum_congr rfl
      intro m _
      have hm : x (jet z m) ∈ W := Submodule.subset_span ⟨⟨⟨z,hz⟩,m⟩,rfl⟩
      change L _ (A (U (W.starProjection (x (jet z m))))) = _
      rw [Submodule.starProjection_eq_self_iff.mpr hm]
    have hnorm : ‖T‖ ≤ ‖U‖ := (U.opNorm_comp_le W.starProjection).trans
      (mul_le_of_le_one_right (norm_nonneg _) W.starProjection_norm_le)
    simpa only [hbval, jet] using (Finset.sum_congr rfl fun z hz ↦ congrArg norm (hw z hz)).symm.le.trans
      ((hfinite T hT).trans (mul_le_mul_of_nonneg_left hnorm hC))
#print axioms spectralBlocks_compact_iff_finite_dualJet_inequality

/-- A bounded insertion that violates block summability implies a single compact insertion
that violates it. The compact witness can depend on the offending bounded operator. -/
theorem spectralBlocks_exists_compact_witness
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (U : H →L[ℂ] H)
    (hU : ¬ Summable (fun z ↦ ∑ m, L (jet z m) (A (U (x (jet z m)))))) :
    ∃ V : compactOperator (RingHom.id ℂ) H H,
      ¬ Summable (fun z ↦ ∑ m, L (jet z m) (A (V.val (x (jet z m))))) := by
  by_contra! h
  obtain ⟨C, _, hC⟩ := (spectralBlocks_compact_iff_bounded_variation A x L N jet).mp h
  exact hU (summable_of_sum_le (fun _ ↦ norm_nonneg _) (hC U)).of_norm

/-- Unbounded operator norms already give one rank-one compact witness. -/
theorem spectralBlocks_exists_rankOne_witness [CompleteSpace E]
    (A : E →L[ℂ] E) (x : J → E) (L : J → StrongDual ℂ E) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J)
    (hunbounded : ¬ ∃ C : ℝ, ∀ (K : Finset Z) (c : Z → ℂ), (∀ z, ‖c z‖ ≤ 1) →
      ‖∑ z ∈ K, c z • spectralConvolutionFiniteSum A x L {z} N jet‖ ≤ C) :
    ∃ (v : E) (g : StrongDual ℂ E), IsCompactOperator (g.smulRight v) ∧
      ¬ Summable (fun z ↦ ∑ m, L (jet z m) (A ((g.smulRight v) (x (jet z m))))) := by
  have h := (spectralBlocks_rankOne_summable_iff A x L N jet).not.mpr hunbounded
  push Not at h
  obtain ⟨v, g, h⟩ := h
  exact ⟨v, g, (isCompactOperator_of_locallyCompactSpace_rng
    ((ContinuousLinearMap.id ℂ ℂ).smulRight v)).comp_clm g, h⟩
#print axioms spectralBlocks_exists_compact_witness
#print axioms spectralBlocks_exists_rankOne_witness

section ActualStrip

open NumberField
open scoped NNReal NumberField.AdeleRing

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] (a : ℝ)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

open Classical in
/-- The finite-jet inequality for precisely the compact insertion and complete zero
blocks of Theorem 10.3.2.1(1), pp. 453–455. -/
theorem spectralStripCompacts_iff_finite_jet_inequality
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice (F := F) χ)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex χ a α s → Q(a, hStrip(hα), hs₀(hs)))
    (L : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hStrip(hα), hs₀(hs)))
    (hb : IsSpectralMarkushevichBasis x L)
    (_hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs) (L j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs₀(hs) j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let H := Q(a, hStrip(hα), hs₀(hs))
    let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
    let jet (z : Z(χ, α)) (m : Fin (N(χ, α, s, z))) : SpectralStripJetIndex χ a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    let row (j : SpectralStripJetIndex χ a α s) : Z(χ, α) :=
      ⟨(j.val.1,j.val.2.1,j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
    (∀ U : compactOperator (RingHom.id ℂ) H H,
      Summable (fun z : Z(χ, α) ↦ ∑ m, L (jet z m) (A (U.val (x (jet z m)))))) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Finset (Z(χ, α)))
      (I : Finset (SpectralStripJetIndex χ a α s × H)) (d : SpectralStripJetIndex χ a α s × H → ℂ),
      ∑ z ∈ K, ‖∑ p ∈ I, d p * (@ite ℂ (row p.1 = z) (Classical.propDecidable _) (L p.1 (A p.2)) 0)‖ ≤
        C * ‖∑ p ∈ I, d p • (L p.1).smulRight p.2‖ := by
  intro H A jet row
  let i (j : SpectralStripJetIndex χ a α s) : (z : Z(χ, α)) × Fin (N(χ, α, s, z)) :=
    ⟨row j, ⟨j.val.2.2.2, j.property⟩⟩
  let e : ((z : Z(χ, α)) × Fin (N(χ, α, s, z))) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ jet p.1 p.2, i, fun _ ↦ rfl, fun _ ↦ rfl⟩
  exact spectralBlocks_compact_iff_finite_dualJet_inequality A x L hb _ e
#print axioms spectralStripCompacts_iff_finite_jet_inequality

end ActualStrip

end RiemannMasullo
