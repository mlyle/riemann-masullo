module

public import RiemannMasullo.AppC_LCTVS.Sec2b
import RiemannMasullo.AppC_LCTVS.Sec3a
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.TensorProduct.Bounded

/-! # Bounded sets in completed tensors with a strict LF-space -/

public section

namespace RiemannMasullo

open Bornology Filter Function Set Topology UniformSpace
open scoped TensorProduct Pointwise

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

private theorem bounded_of_inducing_image {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (f : A →L[ℂ] B) (hf : IsInducing f) (S : Set A) (h : IsVonNBounded ℂ (f '' S)) :
    IsVonNBounded ℂ S := by
  rw [isVonNBounded_iff_tendsto_smallSets_nhds, hf.nhds_eq_comap, map_zero,
    smallSets_comap_eq_comap_image, tendsto_comap_iff]
  simpa only [Function.comp_def, image_smul_set] using h.tendsto_smallSets_nhds

/-- A comparison is a bounded isomorphism if the source is exhausted by stages
embedded in the target and every bounded subset of the target lies in one stage. -/
private theorem comparison_of_bounded_stages {X Y : Type*} {S : ℕ → Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [ContinuousSMul ℂ Y]
    [∀ n, AddCommGroup (S n)] [∀ n, Module ℂ (S n)] [∀ n, TopologicalSpace (S n)]
    (C : X →L[ℂ] Y) (i : ∀ n, S n →L[ℂ] X)
    (hex : ∀ x, ∃ n, x ∈ range (i n)) (hi : ∀ n, IsEmbedding (C.comp (i n)))
    (hb : ∀ B : Set Y, IsVonNBounded ℂ B → ∃ n, B ⊆ range (C.comp (i n))) :
    Bijective C ∧ ∀ B : Set X, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  have hinj : Injective C := by
    intro x y h
    obtain ⟨n, a, ha⟩ := hex (x - y)
    have hz : C (i n a) = 0 := by rw [ha, map_sub, h, sub_self]
    have ha0 : a = 0 := (hi n).injective (hz.trans (map_zero (C.comp (i n))).symm)
    exact sub_eq_zero.mp (ha.symm.trans (ha0 ▸ map_zero (i n)))
  refine ⟨⟨hinj, fun y ↦ ?_⟩, fun B ↦ ⟨fun hB ↦ ?_, fun h ↦ h.image C⟩⟩
  · obtain ⟨n, hn⟩ := hb {y} (isVonNBounded_singleton _)
    obtain ⟨a, ha⟩ := hn (mem_singleton y)
    exact ⟨i n a, ha⟩
  · obtain ⟨n, hn⟩ := hb (C '' B) hB
    let A := (C.comp (i n)) ⁻¹' (C '' B)
    have hA : IsVonNBounded ℂ A := bounded_of_inducing_image _ (hi n).isInducing A
      (hB.subset (image_preimage_subset _ _))
    refine (hA.image (i n)).subset fun x hx ↦ ?_
    obtain ⟨a, ha⟩ := hn (mem_image_of_mem C hx)
    exact ⟨a, show (C.comp (i n)) a ∈ C '' B from ha.symm ▸ mem_image_of_mem C hx, hinj ha⟩

section Operators

variable {X D Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup D] [Module ℂ D] [UniformSpace D] [IsUniformAddGroup D]
    [PolynormableSpace ℂ D] [T2Space D] [BarrelledSpace ℂ D] [CompleteSpace D]
    [CompleteSpace (StrongDual ℂ D)]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [T2Space Y] [CompleteSpace Y]

/-- Transport the projective tensor kernel theorem along an identification of
the first factor with a strong dual. -/
private theorem projective_tensor_as_operators (b : X ≃L[ℂ] StrongDual ℂ D)
    (hn : IsNuclearTVS.{0} (StrongDual ℂ D)) :
    ∃ M : Completion (ProjectiveTensor X Y) ≃L[ℂ] (D →L[ℂ] Y),
      ∀ x y d, M (Completion.coe' (α := ProjectiveTensor X Y) (x ⊗ₜ[ℂ] y)) d = b x d • y := by
  let : T2Space (StrongDual ℂ D) := hn.1
  let : PolynormableSpace ℂ (StrongDual ℂ D) := hn.2.1
  let one := ContinuousLinearMap.id ℂ Y
  let t : ProjectiveTensor X Y ≃ₗ[ℂ] ProjectiveTensor (StrongDual ℂ D) Y :=
    TensorProduct.congr b.toLinearEquiv (LinearEquiv.refl ℂ Y)
  let T : ProjectiveTensor X Y →L[ℂ] ProjectiveTensor (StrongDual ℂ D) Y :=
    ⟨t.toLinearMap, projectiveTensorMap_continuous b.toContinuousLinearMap one⟩
  let R : ProjectiveTensor (StrongDual ℂ D) Y →L[ℂ] ProjectiveTensor X Y :=
    ⟨t.symm.toLinearMap, projectiveTensorMap_continuous b.symm.toContinuousLinearMap one⟩
  let u : ProjectiveTensor X Y ≃ᵤ ProjectiveTensor (StrongDual ℂ D) Y :=
    ⟨t.toEquiv, T.uniformContinuous, R.uniformContinuous⟩
  have hh : IsHomeomorph T.completion := (Completion.mapEquiv u).toHomeomorph.isHomeomorph
  let v := ContinuousLinearEquiv.ofIsHomeomorph
    (LinearEquiv.ofBijective T.completion.toLinearMap hh.bijective) hh
  obtain ⟨M, hM⟩ := (completedProjectiveTensorToOperators_equiv (E := D) (F := Y) hn).2
  refine ⟨v.trans M, fun x y d ↦ ?_⟩
  exact (congrArg (fun z ↦ M z d) (T.completion_apply_coe (x ⊗ₜ[ℂ] y))).trans
    (congrArg (fun L : D →L[ℂ] Y ↦ L d) (hM (b x ⊗ₜ[ℂ] y)))

end Operators

/-- The polar of the unit ball of a continuous norm in a reflexive Montel space is
bounded and is contained in no proper closed subspace of the strong dual. -/
private theorem strongDual_bounded_total_set {X : Type*} [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul ℂ X] [PolynormableSpace ℂ X]
    [T2Space X] [MontelSpace ℂ X] [PolynormableSpace ℂ (StrongDual ℂ X)]
    (p : Seminorm ℂ X) (hp : Continuous p) (hsep : ∀ x, p x = 0 → x = 0) :
    ∃ U : Set (StrongDual ℂ X), IsVonNBounded ℂ U ∧
      ∀ S : Submodule ℂ (StrongDual ℂ X), IsClosed (S : Set (StrongDual ℂ X)) → U ⊆ (S : Set (StrongDual ℂ X)) → S = ⊤ := by
  let D := StrongDual ℂ X
  let U := StrongDual.polar ℂ (p.ball 0 1)
  refine ⟨U, (isCompact_strongDual_polar (p.ball_mem_nhds hp one_pos)).isVonNBounded ℂ, ?_⟩
  intro S hS hUS
  apply top_unique
  intro φ _
  by_contra hφ
  let : LocallyConvexSpace ℝ D := (PolynormableSpace.withSeminorms ℂ D).toLocallyConvexSpace
  obtain ⟨l, hl, hz⟩ := exists_dual_eq_zero_on_submodule_of_notMem S hS hφ
  obtain ⟨x, hx⟩ := surjective_strongBidual_eval l
  obtain ⟨ψ, hψ, hnorm⟩ := exists_dual_norm_eq_seminorm p hp x
  have hψU : ψ ∈ U := fun y hy ↦ (hψ y).trans (p.mem_ball_zero.mp hy).le
  have hz' : ψ x = 0 := (congrArg (fun f : StrongDual ℂ D ↦ f ψ) hx).trans (hz ψ (hUS hψU))
  have hx0 := hsep x (hnorm.symm.trans (hz' ▸ norm_zero))
  exact hl ((congrArg (fun f : StrongDual ℂ D ↦ f φ) hx).symm.trans (hx0 ▸ map_zero φ))

/-- For a nuclear Montel Fréchet space with a continuous norm and barrelled strong dual,
tensoring a strict LF-space gives a bounded bijection between the completed inductive
and projective tensor products. -/
theorem completedTensor_comparison_bounded_of_strictLF {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace ℂ X] [T2Space X] [MontelSpace ℂ X] [BarrelledSpace ℂ (StrongDual ℂ X)]
    [AddCommGroup Y] [Module ℂ Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace ℂ Y] [CompleteSpace Y]
    (hX : IsFrechetTVS X) (hn : IsNuclearTVS.{0} X) (p : Seminorm ℂ X)
    (hp : Continuous p) (hsep : ∀ x, p x = 0 → x = 0) (hY : IsStrictLFSpace Y) :
    let TI := InductiveTensor X Y
    let TP := ProjectiveTensor X Y
    ∃ C : Completion TI →L[ℂ] Completion TP, ⇑C = @Completion.map TI _ TP _ id ∧
      Bijective C ∧ ∀ B : Set (Completion TI), IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  classical
  intro TI TP
  obtain ⟨hT₂, S, hmono, hF, hcover, htop⟩ := hY
  let D := StrongDual ℂ X
  let : ContinuousSMul ℂ X := PolynormableSpace.continuousSMul ℂ X
  let : ContinuousSMul ℂ Y := PolynormableSpace.continuousSMul ℂ Y
  let : TopologicalSpace.MetrizableSpace X := hX.choose_spec.2.1
  let : CompleteSpace X := by
    have h := hX.choose_spec.2.2
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at h
  let : BarrelledSpace ℂ X := isFrechetTVS_barrelled hX
  let : PolynormableSpace ℂ D := uniformConvergenceCLM_polynormable (F := ℂ) _ (fun _ h ↦ h)
    (by rw [sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  let : PolynormableSpace ℂ (StrongDual ℂ D) := uniformConvergenceCLM_polynormable (F := ℂ) _
    (fun _ h ↦ h) (by rw [sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  let ev := ContinuousLinearMap.applyₗ (E := X) ℂ (RingHom.id ℂ)
  have hev : IsHomeomorph ev := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_strongBidual_eval, surjective_strongBidual_eval⟩
  let b := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective ev hev.bijective) hev
  let ub : X ≃ᵤ StrongDual ℂ D := ⟨b.toEquiv, b.toContinuousLinearMap.uniformContinuous,
    b.symm.toContinuousLinearMap.uniformContinuous⟩
  let : CompleteSpace (StrongDual ℂ D) := ub.completeSpace_iff.mp inferInstance
  have hn' := nuclear_of_equiv b hn
  let : ∀ n, PolynormableSpace ℂ (S n) := fun n ↦ (hF n).choose_spec.1
  let : ∀ n, IsUniformAddGroup (S n) := fun n ↦ (S n).toAddSubgroup.isUniformAddGroup
  let : ∀ n, CompleteSpace (S n) := fun n ↦ by
    have h := (hF n).choose_spec.2.2
    rwa [IsUniformAddGroup.rightUniformSpace_eq] at h
  have hclosed (n : ℕ) : IsClosed (S n : Set Y) := (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (S n))).isClosed
  let inc (n : ℕ) := (S n).subtypeL
  let step (n : ℕ) := (S n).subtypeL.codRestrict (S (n+1)) (fun x ↦ hmono n.le_succ x.property)
  have hlim : IsInjectiveLCLimit step inc := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, htop⟩
    obtain ⟨n, hx⟩ := hcover x
    exact ⟨n, ⟨x, hx⟩, rfl⟩
  have hstep (n : ℕ) : IsClosedEmbedding (step n) :=
    IsClosedEmbedding.of_comp IsEmbedding.subtypeVal (hclosed n).isClosedEmbedding_subtypeVal
  let one := ContinuousLinearMap.id ℂ X
  let Z (n : ℕ) := ProjectiveTensor X (S n)
  let u (n : ℕ) : Z n →L[ℂ] TI := ⟨TensorProduct.map one.toLinearMap (inc n).toLinearMap,
    continuous_projectiveStage_inductiveTensor one (inc n) hX (hF n)⟩
  let C₀ : TI →L[ℂ] TP := ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩
  let C := C₀.completion
  let : PolynormableSpace ℂ (Completion TI) := polynormableSpace_completion
  let : ContinuousSMul ℂ (Completion TI) := PolynormableSpace.continuousSMul ℂ _
  let : PolynormableSpace ℂ (Completion TP) := polynormableSpace_completion
  let : ContinuousSMul ℂ (Completion TP) := PolynormableSpace.continuousSMul ℂ _
  obtain ⟨M, hM⟩ := projective_tensor_as_operators (Y := Y) b hn'
  choose Mₙ hMₙ using fun n ↦ projective_tensor_as_operators (Y := S n) b hn'
  let post (n : ℕ) : (D →L[ℂ] (S n)) →L[ℂ] (D →L[ℂ] Y) :=
    (inc n).postcompUniformConvergenceCLM {s : Set D | IsVonNBounded ℂ s}
  -- In operator coordinates the stage map is postcomposition by the inclusion.
  have hcomm (n : ℕ) : M.toContinuousLinearMap.comp (C.comp (u n).completion) =
      (post n).comp (Mₙ n).toContinuousLinearMap := by
    let L := M.toContinuousLinearMap.comp (C.comp (u n).completion)
    let R := (post n).comp (Mₙ n).toContinuousLinearMap
    let j := (Completion.toComplL : Z n →L[ℂ] Completion (Z n))
    have he : (L.comp j).toLinearMap = (R.comp j).toLinearMap := by
      refine TensorProduct.ext' fun x y ↦ ContinuousLinearMap.ext fun d ↦ ?_
      change M (C ((u n).completion (Completion.coe' (α := Z n) (x ⊗ₜ[ℂ] y)))) d =
        inc n ((Mₙ n (Completion.coe' (α := Z n) (x ⊗ₜ[ℂ] y))) d)
      have hu := (u n).completion_apply_coe (show Z n from x ⊗ₜ[ℂ] y)
      have hc := C₀.completion_apply_coe (show TI from x ⊗ₜ[ℂ] inc n y)
      exact (congrArg (fun w ↦ M (C w) d) hu).trans ((congrArg (fun w ↦ M w d) hc).trans
        ((hM x (inc n y) d).trans (((inc n).map_smul _ _).symm.trans
          (congrArg (inc n) (hMₙ n x y d).symm))))
    exact ContinuousLinearMap.ext (Completion.ext' L.continuous R.continuous (LinearMap.congr_fun he))
  refine ⟨C, rfl, comparison_of_bounded_stages C (fun n ↦ (u n).completion) ?_ ?_ ?_⟩
  · intro x
    obtain ⟨n, A, _, hA⟩ := completedInductiveTensor_bounded_projectiveStage
      (isInjectiveLCLimit_const (E := X)) hlim (fun _ ↦ IsEmbedding.id)
      (fun n ↦ (hstep n).isEmbedding) (fun _ ↦ hX) hF (fun _ ↦ nuclear_changeUniverse hn)
      (isVonNBounded_singleton (𝕜 := ℂ) x)
    obtain ⟨a, _, ha⟩ := hA.symm ▸ mem_singleton x
    exact ⟨n, a, ha⟩
  · intro n
    apply M.toHomeomorph.isEmbedding.of_comp_iff.mp
    change IsEmbedding (M.toContinuousLinearMap.comp (C.comp (u n).completion))
    rw [hcomm]
    exact (ContinuousLinearMap.isEmbedding_postcomp (inc n) IsEmbedding.subtypeVal).comp
      (Mₙ n).toHomeomorph.isEmbedding
  · intro B hB
    obtain ⟨U, hU, htotal⟩ := strongDual_bounded_total_set p hp hsep
    have hb := ContinuousLinearMap.isVonNBounded_iff.mp (hB.image M.toContinuousLinearMap) U hU
    obtain ⟨n, A, _, hA⟩ := (isVonNBounded_iff_bounded_stage hlim hstep _).mp hb
    refine ⟨n, fun z hz ↦ ?_⟩
    have hsub : U ⊆ ((S n).comap (M z).toLinearMap : Set D) := by
      intro d hd
      have hm := mem_image2_of_mem (f := fun (T : D →L[ℂ] Y) d ↦ T d)
        (mem_image_of_mem M.toContinuousLinearMap hz) hd
      obtain ⟨a, _, ha⟩ := hA.symm ▸ hm
      exact (congrArg (· ∈ S n) (show (inc n) a = (M z) d from ha)).mp a.property
    have hall := htotal ((S n).comap (M z).toLinearMap) ((hclosed n).preimage (M z).continuous) hsub
    let L := (M z).codRestrict (S n) fun d ↦ show d ∈ (S n).comap (M z).toLinearMap from
      hall.symm ▸ Submodule.mem_top
    let a := (Mₙ n).symm L
    refine ⟨a, M.injective ?_⟩
    exact (DFunLike.congr_fun (hcomm n) a).trans (congrArg (post n) ((Mₙ n).apply_symm_apply L))

end RiemannMasullo
