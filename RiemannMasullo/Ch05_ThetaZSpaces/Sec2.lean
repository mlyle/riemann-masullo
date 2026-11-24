module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1d
import all RiemannMasullo.AppA_AlgebraicNT.Sec1
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongDualPrecompact
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.InfiniteAdeleRing
import all RiemannMasullo.AppC_LCTVS.Sec1
import RiemannMasullo.AppC_LCTVS.Sec2b
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.StrongDualQuotient
import RiemannMasullo.ForMathlib.Analysis.Normed.Group.InfiniteSum
import RiemannMasullo.ForMathlib.Topology.Algebra.Valued.LocallyConstant

/-! # Structure Theorem I for adelic theta spaces

Masullo, §5.2.1–5.2.2, pp. 230–232. The finite sets index the finite places.
Every S-adelic space below includes all archimedean places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped NumberField.AdeleRing NNReal

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
variable {S T U : Finset (HeightOneSpectrum (𝓞 F))}

local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "K𝔽" => LinearMap.ker (adelicThetaLinearMap F)
local notation "Kₛ(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "J₁(" S ")" => MonoidHom.ker (sIdeleQuotientNorm F S)

open scoped TensorProduct in
private theorem sAdeleSchwartz_continuous_tmul_fixed {A V : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] (t : V) :
    @Continuous A (InductiveTensor A V) _ _ (fun b ↦ b ⊗ₜ[ℂ] t) := by
  let p := fun q : {q : Seminorm ℂ (A ⊗[ℂ] V) //
    (∀ a : A, Continuous fun b : V ↦ q (a ⊗ₜ[ℂ] b)) ∧
    (∀ b : V, Continuous fun a : A ↦ q (a ⊗ₜ[ℂ] b))} ↦ q.val
  have h := withGeneratingSeminorms_spec (A ⊗[ℂ] V) p
  exact h.continuous_of_continuous_comp ((TensorProduct.mk ℂ A V).flip t) (fun q ↦ q.property.2 t)

private theorem sAdeleSchwartz_compact_support_product (f : ℬₛ(S))
    (a : InfiniteAdeleRing F → ℂ) (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F)))
    (ha : HasCompactSupport a)
    (he : ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
      a x.1 * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w))) : HasCompactSupport f.val := by
  let K : Set (SAdeleRing F S) :=
    tsupport a ×ˢ (Set.pi Set.univ (fun w : S ↦ tsupport (fun x : w.val.adicCompletion F ↦
      g w (Multiplicative.ofAdd x))))
  have hG (w : S) : HasCompactSupport (fun x : w.val.adicCompletion F ↦ g w (Multiplicative.ofAdd x)) :=
    ((mem_finitePlaceSchwartz_iff F w.val _).mp ⟨g w, fun _ ↦ rfl⟩).2
  have hK : IsCompact K := ha.prod (isCompact_univ_pi fun w ↦ hG w)
  refine HasCompactSupport.intro (hK.image continuous_ofAdd) (fun x hx ↦ ?_)
  change f x = 0
  rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, he]
  by_contra hn
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hn
  apply hx
  refine ⟨x.toAdd, ⟨subset_tsupport _ h₁, fun w _ ↦ subset_tsupport _ ?_⟩, rfl⟩
  intro hz
  exact h₂ (Finset.prod_eq_zero (Finset.mem_univ w) hz)

open scoped Classical in
private theorem sAdeleSchwartz_archimedean_compact_seq (c : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) :
    ∃ u : ℕ → SchwartzMap (mixedEmbedding.mixedSpace F) ℂ,
      (∀ n, HasCompactSupport (u n)) ∧ Tendsto u atTop (𝓝 c) := by
  let C : Set (SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) := {b | HasCompactSupport b}
  have hcC : c ∈ closure C := SchwartzMap.dense_hasCompactSupport c
  exact mem_closure_iff_seq_limit.mp hcC

open scoped Classical TensorProduct in
private theorem sAdeleSchwartz_pure_compact_support_seq
    (J : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ ≃L[ℂ]
      SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (hJ : ∀ f x, J f (Multiplicative.ofAdd x) = f (InfiniteAdeleRing.ringEquiv_mixedSpace F x))
    (e : InductiveTensor (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (FinestLocallyConvex (⨂[ℂ] w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))))
      ≃L[ℂ] ℬₛ(S))
    (he : ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F)))
      (x : SAdeleRing F S),
      e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd x) =
        a (Multiplicative.ofAdd x.1) * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w)))
    (c : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
    ∃ u : ℕ → ℬₛ(S), (∀ n, HasCompactSupport (u n).val) ∧
      Tendsto u atTop (𝓝 (e (J c ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)))) := by
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  let h := sAdeleSchwartz_archimedean_compact_seq (F := F) c
  let u := h.choose
  have hu := h.choose_spec.1
  have hut := h.choose_spec.2
  let t : V := ⨂ₜ[ℂ] w, g w
  have htmul := sAdeleSchwartz_continuous_tmul_fixed (A := A) (V := V) t
  let M := fun b : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ ↦ e (J b ⊗ₜ[ℂ] t)
  have hM : Continuous M := e.continuous.comp (htmul.comp J.continuous)
  refine ⟨M ∘ u, fun n ↦ ?_, ?_⟩
  · change HasCompactSupport (M (u n)).val
    let a (x : InfiniteAdeleRing F) := u n (InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    have ha : HasCompactSupport a := (hu n).comp_homeomorph (infiniteAdeleHomeomorphMixedSpace F)
    apply sAdeleSchwartz_compact_support_product (M (u n)) a g ha
    intro x
    exact (he (J (u n)) g x).trans
      (congrArg (fun z : ℂ ↦ z * ∏ w, g w (Multiplicative.ofAdd (x.2 w))) (hJ _ _))
  · exact hM.continuousAt.tendsto.comp hut

open scoped TensorProduct in
/-- Compactly supported S-adelic Schwartz–Bruhat tests approximate every test
sequentially. Only the archimedean factor needs approximation. -/
theorem exists_sAdeleSchwartz_compact_support_seq (f : ℬₛ(S)) :
    ∃ u : ℕ → ℬₛ(S), (∀ n, HasCompactSupport (u n).val) ∧ Tendsto u atTop (𝓝 f) := by
  classical
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  let D : Submodule ℂ (ℬₛ(S)) :=
    { carrier := {x | ∃ u : ℕ → ℬₛ(S), (∀ n, HasCompactSupport (u n).val) ∧ Tendsto u atTop (𝓝 x)}
      zero_mem' := ⟨fun _ ↦ 0, fun _ ↦ HasCompactSupport.zero, tendsto_const_nhds⟩
      add_mem' := by
        rintro x y ⟨u, hu, hut⟩ ⟨v, hv, hvt⟩
        exact ⟨fun n ↦ u n + v n, fun n ↦ (hu n).add (hv n), hut.add hvt⟩
      smul_mem' := by
        rintro c x ⟨u, hu, ht⟩
        exact ⟨fun n ↦ c • u n, fun n ↦ (hu n).smul_left (f := fun _ ↦ c), ht.const_smul c⟩ }
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  have hpure (a : A) (g : ∀ w, B w) :
      e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, g w))) ∈ D := by
    have h : ∃ c : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ, J c = a := J.surjective a
    obtain ⟨c, hc⟩ := h
    have hP := sAdeleSchwartz_pure_compact_support_seq J hJ e he c g
    change ∃ u : ℕ → ℬₛ(S), (∀ n, HasCompactSupport (u n).val) ∧
      Tendsto u atTop (𝓝 (e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, g w)))))
    rw [← hc]
    exact hP
  have hgen (a : A) (v : V) : e (a ⊗ₜ[ℂ] v) ∈ D := by
    let L : V →ₗ[ℂ] ℬₛ(S) := e.toLinearMap.comp (TensorProduct.mk ℂ A V a)
    change L v ∈ D
    refine PiTensorProduct.induction_on (motive := fun v : ⨂[ℂ] w, B w ↦ L v ∈ D) v ?_ ?_
    · intro r g
      change L (r • (show V from (⨂ₜ[ℂ] w, g w))) ∈ D
      rw [map_smul]
      exact D.smul_mem r (hpure a g)
    · intro x y hx hy
      exact (D.comap L).add_mem hx hy
  obtain ⟨z, rfl⟩ := e.surjective f
  exact TensorProduct.inductionOn (motive := fun z ↦ e z ∈ D) z hgen
    (fun _ _ hx hy ↦ (D.comap e.toLinearMap).add_mem hx hy)

/-- Evaluation on the S-adelic Schwartz–Bruhat space is continuous. -/
theorem continuous_sAdeleSchwartz_eval (x : SAdeleRing F S) :
    Continuous (fun f : ℬₛ(S) ↦ f (Multiplicative.ofAdd x)) :=
  continuous_schwartzBruhat_eval (Multiplicative.ofAdd x)

section Topology

-- TODO(paper-gap): On p. 231 the Fréchet quotients of the test-function stages
-- give an LF presentation. Strictness requires control of their induced topologies.
-- See Example C.1.4.6(4) and Corollary C.1.5.13 for the bounded-lifting issue in (5.2.1.4).

/-- The global quotient by the closed theta kernel is an LF-space. -/
theorem globalAdelicThetaSpace_lf : IsLFSpace Θ𝔽 :=
  lfSpace_quotient_properties.2 (lfSpace_quotient_properties.1
    (adeleSchwartz_strictLF (F := F)).2) _ adelicTheta_ker_isClosed

/-- The local quotient by the closed theta kernel is an LF-space. -/
theorem sLocalAdelicThetaSpace_lf : IsLFSpace (Θₛ(S)) :=
  lfSpace_quotient_properties.2 (lfSpace_quotient_properties.1
    (sAdeleSchwartz_strictLF F S)) _ sLocalAdelicTheta_ker_isClosed

private theorem frechet_quotient_of_metrizable_strictLF {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (he : IsStrictLFSpace E) (hp : PolynormableSpace ℂ E) (hm : TopologicalSpace.MetrizableSpace E)
    (K : Submodule ℂ E) (hK : IsClosed (K : Set E)) : IsFrechetTVS (E ⧸ K) :=
  isFrechetTVS_quotient ⟨inferInstance, hp, hm, IsStrictLFSpace.completeSpace (E := E) he⟩ K hK

private theorem empty_test_metrizable : TopologicalSpace.MetrizableSpace (ℬₛ(∅)) := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let D := (v : S) → v.val.adicCompletion F
  let : IsEmpty S := ⟨fun v ↦ Finset.notMem_empty v.val v.property⟩
  let : Unique D := uniqueOfSubsingleton 0
  let e : Multiplicative (SAdeleRing F S) ≃ₜ* Multiplicative (InfiniteAdeleRing F) :=
    { toMulEquiv := (AddEquiv.prodUnique (M := InfiniteAdeleRing F) (N := D)).toMultiplicative
      continuous_toFun := (continuous_fst : Continuous (Prod.fst : InfiniteAdeleRing F × D → _))
      continuous_invFun := (continuous_id.prodMk continuous_const :
        Continuous (fun x : InfiniteAdeleRing F ↦ (x, (default : D)))) }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) := InfiniteAdeleRing.locallyCompactSpace F
  let : T2Space (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let T := (schwartzBruhat_congr e).choose
  let J := (archimedeanSchwartzBruhat_equiv (F := F)).choose
  let V := mixedEmbedding.mixedSpace F
  have : (uniformity (SchwartzMap V ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : TopologicalSpace.MetrizableSpace (SchwartzMap V ℂ) := UniformSpace.metrizableSpace
  exact (T.trans J.symm).toHomeomorph.isEmbedding.metrizableSpace

/-- For the archimedean stage there are no finite coordinates. Its test space is
classical Schwartz space, so the theta quotient by its closed kernel is Fréchet. -/
theorem sLocalAdelicThetaSpace_empty_frechet : IsFrechetTVS (Θₛ(∅)) :=
  frechet_quotient_of_metrizable_strictLF (E := ℬₛ(∅)) (sAdeleSchwartz_strictLF F ∅)
    (show IsNuclearTVS.{0} (ℬₛ(∅)) from sAdeleSchwartz_nuclear F ∅).2.1
    (empty_test_metrizable (F := F)) (Kₛ(∅)) (sLocalAdelicTheta_ker_isClosed (F := F) (S := ∅))

open Set TopologicalSpace in
/-- A space with a continuous linear closed embedding into a Fréchet space is Fréchet. -/
private theorem sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →L[ℂ] Y)
    (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) : IsFrechetTVS X := by
  obtain ⟨a, p, m, c⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Y := c
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing
    (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩

open Set TopologicalSpace in
/-- The range of a continuous linear embedding of a Fréchet space into a Hausdorff
topological vector space is closed, and Fréchet in the induced topology. -/
private theorem sLocalAdelicThetaSpace_strictLF_embedded_frechet_range {X E : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] (i : X →L[ℂ] E)
    (hi : IsEmbedding i) (hX : IsFrechetTVS X) :
    IsClosed (range i) ∧ IsFrechetTVS i.toLinearMap.range := by
  obtain ⟨a, p, m, c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let e := LinearEquiv.ofInjective i.toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] i.toLinearMap.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact ⟨(AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom)
      hi.isInducing).isComplete_range.isClosed,
    sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding L.symm.toContinuousLinearMap
      L.symm.toHomeomorph.isClosedEmbedding ⟨a, p, m, c⟩⟩

open Set TopologicalSpace in
/-- By the Baire category theorem, the range of a continuous linear map from a Fréchet space
lies in one member of a countable cover of the target by closed subspaces. -/
private theorem sLocalAdelicThetaSpace_strictLF_frechet_range_in_cover {ι X E : Type*}
    [Countable ι] [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (i : X →L[ℂ] E) (hX : IsFrechetTVS X)
    (D : ι → Submodule ℂ E) (hd : ∀ t, IsClosed (D t : Set E)) (hc : ∀ x : E, ∃ t, x ∈ D t) :
    ∃ t, i.toLinearMap.range ≤ D t := by
  obtain ⟨a, p, m, c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  have : (uniformity X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  let : BaireSpace X := by
    let := UniformSpace.metricSpace X
    infer_instance
  let K (t : ι) := (D t).comap i.toLinearMap
  have hcov : (⋃ t, (K t : Set X)) = univ :=
    eq_univ_of_forall fun x ↦ (hc (i x)).elim fun t ht ↦ mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨t, ht⟩ := nonempty_interior_of_iUnion_of_closed
    (fun t ↦ (hd t).preimage i.continuous) hcov
  have htop : K t = ⊤ := (K t).eq_top_of_nonempty_interior' ht
  exact ⟨t, fun _ ⟨x, hx⟩ ↦ hx ▸ (show x ∈ K t from htop.symm ▸ Submodule.mem_top)⟩

open Set TopologicalSpace in
/-- An LF-space covered by countably many closed subspaces that are Fréchet in the induced
topology is strict. The closure of each defining stage lies in one member of the cover. -/
private theorem sLocalAdelicThetaSpace_strictLF_of_countable_frechet_cover {ι E : Type*}
    [Countable ι] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (hLF : IsLFSpace E) (D : ι → Submodule ℂ E)
    (hd : ∀ t, IsClosed (D t : Set E)) (hD : ∀ t, IsFrechetTVS (D t))
    (hc : ∀ x : E, ∃ t, x ∈ D t) : IsStrictLFSpace E := by
  obtain ⟨h₂, X, _, _, _, hX, j, i, h⟩ := hLF
  let R (k : ℕ) := (i k).toLinearMap.range
  let C (k : ℕ) := (R k).topologicalClosure
  have hP : WithSeminorms (Subtype.val :
      {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} → _) := ⟨h.topology_eq⟩
  have hC (k : ℕ) : IsFrechetTVS (C k) := by
    obtain ⟨t, ht⟩ :=
      sLocalAdelicThetaSpace_strictLF_frechet_range_in_cover (i k) (hX k) D hd hc
    have hst : C k ≤ D t := closure_minimal ht (hd t)
    let l := Submodule.inclusion hst
    have he : IsEmbedding l := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
    have hr : range l = Subtype.val ⁻¹' (C k : Set E) := by
      ext x
      exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x.val, hx⟩, rfl⟩⟩
    exact sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding ⟨l, he.continuous⟩
      ⟨he, hr ▸ (R k).isClosed_topologicalClosure.preimage continuous_subtype_val⟩ (hD t)
  refine ⟨h₂, C, monotone_nat_of_le_succ (fun k ↦ ?_), hC, fun x ↦ ?_, ?_⟩
  · apply closure_mono
    rintro _ ⟨y, rfl⟩
    exact ⟨j k y, DFunLike.congr_fun (h.compatible k) y⟩
  · obtain ⟨k, hk⟩ := h.exhaustive x
    exact ⟨k, subset_closure hk⟩
  · have hs : (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (C k).subtype)) =
        (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (i k).toLinearMap)) := by
      funext p
      apply propext
      refine ⟨fun hp k ↦ ?_,
        fun hp k ↦ (hP.continuous_seminorm ⟨p, hp⟩).comp continuous_subtype_val⟩
      exact (hp k).comp
        ((i k).codRestrict (C k) (fun y ↦ subset_closure (mem_range_self y))).continuous
    unfold locallyConvexFinalTopology
    rw [hs]
    exact hP.withSeminorms_eq

open Set TopologicalSpace in
/-- A continuous linear injection between Fréchet spaces with closed range is an
embedding, by the open mapping theorem applied onto its range. -/
private theorem sLocalAdelicThetaSpace_strictLF_frechet_embedding {A B : Type*}
    [AddCommGroup A] [Module ℂ A] [TopologicalSpace A] [AddCommGroup B] [Module ℂ B]
    [TopologicalSpace B] (hA : IsFrechetTVS A) (hB : IsFrechetTVS B) (f : A →L[ℂ] B)
    (hi : Injective f) (hc : IsClosed (range f)) : IsEmbedding f := by
  let : IsTopologicalAddGroup A := hA.1
  let : IsTopologicalAddGroup B := hB.1
  let : PolynormableSpace ℂ A := hA.2.1
  let : MetrizableSpace A := hA.2.2.1
  let R := f.toLinearMap.range
  let g := f.codRestrict R (fun x ↦ ⟨x, rfl⟩)
  have hs : Surjective g := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
  have hR := sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding R.subtypeL
    hc.isClosedEmbedding_subtypeVal hB
  have ho := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hR) (X := fun _ ↦ A)
    (fun _ ↦ hA) (fun _ ↦ ContinuousLinearMap.id ℂ A) (fun _ ↦ Subset.rfl)
    (fun x ↦ ⟨0, x, rfl⟩) g hs
  let e := Equiv.ofBijective g ⟨fun _ _ he ↦ hi (congrArg Subtype.val he), hs⟩
  exact IsEmbedding.subtypeVal.comp
    (e.toHomeomorphOfContinuousOpen g.continuous ho).isEmbedding

open Set TopologicalSpace in
/-- An LF-space exhausted by rising closed ranges of continuous linear injections of
Fréchet spaces is strict: the injections form a strict system by the open mapping
theorem, so each of them is an embedding. -/
private theorem sLocalAdelicThetaSpace_strictLF_of_closed_frechet_images {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E] {X : ℕ → Type*}
    [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)] [∀ n, TopologicalSpace (X n)]
    (lf : IsLFSpace E) (hX : ∀ n, IsFrechetTVS (X n)) (u : ∀ n, X n →L[ℂ] E)
    (hi : ∀ n, Injective (u n)) (hr : ∀ n, range (u n) ⊆ range (u (n+1)))
    (hc : ∀ n, IsClosed (range (u n))) (cover : ∀ x, ∃ n, x ∈ range (u n)) :
    IsStrictLFSpace E := by
  let R n := (u n).toLinearMap.range
  have step (n : ℕ) : ∃ v : X n →L[ℂ] X (n+1), (u (n+1)).comp v = u n := by
    let b := (u (n+1)).codRestrict (R (n+1)) (fun x ↦ ⟨x, rfl⟩)
    let a := (u n).codRestrict (R (n+1)) (fun x ↦ hr n ⟨x, rfl⟩)
    have sur : Surjective b := fun z ↦ z.property.elim fun x hx ↦ ⟨x, Subtype.ext hx⟩
    obtain ⟨_, v, hv⟩ := frechet_factorization (X := fun _ ↦ X (n+1)) (fun _ ↦ hX _)
      (fun _ ↦ b) (fun _ _ _ eq ↦ hi _ (congrArg Subtype.val eq))
      (fun _ ↦ Subset.rfl) (fun y ↦ ⟨0, sur y⟩) (hX n) a
    exact ⟨v, ContinuousLinearMap.ext fun x ↦ congrArg Subtype.val (DFunLike.congr_fun hv x)⟩
  choose j hj using step
  have hem (n : ℕ) : IsEmbedding (j n) := by
    refine sLocalAdelicThetaSpace_strictLF_frechet_embedding (hX n) (hX _) _ ?_ ?_
    · intro a b hab
      exact hi n (((DFunLike.congr_fun (hj n) a).symm.trans
        (congrArg (u (n+1)) hab)).trans (DFunLike.congr_fun (hj n) b))
    · have eq : range (j n) = u (n+1) ⁻¹' range (u n) := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨y, (DFunLike.congr_fun (hj n) y).symm⟩
        · rintro ⟨y, hy⟩
          exact ⟨y, hi _ ((DFunLike.congr_fun (hj n) y).trans hy)⟩
      rw [eq]
      exact (hc n).preimage (u _).continuous
  have hlim : IsInjectiveLCLimit j u := by
    refine ⟨hi, hj, cover, ?_⟩
    obtain ⟨_, Y, _, _, _, hY, _, i, h⟩ := lf
    have hP : WithSeminorms (Subtype.val :
        {p : Seminorm ℂ E // ∀ n, Continuous (p ∘ (i n).toLinearMap)} → _) := ⟨h.topology_eq⟩
    have eq : (fun p : Seminorm ℂ E ↦ ∀ n, Continuous (p ∘ (u n).toLinearMap)) =
        (fun p : Seminorm ℂ E ↦ ∀ n, Continuous (p ∘ (i n).toLinearMap)) := by
      funext p
      apply propext
      constructor
      · intro hp n
        obtain ⟨k, v, hv⟩ := frechet_factorization hX u hi hr cover (hY n) (i n)
        exact hv ▸ (hp k).comp v.continuous
      · intro hp k
        exact (hP.continuous_seminorm ⟨p, hp⟩).comp (u k).continuous
    unfold locallyConvexFinalTopology
    rw [eq]
    exact hP.withSeminorms_eq
  let (n : ℕ) : IsTopologicalAddGroup (X n) := (hX n).1
  let (n : ℕ) : PolynormableSpace ℂ (X n) := (hX n).2.1
  have hf n := (sLocalAdelicThetaSpace_strictLF_embedded_frechet_range (u n)
    (hlim.isEmbedding_stage hem n) (hX n)).2
  exact sLocalAdelicThetaSpace_strictLF_of_countable_frechet_cover lf R hc hf cover


open Set TopologicalSpace in
/-- An LF-space with a rising cover by closed subspaces, each inside the range of a
continuous linear map from a Fréchet space, is strict. -/
private theorem sLocalAdelicThetaSpace_strictLF_of_closed_levels {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] {Y : ℕ → Type*}
    [∀ n, AddCommGroup (Y n)] [∀ n, Module ℂ (Y n)] [∀ n, TopologicalSpace (Y n)]
    (lf : IsLFSpace E) (L : ℕ → Submodule ℂ E) (hmono : Monotone L)
    (hclosed : ∀ n, IsClosed (L n : Set E)) (hcover : ∀ x, ∃ n, x ∈ L n)
    (hY : ∀ n, IsFrechetTVS (Y n)) (p : ∀ n, Y n →L[ℂ] E)
    (hp : ∀ n, (L n : Set E) ⊆ range (p n)) : IsStrictLFSpace E := by
  let : T2Space E := lf.1
  let (n : ℕ) : IsTopologicalAddGroup (Y n) := (hY n).1
  let M (n : ℕ) : Submodule ℂ (Y n) := (L n).comap (p n).toLinearMap
  have hMc (n : ℕ) : IsClosed (M n : Set (Y n)) := (hclosed n).preimage (p n).continuous
  have hM (n : ℕ) : IsFrechetTVS (M n) :=
    sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding (M n).subtypeL
      (hMc n).isClosedEmbedding_subtypeVal (hY n)
  let q (n : ℕ) : M n →L[ℂ] E := (p n).comp (M n).subtypeL
  let K (n : ℕ) := (q n).ker
  let u (n : ℕ) := (K n).liftQL (q n) le_rfl
  have hr (n : ℕ) : range (u n) = (L n : Set E) := by
    have h1 : range (u n) = range (q n) := ((K n).mkQ_surjective.range_comp (u n)).symm
    rw [h1]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      obtain ⟨y, rfl⟩ := hp n hx
      exact ⟨⟨y, hx⟩, rfl⟩
  apply sLocalAdelicThetaSpace_strictLF_of_closed_frechet_images lf
    (fun n ↦ isFrechetTVS_quotient (hM n) (K n) (q n).isClosed_ker) u
    (fun n ↦ LinearMap.ker_eq_bot.mp ((K n).ker_liftQ_eq_bot' (q n).toLinearMap rfl))
  · intro n
    rw [hr, hr]
    exact hmono n.le_succ
  · intro n
    rw [hr]
    exact hclosed n
  · intro x
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, (hr n).symm ▸ hn⟩

/-- A finite power of a Fréchet space is Fréchet. -/
private theorem sLocalAdelicThetaSpace_strictLF_frechet_pi {A : Type*} [AddCommGroup A]
    [Module ℂ A] [TopologicalSpace A] (hA : IsFrechetTVS A) (d : ℕ) :
    IsFrechetTVS (Fin d → A) := by
  obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hA
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace A := hcomp
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

open Set in
/-- Strictness of the quotient of a test space by the kernel of a linear transform into
continuous functions, when that quotient is an LF-space. The classes whose transforms take
equal values on the pairs of `R n` form a closed subspace. If these subspaces rise to
cover the quotient, and each is represented by finitely many continuous families of
tests over a fixed Fréchet space, the quotient is a strict LF-space. -/
private theorem sLocalAdelicThetaSpace_strictLF_of_levels {X Q A : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [TopologicalSpace Q] [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] (θ : X →ₗ[ℂ] C(Q, ℂ)) (lf : IsLFSpace (X ⧸ LinearMap.ker θ))
    (hA : IsFrechetTVS A) (hev : ∀ g : Q, Continuous (fun f ↦ θ f g))
    (R : ℕ → Set (Q × Q)) (hR : ∀ n, R (n+1) ⊆ R n)
    (hcover : ∀ f, ∃ n, ∀ r ∈ R n, θ f r.1 = θ f r.2)
    (hgen : ∀ n, ∃ (d : ℕ) (p : Fin d → (A →L[ℂ] X)), ∀ f,
      (∀ r ∈ R n, θ f r.1 = θ f r.2) → ∃ a : Fin d → A, θ (∑ j, p j (a j)) = θ f) :
    IsStrictLFSpace (X ⧸ LinearMap.ker θ) := by
  let K := LinearMap.ker θ
  let ev (g : Q) : X ⧸ K →L[ℂ] ℂ :=
    K.liftQL (⟨(ContinuousMap.evalCLM ℂ g).toLinearMap.comp θ, hev g⟩ : X →L[ℂ] ℂ)
      (fun f h ↦ congrArg (fun φ : C(Q, ℂ) ↦ φ g) (LinearMap.mem_ker.mp h))
  let L (n : ℕ) : Submodule ℂ (X ⧸ K) :=
    { carrier := {t | ∀ r ∈ R n, ev r.1 t = ev r.2 t}
      zero_mem' := fun r _ ↦ by simp only [map_zero]
      add_mem' := fun {x y} hx hy r hr ↦ by simp only [map_add, hx r hr, hy r hr]
      smul_mem' := fun c {x} hx r hr ↦ by simp only [map_smul, hx r hr] }
  have hmem (n : ℕ) (f : X) : K.mkQ f ∈ L n ↔ ∀ r ∈ R n, θ f r.1 = θ f r.2 := Iff.rfl
  have hmono : Monotone L := monotone_nat_of_le_succ fun n t ht r hr ↦ ht r (hR n hr)
  have hclosed (n : ℕ) : IsClosed (L n : Set (X ⧸ K)) := by
    have hset : (L n : Set (X ⧸ K)) = ⋂ r ∈ R n, {t | ev r.1 t = ev r.2 t} := by
      ext t
      simp only [mem_iInter]
      rfl
    rw [hset]
    exact isClosed_biInter fun r _ ↦ isClosed_eq (ev r.1).continuous (ev r.2).continuous
  have hcov (t : X ⧸ K) : ∃ n, t ∈ L n := by
    obtain ⟨f, rfl⟩ := K.mkQ_surjective t
    exact (hcover f).imp fun n hn ↦ (hmem n f).mpr hn
  choose d p hp using hgen
  let P (n : ℕ) : (Fin (d n) → A) →L[ℂ] X ⧸ K :=
    K.mkQL.comp (∑ j, (p n j).comp (ContinuousLinearMap.proj j))
  refine sLocalAdelicThetaSpace_strictLF_of_closed_levels lf L hmono hclosed hcov
    (fun n ↦ sLocalAdelicThetaSpace_strictLF_frechet_pi hA (d n)) P (fun n t ht ↦ ?_)
  obtain ⟨f, rfl⟩ := K.mkQ_surjective t
  obtain ⟨a, ha⟩ := hp n f ((hmem n f).mp ht)
  refine ⟨a, ?_⟩
  have hP : P n a = K.mkQ (∑ j, p n j (a j)) := by
    simp only [P, ContinuousLinearMap.comp_apply, sum_apply,
      ContinuousLinearMap.proj_apply]
    rfl
  rw [hP]
  apply (Submodule.Quotient.eq K).mpr
  rw [LinearMap.mem_ker, map_sub, ha, sub_self]


open Set in
/-- A locally constant function with compact support on a discretely valued field is
unchanged when its argument is multiplied by an element close enough to one. -/
private theorem sLocalAdelicThetaSpace_strictLF_local_dilation {K : Type*} [Field K]
    [Valued K (WithZero (Multiplicative ℤ))] (f : K → ℂ) (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) :
    ∃ m : ℕ, ∀ u y : K, Valued.v (u - 1) ≤ WithZero.exp (-(m + 1 : ℤ)) → f (u * y) = f y := by
  let G : K × K → ℂ := fun p ↦ f (p.1 * p.2) - f p.2
  have hG : IsLocallyConstant G :=
    (hf.comp_continuous (continuous_fst.mul continuous_snd)).comp₂
      (hf.comp_continuous continuous_snd) (· - ·)
  let N : Set (K × K) := G ⁻¹' {0}
  have hN : IsOpen N := hG.isOpen_fiber 0
  have hsub : ({1} : Set K) ×ˢ tsupport f ⊆ N := by
    rintro ⟨u, y⟩ ⟨hu, -⟩
    have hu' : u = 1 := hu
    simp only [N, G, mem_preimage, mem_singleton_iff, hu', one_mul, sub_self]
  obtain ⟨U, W, hU, -, h1U, hCW, hUW⟩ := generalized_tube_lemma isCompact_singleton hc hN hsub
  have hU1 : U ∈ 𝓝 (1 : K) := hU.mem_nhds (h1U rfl)
  have hinv : (fun u : K ↦ u⁻¹) ⁻¹' U ∈ 𝓝 (1 : K) :=
    (continuousAt_inv₀ (one_ne_zero (α := K))) (by simpa only [inv_one] using hU1)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp (inter_mem hU1 hinv)
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let r : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := by simp [r]
  let k : ℤ := WithZero.log r
  refine ⟨(-k).toNat, fun u y hu ↦ ?_⟩
  have hlt : WithZero.exp (-(((-k).toNat : ℤ) + 1)) < r :=
    calc WithZero.exp (-(((-k).toNat : ℤ) + 1)) < WithZero.exp k :=
          WithZero.exp_lt_exp.mpr (by have := Int.self_le_toNat (-k); omega)
      _ = r := WithZero.exp_log hr
  have huU : u ∈ U ∩ (fun u : K ↦ u⁻¹) ⁻¹' U :=
    hγ ((ν.restrict_lt_iff_lt_embedding).mpr (lt_of_le_of_lt hu hlt))
  have huU₁ : u ∈ U := huU.1
  have huU₂ : u⁻¹ ∈ U := huU.2
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h1 : ν ((0 : K) - 1) = 1 := by
      rw [zero_sub, Valuation.map_neg, Valuation.map_one]
    have h2 : WithZero.exp (-(((-k).toNat : ℤ) + 1)) < 1 := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    exact absurd (h1 ▸ hu) (not_le.mpr h2)
  by_cases hy : y ∈ tsupport f
  · have h0 : G (u, y) = 0 := hUW (⟨huU₁, hCW hy⟩ : (u, y) ∈ U ×ˢ W)
    exact sub_eq_zero.mp h0
  · have hy0 : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    by_contra hne
    have huy : u * y ∈ tsupport f := subset_tsupport f fun h0 ↦ hne (h0.trans hy0.symm)
    have h0 : G (u⁻¹, u * y) = 0 := hUW (⟨huU₂, hCW huy⟩ : (u⁻¹, u * y) ∈ U ×ˢ W)
    have h3 : f (u⁻¹ * (u * y)) = f (u * y) := sub_eq_zero.mp h0
    rw [inv_mul_cancel_left₀ hu0] at h3
    exact hne h3.symm

open scoped TensorProduct in
/-- Each S-adelic test function is unchanged when its finite coordinates are multiplied
by elements close enough to one. -/
private theorem sLocalAdelicThetaSpace_strictLF_test_dilation
    {S : Finset (HeightOneSpectrum (𝓞 F))} (f : ℬₛ(S)) :
    ∃ m : ℕ, ∀ h : SAdeleRing F S, h.1 = 1 →
      (∀ w : S, Valued.v (h.2 w - 1) ≤ WithZero.exp (-(m + 1 : ℤ))) →
      ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd (h * x)) = f (Multiplicative.ofAdd x) := by
  classical
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  let P (m : ℕ) (f : ℬₛ(S)) : Prop := ∀ h : SAdeleRing F S, h.1 = 1 →
    (∀ w : S, Valued.v (h.2 w - 1) ≤ WithZero.exp (-(m + 1 : ℤ))) →
    ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd (h * x)) = f (Multiplicative.ofAdd x)
  have hPmono {m m' : ℕ} (hm : m ≤ m') {f : ℬₛ(S)} (hf : P m f) : P m' f :=
    fun h h1 hw x ↦ hf h h1 (fun w ↦ (hw w).trans (WithZero.exp_le_exp.mpr (by omega))) x
  let D : Submodule ℂ (ℬₛ(S)) :=
    { carrier := {f | ∃ m, P m f}
      zero_mem' := ⟨0, fun _ _ _ _ ↦ rfl⟩
      add_mem' := by
        rintro f g ⟨m, hm⟩ ⟨m', hm'⟩
        refine ⟨max m m', fun h h1 hw x ↦ ?_⟩
        exact congrArg₂ (· + ·) (hPmono (le_max_left m m') hm h h1 hw x)
          (hPmono (le_max_right m m') hm' h h1 hw x)
      smul_mem' := by
        rintro c f ⟨m, hm⟩
        exact ⟨m, fun h h1 hw x ↦ congrArg (c • ·) (hm h h1 hw x)⟩ }
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  have hpure (a : A) (g : ∀ w, B w) :
      e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, g w))) ∈ D := by
    have hloc (w : S) := sLocalAdelicThetaSpace_strictLF_local_dilation
      (fun y : w.val.adicCompletion F ↦ g w (Multiplicative.ofAdd y))
      ((mem_finitePlaceSchwartz_iff F w.val _).mp ⟨g w, fun _ ↦ rfl⟩).1
      ((mem_finitePlaceSchwartz_iff F w.val _).mp ⟨g w, fun _ ↦ rfl⟩).2
    choose m hm using hloc
    refine ⟨Finset.univ.sup m, fun h h1 hw x ↦ ?_⟩
    refine (he a g (h * x)).trans (Eq.trans ?_ (he a g x).symm)
    have e1 : (h * x).1 = x.1 := by rw [Prod.fst_mul, h1, one_mul]
    rw [e1]
    congr 1
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    refine hm w (h.2 w) (x.2 w) ((hw w).trans (WithZero.exp_le_exp.mpr ?_))
    have := Finset.le_sup (f := m) (Finset.mem_univ w)
    omega
  have hgen (a : A) (v : V) : e (a ⊗ₜ[ℂ] v) ∈ D := by
    let L : V →ₗ[ℂ] ℬₛ(S) := e.toLinearMap.comp (TensorProduct.mk ℂ A V a)
    change L v ∈ D
    refine PiTensorProduct.induction_on (motive := fun v : ⨂[ℂ] w, B w ↦ L v ∈ D) v ?_ ?_
    · intro r g
      change L (r • (show V from (⨂ₜ[ℂ] w, g w))) ∈ D
      rw [map_smul]
      exact D.smul_mem r (hpure a g)
    · intro x y hx hy
      exact (D.comap L).add_mem hx hy
  obtain ⟨z, rfl⟩ := e.surjective f
  exact TensorProduct.inductionOn (motive := fun z ↦ e z ∈ D) z hgen
    (fun _ _ hx hy ↦ (D.comap e.toLinearMap).add_mem hx hy)

/-- Each S-local theta function is unchanged by the finite ideles close enough to one. -/
private theorem sLocalAdelicThetaSpace_strictLF_level_cover
    {S : Finset (HeightOneSpectrum (𝓞 F))} (f : ℬₛ(S)) :
    ∃ n : ℕ, ∀ h g : (SAdeleRing F S)ˣ, h.val.1 = 1 →
      (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
      sLocalAdelicTheta F S f (h * g) = sLocalAdelicTheta F S f g := by
  obtain ⟨m, hm⟩ := sLocalAdelicThetaSpace_strictLF_test_dilation f
  refine ⟨m, fun h g h1 hw ↦ ?_⟩
  refine (sLocalAdelicTheta_apply F S f (h * g)).trans
    (Eq.trans (tsum_congr fun ξ ↦ ?_) (sLocalAdelicTheta_apply F S f g).symm)
  have e1 : (sUnitEmbedding F S ξ * (h * g)).val = h.val * (sUnitEmbedding F S ξ * g).val := by
    simp only [Units.val_mul]
    exact mul_left_comm _ _ _
  exact (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) e1).trans (hm h.val h1 hw _)


/-- In a discretely valued field, an element congruent to one modulo a positive power of the
maximal ideal has valuation one, and multiplying by it preserves this congruence class in
both directions. -/
private theorem sLocalAdelicThetaSpace_strictLF_level_mul {K : Type*} [Field K]
    [Valued K (WithZero (Multiplicative ℤ))] (n : ℕ) (u y : K)
    (hu : Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) :
    Valued.v u = 1 ∧ (Valued.v (u * y - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) ↔
      Valued.v (y - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) := by
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  have hlt : ν (u - 1) < 1 := lt_of_le_of_lt hu (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega))
  have hu1 : ν u = 1 := by
    have h1 := ν.map_one_add_of_lt hlt
    rwa [add_sub_cancel] at h1
  refine ⟨hu1, fun h ↦ ?_, fun h ↦ ?_⟩
  · have e : u * (y - 1) = (u * y - 1) - (u - 1) := by ring
    have h2 : ν (u * (y - 1)) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
      rw [e]
      exact (ν.map_sub _ _).trans (max_le h hu)
    rwa [map_mul, hu1, one_mul] at h2
  · have e : u * y - 1 = u * (y - 1) + (u - 1) := by ring
    change ν (u * y - 1) ≤ _
    rw [e]
    refine (ν.map_add _ _).trans (max_le ?_ hu)
    rw [map_mul, hu1, one_mul]
    exact h

open Set in
/-- The indicators of the local integers and of the elements congruent to one modulo a
positive power of the maximal ideal are local tests. -/
private theorem sLocalAdelicThetaSpace_strictLF_indicator_tests
    (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ∃ b : Bool → SchwartzBruhat (Multiplicative (w.adicCompletion F)),
      (∀ x : w.adicCompletion F, b false (Multiplicative.ofAdd x) =
        indicator {x : w.adicCompletion F | Valued.v x ≤ 1} 1 x) ∧
      (∀ x : w.adicCompletion F, b true (Multiplicative.ofAdd x) =
        indicator {x : w.adicCompletion F |
          Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))} 1 x) := by
  let K := w.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let sO : Set K := {x | ν x ≤ 1}
  let sH : Set K := {x | ν (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))}
  have hOc : IsCompact sO :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w)
  have hOo : IsOpen sO := Valued.isOpen_valuationSubring K
  obtain ⟨z, hz⟩ := w.valuedAdicCompletion_surjective F (WithZero.exp (-(n + 1 : ℤ)))
  have hz0 : ν.restrict z ≠ 0 := fun h0 ↦
    WithZero.exp_ne_zero (hz.symm.trans (ν.restrict_eq_zero_iff.mp h0))
  have hball : IsClopen {y : K | ν.restrict y ≤ ν.restrict z} :=
    Valued.isClopen_closedBall K hz0
  have hball' : IsClopen {y : K | ν y ≤ WithZero.exp (-(n + 1 : ℤ))} := by
    have hset : {y : K | ν y ≤ WithZero.exp (-(n + 1 : ℤ))} =
        {y : K | ν.restrict y ≤ ν.restrict z} := by
      ext y
      change ν y ≤ _ ↔ ν.restrict y ≤ ν.restrict z
      rw [Valuation.restrict_le_iff]
      exact hz.symm ▸ Iff.rfl
    rw [hset]
    exact hball
  have hHcl : IsClopen sH := hball'.preimage (continuous_id.sub continuous_const)
  have hHc : IsCompact sH := hOc.of_isClosed_subset hHcl.isClosed fun x hx ↦
    (sLocalAdelicThetaSpace_strictLF_level_mul n x 1 hx).1.le
  have key (s : Set K) (hcl : IsClopen s) (hc : IsCompact s) :
      ∃ g : SchwartzBruhat (Multiplicative K), ∀ x : K,
        g (Multiplicative.ofAdd x) = indicator s 1 x := by
    refine (mem_finitePlaceSchwartz_iff F w (indicator s 1)).mpr ⟨?_, ?_⟩
    · have h : IsLocallyConstant (⇑(LocallyConstant.charFn ℂ hcl) : K → ℂ) :=
        (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      rwa [LocallyConstant.coe_charFn] at h
    · exact HasCompactSupport.intro hc fun x hx ↦ indicator_of_notMem hx _
  obtain ⟨bO, hbO⟩ := key sO ⟨hOc.isClosed, hOo⟩ hOc
  obtain ⟨bH, hbH⟩ := key sH hHcl hHc
  exact ⟨fun t ↦ if t then bH else bO, hbO, hbH⟩


open Set in
/-- Structure of the local tests fixed by the elements congruent to one modulo a positive
power of the maximal ideal: such a test is a finite combination of dilates of the indicator
of the local integers and of the indicator of that congruence class. Near zero the test
is constant, which is a multiple of a dilate of the first indicator. What is left has
compact support away from zero, covered by finitely many classes, on each of which the
test is constant. -/
private theorem sLocalAdelicThetaSpace_strictLF_local_expansion
    (w : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (b : Bool → SchwartzBruhat (Multiplicative (w.adicCompletion F)))
    (hbO : ∀ x : w.adicCompletion F, b false (Multiplicative.ofAdd x) =
      indicator {x : w.adicCompletion F | Valued.v x ≤ 1} 1 x)
    (hbH : ∀ x : w.adicCompletion F, b true (Multiplicative.ofAdd x) =
      indicator {x : w.adicCompletion F |
        Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))} 1 x)
    (g : SchwartzBruhat (Multiplicative (w.adicCompletion F)))
    (hg : ∀ u y : w.adicCompletion F, Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) →
      g (Multiplicative.ofAdd (u * y)) = g (Multiplicative.ofAdd y)) :
    g ∈ Submodule.span ℂ (range fun q : Bool × (w.adicCompletion F)ˣ ↦
      schwartzBruhatUnitTranslate q.2 (b q.1)) := by
  classical
  let K := w.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n + 1 : ℤ))
  let X : Set (SchwartzBruhat (Multiplicative K)) :=
    range fun q : Bool × Kˣ ↦ schwartzBruhatUnitTranslate q.2 (b q.1)
  have hX (t : Bool) (c : Kˣ) : schwartzBruhatUnitTranslate c (b t) ∈ Submodule.span ℂ X :=
    Submodule.subset_span ⟨(t, c), rfl⟩
  have hext (g₁ g₂ : SchwartzBruhat (Multiplicative K))
      (h : ∀ y : K, g₁ (Multiplicative.ofAdd y) = g₂ (Multiplicative.ofAdd y)) : g₁ = g₂ :=
    Subtype.ext (funext fun x ↦ h x.toAdd)
  have hsub (g₁ g₂ : SchwartzBruhat (Multiplicative K)) (c : ℂ) (y : K) :
      (g₁ - c • g₂) (Multiplicative.ofAdd y) =
        g₁ (Multiplicative.ofAdd y) - c * g₂ (Multiplicative.ofAdd y) := rfl
  -- the two dilated indicators
  have hO (c : Kˣ) (y : K) : schwartzBruhatUnitTranslate c (b false) (Multiplicative.ofAdd y) =
      indicator {x : K | ν x ≤ ν c.val} 1 y := by
    rw [schwartzBruhatUnitTranslate_apply, hbO]
    have hiff : (c⁻¹ : Kˣ).val * y ∈ {x : K | ν x ≤ 1} ↔ y ∈ {x : K | ν x ≤ ν c.val} := by
      change ν ((c⁻¹ : Kˣ).val * y) ≤ 1 ↔ ν y ≤ ν c.val
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀,
        inv_mul_le_iff₀ (zero_lt_iff.mpr ((ν.ne_zero_iff).mpr c.ne_zero)), mul_one]
    by_cases hy : y ∈ {x : K | ν x ≤ ν c.val}
    · rw [indicator_of_mem hy, indicator_of_mem (hiff.mpr hy)]
      rfl
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy (hiff.mp h))]
  have hH (c : Kˣ) (y : K) : schwartzBruhatUnitTranslate c (b true) (Multiplicative.ofAdd y) =
      indicator {x : K | ν ((c⁻¹ : Kˣ).val * x - 1) ≤ ε} 1 y := by
    rw [schwartzBruhatUnitTranslate_apply, hbH]
    rfl
  -- the claim for tests supported in finitely many classes
  have claim : ∀ D : Finset K, ∀ g₁ : SchwartzBruhat (Multiplicative K),
      (∀ u y : K, ν (u - 1) ≤ ε →
        g₁ (Multiplicative.ofAdd (u * y)) = g₁ (Multiplicative.ofAdd y)) →
      (∀ y : K, g₁ (Multiplicative.ofAdd y) ≠ 0 → ∃ d ∈ D, d ≠ 0 ∧ ν (d⁻¹ * y - 1) ≤ ε) →
      g₁ ∈ Submodule.span ℂ X := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro g₁ _ hsupp
      have h0 : g₁ = 0 := hext g₁ 0 fun y ↦ by
        by_contra hne
        obtain ⟨d, hd, -⟩ := hsupp y hne
        exact absurd hd (Finset.notMem_empty d)
      rw [h0]
      exact Submodule.zero_mem _
    | insert d D hdD ih =>
      intro g₁ hinv hsupp
      by_cases hd0 : d = 0
      · refine ih g₁ hinv fun y hy ↦ ?_
        obtain ⟨d', hd', hd'0, hd'y⟩ := hsupp y hy
        rcases Finset.mem_insert.mp hd' with rfl | hmem
        · exact absurd hd0 hd'0
        · exact ⟨d', hmem, hd'0, hd'y⟩
      · let c : Kˣ := Units.mk0 d hd0
        let g₂ := g₁ - g₁ (Multiplicative.ofAdd d) • schwartzBruhatUnitTranslate c (b true)
        have hc : (c⁻¹ : Kˣ).val = d⁻¹ := by
          rw [Units.val_inv_eq_inv_val]
          rfl
        have hg₂ (y : K) : g₂ (Multiplicative.ofAdd y) = g₁ (Multiplicative.ofAdd y) -
            g₁ (Multiplicative.ofAdd d) * indicator {x : K | ν (d⁻¹ * x - 1) ≤ ε} 1 y := by
          have h := hsub g₁ (schwartzBruhatUnitTranslate c (b true))
            (g₁ (Multiplicative.ofAdd d)) y
          rw [hH, hc] at h
          exact h
        have hval (y : K) (hy : ν (d⁻¹ * y - 1) ≤ ε) :
            g₁ (Multiplicative.ofAdd y) = g₁ (Multiplicative.ofAdd d) := by
          have := hinv (d⁻¹ * y) d hy
          rwa [mul_comm d⁻¹ y, mul_assoc, inv_mul_cancel₀ hd0, mul_one] at this
        have hmem : g₂ ∈ Submodule.span ℂ X := by
          refine ih g₂ (fun u y hu ↦ ?_) (fun y hy ↦ ?_)
          · rw [hg₂, hg₂, hinv u y hu]
            congr 2
            have hiff : u * y ∈ {x : K | ν (d⁻¹ * x - 1) ≤ ε} ↔
                y ∈ {x : K | ν (d⁻¹ * x - 1) ≤ ε} := by
              change ν (d⁻¹ * (u * y) - 1) ≤ ε ↔ ν (d⁻¹ * y - 1) ≤ ε
              rw [show d⁻¹ * (u * y) = u * (d⁻¹ * y) by ring]
              exact (sLocalAdelicThetaSpace_strictLF_level_mul n u (d⁻¹ * y) hu).2
            by_cases hy : y ∈ {x : K | ν (d⁻¹ * x - 1) ≤ ε}
            · rw [indicator_of_mem hy, indicator_of_mem (hiff.mpr hy)]
              rfl
            · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy (hiff.mp h))]
          · by_cases hyd : ν (d⁻¹ * y - 1) ≤ ε
            · exfalso
              apply hy
              rw [hg₂, indicator_of_mem (show y ∈ {x : K | ν (d⁻¹ * x - 1) ≤ ε} from hyd),
                hval y hyd]
              simp only [Pi.one_apply, mul_one, sub_self]
            · have hy1 : g₁ (Multiplicative.ofAdd y) ≠ 0 := by
                intro h0
                apply hy
                rw [hg₂, indicator_of_notMem (show y ∉ {x : K | ν (d⁻¹ * x - 1) ≤ ε} from hyd),
                  h0, mul_zero, sub_zero]
              obtain ⟨d', hd', hd'0, hd'y⟩ := hsupp y hy1
              rcases Finset.mem_insert.mp hd' with rfl | hmem
              · exact absurd hd'y hyd
              · exact ⟨d', hmem, hd'0, hd'y⟩
        have hdecomp : g₁ = g₂ +
            g₁ (Multiplicative.ofAdd d) • schwartzBruhatUnitTranslate c (b true) :=
          (sub_add_cancel _ _).symm
        rw [hdecomp]
        exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ (hX true c))
  -- the test is constant near zero
  obtain ⟨hlc, -⟩ := (mem_finitePlaceSchwartz_iff F w
    (fun y : K ↦ g (Multiplicative.ofAdd y))).mp ⟨g, fun _ ↦ rfl⟩
  have hU : (fun y : K ↦ g (Multiplicative.ofAdd y)) ⁻¹' {g (Multiplicative.ofAdd (0 : K))} ∈
      𝓝 (0 : K) := (hlc.isOpen_fiber _).mem_nhds rfl
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  let r : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := by simp [r]
  obtain ⟨z, hz⟩ := w.valuedAdicCompletion_surjective F (WithZero.exp (WithZero.log r - 1))
  have hz0 : z ≠ 0 := fun h0 ↦ WithZero.exp_ne_zero (a := WithZero.log r - 1)
    (hz.symm.trans (by rw [h0, map_zero]))
  have hzr : ν z < r := by
    change Valued.v z < r
    rw [hz]
    calc WithZero.exp (WithZero.log r - 1) < WithZero.exp (WithZero.log r) :=
          WithZero.exp_lt_exp.mpr (by omega)
      _ = r := WithZero.exp_log hr
  let c₀ : Kˣ := Units.mk0 z hz0
  have hnear (y : K) (hy : ν y ≤ ν z) :
      g (Multiplicative.ofAdd y) = g (Multiplicative.ofAdd (0 : K)) :=
    hγ ((ν.restrict_lt_iff_lt_embedding).mpr (lt_of_le_of_lt hy hzr))
  let g₁ := g - g (Multiplicative.ofAdd (0 : K)) • schwartzBruhatUnitTranslate c₀ (b false)
  have hg₁ (y : K) : g₁ (Multiplicative.ofAdd y) = g (Multiplicative.ofAdd y) -
      g (Multiplicative.ofAdd (0 : K)) * indicator {x : K | ν x ≤ ν z} 1 y := by
    have h := hsub g (schwartzBruhatUnitTranslate c₀ (b false))
      (g (Multiplicative.ofAdd (0 : K))) y
    rw [hO] at h
    exact h
  have hg₁zero (y : K) (hy : ν y ≤ ν z) : g₁ (Multiplicative.ofAdd y) = 0 := by
    rw [hg₁, indicator_of_mem (show y ∈ {x : K | ν x ≤ ν z} from hy), hnear y hy]
    simp only [Pi.one_apply, mul_one, sub_self]
  have hg₁inv (u y : K) (hu : ν (u - 1) ≤ ε) :
      g₁ (Multiplicative.ofAdd (u * y)) = g₁ (Multiplicative.ofAdd y) := by
    rw [hg₁, hg₁, hg u y hu]
    congr 2
    have hiff : u * y ∈ {x : K | ν x ≤ ν z} ↔ y ∈ {x : K | ν x ≤ ν z} := by
      change ν (u * y) ≤ ν z ↔ ν y ≤ ν z
      rw [map_mul, show ν u = 1 from (sLocalAdelicThetaSpace_strictLF_level_mul n u 1 hu).1,
        one_mul]
    by_cases hy : y ∈ {x : K | ν x ≤ ν z}
    · rw [indicator_of_mem hy, indicator_of_mem (hiff.mpr hy)]
      rfl
    · rw [indicator_of_notMem hy, indicator_of_notMem (fun h ↦ hy (hiff.mp h))]
  -- cover the support of what is left by finitely many classes
  obtain ⟨-, hcs⟩ := (mem_finitePlaceSchwartz_iff F w
    (fun y : K ↦ g₁ (Multiplicative.ofAdd y))).mp ⟨g₁, fun _ ↦ rfl⟩
  have hB : {u : K | ν (u - 1) ≤ ε} ∈ 𝓝 (1 : K) := by
    obtain ⟨z', hz'⟩ := w.valuedAdicCompletion_surjective F ε
    have hz'0 : ν.restrict z' ≠ 0 := fun h0 ↦
      WithZero.exp_ne_zero (hz'.symm.trans (ν.restrict_eq_zero_iff.mp h0))
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ hz'0, fun u hu ↦ ?_⟩
    have hlt : ν (u - 1) < ν z' := ν.restrict_lt_iff.mp hu
    exact (hz' ▸ hlt).le
  have hN₀ : {y : K | ν y ≤ ν z} ∈ 𝓝 (0 : K) := by
    have hz0' : ν.restrict z ≠ 0 := fun h0 ↦ hz0 ((ν.zero_iff).mp (ν.restrict_eq_zero_iff.mp h0))
    refine Valued.mem_nhds_zero.mpr ⟨Units.mk0 _ hz0', fun y hy ↦ ?_⟩
    exact (ν.restrict_lt_iff.mp hy).le
  let U (y : K) : Set K := if y = 0 then {y' : K | ν y' ≤ ν z} else {y' : K | ν (y⁻¹ * y' - 1) ≤ ε}
  have hUn (y : K) : U y ∈ 𝓝 y := by
    by_cases hy : y = 0
    · rw [show U y = {y' : K | ν y' ≤ ν z} from ite_eq_left_of_eq_true _ _ (eq_true hy), hy]
      exact hN₀
    · rw [show U y = {y' : K | ν (y⁻¹ * y' - 1) ≤ ε} from
        ite_eq_right_of_eq_false _ _ (eq_false hy)]
      have hcont : Continuous fun y' : K ↦ y⁻¹ * y' := continuous_const.mul continuous_id
      exact hcont.continuousAt.preimage_mem_nhds (by rw [inv_mul_cancel₀ hy]; exact hB)
  obtain ⟨D, -, hD⟩ := hcs.elim_nhds_subcover U (fun y _ ↦ hUn y)
  have hmem : g₁ ∈ Submodule.span ℂ X := by
    refine claim D g₁ hg₁inv fun y hy ↦ ?_
    obtain ⟨d, hd, hyd⟩ := mem_iUnion₂.mp (hD (subset_tsupport _ hy))
    by_cases hd0 : d = 0
    · rw [show U d = {y' : K | ν y' ≤ ν z} from ite_eq_left_of_eq_true _ _ (eq_true hd0)] at hyd
      exact absurd (hg₁zero y hyd) hy
    · rw [show U d = {y' : K | ν (d⁻¹ * y' - 1) ≤ ε} from
        ite_eq_right_of_eq_false _ _ (eq_false hd0)] at hyd
      exact ⟨d, hd, hd0, hyd⟩
  have hdecomp : g = g₁ +
      g (Multiplicative.ofAdd (0 : K)) • schwartzBruhatUnitTranslate c₀ (b false) :=
    (sub_add_cancel _ _).symm
  rw [hdecomp]
  exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _ (hX false c₀))

open Set in
open scoped TensorProduct in
/-- Templates on the finite coordinates for a congruence level. At each place of `S` take
the indicator of the local integers or of the elements congruent to one modulo the
`(n+1)`-st power of the maximal ideal. The products of these, dilated by S-ideles and
tensored with archimedean tests, span every pure tensor whose local factors are fixed by
the elements congruent to one. -/
private theorem sLocalAdelicThetaSpace_strictLF_level_pure
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
    ∃ (N : ℕ) (β : Fin N → ((w : S) → w.val.adicCompletion F) → ℂ)
      (P : Fin N → (SAdeleRing F S)ˣ →
        (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ] ℬₛ(S))),
      (∀ j c a (x : SAdeleRing F S), P j c a (Multiplicative.ofAdd x) =
        a (Multiplicative.ofAdd x.1) * β j ((c⁻¹).val.2 * x.2)) ∧
      (∀ j (h y : (w : S) → w.val.adicCompletion F),
        (∀ w : S, Valued.v (h w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
        β j (h * y) = β j y) ∧
      ∀ (f' : ℬₛ(S)) (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
        (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
        (∀ (w : S) (u y : w.val.adicCompletion F),
          Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) →
          g w (Multiplicative.ofAdd (u * y)) = g w (Multiplicative.ofAdd y)) →
        (∀ x : SAdeleRing F S, f' (Multiplicative.ofAdd x) =
          a (Multiplicative.ofAdd x.1) * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w))) →
        f' ∈ Submodule.span ℂ (range fun q : Fin N × (SAdeleRing F S)ˣ ×
          SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) ↦ P q.1 q.2.1 q.2.2) := by
  classical
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  choose b hbO hbH using fun w : S ↦
    sLocalAdelicThetaSpace_strictLF_indicator_tests (F := F) w.val n
  let cw (c : (SAdeleRing F S)ˣ) (w : S) : (w.val.adicCompletion F)ˣ :=
    Units.map ((Pi.evalRingHom (fun w : S ↦ w.val.adicCompletion F) w).comp
      (RingHom.snd _ _)).toMonoidHom c
  let loc (t : S → Bool) (c : (SAdeleRing F S)ˣ) (w : S) : B w :=
    schwartzBruhatUnitTranslate (cw c w) (b w (t w))
  let tens (t : S → Bool) (c : (SAdeleRing F S)ˣ) : V := ⨂ₜ[ℂ] w, loc t c w
  let slice (v : V) : A →L[ℂ] InductiveTensor A V :=
    ⟨(TensorProduct.mk ℂ A V).flip v, sAdeleSchwartz_continuous_tmul_fixed (A := A) (V := V) v⟩
  let P₀ (t : S → Bool) (c : (SAdeleRing F S)ˣ) : A →L[ℂ] ℬₛ(S) :=
    e.toContinuousLinearMap.comp (slice (tens t c))
  let β₀ (t : S → Bool) (y : (w : S) → w.val.adicCompletion F) : ℂ :=
    ∏ w : S, b w (t w) (Multiplicative.ofAdd (y w))
  have hPe (t : S → Bool) (c : (SAdeleRing F S)ˣ) (a : A) :
      P₀ t c a = e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, loc t c w))) := rfl
  let Eq : (S → Bool) ≃ Fin (Fintype.card (S → Bool)) := Fintype.equivFin (S → Bool)
  let P (j : Fin (Fintype.card (S → Bool))) := P₀ (Eq.symm j)
  let β (j : Fin (Fintype.card (S → Bool))) := β₀ (Eq.symm j)
  have hPEq (t : S → Bool) (c : (SAdeleRing F S)ˣ) (a : A) : P (Eq t) c a = P₀ t c a := by
    change P₀ (Eq.symm (Eq t)) c a = P₀ t c a
    rw [Equiv.symm_apply_apply]
  refine ⟨Fintype.card (S → Bool), β, P, fun j c a x ↦ ?_, fun j h y hh ↦ ?_,
    fun f' a g hg hf' ↦ ?_⟩
  · change P₀ (Eq.symm j) c a (Multiplicative.ofAdd x) = _
    rw [hPe]
    exact he a (loc (Eq.symm j) c) x
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    change b w (Eq.symm j w) (Multiplicative.ofAdd (h w * y w)) =
      b w (Eq.symm j w) (Multiplicative.ofAdd (y w))
    have hlev := sLocalAdelicThetaSpace_strictLF_level_mul n (h w) (y w) (hh w)
    cases Eq.symm j w with
    | false =>
      rw [hbO, hbO]
      have hiff : h w * y w ∈ {x : w.val.adicCompletion F | Valued.v x ≤ 1} ↔
          y w ∈ {x : w.val.adicCompletion F | Valued.v x ≤ 1} := by
        change Valued.v (h w * y w) ≤ 1 ↔ Valued.v (y w) ≤ 1
        rw [map_mul, hlev.1, one_mul]
      by_cases hy : y w ∈ {x : w.val.adicCompletion F | Valued.v x ≤ 1}
      · rw [indicator_of_mem hy, indicator_of_mem (hiff.mpr hy)]
        rfl
      · rw [indicator_of_notMem hy, indicator_of_notMem (fun hx ↦ hy (hiff.mp hx))]
    | true =>
      rw [hbH, hbH]
      have hiff : h w * y w ∈ {x : w.val.adicCompletion F |
            Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))} ↔
          y w ∈ {x : w.val.adicCompletion F |
            Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))} := hlev.2
      by_cases hy : y w ∈ {x : w.val.adicCompletion F |
          Valued.v (x - 1) ≤ WithZero.exp (-(n + 1 : ℤ))}
      · rw [indicator_of_mem hy, indicator_of_mem (hiff.mpr hy)]
        rfl
      · rw [indicator_of_notMem hy, indicator_of_notMem (fun hx ↦ hy (hiff.mp hx))]
  · let Sp : Submodule ℂ (ℬₛ(S)) := Submodule.span ℂ
      (range fun q : Fin (Fintype.card (S → Bool)) × (SAdeleRing F S)ˣ × A ↦ P q.1 q.2.1 q.2.2)
    let X (w : S) : Set (B w) := range fun q : Bool × (w.val.adicCompletion F)ˣ ↦
      schwartzBruhatUnitTranslate q.2 (b w q.1)
    let Φ : MultilinearMap (RingHom.id ℂ) (fun w : S ↦ B w) (ℬₛ(S)) :=
      (e.toLinearMap.comp (TensorProduct.mk ℂ A V a)).compMultilinearMap
        (PiTensorProduct.tprod ℂ)
    have hΦ (k : ∀ w : S, B w) : Φ k = e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, k w))) := rfl
    have hf'Φ : f' = Φ g := by
      rw [hΦ]
      exact Subtype.ext (funext fun x ↦ (hf' x.toAdd).trans (he a g x.toAdd).symm)
    have claim : ∀ (U : Finset S) (k : ∀ w : S, B w),
        (∀ w ∈ U, k w ∈ Submodule.span ℂ (X w)) → (∀ w ∉ U, k w ∈ X w) → Φ k ∈ Sp := by
      intro U
      induction U using Finset.induction_on with
      | empty =>
        intro k _ hk
        choose q hq using fun w : S ↦ hk w (Finset.notMem_empty w)
        let c : (SAdeleRing F S)ˣ :=
          MulEquiv.prodUnits.symm (1, MulEquiv.piUnits.symm fun w ↦ (q w).2)
        have hc (w : S) : cw c w = (q w).2 := Units.ext rfl
        have hk' : k = loc (fun w ↦ (q w).1) c := funext fun w ↦ by
          change k w = schwartzBruhatUnitTranslate (cw c w) (b w (q w).1)
          rw [hc w]
          exact (hq w).symm
        rw [hΦ, hk']
        exact Submodule.subset_span ⟨(Eq fun w ↦ (q w).1, c, a), hPEq _ c a⟩
      | insert w₀ U hw₀ ih =>
        intro k hkU hkX
        have hle : Submodule.span ℂ (X w₀) ≤ Sp.comap (Φ.toLinearMap k w₀) := by
          refine Submodule.span_le.mpr fun x hx ↦ ?_
          change Φ.toLinearMap k w₀ x ∈ Sp
          rw [MultilinearMap.toLinearMap_apply]
          refine ih _ (fun w hw ↦ ?_) (fun w hw ↦ ?_)
          · have hne : w ≠ w₀ := fun h ↦ hw₀ (h ▸ hw)
            rw [Function.update_of_ne hne]
            exact hkU w (Finset.mem_insert_of_mem hw)
          · by_cases hww : w = w₀
            · subst hww
              rw [Function.update_self]
              exact hx
            · rw [Function.update_of_ne hww]
              exact hkX w fun h ↦ (Finset.mem_insert.mp h).elim hww hw
        have hmem := hle (hkU w₀ (Finset.mem_insert_self w₀ U))
        change Φ.toLinearMap k w₀ (k w₀) ∈ Sp at hmem
        rwa [MultilinearMap.toLinearMap_apply, Function.update_eq_self] at hmem
    rw [hf'Φ]
    refine claim Finset.univ g (fun w _ ↦ ?_) (fun w hw ↦ absurd (Finset.mem_univ w) hw)
    exact sLocalAdelicThetaSpace_strictLF_local_expansion w.val n (b w) (hbO w) (hbH w) (g w)
      (hg w)


/-- Dilating all coordinates of a test function by an S-idele translates its S-local theta
function by that idele. -/
private theorem sLocalAdelicThetaSpace_strictLF_theta_dilation
    {S : Finset (HeightOneSpectrum (𝓞 F))} (h : (SAdeleRing F S)ˣ) (f₁ f₂ : ℬₛ(S))
    (hf : ∀ x : SAdeleRing F S, f₂ (Multiplicative.ofAdd x) =
      f₁ (Multiplicative.ofAdd (h.val * x))) (g : (SAdeleRing F S)ˣ) :
    sLocalAdelicTheta F S f₂ g = sLocalAdelicTheta F S f₁ (h * g) := by
  refine (sLocalAdelicTheta_apply F S f₂ g).trans
    (Eq.trans (tsum_congr fun ξ ↦ ?_) (sLocalAdelicTheta_apply F S f₁ (h * g)).symm)
  have e1 : (sUnitEmbedding F S ξ * (h * g)).val = h.val * (sUnitEmbedding F S ξ * g).val := by
    simp only [Units.val_mul]
    exact mul_left_comm _ _ _
  exact (hf _).trans (congrArg (fun y ↦ f₁ (Multiplicative.ofAdd y)) e1.symm)

/-- Evaluating a finite combination of Schwartz–Bruhat functions at a point. -/
private theorem sLocalAdelicThetaSpace_strictLF_eval_sum {G ι : Type*} [CommGroup G]
    [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (g : ι → SchwartzBruhat G) (x : G) :
    (∑ i ∈ s, c i • g i) x = ∑ i ∈ s, c i * g i x := by
  let ev : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule _).subtype
  change ev (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i * ev (g i)
  simp only [map_sum, map_smul, smul_eq_mul]

/-- A Schwartz–Bruhat function in the span of a set is, pointwise, a finite combination of
members of the set. -/
private theorem sLocalAdelicThetaSpace_strictLF_span_eval {G : Type*} [CommGroup G]
    [TopologicalSpace G] (s : Set (SchwartzBruhat G)) (f : SchwartzBruhat G)
    (hf : f ∈ Submodule.span ℂ s) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → SchwartzBruhat G),
      (∀ i, g i ∈ s) ∧ ∀ x : G, f x = ∑ i, c i * g i x := by
  obtain ⟨m, c, x, hx⟩ := Submodule.mem_span_set'.mp hf
  refine ⟨m, c, fun i ↦ (x i).val, fun i ↦ (x i).property, fun y ↦ ?_⟩
  rw [← hx]
  exact sLocalAdelicThetaSpace_strictLF_eval_sum Finset.univ c (fun i ↦ (x i).val) y

open scoped TensorProduct in
/-- Each S-adelic test function is a finite combination of products of an archimedean test
and local tests at the places of `S`. -/
private theorem sLocalAdelicThetaSpace_strictLF_pure_sum
    {S : Finset (HeightOneSpectrum (𝓞 F))} (f : ℬₛ(S)) :
    ∃ (m : ℕ) (c : Fin m → ℂ)
      (a : Fin m → SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : Fin m → ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
      ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
        ∑ k, c k * (a k (Multiplicative.ofAdd x.1) *
          ∏ w : S, g k w (Multiplicative.ofAdd (x.2 w))) := by
  classical
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let D : Submodule ℂ (ℬₛ(S)) := Submodule.span ℂ (Set.range fun q : A × (∀ w : S, B w) ↦
    e (q.1 ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, q.2 w))))
  have hpure (a : A) (g : ∀ w, B w) :
      e (a ⊗ₜ[ℂ] (show V from (⨂ₜ[ℂ] w, g w))) ∈ D := Submodule.subset_span ⟨(a, g), rfl⟩
  have hgen (a : A) (v : V) : e (a ⊗ₜ[ℂ] v) ∈ D := by
    let L : V →ₗ[ℂ] ℬₛ(S) := e.toLinearMap.comp (TensorProduct.mk ℂ A V a)
    change L v ∈ D
    refine PiTensorProduct.induction_on (motive := fun v : ⨂[ℂ] w, B w ↦ L v ∈ D) v ?_ ?_
    · intro r g
      change L (r • (show V from (⨂ₜ[ℂ] w, g w))) ∈ D
      rw [map_smul]
      exact D.smul_mem r (hpure a g)
    · intro x y hx hy
      exact (D.comap L).add_mem hx hy
  have hfD : f ∈ D := by
    obtain ⟨z, rfl⟩ := e.surjective f
    exact TensorProduct.inductionOn (motive := fun z ↦ e z ∈ D) z hgen
      (fun _ _ hx hy ↦ (D.comap e.toLinearMap).add_mem hx hy)
  obtain ⟨m, c, x, hxs, hx⟩ := sLocalAdelicThetaSpace_strictLF_span_eval _ f hfD
  choose q hq using hxs
  refine ⟨m, c, fun i ↦ (q i).1, fun i ↦ (q i).2, fun y ↦ ?_⟩
  refine (hx (Multiplicative.ofAdd y)).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [← hq i]
  exact congrArg (c i * ·) (he (q i).1 (q i).2 y)

/-- Orbit sums at one finite place. The dilates of a finite family of local tests by the
elements congruent to one modulo a positive power of the maximal ideal form a finite set of
families, and summing a fixed member over this set gives a local test fixed by those
elements, which permute the set. -/
private theorem sLocalAdelicThetaSpace_strictLF_orbit_sum (w : HeightOneSpectrum (𝓞 F))
    (n m : ℕ) (G : Fin m → SchwartzBruhat (Multiplicative (w.adicCompletion F))) :
    ∃ Ω : Finset (Fin m → SchwartzBruhat (Multiplicative (w.adicCompletion F))),
      Ω.Nonempty ∧
      (∀ ω ∈ Ω, ∃ u : (w.adicCompletion F)ˣ,
        Valued.v (u.val - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) ∧
        ∀ k, ω k = schwartzBruhatUnitTranslate u (G k)) ∧
      ∀ (k : Fin m) (u y : w.adicCompletion F),
        Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) →
        (∑ ω ∈ Ω, ω k) (Multiplicative.ofAdd (u * y)) =
          (∑ ω ∈ Ω, ω k) (Multiplicative.ofAdd y) := by
  classical
  let K := w.adicCompletion F
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  let ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n + 1 : ℤ))
  let Hs : Set Kˣ := {u | ν (u.val - 1) ≤ ε}
  have hmulH (u u' : Kˣ) (hu : u ∈ Hs) (hu' : u' ∈ Hs) : u * u' ∈ Hs := by
    change ν ((u * u').val - 1) ≤ ε
    rw [Units.val_mul]
    exact (sLocalAdelicThetaSpace_strictLF_level_mul n u.val u'.val hu).2.mpr hu'
  have hinvH (u : Kˣ) (hu : u ∈ Hs) : u⁻¹ ∈ Hs := by
    refine (sLocalAdelicThetaSpace_strictLF_level_mul n u.val (u⁻¹).val hu).2.mp ?_
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, sub_self, map_zero]
    exact zero_le
  have hone : (1 : Kˣ) ∈ Hs := by
    change ν ((1 : Kˣ).val - 1) ≤ ε
    rw [Units.val_one, sub_self, map_zero]
    exact zero_le
  have hext (g₁ g₂ : SchwartzBruhat (Multiplicative K))
      (h : ∀ y : K, g₁ (Multiplicative.ofAdd y) = g₂ (Multiplicative.ofAdd y)) : g₁ = g₂ :=
    Subtype.ext (funext fun x ↦ h x.toAdd)
  have hτmul (u u' : Kˣ) (g : SchwartzBruhat (Multiplicative K)) :
      schwartzBruhatUnitTranslate u (schwartzBruhatUnitTranslate u' g) =
        schwartzBruhatUnitTranslate (u * u') g := hext _ _ fun y ↦ by
    rw [schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply,
      schwartzBruhatUnitTranslate_apply, mul_inv_rev, Units.val_mul, mul_assoc]
  have hτone (g : SchwartzBruhat (Multiplicative K)) :
      schwartzBruhatUnitTranslate (1 : Kˣ) g = g := hext _ _ fun y ↦ by
    rw [schwartzBruhatUnitTranslate_apply, inv_one, Units.val_one, one_mul]
  let T (u : Kˣ) : Fin m → SchwartzBruhat (Multiplicative K) :=
    fun k ↦ schwartzBruhatUnitTranslate u (G k)
  have hOfin : (T '' Hs).Finite := by
    let C : Set K := {x | ν x ≤ 1}
    have hC : IsCompact C :=
      isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w)
    have hk (k : Fin m) := finite_unit_dilates C hC (G k)
      ((mem_finitePlaceSchwartz_iff F w _).mp ⟨G k, fun _ ↦ rfl⟩).1
      ((mem_finitePlaceSchwartz_iff F w _).mp ⟨G k, fun _ ↦ rfl⟩).2
    refine (Set.Finite.pi fun k ↦ hk k).subset ?_
    rintro _ ⟨u, hu, rfl⟩ k -
    refine ⟨⟨u, ?_, ?_⟩, rfl⟩
    · exact (sLocalAdelicThetaSpace_strictLF_level_mul n u.val 1 hu).1.le
    · exact (sLocalAdelicThetaSpace_strictLF_level_mul n (u⁻¹).val 1 (hinvH u hu)).1.le
  let Ω := hOfin.toFinset
  have hΩ (ω : Fin m → SchwartzBruhat (Multiplicative K)) : ω ∈ Ω ↔ ∃ u ∈ Hs, T u = ω := by
    rw [Set.Finite.mem_toFinset]
    rfl
  refine ⟨Ω, ⟨T 1, (hΩ _).mpr ⟨1, hone, rfl⟩⟩, fun ω hω ↦ ?_, fun k u y hu ↦ ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (hΩ ω).mp hω
    exact ⟨u, hu, fun k ↦ rfl⟩
  · have hu1 : ν u = 1 := (sLocalAdelicThetaSpace_strictLF_level_mul n u 1 hu).1
    have hu0 : u ≠ 0 := fun h0 ↦ by
      rw [h0, map_zero] at hu1
      exact zero_ne_one hu1
    let U : Kˣ := Units.mk0 u hu0
    have hU : U ∈ Hs := hu
    let ev (x : K) : SchwartzBruhat (Multiplicative K) →ₗ[ℂ] ℂ :=
      (LinearMap.proj (Multiplicative.ofAdd x)).comp (schwartzBruhatSubmodule _).subtype
    change ev (u * y) (∑ ω ∈ Ω, ω k) = ev y (∑ ω ∈ Ω, ω k)
    rw [map_sum, map_sum]
    refine Finset.sum_nbij' (fun ω k ↦ schwartzBruhatUnitTranslate U⁻¹ (ω k))
      (fun ω k ↦ schwartzBruhatUnitTranslate U (ω k)) ?_ ?_ ?_ ?_ ?_
    · intro ω hω
      obtain ⟨u', hu', rfl⟩ := (hΩ ω).mp hω
      exact (hΩ _).mpr ⟨U⁻¹ * u', hmulH _ _ (hinvH U hU) hu',
        funext fun k ↦ (hτmul U⁻¹ u' (G k)).symm⟩
    · intro ω hω
      obtain ⟨u', hu', rfl⟩ := (hΩ ω).mp hω
      exact (hΩ _).mpr ⟨U * u', hmulH _ _ hU hu', funext fun k ↦ (hτmul U u' (G k)).symm⟩
    · intro ω _
      funext k
      rw [hτmul, mul_inv_cancel, hτone]
    · intro ω _
      funext k
      rw [hτmul, inv_mul_cancel, hτone]
    · intro ω _
      change ω k (Multiplicative.ofAdd (u * y)) =
        schwartzBruhatUnitTranslate U⁻¹ (ω k) (Multiplicative.ofAdd y)
      rw [schwartzBruhatUnitTranslate_apply, inv_inv]
      rfl


open scoped TensorProduct in
/-- Averaging over a congruence level. If the theta function of a test is invariant under
the S-ideles with archimedean coordinate `1` and finite coordinates congruent to `1` modulo
the `(n+1)`-st power of the maximal ideals, it is a combination of theta functions of pure
tensors whose local factors are fixed by the elements congruent to `1`. Write the test as a
combination of pure tensors. At each place the dilates of its local factors by these
elements form a finite set, and summing over the products of these sets replaces every
local factor by its orbit sum, while each summand is a dilate of the test and has the same
theta function. -/
private theorem sLocalAdelicThetaSpace_strictLF_level_average
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (f : ℬₛ(S))
    (hf : ∀ h g : (SAdeleRing F S)ˣ, h.val.1 = 1 →
      (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
      sLocalAdelicTheta F S f (h * g) = sLocalAdelicTheta F S f g) :
    sLocalAdelicTheta F S f ∈ Submodule.span ℂ
      {φ | ∃ (f' : ℬₛ(S)) (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
        (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
        (∀ (w : S) (u y : w.val.adicCompletion F),
          Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) →
          g w (Multiplicative.ofAdd (u * y)) = g w (Multiplicative.ofAdd y)) ∧
        (∀ x : SAdeleRing F S, f' (Multiplicative.ofAdd x) =
          a (Multiplicative.ofAdd x.1) * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w))) ∧
        φ = sLocalAdelicTheta F S f'} := by
  classical
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let B (w : S) := SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let V := FinestLocallyConvex (⨂[ℂ] w, B w)
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  obtain ⟨m, c, a, g, hfg⟩ := sLocalAdelicThetaSpace_strictLF_pure_sum f
  choose Ω hΩne hΩ hΩinv using fun w : S ↦
    sLocalAdelicThetaSpace_strictLF_orbit_sum (F := F) w.val n m (fun k ↦ g k w)
  let Φ (k : Fin m) : MultilinearMap (RingHom.id ℂ) (fun w : S ↦ B w) (ℬₛ(S)) :=
    (e.toLinearMap.comp (TensorProduct.mk ℂ A V (a k))).compMultilinearMap
      (PiTensorProduct.tprod ℂ)
  have hΦ (k : Fin m) (t : ∀ w : S, B w) (x : SAdeleRing F S) :
      Φ k t (Multiplicative.ofAdd x) = a k (Multiplicative.ofAdd x.1) *
        ∏ w : S, t w (Multiplicative.ofAdd (x.2 w)) := he (a k) t x
  let gbar (k : Fin m) (w : S) : B w := ∑ ω ∈ Ω w, ω k
  have hGen (k : Fin m) : sLocalAdelicTheta F S (Φ k (gbar k)) ∈ Submodule.span ℂ
      {φ | ∃ (f' : ℬₛ(S)) (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
        (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
        (∀ (w : S) (u y : w.val.adicCompletion F),
          Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) →
          g w (Multiplicative.ofAdd (u * y)) = g w (Multiplicative.ofAdd y)) ∧
        (∀ x : SAdeleRing F S, f' (Multiplicative.ofAdd x) =
          a (Multiplicative.ofAdd x.1) * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w))) ∧
        φ = sLocalAdelicTheta F S f'} :=
    Submodule.subset_span ⟨Φ k (gbar k), a k, gbar k, fun w u y hu ↦ hΩinv w k u y hu,
      fun x ↦ hΦ k (gbar k) x, rfl⟩
  let R := Fintype.piFinset Ω
  let fr (r : ∀ w : S, Fin m → B w) : ℬₛ(S) := ∑ k, c k • Φ k (fun w ↦ r w k)
  have hfr (r : ∀ w : S, Fin m → B w) (hr : r ∈ R) :
      sLocalAdelicTheta F S (fr r) = sLocalAdelicTheta F S f := by
    have hr' : ∀ w, r w ∈ Ω w := Fintype.mem_piFinset.mp hr
    choose u hu hru using fun w ↦ hΩ w (r w) (hr' w)
    let h : (SAdeleRing F S)ˣ :=
      MulEquiv.prodUnits.symm (1, MulEquiv.piUnits.symm fun w ↦ (u w)⁻¹)
    have h1 : h.val.1 = 1 := rfl
    have h2 (w : S) : h.val.2 w = ((u w)⁻¹).val := rfl
    have hlev (w : S) : Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
      rw [h2]
      refine (sLocalAdelicThetaSpace_strictLF_level_mul n (u w).val ((u w)⁻¹).val (hu w)).2.mp ?_
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, sub_self, map_zero]
      exact zero_le
    have hpt (x : SAdeleRing F S) : fr r (Multiplicative.ofAdd x) =
        f (Multiplicative.ofAdd (h.val * x)) := by
      rw [hfg (h.val * x)]
      refine (sLocalAdelicThetaSpace_strictLF_eval_sum Finset.univ c
        (fun k ↦ Φ k (fun w ↦ r w k)) (Multiplicative.ofAdd x)).trans
        (Finset.sum_congr rfl fun k _ ↦ ?_)
      rw [hΦ]
      have e1 : (h.val * x).1 = x.1 := by rw [Prod.fst_mul, h1, one_mul]
      rw [e1]
      congr 2
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [hru w k, schwartzBruhatUnitTranslate_apply]
      rfl
    ext g₀
    exact (sLocalAdelicThetaSpace_strictLF_theta_dilation h f (fr r) hpt g₀).trans
      (hf h g₀ h1 hlev)
  have hsum : ∑ r ∈ R, fr r = ∑ k, c k • Φ k (gbar k) := by
    change ∑ r ∈ R, ∑ k, c k • Φ k (fun w ↦ r w k) = _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.smul_sum]
    congr 1
    exact ((Φ k).map_sum_finset (fun w (ω : Fin m → B w) ↦ ω k) Ω).symm
  have hRne : R.Nonempty := Fintype.piFinset_nonempty.mpr hΩne
  have hN : (R.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hRne)
  have hθ : (R.card : ℂ) • sLocalAdelicTheta F S f =
      ∑ k, c k • sLocalAdelicTheta F S (Φ k (gbar k)) := by
    have h3 : sLocalAdelicTheta F S (∑ r ∈ R, fr r) = ∑ r ∈ R, sLocalAdelicTheta F S f := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun r hr ↦ hfr r hr
    rw [hsum, map_sum] at h3
    simp only [map_smul] at h3
    rw [h3, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hfinal : sLocalAdelicTheta F S f =
      (R.card : ℂ)⁻¹ • ∑ k, c k • sLocalAdelicTheta F S (Φ k (gbar k)) := by
    rw [← hθ, smul_smul, inv_mul_cancel₀ hN, one_smul]
  rw [hfinal]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ ↦
    Submodule.smul_mem _ _ (hGen k))

/-- Templates for a congruence level of S-local theta functions. There are finitely many
functions `β j` on the finite coordinates, fixed by the elements congruent to `1` modulo
the `(n+1)`-st power of the maximal ideals, and continuous linear maps `P j c` sending an
archimedean test `a` to the test `x ↦ a x₁ * β j (c⁻¹ x₂)`, such that the theta functions
of these tests span every theta function invariant under the S-ideles of that level. -/
private theorem sLocalAdelicThetaSpace_strictLF_level_templates
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
    ∃ (N : ℕ) (β : Fin N → ((w : S) → w.val.adicCompletion F) → ℂ)
      (P : Fin N → (SAdeleRing F S)ˣ →
        (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ] ℬₛ(S))),
      (∀ j c a (x : SAdeleRing F S), P j c a (Multiplicative.ofAdd x) =
        a (Multiplicative.ofAdd x.1) * β j ((c⁻¹).val.2 * x.2)) ∧
      (∀ j (h y : (w : S) → w.val.adicCompletion F),
        (∀ w : S, Valued.v (h w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
        β j (h * y) = β j y) ∧
      ∀ f : ℬₛ(S),
        (∀ h g : (SAdeleRing F S)ˣ, h.val.1 = 1 →
          (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
          sLocalAdelicTheta F S f (h * g) = sLocalAdelicTheta F S f g) →
        sLocalAdelicTheta F S f ∈ Submodule.span ℂ (Set.range fun q : Fin N ×
          (SAdeleRing F S)ˣ × SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) ↦
            sLocalAdelicTheta F S (P q.1 q.2.1 q.2.2)) := by
  obtain ⟨N, β, P, hP, hβ, hpure⟩ := sLocalAdelicThetaSpace_strictLF_level_pure (F := F) S n
  refine ⟨N, β, P, hP, hβ, fun f hf ↦ ?_⟩
  refine Submodule.span_le.mpr ?_ (sLocalAdelicThetaSpace_strictLF_level_average S n f hf)
  rintro _ ⟨f', a, g, hg, hf', rfl⟩
  have hmap := Submodule.apply_mem_span_image_of_mem_span (sLocalAdelicTheta F S)
    (hpure f' a g hg hf')
  rwa [← Set.range_comp] at hmap


/-- Dilating all coordinates of a test function by an S-unit does not change its S-local
theta function: the dilation permutes the terms of the series. -/
private theorem sLocalAdelicThetaSpace_strictLF_theta_unit_dilation
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (ξ : (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ) (f₁ f₂ : ℬₛ(S))
    (h : ∀ x : SAdeleRing F S, f₂ (Multiplicative.ofAdd x) =
      f₁ (Multiplicative.ofAdd ((sUnitEmbedding F S ξ).val * x))) :
    sLocalAdelicTheta F S f₂ = sLocalAdelicTheta F S f₁ := by
  ext g
  refine (sLocalAdelicTheta_apply F S f₂ g).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f₁ g).symm)
  refine Eq.trans (tsum_congr fun η ↦ ?_) ((Equiv.mulLeft ξ).tsum_eq
    (fun η ↦ f₁ (Multiplicative.ofAdd (sUnitEmbedding F S η * g).val)))
  change f₂ (Multiplicative.ofAdd (sUnitEmbedding F S η * g).val) =
    f₁ (Multiplicative.ofAdd (sUnitEmbedding F S (ξ * η) * g).val)
  have e : (sUnitEmbedding F S (ξ * η) * g).val =
      (sUnitEmbedding F S ξ).val * (sUnitEmbedding F S η * g).val := by
    rw [map_mul (sUnitEmbedding F S) ξ η, mul_assoc, Units.val_mul]
  rw [h, e]

/-- Finiteness of the finite S-idele classes modulo S-units and a congruence level: the
finite part of every S-idele is that of one of finitely many fixed ideles, up to an S-unit
and a factor congruent to one. The norm-one S-idele classes are compact, and the canonical
norm section has trivial finite part. -/
private theorem sLocalAdelicThetaSpace_strictLF_finite_idele_classes
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
    ∃ s : Finset (SAdeleRing F S)ˣ, ∀ c : (SAdeleRing F S)ˣ,
      ∃ r ∈ s, ∃ (ξ : (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ)
        (h : (w : S) → w.val.adicCompletion F),
        (∀ w : S, Valued.v (h w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) ∧
        (c⁻¹).val.2 * (sUnitEmbedding F S ξ).val.2 = (r⁻¹).val.2 * h := by
  classical
  obtain ⟨K, hK, hRep⟩ := sLocalTheta_exists_compact_representatives F S
  let B (w : S) : Set (w.val.adicCompletion F) :=
    {u | Valued.v (u - 1) ≤ WithZero.exp (-(n + 1 : ℤ))}
  have hB (w : S) : B w ∈ 𝓝 (1 : w.val.adicCompletion F) := by
    let ν : Valuation (w.val.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨z, hz⟩ := w.val.valuedAdicCompletion_surjective F (WithZero.exp (-(n + 1 : ℤ)))
    have hz0 : ν.restrict z ≠ 0 := fun h0 ↦
      WithZero.exp_ne_zero (hz.symm.trans (ν.restrict_eq_zero_iff.mp h0))
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ hz0, fun u hu ↦ ?_⟩
    have hlt : ν (u - 1) < ν z := ν.restrict_lt_iff.mp hu
    exact (hz ▸ hlt).le
  let O (r : (SAdeleRing F S)ˣ) : Set (SAdeleRing F S)ˣ :=
    {k | ∀ w : S, r.val.2 w * (k⁻¹).val.2 w ∈ B w}
  have hO (r : (SAdeleRing F S)ˣ) : O r ∈ 𝓝 r := by
    have hset : O r = ⋂ w : S, {k | r.val.2 w * (k⁻¹).val.2 w ∈ B w} := by
      ext k
      simp only [O, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    refine Filter.iInter_mem.mpr fun w ↦ ?_
    have hcont : Continuous (fun k : (SAdeleRing F S)ˣ ↦ r.val.2 w * (k⁻¹).val.2 w) :=
      continuous_const.mul ((continuous_apply w).comp
        (continuous_snd.comp (Units.continuous_val.comp continuous_inv)))
    have h1 : r.val.2 w * (r⁻¹).val.2 w = 1 :=
      congrArg (fun g : (SAdeleRing F S)ˣ ↦ g.val.2 w) (mul_inv_cancel r)
    exact hcont.continuousAt.preimage_mem_nhds (by rw [h1]; exact hB w)
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover O (fun r _ ↦ hO r)
  refine ⟨s, fun c ↦ ?_⟩
  let t := sIdeleNorm F S c
  let a : (SAdeleRing F S)ˣ :=
    Units.map (adeleProjection F S).toMonoidHom (canonicalIdeleNormSection F t)
  have haNorm : sIdeleNorm F S a = t := sLocalTheta_radial_norm F S t
  have hnorm : sIdeleQuotientNorm F S (QuotientGroup.mk (a⁻¹ * c)) = 1 := by
    rw [sIdeleQuotientNorm_mk, map_mul, map_inv, haNorm]
    exact inv_mul_cancel t
  obtain ⟨k, hkK, hk⟩ := hRep _ hnorm
  have hmem := QuotientGroup.eq.mp hk
  rw [sProjectedDiagonal, MonoidHom.map_range, MonoidHom.mem_range] at hmem
  obtain ⟨ξ, hξ⟩ := hmem
  have hc : c⁻¹ * sUnitEmbedding F S ξ = k⁻¹ * a⁻¹ := by
    have hξ' : sUnitEmbedding F S ξ = k⁻¹ * (a⁻¹ * c) := hξ
    rw [hξ', mul_comm c⁻¹, ← mul_assoc, mul_inv_cancel_right]
  have ha2 : a.val.2 = 1 := by
    funext w
    change (canonicalIdeleNormSection F t).val.2 w.val = 1
    exact congrArg (fun b : FiniteAdeleRing (𝓞 F) F ↦ b w.val)
      (canonicalIdeleNormSection_finite F t)
  have ha2' : (a⁻¹).val.2 = 1 := by
    have h1 : (a⁻¹).val.2 * a.val.2 = 1 :=
      congrArg (fun g : (SAdeleRing F S)ˣ ↦ g.val.2) (inv_mul_cancel a)
    rwa [ha2, mul_one] at h1
  obtain ⟨r, hr, hkr⟩ := Set.mem_iUnion₂.mp (hs hkK)
  refine ⟨r, hr, ξ, fun w ↦ r.val.2 w * (k⁻¹).val.2 w, hkr, ?_⟩
  have e1 : (c⁻¹).val.2 * (sUnitEmbedding F S ξ).val.2 = (k⁻¹).val.2 * (a⁻¹).val.2 :=
    congrArg (fun g : (SAdeleRing F S)ˣ ↦ g.val.2) hc
  rw [e1, ha2', mul_one]
  funext w
  have h1 : (r⁻¹).val.2 w * r.val.2 w = 1 :=
    congrArg (fun g : (SAdeleRing F S)ˣ ↦ g.val.2 w) (inv_mul_cancel r)
  change (k⁻¹).val.2 w = (r⁻¹).val.2 w * (r.val.2 w * (k⁻¹).val.2 w)
  rw [← mul_assoc, h1, one_mul]


/-- Finite generation of a level of S-local theta functions. For each `n`, finitely many
continuous linear maps `p j` from the archimedean Schwartz space to the S-adelic test space
represent every theta function that is invariant under the S-ideles with archimedean
coordinate `1` and finite coordinates congruent to `1` modulo the `(n+1)`-st power of the
maximal ideals. The maps are the templates of
`sLocalAdelicThetaSpace_strictLF_level_templates` dilated by the finitely many ideles of
`sLocalAdelicThetaSpace_strictLF_finite_idele_classes`: any other dilate differs from one
of these by a factor fixing the template and an S-unit, which can be moved to the
archimedean test without changing the theta function. -/
theorem sLocalAdelicThetaSpace_strictLF_level_generators
    (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
    ∃ (d : ℕ) (p : Fin d →
        (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ] ℬₛ(S))),
      ∀ f : ℬₛ(S),
        (∀ h g : (SAdeleRing F S)ˣ, h.val.1 = 1 →
          (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) →
          sLocalAdelicTheta F S f (h * g) = sLocalAdelicTheta F S f g) →
        ∃ a : Fin d → SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
          sLocalAdelicTheta F S (∑ j, p j (a j)) = sLocalAdelicTheta F S f := by
  classical
  obtain ⟨N, β, P, hP, hβ, hrep⟩ :=
    sLocalAdelicThetaSpace_strictLF_level_templates (F := F) S n
  obtain ⟨s, hs⟩ := sLocalAdelicThetaSpace_strictLF_finite_idele_classes (F := F) S n
  let ι := Fin N × {r // r ∈ s}
  let E : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let p : Fin (Fintype.card ι) →
      (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) →L[ℂ] ℬₛ(S)) :=
    fun q ↦ P (E.symm q).1 (E.symm q).2.val
  refine ⟨Fintype.card ι, p, fun f hf ↦ ?_⟩
  let G : Submodule ℂ C((SAdeleRing F S)ˣ, ℂ) :=
    { carrier := {φ | ∃ a : Fin (Fintype.card ι) →
        SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
        sLocalAdelicTheta F S (∑ q, p q (a q)) = φ}
      zero_mem' := ⟨0, by simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
        exact ⟨a + a', by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]⟩
      smul_mem' := by
        rintro c _ ⟨a, rfl⟩
        exact ⟨c • a, by simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum]⟩ }
  have hG : Submodule.span ℂ (Set.range fun q : Fin N × (SAdeleRing F S)ˣ ×
      SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) ↦
        sLocalAdelicTheta F S (P q.1 q.2.1 q.2.2)) ≤ G := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨j, c, a⟩, rfl⟩
    obtain ⟨r, hr, ξ, h, hh, heq⟩ := hs c
    let u : (InfiniteAdeleRing F)ˣ :=
      Units.map (RingHom.fst _ _).toMonoidHom (sUnitEmbedding F S ξ)
    refine ⟨Pi.single (E (j, ⟨r, hr⟩)) (schwartzBruhatUnitTranslate u⁻¹ a), ?_⟩
    have hsum : ∑ q, p q ((Pi.single (E (j, ⟨r, hr⟩)) (schwartzBruhatUnitTranslate u⁻¹ a) :
        Fin (Fintype.card ι) → SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) q) =
        P j r (schwartzBruhatUnitTranslate u⁻¹ a) := by
      rw [Finset.sum_eq_single (E (j, ⟨r, hr⟩))]
      · rw [Pi.single_eq_same]
        change P (E.symm (E (j, ⟨r, hr⟩))).1 (E.symm (E (j, ⟨r, hr⟩))).2.val _ = _
        rw [Equiv.symm_apply_apply]
      · intro q _ hq
        rw [Pi.single_eq_of_ne hq, map_zero]
      · intro hne
        exact absurd (Finset.mem_univ _) hne
    change sLocalAdelicTheta F S (∑ q, p q ((Pi.single (E (j, ⟨r, hr⟩))
      (schwartzBruhatUnitTranslate u⁻¹ a) : Fin (Fintype.card ι) →
        SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) q)) = _
    rw [hsum]
    refine sLocalAdelicThetaSpace_strictLF_theta_unit_dilation ξ _ _ fun x ↦ ?_
    rw [hP, hP]
    have e0 : schwartzBruhatUnitTranslate u⁻¹ a (Multiplicative.ofAdd x.1) =
        a (Multiplicative.ofAdd ((sUnitEmbedding F S ξ).val * x).1) :=
      (schwartzBruhatUnitTranslate_apply u⁻¹ a x.1).trans
        (congrArg (fun y ↦ a (Multiplicative.ofAdd (y * x.1)))
          (congrArg Units.val (inv_inv u)))
    have e1 : (c⁻¹).val.2 * ((sUnitEmbedding F S ξ).val * x).2 =
        h * ((r⁻¹).val.2 * x.2) := by
      rw [Prod.snd_mul, ← mul_assoc, heq, mul_comm (r⁻¹).val.2 h, mul_assoc]
    rw [e0, e1, hβ j h _ hh]
  exact hG (hrep f hf)

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem sLocalAdelicThetaSpace_strictLF : IsStrictLFSpace (Θₛ(S)) := by
  classical
  -- The archimedean Schwartz–Bruhat space is Fréchet: it is the classical Schwartz space.
  obtain ⟨J, -⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  have hSch : IsFrechetTVS (SchwartzMap (mixedEmbedding.mixedSpace F) ℂ) := by
    have : (uniformity (SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)).IsCountablyGenerated := by
      rw [uniformity_eq_comap_nhds_zero]
      infer_instance
    refine ⟨inferInstance, (schwartz_withSeminorms ℂ _ _).toPolynormableSpace,
      UniformSpace.metrizableSpace, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    exact completeSpace_schwartzMap
  have hA : IsFrechetTVS (SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :=
    sLocalAdelicThetaSpace_strictLF_frechet_of_closed_embedding J.symm.toContinuousLinearMap
      J.symm.toHomeomorph.isClosedEmbedding hSch
  -- Each value of the theta function depends continuously on the test function.
  have hev (g : (SAdeleRing F S)ˣ) :
      Continuous (fun f : ℬₛ(S) ↦ sLocalAdelicTheta F S f g) := by
    let : BarrelledSpace ℂ (ℬₛ(S)) := (sAdeleSchwartz_montel (F := F) S).1
    let : Countable F := Countable.of_moduleFinite (R := ℚ)
    let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ :=
      Units.val_injective.countable
    exact schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
      (sLocalAdelicTheta_hasSumUniformlyOn F S f {g} isCompact_singleton).hasSum rfl
  -- Level `n`: invariance under the ideles with archimedean coordinate `1` and finite
  -- coordinates congruent to `1` modulo the `(n+1)`-st power of the maximal ideals.
  let R (n : ℕ) : Set ((SAdeleRing F S)ˣ × (SAdeleRing F S)ˣ) :=
    {r | ∃ h : (SAdeleRing F S)ˣ, h.val.1 = 1 ∧
      (∀ w : S, Valued.v (h.val.2 w - 1) ≤ WithZero.exp (-(n + 1 : ℤ))) ∧ r.1 = h * r.2}
  refine sLocalAdelicThetaSpace_strictLF_of_levels (sLocalAdelicTheta F S)
    sLocalAdelicThetaSpace_lf hA hev R ?_ ?_ ?_
  · rintro n r ⟨h, h1, hw, hr⟩
    refine ⟨h, h1, fun w ↦ (hw w).trans (WithZero.exp_le_exp.mpr ?_), hr⟩
    push_cast
    omega
  · intro f
    obtain ⟨n, hn⟩ := sLocalAdelicThetaSpace_strictLF_level_cover f
    refine ⟨n, ?_⟩
    rintro ⟨r₁, r₂⟩ ⟨h, h1, hw, hr⟩
    rw [show r₁ = h * r₂ from hr]
    exact hn h r₂ h1 hw
  · intro n
    obtain ⟨d, p, hp⟩ := sLocalAdelicThetaSpace_strictLF_level_generators (F := F) S n
    refine ⟨d, p, fun f hf ↦ hp f fun h g h1 hw ↦ ?_⟩
    exact hf (h * g, g) ⟨h, h1, hw, rfl⟩

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_complete :
    @CompleteSpace (Θₛ(S)) (IsTopologicalAddGroup.rightUniformSpace (Θₛ(S))) := by
  exact IsStrictLFSpace.completeSpace (E := (Θₛ(S))) sLocalAdelicThetaSpace_strictLF

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_nuclear : IsNuclearTVS Θ𝔽 := by
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed adelicTheta_ker_isClosed
  exact isNuclearTVS_quotient (adeleSchwartz_nuclear (F := F)).2 _

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_nuclear : IsNuclearTVS (Θₛ(S)) := by
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed sLocalAdelicTheta_ker_isClosed
  exact isNuclearTVS_quotient (sAdeleSchwartz_nuclear F S) _

section BoundedSets

open Bornology Set
open scoped Pointwise

/-- Each continuous seminorm on a Schwartz space admits finite nets on bounded sets. -/
private theorem totallyBounded_of_schwartz
    {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    (hS : IsSchwartzTVS E) {B : Set E} (hB : IsVonNBounded ℂ B) :
    TotallyBounded B := by
  let : PolynormableSpace ℂ E := hS.1
  apply (PolynormableSpace.hasBasis_zero_ball ℂ E).uniformity_of_nhds_zero_swapped.totallyBounded_iff.mpr
  intro p hp
  obtain ⟨V, hV, htotal⟩ := hS.2 p hp
  obtain ⟨r, hr, hsub⟩ := (hB hV).exists_pos
  let c : ℂ := r
  have hBV : B ⊆ c • V := hsub c (by simp [c, abs_of_pos hr])
  let := p.toSeminormedAddCommGroup
  let : UniformSpace E := p.toSeminormedAddCommGroup.toUniformSpace
  have hsmul : LipschitzWith ‖c‖₊ (c • · : E → E) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [dist_eq_norm_sub, dist_eq_norm_sub, ← smul_sub]
      exact (map_smul_eq_mul p c (x - y)).le
  have htotalB : TotallyBounded B :=
    (htotal.image hsmul.uniformContinuous).subset hBV
  obtain ⟨A, hA, hcover⟩ := Metric.totallyBounded_iff.mp htotalB 1 zero_lt_one
  refine ⟨A, hA, fun x hx ↦ ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hcover hx)
  refine mem_iUnion₂.mpr ⟨a, ha, ?_⟩
  change x - a ∈ p.ball 0 1
  rwa [p.sub_mem_ball, add_zero, p.ball_eq_metric]

/-- Bounded sets in the global theta space are totally bounded, independently of
the completeness of its quotient topology. -/
theorem globalAdelicThetaSpace_bounded_totallyBounded {B : Set Θ𝔽} (hB : Bornology.IsVonNBounded ℂ B) :
    @TotallyBounded Θ𝔽 (IsTopologicalAddGroup.rightUniformSpace _) B := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  exact totallyBounded_of_schwartz (isSchwartzTVS_of_isNuclearTVS.{0} (globalAdelicThetaSpace_nuclear (F := F))) hB

/-- Bounded sets in every finite theta quotient are totally bounded. -/
theorem sLocalAdelicThetaSpace_bounded_totallyBounded {B : Set (Θₛ(S))} (hB : Bornology.IsVonNBounded ℂ B) :
    @TotallyBounded (Θₛ(S)) (IsTopologicalAddGroup.rightUniformSpace _) B := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  exact totallyBounded_of_schwartz (isSchwartzTVS_of_isNuclearTVS.{0} (sLocalAdelicThetaSpace_nuclear (F := F) (S := S))) hB

end BoundedSets

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_barrelled : BarrelledSpace ℂ Θ𝔽 :=
  IsLFSpace.barrelled (E := Θ𝔽) globalAdelicThetaSpace_lf

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_barrelled : BarrelledSpace ℂ (Θₛ(S)) :=
  IsLFSpace.barrelled (E := Θₛ(S)) sLocalAdelicThetaSpace_lf

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_montel : MontelSpace ℂ (Θₛ(S)) := montelSpace_of_nuclear_strictLF.{0} sLocalAdelicThetaSpace_strictLF
    sLocalAdelicThetaSpace_nuclear

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is complete. -/
theorem globalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ Θ𝔽) := by
  let : CompleteSpace (StrongDual ℂ ℬ𝔽) := (adeleSchwartz_strongDual_complete (F := F)).2
  exact completeSpace_strongDual_quotient _

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is complete. -/
theorem sLocalAdelicThetaSpace_strongDual_complete : CompleteSpace (StrongDual ℂ (Θₛ(S))) := by
  let : CompleteSpace (StrongDual ℂ (ℬₛ(S))) := sAdeleSchwartz_strongDual_complete F S
  exact completeSpace_strongDual_quotient _

private theorem isEmbedding_transpose_quotient_of_strictLF {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (K : Submodule ℂ E)
    (hE : IsStrictLFSpace E) (hN : IsNuclearTVS.{0} E) (hK : IsClosed (K : Set E))
    (hQ : IsStrictLFSpace (E ⧸ K)) : IsEmbedding (fun l : StrongDual ℂ (E ⧸ K) ↦ l.comp K.mkQL) := by
  let := hN.1
  let := hQ.1
  obtain ⟨_, V, hV, hF, hex, ht⟩ := hE
  let j (n : ℕ) := (V n).subtypeL.codRestrict (V (n+1)) fun x ↦ hV n.le_succ x.property
  have hj (n : ℕ) : IsEmbedding (j n) :=
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal
  have hlim : IsInjectiveLCLimit j (fun n ↦ (V n).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, ht⟩
    obtain ⟨n, hn⟩ := hex x
    exact ⟨n, ⟨x, hn⟩, rfl⟩
  have hlift := (liftsBoundedSets_quotient_of_nuclear_strictLF hlim hj hF
    (fun n ↦ isNuclearTVS_submodule hN (V n)) K hK hQ (isNuclearTVS_quotient hN K)).1
  let R : StrongDual ℂ (E ⧸ K) →L[ℂ] StrongDual ℂ E := ContinuousLinearMap.precomp ℂ K.mkQL
  change IsEmbedding R
  constructor
  · apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
    refine le_antisymm (map_le_iff_le_comap.mp ?_) ?_
    · simpa only [Tendsto, map_zero] using R.continuous.tendsto 0
    · apply ContinuousLinearMap.hasBasis_nhds_zero.ge_iff.mpr
      rintro ⟨B, U⟩ ⟨hB, hU⟩
      obtain ⟨A, hA, hBA⟩ := hlift B hB
      refine mem_comap.mpr ⟨{l : StrongDual ℂ E | Set.MapsTo l A U},
        ContinuousLinearMap.eventually_nhds_zero_mapsTo hA hU, ?_⟩
      intro l hl b hb
      obtain ⟨a, ha, rfl⟩ := hBA hb
      exact hl ha
  · intro l m he
    ext x
    obtain ⟨a, rfl⟩ := K.mkQ_surjective x
    exact DFunLike.congr_fun he a

universe v

private theorem nuclear_of_linear_embedding {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →L[ℂ] Y)
    (hi : IsEmbedding i) (hY : IsNuclearTVS.{v} Y) : IsNuclearTVS.{v} X := by
  let : PolynormableSpace ℂ Y := hY.2.1
  have : PolynormableSpace ℂ X := hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap
  let e := LinearEquiv.ofInjective i.toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] i.toLinearMap.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact nuclear_of_equiv L.symm (isNuclearTVS_submodule hY _)

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is nuclear. -/
theorem sLocalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ (Θₛ(S))) := by
  apply nuclear_of_linear_embedding (ContinuousLinearMap.precomp ℂ (Kₛ(S)).mkQL)
  · exact isEmbedding_transpose_quotient_of_strictLF _ (sAdeleSchwartz_strictLF F S)
      (sAdeleSchwartz_nuclear F S) sLocalAdelicTheta_ker_isClosed sLocalAdelicThetaSpace_strictLF
  · exact (sAdeleSchwartz_strongDual_nuclear F S)

private theorem barrelled_strongDual_of_montel {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MontelSpace ℂ E] : BarrelledSpace ℂ (StrongDual ℂ E) := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  apply barrelled_of_barrel_nbhd
  apply strongDual_barrel_nbhd
  intro l
  obtain ⟨x, rfl⟩ := surjective_strongBidual_eval l
  exact ⟨x, fun _ ↦ rfl⟩

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the S-local theta quotient is barrelled. -/
theorem sLocalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (Θₛ(S))) := by
    let : T2Space (Θₛ(S)) := (sLocalAdelicThetaSpace_lf (F := F) (S := S)).1
    let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
    let : MontelSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_montel
    exact barrelled_strongDual_of_montel

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the S-local theta quotient. -/
theorem sLocalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ (Θₛ(S))) := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_barrelled (F := F) (S := S)
  exact montelSpace_strongDual_of_precompact (fun _ hb ↦ sLocalAdelicThetaSpace_bounded_totallyBounded (F := F) (S := S) hb)

/-- On every family bounded after pullback, the global theta transpose is an
embedding for bounded convergence. This does not require strictness of the quotient. -/
theorem globalThetaQuotient_transpose_isEmbedding_of_bounded_image (B : Set (StrongDual ℂ Θ𝔽))
    (hB : Bornology.IsVonNBounded ℂ ((fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL) '' B)) :
    IsEmbedding (fun l : B ↦ l.val.comp (K𝔽).mkQL) := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ Θ𝔽 := globalAdelicThetaSpace_barrelled (F := F)
  exact isEmbedding_transpose_of_bounded_image (K𝔽).mkQL (K𝔽).mkQ_surjective
    (fun _ hb ↦ globalAdelicThetaSpace_bounded_totallyBounded (F := F) hb) B hB

/-- In bounded convergence the transpose has closed range independently of strictness. -/
theorem globalThetaQuotient_transpose_isClosed_range :
    IsClosed (Set.range (fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL)) :=
  isClosed_range_transpose_mkQL _

end Topology

-- TODO(paper-gap): Footnote 1 on p. 230 asks for a version with an
-- I-exponentially decaying target without giving a statement.
-- TODO(paper-gap): Footnote 2 on p. 231 asks to adjust Theorem 5.2.1.1
-- and gives no replacement. Its proof needs a stage projection preserving
-- the theta kernel. For ℚ and S = {∞}, put e = 1_{ℤ̂}. Every tail functional
-- fixing e sends f − ρ(2)f, for f = φ ⊗ e, to (φ − c φ(·/2)) ⊗ e for some c.
-- For an even bump φ supported within 1/4 of ±1 with φ(±1) = 1, this has
-- theta values 2(1−c) and −2c at real scales 1 and 2. Thus the tensor
-- projections used on p. 73 cannot descend. The assertion on p. 232 about
-- convergence on bounded sets requires a family of projections on the quotients.

section Transitions

section KernelDescent

open Set

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "I" => IdeleGroup (𝓞 F) F
local notation "A" => 𝔸[F]
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "Uₛ(" S ")" => (Set.integer (S : Set V) F)ˣ
local notation "Aₛ(" S ")" => integralAdelesOutside F S

private theorem mul_integralUnit_mem_iff {R : Type*} [CommRing R] {D : Subring R} (u : Dˣ) (x : R) :
    u.val.val * x ∈ D ↔ x ∈ D := by
  constructor
  · intro h
    have hh := D.mul_mem u.inv.property h
    rwa [← mul_assoc, show u.inv.val * u.val.val = 1 from congrArg Subtype.val u.inv_val, one_mul] at hh
  · exact D.mul_mem u.val.property

private theorem toGlobal_apply_integral (f : ℬₛ(S)) (x : 𝔸[F]) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x) =
      open Classical in if x ∈ Aₛ(S) then f (Multiplicative.ofAdd (adeleProjection F S x)) else 0 := by
  classical
  have hi : x ∈ integralAdelesOutside F S ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      x.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  exact (sAdeleSchwartzToGlobal_apply F S f x).trans
    (if_congr hi.symm rfl rfl)

/-- On a fixed coset of the S-units, outside integrality holds everywhere or nowhere.
In the first case its sum is the local theta value at the projected idele. -/
private theorem thetaSum_zero_globalInsert (S : Finset (HeightOneSpectrum (𝓞 F))) (f : ℬₛ(S))
    (hf : sLocalAdelicTheta F S f = 0) (g : IdeleGroup (𝓞 F) F) :
    adelicTheta (sAdeleSchwartzToGlobal F S f) (QuotientGroup.mk g) = 0 := by
  classical
  let d := Units.map ((S : Set (HeightOneSpectrum (𝓞 F))).integer F).subtype.toMonoidHom
  let diag := Units.map (algebraMap F 𝔸[F]).toMonoidHom
  let a (t : Fˣ) := sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd ((diag t).val * g.val))
  have hd : Injective d := fun x y h ↦ Units.ext (Subtype.ext (congrArg Units.val h))
  have ha : Summable (fun t : Fˣ ↦ sAdeleSchwartzToGlobal F S f
      (Multiplicative.ofAdd (algebraMap F 𝔸[F] t.val * g.val))) := by
    have h := ((adelicAverage_summableUniformlyOn (sAdeleSchwartzToGlobal F S f)
      {(g, 0)} isCompact_singleton).summable rfl).of_norm
    exact h.congr fun t ↦ congrArg (fun x ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x))
      ((congrArg (g.val * ·) (add_zero _)).trans (mul_comm _ _))
  refine (adelicTheta_mk (sAdeleSchwartzToGlobal F S f) g).trans
    (tsum_zero_of_cosets (a := a) d hd ha (fun t ↦ ?_))
  let y := diag t * g
  let G := Units.map (integralAdeleDiagonal F S).toMonoidHom
  let proj := Units.map (adeleProjection F S).toMonoidHom
  let ψ (u : Uₛ(S)) := f (Multiplicative.ofAdd (adeleProjection F S ((G u).val.val * y.val)))
  have hterm (u : Uₛ(S)) : a (t * d u) =
      if y.val ∈ Aₛ(S) then ψ u else 0 := by
    have hm : (diag (t * d u)).val * g.val = (G u).val.val * y.val := by
      change algebraMap F 𝔸[F] (t.val * (d u).val) * g.val =
        algebraMap F 𝔸[F] (d u).val * (algebraMap F 𝔸[F] t.val * g.val)
      exact (congrArg (· * g.val) (map_mul (algebraMap F 𝔸[F]) _ _)).trans ((mul_assoc _ _ _).trans (mul_left_comm _ _ _))
    refine (congrArg (fun w ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd w)) hm).trans ?_
    exact (toGlobal_apply_integral f ((G u).val.val * y.val)).trans
      (if_congr (mul_integralUnit_mem_iff (G u) y.val) rfl rfl)
  refine (tsum_congr hterm).trans ?_
  by_cases hy : y.val ∈ Aₛ(S)
  · have localSum : ∑' u, ψ u = sLocalAdelicTheta F S f (proj y) := by
      exact tsum_congr fun u ↦ congrArg (fun x ↦ f (Multiplicative.ofAdd x))
        (map_mul (adeleProjection F S) (G u).val.val y.val)
    refine (tsum_congr (fun u ↦ ite_eq_left (t := ψ u) hy)).trans ?_
    exact localSum.trans (congrArg (fun φ : C((SAdeleRing F S)ˣ, ℂ) ↦ φ (proj y)) hf)
  · exact (tsum_congr fun u ↦ ite_eq_right (t := ψ u) hy).trans tsum_zero

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The global insertion of a test function sends the corresponding S-local theta kernel
into the global theta kernel. -/
theorem sLocalThetaToGlobal_preserves_kernel :
    Kₛ(S) ≤ (K𝔽).comap (sAdeleSchwartzToGlobal F S) := by
  intro f hf
  change adelicThetaLinearMap F (sAdeleSchwartzToGlobal F S f) = 0
  refine ContinuousMap.ext fun q ↦ ?_
  exact QuotientGroup.induction_on q (thetaSum_zero_globalInsert S f hf)

open Classical in
/-- Prescribe a finite set of strict valuation cutoffs outside S. -/
private theorem exists_cutIdele (S : Finset V) (B : Finset {v : V // v ∉ S}) :
    ∃ z : I, adeleProjection F S z.val = 1 ∧
      ∀ (v : V) (hv : v ∉ S) (t : Fˣ),
        ((algebraMap F A (t : F)).2 v * z.val.2 v ∈ O(v)) ↔
          if (⟨v, hv⟩ : {v : V // v ∉ S}) ∈ B then v.valuation F t.val < 1
          else v.valuation F t.val ≤ 1 := by
  classical
  choose b hb using fun v : V ↦ (v.valuation_surjective F (WithZero.exp (1 : ℤ)))
  have hb0 (v : V) : b v ≠ 0 := by
    intro h
    simpa [h] using (hb v).symm
  let β (v : V) := Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom (Units.mk0 (b v) (hb0 v))
  let B' := B.image Subtype.val
  let a (v : V) : (v.adicCompletion F)ˣ := if v ∈ B' then β v else 1
  let zFin : (FiniteAdeleRing (𝓞 F) F)ˣ :=
    { val := ⟨fun v ↦ (a v).val, by
        filter_upwards [B'.finite_toSet.compl_mem_cofinite] with v hv
        simp [a, show v ∉ B' from hv]⟩
      inv := ⟨fun v ↦ (a v).inv, by
        filter_upwards [B'.finite_toSet.compl_mem_cofinite] with v hv
        simp [a, show v ∉ B' from hv]⟩
      val_inv := by ext1 v; exact (a v).val_inv
      inv_val := by ext1 v; exact (a v).inv_val }
  let z : I := (MulEquiv.prodUnits ..).symm (1, zFin)
  refine ⟨z, Prod.ext rfl (funext fun v ↦ ?_), fun v hv t ↦ ?_⟩
  · have h : v.val ∉ B' := by
      rintro h
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
      exact w.property (hw ▸ v.property)
    change (a v.val).val = 1
    simp [a, h]
  · change Valued.v (((t : F) : v.adicCompletion F) * (a v).val) ≤ 1 ↔ _
    rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    by_cases h : (⟨v, hv⟩ : {v : V // v ∉ S}) ∈ B
    · have hvB : v ∈ B' := Finset.mem_image_of_mem Subtype.val h
      simp only [ite_eq_left h, a, ite_eq_left hvB]
      change v.valuation F t.val * Valued.v ((b v : F) : v.adicCompletion F) ≤ 1 ↔ _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hb]
      have ht : v.valuation F t.val ≠ 0 := by simp
      rw [← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero (M := ℤ)]
      simp only [WithZero.exp_le_exp, WithZero.exp_lt_exp]
      omega
    · have hvB : v ∉ B' := by
        rintro hx
        obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hx
        exact h ((Subtype.ext heq : w = ⟨v, hv⟩) ▸ hw)
      simp [a, hvB, h]

private theorem outsideCut_iff {ι : Type*} {L : Type*} [PartialOrder L] [One L]
    [DecidableEq ι] (B : Finset ι) (v : ι → L) :
     (∀ i, if i ∈ B then v i < 1 else v i ≤ 1) ↔
      (∀ i, v i ≤ 1) ∧ ∀ i ∈ B, v i < 1 := by
  classical
  constructor
  · intro h
    refine ⟨fun i ↦ ?_, fun i hi ↦ by simpa only [ite_eq_left hi] using h i⟩
    by_cases hi : i ∈ B
    · exact (show v i < 1 from by simpa only [ite_eq_left hi] using h i).le
    · simpa only [ite_eq_right hi] using h i
  · rintro ⟨ha,hb⟩ i
    split_ifs with hi
    · exact hb i hi
    · exact ha i

/-- Evaluating an inserted test at a shifted idele selects a finite intersection of valuation cutoffs. -/
private theorem cutIdeleTest_eval {S : Finset V} (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (g : (SAdeleRing F S)ˣ) (B : Finset {v : V // v ∉ S}) :
    open Classical in ∃ z : I, ∀ t : Fˣ,
      sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * z.val)) =
      if ∀ v ∈ B, v.val.valuation F t.val < 1 then
        if ∀ v : {v : V // v ∉ S}, v.val.valuation F t.val ≤ 1 then
          f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))
        else 0 else 0 := by
  classical
  let g₀ := sIdeleInsertion F S g
  have hproj : adeleProjection F S g₀.val = g.val :=
    Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  refine (exists_cutIdele (F := F) S B).elim fun z ⟨hzs, hz⟩ ↦ ⟨g₀ * z, fun t ↦ ?_⟩
  let x := algebraMap F A t.val
  have hcoord (v : V) (hv : v ∉ S) :
      (x * (g₀ * z).val).2 v = x.2 v * z.val.2 v := by
    change x.2 v * (g₀.val.2 v * z.val.2 v) = _
    exact congrArg (x.2 v * ·) ((congrArg (· * z.val.2 v) ((sIdeleInsertion_apply F S g).2.2 v hv)).trans (one_mul _))
  have hint : (∀ v : V, v ∉ S → (x * (g₀ * z).val).2 v ∈ O(v)) ↔
      (∀ v : {v : V // v ∉ S}, v.val.valuation F t.val ≤ 1) ∧
        ∀ v ∈ B, v.val.valuation F t.val < 1 := by
    refine Iff.trans ?_ (outsideCut_iff B fun v ↦ v.val.valuation F t.val)
    constructor
    · intro h v
      exact (hz v.val v.property t).mp (hcoord v.val v.property ▸ h v.val v.property)
    · intro h v hv
      exact (hcoord v hv).symm ▸ (hz v hv t).mpr (h ⟨v, hv⟩)
  have hxs : adeleProjection F S (x * (g₀ * z).val) = adeleProjection F S x * g.val := by
    calc
      _ = adeleProjection F S x * (adeleProjection F S g₀.val * adeleProjection F S z.val) :=
        ((map_mul (adeleProjection F S) x (g₀.val * z.val))).trans
          (congrArg (_ * ·) (map_mul (adeleProjection F S) g₀.val z.val))
      _ = _ := congrArg (adeleProjection F S x * ·)
        ((congrArg₂ (· * ·) hproj hzs).trans (mul_one _))
  refine (sAdeleSchwartzToGlobal_apply F S f (x * (g₀ * z).val)).trans ?_
  refine (if_congr hint (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) hxs) rfl).trans ?_
  split_ifs <;> tauto

/-- Finite exclusion followed by dominated convergence leaves exactly the S-units. -/
private theorem localSum_of_globalKernel {S : Finset V} (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hf : sAdeleSchwartzToGlobal F S f ∈ LinearMap.ker (adelicThetaLinearMap F)) :
    ∀ g : (SAdeleRing F S)ˣ, sLocalAdelicTheta F S f g = 0 := by
  classical
  intro g
  let W := {v : V // v ∉ S}
  let ok (t : Fˣ) := ∀ v : W, v.val.valuation F t.val ≤ 1
  let P (v : W) (t : Fˣ) := v.val.valuation F t.val < 1
  let b (t : Fˣ) := f (Multiplicative.ofAdd
    (adeleProjection F S (algebraMap F A t.val) * g.val))
  let a (t : Fˣ) := if ok t then b t else 0
  have hterm (B : Finset W) : ∃ z : I, ∀ t : Fˣ,
      sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * z.val)) =
        if ∀ v ∈ B, P v t then a t else 0 := cutIdeleTest_eval f g B
  let z (B : Finset W) := (hterm B).choose
  have hz (B : Finset W) := (hterm B).choose_spec
  have hsum : Summable (fun t ↦ ‖a t‖) := by
    have he (t : Fˣ) :
        sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd (algebraMap F A t.val * (z ∅).val)) = a t :=
      (hz ∅ t).trans (ite_eq_left (by simp))
    have H := (adelicAverage_summableUniformlyOn (sAdeleSchwartzToGlobal F S f)
      {(z ∅, 0)} isCompact_singleton).summable rfl
    change Summable (fun t : Fˣ ↦ ‖sAdeleSchwartzToGlobal F S f
      (Multiplicative.ofAdd ((z ∅).val * (algebraMap F A t.val + 0)))‖) at H
    exact H.congr fun t ↦ congrArg norm ((congrArg (fun y ↦ sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd y))
      ((congrArg ((z ∅).val * ·) (add_zero _)).trans (mul_comm _ _))).trans (he t))
  have hzero (B : Finset W) : (∑' t, if ∀ v ∈ B, P v t then a t else 0) = 0 := by
    have h := congrArg (fun φ : C(IdeleClassGroup (𝓞 F) F, ℂ) ↦ φ (QuotientGroup.mk (z B)))
      (show adelicThetaLinearMap F (sAdeleSchwartzToGlobal F S f) = 0 from hf)
    exact (tsum_congr (hz B)).symm.trans ((adelicTheta_mk (sAdeleSchwartzToGlobal F S f) (z B)).symm.trans h)
  have hall := tsum_avoiding_of_tsum_intersections a P hsum hzero
  let H := (S : Set V).unit F
  have hsel (t : Fˣ) : (if ∀ v, ¬ P v t then a t else 0) =
      (H : Set Fˣ).indicator b t := by
    have heq : t ∈ H ↔ ok t ∧ ∀ v, ¬ P v t := by
      constructor
      · intro ht
        exact ⟨fun v ↦ (ht v.val v.property).le, fun v ↦ (ht v.val v.property).ge.not_gt⟩
      · rintro ⟨h₁, h₂⟩ v hv
        exact le_antisymm (h₁ ⟨v, hv⟩) (not_lt.mp (h₂ ⟨v, hv⟩))
    by_cases ht : t ∈ H
    · simp [indicator_of_mem ht, a, (heq.mp ht).1, (heq.mp ht).2]
    · rw [indicator_of_notMem ht]
      unfold a
      split_ifs <;> tauto
  rw [tsum_congr hsel, ← tsum_subtype] at hall
  let e := (Set.unitEquivUnitsInteger (S : Set V) F).symm
  exact (e.tsum_eq (fun u ↦ b u.val)).trans hall

/-- An inserted test of zero global theta already has zero S-local theta. -/
theorem sLocalThetaToGlobal_reflects_kernel :
    (K𝔽).comap (sAdeleSchwartzToGlobal F S) ≤ Kₛ(S) := by
  intro f hf
  exact ContinuousMap.ext (localSum_of_globalKernel f hf)

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Schwartz–Bruhat transition sends the S-local theta kernel into the T-local theta kernel. -/
theorem sLocalThetaTransition_preserves_kernel (hST : S ⊆ T) :
    Kₛ(S) ≤ (Kₛ(T)).comap (sAdeleSchwartzTransition F hST) := by
  intro f hf
  apply sLocalThetaToGlobal_reflects_kernel (S := T)
  have h := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hST) f
  exact (congrArg (fun z : ℬ𝔽 ↦ z ∈ K𝔽) h).mpr
    (sLocalThetaToGlobal_preserves_kernel (S := S) hf)

/-- Paper: (5.2.1.1), p. 230.
The transition on theta quotients is induced by the Schwartz–Bruhat stage transition. -/
def sLocalThetaTransition (hST : S ⊆ T) : Θₛ(S) →ₗ[ℂ] Θₛ(T) :=
  (Kₛ(S)).mapQ (Kₛ(T)) (sAdeleSchwartzTransition F hST)
    (sLocalThetaTransition_preserves_kernel hST)

private theorem localCut_eval {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ)
    (B : Finset {w : T // w.val ∉ S}) :
    open Classical in ∃ y : (SAdeleRing F T)ˣ, ∀ (f : ℬₛ(S)) (t : Fˣ),
      sAdeleSchwartzTransition F hST f (Multiplicative.ofAdd
        (adeleProjection F T (algebraMap F A t.val) * y.val)) =
      if ∀ w ∈ B, w.val.val.valuation F t.val < 1 then
        if ∀ w : {w : T // w.val ∉ S}, w.val.val.valuation F t.val ≤ 1 then
          f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))
        else 0 else 0 := by
  classical
  let W := {w : T // w.val ∉ S}
  let cast (w : W) : {v : V // v ∉ S} := ⟨w.val.val, w.property⟩
  let B' := B.image cast
  have hB (w : W) : cast w ∈ B' ↔ w ∈ B := by
    refine ⟨fun h ↦ ?_, Finset.mem_image_of_mem cast⟩
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp h
    have hv : q.val.val = w.val.val :=
      congrArg (fun v : {v : V // v ∉ S} ↦ v.val) he
    exact (show q = w from Subtype.ext (Subtype.ext hv)) ▸ hq
  let z := (exists_cutIdele (F := F) S B').choose
  have hs := (exists_cutIdele (F := F) S B').choose_spec.1
  have hz := (exists_cutIdele (F := F) S B').choose_spec.2
  let g₀ := sIdeleInsertion F S g
  let y := Units.map (adeleProjection F T).toMonoidHom (g₀ * z)
  have hg₀ : adeleProjection F S g₀.val = g.val :=
    Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  have hy : adeleProjection F S (g₀.val * z.val) = g.val :=
    (map_mul (adeleProjection F S) _ _).trans ((congrArg₂ (· * ·) hg₀ hs).trans (mul_one _))
  refine ⟨y, fun f t ↦ ?_⟩
  let x := algebraMap F A t.val
  let xT := adeleProjection F T x * y.val
  have hS : (xT.1, fun w : S ↦ xT.2 ⟨w.val, hST w.property⟩) =
      adeleProjection F S x * g.val :=
    congrArg (adeleProjection F S x * ·) hy
  have hcoord (w : W) : xT.2 w.val = x.2 w.val.val * z.val.2 w.val.val :=
    congrArg (x.2 w.val.val * ·) ((congrArg (· * z.val.2 w.val.val)
      ((sIdeleInsertion_apply F S g).2.2 w.val.val w.property)).trans (one_mul _))
  have hint (w : W) : xT.2 w.val ∈ O(w.val.val) ↔
      if w ∈ B then w.val.val.valuation F t.val < 1 else w.val.val.valuation F t.val ≤ 1 := by
    exact (hcoord w).symm ▸ ((hz w.val.val w.property t).trans
      (Iff.of_eq (if_congr (hB w) rfl rfl)))
  have hcut : (∀ w : T, w.val ∉ S → xT.2 w ∈ O(w.val)) ↔
      (∀ w : W, w.val.val.valuation F t.val ≤ 1) ∧ ∀ w ∈ B, w.val.val.valuation F t.val < 1 := by
    refine Iff.trans ?_ (outsideCut_iff B fun w ↦ w.val.val.valuation F t.val)
    exact ⟨fun h w ↦ (hint w).mp (h w.val w.property),
      fun h w hw ↦ (hint ⟨w,hw⟩).mpr (h ⟨w,hw⟩)⟩
  refine (sAdeleSchwartzTransition_apply F hST f xT).trans
    ((if_congr hcut (congrArg (fun q ↦ f (Multiplicative.ofAdd q)) hS) rfl).trans ?_)
  split_ifs <;> tauto

/-- A continuous point evaluation of a linear transform descends to its kernel quotient. -/
def thetaQuotientEval {X Q : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [TopologicalSpace Q] (θ : X →ₗ[ℂ] C(Q, ℂ)) (a : Q) (hc : Continuous (fun f ↦ θ f a)) :
    StrongDual ℂ (X ⧸ θ.ker) := by
  let l : X →L[ℂ] ℂ := ⟨(ContinuousMap.evalCLM ℂ a).toLinearMap.comp θ, hc⟩
  exact θ.ker.liftQL l fun f h ↦ congrArg (fun φ : C(Q, ℂ) ↦ φ a) (LinearMap.mem_ker.mp h)

/-- Each S-local theta evaluation is continuous on the Schwartz–Bruhat test space. -/
theorem sLocalAdelicTheta_continuous_eval {S : Finset V} (g : (SAdeleRing F S)ˣ) :
    Continuous (fun f ↦ sLocalAdelicTheta F S f g) := by
  let : BarrelledSpace ℂ (ℬₛ(S)) := (sAdeleSchwartz_montel (F := F) S).1
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ := Units.val_injective.countable
  exact schwartzBruhat_continuous_of_hasSum _ _ fun f ↦
    (sLocalAdelicTheta_hasSumUniformlyOn F S f {g} isCompact_singleton).hasSum rfl

private theorem localTheta_indicator_hasSum (S : Finset V) (f : ℬₛ(S)) (y : (SAdeleRing F S)ˣ) :
    HasSum (((S : Set V).unit F : Set Fˣ).indicator (fun t ↦
      f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * y.val))))
      (sLocalAdelicTheta F S f y) := by
  let e := (Set.unitEquivUnitsInteger (S : Set V) F).symm
  apply hasSum_subtype_iff_indicator.mp
  exact (e.toEquiv.hasSum_iff).mp ((sLocalAdelicTheta_hasSumUniformlyOn F S f {y} isCompact_singleton).hasSum rfl)

private theorem units_in_smaller_stage {S T : Finset V} (hST : S ⊆ T) (t : Fˣ) :
    t ∈ (S : Set V).unit F ↔ t ∈ (T : Set V).unit F ∧
      ∀ w : {w : T // w.val ∉ S}, w.val.val.valuation F t.val = 1 := by
  refine ⟨fun h ↦ ⟨fun v hv ↦ h v (fun h ↦ hv (hST h)), fun w ↦ h w.val.val w.property⟩, ?_⟩
  intro ⟨ht,hw⟩ v hv
  by_cases hT : v ∈ T
  · exact hw ⟨⟨v,hT⟩,hv⟩
  · exact ht v hT

private theorem cutoff_indicator {W α : Type*} [Fintype W]
    (H K : Set α) (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ)
    (h : ∀ t, t ∈ H ↔ t ∈ K ∧ ∀ w, v w t = 1) (t : α) :
    open Classical in
    (if ∀ w, ¬ v w t < 1 then
      K.indicator (fun s ↦ if ∀ w, v w s ≤ 1 then b s else 0) t else 0) = H.indicator b t := by
  classical
  by_cases ht : t ∈ H
  · obtain ⟨hK,hv⟩ := (h t).mp ht
    simp [Set.indicator_of_mem ht, Set.indicator_of_mem hK, hv]
  · rw [Set.indicator_of_notMem ht]
    by_cases hK : t ∈ K
    · rw [Set.indicator_of_mem hK]
      split_ifs with h₁ h₂
      · exact (ht ((h t).mpr ⟨hK, fun w ↦ le_antisymm (h₂ w) (not_lt.mp (h₁ w))⟩)).elim
      all_goals rfl
    · simp only [Set.indicator_of_notMem hK, ite_self]

private noncomputable def cutSummand {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ) (t : α) : ℂ :=
  open Classical in if ∀ w ∈ B, v w t < 1 then
    K.indicator (fun z ↦ if ∀ w, v w z ≤ 1 then b z else 0) t else 0

private theorem cutSummand_eq_ite {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (b : α → ℂ) (t : α)
    [d : Decidable (∀ w ∈ B, v w t < 1)] [e : ∀ z, Decidable (∀ w, v w z ≤ 1)] :
    cutSummand B K v b t = if ∀ w ∈ B, v w t < 1 then
      K.indicator (fun z ↦ if ∀ w, v w z ≤ 1 then b z else 0) t else 0 := by
  classical
  by_cases ht : t ∈ K <;> by_cases hp : ∀ w ∈ B, v w t < 1 <;>
    by_cases hq : ∀ w, v w t ≤ 1 <;> simp [cutSummand, ht, hp, hq]

private theorem cutSummand_indicator {W α : Type*} (B : Finset W) (K : Set α)
    (v : W → α → WithZero (Multiplicative ℤ)) (q b : α → ℂ) (t : α)
    {d : Decidable (∀ w ∈ B, v w t < 1)} {e : Decidable (∀ w, v w t ≤ 1)}
    (hq : q t = @ite ℂ _ d (@ite ℂ _ e (b t) 0) 0) :
    cutSummand B K v b t = K.indicator q t := by
  classical
  by_cases ht : t ∈ K
  · by_cases h₁ : ∀ w ∈ B, v w t < 1 <;> by_cases h₂ : ∀ w, v w t ≤ 1 <;>
      simpa only [cutSummand, Set.indicator_of_mem ht, h₁, h₂, ite_true, ite_false] using hq.symm
  · simp only [cutSummand, Set.indicator_of_notMem ht, ite_self]

private theorem ite_decision_irrel {P : Prop} (a b : ℂ) (d e : Decidable P) :
    @ite ℂ P d a b = @ite ℂ P e a b :=
  congrArg (fun i ↦ @ite ℂ P i a b) (Subsingleton.elim d e)

private theorem extendFiniteCutIn {W α X Y : Type*} [Fintype W] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (M : Submodule ℂ (StrongDual ℂ Y)) (j : X → Y) (H K : Set α) (v : W → α → WithZero (Multiplicative ℤ))
    (b : X → α → ℂ) (c : X → ℂ) (h : ∀ t, t ∈ H ↔ t ∈ K ∧ ∀ w, v w t = 1)
    (hc : ∀ x, HasSum (H.indicator (b x)) (c x))
    (hi : ∀ B : Finset W, ∃ L : M, ∀ x,
      HasSum (cutSummand B K v (b x)) (L.val (j x))) :
    ∃ L : M, ∀ x, L.val (j x) = c x := by
  classical
  let a (x : X) := K.indicator (fun t ↦ if ∀ w, v w t ≤ 1 then b x t else 0)
  let p : M →ₗ[ℂ] (X → ℂ) :=
    { toFun := fun l x ↦ l.val (j x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have ha (f : X) : Summable (a f) :=
    ((hi ∅).choose_spec f).summable.congr fun t ↦
      (cutSummand_eq_ite ∅ K v (b f) t).trans (ite_eq_left (by simp))
  have hm (B : Finset W) : (fun f ↦ ∑' t, if ∀ w ∈ B, v w t < 1 then a f t else 0) ∈ p.range :=
    ⟨(hi B).choose, funext fun f ↦ ((hi B).choose_spec f).tsum_eq.symm.trans
      (tsum_congr (fun t ↦ cutSummand_eq_ite B K v (b f) t))⟩
  have hmem := tsum_avoiding_finset_mem p.range.toAddSubgroup a (fun f ↦ (ha f).norm)
    (fun w t ↦ v w t < 1) (fun B ↦ by
    obtain ⟨l,hl⟩ := hm B
    refine ⟨l, hl.trans (funext fun f ↦ tsum_congr fun t ↦ ?_)⟩
    exact ite_decision_irrel (P := ∀ w ∈ B, v w t < 1) (a f t) 0 _ _) Finset.univ
  obtain ⟨L,hh⟩ := hmem
  have hL : p L = fun f ↦ ∑' t, if ∀ w, ¬ v w t < 1 then a f t else 0 := by
    refine hh.trans (funext fun f ↦ tsum_congr fun t ↦ ?_)
    simp only [Finset.mem_univ, forall_true_left]
  exact ⟨L, fun f ↦ (congrFun hL f).trans ((tsum_congr
    (cutoff_indicator H K v (b f) h)).trans (hc f).tsum_eq)⟩

/-- The span of evaluation functionals on an S-local theta quotient. -/
def sLocalThetaEvaluationSpan (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Submodule ℂ (StrongDual ℂ (SLocalAdelicThetaSpace F S)) :=
  Submodule.span ℂ (range fun x ↦ thetaQuotientEval (sLocalAdelicTheta F S) x (sLocalAdelicTheta_continuous_eval x))

private theorem localCut_inSpan {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ)
    (B : Finset {w : T // w.val ∉ S}) : ∃ L : sLocalThetaEvaluationSpan F T, ∀ f : ℬₛ(S),
      HasSum (cutSummand (α := Fˣ) B ((T : Set V).unit F) (fun w t ↦ w.val.val.valuation F t.val)
        (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))))
        (L.val ((Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f))) := by
  classical
  let y := (localCut_eval hST g B).choose
  have hy := (localCut_eval hST g B).choose_spec
  refine ⟨⟨thetaQuotientEval (sLocalAdelicTheta F T) y (sLocalAdelicTheta_continuous_eval y), Submodule.subset_span (mem_range_self y)⟩, fun f ↦ ?_⟩
  refine (localTheta_indicator_hasSum T (sAdeleSchwartzTransition F hST f) y).congr_fun fun t ↦ ?_
  exact cutSummand_indicator (α := Fˣ) B ((T : Set V).unit F)
    (fun w t ↦ w.val.val.valuation F t.val) _
    (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val))) t (hy f t)

/-- A theta evaluation on an old stage extends to a finite linear combination of
theta evaluations on a larger stage. -/
theorem sLocalThetaTransition_extend_eval_in_span {S T : Finset V} (hST : S ⊆ T) (g : (SAdeleRing F S)ˣ) :
    ∃ L : sLocalThetaEvaluationSpan F T, ∀ f : ℬₛ(S),
      L.val ((Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f)) = sLocalAdelicTheta F S f g := by
  classical
  refine extendFiniteCutIn (α := Fˣ) (X := ℬₛ(S)) (Y := Θₛ(T)) (W := {w : T // w.val ∉ S})
    (sLocalThetaEvaluationSpan F T) (fun f : ℬₛ(S) ↦ (Kₛ(T)).mkQ (sAdeleSchwartzTransition F hST f))
    ((S : Set V).unit F) ((T : Set V).unit F) (fun w t ↦ w.val.val.valuation F t.val)
    (fun f t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * g.val)))
    (fun f ↦ sLocalAdelicTheta F S f g) ?_ ?_ ?_
  · exact units_in_smaller_stage (F := F) hST
  · exact fun f ↦ localTheta_indicator_hasSum S f g
  · exact localCut_inSpan (F := F) hST g

private theorem hasSum_group_fiber {G Q E : Type*} [CommGroup G] [Group Q]
    [AddCommMonoid E] [TopologicalSpace E] (K H : Subgroup G) (v : G →* Q)
    (hH : ∀ t, t ∈ H ↔ t ∈ K ∧ v t = 1) (k : Q) (t₀ : G)
    (hk : t₀ ∈ K ∧ v t₀ = k) (f : G → E) {s : E}
    (h : HasSum (fun u : H ↦ f (u.val * t₀)) s) :
    HasSum (({t : G | t ∈ K ∧ v t = k} : Set G).indicator f) s := by
  let Z := {t : G | t ∈ K ∧ v t = k}
  let e (u : H) : Z := ⟨u.val * t₀, K.mul_mem ((hH _).mp u.property).1 hk.1,
    (v.map_mul _ _).trans (by rw [((hH _).mp u.property).2, one_mul, hk.2])⟩
  have he : Bijective e := by
    refine ⟨fun x y h ↦ Subtype.ext (mul_right_cancel (congrArg Subtype.val h)), ?_⟩
    rintro ⟨t, ht, hv⟩
    refine ⟨⟨t / t₀, (hH _).mpr ⟨K.div_mem ht hk.1, ?_⟩⟩, Subtype.ext (div_mul_cancel t t₀)⟩
    rw [map_div, hv, hk.2]
    exact div_self' k
  exact hasSum_subtype_iff_indicator.mp (((Equiv.ofBijective e he).hasSum_iff).mp h)

private theorem exists_translate_fiber {G Q J X : Type*} [CommGroup G] [Group Q] [Group J]
    (K H : Subgroup G) (v : G →* Q) (d : G →* J) (b θ : X → J → ℂ)
    (hH : ∀ t, t ∈ H ↔ t ∈ K ∧ v t = 1)
    (hθ : ∀ f x, HasSum (fun u : H ↦ b f (d u.val * x)) (θ f x)) (k : Q) :
    ∃ y : Option J, ∀ f x,
      HasSum (({t : G | t ∈ K ∧ v t = k} : Set G).indicator (fun t ↦ b f (d t * x)))
        (y.elim 0 (fun g ↦ θ f (g * x))) := by
  classical
  by_cases hex : ∃ t : G, t ∈ K ∧ v t = k
  · obtain ⟨t₀,ht⟩ := hex
    refine ⟨some (d t₀), fun f x ↦ hasSum_group_fiber K H v hH k t₀ ht _ ?_⟩
    exact (hθ f (d t₀ * x)).congr_fun fun u ↦ congrArg (b f) <|
      (congrArg (· * x) (d.map_mul u.val t₀)).trans (mul_assoc _ _ _)
  · refine ⟨none, fun f x ↦ ?_⟩
    refine hasSum_zero.congr_fun fun t ↦ ?_
    exact Set.indicator_of_notMem (fun ht ↦ hex ⟨t,ht⟩) _

private theorem localTheta_unit_hasSum (S : Finset V) (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
    HasSum (fun u : (S : Set V).unit F ↦ f (Multiplicative.ofAdd
        (adeleProjection F S (algebraMap F A u.val.val) * x.val))) (sLocalAdelicTheta F S f x) :=
  hasSum_subtype_iff_indicator.mpr (localTheta_indicator_hasSum S f x)

private theorem unit_fun_eq_iff {W M : Type*} [Monoid M] (u v : W → Mˣ) :
    (∀ w, (u w).val = (v w).val) ↔ u = v :=
  ⟨fun h ↦ funext fun w ↦ Units.ext (h w), fun h w ↦ congrArg Units.val (congrFun h w)⟩

/-- On a single valuation fiber the sum over the larger unit group is a translate
of the S-local theta sum. Empty fibers contribute zero. The representative works
for all test functions and all evaluation points simultaneously. -/
theorem sLocalTheta_valuationFiber {S T : Finset V} (hST : S ⊆ T)
    (k : {w : T // w.val ∉ S} → (WithZero (Multiplicative ℤ))ˣ) :
    let v : Fˣ →* ({w : T // w.val ∉ S} → (WithZero (Multiplicative ℤ))ˣ) :=
      MonoidHom.pi fun w ↦ Units.map (w.val.val.valuation F).toMonoidHom
    ∃ y : Option (SAdeleRing F S)ˣ, ∀ (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ),
      HasSum (({t : Fˣ | t ∈ (T : Set V).unit F ∧ v t = k} : Set Fˣ).indicator
        (fun t ↦ f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F A t.val) * x.val))))
        (y.elim 0 fun g ↦ sLocalAdelicTheta F S f (g * x)) := by
  classical
  let W := {w : T // w.val ∉ S}
  let v : Fˣ →* (W → (WithZero (Multiplicative ℤ))ˣ) :=
    MonoidHom.pi fun w ↦ Units.map (w.val.val.valuation F).toMonoidHom
  have hh (t : Fˣ) : t ∈ (S : Set V).unit F ↔ t ∈ (T : Set V).unit F ∧ v t = 1 :=
    (units_in_smaller_stage (F := F) hST t).trans (and_congr_right' (unit_fun_eq_iff (v t) 1))
  let d := Units.map ((adeleProjection F S).toMonoidHom.comp (algebraMap F A).toMonoidHom)
  let b (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd x.val)
  have hθ (f : ℬₛ(S)) (x : (SAdeleRing F S)ˣ) :
      HasSum (fun u : (S : Set V).unit F ↦ b f (d u.val * x)) (sLocalAdelicTheta F S f x) :=
    localTheta_unit_hasSum S f x
  have result := exists_translate_fiber ((T : Set V).unit F) ((S : Set V).unit F) v d b
    (fun f x ↦ sLocalAdelicTheta F S f x) hh hθ k
  exact result

end KernelDescent

private theorem quotientMap_unique {R X Y : Type*} [Ring R] [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (K : Submodule R X) (L : Submodule R Y)
    (j : X →ₗ[R] Y) (hj : K ≤ L.comap j) :
    (K.mapQ L j hj).comp K.mkQ = L.mkQ.comp j ∧
      ∀ π : (X ⧸ K) →ₗ[R] (Y ⧸ L), π.comp K.mkQ = L.mkQ.comp j → π = K.mapQ L j hj := by
  refine ⟨K.mapQ_mkQ L j, fun π hπ ↦ LinearMap.ext fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := K.mkQ_surjective x
  exact DFunLike.congr_fun hπ a

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The theta transition is the unique linear map taking each class to the class of its
Schwartz–Bruhat transition. -/
theorem sLocalThetaTransition_unique (hST : S ⊆ T) :
    let descends := fun π : Θₛ(S) →ₗ[ℂ] Θₛ(T) ↦
      π.comp (Kₛ(S)).mkQ = (Kₛ(T)).mkQ.comp (sAdeleSchwartzTransition F hST)
    descends (sLocalThetaTransition hST) ∧
      ∀ π, descends π → π = sLocalThetaTransition hST :=
  quotientMap_unique (Kₛ(S)) (Kₛ(T)) (sAdeleSchwartzTransition F hST)
    (sLocalThetaTransition_preserves_kernel hST)

private theorem quotientMap_comp {R X Y Z : Type*} [Ring R] [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z] (K : Submodule R X) (L : Submodule R Y) (M : Submodule R Z)
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : X →ₗ[R] Z)
    (hf : K ≤ L.comap f) (hg : L ≤ M.comap g) (hh : K ≤ M.comap h) (hc : g.comp f = h) :
    (L.mapQ M g hg).comp (K.mapQ L f hf) = K.mapQ M h hh := by
  subst h
  exact (K.mapQ_comp L M f g hf hg).symm

private theorem testTransition_comp (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sAdeleSchwartzTransition F hTU).comp (sAdeleSchwartzTransition F hST) =
      sAdeleSchwartzTransition F (hST.trans hTU) := by
  refine LinearMap.ext fun f ↦ (sAdeleSchwartzToGlobal_isEmbedding F U).injective ?_
  have h {A B : Finset (HeightOneSpectrum (𝓞 F))} (hAB : A ⊆ B) (g : ℬₛ(A)) :
      sAdeleSchwartzToGlobal F B (sAdeleSchwartzTransition F hAB g) =
        sAdeleSchwartzToGlobal F A g := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hAB) g
  exact ((h hTU _).trans (h hST f)).trans (h (hST.trans hTU) f).symm

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Two successive theta transitions agree with the direct transition. -/
theorem sLocalThetaTransition_comp (hST : S ⊆ T) (hTU : T ⊆ U) :
    (sLocalThetaTransition (F := F) hTU).comp (sLocalThetaTransition hST) =
      sLocalThetaTransition (hST.trans hTU) := quotientMap_comp _ _ _ _ _ _
    (sLocalThetaTransition_preserves_kernel hST) (sLocalThetaTransition_preserves_kernel hTU)
    (sLocalThetaTransition_preserves_kernel (hST.trans hTU)) (testTransition_comp hST hTU)

variable (F S) in
/-- Paper: (5.2.1.3), p. 230.
The insertion of S-local theta classes into global theta classes is the map
induced by the insertion of test functions. -/
def sLocalThetaToGlobal : Θₛ(S) →ₗ[ℂ] Θ𝔽 :=
  (Kₛ(S)).mapQ K𝔽 (sAdeleSchwartzToGlobal F S) sLocalThetaToGlobal_preserves_kernel

/-- Continuity descends from the transition of test functions through the quotient map. -/
theorem sLocalThetaTransition_continuous (hST : S ⊆ T) :
    Continuous (sLocalThetaTransition (F := F) hST) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (Kₛ(T)).mkQL.continuous.comp (sAdeleSchwartzTransition_isEmbedding F hST).continuous

/-- Continuity of the global insertion descends through the local quotient. -/
theorem sLocalThetaToGlobal_continuous : Continuous (sLocalThetaToGlobal F S) := by
  apply (Kₛ(S)).isQuotientMap_mkQ.continuous_iff.mpr
  exact (K𝔽).mkQL.continuous.comp (sAdeleSchwartzToGlobal_isEmbedding F S).continuous

/-- Paper: (5.2.1.3), p. 230.
Inserting the class of a local test function gives the class of its extension to the adeles. -/
theorem sLocalThetaToGlobal_mk (f : ℬₛ(S)) :
    sLocalThetaToGlobal F S (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdeleSchwartzToGlobal F S f) := rfl

private theorem injective_mapQ_of_comap_le {R X Y : Type*} [Ring R] [AddCommGroup X]
    [AddCommGroup Y] [Module R X] [Module R Y] (K : Submodule R X) (L : Submodule R Y)
    (j : X →ₗ[R] Y) (hj : K ≤ L.comap j) (hr : L.comap j ≤ K) :
    Injective (K.mapQ L j hj) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.ker_mapQ, le_antisymm hr hj, Submodule.mkQ_map_self]

/-- Insertion is injective because global theta detects the S-unit sum on an inserted test. -/
theorem sLocalThetaToGlobal_injective : Injective (sLocalThetaToGlobal F S) :=
  injective_mapQ_of_comap_le (Kₛ(S)) (K𝔽) (sAdeleSchwartzToGlobal F S)
    (sLocalThetaToGlobal_preserves_kernel (F := F) (S := S))
    (sLocalThetaToGlobal_reflects_kernel (F := F) (S := S))

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The stage insertions and transitions form a compatible family in the global quotient. -/
theorem sLocalThetaToGlobal_comp (hST : S ⊆ T) :
    (sLocalThetaToGlobal F T).comp (sLocalThetaTransition hST) = sLocalThetaToGlobal F S :=
  quotientMap_comp _ _ _ _ _ _
    (sLocalThetaTransition_preserves_kernel hST) sLocalThetaToGlobal_preserves_kernel
    sLocalThetaToGlobal_preserves_kernel (sAdeleSchwartzToGlobal_comp F hST)

private theorem quotientMap_exhaustive {ι R Y : Type*} [Ring R] [AddCommGroup Y] [Module R Y]
    {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)] (K : Submodule R Y)
    (D : ∀ i, Submodule R (X i)) (j : ∀ i, X i →ₗ[R] Y) (hj : ∀ i, D i ≤ K.comap (j i))
    (he : ∀ y, ∃ i, y ∈ (j i).range) (x : Y ⧸ K) :
    ∃ i z, (D i).mapQ K (j i) (hj i) z = x := by
  obtain ⟨f,rfl⟩ := K.mkQ_surjective x
  obtain ⟨i,g,rfl⟩ := he f
  exact ⟨i, (D i).mkQ g, rfl⟩

/-- The compatible injections into global theta space detect equality at every finite stage. -/
theorem sLocalThetaTransition_injective (hST : S ⊆ T) :
    Injective (sLocalThetaTransition (F := F) hST) := by
  intro x y h
  have hc := sLocalThetaToGlobal_comp (F := F) hST
  exact sLocalThetaToGlobal_injective (F := F) (S := S) (((DFunLike.congr_fun hc x).symm.trans
    (congrArg (sLocalThetaToGlobal F T) h)).trans (DFunLike.congr_fun hc y))

private theorem closedEmbedding_of_linear_comp {R X Y Z : Type*} [Semiring R]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z] [Module R X] [Module R Y] [Module R Z]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (h : X →ₗ[R] Z) (he : IsEmbedding g)
    (hc : IsClosedEmbedding h) (eq : g.comp f = h) : IsClosedEmbedding f := by
  subst h
  exact IsClosedEmbedding.of_comp he hc

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Every global theta class comes from a finite stage. -/
theorem sLocalThetaToGlobal_exhaustive (x : Θ𝔽) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (y : Θₛ(S)),
      sLocalThetaToGlobal F S y = x :=
  quotientMap_exhaustive (K𝔽) (fun S ↦ Kₛ(S)) (sAdeleSchwartzToGlobal F)
    (fun S ↦ sLocalThetaToGlobal_preserves_kernel (F := F) (S := S))
    (sAdeleSchwartzToGlobal_exhaustive F) x

private theorem quotient_finalTopology {ι E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] {X : ι → Type*}
    [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] [∀ i, TopologicalSpace (X i)]
    (j : ∀ i, X i →ₗ[ℂ] E) (hj : ∀ i, Continuous (j i)) (K : Submodule ℂ E)
    (D : ∀ i, Submodule ℂ (X i)) (hD : ∀ i, D i ≤ K.comap (j i))
    [PolynormableSpace ℂ (E ⧸ K)]
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology j) :
    (inferInstance : TopologicalSpace (E ⧸ K)) = locallyConvexFinalTopology
      (fun i ↦ (D i).mapQ K (j i) (hD i)) := by
  let jQ i := (D i).mapQ K (j i) (hD i)
  have hP : WithSeminorms (Subtype.val : {p : Seminorm ℂ E // ∀ i, Continuous (p ∘ j i)} → _) := ⟨ht⟩
  have h : (fun p : Seminorm ℂ (E ⧸ K) ↦ ∀ i, Continuous (p ∘ jQ i)) =
      (fun p : Seminorm ℂ (E ⧸ K) ↦ Continuous p) := by
    funext p
    apply propext
    refine ⟨fun hp ↦ K.isQuotientMap_mkQ.continuous_iff.mpr ?_, fun hp i ↦ ?_⟩
    · exact hP.continuous_seminorm ⟨p.comp K.mkQ, fun i ↦ (hp i).comp (D i).mkQL.continuous⟩
    · exact (D i).isQuotientMap_mkQ.continuous_iff.mpr ((hp.comp K.mkQL.continuous).comp (hj i))
  let gen (P : Seminorm ℂ (E ⧸ K) → Prop) := (SeminormFamily.moduleFilterBasis
    (Subtype.val : {p : Seminorm ℂ (E ⧸ K) // P p} → Seminorm ℂ (E ⧸ K))).topology
  exact (PolynormableSpace.withSeminorms ℂ (E ⧸ K)).withSeminorms_eq.trans (congrArg gen h.symm)

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The global quotient has the final locally convex topology for the S-local insertions.
Deviation: The compatible embeddings and exhaustion identify the algebraic colimit
with the global space, where the assertion becomes an equality of topologies. -/
theorem sLocalThetaToGlobal_finalTopology :
    (inferInstance : TopologicalSpace Θ𝔽) = locallyConvexFinalTopology (sLocalThetaToGlobal F) := by
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
  exact quotient_finalTopology (sAdeleSchwartzToGlobal F)
    (fun S ↦ (sAdeleSchwartzToGlobal_isEmbedding F S).continuous) (K𝔽)
    (fun S ↦ Kₛ(S)) (fun _ ↦ sLocalThetaToGlobal_preserves_kernel)
    (sAdeleSchwartzToGlobal_finalTopology F)

section CofinalStages

open Set

/-- Cofinal countable chains of finite sets recover the topology of a locally convex
limit. It suffices to embed across one new coordinate at a time. -/
private theorem finset_limit_isEmbedding {V E : Type*} [Countable V] [DecidableEq V]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {X : Finset V → Type*} [∀ S, AddCommGroup (X S)] [∀ S, Module ℂ (X S)]
    [∀ S, TopologicalSpace (X S)] [∀ S, IsTopologicalAddGroup (X S)] [∀ S, PolynormableSpace ℂ (X S)]
    (i : ∀ S, X S →L[ℂ] E) (j : ∀ {S T}, S ⊆ T → X S →L[ℂ] X T)
    (hi : ∀ S, Injective (i S)) (hc : ∀ (S T) (h : S ⊆ T), (i T).comp (j h) = i S)
    (hx : ∀ x, ∃ S y, i S y = x)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun S ↦ (i S).toLinearMap))
    (he : ∀ (S : Finset V) (v : V), IsEmbedding (j (Finset.subset_insert v S))) (S : Finset V) : IsEmbedding (i S) := by
  classical
  let h := exists_surjective_nat (Finset V)
  let e := h.choose
  let C (n : ℕ) := S ∪ (Finset.range n).biUnion e
  have hm : Monotone C := fun a b hab ↦ Finset.union_subset_union_right <|
    Finset.biUnion_subset_biUnion_of_subset_left e (Finset.range_mono hab)
  have hco (U : Finset V) : ∃ n, U ⊆ C n := by
    obtain ⟨n,hn⟩ := h.choose_spec U
    refine ⟨n+1, fun u hu ↦ Finset.mem_union_right _ ?_⟩
    exact Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr n.lt_succ_self, show u ∈ e n from (show e n = U from hn).symm ▸ hu⟩
  have hcomp {U T : Finset V} (hUT : U ⊆ T) (x : X U) : i T (j hUT x) = i U x :=
    DFunLike.congr_fun (hc U T hUT) x
  have hj {U T : Finset V} (hUT : U ⊆ T) : IsEmbedding (j hUT) := by
    have hrefl {Q : Finset V} (eq : U = Q) (H : U ⊆ Q) : IsEmbedding (j H) := by
      subst Q
      have hid : ⇑(j H) = id := funext fun x ↦ hi U (hcomp H x)
      exact (congrArg IsEmbedding hid).mpr IsEmbedding.id
    have hu (B : Finset V) : ∀ (H : U ⊆ U ∪ B), IsEmbedding (j H) := by
      induction B using Finset.induction_on with
      | empty =>
        exact hrefl (Finset.union_empty U).symm
      | insert v B _ ih =>
        rw [Finset.union_insert]
        intro H
        let hB : U ⊆ U ∪ B := Finset.subset_union_left
        let hv := Finset.subset_insert v (U ∪ B)
        have hjc : ⇑(j H) = (j hv) ∘ (j hB) := funext fun x ↦ hi _
          ((hcomp H x).trans ((hcomp hv (j hB x)).trans (hcomp hB x)).symm)
        rw [hjc]
        exact (he _ _).comp (ih hB)
    have heq := Finset.union_eq_right.mpr hUT
    have hh := hu T
    rw [heq] at hh
    exact hh hUT
  let m n := j (hm (Nat.le_succ n))
  have hlim : IsInjectiveLCLimit m (fun n ↦ i (C n)) := by
    refine ⟨fun n ↦ hi _, fun n ↦ hc _ _ _, fun x ↦ ?_, ?_⟩
    · obtain ⟨U,y,rfl⟩ := hx x
      obtain ⟨n,hn⟩ := hco U
      exact ⟨n,j hn y,hcomp hn y⟩
    · have hk : (fun p : Seminorm ℂ E ↦ ∀ n : ℕ, Continuous (p ∘ (i (C n)).toLinearMap)) =
          (fun p : Seminorm ℂ E ↦ ∀ U, Continuous (p ∘ (i U).toLinearMap)) := by
        funext p
        apply propext
        refine ⟨fun hp U ↦ ?_, fun hp n ↦ hp (C n)⟩
        obtain ⟨n,hn⟩ := hco U
        exact ((hp n).comp (j hn).continuous).congr fun x ↦ congrArg p (hcomp hn x)
      unfold locallyConvexFinalTopology at ht ⊢
      rwa [hk]
  have h0 : C 0 = S := by simp [C]
  have hh := hlim.isEmbedding_stage (fun n ↦ hj _) 0
  rw [h0] at hh
  exact hh

local notation "V" => HeightOneSpectrum (𝓞 F)

open Classical in
/-- Embeddings for one-place enlargements suffice to embed every finite theta stage
in the global quotient endowed with its final locally convex topology. -/
theorem sLocalThetaToGlobal_isEmbedding_of_insert
    (he : ∀ (T : Finset V) (v : V),
      IsEmbedding (sLocalThetaTransition (F := F) (Finset.subset_insert v T))) (S : Finset V) :
    IsEmbedding (sLocalThetaToGlobal F S) := by
  classical
  let : Countable V := finitePlaces_countable F
  let (T : Finset V) : PolynormableSpace ℂ (Θₛ(T)) :=
    sLocalAdelicThetaSpace_polynormable (F := F) (S := T)
  let i (T : Finset V) : Θₛ(T) →L[ℂ] Θ𝔽 :=
    ⟨sLocalThetaToGlobal F T, sLocalThetaToGlobal_continuous (F := F) (S := T)⟩
  let j {T U : Finset V} (h : T ⊆ U) : Θₛ(T) →L[ℂ] Θₛ(U) :=
    ⟨sLocalThetaTransition (F := F) h, sLocalThetaTransition_continuous (F := F) h⟩
  have hcomp (T U : Finset V) (h : T ⊆ U) : (i U).comp (j h) = i T :=
    ContinuousLinearMap.ext fun x ↦ DFunLike.congr_fun (sLocalThetaToGlobal_comp (F := F) h) x
  exact finset_limit_isEmbedding (X := fun T : Finset V ↦ Θₛ(T)) i (fun h ↦ j h)
    (fun T ↦ sLocalThetaToGlobal_injective (F := F) (S := T))
    hcomp
    (sLocalThetaToGlobal_exhaustive (F := F)) (sLocalThetaToGlobal_finalTopology (F := F)) he S

end CofinalStages

section UnitActions

open Bornology Set
open scoped Uniformity Classical TensorProduct RestrictedProduct

/-- Pointwise continuity of a locally compact family of continuous linear maps
gives joint continuity when the domain is barrelled. -/
theorem continuous_family_of_orbits {G E : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [BarrelledSpace ℂ E]
    (T : G → E →L[ℂ] E) (hT : ∀ x, Continuous fun g ↦ T g x) :
    Continuous fun p : G × E ↦ T p.1 p.2 := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨g,x⟩
  obtain ⟨K, hK, hKg⟩ := exists_compact_mem_nhds g
  have hb (y : E) : IsVonNBounded ℂ (range fun k : K ↦ T k.val y) := by
    exact (congrArg (IsVonNBounded ℂ) (image_eq_range (fun g ↦ T g y) K)).mp ((hK.image (hT y)).isVonNBounded ℂ)
  have hEq := (PolynormableSpace.banach_steinhaus hb).equicontinuous x
  apply ((hT x).continuousAt.comp (continuousAt_fst (p := (g,x)))).congr_uniformity
  intro U hU
  change ∀ᶠ p : G × E in 𝓝 (g,x), (T p.1 x, T p.1 p.2) ∈ U
  filter_upwards [continuousAt_fst.preimage_mem_nhds hKg, continuousAt_snd.preimage_mem_nhds (hEq U hU)]
    with p hp he
  exact he ⟨p.1,hp⟩

/-- The Schwartz space of a finite-dimensional real vector space is a Montel space. -/
theorem finiteDimensional_schwartz_montel {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] : MontelSpace ℂ (SchwartzMap V ℂ) := by
  let m := Module.finrank ℝ V
  let E := EuclideanSpace ℝ (Fin m)
  let L : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, m, finrank_euclideanSpace])
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (F := ℂ)
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L (F := ℂ)
  let e := ContinuousLinearEquiv.equivOfInverse P Q
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (L.apply_symm_apply x))
  let : MontelSpace ℂ (SchwartzMap E ℂ) := montel_euclideanSchwartz m
  constructor
  intro s hs hb
  exact e.toHomeomorph.isEmbedding.isCompact_iff.mpr
    (MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ
      (e.toHomeomorph.isClosedMap s hs) (hb.image e.toContinuousLinearMap))

/-- Multiplication by a unit of a normed `ℝ`-algebra, as a continuous `ℝ`-linear equivalence. -/
def mulUnitLinearEquiv {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V]
    (u : Vˣ) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (ContinuousLinearMap.mul ℝ V u.val)
    (ContinuousLinearMap.mul ℝ V u.inv)
    (fun x ↦ by change u.inv * (u.val * x) = x; rw [← mul_assoc, u.inv_val, one_mul])
    (fun x ↦ by change u.val * (u.inv * x) = x; rw [← mul_assoc, u.val_inv, one_mul])

private theorem continuous_mixedCoordinates (F : Type*) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  let M := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h : ⇑M = fun x ↦
      ((fun (v : {w : InfinitePlace F // InfinitePlace.IsReal w}) ↦
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
       (fun (v : {w : InfinitePlace F // InfinitePlace.IsComplex w}) ↦
        InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
    funext (InfiniteAdeleRing.ringEquiv_mixedSpace_apply F)
  exact h ▸ ((continuous_pi fun v ↦
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk (continuous_pi fun v ↦
    (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply v.1)))

private theorem continuous_schwartzUnitOrbit_of_coordinates
    {R V G : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [NormedCommRing V] [NormedAlgebra ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    (M : R ≃+* V) (hM : Continuous M)
    (J : SchwartzMap V ℂ ≃L[ℂ] SchwartzBruhat (Multiplicative R))
    (hJ : ∀ f x, J f (Multiplicative.ofAdd x) = f (M x))
    (g : G → Rˣ) (hg : Continuous g) (f : SchwartzBruhat (Multiplicative R)) :
    Continuous fun t ↦ schwartzBruhatUnitTranslate (g t) f := by
  let u (t : G) := Units.map M.toMonoidHom (g t)
  let A (t : G) : V ≃L[ℝ] V := mulUnitLinearEquiv (u t)⁻¹
  have hA : Continuous fun t ↦ (A t).toContinuousLinearMap :=
    (ContinuousLinearMap.mul ℝ V).continuous.comp (hM.comp (Units.continuous_coe_inv.comp hg))
  have hB : Continuous fun t ↦ (A t).symm.toContinuousLinearMap :=
    (ContinuousLinearMap.mul ℝ V).continuous.comp (hM.comp (Units.continuous_val.comp hg))
  let : MontelSpace ℂ (SchwartzMap V ℂ) := finiteDimensional_schwartz_montel
  refine (J.continuous.comp (continuous_schwartz_comp_family A hA hB (J.symm f))).congr ?_
  intro t
  apply Subtype.ext
  funext x
  refine (hJ _ x.toAdd).trans ?_
  exact (congrArg (J.symm f) (M.map_mul (g t).inv x.toAdd).symm).trans
    ((hJ (J.symm f) ((g t).inv * x.toAdd)).symm.trans
      (congrArg (fun φ : SchwartzBruhat (Multiplicative R) ↦
        φ (Multiplicative.ofAdd ((g t).inv * x.toAdd))) (J.apply_symm_apply f)))

private theorem continuous_archUnitOrbit {F G : Type*} [Field F] [NumberField F]
    [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    (g : G → (InfiniteAdeleRing F)ˣ) (hg : Continuous g)
    (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))) :
    Continuous fun t ↦ schwartzBruhatUnitTranslate (g t) f :=
  continuous_schwartzUnitOrbit_of_coordinates (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    (continuous_mixedCoordinates F) (archimedeanSchwartzBruhat_equiv (F := F)).choose
    (archimedeanSchwartzBruhat_equiv (F := F)).choose_spec g hg f

private theorem locallyConstant_unit_family {G R Y : Type*} [TopologicalSpace G] [WeaklyLocallyCompactSpace G]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Zero Y]
    (u : G → Rˣ) (hu : Continuous u) (f : R → Y) (hf : IsLocallyConstant f) (hK : HasCompactSupport f) :
    IsLocallyConstant fun g x ↦ f ((u g).inv * x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro g
  obtain ⟨L,hL,hLg⟩ := exists_compact_mem_nhds g
  let K := (fun p : G × R ↦ (u p.1).val * p.2) '' (L ×ˢ tsupport f)
  have hc : IsCompact K := (hL.prod hK).image ((Units.continuous_val.comp (hu.comp continuous_fst)).mul continuous_snd)
  let W := {p : G × R | f ((u p.1).inv * p.2) = f ((u g).inv * p.2)}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have h₁ := (Units.continuous_coe_inv.comp (hu.comp continuous_fst)).mul (continuous_snd (X := G) (Y := R))
    have h₂ : Continuous (fun p : G × R ↦ (u g).inv * p.2) := continuous_const.mul continuous_snd
    filter_upwards [h₁.continuousAt (hf.eventually_eq _), h₂.continuousAt (hf.eventually_eq _)]
      with q hq hq'
    exact hq.trans (hp.trans hq'.symm)
  obtain ⟨U,V,hU,_,hu₀,hV,hUV⟩ := generalized_tube_lemma (isCompact_singleton (x := g)) hc hW
    (fun ⟨g',x⟩ h ↦ by rw [show g' = g from h.1]; rfl)
  filter_upwards [hLg, hU.mem_nhds (hu₀ (mem_singleton g))] with t ht hu'
  funext x
  by_cases hx : x ∈ K
  · exact @hUV (t,x) ⟨hu',hV hx⟩
  · have hz (a : G) (ha : a ∈ L) : f ((u a).inv * x) = 0 := by
      by_contra hn
      exact hx ⟨(a, (u a).inv * x), ⟨ha, subset_closure (show (u a).inv * x ∈ support f from hn)⟩,
        by change (u a).val * ((u a).inv * x) = x; rw [← mul_assoc, (u a).val_inv, one_mul]⟩
    exact (hz t ht).trans (hz g (mem_of_mem_nhds hLg)).symm

section
variable {F : Type*} [Field F] [NumberField F]

private theorem compact_subgroups_of_equiv {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (e : A ≃* B) (he : IsHomeomorph e)
    (h : ∀ s : Set A, IsCompact s → ∃ H : Subgroup A, IsCompact (H : Set A) ∧ s ⊆ H)
    (s : Set B) (hs : IsCompact s) : ∃ H : Subgroup B, IsCompact (H : Set B) ∧ s ⊆ H := by
  obtain ⟨K,hK,hsub⟩ := h (e ⁻¹' s) (he.isClosedEmbedding.isCompact_preimage hs)
  exact ⟨K.map e, hK.image he.continuous, fun x hx ↦
    ⟨e.symm x, hsub (show e (e.symm x) ∈ s from (e.apply_symm_apply x).symm ▸ hx), e.apply_symm_apply x⟩⟩

private theorem finiteAdele_test_locallyConstant (f : SchwartzBruhat (Multiplicative (FiniteAdeleRing (𝓞 F) F))) :
    IsLocallyConstant (fun x ↦ f (Multiplicative.ofAdd x)) ∧
      HasCompactSupport (fun x ↦ f (Multiplicative.ofAdd x)) := by
  let G := Multiplicative (FiniteAdeleRing (𝓞 F) F)
  let E := (finiteAdeleTail_empty F).choose
  have hE := (finiteAdeleTail_empty F).choose_spec.1
  let e := E.toAddEquiv.toMultiplicative
  have he : IsHomeomorph e := hE
  let : TotallyDisconnectedSpace G :=
    ⟨isTotallyDisconnected_of_image
      (RestrictedProduct.continuous_coe.comp continuous_toAdd).continuousOn
      (DFunLike.coe_injective.comp Multiplicative.toAdd.injective)
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : T2Space G := by
    change T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let M : Submodule ℂ (G → ℂ) :=
    { carrier := {h | IsLocallyConstant h ∧ HasCompactSupport h}
      zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      add_mem' := fun hf hh ↦ ⟨hf.1.comp₂ hh.1 (· + ·), hf.2.add hh.2⟩
      smul_mem' := fun c _ hf ↦ ⟨hf.1.comp (c • ·), hf.2.smul_left⟩ }
  have hle : schwartzBruhatSubmodule G ≤ M := by
    refine iSup_le fun a ↦ iSup_le fun w ↦ ?_
    rintro _ ⟨s, rfl⟩
    exact bruhatStage_locallyConstant_compactSupport
      (compact_subgroups_of_equiv e he (finiteAdeleTail_compact_subset_subgroup F ∅)) a w s
  exact hle f.property
end

section
variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
local notation "B" => SchwartzBruhat (Multiplicative R)

/-- The action of the units of `R` on Schwartz-Bruhat functions by translation, as a monoid
homomorphism to the endomorphisms. -/
def unitTranslateEnd : Rˣ →* Module.End ℂ B where
  toFun u :=
    { toFun := schwartzBruhatUnitTranslate u
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_one' := LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦
    congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (one_mul x.toAdd))
  map_mul' := fun u v ↦ LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦
    congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_assoc v.inv u.inv x.toAdd))

/-- Translation of Schwartz-Bruhat functions by a unit is continuous. -/
theorem continuous_unitTranslate [T2Space R] [LocallyCompactSpace R] (g : Rˣ) :
    Continuous (schwartzBruhatUnitTranslate g) := by
  let : T2Space (Multiplicative R) := inferInstanceAs (T2Space R)
  let : LocallyCompactSpace (Multiplicative R) := inferInstanceAs (LocallyCompactSpace R)
  let d : Multiplicative R ≃ₜ* Multiplicative R :=
    { toFun := fun x ↦ Multiplicative.ofAdd (g.val * x.toAdd)
      invFun := fun x ↦ Multiplicative.ofAdd (g.inv * x.toAdd)
      left_inv := fun x ↦ congrArg Multiplicative.ofAdd (by change g.inv * (g.val * x.toAdd) = x.toAdd; rw [← mul_assoc, g.inv_val, one_mul])
      right_inv := fun x ↦ congrArg Multiplicative.ofAdd (by change g.val * (g.inv * x.toAdd) = x.toAdd; rw [← mul_assoc, g.val_inv, one_mul])
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (mul_add g.val x.toAdd y.toAdd)
      continuous_toFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd)
      continuous_invFun := continuous_ofAdd.comp (continuous_const.mul continuous_toAdd) }
  obtain ⟨L, hL⟩ := schwartzBruhat_transport d
  exact L.continuous.congr fun f ↦ Subtype.ext (funext (hL f))

end

private theorem tensor_orbits_continuous {G X Y Z : Type*} [TopologicalSpace G]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
    (e : InductiveTensor X Y ≃L[ℂ] Z) (T : G → Module.End ℂ Z)
    (a : G → X → X) (b : G → Y → Y) (ha : ∀ x, Continuous fun g ↦ a g x)
    (hb : ∀ y, IsLocallyConstant fun g ↦ b g y)
    (he : ∀ g x y, T g (e (x ⊗ₜ[ℂ] y)) = e (a g x ⊗ₜ[ℂ] b g y)) :
    ∀ z, Continuous fun g ↦ T g z := by
  have hsp := withGeneratingSeminorms_spec (X ⊗[ℂ] Y)
    (fun p : {p : Seminorm ℂ (X ⊗[ℂ] Y) //
      (∀ x : X, Continuous (fun y : Y ↦ p (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : Y, Continuous (fun x : X ↦ p (x ⊗ₜ[ℂ] y)))} ↦ p.val)
  have hleft (y : Y) : Continuous (fun x : X ↦ e (x ⊗ₜ[ℂ] y)) := e.continuous.comp
    (hsp.continuous_of_continuous_comp ((TensorProduct.mk ℂ X Y).flip y) fun p ↦ p.2.2 y)
  intro z
  obtain ⟨w, rfl⟩ := e.surjective z
  induction w using TensorProduct.inductionOn with
  | tmul x y =>
    apply continuous_iff_continuousAt.mpr
    intro g
    apply ((hleft (b g y)).comp (ha x)).continuousAt.congr_of_eventuallyEq
    filter_upwards [(hb y).eventually_eq g] with t ht
    exact (he t x y).trans (congrArg (fun s ↦ e (a t x ⊗ₜ[ℂ] s)) ht)
  | add u v hu hv =>
    exact (hu.add hv).congr fun g ↦ ((congrArg (T g) (e.map_add u v)).trans
      ((T g).map_add (e u) (e v))).symm
private theorem continuous_global_unit_orbits {F : Type*} [Field F] [NumberField F]
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    Continuous fun u : IdeleGroup (𝓞 F) F ↦ schwartzBruhatUnitTranslate u f := by
  let I := IdeleGroup (𝓞 F) F
  let R := FiniteAdeleRing (𝓞 F) F
  let : LocallyCompactSpace I := (ideleGroup_topology F).2.1
  let πa : I →* (InfiniteAdeleRing F)ˣ := Units.map (MonoidHom.fst _ _)
  let πb : I →* Rˣ := Units.map (MonoidHom.snd _ _)
  have hπa : Continuous πa := continuous_fst.units_map _
  have hπb : Continuous πb := continuous_snd.units_map _
  let e := (adeleSchwartz_inductiveTensor_equiv F).choose
  have he := (adeleSchwartz_inductiveTensor_equiv F).choose_spec
  refine tensor_orbits_continuous (G := I) e (fun u ↦ unitTranslateEnd (R := 𝔸[F]) u)
    (fun u ↦ schwartzBruhatUnitTranslate (πa u)) (fun u ↦ schwartzBruhatUnitTranslate (πb u))
    (continuous_archUnitOrbit πa hπa) ?_ ?_ f
  · intro φ
    obtain ⟨hl, hc⟩ := finiteAdele_test_locallyConstant φ
    have H := locallyConstant_unit_family πb hπb (fun x ↦ φ (Multiplicative.ofAdd x)) hl hc
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun u ↦ ?_
    filter_upwards [H.eventually_eq u] with t ht
    exact Subtype.ext (funext fun x ↦ congrFun ht x.toAdd)
  · intro u a b
    apply Subtype.ext
    funext x
    exact (he a b (u.inv * x.toAdd)).trans
      (he (schwartzBruhatUnitTranslate (πa u) a) (schwartzBruhatUnitTranslate (πb u) b) x.toAdd).symm

private theorem global_unit_joint {F : Type*} [Field F] [NumberField F] :
    Continuous fun p : IdeleGroup (𝓞 F) F × SchwartzBruhat (Multiplicative 𝔸[F]) ↦
      schwartzBruhatUnitTranslate p.1 p.2 := by
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let : LocallyCompactSpace (IdeleGroup (𝓞 F) F) := (ideleGroup_topology F).2.1
  let : LocallyCompactSpace 𝔸[F] := adele_locallyCompact F
  let : T2Space 𝔸[F] := (adeleHausdorff_ideleLocallyCompact F).1
  let : BarrelledSpace ℂ E := (adeleSchwartz_montel (F := F)).2.1
  let : PolynormableSpace ℂ E := (show IsNuclearTVS.{0} E from (adeleSchwartz_nuclear (F := F)).2).2.1
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact continuous_family_of_orbits (G := IdeleGroup (𝓞 F) F) (E := E) (fun u ↦ ⟨unitTranslateEnd (R := 𝔸[F]) u, continuous_unitTranslate (R := 𝔸[F]) u⟩)
    (continuous_global_unit_orbits (F := F))

/-- Descend a jointly continuous family through open quotient maps on both factors.
The stabilizing subgroup acts trivially on the quotient module. -/
private theorem descendQuotientAction {G E : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (N : Subgroup G) [N.Normal] (K : Submodule ℂ E)
    (T : G →* (Module.End ℂ E)) (hc : Continuous fun p : G × E ↦ T p.1 p.2)
    (hs : ∀ g, K ≤ K.comap (T g)) (ht : ∀ g ∈ N, ∀ x, K.mkQ (T g x) = K.mkQ x) :
    ∃! ρ : G ⧸ N →* ((E ⧸ K) →L[ℂ] (E ⧸ K)),
      (Continuous fun p : (G ⧸ N) × (E ⧸ K) ↦ ρ p.1 p.2) ∧
      ∀ g x, ρ (QuotientGroup.mk g) (K.mkQ x) = K.mkQ (T g x) := by
  let L (g : G) : (E ⧸ K) →L[ℂ] (E ⧸ K) :=
    ⟨K.mapQ K (T g) (hs g), K.isQuotientMap_mkQ.continuous_iff.mpr
      (K.mkQL.continuous.comp (hc.comp (continuous_const.prodMk continuous_id)))⟩
  have hL (g : G) (x : E) : L g (K.mkQ x) = K.mkQ (T g x) := rfl
  let A : G →* ((E ⧸ K) →L[ℂ] (E ⧸ K)) :=
    { toFun := L
      map_one' := ContinuousLinearMap.ext fun x ↦ K.mkQ_surjective x |>.elim fun f hf ↦ by
        rw [← hf, hL, map_one]; rfl
      map_mul' := fun a b ↦ ContinuousLinearMap.ext fun x ↦ K.mkQ_surjective x |>.elim fun f hf ↦ by
        rw [← hf]
        exact (hL (a*b) f).trans (congrArg K.mkQ (DFunLike.congr_fun (T.map_mul a b) f)) }
  have hN : N ≤ A.ker := fun g hg ↦ ContinuousLinearMap.ext fun x ↦
    (K.mkQ_surjective x).elim fun f hf ↦ hf ▸ ht g hg f
  let ρ := QuotientGroup.lift N A hN
  have hprod := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap K.isOpenQuotientMap_mkQ
  refine ⟨ρ, ⟨hprod.isQuotientMap.continuous_iff.mpr (K.mkQL.continuous.comp hc),
    fun _ _ ↦ rfl⟩, ?_⟩
  intro τ hτ
  refine MonoidHom.ext fun a ↦ ContinuousLinearMap.ext fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨f, rfl⟩ := K.mkQ_surjective x
  exact hτ.2 g f

private theorem globalTheta_translate_apply (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽) (a : C𝔽) :
    adelicTheta (schwartzBruhatUnitTranslate g f) a = adelicTheta f ((QuotientGroup.mk g)⁻¹ * a) := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  change _ = adelicTheta f (QuotientGroup.mk (g⁻¹ * x))
  rw [adelicTheta_mk (schwartzBruhatUnitTranslate g f) x, adelicTheta_mk f (g⁻¹ * x)]
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y))
    (mul_left_comm g.inv (algebraMap F 𝔸[F] (t : F)) x.val)

private theorem thetaAction_of_translate {G E A : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [TopologicalSpace A] (N : Subgroup G) [N.Normal]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (T : G →* Module.End ℂ E) (t : G → E → E)
    (ht : ∀ g x, T g x = t g x)
    (hc : Continuous fun p : G × E ↦ t p.1 p.2) (r : G → A → A)
    (hr : ∀ g f a, θ (t g f) a = θ f (r g a))
    (hN : ∀ g ∈ N, ∀ f a, θ f (r g a) = θ f a) :
    ∃! ρ : G ⧸ N →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)),
      (Continuous fun p : (G ⧸ N) × (E ⧸ θ.ker) ↦ ρ p.1 p.2) ∧
      ∀ g x, ρ (QuotientGroup.mk g) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (t g x) := by
  have he : t = fun g x ↦ T g x := funext fun g ↦ funext fun x ↦ (ht g x).symm
  subst t
  apply descendQuotientAction N θ.ker T hc
  · intro g f hf
    exact ContinuousMap.ext fun a ↦ (hr g f a).trans
      (congrArg (fun φ : C(A, ℂ) ↦ φ (r g a)) (LinearMap.mem_ker.mp hf))
  · intro g hg f
    apply (Submodule.Quotient.eq _).mpr
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ContinuousMap.ext fun a ↦ (hr g f a).trans (hN g hg f a)

/-- The radial dilation difference on the added finite place has only finitely
many valuation shells, uniformly in the other variables of a pure tensor. -/
theorem finitePlaceSchwartz_dilation_sub_valuation (w : HeightOneSpectrum (𝓞 F))
    (f : SchwartzBruhat (Multiplicative (w.adicCompletion F))) (c : (w.adicCompletion F)ˣ)
    (hr : ∀ x y : w.adicCompletion F, x ≠ 0 → y ≠ 0 → Valued.v x = Valued.v y →
      f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd y)) :
    ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ, ∀ x : w.adicCompletion F, x ≠ 0 →
      b (Valued.v x) = f (Multiplicative.ofAdd x) - f (Multiplicative.ofAdd (c.val * x)) := by
  obtain ⟨hf, hc⟩ := (mem_finitePlaceSchwartz_iff F w _).mp ⟨f, fun _ ↦ rfl⟩
  exact exists_finsupp_valuation_dilation_sub Valued.v
    (fun x hx ↦ Valued.locally_const ((Valuation.ne_zero_iff _).mpr hx))
    _ hf hc hr c

private theorem sum_orbit_invariant {G E : Type*} [Group G] [AddCommMonoid E] [Module ℂ E]
    (r : G →* Module.End ℂ E) (f : E) (hf : (range fun g ↦ r g f).Finite) (g : G) :
    r g (∑ y ∈ hf.toFinset, y) = ∑ y ∈ hf.toFinset, y := by
  classical
  have he (a b : G) (x : E) : r (a * b) x = r a (r b x) := DFunLike.congr_fun (r.map_mul a b) x
  have hi (x : E) (h : x ∈ hf.toFinset) (a : G) : r a x ∈ hf.toFinset := by
    obtain ⟨b,rfl⟩ := hf.mem_toFinset.mp h
    exact hf.mem_toFinset.mpr ⟨a*b, he _ _ _⟩
  have hinv (a : G) (x : E) : r a⁻¹ (r a x) = x := by rw [← he, inv_mul_cancel, map_one]; rfl
  rw [map_sum]
  exact Finset.sum_bij' (fun a _ ↦ r g a) (fun a _ ↦ r g⁻¹ a)
    (fun a ha ↦ hi a ha g) (fun a ha ↦ hi a ha g⁻¹) (fun a _ ↦ hinv g a)
    (fun a _ ↦ by simpa using hinv g⁻¹ a) (fun _ _ ↦ rfl)

/-- Normalized averaging over the finite orbit under local units gives a radial
test function. Each dilation difference of that average has finite valuation support. -/
theorem finitePlaceSchwartz_average_dilation (w : HeightOneSpectrum (𝓞 F))
    (f : SchwartzBruhat (Multiplicative (w.adicCompletion F))) :
    ∃ O : Finset (SchwartzBruhat (Multiplicative (w.adicCompletion F))),
      (∀ h, h ∈ O ↔ ∃ u : (w.adicCompletionIntegers F).units, schwartzBruhatUnitTranslate u.val f = h) ∧
      ∀ c : (w.adicCompletion F)ˣ, ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ,
        ∀ x : w.adicCompletion F, x ≠ 0 →
          b (Valued.v x) = (O.card : ℂ)⁻¹ * ∑ h ∈ O,
            (h (Multiplicative.ofAdd x) - h (Multiplicative.ofAdd (c.val * x))) := by
  classical
  let H := (w.adicCompletionIntegers F).units
  let : CompactSpace H := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers w)))
  let r := (unitTranslateEnd (R := w.adicCompletion F)).comp H.subtype
  obtain ⟨hf,hc⟩ := (mem_finitePlaceSchwartz_iff F w _).mp ⟨f, fun _ ↦ rfl⟩
  have hloc := locallyConstant_unit_family (H.subtype : H → (w.adicCompletion F)ˣ)
    continuous_subtype_val (fun x ↦ f (Multiplicative.ofAdd x)) hf hc
  have hfinite : (range fun u : H ↦ r u f).Finite := by
    apply IsLocallyConstant.range_finite
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun u ↦
      (hloc.eventually_eq u).mono fun a h ↦ Subtype.ext h
  let O := hfinite.toFinset
  let avg := (O.card : ℂ)⁻¹ • ∑ h ∈ O, h
  refine ⟨O, fun h ↦ hfinite.mem_toFinset, fun c ↦ ?_⟩
  have hinv (a : H) : r a avg = avg :=
    (map_smul (r a) _ _).trans (congrArg ((O.card : ℂ)⁻¹ • ·) (sum_orbit_invariant r f hfinite a))
  have hr (x y : w.adicCompletion F) (hx : x ≠ 0) (hy : y ≠ 0) (he : Valued.v x = Valued.v y) :
      avg (Multiplicative.ofAdd x) = avg (Multiplicative.ofAdd y) := by
    let u := Units.mk0 y hy / Units.mk0 x hx
    have hu : u ∈ H := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (show Valued.v (y / x) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
    have hu' : u.val * x = y := div_mul_cancel₀ _ hx
    have hh := congrArg (fun h : SchwartzBruhat (Multiplicative (w.adicCompletion F)) ↦
      h (Multiplicative.ofAdd x)) (hinv (⟨u,hu⟩ : H)⁻¹)
    exact hh.symm.trans (congrArg (fun z ↦ avg (Multiplicative.ofAdd z)) hu')
  obtain ⟨b,hb⟩ := finitePlaceSchwartz_dilation_sub_valuation w avg c hr
  refine ⟨b, fun x hx ↦ (hb x hx).trans ?_⟩
  have havg (y : w.adicCompletion F) : avg (Multiplicative.ofAdd y) =
      (O.card : ℂ)⁻¹ * ∑ h ∈ O, h (Multiplicative.ofAdd y) := by
    change (O.card : ℂ)⁻¹ * ((∑ h ∈ O, h : SchwartzBruhat _) (Multiplicative.ofAdd y)) = _
    exact congrArg ((O.card : ℂ)⁻¹ * ·) (map_sum (schwartzBruhatEvalCLM (Multiplicative.ofAdd y)) _ _)
  rw [havg, havg, ← mul_sub, Finset.sum_sub_distrib]

end UnitActions

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the global idele class group induces a jointly continuous linear
action on the global theta quotient.
Deviation: The action is characterized on test functions by idele representatives. -/
theorem existsUnique_globalThetaAction :
    ∃! ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽),
      Continuous (fun p : C𝔽 × Θ𝔽 ↦ ρ p.1 p.2) ∧
      ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by
  let π : IdeleGroup (𝓞 F) F →* C𝔽 := QuotientGroup.mk' _
  have h (g : IdeleGroup (𝓞 F) F) (hg : g ∈ IdeleGroup.principalSubgroup (𝓞 F) F)
      (f : ℬ𝔽) (a : C𝔽) : adelicTheta f ((π g)⁻¹ * a) = adelicTheta f a :=
    congrArg (adelicTheta f) ((congrArg (fun z : C𝔽 ↦ z⁻¹ * a)
      ((QuotientGroup.eq_one_iff g).mpr hg)).trans ((congrArg (· * a) inv_one).trans (one_mul a)))
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  let Tt := unitTranslateEnd (R := 𝔸[F])
  let θ := adelicThetaLinearMap F
  let t := schwartzBruhatUnitTranslate (R := 𝔸[F])
  let r (g : IdeleGroup (𝓞 F) F) (a : C𝔽) := (π g)⁻¹ * a
  have hr : ∀ g f a, θ (t g f) a = θ f (r g a) := globalTheta_translate_apply (F := F)
  have hc : Continuous (fun p : IdeleGroup (𝓞 F) F × ℬ𝔽 ↦ t p.1 p.2) :=
    global_unit_joint (F := F)
  have htt : ∀ g f, Tt g f = t g f := fun _ _ ↦ rfl
  have result := thetaAction_of_translate (G := IdeleGroup (𝓞 F) F) (E := ℬ𝔽) (A := C𝔽)
    N θ Tt t htt hc r hr h
  with_reducible exact result

private theorem insert_translate_eq (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f) := by
  classical
  let g := integralIdeleInsertion F S u
  let gS := Units.map (adeleProjection F S).toMonoidHom g
  refine Subtype.ext (funext fun x ↦ ?_)
  let y := x.toAdd
  have h := mul_integralUnit_mem_iff u⁻¹ y
  change g.inv * y ∈ integralAdelesOutside F S ↔ y ∈ integralAdelesOutside F S at h
  refine (toGlobal_apply_integral (schwartzBruhatUnitTranslate gS f) y).trans ?_
  refine Eq.trans (if_congr h.symm ?_ rfl) (toGlobal_apply_integral f (g.inv * y)).symm
  exact congrArg (fun t ↦ f (Multiplicative.ofAdd t)) (map_mul (adeleProjection F S) g.inv y).symm

private theorem insert_translate_of_mem_range {g : IdeleGroup (𝓞 F) F}
    (hg : g ∈ Set.range (integralIdeleInsertion F T)) (f : ℬₛ(T)) :
    sAdeleSchwartzToGlobal F T
      (schwartzBruhatUnitTranslate (Units.map (adeleProjection F T).toMonoidHom g) f) =
        schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F T f) := by
  obtain ⟨u, rfl⟩ := hg
  exact insert_translate_eq u f

private theorem localTheta_translate_apply (g x : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g f) x = sLocalAdelicTheta F S f (g⁻¹ * x) := by
  let d := (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F S).toMonoidHom)
  refine (sLocalAdelicTheta_apply F S (schwartzBruhatUnitTranslate g f) x).trans
    (Eq.trans ?_ (sLocalAdelicTheta_apply F S f (g⁻¹ * x)).symm)
  exact tsum_congr fun t ↦ congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_left_comm g.inv (d t).val x.val)

private theorem test_insert_translate (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)) :
    sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate g f) =
      schwartzBruhatUnitTranslate (sIdeleInsertion F S g) (sAdeleSchwartzToGlobal F S f) := by
  let j := sIdeleInsertion F S
  have hu : j g ∈ Set.range (integralIdeleInsertion F S) :=
    (mem_range_integralIdeleInsertion F S (j g)).mpr fun v hv ↦ by
      refine ⟨(sIdeleInsertion_apply F S g).2.2 v hv ▸ (v.adicCompletionIntegers F).one_mem, ?_⟩
      have h' : (j g).inv.2 v = 1 := (congrArg (fun x : IdeleGroup (𝓞 F) F ↦ x.val.2 v)
        (map_inv j g).symm).trans ((sIdeleInsertion_apply F S g⁻¹).2.2 v hv)
      exact h' ▸ (v.adicCompletionIntegers F).one_mem
  have hp : Units.map (adeleProjection F S).toMonoidHom (j g) = g := Units.ext
    (Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1))
  exact (congrArg (fun v ↦ sAdeleSchwartzToGlobal F S (schwartzBruhatUnitTranslate v f)) hp.symm).trans
    (insert_translate_of_mem_range (F := F) (T := S) (g := j g) hu f)

private theorem joint_of_inducing {H G X Y : Type*} [TopologicalSpace H] [TopologicalSpace G]
    [TopologicalSpace X] [TopologicalSpace Y] (a : H → X → X) (b : G → Y → Y)
    (u : H → G) (i : X → Y) (hu : Continuous u) (hi : IsInducing i)
    (hb : Continuous fun p : G × Y ↦ b p.1 p.2)
    (h : ∀ v x, i (a v x) = b (u v) (i x)) : Continuous fun p : H × X ↦ a p.1 p.2 :=
  hi.continuous_iff.mpr <| (hb.comp ((hu.comp continuous_fst).prodMk
    (hi.continuous.comp continuous_snd))).congr fun p ↦ (h p.1 p.2).symm

private theorem local_unit_joint :
    Continuous fun p : (SAdeleRing F S)ˣ × ℬₛ(S) ↦ schwartzBruhatUnitTranslate p.1 p.2 :=
  joint_of_inducing (H := (SAdeleRing F S)ˣ) (G := IdeleGroup (𝓞 F) F)
    (X := ℬₛ(S)) (Y := ℬ𝔽) schwartzBruhatUnitTranslate schwartzBruhatUnitTranslate
    (sIdeleInsertion F S) (sAdeleSchwartzToGlobal F S) (isClosedEmbedding_sIdeleInsertion F S).continuous
    (sAdeleSchwartzToGlobal_isEmbedding F S).isInducing (global_unit_joint (F := F))
    (test_insert_translate (F := F) (S := S))

private theorem mk_inv_mul_of_mem {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    {g : G} (hg : g ∈ N) (a : G) :
    (QuotientGroup.mk (g⁻¹ * a) : G ⧸ N) = QuotientGroup.mk a := by
  let π := QuotientGroup.mk' N
  change π (g⁻¹ * a) = π a
  rw [map_mul, map_inv, show π g = 1 from (QuotientGroup.eq_one_iff g).mpr hg, inv_one, one_mul]

/-- Paper: Theorem 5.2.1.1(2), p. 230.
Left translation by the S-idele quotient induces a jointly continuous linear
action on the S-local theta quotient.
Deviation: The action is characterized on test functions by S-idele representatives. -/
theorem existsUnique_sLocalThetaAction :
    ∃! ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)),
      Continuous (fun p : Jₛ(S) × Θₛ(S) ↦ ρ p.1 p.2) ∧
      ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)),
        ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
          Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f) := by
  let N := Subgroup.map (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    (MonoidHom.range (Units.map (integralAdeleDiagonal F S).toMonoidHom))
  have h (g : (SAdeleRing F S)ˣ) (hg : g ∈ N) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      sLocalAdelicTheta F S f (g⁻¹ * a) = sLocalAdelicTheta F S f a :=
    sLocalAdelicTheta_factorsThrough F S f (mk_inv_mul_of_mem N hg a)
  let Tt := unitTranslateEnd (R := SAdeleRing F S)
  let θ := sLocalAdelicTheta F S
  let t := schwartzBruhatUnitTranslate (R := SAdeleRing F S)
  let r (g a : (SAdeleRing F S)ˣ) := g⁻¹ * a
  have hr : ∀ g f a, θ (t g f) a = θ f (r g a) :=
    fun g f a ↦ localTheta_translate_apply (F := F) (S := S) g a f
  have hc : Continuous (fun p : (SAdeleRing F S)ˣ × ℬₛ(S) ↦ t p.1 p.2) :=
    local_unit_joint (F := F) (S := S)
  have htt : ∀ g f, Tt g f = t g f := fun _ _ ↦ rfl
  have result := thetaAction_of_translate (G := (SAdeleRing F S)ˣ) (E := ℬₛ(S)) (A := (SAdeleRing F S)ˣ)
    N θ Tt t htt hc r hr h
  with_reducible exact result

private theorem insert_mem_larger (hST : S ⊆ T) (u : (integralAdelesOutside F S)ˣ) :
    integralIdeleInsertion F S u ∈ Set.range (integralIdeleInsertion F T) := by
  let g := integralIdeleInsertion F S u
  have hg : g ∈ Set.range (integralIdeleInsertion F S) := ⟨u, rfl⟩
  exact (mem_range_integralIdeleInsertion F T g).mpr fun v hv ↦
    (mem_range_integralIdeleInsertion F S g).mp hg v (fun h ↦ hv (hST h))

private theorem testTransition_translate_eq (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sAdeleSchwartzTransition F hST (schwartzBruhatUnitTranslate gS f) =
      schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f) := by
  let g := integralIdeleInsertion F S u
  let gS := Units.map (adeleProjection F S).toMonoidHom g
  let gT := Units.map (adeleProjection F T).toMonoidHom g
  have hTS (k : ℬₛ(S)) : sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST k) =
      sAdeleSchwartzToGlobal F S k := DFunLike.congr_fun (sAdeleSchwartzToGlobal_comp F hST) k
  have hT := insert_translate_of_mem_range (insert_mem_larger hST u) (sAdeleSchwartzTransition F hST f)
  exact (sAdeleSchwartzToGlobal_isEmbedding F T).injective
    ((hTS _).trans ((insert_translate_eq u f).trans
        ((congrArg (schwartzBruhatUnitTranslate g) (hTS f).symm).trans hT.symm)))

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The S-to-T theta transition intertwines the actions of the S-idele classes.
Deviation: On an integral-outside-S idele representative, the two actions are
given by projecting it to S and T, respectively. -/
theorem sLocalThetaTransition_equivariant (hST : S ⊆ T)
    (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    let gT := Units.map (adeleProjection F T).toMonoidHom g
    sLocalThetaTransition hST (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate gT (sAdeleSchwartzTransition F hST f)) := congrArg (Kₛ(T)).mkQ (testTransition_translate_eq hST u f)

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local insertion intertwines the actions of S-idele classes through their
projection to the S-idele quotient and their inclusion in the global classes.
Deviation: The equation is on representatives of the acting group and the theta quotient. -/
theorem sLocalThetaToGlobal_equivariant (u : (integralAdelesOutside F S)ˣ) (f : ℬₛ(S)) :
    let g := integralIdeleInsertion F S u
    let gS := Units.map (adeleProjection F S).toMonoidHom g
    sLocalThetaToGlobal F S (Submodule.Quotient.mk (schwartzBruhatUnitTranslate gS f)) =
      Submodule.Quotient.mk
        (schwartzBruhatUnitTranslate g (sAdeleSchwartzToGlobal F S f)) := congrArg (K𝔽).mkQ (insert_translate_eq u f)

section OnePlaceRetraction

/-! To retract a one-place enlargement, average its theta values over the new unit group
and subtract the same average shifted by an inverse uniformizer. On a pure tensor the
difference has finitely many valuation shells, each giving a translate of the old test.
Separate continuity on tensors and descent along the theta quotient extend this formula
to a continuous linear left inverse on the entire larger space. -/

open TensorProduct Set
open scoped TensorProduct Classical


/-- Recover a quotient-valued operator from its separated scalar evaluations on each tensor slice. -/
private theorem recover_tensor_quotient {X V Z Q A : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [PolynormableSpace ℂ V] [T2Space V]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [PolynormableSpace ℂ Z] [T2Space Z]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (q : InductiveTensor X V →ₗ[ℂ] Q) (hq : IsQuotientMap q)
    (ev : Z →ₗ[ℂ] (A → ℂ)) (hinj : Injective ev) (sample : Q →ₗ[ℂ] (A → ℂ))
    (hfin : ∀ L : V →ₗ[ℂ] Z, Continuous L)
    (hslice : ∀ v : V, ∃ L : X →L[ℂ] Z, ∀ x : X, ev (L x) = sample (q (x ⊗ₜ[ℂ] v))) :
    ∃ r : Q →L[ℂ] Z, ∀ z, ev (r z) = sample z := by
  have hrange (z : Q) : sample z ∈ ev.range := by
    obtain ⟨t, rfl⟩ := hq.surjective z
    let q' : X ⊗[ℂ] V →ₗ[ℂ] Q := q
    change sample (q' t) ∈ ev.range
    induction t using TensorProduct.inductionOn with
    | tmul x v =>
      obtain ⟨L, hL⟩ := hslice v
      exact ⟨L x, hL x⟩
    | add x y hx hy => rw [q'.map_add x y, sample.map_add]; exact ev.range.add_mem hx hy
  let e := LinearEquiv.ofInjective ev hinj
  let r := e.symm.toLinearMap.comp (sample.codRestrict ev.range hrange)
  have he (z : Q) : ev (r z) = sample z :=
    congrArg Subtype.val (e.apply_symm_apply ⟨sample z, hrange z⟩)
  refine ⟨⟨r, hq.continuous_iff.mpr ((continuous_inductiveTensor_iff (r.comp q)).mpr ⟨?_, ?_⟩)⟩, he⟩
  · intro x
    exact hfin ((r.comp q).comp (TensorProduct.mk ℂ X V x))
  · intro v
    obtain ⟨L, hL⟩ := hslice v
    exact L.continuous.congr fun x ↦ hinj ((hL x).trans (he (q (x ⊗ₜ[ℂ] v))).symm)

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "B(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Y(" S ")" => SchwartzBruhat (Multiplicative (FinitePlaceProduct F S))
local notation "Q(" S ")" => SLocalAdelicThetaSpace F S
local notation "K(" S ")" => LinearMap.ker (sLocalAdelicTheta F S)

private def testValues {X A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace A]
    (θ : X →ₗ[ℂ] C(A, ℂ)) : (X ⧸ θ.ker) →ₗ[ℂ] (A → ℂ) :=
  LinearMap.pi fun a ↦ (ContinuousMap.evalCLM ℂ a).toLinearMap.comp (θ.ker.liftQ θ le_rfl)

private theorem testValues_injective {X A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace A]
    (θ : X →ₗ[ℂ] C(A, ℂ)) : Injective (testValues θ) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, rfl⟩ := θ.ker.mkQ_surjective z
  exact (Submodule.Quotient.mk_eq_zero _).mpr (ContinuousMap.ext fun a ↦ congrFun (LinearMap.mem_ker.mp hz) a)

private def localValues (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SLocalAdelicThetaSpace F S →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ) :=
  testValues (sLocalAdelicTheta F S)

private def localClass (S : Finset V) (f : B(S)) : Q(S) := Submodule.Quotient.mk f

/-- Separate continuity for the inductive tensor product descends through the larger quotient. -/
private theorem quotient_retraction_of_classes {X N Y A B : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [PolynormableSpace ℂ X] [T2Space X]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N] [PolynormableSpace ℂ N] [T2Space N]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    (θ : X →ₗ[ℂ] C(A, ℂ)) (τ : Y →ₗ[ℂ] C(B, ℂ))
    [T2Space (X ⧸ θ.ker)] [PolynormableSpace ℂ (X ⧸ θ.ker)]
    (j : X →ₗ[ℂ] Y) (hj : θ.ker ≤ τ.ker.comap j) (e : InductiveTensor X N ≃L[ℂ] Y)
    (hfin : (inferInstance : TopologicalSpace N) = (inferInstance : TopologicalSpace (FinestLocallyConvex N)))
    (sample : (Y ⧸ τ.ker) →ₗ[ℂ] (A → ℂ))
    (hslice : ∀ v : N, ∃ L : X →L[ℂ] (X ⧸ θ.ker), ∀ x,
      testValues θ (L x) = sample (Submodule.Quotient.mk (e (x ⊗ₜ[ℂ] v))))
    (hfix : ∀ x, sample (Submodule.Quotient.mk (j x)) = ⇑(θ x)) :
    ∃ r : (Y ⧸ τ.ker) →L[ℂ] (X ⧸ θ.ker), LeftInverse r (θ.ker.mapQ τ.ker j hj) ∧
      ∀ z, testValues θ (r z) = sample z := by
  let q := τ.ker.mkQ.comp e.toLinearMap
  have hq : IsQuotientMap q := τ.ker.isQuotientMap_mkQ.comp e.toHomeomorph.isQuotientMap
  have hc (L : N →ₗ[ℂ] (X ⧸ θ.ker)) : Continuous L :=
    Eq.mpr (congrArg (fun t ↦ @Continuous N (X ⧸ θ.ker) t _ L) hfin) (continuous_of_finestLocallyConvex N L)
  obtain ⟨r, hr⟩ := recover_tensor_quotient (X := X) («V» := N) q hq _ (testValues_injective θ) sample hc hslice
  refine ⟨r, fun z ↦ ?_, hr⟩
  obtain ⟨x, rfl⟩ := θ.ker.mkQ_surjective z
  exact testValues_injective θ ((hr _).trans (hfix x))

open Classical in
private theorem finiteTheta_retraction_of_classes {S T : Finset V} (h : S ⊆ T)
    (e : InductiveTensor B(S) Y(T \ S) ≃L[ℂ] B(T))
    (sample : Q(T) →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ))
    (hslice : ∀ v : Y(T \ S), ∃ L : B(S) →L[ℂ] Q(S), ∀ x,
      localValues F S (L x) = sample (localClass (F := F) T (e (x ⊗ₜ[ℂ] v))))
    (hfix : ∀ f : B(S), sample (localClass (F := F) T (sAdeleSchwartzTransition F h f)) =
      ⇑(sLocalAdelicTheta F S f)) :
    ∃ r : Q(T) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) h) ∧
      ∀ z, localValues F S (r z) = sample z := by
  classical
  let D := T \ S
  let : T2Space B(S) := (sAdeleSchwartz_strictLF F S).1
  let : T2Space Y(D) := (finiteProduct_tailSchwartz_strictLF F D ∅).1.1
  let : T2Space Q(S) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ Q(S) := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  change ∃ r : Q(T) →L[ℂ] Q(S), LeftInverse r ((K(S)).mapQ (K(T)) (sAdeleSchwartzTransition F h)
    (sLocalThetaTransition_preserves_kernel (F := F) h)) ∧
      ∀ z, testValues (sLocalAdelicTheta F S) (r z) = sample z
  unfold localClass at hslice hfix
  unfold localValues at hslice
  with_reducible_and_instances
    exact quotient_retraction_of_classes (X := B(S)) (N := Y(D)) (Y := B(T))
      (A := (SAdeleRing F S)ˣ) (B := (SAdeleRing F T)ˣ) (sLocalAdelicTheta F S) (sLocalAdelicTheta F T)
      (sAdeleSchwartzTransition F h) (sLocalThetaTransition_preserves_kernel (F := F) h) e
      (finiteProduct_tailSchwartz_finestTopology F D ∅).1 sample hslice hfix

set_option quotPrecheck false in
local notation "H(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units

open Classical in
private def newUnits (S : Finset V) (v : V) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (w : ↥(insert v S)) : (w.val.adicCompletion F)ˣ := by
  classical
  let split (T : Finset V) := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F T)
  let old := ContinuousMulEquiv.piUnits (M := fun w : S ↦ w.val.adicCompletion F) ((split S x).2)
  exact if hw : w.val = v then hw.symm ▸ u else old ⟨w.val, (Finset.mem_insert.mp w.property).resolve_left hw⟩

open Classical in
private def onePlaceIdele (S : Finset V) (v : V) (x : (SAdeleRing F S)ˣ) :
    C((v.adicCompletion F)ˣ, (SAdeleRing F (insert v S))ˣ) := by
  classical
  let split (T : Finset V) := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FinitePlaceProduct F T)
  let old := ContinuousMulEquiv.piUnits (M := fun w : S ↦ w.val.adicCompletion F) ((split S x).2)
  let fin := ContinuousMulEquiv.piUnits (M := fun w : ↥(insert v S) ↦ w.val.adicCompletion F)
  let j := newUnits S v x
  refine ⟨fun u ↦ (split (insert v S)).symm ((split S x).1, fin.symm (j u)),
    (split (insert v S)).symm.continuous.comp (continuous_const.prodMk
      (fin.symm.continuous.comp (continuous_pi fun w ↦ ?_)))⟩
  have hcast (v₁ v₂ : V) (h : v₁ = v₂) : Continuous (fun u : (v₁.adicCompletion F)ˣ ↦ (h ▸ u : (v₂.adicCompletion F)ˣ)) := by
    cases h
    exact continuous_id
  by_cases hw : w.val = v
  · simpa only [j, newUnits, dite_eq_left hw] using hcast _ _ hw.symm
  · simp only [j, newUnits, dite_eq_right hw]
    exact continuous_const

open TensorProduct
open scoped TensorProduct Classical
private theorem new_coord_eq {S : Finset V} {v : V} (w : ↥(insert v S \ S)) : w.val = v := by
  obtain ⟨ht, hs⟩ := Finset.mem_sdiff.mp w.property
  exact (Finset.mem_insert.mp ht).resolve_right hs

private def newCoords {S : Finset V} (v : V) (hv : v ∉ S) :
    v.adicCompletion F ≃ₜ FinitePlaceProduct F (insert v S \ S) := by
  let w : ↥(insert v S \ S) := ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, hv⟩⟩
  let : Unique ↥(insert v S \ S) := ⟨⟨w⟩, fun z ↦ Subtype.ext (new_coord_eq z)⟩
  exact (Homeomorph.piUnique (fun z : ↥(insert v S \ S) ↦ z.val.adicCompletion F)).symm

private theorem coordinates_old {S : Finset V} {v : V} (hv : v ∉ S) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let h := Finset.subset_insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    (z.1, fun w : S ↦ z.2 ⟨w.val, h w.property⟩) =
      adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val := by
  dsimp only
  refine Prod.ext rfl (funext fun w ↦ ?_)
  have hw : w.val ≠ v := fun e ↦ hv (e ▸ w.property)
  let w' : ↥(insert v S) := ⟨w.val, (Finset.subset_insert v S) w.property⟩
  have h : (newUnits S v x u w').val = x.val.2 w := by
    simp only [newUnits, show w'.val ≠ v from hw, dite_false]
    rfl
  exact congrArg ((algebraMap F (w.val.adicCompletion F) t.val) * ·) h

private theorem coordinates_new {S : Finset V} {v : V} (hv : v ∉ S) (x : (SAdeleRing F S)ˣ)
    (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    (fun w : ↥(T \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) =
      newCoords v hv (algebraMap F (v.adicCompletion F) t.val * u.val) := by
  dsimp only
  apply (newCoords v hv).symm.injective
  rw [Homeomorph.symm_apply_apply]
  let w' : ↥(insert v S) := ⟨v, Finset.mem_insert_self _ _⟩
  have h : (newUnits S v x u w').val = u.val := by
    simp only [newUnits, show w'.val = v from rfl, dite_true]
    rfl
  exact congrArg ((algebraMap F (v.adicCompletion F) t.val) * ·) h

private theorem newTest_exists {S : Finset V} {v : V} (hv : v ∉ S)
    (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S)))) :
    ∃ φ : SchwartzBruhat (Multiplicative (v.adicCompletion F)), ∀ x,
      φ (Multiplicative.ofAdd x) = g (Multiplicative.ofAdd (newCoords v hv x)) := by
  apply (mem_finitePlaceSchwartz_iff F v _).mpr
  let D := insert v S \ S
  let : TotallyDisconnectedSpace (Multiplicative (FinitePlaceProduct F D)) :=
    inferInstanceAs (TotallyDisconnectedSpace (∀ w : D, w.val.adicCompletion F))
  obtain ⟨hl, hc⟩ := schwartzBruhat_locallyConstant_compactSupport (finitePlaceProduct_compact_subset_subgroup F D) g
  exact ⟨hl.comp_continuous (continuous_ofAdd.comp (newCoords v hv).continuous),
    hc.comp_homeomorph (newCoords v hv)⟩

open Classical in
/-- The product of an old test of product form and a new test at one new place `v` is a test of
product form on the enlarged stage: its factors are those of the old test at the old places and a
factor `φ` at `v`, which only depends on the new test. -/
theorem sAdeleDifferenceSchwartz_insert_pure {S : Finset V} (v : V) (hv : v ∉ S)
    (e : InductiveTensor B(S) Y(insert v S \ S) ≃L[ℂ] B(insert v S))
    (he : ∀ (f : B(S)) (g : Y(insert v S \ S)) (z : SAdeleRing F (insert v S)),
      e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
        f (Multiplicative.ofAdd (z.1, fun w : S ↦
          z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
        g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦
          z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)))
    (g : Y(insert v S \ S)) :
    ∃ φ : SchwartzBruhat (Multiplicative (v.adicCompletion F)),
      ∀ (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
        (b : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F)))
        (c : ∀ w : ↥(insert v S), SchwartzBruhat (Multiplicative (w.val.adicCompletion F))),
        (∀ w : S, c ⟨w.val, Finset.mem_insert_of_mem w.property⟩ = b w) →
        c ⟨v, Finset.mem_insert_self v S⟩ = φ →
        e ((sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ⊗ₜ[ℂ] g) =
          (sAdeleSchwartz_inductiveTensor_equiv F (insert v S)).choose
            (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, c w)) := by
  have witness := newTest_exists (F := F) (S := S) (v := v) hv g
  let φ := witness.choose
  have hφ := witness.choose_spec
  refine ⟨φ, fun a b c hcS hcv ↦ SchwartzBruhat.ext fun x ↦ ?_⟩
  let z := Multiplicative.toAdd x
  let wv : ↥(insert v S) := ⟨v, Finset.mem_insert_self v S⟩
  have hS := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec a b
    (z.1, fun w : S ↦ z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)
  have hT := (sAdeleSchwartz_inductiveTensor_equiv F (insert v S)).choose_spec a c z
  have hnew : (fun w : ↥(insert v S \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩) =
      newCoords v hv (z.2 wv) := by
    apply (newCoords v hv).symm.injective
    rw [Homeomorph.symm_apply_apply]
    rfl
  have hprod := prod_subtype_insert S v hv (fun w ↦ c w (Multiplicative.ofAdd (z.2 w)))
  have hcSv (w : S) : c ⟨w.val, Finset.mem_insert_of_mem w.property⟩
      (Multiplicative.ofAdd (z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) =
        b w (Multiplicative.ofAdd (z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) := by
    rw [hcS w]
  have hcvv : c wv (Multiplicative.ofAdd (z.2 wv)) = φ (Multiplicative.ofAdd (z.2 wv)) := by
    rw [hcv]
  rw [Finset.prod_congr rfl fun w _ ↦ hcSv w, hcvv, hφ, ← hnew] at hprod
  refine (he _ g z).trans ?_
  refine Eq.trans ?_ hT.symm
  rw [hS, ← hprod, mul_assoc]

/-- The dilation difference vanishes near zero. Its Haar averages are constant on valuation
shells and are supported on the finite valuation image of a compact set. -/
private theorem shell_weights (w : V) [MeasurableSpace H(w)] [BorelSpace H(w)] (ν : Measure H(w))
    [ν.IsMulLeftInvariant] (φ : w.adicCompletion F → ℂ) (hl : IsLocallyConstant φ)
    (hc : HasCompactSupport φ) (c : (w.adicCompletion F)ˣ) :
    ∃ b : WithZero (Multiplicative ℤ) →₀ ℂ, ∀ x : w.adicCompletion F, x ≠ 0 →
      b (Valued.v x) = ∫ u : H(w), φ (x * u.val.val) - φ (c.val * (x * u.val.val)) ∂ν := by
  classical
  let K := w.adicCompletion F
  let D (x : K) := φ x - φ (c.val * x)
  let hdil := Homeomorph.mulLeft₀ c.val c.ne_zero
  have hd : HasCompactSupport D := hc.sub (hc.comp_homeomorph hdil)
  have hloc : IsLocallyConstant D := hl.comp₂ (hl.comp_continuous hdil.continuous) (· - ·)
  have hzero : 0 ∉ tsupport D := by
    have hz : D 0 = 0 := by simp [D]
    have hcl : IsClosed (support D) := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
    exact fun h ↦ (hcl.closure_eq ▸ h : 0 ∈ support D) hz
  let Z := tsupport D
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hd
  have hfinite : (Valued.v '' Z).Finite := by
    rw [image_eq_range]
    apply IsLocallyConstant.range_finite
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦
      continuous_subtype_val.continuousAt (Valued.locally_const
        ((Valuation.ne_zero_iff _).mpr fun h ↦ hzero (h ▸ x.property)))
  let β (x : K) := ∫ u : H(w), D (x * u.val.val) ∂ν
  have hinv (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) (he : Valued.v x = Valued.v y) : β x = β y := by
    let d := Units.mk0 y hy / Units.mk0 x hx
    have hmem : d ∈ H(w) := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
      (show Valued.v (y / x) = 1 by rw [map_div₀, he, div_self ((Valuation.ne_zero_iff _).mpr hy)])
    let a : H(w) := ⟨d, hmem⟩
    have heq (u : H(w)) : D (x * (a * u).val.val) = D (y * u.val.val) := by
      apply congrArg D
      change x * ((y / x) * u.val.val) = _
      rw [← mul_assoc, mul_div_cancel₀ y hx]
    exact (integral_mul_left_eq_self (μ := ν) (fun u : H(w) ↦ D (x * u.val.val)) a).symm.trans
      (integral_congr_ae (.of_forall heq))
  let b (r : WithZero (Multiplicative ℤ)) :=
    if h : ∃ x : K, x ≠ 0 ∧ Valued.v x = r then β h.choose else 0
  have hb (x : K) (hx : x ≠ 0) : b (Valued.v x) = β x := by
    have h : ∃ y : K, y ≠ 0 ∧ Valued.v y = Valued.v x := ⟨x, hx, rfl⟩
    exact (dite_eq_left h).trans (hinv _ _ h.choose_spec.1 hx h.choose_spec.2)
  have hsupport : (support b).Finite := hfinite.subset fun r hr ↦ by
    by_cases h : ∃ x : K, x ≠ 0 ∧ Valued.v x = r
    · obtain ⟨x, hx, rfl⟩ := h
      have hu : ∃ u : H(w), D (x * u.val.val) ≠ 0 := by
        by_contra! hn
        apply hr
        rw [hb x hx]
        simp [β, hn]
      obtain ⟨u, hu⟩ := hu
      refine ⟨x * u.val.val, subset_closure hu, ?_⟩
      rw [map_mul, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.property, mul_one]
    · exact (hr (dite_eq_right h)).elim
  exact ⟨Finsupp.ofSupportFinite b hsupport, hb⟩

open Set in
private theorem integral_series {ι Z P : Type*} [Countable ι] [TopologicalSpace Z]
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (ν : Measure P) [IsFiniteMeasure ν] (p : C(P, Z)) (t : ι → Z → ℂ)
    (ht : ∀ i, Continuous (t i)) (s : Z → ℂ) (hs : ∀ z, HasSum (fun i ↦ t i z) (s z))
    (hb : ∃ b : ι → ℝ, Summable b ∧ ∀ i z, z ∈ range p → ‖t i z‖ ≤ b i) :
    HasSum (fun i ↦ ∫ u, t i (p u) ∂ν) (∫ u, s (p u) ∂ν) := by
  obtain ⟨b, h, hbound⟩ := hb
  exact hasSum_integral_of_dominated_convergence (fun i _ ↦ b i)
    (fun i ↦ ((ht i).comp p.continuous).aestronglyMeasurable)
    (fun i ↦ .of_forall fun u ↦ hbound i _ ⟨u, rfl⟩) (.of_forall fun _ ↦ h)
    (integrable_const _) (.of_forall fun u ↦ hs (p u))
open Set in
/-- The compact-uniform summable bound allows integration of the theta series term by term. -/
private theorem integral_theta_series {T : Finset V} {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    (p : C(P, (SAdeleRing F T)ˣ)) (ν : Measure P) [IsFiniteMeasure ν] (f : B(T)) :
    HasSum (fun t : (T : Set V).unit F ↦ ∫ u, f (Multiplicative.ofAdd
      (adeleProjection F T (algebraMap F 𝔸[F] t.val.val) * (p u).val)) ∂ν)
      (∫ u, sLocalAdelicTheta F T f (p u) ∂ν) := by

  let D := (Set.integer (T : Set V) F)ˣ
  let d := (Units.map ((adeleProjection F T).comp (integralAdelesOutside F T).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F T).toMonoidHom)
  let term (t : D) (z : (SAdeleRing F T)ˣ) := f (Multiplicative.ofAdd ((d t * z).val))
  let e := (Set.unitEquivUnitsInteger (T : Set V) F).symm
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable D := Units.val_injective.countable
  have hbound : ∃ b : D → ℝ, Summable b ∧ ∀ i (z : (SAdeleRing F T)ˣ), z ∈ range p → ‖term i z‖ ≤ b i :=
    sLocalAdelicTheta_exists_summable_bound F T f (range p) (isCompact_range p.continuous)
  have ht (t : D) : Continuous (term t) := (continuous_schwartzBruhat_apply f).comp
    (continuous_ofAdd.comp (Units.continuous_val.comp (continuous_const.mul continuous_id)))
  have hsum (z : (SAdeleRing F T)ˣ) : HasSum (fun i : D ↦ term i z) (sLocalAdelicTheta F T f z) :=
    (sLocalAdelicTheta_hasSumUniformlyOn F T f {z} isCompact_singleton).hasSum rfl
  have h := integral_series (ι := D) ν p term ht (sLocalAdelicTheta F T f) hsum hbound
  let a (i : (T : Set V).unit F) := ∫ u, f (Multiplicative.ofAdd
      (adeleProjection F T (algebraMap F 𝔸[F] i.val.val) * (p u).val)) ∂ν
  change HasSum a _
  apply (e.toEquiv.hasSum_iff (f := a)).mp
  exact h

private theorem integral_pair_hasSum {P I : Type*} [TopologicalSpace P] [CompactSpace P]
    [MeasurableSpace P] [BorelSpace P] (ν : Measure P) [IsFiniteMeasure ν]
    (t₀ t₁ : I → C(P, ℂ)) (s₀ s₁ : C(P, ℂ))
    (h₀ : HasSum (fun i ↦ ∫ u, t₀ i u ∂ν) (∫ u, s₀ u ∂ν))
    (h₁ : HasSum (fun i ↦ ∫ u, t₁ i u ∂ν) (∫ u, s₁ u ∂ν)) :
    HasSum (fun i ↦ ∫ u, t₀ i u - t₁ i u ∂ν) (∫ u, s₀ u - s₁ u ∂ν) := by
  have hi (f : C(P, ℂ)) : Integrable f ν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (hi s₀) (hi s₁)]
  exact (h₀.sub h₁).congr_fun fun i ↦ integral_sub (hi (t₀ i)) (hi (t₁ i))

private def scalarReadings {A B U : Type*} [TopologicalSpace B] [TopologicalSpace U]
    [MeasurableSpace U] [BorelSpace U] [CompactSpace U] (ν : Measure U) [IsFiniteMeasure ν]
    (p₀ p₁ : A → C(U, B)) : C(B, ℂ) →ₗ[ℂ] (A → ℂ) := by
  let d (z : C(B, ℂ)) (a : A) : C(U, ℂ) := z.comp (p₀ a) - z.comp (p₁ a)
  have hi (z a) : Integrable (d z a) ν := (d z a).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  refine { toFun z a := ∫ u, d z a u ∂ν, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    funext a
    refine (integral_congr_ae (.of_forall (fun u ↦ ?_))).trans (integral_add (hi x a) (hi y a))
    simp only [d, ContinuousMap.sub_apply, ContinuousMap.comp_apply, ContinuousMap.add_apply]
    abel
  · intro c x
    funext a
    refine (integral_congr_ae (.of_forall (fun u ↦ ?_))).trans (integral_smul c (d x a))
    simp [d, mul_sub]

private def quotientReadings {Y B A : Type*} [TopologicalSpace B] [AddCommGroup Y] [Module ℂ Y]
    (θ : Y →ₗ[ℂ] C(B, ℂ)) (sample : C(B, ℂ) →ₗ[ℂ] (A → ℂ)) := sample.comp (θ.ker.liftQ θ le_rfl)

/-- Evaluate a larger theta class at the old idele and average the difference between two
adjacent shells at the new place. -/
private def unitCut {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] :
    Q(insert v S) →ₗ[ℂ] ((SAdeleRing F S)ˣ → ℂ) := by
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let T := insert v S
  let p₀ (x : (SAdeleRing F S)ˣ) : C(H(v), (SAdeleRing F T)ˣ) :=
    (onePlaceIdele S v x).comp ⟨Subtype.val, continuous_subtype_val⟩
  let p₁ (x : (SAdeleRing F S)ˣ) : C(H(v), (SAdeleRing F T)ˣ) :=
    (onePlaceIdele S v x).comp ⟨fun u ↦ c * u.val, continuous_const.mul continuous_subtype_val⟩
  let read := scalarReadings (A := (SAdeleRing F S)ˣ) (B := (SAdeleRing F T)ˣ) (U := H(v)) ν p₀ p₁
  let L := quotientReadings (Y := B(T)) (B := (SAdeleRing F T)ˣ) (A := (SAdeleRing F S)ˣ)
    (sLocalAdelicTheta F T) read
  with_reducible_and_instances exact L

private theorem unitCut_mk {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(insert v S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let a := onePlaceIdele S v x
    unitCut (S := S) (F := F) v c ν (localClass (F := F) (insert v S) f) x =
      ∫ u : H(v), sLocalAdelicTheta F T f (a u.val) - sLocalAdelicTheta F T f (a (c * u.val)) ∂ν := rfl

private theorem sum_value {I : Type*} {f : I → ℂ} {x y : ℂ} (h : HasSum f x) (e : y = x) : HasSum f y := e.symm ▸ h

open Set in
private theorem pair_theta_sum {T : Finset V} {P : Type*}
    [TopologicalSpace P] [CompactSpace P] [MeasurableSpace P] [BorelSpace P]
    (ν : Measure P) [IsFiniteMeasure ν] (f : B(T)) (p₀ p₁ : C(P, (SAdeleRing F T)ˣ)) :
    let d (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
    HasSum (fun t ↦ ∫ u, f (Multiplicative.ofAdd (d t * (p₀ u).val)) -
      f (Multiplicative.ofAdd (d t * (p₁ u).val)) ∂ν)
      (∫ u, sLocalAdelicTheta F T f (p₀ u) - sLocalAdelicTheta F T f (p₁ u) ∂ν) := by
  let s (p : C(P, (SAdeleRing F T)ˣ)) := (sLocalAdelicTheta F T f).comp p
  let val (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
  let t (p : C(P, (SAdeleRing F T)ˣ)) (ξ : (T : Set V).unit F) : C(P, ℂ) :=
    ⟨fun u ↦ f (Multiplicative.ofAdd (val ξ * (p u).val)), (continuous_schwartzBruhat_apply f).comp
      (continuous_ofAdd.comp (continuous_const.mul (Units.continuous_val.comp p.continuous)))⟩
  have hs (p : C(P, (SAdeleRing F T)ˣ)) :
      HasSum (fun ξ ↦ ∫ u, t p ξ u ∂ν) (∫ u, s p u ∂ν) := integral_theta_series (F := F) (T := T) p ν f
  have result := integral_pair_hasSum ν (t p₀) (t p₁) (s p₀) (s p₁) (hs p₀) (hs p₁)
  exact result

open Set in
private theorem cut_hasSum {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(insert v S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let a := onePlaceIdele S v x
    let d (t : (T : Set V).unit F) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val)
    HasSum (fun t : (T : Set V).unit F ↦ ∫ u : H(v),
      f (Multiplicative.ofAdd (d t * (a u.val).val)) -
      f (Multiplicative.ofAdd (d t * (a (c * u.val)).val)) ∂ν)
      (unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) f) x) := by
  let T := insert v S
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j := onePlaceIdele S v x
  let p₀ : C(H(v), (SAdeleRing F T)ˣ) := j.comp ⟨Subtype.val, continuous_subtype_val⟩
  let p₁ : C(H(v), (SAdeleRing F T)ˣ) := j.comp ⟨fun u ↦ c * u.val, continuous_const.mul continuous_subtype_val⟩
  have result := pair_theta_sum (F := F) (T := T) ν f p₀ p₁
  have he := unitCut_mk (F := F) (S := S) v c ν f x
  have out := sum_value result he
  exact out

private theorem weighted_slices {G I X Q A : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (H : Set G) (v : G → I) (val : X → A → G → ℂ) (ev : Q →ₗ[ℂ] (A → ℂ))
    (M : Submodule ℂ (X →L[ℂ] Q))
    (hs : ∀ i : I, ∃ L ∈ M, ∀ f a, HasSum
      (({t | t ∈ H ∧ v t = i} : Set G).indicator (val f a)) (ev (L f) a))
    (b : I →₀ ℂ) : ∃ L ∈ M, ∀ f a, HasSum
      (H.indicator (fun t ↦ b (v t) * val f a t)) (ev (L f) a) := by
  induction b using Finsupp.induction_linear with
  | zero => exact ⟨0, M.zero_mem, fun f a ↦ by simp⟩
  | add b d hb hd =>
    obtain ⟨L, hLM, hL⟩ := hb
    obtain ⟨N, hNM, hM⟩ := hd
    refine ⟨L + N, M.add_mem hLM hNM, fun f a ↦ ?_⟩
    simp only [add_apply, map_add, Pi.add_apply]
    exact ((hL f a).add (hM f a)).congr_fun fun t ↦ by by_cases h : t ∈ H <;> simp [h, add_mul]
  | single i c =>
    obtain ⟨L, hLM, hL⟩ := hs i
    refine ⟨c • L, M.smul_mem c hLM, fun f a ↦ ?_⟩
    simp only [smul_apply, map_smul, Pi.smul_apply]
    exact ((hL f a).const_smul c).congr_fun fun t ↦ by
      by_cases h : t ∈ H <;> by_cases he : v t = i <;> simp [h, he, Ne.symm, eq_comm, Finsupp.single_apply, smul_eq_mul]

private def translationCLM {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (u : Rˣ) (hc : Continuous (schwartzBruhatUnitTranslate u)) :
    SchwartzBruhat (Multiplicative R) →L[ℂ] SchwartzBruhat (Multiplicative R) :=
  ⟨unitTranslateEnd (R := R) u, hc⟩

private theorem eval_translate_slice {S : Finset V} (g : (SAdeleRing F S)ˣ) :
    ∃ L : B(S) →L[ℂ] Q(S),
      (∀ f, L f = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g⁻¹ f)) ∧
      ∀ f a, localValues F S (L f) a = sLocalAdelicTheta F S f (g * a) := by
  have hc : Continuous (schwartzBruhatUnitTranslate (R := SAdeleRing F S) g⁻¹) :=
    (local_unit_joint (F := F) (S := S)).comp (continuous_const.prodMk continuous_id)
  let tr := translationCLM (R := SAdeleRing F S) g⁻¹ hc
  let L := (K(S)).mkQL.comp tr
  refine ⟨L, fun f ↦ rfl, fun f a ↦ ?_⟩
  change sLocalAdelicTheta F S (schwartzBruhatUnitTranslate g⁻¹ f) a = _
  exact (localTheta_translate_apply (F := F) (S := S) g⁻¹ a f).trans
    (congrArg (fun t ↦ sLocalAdelicTheta F S f (t * a)) (inv_inv g))

private theorem old_mem_iff {S : Finset V} (v : V) (hv : v ∉ S) (t : Fˣ) :
    t ∈ (S : Set V).unit F ↔ t ∈ ((insert v S : Finset V) : Set V).unit F ∧ v.valuation F t.val = 1 := by
  refine ⟨fun h ↦ ⟨fun w hw ↦ h w (fun hs ↦ hw (Finset.mem_insert_of_mem hs)), h v hv⟩, ?_⟩
  intro ⟨h, he⟩ w hw
  by_cases eq : w = v
  · exact eq ▸ he
  · exact h w fun ht ↦ (Finset.mem_insert.mp ht).elim eq hw

private theorem value_unit_eq_one {G M : Type*} [Monoid G] [Monoid M] (v : G →* M) (t : Gˣ) :
    v t.val = 1 ↔ Units.map v t = 1 := ⟨fun h ↦ Units.ext h, fun h ↦ congrArg Units.val h⟩

/-- Each occupied valuation fiber is a translate of the old unit group. Take the finite
linear combination of the corresponding continuous translation operators. -/
private theorem weighted_translation_slices {G I A X Z : Type*} [CommGroup G] [Group I] [Group A]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
    (J H : Subgroup G) (i : G →* I) (d : G →* A) (φ θ : X → A → ℂ) (ev : Z →ₗ[ℂ] (A → ℂ))
    (hh : ∀ t, t ∈ H ↔ t ∈ J ∧ i t = 1)
    (sum : ∀ f a, HasSum (fun u : H ↦ φ f (d u.val * a)) (θ f a))
    (M : Submodule ℂ (X →L[ℂ] Z))
    (tr : ∀ g : A, ∃ L ∈ M, ∀ f a, ev (L f) a = θ f (g * a)) (b : I →₀ ℂ) :
    ∃ L ∈ M, ∀ f a, HasSum (fun t : J ↦ b (i t.val) * φ f (d t.val * a)) (ev (L f) a) := by
  let val (f : X) (a : A) (t : G) := φ f (d t * a)
  have hs (k : I) : ∃ L ∈ M, ∀ f a,
      HasSum (({t : G | t ∈ J ∧ i t = k} : Set G).indicator (val f a)) (ev (L f) a) := by
    obtain ⟨y, hy⟩ := exists_translate_fiber J H i d φ θ hh sum k
    cases y with
    | none =>
      refine ⟨0, M.zero_mem, fun f a ↦ ?_⟩
      rw [zero_apply, ev.map_zero]
      exact hy f a
    | some g =>
      obtain ⟨L, hLM, hL⟩ := tr g
      refine ⟨L, hLM, fun f a ↦ ?_⟩
      rw [hL]
      exact hy f a
  obtain ⟨L, hLM, hL⟩ := weighted_slices (J : Set G) i val ev M hs b
  exact ⟨L, hLM, fun f a ↦ hasSum_subtype_iff_indicator.mpr (hL f a)⟩

private theorem weighted_theta_slice {S : Finset V} (w : V) (hw : w ∉ S) (b : WithZero (Multiplicative ℤ) →₀ ℂ)
    (M : Submodule ℂ (B(S) →L[ℂ] Q(S)))
    (hM : ∀ (L : B(S) →L[ℂ] Q(S)) (g : (SAdeleRing F S)ˣ),
      (∀ f, L f = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f)) → L ∈ M) :
    let T := insert w S
    ∃ L ∈ M, ∀ (f : B(S)) (x : (SAdeleRing F S)ˣ),
      HasSum (fun t : (T : Set V).unit F ↦ b (w.valuation F t.val.val) *
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val)))
        (localValues F S (L f) x) := by
  let T := insert w S
  let J := (T : Set V).unit F
  let H := (S : Set V).unit F
  let i := Units.map (w.valuation F).toMonoidHom
  let d := Units.map ((adeleProjection F S).toMonoidHom.comp (algebraMap F 𝔸[F]).toMonoidHom)
  let φ (f : B(S)) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd x.val)
  let ev := localValues F S
  let θ (f : B(S)) (x : (SAdeleRing F S)ˣ) := sLocalAdelicTheta F S f x
  have hh (t : Fˣ) : t ∈ H ↔ t ∈ J ∧ i t = 1 := (old_mem_iff (F := F) (S := S) w hw t).trans
    (and_congr_right' (value_unit_eq_one (w.valuation F).toMonoidHom t))
  let coeff := b.comapDomain Units.val Units.val_injective.injOn
  have res := weighted_translation_slices (G := Fˣ) (I := (WithZero (Multiplicative ℤ))ˣ)
    (A := (SAdeleRing F S)ˣ) (X := B(S)) (Z := Q(S))
    J H i d φ θ ev hh (localTheta_unit_hasSum (F := F) S) M (fun g ↦
      (eval_translate_slice (F := F) (S := S) g).imp fun L hL ↦ ⟨hM L g⁻¹ hL.1, hL.2⟩) coeff
  obtain ⟨L, hLM, hL⟩ := res
  refine ⟨L, hLM, fun f x ↦ ?_⟩
  exact hL f x

private theorem shell_integral_mul {U : Type*} [MeasurableSpace U] (ν : Measure U)
    (a b : ℂ) (g₀ g₁ t₀ t₁ : U → ℂ) (h₀ : ∀ u, t₀ u = a * g₀ u)
    (h₁ : ∀ u, t₁ u = a * g₁ u) (hb : b = ∫ u, g₀ u - g₁ u ∂ν) :
    b * a = ∫ u, t₀ u - t₁ u ∂ν := by
  symm
  calc
    _ = ∫ u, a * (g₀ u - g₁ u) ∂ν := integral_congr_ae (.of_forall fun u ↦ (congrArg₂ (· - ·) (h₀ u) (h₁ u)).trans (mul_sub _ _ _).symm)
    _ = _ := (integral_const_mul (μ := ν) a (fun u ↦ g₀ u - g₁ u)).trans ((congrArg (a * ·) hb.symm).trans (mul_comm _ _))

private theorem cut_term_of_product {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] (ν : Measure H(v)) (f : B(S))
    (k : B(insert v S)) (ψ : v.adicCompletion F → ℂ)
    (x : (SAdeleRing F S)ˣ) (t : Fˣ)
    (eval : ∀ (u : (v.adicCompletion F)ˣ),
      k (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val))
    (b : WithZero (Multiplicative ℤ) →₀ ℂ) (hb : ∀ y : v.adicCompletion F, y ≠ 0 →
      b (Valued.v y) = ∫ u : H(v), ψ (y * u.val.val) - ψ (c.val * (y * u.val.val)) ∂ν)
    :
    let T := insert v S
    let a := onePlaceIdele S v x
    let z (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
    let v₀ := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
    b (v.valuation F t.val) * v₀ = ∫ u : H(v),
      k (Multiplicative.ofAdd (z u.val)) - k (Multiplicative.ofAdd (z (c * u.val))) ∂ν := by
  let T := insert v S
  let a := onePlaceIdele S v x
  let z (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
  let w := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  let y := algebraMap F (v.adicCompletion F) t.val
  let g₀ (u : H(v)) := ψ (y * u.val.val)
  let g₁ (u : H(v)) := ψ (c.val * (y * u.val.val))
  let t₀ (u : H(v)) := k (Multiplicative.ofAdd (z u.val))
  let t₁ (u : H(v)) := k (Multiplicative.ofAdd (z (c * u.val)))
  have h₁ (u : H(v)) : t₁ u = w * g₁ u := (eval (c * u.val)).trans
    (congrArg (fun q ↦ w * ψ q) (mul_left_comm y c.val u.val.val))
  have hy : y ≠ 0 := (map_ne_zero (algebraMap F (v.adicCompletion F))).mpr t.ne_zero
  have heval : Valued.v y = v.valuation F t.val := v.valuedAdicCompletion_eq_valuation' t.val
  have weight := hb y hy
  rw [heval] at weight
  have h := shell_integral_mul ν w (b (v.valuation F t.val)) g₀ g₁ t₀ t₁
    (fun u ↦ eval u.val) h₁ weight
  with_reducible_and_instances exact h

private theorem sums_agree {I : Type*} {w z : I → ℂ} {a b : ℂ}
    (h₁ : HasSum w a) (h₂ : HasSum z b) (eq : ∀ t, w t = z t) : a = b :=
  h₁.unique (h₂.congr_fun eq)

private theorem cut_value_of_product {S : Finset V} (v : V) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν]
    (f : B(S)) (k : B(insert v S)) (x : (SAdeleRing F S)ˣ) (ψ : v.adicCompletion F → ℂ)
    (eval : ∀ (t : Fˣ) (u : (v.adicCompletion F)ˣ),
      k (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val))
    (b : WithZero (Multiplicative ℤ) →₀ ℂ)
    (hb : ∀ y : v.adicCompletion F, y ≠ 0 → b (Valued.v y) =
      ∫ u : H(v), ψ (y * u.val.val) - ψ (c.val * (y * u.val.val)) ∂ν)
    (value : ℂ) (hval : HasSum (fun t : ((insert v S : Finset V) : Set V).unit F ↦
      b (v.valuation F t.val.val) * f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val))) value) :
    value = unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) k) x := by
  let T := insert v S
  have h := cut_hasSum (F := F) (S := S) v c ν k x
  have term (t : (T : Set V).unit F) := cut_term_of_product (F := F) (S := S) v c ν f k ψ x t.val (eval t.val) b hb
  with_reducible_and_instances exact sums_agree hval h term

private theorem slice_of_product {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
    (k : B(S) → B(insert v S)) (ψ : v.adicCompletion F → ℂ) (hl : IsLocallyConstant ψ) (hp : HasCompactSupport ψ)
    (eval : ∀ (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : Fˣ) (u : (v.adicCompletion F)ˣ),
      k f (Multiplicative.ofAdd (adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val)) =
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) *
          ψ (algebraMap F (v.adicCompletion F) t.val * u.val))
    (M : Submodule ℂ (B(S) →L[ℂ] Q(S)))
    (hM : ∀ (L : B(S) →L[ℂ] Q(S)) (g : (SAdeleRing F S)ˣ),
      (∀ f, L f = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f)) → L ∈ M) :
    ∃ L ∈ M, ∀ f, localValues F S (L f) =
      unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (k f)) := by
  have W := shell_weights (F := F) v ν ψ hl hp c
  let b := W.choose
  obtain ⟨L, hLM, hL⟩ := weighted_theta_slice (F := F) (S := S) v hv b M hM
  have eq (f : B(S)) (x : (SAdeleRing F S)ˣ) := cut_value_of_product (F := F) (S := S)
    v c ν f (k f) x ψ (eval f x) b W.choose_spec (localValues F S (L f) x) (hL f x)
  exact ⟨L, hLM, fun f ↦ funext (eq f)⟩

/-- On a pure tensor, the scalar cut is the old theta transform of a finite sum of
translates. The operator on old tests is continuous for each fixed new test. -/
private theorem unitCut_tensor_slice {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]
    (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S))))
    (k : B(S) → B(insert v S))
    (hk : ∀ (f : B(S)) (z : SAdeleRing F (insert v S)), k f (Multiplicative.ofAdd z) =
      f (Multiplicative.ofAdd (z.1, fun w : S ↦ z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
      g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)))
    (M : Submodule ℂ (B(S) →L[ℂ] Q(S)))
    (hM : ∀ (L : B(S) →L[ℂ] Q(S)) (g : (SAdeleRing F S)ˣ),
      (∀ f, L f = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f)) → L ∈ M) :
    ∃ L ∈ M, ∀ f, localValues F S (L f) =
      unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (k f)) := by
  have witness := newTest_exists (F := F) (S := S) (v := v) hv g
  let φ := witness.choose
  have hφ := witness.choose_spec
  let ψ (y : v.adicCompletion F) := φ (Multiplicative.ofAdd y)
  have hp := (mem_finitePlaceSchwartz_iff F v ψ).mp ⟨φ, fun _ ↦ rfl⟩
  refine slice_of_product (F := F) (S := S) v hv c ν k ψ hp.1 hp.2 ?_ M hM
  intro f x t u
  let z : SAdeleRing F (insert v S) := adeleProjection F (insert v S) (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
  have h₀ := congrArg (fun q : SAdeleRing F S ↦ f (Multiplicative.ofAdd q))
    (coordinates_old (F := F) (S := S) (v := v) hv x u t)
  have h₁ := congrArg (fun q : FinitePlaceProduct F (insert v S \ S) ↦ g (Multiplicative.ofAdd q))
    (coordinates_new (F := F) (S := S) (v := v) hv x u t)
  have h' := h₁.trans (hφ (algebraMap F (v.adicCompletion F) t.val * u.val)).symm
  have H := (hk f z).trans (congrArg₂ (fun a b : ℂ ↦ a * b) h₀ h')
  exact H

private theorem strict_shell {r : WithZero (Multiplicative ℤ)} (h : r ≠ 0) :
    r * WithZero.exp (1 : ℤ) ≤ 1 ↔ r < 1 := by
  rw [← WithZero.exp_log h, ← WithZero.exp_add]
  simp only [WithZero.exp_le_one_iff, WithZero.exp_lt_one_iff]
  omega

private theorem forall_new_iff {α : Type*} [DecidableEq α] (S : Finset α) (v : α) (hv : v ∉ S)
    (P : ↥(insert v S) → Prop) : (∀ w : ↥(insert v S), w.val ∉ S → P w) ↔ P ⟨v, Finset.mem_insert_self v S⟩ := by
  refine ⟨fun h ↦ h ⟨v, Finset.mem_insert_self v S⟩ hv, fun h w hw ↦ ?_⟩
  have eq : w = ⟨v, Finset.mem_insert_self v S⟩ := Subtype.ext ((Finset.mem_insert.mp w.property).resolve_right hw)
  exact eq.symm ▸ h

private theorem last_coordinate {S : Finset V} (v : V)
    (x : (SAdeleRing F S)ˣ) (u : (v.adicCompletion F)ˣ) (t : Fˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    z.2 ⟨v, Finset.mem_insert_self _ _⟩ = algebraMap F (v.adicCompletion F) t.val * u.val := by
  let w' : ↥(insert v S) := ⟨v, Finset.mem_insert_self _ _⟩
  have h : (newUnits S v x u w').val = u.val := by
    simp only [newUnits, show w'.val = v from rfl, dite_true]
    rfl
  exact congrArg ((algebraMap F (v.adicCompletion F) t.val) * ·) h

open Set in
private theorem inserted_test_value {S : Finset V} (v : V) (hv : v ∉ S)
    (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : Fˣ) (u : (v.adicCompletion F)ˣ) :
    let T := insert v S
    let z := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (onePlaceIdele S v x u).val
    sAdeleSchwartzTransition F (Finset.subset_insert v S) f (Multiplicative.ofAdd z) =
      if v.valuation F t.val * Valued.v u.val ≤ 1 then
        f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val)) else 0 := by
  let T := insert v S
  let h := Finset.subset_insert v S
  let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  let a := onePlaceIdele S v x
  let z (t : Fˣ) (u : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val) * (a u).val
  have integral_iff (p : SAdeleRing F T) : (∀ w : T, w.val ∉ S → p.2 w ∈ w.val.adicCompletionIntegers F) ↔
      p.2 ⟨v, Finset.mem_insert_self _ _⟩ ∈ v.adicCompletionIntegers F :=
    forall_new_iff S v hv (fun w ↦ p.2 w ∈ w.val.adicCompletionIntegers F)
  have hnew := last_coordinate (F := F) (S := S) v x u t
  have hcond : (∀ w : T, w.val ∉ S → (z t u).2 w ∈ w.val.adicCompletionIntegers F) ↔
      v.valuation F t.val * Valued.v u.val ≤ 1 := by
    refine (integral_iff _).trans ?_
    change Valued.v ((z t u).2 ⟨v, Finset.mem_insert_self _ _⟩) ≤ 1 ↔ _
    change (z t u).2 ⟨v, Finset.mem_insert_self _ _⟩ = _ at hnew
    have he : Valued.v (algebraMap F (v.adicCompletion F) t.val) = v.valuation F t.val :=
      v.valuedAdicCompletion_eq_valuation' t.val
    rw [hnew, map_mul, he]
  exact (sAdeleSchwartzTransition_apply F h f _).trans (if_congr hcond
    (congrArg (fun q ↦ f (Multiplicative.ofAdd q)) (coordinates_old (F := F) (S := S) (v := v) hv x u t)) rfl)

private theorem shell_indicator_difference (q r r' : WithZero (Multiplicative ℤ)) (a : ℂ)
    (P : Prop) [Decidable P] (hq : q ≠ 0) (hr : r = 1) (hr' : r' = WithZero.exp (1 : ℤ))
    (hP : P ↔ q = 1) : (if q * r ≤ 1 then a else 0) - (if q * r' ≤ 1 then a else 0) =
      if P then a else 0 := by
  simp only [hr, hr', mul_one, strict_shell hq, hP]
  rcases lt_trichotomy q 1 with h | h | h
  · simp [h.le, h, h.ne]
  · simp [h]
  · simp [h.not_ge, h.not_gt, h.ne']

private theorem integral_const_value {U : Type*} [MeasurableSpace U] (ν : Measure U) [IsProbabilityMeasure ν]
    (f : U → ℂ) (b : ℂ) (hf : ∀ u, f u = b) : b = ∫ u, f u ∂ν := by
  rw [funext hf]
  simp

private def insertedTest (S : Finset V) (v : V) (f : B(S)) : B(insert v S) :=
  sAdeleSchwartzTransition F (Finset.subset_insert v S) f

private theorem inserted_term_difference {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    (f : B(S)) (x : (SAdeleRing F S)ˣ) (t : ((insert v S : Finset V) : Set V).unit F) (u : H(v)) :
    let T := insert v S
    let a := onePlaceIdele S v x
    let z (q : (v.adicCompletion F)ˣ) := adeleProjection F T (algebraMap F 𝔸[F] t.val.val) * (a q).val
    let val := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val))
    let g := insertedTest (F := F) S v f
    g (Multiplicative.ofAdd (z u.val)) - g (Multiplicative.ofAdd (z (c * u.val))) =
      if t.val ∈ (S : Set V).unit F then val else 0 := by
  let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  have hu : Valued.v u.val.val = 1 := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.property
  have ht : v.valuation F t.val.val ≠ 0 := (Valuation.ne_zero_iff _).mpr t.val.ne_zero
  have e₀ := inserted_test_value (F := F) (S := S) v hv f x t.val u.val
  have e₁ := inserted_test_value (F := F) (S := S) v hv f x t.val (c * u.val)
  have hcu : Valued.v (c * u.val).val = WithZero.exp (1 : ℤ) := by
    rw [Units.val_mul, map_mul, hu, mul_one, hc]
  have hh : t.val ∈ (S : Set V).unit F ↔ v.valuation F t.val.val = 1 :=
    (old_mem_iff (F := F) (S := S) v hv t.val).trans (and_iff_right t.property)
  have result := shell_indicator_difference _ _ _ (val t.val) _ ht hu hcu hh
  exact (congrArg₂ (· - ·) e₀ e₁).trans result

open Set in
/-- For the inserted integer-ring indicator, only the terms whose new component is a unit survive. -/
private theorem unitCut_hasSum_inserted {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν]
    (f : B(S)) (x : (SAdeleRing F S)ˣ) :
    let T := insert v S
    let val (t : Fˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
    HasSum (fun t : (T : Set V).unit F ↦ if t.val ∈ (S : Set V).unit F then val t.val else 0)
      (unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (insertedTest (F := F) S v f)) x) := by
  let T := insert v S
  let g := insertedTest (F := F) S v f
  let w (t : (T : Set V).unit F) := if t.val ∈ (S : Set V).unit F then
    f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val.val) * x.val)) else 0
  have eq (t : (T : Set V).unit F) := integral_const_value ν _ (w t)
    (inserted_term_difference (F := F) (S := S) v hv c hc f x t)
  have h := (cut_hasSum (F := F) (S := S) v c ν g x).congr_fun (g := w) eq
  exact h

private theorem extend_subtype_sum {A : Type*} {J H : Set A} (hj : H ⊆ J)
    (f : A → ℂ) {z : ℂ} (h : HasSum (H.indicator f) z) :
    HasSum (fun t : J ↦ if t.val ∈ H then f t.val else 0) z := by
  apply (hasSum_subtype_iff_indicator (f := fun a : A ↦ if a ∈ H then f a else 0) (s := J)).mpr
  refine h.congr_fun fun t ↦ ?_
  by_cases ht : t ∈ H
  · simp [ht, hj ht]
  · by_cases hJ : t ∈ J <;> simp [ht, hJ]

open Set in
private theorem unitCut_section {S : Finset V} (v : V) (hv : v ∉ S) (c : (v.adicCompletion F)ˣ)
    (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] (f : B(S)) :
    unitCut (F := F) (S := S) v c ν (localClass (F := F) (insert v S) (insertedTest (F := F) S v f)) =
      ⇑(sLocalAdelicTheta F S f) := by
  let T := insert v S
  let val (t : Fˣ) (x : (SAdeleRing F S)ˣ) := f (Multiplicative.ofAdd (adeleProjection F S (algebraMap F 𝔸[F] t.val) * x.val))
  funext x
  apply (unitCut_hasSum_inserted (F := F) (S := S) v hv c hc ν f x).unique
  have hi : ((S : Set V).unit F : Set Fˣ) ⊆ ((T : Set V).unit F : Set Fˣ) :=
    fun {t} ht ↦ ((old_mem_iff (F := F) (S := S) v hv t).mp ht).1
  have result := extend_subtype_sum hi (fun t ↦ val t x) (localTheta_indicator_hasSum (F := F) S f x)
  with_reducible_and_instances exact result

private theorem cut_retraction_for_equiv {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    (e : InductiveTensor B(S) (SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S)))) ≃L[ℂ] B(insert v S))
    (he : ∀ (f : B(S)) (g : SchwartzBruhat (Multiplicative (FinitePlaceProduct F (insert v S \ S))))
      (z : SAdeleRing F (insert v S)), e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
        f (Multiplicative.ofAdd (z.1, fun w : S ↦ z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
        g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦ z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩))) :
    ∃ r : Q(insert v S) →L[ℂ] Q(S),
      LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) ∧
      ∀ (A : B(S) →ₗ[ℂ] B(S)) (A' : Q(S) →ₗ[ℂ] Q(S)),
        (∀ f, A' (Submodule.Quotient.mk f) = Submodule.Quotient.mk (A f)) →
        (∀ (γ : (SAdeleRing F S)ˣ) (f : B(S)),
          (Submodule.Quotient.mk (A (schwartzBruhatUnitTranslate γ f)) : Q(S)) =
            Submodule.Quotient.mk (schwartzBruhatUnitTranslate γ (A f))) →
        ∀ (f : B(S)) (g : Y(insert v S \ S)),
          r (Submodule.Quotient.mk (e (A f ⊗ₜ[ℂ] g))) =
            A' (r (Submodule.Quotient.mk (e (f ⊗ₜ[ℂ] g)))) := by
  let M : Submodule ℂ (B(S) →L[ℂ] Q(S)) :=
    { carrier := {L | ∀ (A : B(S) →ₗ[ℂ] B(S)) (A' : Q(S) →ₗ[ℂ] Q(S)),
        (∀ f, A' (Submodule.Quotient.mk f) = Submodule.Quotient.mk (A f)) →
        (∀ (γ : (SAdeleRing F S)ˣ) (f : B(S)),
          (Submodule.Quotient.mk (A (schwartzBruhatUnitTranslate γ f)) : Q(S)) =
            Submodule.Quotient.mk (schwartzBruhatUnitTranslate γ (A f))) →
        ∀ f, L (A f) = A' (L f)}
      add_mem' := fun {L N} hL hN A A' hA hT f ↦ by
        change L (A f) + N (A f) = A' (L f + N f)
        rw [map_add, hL A A' hA hT f, hN A A' hA hT f]
      zero_mem' := fun A A' _ _ f ↦ by
        change (0 : Q(S)) = A' 0
        rw [map_zero]
      smul_mem' := fun a {L} hL A A' hA hT f ↦ by
        change a • L (A f) = A' (a • L f)
        rw [map_smul, hL A A' hA hT f] }
  have hM (L : B(S) →L[ℂ] Q(S)) (g : (SAdeleRing F S)ˣ)
      (hL : ∀ f, L f = Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f)) : L ∈ M := by
    intro A A' hA hT f
    rw [hL, hL, hA, hT]
  obtain ⟨r, hr, hval⟩ : ∃ r : Q(insert v S) →L[ℂ] Q(S),
      LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) ∧
      ∀ z, localValues F S (r z) = unitCut (F := F) (S := S) v c ν z := by
    with_reducible_and_instances
      refine finiteTheta_retraction_of_classes (F := F) (S := S) (T := insert v S)
        (Finset.subset_insert v S) e (unitCut (F := F) (S := S) v c ν) ?_ ?_
    · intro g
      let k (f : B(S)) : B(insert v S) := e (f ⊗ₜ[ℂ] g)
      have eq (f : B(S)) (z : SAdeleRing F (insert v S)) := he f g z
      have h := unitCut_tensor_slice (F := F) (S := S) v hv c ν g k eq M hM
      with_reducible_and_instances exact h.imp fun L hL ↦ hL.2
    · intro f
      exact unitCut_section (F := F) (S := S) v hv c hc ν f
  refine ⟨r, hr, fun A A' hA hT f g ↦ ?_⟩
  let k (f : B(S)) : B(insert v S) := e (f ⊗ₜ[ℂ] g)
  have eq (f : B(S)) (z : SAdeleRing F (insert v S)) := he f g z
  have hs := unitCut_tensor_slice (F := F) (S := S) v hv c ν g k eq M hM
  have hrL (f' : B(S)) : r (Submodule.Quotient.mk (e (f' ⊗ₜ[ℂ] g))) = hs.choose f' :=
    testValues_injective (sLocalAdelicTheta F S) ((hval _).trans (hs.choose_spec.2 f').symm)
  have hmem : ∀ f₀, hs.choose (A f₀) = A' (hs.choose f₀) := hs.choose_spec.1 A A' hA hT
  exact (hrL (A f)).trans ((hmem f).trans (congrArg A' (hrL f).symm))

private theorem cut_retraction {S : Finset V} (v : V) (hv : v ∉ S)
    (c : (v.adicCompletion F)ˣ) (hc : Valued.v c.val = WithZero.exp (1 : ℤ))
    [MeasurableSpace H(v)] [BorelSpace H(v)] (ν : Measure H(v)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    ∃ r : Q(insert v S) →L[ℂ] Q(S),
      LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) ∧
      ∀ (e : InductiveTensor B(S) Y(insert v S \ S) ≃L[ℂ] B(insert v S)),
        (∀ (f : B(S)) (g : Y(insert v S \ S)) (z : SAdeleRing F (insert v S)),
          e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
            f (Multiplicative.ofAdd (z.1, fun w : S ↦
              z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
            g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦
              z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩))) →
      ∀ (A : B(S) →ₗ[ℂ] B(S)) (A' : Q(S) →ₗ[ℂ] Q(S)),
        (∀ f, A' (Submodule.Quotient.mk f) = Submodule.Quotient.mk (A f)) →
        (∀ (γ : (SAdeleRing F S)ˣ) (f : B(S)),
          (Submodule.Quotient.mk (A (schwartzBruhatUnitTranslate γ f)) : Q(S)) =
            Submodule.Quotient.mk (schwartzBruhatUnitTranslate γ (A f))) →
        ∀ (f : B(S)) (g : Y(insert v S \ S)),
          r (Submodule.Quotient.mk (e (A f ⊗ₜ[ℂ] g))) =
            A' (r (Submodule.Quotient.mk (e (f ⊗ₜ[ℂ] g)))) := by
  have ht := sAdeleDifferenceSchwartz_inductiveTensor_equiv (S := S) (T := insert v S) F (Finset.subset_insert v S)
  have h := cut_retraction_for_equiv (F := F) (S := S) v hv c hc ν ht.choose ht.choose_spec
  refine ⟨h.choose, h.choose_spec.1, fun e he A A' hA hT f g ↦ ?_⟩
  -- The product formula determines the inserted pure tensors.
  have heq (f' : B(S)) : e (f' ⊗ₜ[ℂ] g) = ht.choose (f' ⊗ₜ[ℂ] g) :=
    SchwartzBruhat.ext fun x ↦ (he f' g x.toAdd).trans (ht.choose_spec f' g x.toAdd).symm
  exact (congrArg (fun k ↦ h.choose (Submodule.Quotient.mk k : Q(insert v S))) (heq (A f))).trans
    ((h.choose_spec.2 A A' hA hT f g).trans
      (congrArg (fun k ↦ A' (h.choose (Submodule.Quotient.mk k : Q(insert v S)))) (heq f).symm))

private theorem exists_unit_probability (U : Type*) [CommGroup U] [TopologicalSpace U] [IsTopologicalGroup U]
    [T2Space U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U] :
    ∃ ν : Measure U, IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant := by
  let K : TopologicalSpace.PositiveCompacts U := ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩
  let ν := Measure.haarMeasure K
  exact ⟨ν, ⟨Measure.haarMeasure_self (K₀ := K)⟩, inferInstance⟩

private theorem exists_unit_cut_parameter (v : V) : ∃ c : (v.adicCompletion F)ˣ, Valued.v c.val = WithZero.exp (1 : ℤ) := by
  have h := v.valuedAdicCompletion_surjective F (WithZero.exp (1 : ℤ))
  let p := h.choose
  have hp : Valued.v p = WithZero.exp (1 : ℤ) := h.choose_spec
  have hp0 : p ≠ 0 := fun hn ↦ WithZero.exp_ne_zero (a := (1 : ℤ)) (hp.symm.trans (by rw [hn, map_zero]))
  exact ⟨Units.mk0 p hp0, hp⟩

/-- Averaging the difference of two adjacent local-unit orbits gives a continuous linear
left inverse to insertion at one new finite place. On the class of the product of an old test `f`
and a new test `g` it is a finite combination of classes of translates of `f` by S-ideles, so it
commutes with every operator on old tests that commutes with these translations on classes. -/
theorem sLocalThetaTransition_exists_leftInverse_insert_commute {S : Finset V} (v : V)
    (hv : v ∉ S) :
    ∃ r : Q(insert v S) →L[ℂ] Q(S),
      LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) ∧
      ∀ (e : InductiveTensor B(S) Y(insert v S \ S) ≃L[ℂ] B(insert v S)),
        (∀ (f : B(S)) (g : Y(insert v S \ S)) (z : SAdeleRing F (insert v S)),
          e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd z) =
            f (Multiplicative.ofAdd (z.1, fun w : S ↦
              z.2 ⟨w.val, Finset.mem_insert_of_mem w.property⟩)) *
            g (Multiplicative.ofAdd (fun w : ↥(insert v S \ S) ↦
              z.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩))) →
      ∀ (A : B(S) →ₗ[ℂ] B(S)) (A' : Q(S) →ₗ[ℂ] Q(S)),
        (∀ f, A' (Submodule.Quotient.mk f) = Submodule.Quotient.mk (A f)) →
        (∀ (γ : (SAdeleRing F S)ˣ) (f : B(S)),
          (Submodule.Quotient.mk (A (schwartzBruhatUnitTranslate γ f)) : Q(S)) =
            Submodule.Quotient.mk (schwartzBruhatUnitTranslate γ (A f))) →
        ∀ (f : B(S)) (g : Y(insert v S \ S)),
          r (Submodule.Quotient.mk (e (A f ⊗ₜ[ℂ] g))) =
            A' (r (Submodule.Quotient.mk (e (f ⊗ₜ[ℂ] g)))) := by
  let : CompactSpace H(v) := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let : MeasurableSpace H(v) := borel _
  let : BorelSpace H(v) := ⟨rfl⟩
  have hm := exists_unit_probability H(v)
  let ν := hm.choose
  let : IsProbabilityMeasure ν := hm.choose_spec.1
  let : ν.IsMulLeftInvariant := hm.choose_spec.2
  have hc := exists_unit_cut_parameter (F := F) v
  with_reducible_and_instances exact cut_retraction (F := F) (S := S) v hv hc.choose hc.choose_spec ν

/-- Averaging the difference of two adjacent local-unit orbits gives a continuous linear
left inverse to insertion at one new finite place. -/
theorem sLocalThetaTransition_exists_leftInverse_insert {S : Finset V} (v : V) (hv : v ∉ S) :
    ∃ r : Q(insert v S) →L[ℂ] Q(S), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v S)) :=
  (sLocalThetaTransition_exists_leftInverse_insert_commute (F := F) v hv).imp fun _ h ↦ h.1

private theorem embedding_of_fixed {X : Type*} [TopologicalSpace X] (f : X → X)
    (h : ∀ x, f x = x) : IsEmbedding f := by
  have hf : f = id := funext h
  rw [hf]
  exact IsEmbedding.id

private theorem self_embedding_of_comp {X Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Z] [Module ℂ Z] (i : X →ₗ[ℂ] Z) (j : X →ₗ[ℂ] X) (hi : Injective i)
    (h : i.comp j = i) : IsEmbedding j :=
  embedding_of_fixed j fun x ↦ hi (DFunLike.congr_fun h x)

private theorem insert_cases_prop {A : Type*} [DecidableEq A] (S : Finset A) (v : A)
    (P : ∀ T : Finset A, S ⊆ T → Prop) (hS : ∀ h : S ⊆ S, P S h)
    (hI : v ∉ S → P (insert v S) (Finset.subset_insert v S)) : P (insert v S) (Finset.subset_insert v S) := by
  by_cases hv : v ∈ S
  · have h (T : Finset A) (hT : T = S) (hs : S ⊆ T) : P T hs := by
      subst T
      exact hS hs
    exact h _ (Finset.insert_eq_of_mem hv) _
  · exact hI hv

private theorem embedding_of_split_linear {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (j : X →ₗ[ℂ] Y) (hc : Continuous j)
    (hs : ∃ r : Y →L[ℂ] X, LeftInverse r j) : IsEmbedding j := by
  obtain ⟨r, h⟩ := hs
  exact h.isEmbedding r.continuous hc

private theorem self_transition_embedding (T : Finset V) (h : T ⊆ T) :
    IsEmbedding (sLocalThetaTransition (F := F) (S := T) (T := T) h) := by
  with_reducible_and_instances
    exact self_embedding_of_comp (X := Q(T)) (Z := GlobalAdelicThetaSpace F)
      (sLocalThetaToGlobal F T) (sLocalThetaTransition (F := F) (S := T) (T := T) h)
      (sLocalThetaToGlobal_injective (F := F) (S := T)) (sLocalThetaToGlobal_comp (F := F) (S := T) (T := T) h)

private theorem new_transition_embedding (T : Finset V) (v : V)
    (ret : ∃ r : Q(insert v T) →L[ℂ] Q(T), LeftInverse r (sLocalThetaTransition (F := F) (Finset.subset_insert v T))) :
    IsEmbedding (sLocalThetaTransition (F := F) (Finset.subset_insert v T)) := by
  with_reducible_and_instances
    exact embedding_of_split_linear (X := Q(T)) (Y := Q(insert v T))
      (sLocalThetaTransition (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T))
      (sLocalThetaTransition_continuous (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) ret

private def stageEmb {S T : Finset V} (h : S ⊆ T) : Prop :=
  IsEmbedding (sLocalThetaTransition (F := F) (S := S) (T := T) h)

private theorem all_stage_emb (T : Finset V) (v : V) (he : v ∉ T →
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) :
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T) := by
  have hs (h : T ⊆ T) : stageEmb (F := F) (S := T) (T := T) h := self_transition_embedding (F := F) T h
  exact insert_cases_prop T v (fun U h ↦ stageEmb (F := F) (S := T) (T := U) h) hs he

private theorem stage_of_retraction (T : Finset V) (v : V)
    (ret : v ∉ T → ∃ r : Q(insert v T) →L[ℂ] Q(T), LeftInverse r (sLocalThetaTransition (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T))) :
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T) := by
  refine all_stage_emb (F := F) T v ?_
  intro hv
  unfold stageEmb
  with_reducible_and_instances exact new_transition_embedding (F := F) T v (ret hv)

private theorem global_of_stages (he : ∀ (T : Finset V) (v : V),
    stageEmb (F := F) (S := T) (T := insert v T) (Finset.subset_insert v T)) (S : Finset V) :
    IsEmbedding (sLocalThetaToGlobal F S) := by
  refine sLocalThetaToGlobal_isEmbedding_of_insert (F := F) (fun T v ↦ ?_) S
  exact he T v

private theorem global_embedding_from_cut (S : Finset V) : IsEmbedding (sLocalThetaToGlobal F S) := by
  refine global_of_stages (F := F) (fun T v ↦ ?_) S
  exact stage_of_retraction (F := F) T v (sLocalThetaTransition_exists_leftInverse_insert (F := F) (S := T) v)

end OnePlaceRetraction

/-- Paper: Theorem 5.2.1.1(3), p. 230.
The S-local theta space embeds topologically in the global theta space. -/
theorem sLocalThetaToGlobal_isEmbedding : IsEmbedding (sLocalThetaToGlobal F S) :=
  global_embedding_from_cut (F := F) S

/-- Paper: Theorem 5.2.1.1(3), p. 231.
The global stage insertion has closed range, as used in Lemma 5.3.1.5. -/
theorem sLocalThetaToGlobal_isClosed_range :
    IsClosed (Set.range (sLocalThetaToGlobal F S)) := by
  let : UniformSpace (Θₛ(S)) := IsTopologicalAddGroup.rightUniformSpace _
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Θₛ(S)) := isUniformAddGroup_of_addCommGroup
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace (Θₛ(S)) := sLocalAdelicThetaSpace_complete
  let : T2Space Θ𝔽 := (globalAdelicThetaSpace_lf (F := F)).1
  exact (AddMonoidHom.isUniformInducing_of_isInducing
    (sLocalThetaToGlobal_isEmbedding (F := F) (S := S)).isInducing).isComplete_range.isClosed

/-- Paper: Theorem 5.2.1.1(2), p. 230.
The transition on theta quotients embeds each stage as a closed subspace of a larger stage. -/
theorem sLocalThetaTransition_isClosedEmbedding (hST : S ⊆ T) :
    IsClosedEmbedding (sLocalThetaTransition (F := F) hST) :=
  closedEmbedding_of_linear_comp (sLocalThetaTransition hST) (sLocalThetaToGlobal F T)
    (sLocalThetaToGlobal F S) (sLocalThetaToGlobal_isEmbedding (F := F) (S := T))
    ⟨sLocalThetaToGlobal_isEmbedding (F := F) (S := S), sLocalThetaToGlobal_isClosed_range (F := F) (S := S)⟩
    (sLocalThetaToGlobal_comp (F := F) hST)

end Transitions

section GlobalTopology

open Set TopologicalSpace

private theorem frechet_of_closed_embedding {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y]
    [TopologicalSpace Y] (i : X →L[ℂ] Y) (hi : IsClosedEmbedding i) (hY : IsFrechetTVS Y) :
    IsFrechetTVS X := by
  obtain ⟨a,p,m,c⟩ := hY
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  let : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace Y := c
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have hu := AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom) hi.isInducing
  exact ⟨inferInstance, hi.eq_induced ▸ PolynormableSpace.induced i.toLinearMap,
    hi.isEmbedding.metrizableSpace, hu.completeSpace hi.isClosed_range.isComplete⟩

private theorem embedded_frechet_range {X E : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] (i : X →L[ℂ] E) (hi : IsEmbedding i)
    (hX : IsFrechetTVS X) : IsClosed (range i) ∧ IsFrechetTVS i.toLinearMap.range := by
  obtain ⟨a,p,m,c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let e := LinearEquiv.ofInjective i.toLinearMap hi.injective
  have he : IsInducing e := IsInducing.subtypeVal.of_comp_iff.mp hi.isInducing
  let h := e.toEquiv.toHomeomorphOfIsInducing he
  let L : X ≃L[ℂ] i.toLinearMap.range := ⟨e, h.continuous, h.continuous_symm⟩
  exact ⟨(AddMonoidHom.isUniformInducing_of_isInducing (f := i.toLinearMap.toAddMonoidHom)
      hi.isInducing).isComplete_range.isClosed,
    frechet_of_closed_embedding L.symm.toContinuousLinearMap L.symm.toHomeomorph.isClosedEmbedding ⟨a,p,m,c⟩⟩

private theorem frechet_range_in_cover {ι X E : Type*} [Countable ι] [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (i : X →L[ℂ] E) (hX : IsFrechetTVS X) (D : ι → Submodule ℂ E)
    (hd : ∀ t, IsClosed (D t : Set E)) (hc : ∀ x : E, ∃ t, x ∈ D t) :
    ∃ t, i.toLinearMap.range ≤ D t := by
  obtain ⟨a,p,m,c⟩ := hX
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace X := c
  have : (uniformity X).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero X]
    infer_instance
  let : BaireSpace X := by
    let := UniformSpace.metricSpace X
    infer_instance
  let K (t : ι) := (D t).comap i.toLinearMap
  have hcov : (⋃ t, (K t : Set X)) = univ :=
    eq_univ_of_forall fun x ↦ (hc (i x)).elim fun t ht ↦ mem_iUnion.mpr ⟨t, ht⟩
  obtain ⟨t, ht⟩ := nonempty_interior_of_iUnion_of_closed (fun t ↦ (hd t).preimage i.continuous) hcov
  have htop : K t = ⊤ := (K t).eq_top_of_nonempty_interior' ht
  exact ⟨t, fun _ ⟨x,hx⟩ ↦ hx ▸ (show x ∈ K t from htop.symm ▸ Submodule.mem_top)⟩

/-- An LF-space covered by countably many closed Fréchet subspaces is strict.
The closure of each defining stage lies in a single member of the cover by Baire. -/
private theorem strictLF_of_countable_frechet_cover {ι E : Type*} [Countable ι] [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (hLF : IsLFSpace E) (D : ι → Submodule ℂ E) (hd : ∀ t, IsClosed (D t : Set E))
    (hD : ∀ t, IsFrechetTVS (D t)) (hc : ∀ x : E, ∃ t, x ∈ D t) : IsStrictLFSpace E := by
  obtain ⟨h₂,X,_,_,_,hX,j,i,h⟩ := hLF
  let R (k : ℕ) := (i k).toLinearMap.range
  let S (k : ℕ) := (R k).topologicalClosure
  have hP : WithSeminorms (Subtype.val :
      {p : Seminorm ℂ E // ∀ k, Continuous (p ∘ (i k).toLinearMap)} → _) := ⟨h.topology_eq⟩
  have hS (k : ℕ) : IsFrechetTVS (S k) := by
    obtain ⟨t,ht⟩ := frechet_range_in_cover (i k) (hX k) D hd hc
    have hst : S k ≤ D t := closure_minimal ht (hd t)
    let l := Submodule.inclusion hst
    have he : IsEmbedding l := IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal
    have hr : range l = Subtype.val ⁻¹' (S k : Set E) := by
      ext x
      exact ⟨fun ⟨y,hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x.val, hx⟩, rfl⟩⟩
    exact frechet_of_closed_embedding ⟨l, he.continuous⟩
      ⟨he, hr ▸ (R k).isClosed_topologicalClosure.preimage continuous_subtype_val⟩ (hD t)
  refine ⟨h₂, S, monotone_nat_of_le_succ (fun k ↦ ?_), hS, fun x ↦ ?_, ?_⟩
  · apply closure_mono
    rintro _ ⟨y,rfl⟩
    exact ⟨j k y, DFunLike.congr_fun (h.compatible k) y⟩
  · obtain ⟨k,hk⟩ := h.exhaustive x
    exact ⟨k, subset_closure hk⟩
  · have hs : (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (S k).subtype)) =
        (fun p : Seminorm ℂ E ↦ ∀ k, Continuous (p ∘ (i k).toLinearMap)) := by
      funext p
      apply propext
      refine ⟨fun hp k ↦ ?_, fun hp k ↦ (hP.continuous_seminorm ⟨p,hp⟩).comp continuous_subtype_val⟩
      exact (hp k).comp ((i k).codRestrict (S k) (fun y ↦ subset_closure (mem_range_self y))).continuous
    unfold locallyConvexFinalTopology
    rw [hs]
    exact hP.withSeminorms_eq

private theorem strictLF_of_embedded_strictLF_cover {ι E : Type*} [Countable ι]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {X : ι → Type*} [∀ t, AddCommGroup (X t)] [∀ t, Module ℂ (X t)] [∀ t, TopologicalSpace (X t)]
    (hLF : IsLFSpace E) (j : ∀ t, X t →L[ℂ] E) (hi : ∀ t, IsEmbedding (j t))
    (hx : ∀ t, IsStrictLFSpace (X t)) (hc : ∀ x, ∃ t y, j t y = x) : IsStrictLFSpace E := by
  let : T2Space E := hLF.1
  let S t := (hx t).2.choose
  have hS t := (hx t).2.choose_spec
  let u (p : ι × ℕ) := (j p.1).comp ((S p.1 p.2).subtypeL)
  have he (p : ι × ℕ) := embedded_frechet_range (u p) ((hi p.1).comp IsEmbedding.subtypeVal)
    ((hS p.1).2.1 p.2)
  apply strictLF_of_countable_frechet_cover hLF (fun p ↦ (u p).toLinearMap.range) (fun p ↦ (he p).1) (fun p ↦ (he p).2)
  intro x
  obtain ⟨t,y,rfl⟩ := hc x
  obtain ⟨n,hn⟩ := (hS t).2.2.1 y
  exact ⟨(t,n), ⟨y,hn⟩,rfl⟩
/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta space is a strict LF-space.
Deviation: The Fréchet stages inherit nuclearity from the separately stated
nuclearity of the whole space under `isNuclearTVS_submodule`. -/
theorem globalAdelicThetaSpace_strictLF : IsStrictLFSpace Θ𝔽 := by
  let : Countable (HeightOneSpectrum (𝓞 F)) := finitePlaces_countable F
  let j (S : Finset (HeightOneSpectrum (𝓞 F))) : Θₛ(S) →L[ℂ] Θ𝔽 :=
    ⟨sLocalThetaToGlobal F S, sLocalThetaToGlobal_continuous (F := F) (S := S)⟩
  exact strictLF_of_embedded_strictLF_cover (globalAdelicThetaSpace_lf (F := F)) j
    (fun S ↦ sLocalThetaToGlobal_isEmbedding (F := F) (S := S))
    (fun S ↦ sLocalAdelicThetaSpace_strictLF (F := F) (S := S))
    (sLocalThetaToGlobal_exhaustive (F := F))

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The global theta quotient is complete. -/
theorem globalAdelicThetaSpace_complete :
    @CompleteSpace Θ𝔽 (IsTopologicalAddGroup.rightUniformSpace Θ𝔽) := by
  exact IsStrictLFSpace.completeSpace (E := Θ𝔽) globalAdelicThetaSpace_strictLF

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the global theta quotient. -/
theorem globalAdelicThetaSpace_montel : MontelSpace ℂ Θ𝔽 := montelSpace_of_nuclear_strictLF.{0} globalAdelicThetaSpace_strictLF
    globalAdelicThetaSpace_nuclear

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is nuclear. -/
theorem globalAdelicThetaSpace_strongDual_nuclear : IsNuclearTVS (StrongDual ℂ Θ𝔽) := by
  apply nuclear_of_linear_embedding (ContinuousLinearMap.precomp ℂ (K𝔽).mkQL)
  · exact isEmbedding_transpose_quotient_of_strictLF _ (adeleSchwartz_strictLF (F := F)).2
      (adeleSchwartz_nuclear (F := F)).2 adelicTheta_ker_isClosed globalAdelicThetaSpace_strictLF
  · exact (adeleSchwartz_strongDual_nuclear (F := F)).2

/-- Paper: Theorem 5.2.1.1(1), p. 230.
The strong dual of the global theta quotient is barrelled. -/
theorem globalAdelicThetaSpace_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ Θ𝔽) := by
    let : T2Space Θ𝔽 := (globalAdelicThetaSpace_lf (F := F) ).1
    let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable
    let : MontelSpace ℂ Θ𝔽 := globalAdelicThetaSpace_montel
    exact barrelled_strongDual_of_montel

/-- Paper: Theorem 5.2.1.1(1), p. 230.
Closed bounded subsets are compact in the strong dual of the global theta quotient. -/
theorem globalAdelicThetaSpace_strongDual_montel : MontelSpace ℂ (StrongDual ℂ Θ𝔽) := by
  let : UniformSpace Θ𝔽 := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup Θ𝔽 := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ Θ𝔽 := globalAdelicThetaSpace_barrelled (F := F)
  exact montelSpace_strongDual_of_precompact (fun _ hb ↦ globalAdelicThetaSpace_bounded_totallyBounded (F := F) hb)

/-- Paper: (5.2.1.4), p. 231.
The transpose of the global theta quotient map is an embedding for the strong dual topologies. -/
theorem globalThetaQuotient_transpose_isEmbedding :
    IsEmbedding (fun l : StrongDual ℂ Θ𝔽 ↦ l.comp (K𝔽).mkQL) := by
  exact isEmbedding_transpose_quotient_of_strictLF _ (adeleSchwartz_strictLF (F := F)).2
    (adeleSchwartz_nuclear (F := F)).2 adelicTheta_ker_isClosed globalAdelicThetaSpace_strictLF

end GlobalTopology

section HomogeneousQuotients

-- TODO(paper-gap): Footnote 3 on p. 232 asks to adjust the introduction
-- to §5.2.2 without specifying the adjustment.

-- Use the Borel structure and the Haar normalization in §3.3.1, as in §5.1.
local instance normOneSIdeleQuotientMeasurableSpaceSec2 (F : Type*) [Field F]
    [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    MeasurableSpace (MonoidHom.ker (sIdeleQuotientNorm F S)) := borel _

local instance normOneSIdeleQuotientHaarSec2 :
    Measure.IsHaarMeasure (sLocalNormOneQuotientMeasure F S) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta transform is the complex-linear map of §2.2.5. -/
def homogeneousAdelicThetaLinearMap (ω : PontryaginDual C₁) :
    ℬ𝔽 →ₗ[ℂ] C(C𝔽, ℂ) :=
  IsLinearMap.mk' (homogeneousAdelicTheta ω) (homogeneousAdelicTheta_isLinear ω)

/-- Paper: Definition 5.2.2.1(1), p. 232.
The linear transform evaluates to the global homogeneous theta function. -/
theorem homogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual C₁) (f : ℬ𝔽) :
    homogeneousAdelicThetaLinearMap F ω f = homogeneousAdelicTheta ω f := rfl

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta transform uses the norm-one quotient measure of §3.3.1. -/
def sLocalHomogeneousAdelicThetaLinearMap (ω : PontryaginDual (J₁(S))) :
    ℬₛ(S) →ₗ[ℂ] C(Jₛ(S), ℂ) :=
  sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω

/-- Paper: Definition 5.2.2.1(2), p. 232.
The linear transform evaluates to the S-local homogeneous theta function
with the norm-one Tamagawa measure of §3.3.1. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_apply (ω : PontryaginDual (J₁(S)))
    (f : ℬₛ(S)) (g : Jₛ(S)) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω f g =
      ∫ h : J₁(S), sLocalAdelicThetaOnClasses F S f (g * h.val) * (ω h : ℂ)
        ∂sLocalNormOneQuotientMeasure F S := rfl

local notation "K𝔽ω(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "Kₛω(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F _ ω)

variable (F) in
/-- Paper: Definition 5.2.2.1(1), p. 232.
The global homogeneous theta space is the topological quotient of Schwartz–Bruhat
functions by the kernel of the homogeneous theta transform. -/
abbrev GlobalHomogeneousThetaSpace (ω : PontryaginDual C₁) :=
  ℬ𝔽 ⧸ K𝔽ω(ω)

private theorem quotient_ker_mk_eq {R X Y : Type*} [Ring R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (θ : X →ₗ[R] Y) (f g : X) :
    θ.ker.mkQ f = θ.ker.mkQ g ↔ θ f = θ g := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Paper: Definition 5.2.2.1(1), p. 232.
Two test functions give the same global homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem globalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual C₁) (f g : ℬ𝔽) :
    (Submodule.Quotient.mk f : GlobalHomogeneousThetaSpace F ω) = Submodule.Quotient.mk g ↔
      homogeneousAdelicTheta ω f = homogeneousAdelicTheta ω g := quotient_ker_mk_eq (homogeneousAdelicThetaLinearMap F ω) f g

variable (F S) in
/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous theta space is the topological quotient of S-local
Schwartz–Bruhat functions by the kernel of the S-local homogeneous transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalHomogeneousThetaSpace (ω : PontryaginDual (J₁(S))) :=
  ℬₛ(S) ⧸ Kₛω(ω)

/-- Paper: Definition 5.2.2.1(2), p. 232.
Two S-local test functions give the same homogeneous theta class exactly when
their homogeneous theta functions agree. -/
theorem sLocalHomogeneousThetaSpace_mk_eq_iff (ω : PontryaginDual (J₁(S))) (f g : ℬₛ(S)) :
    (Submodule.Quotient.mk f : SLocalHomogeneousThetaSpace F S ω) = Submodule.Quotient.mk g ↔
      sLocalHomogeneousAdelicThetaLinearMap F S ω f =
        sLocalHomogeneousAdelicThetaLinearMap F S ω g := quotient_ker_mk_eq (sLocalHomogeneousAdelicThetaLinearMap F S ω) f g

section CoinvariantAverages

open Set

private theorem quotientEquiv_of_comap {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (K H : Submodule ℂ X) (D : Submodule ℂ (X ⧸ K)) (h : H = D.comap K.mkQ) :
    ∃ e : (X ⧸ H) ≃L[ℂ] ((X ⧸ K) ⧸ D), ∀ f, e (H.mkQ f) = D.mkQ (K.mkQ f) := by
  let q := D.mkQ.comp K.mkQ
  have hq : H = q.ker := h.trans (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])
  let e := (Submodule.quotEquivOfEq _ _ hq).trans (q.quotKerEquivOfSurjective
    (D.mkQ_surjective.comp K.mkQ_surjective))
  have he (f : X) : e (H.mkQ f) = q f := q.quotKerEquivOfSurjective_apply_mk (D.mkQ_surjective.comp K.mkQ_surjective) f
  have hquot : IsQuotientMap q := D.isQuotientMap_mkQ.comp K.isQuotientMap_mkQ
  have hcont : Continuous e := H.isQuotientMap_mkQ.continuous_iff.mpr
    (hquot.continuous.congr fun f ↦ (he f).symm)
  have hinv : Continuous e.symm := hquot.continuous_iff.mpr
    (H.mkQL.continuous.congr fun f ↦ (e.symm_apply_eq.mpr (he f).symm).symm)
  exact ⟨⟨e, hcont, hinv⟩, he⟩

private theorem ker_isotypicIntegral {G E A : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]
    (hcomplete : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* (E →L[ℂ] E))
    (hρ : Continuous fun p : G × E ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (ev : A → StrongDual ℂ E) (hsep : ∀ x, (∀ a, ev a x = 0) → x = 0) (x : E) :
    x ∈ (Submodule.span ℂ (range (fun p : G × E ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure ↔
      ∀ a, (∫ g, star (ω g : ℂ) * ev a (ρ g x) ∂μ) = 0 := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace E := hcomplete
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : SeparatingDual ℂ E := locallyConvexSpace_separatingDual ℂ E
  let A' (g : G) := star (ω g : ℂ) • ρ g
  have hA : Continuous fun p : G × E ↦ A' p.1 p.2 :=
    (show Continuous (fun p : G × E ↦ star (ω p.1 : ℂ)) from by fun_prop).smul hρ
  obtain ⟨P, hP, _⟩ := existsUnique_pettisIntegral_continuousFamily μ isCompact_univ
    (ae_of_all _ fun _ ↦ mem_univ _) A' hA
  have hav : IsPettisIsotypicAverageOn μ univ ρ ω P := by
    simpa [IsPettisIsotypicAverageOn, A'] using hP
  rw [← compactActionAverage_ker μ ρ hρ ω P hav, LinearMap.mem_ker]
  simp_rw [← compactActionAverage_dual_apply μ ρ ω P hav x]
  exact ⟨fun h a ↦ h ▸ map_zero _, hsep _⟩
private theorem thetaQuotientEval_separates {X A : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [TopologicalSpace A] (θ : X →ₗ[ℂ] C(A, ℂ))
    (hc : ∀ a, Continuous (fun f ↦ θ f a)) (x : X ⧸ θ.ker)
    (h : ∀ a, thetaQuotientEval θ a (hc a) x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := θ.ker.mkQ_surjective x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (ContinuousMap.ext h)

private theorem inv_character_integral {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [MeasurableInv G] (μ : Measure G) [μ.IsInvInvariant]
    (ω : PontryaginDual G) (φ : G → ℂ) :
    (∫ g, star (ω g : ℂ) * φ g⁻¹ ∂μ) = ∫ g, φ g * (ω g : ℂ) ∂μ := by
  refine Eq.trans (integral_congr_ae (.of_forall fun g ↦ ?_))
    (integral_inv_eq_self (fun g ↦ φ g * (ω g : ℂ)) μ)
  rw [map_inv, Circle.coe_inv_eq_conj, mul_comm]
  rfl

private theorem coinvariantEquiv_of_formula {G E A B : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [TopologicalSpace A] [TopologicalSpace B]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (cθ : ∀ a, Continuous (fun f ↦ θ f a))
    [PolynormableSpace ℂ (E ⧸ θ.ker)] [T2Space (E ⧸ θ.ker)]
    (hcomplete : @CompleteSpace (E ⧸ θ.ker) (IsTopologicalAddGroup.rightUniformSpace _))
    (μ : Measure G) [μ.IsHaarMeasure] (ρ : G →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)))
    (hρ : Continuous fun p : G × (E ⧸ θ.ker) ↦ ρ p.1 p.2) (ω : PontryaginDual G)
    (H : E →ₗ[ℂ] C(B, ℂ)) (j : A → B) (hj : Surjective j)
    (h : ∀ f a, (∫ g, star (ω g : ℂ) * thetaQuotientEval θ a (cθ a) (ρ g (θ.ker.mkQ f)) ∂μ) =
      H f (j a)) :
    let D := (Submodule.span ℂ (range (fun p : G × (E ⧸ θ.ker) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1 p.2))).topologicalClosure
    ∃ e : (E ⧸ H.ker) ≃L[ℂ] ((E ⧸ θ.ker) ⧸ D),
      ∀ f, e (H.ker.mkQ f) = D.mkQ (θ.ker.mkQ f) := by
  apply quotientEquiv_of_comap
  refine Submodule.ext fun f ↦ ?_
  refine Iff.trans ?_ (ker_isotypicIntegral hcomplete μ ρ hρ ω
    (fun a ↦ thetaQuotientEval θ a (cθ a)) (thetaQuotientEval_separates θ cθ) _).symm
  refine ⟨fun hf a ↦ (h f a).trans (congrArg (fun s : C(B, ℂ) ↦ s (j a)) (LinearMap.mem_ker.mp hf)),
    fun he ↦ LinearMap.mem_ker.mpr (ContinuousMap.ext fun b ↦ ?_)⟩
  obtain ⟨a, rfl⟩ := hj b
  exact (h f a).symm.trans (he a)

/-- A character average on a compact subgroup identifies the homogeneous quotient with
the quotient by the closed span of the twisted differences. The ordinary theta
quotient must be complete, and its point evaluations separate its elements. -/
theorem thetaQuotient_equiv_coinvariants_of_average {G E A B : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [CompactSpace N] [T2Space N] [MeasurableSpace N]
    [BorelSpace N] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [TopologicalSpace A] [TopologicalSpace B]
    (θ : E →ₗ[ℂ] C(A, ℂ)) (cθ : ∀ a, Continuous (fun f ↦ θ f a))
    [PolynormableSpace ℂ (E ⧸ θ.ker)] [T2Space (E ⧸ θ.ker)]
    (hcomplete : @CompleteSpace (E ⧸ θ.ker) (IsTopologicalAddGroup.rightUniformSpace _))
    (μ : Measure N) [μ.IsHaarMeasure] (ρ : G →* ((E ⧸ θ.ker) →L[ℂ] (E ⧸ θ.ker)))
    (hρ : Continuous fun p : G × (E ⧸ θ.ker) ↦ ρ p.1 p.2) (ω : PontryaginDual N)
    (H : E →ₗ[ℂ] C(B, ℂ)) (j : A → B) (hj : Surjective j)
    (φ : E → A → N → ℂ)
    (hφ : ∀ (g : N) f a, thetaQuotientEval θ a (cθ a) (ρ g.val (θ.ker.mkQ f)) = φ f a g⁻¹)
    (hH : ∀ f a, H f (j a) = ∫ g, φ f a g * (ω g : ℂ) ∂μ) :
    let D := (Submodule.span ℂ (range (fun p : N × (E ⧸ θ.ker) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : (E ⧸ H.ker) ≃L[ℂ] ((E ⧸ θ.ker) ⧸ D),
      ∀ f, e (Submodule.Quotient.mk f) = D.mkQ (θ.ker.mkQ f) := by
  refine coinvariantEquiv_of_formula θ cθ hcomplete μ (ρ.comp N.subtype)
    (hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)) ω H j hj ?_
  intro f a
  exact (integral_congr_ae (μ := μ) (.of_forall fun g : N ↦
    congrArg (star (ω g : ℂ) * ·) (hφ g f a))).trans
      ((inv_character_integral μ ω (φ f a)).trans (hH f a).symm)

/-- On the global theta quotient, translation shifts the argument of every evaluation. -/
theorem globalThetaAction_eval
    (ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽))
    (h : ∀ (g : IdeleGroup (𝓞 F) F) f, ρ (QuotientGroup.mk g) ((K𝔽).mkQ f) =
      (K𝔽).mkQ (schwartzBruhatUnitTranslate g f)) (f : ℬ𝔽) (a q : C𝔽)
    (hc : Continuous (fun f ↦ (adelicThetaLinearMap F f) a)) :
    thetaQuotientEval (adelicThetaLinearMap F) a hc
      (ρ q ((K𝔽).mkQ f)) = adelicTheta f (q⁻¹ * a) :=
  QuotientGroup.induction_on q fun g ↦ (congrArg
    (thetaQuotientEval (adelicThetaLinearMap F) a (adelicTheta_eval_continuous a))
    (h g f)).trans (globalTheta_translate_apply g f a)

end CoinvariantAverages

private theorem global_coinvariants_of_action
    (ρ : C𝔽 →* (Θ𝔽 →L[ℂ] Θ𝔽))
    (horbit : Continuous (fun p : C𝔽 × Θ𝔽 ↦ ρ p.1 p.2))
    (hrep : ∀ (g : IdeleGroup (𝓞 F) F) (f : ℬ𝔽), ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f))
    (ω : PontryaginDual C₁) :
    let D := (Submodule.span ℂ (Set.range (fun p : C₁ × Θ𝔽 ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : GlobalHomogeneousThetaSpace F ω ≃L[ℂ] (Θ𝔽 ⧸ D),
      ∀ f : ℬ𝔽, e (Submodule.Quotient.mk f) = D.mkQ ((K𝔽).mkQ f) := by
  let μ := normOneIdeleClassTamagawaMeasure F
  let : MeasurableSpace C𝔽 := borel _
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : T2Space C₁ := (ideleClassGroup_finiteness F).2.2.1
  let : CompactSpace C₁ := (ideleClassGroup_finiteness F).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : T2Space Θ𝔽 := globalAdelicThetaSpace_t2_of_isClosed (F := F) (adelicTheta_ker_isClosed (F := F))
  let : PolynormableSpace ℂ Θ𝔽 := globalAdelicThetaSpace_polynormable (F := F)
  let φ (f : ℬ𝔽) (a : C𝔽) (g : C₁) := adelicTheta f (g.val * a)
  have heval (g : C₁) (f : ℬ𝔽) (a : C𝔽) :
      thetaQuotientEval (adelicThetaLinearMap F) a (adelicTheta_eval_continuous a)
        (ρ g.val ((K𝔽).mkQ f)) = φ f a g⁻¹ := by
    exact globalThetaAction_eval (F := F) ρ hrep f a g.val (adelicTheta_eval_continuous a)
  have hint (f : ℬ𝔽) (a : C𝔽) :
      homogeneousAdelicThetaLinearMap F ω f a = ∫ g, φ f a g * (ω g : ℂ) ∂μ := rfl
  have cθ (a : C𝔽) : Continuous (fun f ↦ adelicThetaLinearMap F f a) :=
    (adelicTheta_eval_continuous (F := F) a).congr fun f ↦
      DFunLike.congr_fun (adelicThetaLinearMap_apply (F := F) f).symm a
  have hj : Surjective (fun a : C𝔽 ↦ a) := surjective_id
  with_reducible_and_instances
    exact thetaQuotient_equiv_coinvariants_of_average (G := C𝔽) (E := ℬ𝔽) (A := C𝔽) (B := C𝔽)
      (MonoidHom.ker (ideleClassNorm F)) (adelicThetaLinearMap F) cθ
      (globalAdelicThetaSpace_complete (F := F)) μ ρ horbit ω (homogeneousAdelicThetaLinearMap F ω)
      (fun a : C𝔽 ↦ a) hj φ heval hint

/-- Paper: Definition 5.2.2.1(1), p. 232.
The homogeneous theta quotient identifies canonically with the quotient of ordinary
theta space by the closed span of the character-twisted translation differences. -/
theorem globalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual C₁) :
    let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : C₁ × Θ𝔽 ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : GlobalHomogeneousThetaSpace F ω ≃L[ℂ] (Θ𝔽 ⧸ D),
      ∀ f : ℬ𝔽, e (Submodule.Quotient.mk f) = D.mkQ ((K𝔽).mkQ f) := by
  with_reducible_and_instances
    exact global_coinvariants_of_action (F := F) (existsUnique_globalThetaAction (F := F)).exists.choose
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.1
      (existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 ω

/-- On local test representatives the translation action shifts the S-idele class
in the theta evaluation by the inverse translating class. -/
theorem sLocalThetaAction_eval
    (ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)))
    (h : ∀ (g : (SAdeleRing F S)ˣ) f, ρ (QuotientGroup.mk g) ((Kₛ(S)).mkQ f) =
      (Kₛ(S)).mkQ (schwartzBruhatUnitTranslate g f)) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) (q : Jₛ(S))
    (hc : Continuous (fun f ↦ sLocalAdelicTheta F S f a)) :
    thetaQuotientEval (sLocalAdelicTheta F S) a hc
      (ρ q ((Kₛ(S)).mkQ f)) = sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * q⁻¹) := by
  let π : (SAdeleRing F S)ˣ →* Jₛ(S) := QuotientGroup.mk' _
  refine QuotientGroup.induction_on q fun g ↦ (congrArg
    (thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)) (h g f)).trans ?_
  exact (localTheta_translate_apply g a f).trans
    ((sLocalAdelicThetaOnClasses_mk F S f (g⁻¹ * a)).symm.trans
      (congrArg (sLocalAdelicThetaOnClasses F S f) ((π.map_mul _ _).trans
        ((congrArg (· * π a) (π.map_inv g)).trans (mul_comm ((π g)⁻¹) (π a))))))

private theorem local_coinvariants_of_action
    (ρ : Jₛ(S) →* (Θₛ(S) →L[ℂ] Θₛ(S)))
    (horbit : Continuous (fun p : Jₛ(S) × Θₛ(S) ↦ ρ p.1 p.2))
    (hrep : ∀ (g : (SAdeleRing F S)ˣ) (f : ℬₛ(S)), ρ (QuotientGroup.mk g) (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (schwartzBruhatUnitTranslate g f))
    (ω : PontryaginDual (J₁(S))) :
    let D := (Submodule.span ℂ (Set.range (fun p : J₁(S) × Θₛ(S) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : SLocalHomogeneousThetaSpace F S ω ≃L[ℂ] (Θₛ(S) ⧸ D),
      ∀ f : ℬₛ(S), e (Submodule.Quotient.mk f) = D.mkQ ((Kₛ(S)).mkQ f) := by
  let μ := sLocalNormOneQuotientMeasure F S
  have hclosed := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (Jₛ(S)) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space (J₁(S)) := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (Jₛ(S))))
  let : BorelSpace (J₁(S)) := ⟨rfl⟩
  let : CompactSpace (J₁(S)) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space (Θₛ(S)) := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S) (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let φ (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) (g : J₁(S)) :=
    sLocalAdelicThetaOnClasses F S f (QuotientGroup.mk a * g.val)
  have heval (g : J₁(S)) (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      thetaQuotientEval (sLocalAdelicTheta F S) a (sLocalAdelicTheta_continuous_eval a)
        (ρ g.val ((Kₛ(S)).mkQ f)) = φ f a g⁻¹ := sLocalThetaAction_eval (F := F) (S := S) ρ hrep f a g.val (sLocalAdelicTheta_continuous_eval a)
  have hint (f : ℬₛ(S)) (a : (SAdeleRing F S)ˣ) :
      sLocalHomogeneousAdelicThetaLinearMap F S ω f (QuotientGroup.mk a) =
        ∫ g, φ f a g * (ω g : ℂ) ∂μ := rfl
  with_reducible_and_instances
    exact thetaQuotient_equiv_coinvariants_of_average (G := Jₛ(S)) (E := ℬₛ(S)) (A := (SAdeleRing F S)ˣ) (B := Jₛ(S))
      (MonoidHom.ker (sIdeleQuotientNorm F S)) (sLocalAdelicTheta F S)
      (sLocalAdelicTheta_continuous_eval (F := F) (S := S)) (sLocalAdelicThetaSpace_complete (F := F) (S := S))
      μ ρ horbit ω (sLocalHomogeneousAdelicThetaLinearMap F S ω) (QuotientGroup.mk : (SAdeleRing F S)ˣ → Jₛ(S))
      QuotientGroup.mk_surjective φ heval hint

/-- Paper: Definition 5.2.2.1(2), p. 232.
The S-local homogeneous quotient identifies canonically with the quotient of ordinary
S-local theta space by the closed span of the twisted norm-one translation differences. -/
theorem sLocalHomogeneousThetaSpace_equiv_coinvariants (ω : PontryaginDual (J₁(S))) :
    let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
    let D := (Submodule.span ℂ (Set.range (fun p : J₁(S) × Θₛ(S) ↦
      p.2 - star (ω p.1 : ℂ) • ρ p.1.val p.2))).topologicalClosure
    ∃ e : SLocalHomogeneousThetaSpace F S ω ≃L[ℂ] (Θₛ(S) ⧸ D),
      ∀ f : ℬₛ(S), e (Submodule.Quotient.mk f) = D.mkQ ((Kₛ(S)).mkQ f) := by
  with_reducible_and_instances
    exact local_coinvariants_of_action (F := F) (S := S)
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1
      (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.2 ω

end HomogeneousQuotients

-- The first digest ends at Definition 5.2.2.1. The isotypic structure
-- results and the Fourier descent statements remain for a subsequent digest.
-- TODO(continuation): (5.2.2.2), Theorem 5.2.3.1, Proposition 5.2.3.2,
-- Remarks 5.2.3.3–5.2.3.5 and the individual involutions in Theorem 5.2.4.1.
-- TODO(paper-gap): The global L² argument on p. 237 fails for the rational
-- Gaussian, whose theta is asymptotic to 1/t at the origin. Character
-- uniqueness can be applied on each compact norm-one fiber instead.
-- TODO(paper-gap): On p. 234 the proof of Theorem 5.2.3.1 refers to the
-- descending idempotent as "(??)". The proof on p. 231 does not construct
-- a kernel-preserving Schwartz–Bruhat projection.
-- TODO(paper-gap): In Remark 5.2.3.4 the topology induced from the theta
-- quotient is called Hausdorff on the test space. For ℚ it identifies every
-- odd test function with zero.
-- TODO(paper-gap): The Fourier compatibility in Theorem 5.2.4.1 fails upon
-- adding a place dividing the different. For ℚ(i) at the place above 2,
-- Fourier sends the integer indicator to half the inverse-different indicator.

end RiemannMasullo
