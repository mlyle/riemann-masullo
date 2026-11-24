module

public import Mathlib.Data.List.TFAE
public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Strict.Basic

import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.WithTopology

/-!
# Appendix E.1.1. Preparations on compactly generated spaces

Paper: Notation E.0.0.1, p. 824. The categories of sets and spaces are
`CategoryTheory.types` and `TopCat`. Use the coercion to a type for the underlying set
and `ContinuousMap` (notation `C(X, Y)`) for the set of continuous maps.

Paper: Terminology E.0.0.1, p. 824. Set-functions are ordinary Lean functions. Coercion
takes a continuous map to its underlying function, and `CategoryTheory.forget TopCat`
forgets the topology. Compactness and local compactness are `CompactSpace` (with no
separation assumption) and `LocallyCompactSpace` (a basis of compact neighborhoods).

Paper: Terminology E.0.0.2, pp. 824–825. The preimage of a subspace is the subtype of the
set preimage. For immersions, submersive maps, and étale maps use `Topology.IsEmbedding`,
`Topology.IsQuotientMap`, and `IsLocalHomeomorph`, respectively. The intrinsic topology
is the original `TopologicalSpace` instance.

The introduction on pp. 825–828 previews results in §§E.1.2–E.3. Here the compact probes
are compact Hausdorff spaces in an explicit universe, independent of the carrier universe.
-/

@[expose] public section

open Set Topology TopologicalSpace

open scoped Topology

namespace RiemannMasullo

universe u v w

section Image

variable {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [TopologicalSpace Y]

/-- Paper: Terminology E.0.0.2(1)–(2), pp. 824–825.
The topology of the image is the quotient topology on the range of the continuous map. -/
@[instance_reducible]
def quotientImageTopology (f : C(X, Y)) : TopologicalSpace (range f) :=
  tX.coinduced (rangeFactorization f)

/-- Paper: Terminology E.0.0.2(1), pp. 824–825.
A subset of the image is open in the quotient topology exactly when its preimage is open. -/
theorem isOpen_quotientImageTopology_iff (f : C(X, Y)) (s : Set (range f)) :
    IsOpen[quotientImageTopology f] s ↔ IsOpen (rangeFactorization f ⁻¹' s) :=
  isOpen_coinduced

/-- Paper: Terminology E.0.0.2(1), pp. 824–825.
A map is strict exactly when the quotient image topology agrees with the subspace topology. -/
theorem isStrictMap_iff_quotientImageTopology (f : C(X, Y)) :
    IsStrictMap f ↔ quotientImageTopology f = (inferInstance : TopologicalSpace (range f)) := by
  rw [isStrictMap_iff_isQuotientMap_rangeFactorization]
  exact ⟨fun h => h.eq_coinduced.symm, fun h => ⟨⟨h.symm⟩, rangeFactorization_surjective⟩⟩

end Image

section CompactGeneration

variable {X : Type w} [tX : TopologicalSpace X]

/-- Paper: Definition E.1.1.1(1), p. 828.
A subset is k-closed if its preimage under every compact Hausdorff probe is closed.
Deviation: The probes have carriers in a fixed universe `u`. -/
def IsKClosed (s : Set X) : Prop :=
  ∀ (K : CompHaus.{u}) (g : C(K, X)), IsClosed (g ⁻¹' s)

/-- Paper: Definition E.1.1.1(2), p. 828.
Mathlib's compactly generated topology on the original carrier is the coarsest topology
in which every k-closed subset is closed.
Deviation: The probes have carriers in a fixed universe `u`. -/
theorem isCoarsest_compactlyGenerated :
    IsGreatest {t : TopologicalSpace X | ∀ s : Set X, IsKClosed.{u} s → IsClosed[t] s}
      (TopologicalSpace.compactlyGenerated.{u} X) := by
  sorry

/-- Paper: Remark E.1.1.2(1), p. 828.
The identity from the k-topology to the original topology is continuous.
Deviation: The k-topology uses probes in universe `u`. -/
theorem continuous_compactlyGenerated_to_original :
    Continuous[TopologicalSpace.compactlyGenerated.{u} X, tX] (id : X → X) := by
  rw [TopologicalSpace.compactlyGenerated, continuous_coinduced_dom]
  exact continuous_sigma fun i => i.2.continuous

/-- Paper: Remark E.1.1.2(2), p. 828.
The closed sets of the k-topology are exactly the k-closed sets.
Deviation: Both tests use probes in universe `u`. -/
theorem isClosed_compactlyGenerated_iff (s : Set X) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} X] s ↔ IsKClosed.{u} s := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact ⟨fun h K g => h ⟨K, g⟩, fun h i => h i.1 i.2⟩

/-- Paper: Lemma E.1.1.3(1), p. 828.
A function out of the space is continuous exactly when its composites with all compact
Hausdorff probes are continuous.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
def HasCompactHausdorffContinuityTest.{probe, target, carrier} (X : Type carrier)
    [TopologicalSpace X] : Prop :=
  ∀ (Y : Type target) [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ (K : CompHaus.{probe}) (g : C(K, X)), Continuous (f ∘ g)

/-- Paper: Lemma E.1.1.3(2), p. 828.
There is a small family of compact Hausdorff sources such that continuity can be tested on
all continuous maps from every member of the family.
Deviation: Source and target carriers have fixed universes. The index is small in the
common universe of the source carriers and the tested space. -/
def HasCompactHausdorffContinuityTestFamily.{probe, target, carrier} (X : Type carrier)
    [TopologicalSpace X] : Prop :=
  ∃ (I : Type (max probe carrier)) (K : I → CompHaus.{probe}),
    ∀ (Y : Type target) [TopologicalSpace Y] (f : X → Y),
      Continuous f ↔ ∀ i, ∀ g : C(K i, X), Continuous (f ∘ g)

/-- Paper: Lemma E.1.1.3(3), p. 829.
Openness in the space is equivalent to openness of preimages along all compact Hausdorff probes.
Deviation: The probes have carriers in a fixed universe `u`. -/
def HasCompactHausdorffOpennessTest (X : Type w) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsOpen s ↔ ∀ (K : CompHaus.{u}) (g : C(K, X)), IsOpen (g ⁻¹' s)

/-- Paper: Lemma E.1.1.3(4), p. 829.
The space admits a quotient map from a coproduct of compact Hausdorff spaces.
Deviation: The summands lie in universe `u` and the index is small in the common
universe of their carriers and `X`. -/
def HasCompactHausdorffQuotientPresentation (X : Type w) [TopologicalSpace X] : Prop :=
  ∃ (I : Type (max u w)) (K : I → CompHaus.{u}) (q : (Σ i, K i) → X),
    IsQuotientMap q

/-- Continuity of the `ULift`ed Sierpiński indicator of a set is openness of the set. -/
private theorem compactHausdorffTests_tfae_continuous_indicator_iff {Z : Type w}
    [TopologicalSpace Z] (s : Set Z) :
    Continuous (fun z => ULift.up.{v} (z ∈ s)) ↔ IsOpen s := by
  rw [← Homeomorph.ulift.comp_continuous_iff]
  exact continuous_Prop

/-- Paper: Lemma E.1.1.3, pp. 828–829.
The all-probe continuity test, the set of sources test, the openness test, and the
quotient presentation are equivalent.
Deviation: The probe, target, and index universes are those of the corresponding conditions. -/
theorem compactHausdorffTests_tfae (X : Type w) [TopologicalSpace X] :
    List.TFAE [HasCompactHausdorffContinuityTest.{u, v} X,
      HasCompactHausdorffContinuityTestFamily.{u, v} X,
      HasCompactHausdorffOpennessTest.{u} X,
      HasCompactHausdorffQuotientPresentation.{u} X] := by
  tfae_have 1 → 3 := by
    intro h s
    have := h (ULift.{v} Prop) (fun x => ULift.up (x ∈ s))
    rw [compactHausdorffTests_tfae_continuous_indicator_iff.{v}] at this
    rw [this]
    refine forall_congr' fun K => forall_congr' fun g => ?_
    exact compactHausdorffTests_tfae_continuous_indicator_iff.{v} (g ⁻¹' s)
  tfae_have 3 → 1 := by
    intro h Y _ f
    refine ⟨fun hf K g => hf.comp g.continuous, fun hf => continuous_def.2 fun V hV => ?_⟩
    exact (h _).2 fun K g => hV.preimage (hf K g)
  tfae_have 2 → 3 := by
    rintro ⟨I, K, hK⟩ s
    refine ⟨fun hs K g => hs.preimage g.continuous, fun hs => ?_⟩
    rw [← compactHausdorffTests_tfae_continuous_indicator_iff.{v}, hK]
    intro i g
    exact (compactHausdorffTests_tfae_continuous_indicator_iff.{v} (g ⁻¹' s)).2 (hs _ g)
  tfae_have 3 → 4 := by
    intro h
    have hw : ∀ s : {s : Set X // ¬ IsOpen s},
        ∃ (K : CompHaus.{u}) (g : C(K, X)), ¬ IsOpen (g ⁻¹' s.1) := fun s => by
      by_contra hc
      push Not at hc
      exact s.2 ((h s.1).2 hc)
    choose K₀ g₀ hg₀ using hw
    let K : ULift.{u} ({s : Set X // ¬ IsOpen s} ⊕ X) → CompHaus.{u} := fun i =>
      Sum.elim K₀ (fun _ => CompHaus.of PUnit.{u + 1}) i.down
    let g : ∀ i, C(K i, X) := fun i =>
      match i with
      | ⟨Sum.inl s⟩ => g₀ s
      | ⟨Sum.inr x⟩ => ContinuousMap.const _ x
    refine ⟨_, K, fun p => g p.1 p.2, ?_⟩
    have hc : Continuous (fun p : Σ i, K i => g p.1 p.2) :=
      continuous_sigma fun i => (g i).continuous
    refine ⟨isCoinducing_iff.2 fun s => ⟨fun hs => ?_, fun hs => hs.preimage hc⟩,
      fun x => ⟨⟨⟨Sum.inr x⟩, PUnit.unit⟩, rfl⟩⟩
    by_contra hns
    apply hg₀ ⟨s, hns⟩
    exact isOpen_sigma_iff.1 hs ⟨Sum.inl ⟨s, hns⟩⟩
  tfae_have 4 → 2 := by
    rintro ⟨I, K, q, hq⟩
    refine ⟨I, K, fun Y _ f => ⟨fun hf i g => hf.comp g.continuous, fun hf => ?_⟩⟩
    rw [hq.continuous_iff, continuous_sigma_iff]
    intro i
    have hqi : Continuous (fun k : K i => q ⟨i, k⟩) := hq.continuous.comp continuous_sigmaMk
    exact hf i ⟨_, hqi⟩
  tfae_finish

/-- Paper: Lemma E.1.1.4, p. 829.
A point has this property when every subset containing it is closed. -/
def AllSupersetsClosed (x : X) : Prop :=
  ∀ s : Set X, x ∈ s → IsClosed s

/-- Paper: Lemma E.1.1.4(1), p. 829.
Two distinct points all of whose supersets are closed force the space to be discrete. -/
theorem discreteTopology_of_two_allSupersetsClosed {x y : X} (hxy : x ≠ y)
    (hx : AllSupersetsClosed x) (hy : AllSupersetsClosed y) : DiscreteTopology X := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro z
  rw [← isClosed_compl_iff]
  by_cases hzx : z = x
  · subst hzx
    exact hy _ (by simpa using Ne.symm hxy)
  · exact hx _ (by simpa using Ne.symm hzx)

/-- Paper: Lemma E.1.1.4(1), p. 829.
With two distinct points all of whose supersets are closed, the continuity test holds,
and hence so do the other conditions of Lemma E.1.1.3.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
theorem compactHausdorffContinuityTest_of_two_allSupersetsClosed {x y : X} (hxy : x ≠ y)
    (hx : AllSupersetsClosed x) (hy : AllSupersetsClosed y) :
    HasCompactHausdorffContinuityTest.{u, v} X := by
  have := discreteTopology_of_two_allSupersetsClosed hxy hx hy
  intro Y _ f
  exact ⟨fun hf K g => hf.comp g.continuous, fun _ => continuous_of_discreteTopology⟩

/-- If every set containing `x` is closed, two distinct points of the closure of the complement
of the component of `x` have disjoint open neighbourhoods in `X`. -/
private theorem t2Space_closure_compl_connectedComponent_separation (x : X)
    (hx : AllSupersetsClosed x) {a b : X}
    (ha : a ∈ closure (connectedComponent x)ᶜ) (hb : b ∈ closure (connectedComponent x)ᶜ)
    (hab : a ≠ b) : ∃ U W : Set X, IsOpen U ∧ IsOpen W ∧ a ∈ U ∧ b ∈ W ∧ Disjoint U W := by
  have hop : ∀ c, c ≠ x → IsOpen ({c} : Set X) := fun c hc =>
    isClosed_compl_iff.1 (hx _ (by simpa using Ne.symm hc))
  have hV : closure (connectedComponent x)ᶜ ⊆ (connectedComponent x)ᶜ ∪ {x} :=
    closure_minimal subset_union_left (hx _ (by simp))
  -- a point of `V` other than `x` is separated from `x` by an open set
  have hsep : ∀ c ∈ closure (connectedComponent x)ᶜ, c ≠ x →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ c ∉ U := by
    intro c hc hcx
    have hcZ : c ∉ connectedComponent x := by
      rcases hV hc with h | h
      · exact h
      · exact absurd h hcx
    by_contra hne
    push Not at hne
    have hspec : c ⤳ x := specializes_iff_forall_open.2 fun s hs hxs => hne s hs hxs
    have hsub : closure ({c} : Set X) ⊆ connectedComponent x :=
      (isConnected_singleton.closure).isPreconnected.subset_connectedComponent
        (specializes_iff_mem_closure.1 hspec)
    exact hcZ (hsub (subset_closure rfl))
  by_cases hax : a = x
  · subst hax
    obtain ⟨U, hU, haU, hbU⟩ := hsep b hb (Ne.symm hab)
    exact ⟨U, {b}, hU, hop b (Ne.symm hab), haU, rfl, disjoint_singleton_right.2 hbU⟩
  · by_cases hbx : b = x
    · subst hbx
      obtain ⟨U, hU, hbU, haU⟩ := hsep a ha hax
      exact ⟨{a}, U, hop a hax, hU, rfl, hbU, disjoint_singleton_left.2 haU⟩
    · exact ⟨{a}, {b}, hop a hax, hop b hbx, rfl, rfl, disjoint_singleton.2 hab⟩

/-- If every set containing `x` is closed, the closure of the complement of the component of
`x` is Hausdorff. -/
private theorem t2Space_closure_compl_connectedComponent (x : X) (hx : AllSupersetsClosed x) :
    T2Space ↑(closure (connectedComponent x)ᶜ) := by
  refine ⟨fun a b hab => ?_⟩
  obtain ⟨U, W, hU, hW, haU, hbW, hUW⟩ := t2Space_closure_compl_connectedComponent_separation
    x hx a.2 b.2 (fun h => hab (Subtype.ext h))
  exact ⟨_, _, hU.preimage continuous_subtype_val, hW.preimage continuous_subtype_val, haU, hbW,
    hUW.preimage _⟩

/-- If every set containing `x` is closed, the open subsets of the connected component of `x`
are those that miss `x`, and the whole component. -/
private theorem isOpen_connectedComponent_iff_of_allSupersetsClosed (x : X)
    (hx : AllSupersetsClosed x) (s : Set (connectedComponent x)) :
    IsOpen s ↔ (⟨x, mem_connectedComponent⟩ : connectedComponent x) ∉ s ∨ s = univ := by
  constructor
  · intro hs
    by_cases hxs : (⟨x, mem_connectedComponent⟩ : connectedComponent x) ∈ s
    · right
      have : PreconnectedSpace (connectedComponent x) :=
        isPreconnected_iff_preconnectedSpace.1 isPreconnected_connectedComponent
      have hcl : IsClosed s := by
        have h1 : IsClosed (Subtype.val '' s : Set X) := hx _ ⟨_, hxs, rfl⟩
        have h2 := h1.preimage (continuous_subtype_val (p := (· ∈ connectedComponent x)))
        rwa [Subtype.val_injective.preimage_image] at h2
      rcases isClopen_iff.1 ⟨hcl, hs⟩ with h | h
      · exact absurd (h ▸ hxs) (notMem_empty _)
      · exact h
    · left; exact hxs
  · rintro (h | rfl)
    · rw [isOpen_iff_forall_mem_open]
      intro z hz
      refine ⟨{z}, singleton_subset_iff.2 hz, ?_, rfl⟩
      have hzx : (z : X) ≠ x := fun e => by
        have hz' : z = ⟨x, mem_connectedComponent⟩ := Subtype.ext e
        exact h (hz' ▸ hz)
      have : IsOpen ({(z : X)} : Set X) := isClosed_compl_iff.1 (hx _ (by simpa using Ne.symm hzx))
      have := this.preimage (continuous_subtype_val (p := (· ∈ connectedComponent x)))
      rwa [show (Subtype.val ⁻¹' {(z : X)} : Set (connectedComponent x)) = {z} from by
        ext; simp [Subtype.ext_iff]] at this
    · exact isOpen_univ

section UniquePoint

variable (x : X) (hx : ∀ y : X, AllSupersetsClosed y ↔ y = x)

include hx

/-- Paper: Lemma E.1.1.4(2a), p. 829.
The complement of the unique point all of whose supersets are closed is open. -/
theorem isOpen_compl_singleton_of_unique_allSupersetsClosed : IsOpen ({x}ᶜ : Set X) :=
  isOpen_compl_iff.2 (((hx x).2 rfl) _ rfl)

/-- Paper: Lemma E.1.1.4(2a), p. 829.
The complement of the unique point all of whose supersets are closed is discrete. -/
theorem discreteTopology_compl_singleton_of_unique_allSupersetsClosed :
    DiscreteTopology ↑({x}ᶜ : Set X) := by
  rw [discreteTopology_subtype_iff']
  intro y hy
  refine ⟨{y}, isClosed_compl_iff.1 (((hx x).2 rfl) _ (by simpa using Ne.symm hy)), ?_⟩
  ext z
  simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, hy⟩

/-- Paper: Lemma E.1.1.4(2bi), equation (E.1.1.1), p. 829.
The map from the coproduct of the connected component of the distinguished point and
the closure of its complement, given by the two inclusions, is a quotient map. -/
theorem isQuotientMap_connectedComponent_sum_closure_compl :
    IsQuotientMap (Sum.elim
      (Subtype.val : connectedComponent x → X)
      (Subtype.val : closure ((connectedComponent x)ᶜ) → X)) := by
  have hc : Continuous (Sum.elim
      (Subtype.val : connectedComponent x → X)
      (Subtype.val : closure ((connectedComponent x)ᶜ) → X)) :=
    continuous_subtype_val.sumElim continuous_subtype_val
  refine IsClosedMap.isQuotientMap ?_ hc ?_
  · intro C hC
    have : Sum.elim (Subtype.val : connectedComponent x → X)
        (Subtype.val : closure ((connectedComponent x)ᶜ) → X) '' C =
        Subtype.val '' (Sum.inl ⁻¹' C) ∪ Subtype.val '' (Sum.inr ⁻¹' C) := by
      ext y; simp [Sum.exists]
    rw [this]
    exact (isClosed_connectedComponent.isClosedMap_subtype_val _
        (hC.preimage continuous_inl)).union
      (isClosed_closure.isClosedMap_subtype_val _ (hC.preimage continuous_inr))
  · intro y
    by_cases hy : y ∈ connectedComponent x
    · exact ⟨Sum.inl ⟨y, hy⟩, rfl⟩
    · exact ⟨Sum.inr ⟨y, subset_closure hy⟩, rfl⟩

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is compact. -/
theorem isCompact_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : IsCompact (range g) :=
  isCompact_range g.continuous

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is Hausdorff with its subspace topology. -/
theorem t2Space_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : T2Space ↑(range g) := by
  have := t2Space_closure_compl_connectedComponent x ((hx x).2 rfl)
  infer_instance

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is closed in that closure. -/
theorem isClosed_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : IsClosed (range g) := by
  have := t2Space_closure_compl_connectedComponent x ((hx x).2 rfl)
  exact (isCompact_range g.continuous).isClosed

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The map from a compact Hausdorff probe to its range in the closure of the complement
of the component is a quotient map for the subspace topology. -/
theorem isQuotientMap_rangeFactorization_into_closure_compl_connectedComponent
    (K : CompHaus.{u}) (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) :
    IsQuotientMap (rangeFactorization g) := by
  have := t2Space_closure_compl_connectedComponent x ((hx x).2 rfl)
  have hc : Continuous (rangeFactorization g) := g.continuous.rangeFactorization
  exact hc.isClosedMap.isQuotientMap hc rangeFactorization_surjective

-- TODO(paper-gap): On p. 830 the circle coproduct has no marked point when the
-- connected component is a singleton. A singleton probe covers this case.

/-- Paper: Lemma E.1.1.4(2biii), pp. 829–830.
The connected component of the distinguished point is a quotient of a compact Hausdorff space.
Deviation: The witness can be taken in the carrier universe of the original space. -/
theorem exists_compactHausdorff_quotient_connectedComponent :
    ∃ (K : CompHaus.{w}) (g : K → connectedComponent x), IsQuotientMap g := by
  have hxc := (hx x).2 rfl
  let I := {z : connectedComponent x // (z : X) ≠ x}
  have : WeaklyLocallyCompactSpace (WithDiscreteTopology (I × ℕ)) :=
    ⟨fun p => ⟨{p}, isCompact_singleton, by simp [nhds_discrete]⟩⟩
  let K := CompHaus.of (OnePoint (WithDiscreteTopology (I × ℕ)))
  let x₀ : connectedComponent x := ⟨x, mem_connectedComponent⟩
  let g : K → connectedComponent x := fun p =>
    OnePoint.elim p x₀ fun q : WithDiscreteTopology (I × ℕ) => (q.ofTopology.1 : _)
  refine ⟨K, g, ⟨isCoinducing_iff.2 fun s => ?_, ?_⟩⟩
  · rw [isOpen_connectedComponent_iff_of_allSupersetsClosed x hxc]
    constructor
    · intro hs
      by_contra hn
      push Not at hn
      obtain ⟨hxs, hsu⟩ := hn
      obtain ⟨z, hz⟩ := (ne_univ_iff_exists_notMem _).1 hsu
      have hzx : (z : X) ≠ x := fun e => by
        have hz' : z = ⟨x, mem_connectedComponent⟩ := Subtype.ext e
        exact hz (hz' ▸ hxs)
      have hinf : OnePoint.infty ∈ g ⁻¹' s := hxs
      have hcpt := (OnePoint.isOpen_iff_of_mem hinf).1 hs
      -- the complement contains the infinite set `{⟨z, hzx⟩} × ℕ`
      refine Set.infinite_range_of_injective (f := fun n : ℕ =>
        (WithTopology.toTopology ⊥ ((⟨z, hzx⟩ : I), n) : WithDiscreteTopology (I × ℕ)))
        (fun a b h => by simpa using congrArg (fun q => q.ofTopology.2) h) ?_
      refine hcpt.2.finite_of_discrete |>.subset ?_
      rintro _ ⟨n, rfl⟩
      simpa [g] using hz
    · rintro (h | rfl)
      · rw [OnePoint.isOpen_iff_of_notMem h]
        exact isOpen_discrete _
      · exact isOpen_univ
  · intro z
    by_cases hz : (z : X) = x
    · exact ⟨OnePoint.infty, Subtype.ext hz.symm⟩
    · exact ⟨OnePoint.some (WithTopology.toTopology ⊥ (⟨z, hz⟩, 0)), rfl⟩

/-- Paper: Lemma E.1.1.4(2c), pp. 829–830.
For a space with the distinguished point, the continuity test implies the test by a set of sources.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
theorem compactHausdorffContinuityTestFamily_of_unique_allSupersetsClosed :
    HasCompactHausdorffContinuityTest.{u, v} X →
      HasCompactHausdorffContinuityTestFamily.{u, v} X :=
  ((compactHausdorffTests_tfae X).out 1 2).1

end UniquePoint

/-- Paper: Remark E.1.1.5, p. 830.
The closed point of the Sierpiński trait is its unique point with all supersets closed. -/
theorem allSupersetsClosed_sierpinski_iff (p : Prop) :
    AllSupersetsClosed p ↔ p = False := by
  constructor
  · intro h
    by_contra hp
    have hp' : p = True := by simpa using hp
    have h1 := h {True} (by simp [hp'])
    have h2 : ({True}ᶜ : Set Prop) ∈ 𝓝 False := h1.isOpen_compl.mem_nhds (by simp)
    rw [nhds_false, Filter.mem_top] at h2
    have : True ∈ ({True}ᶜ : Set Prop) := h2 ▸ mem_univ _
    simp at this
  · rintro rfl s hs
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro q hq
    have hq' : q = True := by
      by_contra h
      have h' : q = False := by simpa using h
      exact hq (h' ▸ hs)
    subst hq'
    rw [nhds_true, Filter.mem_pure]
    exact hq

/-- Paper: Remark E.1.1.5, p. 830.
The bouquet glues the closed points of Sierpiński traits at `none`. Each `some i` is
the open point of the trait indexed by `i`.
Deviation: The empty bouquet retains its marked point. -/
@[instance_reducible]
def traitBouquetTopology (I : Type u) : TopologicalSpace (Option I) :=
  generateFrom (range fun i : I ↦ ({some i} : Set (Option I)))

/-- Paper: Remark E.1.1.5, p. 830.
The open sets of the bouquet are the subsets of its open points and the whole space. -/
theorem isOpen_traitBouquetTopology_iff {I : Type u} (s : Set (Option I)) :
    IsOpen[traitBouquetTopology I] s ↔ none ∉ s ∨ s = univ := by
  constructor
  · intro h
    induction h with
    | basic t ht =>
      obtain ⟨i, rfl⟩ := ht
      left; simp
    | univ => right; rfl
    | inter a b _ _ ha hb =>
      rcases ha with ha | rfl
      · left; exact fun h => ha h.1
      · rcases hb with hb | rfl
        · left; exact fun h => hb h.2
        · right; exact univ_inter _
    | sUnion S _ hS =>
      by_cases h : ∃ t ∈ S, t = univ
      · obtain ⟨t, ht, rfl⟩ := h
        right; exact eq_univ_of_univ_subset (subset_sUnion_of_mem ht)
      · left
        rintro ⟨t, ht, hn⟩
        rcases hS t ht with h' | h'
        · exact h' hn
        · exact h ⟨t, ht, h'⟩
  · rintro (h | rfl)
    · have : s = ⋃ i ∈ {i : I | some i ∈ s}, ({some i} : Set (Option I)) := by
        ext o
        cases o with
        | none => simp [h]
        | some i => simp
      rw [this]
      exact @isOpen_biUnion _ _ (traitBouquetTopology I) _ _ fun i _ =>
        GenerateOpen.basic _ ⟨i, rfl⟩
    · exact @isOpen_univ _ (traitBouquetTopology I)

/-- Paper: Remark E.1.1.5, p. 830.
The connected component is homeomorphic to the bouquet indexed by its other points,
with the distinguished point sent to the basepoint and all other points sent to their labels.
Deviation: The bouquet of the empty family is the one-point space. -/
theorem exists_homeomorph_connectedComponent_traitBouquet (x : X)
    (hx : ∀ y : X, AllSupersetsClosed y ↔ y = x) :
    let I := {z : connectedComponent x // (z : X) ≠ x}
    let t := traitBouquetTopology I
    ∃ e : connectedComponent x ≃ₜ WithTopology (Option I) t,
      e ⟨x, mem_connectedComponent⟩ = WithTopology.toTopology t none ∧
        ∀ i : I, e i.val = WithTopology.toTopology t (some i) := by
  intro I t
  classical
  have hxc := (hx x).2 rfl
  let x₀ : connectedComponent x := ⟨x, mem_connectedComponent⟩
  let F : connectedComponent x → Option I := fun z =>
    if h : (z : X) = x then none else some ⟨z, h⟩
  let G : Option I → connectedComponent x := fun o => Option.elim o x₀ Subtype.val
  have hGF : ∀ z, G (F z) = z := fun z => by
    by_cases h : (z : X) = x
    · simp only [F, G, h, dite_true, Option.elim_none]; exact Subtype.ext h.symm
    · simp [F, G, h]
  have hFG : ∀ o, F (G o) = o := fun o => by
    cases o with
    | none => simp [F, G, x₀]
    | some i => simp [F, G, i.2]
  have hF0 : F x₀ = none := by simp [F, x₀]
  let e : connectedComponent x ≃ WithTopology (Option I) t :=
    { toFun := fun z => WithTopology.toTopology t (F z)
      invFun := fun w => G w.ofTopology
      left_inv := fun z => hGF z
      right_inv := fun w => by simp [hFG] }
  refine ⟨{ toEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }, ?_, ?_⟩
  · rw [continuous_def]
    intro s hs
    rw [WithTopology.isOpen_iff, isOpen_traitBouquetTopology_iff] at hs
    rw [isOpen_connectedComponent_iff_of_allSupersetsClosed x hxc]
    rcases hs with h | h
    · left
      change WithTopology.toTopology t (F x₀) ∉ s
      rw [hF0]; exact h
    · right
      ext z
      simp only [mem_preimage, mem_univ, iff_true]
      change F z ∈ WithTopology.toTopology t ⁻¹' s
      rw [h]; trivial
  · rw [continuous_def]
    intro s hs
    rw [isOpen_connectedComponent_iff_of_allSupersetsClosed x hxc] at hs
    rw [WithTopology.isOpen_iff, isOpen_traitBouquetTopology_iff]
    rcases hs with h | rfl
    · left; exact h
    · right; rfl
  · exact congrArg (WithTopology.toTopology t) hF0
  · intro i
    change WithTopology.toTopology t (F i.val) = _
    simp [F, i.2]

end CompactGeneration

-- TODO(paper-gap): On p. 831 the witnessing ordinals form an unbounded class. The
-- minimum exists by minimizing below a witnessing stage. For (2) retain all maps
-- over each source. The discrete case on p. 830 includes the empty space.

/-- Paper: Lemma E.1.1.3, equations (E.1.1.2)–(E.1.1.3), p. 831.
Each nonempty class has a least witnessing stage. The supremum of those stages meets
each class, providing a common bound for collecting witnesses.
Deviation: The rank argument is stated for predicates on `ZFSet` and a universe-small
index type. The least stage is specified by its order property. -/
theorem exists_least_vonNeumannStages {I : Type u} (C : I → ZFSet.{u} → Prop)
    (hC : ∀ i, ∃ z, C i z) :
    ∃ (a : I → Ordinal.{u}) (b : Ordinal.{u}),
      (∀ i, IsLeast {o | ∃ z ∈ ZFSet.vonNeumann o, C i z} (a i)) ∧
        IsLUB (range a) b ∧ (∀ i, ∃ z ∈ ZFSet.vonNeumann b, C i z) := by
  have hne : ∀ i, {o | ∃ z ∈ ZFSet.vonNeumann o, C i z}.Nonempty := fun i => by
    obtain ⟨z, hz⟩ := hC i
    exact ⟨_, z, ZFSet.mem_vonNeumann_succ z, hz⟩
  set a : I → Ordinal.{u} := fun i => sInf {o | ∃ z ∈ ZFSet.vonNeumann o, C i z}
  have hb : BddAbove (range a) := Ordinal.bddAbove_of_small
  refine ⟨a, sSup (range a), fun i => ⟨csInf_mem (hne i), fun o ho => csInf_le' ho⟩,
    isLUB_csSup' hb, fun i => ?_⟩
  obtain ⟨z, hz, hc⟩ := csInf_mem (hne i)
  exact ⟨z, ZFSet.vonNeumann_subset_of_le (le_csSup hb ⟨i, rfl⟩) hz, hc⟩

/-- Paper: Lemma E.1.1.3, equation (E.1.1.4), p. 831.
The coproduct map restricts on each summand to the corresponding probe. -/
def compactHausdorffCoproductMap {I : Type v} {K : I → CompHaus.{u}}
    {X : Type w} [TopologicalSpace X] (g : ∀ i, C(K i, X)) (p : Σ i, K i) : X :=
  g p.1 p.2

/-- Paper: Lemma E.1.1.3, equation (E.1.1.5), p. 831.
The preimage under the coproduct map is the disjoint union of the preimages under the summand maps. -/
theorem compactHausdorffCoproductMap_preimage {I : Type v} {K : I → CompHaus.{u}}
    {X : Type w} [TopologicalSpace X] (g : ∀ i, C(K i, X)) (s : Set X) :
    compactHausdorffCoproductMap g ⁻¹' s = univ.sigma (fun i ↦ g i ⁻¹' s) := by
  ext ⟨i, k⟩
  simp [compactHausdorffCoproductMap]

/-- Paper: Remark E.1.1.6, p. 832.
Scott's rank bound allows a set of witnesses to meet every member of a small indexed family
of nonempty classes. The set consists of the elements of the common stage lying in some class.
Deviation: The witnesses are abstract `ZFSet` elements. The collected set can be empty
when the family is empty. This states the set-existence conclusion of the rank argument. -/
theorem exists_zfSet_meeting_classes {I : Type u} (C : I → ZFSet.{u} → Prop)
    (hC : ∀ i, ∃ z, C i z) :
    ∃ (b : Ordinal.{u}) (S : ZFSet.{u}),
      (∀ z, z ∈ S ↔ z ∈ ZFSet.vonNeumann b ∧ ∃ i, C i z) ∧
        ∀ i, ∃ z ∈ S, C i z := by
  obtain ⟨-, b, -, -, hb⟩ := exists_least_vonNeumannStages C hC
  refine ⟨b, ZFSet.sep (fun z => ∃ i, C i z) (ZFSet.vonNeumann b), fun z => ZFSet.mem_sep,
    fun i => ?_⟩
  obtain ⟨z, hz, hc⟩ := hb i
  exact ⟨z, ZFSet.mem_sep.2 ⟨hz, i, hc⟩, hc⟩

/-- Paper: Definition E.1.1.7(1), p. 832.
Mathlib's compact generation predicate agrees with the equivalent conditions of Lemma E.1.1.3.
Deviation: The predicate uses probes in universe `u`; the test uses targets in universe `v`. -/
theorem uCompactlyGeneratedSpace_iff_continuityTest (X : Type w) [TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u} X ↔ HasCompactHausdorffContinuityTest.{u, v} X := by
  refine ⟨fun _ Y _ f => ⟨fun hf K g => hf.comp g.continuous,
    continuous_from_uCompactlyGeneratedSpace f⟩, fun h => ?_⟩
  have h3 : HasCompactHausdorffOpennessTest.{u} X := ((compactHausdorffTests_tfae X).out 1 3).1 h
  exact uCompactlyGeneratedSpace_of_isOpen fun s hs => (h3 s).2 hs

/-- Paper: Definition E.1.1.7(2), p. 832.
Mathlib's category `CompactlyGenerated` has the compactly generated spaces as objects and
continuous maps as morphisms. Its forgetful functor to topological spaces is fully faithful.
Deviation: Objects have carriers in universe `w` and are tested by probes in universe `u`. -/
theorem compactlyGeneratedToTop_full_faithful :
    (CompactlyGenerated.compactlyGeneratedToTop.{u, w}).Full ∧
      (CompactlyGenerated.compactlyGeneratedToTop.{u, w}).Faithful :=
  ⟨inferInstance, inferInstance⟩

/-- Paper: Remark E.1.1.8, p. 832.
A space is compactly generated exactly when its original topology equals its k-topology.
Deviation: Both sides use the same fixed probe universe `u`. -/
theorem uCompactlyGeneratedSpace_iff_eq_compactlyGenerated
    (X : Type w) [tX : TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u} X ↔ TopologicalSpace.compactlyGenerated.{u} X = tX :=
  ⟨fun _ => (eq_compactlyGenerated (X := X)).symm, fun h => ⟨h.ge⟩⟩

/-- Paper: Example E.1.1.9, p. 832.
The cocountable topology is generated by the empty set and complements of countable sets. -/
@[instance_reducible]
def cocountableTopology (X : Type w) : TopologicalSpace X :=
  generateFrom {s | s = ∅ ∨ sᶜ.Countable}

/-- Paper: Example E.1.1.9, p. 832.
The closed sets in the cocountable topology are the countable sets and the whole space. -/
theorem isClosed_cocountableTopology_iff {X : Type w} (s : Set X) :
    IsClosed[cocountableTopology X] s ↔ s = univ ∨ s.Countable := by
  have key : ∀ t : Set X, IsOpen[cocountableTopology X] t ↔ t = ∅ ∨ tᶜ.Countable := by
    intro t
    constructor
    · intro h
      induction h with
      | basic t ht => exact ht
      | univ => right; simp
      | inter a b _ _ ha hb =>
        rcases ha with rfl | ha
        · left; exact empty_inter _
        rcases hb with rfl | hb
        · left; exact inter_empty _
        right; rw [compl_inter]; exact ha.union hb
      | sUnion S _ hS =>
        by_cases h : ∃ t ∈ S, tᶜ.Countable
        · obtain ⟨t, ht, hc⟩ := h
          right; exact hc.mono (compl_subset_compl.2 (subset_sUnion_of_mem ht))
        · left
          rw [sUnion_eq_empty]
          intro t ht
          exact (hS t ht).resolve_right fun hc => h ⟨t, ht, hc⟩
    · intro h; exact GenerateOpen.basic _ h
  rw [← @isOpen_compl_iff X _ (cocountableTopology X), key, compl_compl, compl_empty_iff]

private theorem compactlyGenerated_cocountableTopology_eq_bot_countable {X : Type w} {S : Set X}
    (hS : @IsCompact X (cocountableTopology X) S) : S.Countable := by
  let := cocountableTopology X
  have hcl : ∀ t : Set X, t.Countable → IsClosed t := fun t ht =>
    (isClosed_cocountableTopology_iff t).2 (Or.inr ht)
  by_contra hc
  have hinf : S.Infinite := fun hf => hc hf.countable
  set T : Set X := range (fun n => (hinf.natEmbedding _ n : X)) with hT
  have hTc : T.Countable := countable_range _
  have hTS : T ⊆ S := by rintro _ ⟨n, rfl⟩; exact (hinf.natEmbedding _ n).2
  have hTd : IsDiscrete T := isDiscrete_iff_forall_mem_exists_isClosed.2 fun t ht =>
    ⟨t, hcl t (hTc.mono ht), inter_eq_left.2 ht⟩
  have hTf : T.Finite := (hS.of_isClosed_subset (hcl T hTc) hTS).finite hTd
  have : (range fun n => (hinf.natEmbedding _ n : X)).Infinite :=
    infinite_range_of_injective fun a b h => (hinf.natEmbedding _).injective (Subtype.ext h)
  exact this hTf

/-- Paper: Example E.1.1.9, p. 832.
The k-topology of an uncountable set with the cocountable topology is discrete.
Deviation: The k-topology is formed with probes in a fixed universe `u`. -/
theorem compactlyGenerated_cocountableTopology_eq_bot (X : Type w) [Uncountable X] :
    @TopologicalSpace.compactlyGenerated.{u, w} X (cocountableTopology X) = ⊥ := by
  let := cocountableTopology X
  rw [eq_bot_iff]
  intro s _
  rw [TopologicalSpace.compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff]
  rintro ⟨K, g⟩
  have hc : (range g).Countable :=
    compactlyGenerated_cocountableTopology_eq_bot_countable (isCompact_range g.continuous)
  have : (g : K → X) ⁻¹' s = ((g : K → X) ⁻¹' (sᶜ ∩ range g))ᶜ := by
    ext k; simp
  change IsOpen ((g : K → X) ⁻¹' s)
  rw [this, isOpen_compl_iff]
  exact ((isClosed_cocountableTopology_iff _).2 (Or.inr (hc.mono inter_subset_right))).preimage
    g.continuous

/-- Paper: Example E.1.1.9, p. 832.
An uncountable set with the cocountable topology is not compactly generated.
Deviation: The compact generation predicate uses probes in a fixed universe `u`. -/
theorem not_uCompactlyGeneratedSpace_cocountableTopology (X : Type w) [Uncountable X] :
    ¬ @UCompactlyGeneratedSpace.{u, w} X (cocountableTopology X) := by
  let := cocountableTopology X
  intro h
  have h1 : cocountableTopology X = ⊥ := by
    rw [← compactlyGenerated_cocountableTopology_eq_bot.{u} X]
    exact eq_compactlyGenerated
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have : DiscreteTopology X := ⟨h1⟩
  have h2 : IsClosed ({x}ᶜ : Set X) := isClosed_discrete _
  rcases (isClosed_cocountableTopology_iff _).1 h2 with h3 | h3
  · exact (h3 ▸ mem_univ x : x ∈ ({x}ᶜ : Set X)) rfl
  · exact not_countable_univ (by simpa using h3.union (countable_singleton x))

end RiemannMasullo
