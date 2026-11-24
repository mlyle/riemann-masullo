module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.InnerProductSpace.Calculus

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Covering.Quotient
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Pi
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import all RiemannMasullo.Ch02_AdelicTheta.Sec2b
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.RingTheory.PicardGroup

/-!
# Schwartz–Bruhat topologies on elementary groups and idele class groups

Masullo, §D.1.10, pp. 783–792.
-/

@[expose] public noncomputable section

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Distributions ENNReal FourierTransform NNReal NumberField.AdeleRing Real SchwartzMap

namespace RiemannMasullo

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F

section IdeleInsertion

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "SUnits" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ

-- TODO(paper-gap): The sentence before (D.1.10.1) includes the outside-S integer
-- factors in A_{F,S}, although the insertion formula and (A.1.5.1) separate them.

/-- Paper: (D.1.10.1), p. 783. Take units of the subring of adeles integral
outside S and include them into the global idele group.
Deviation: Appendix A's integral-outside-S subring already includes the outside
factors. The finite set records the finite part of S. -/
def integralIdeleInsertion : (integralAdelesOutside F S)ˣ →* 𝕀[F] :=
  Units.map (integralAdelesOutside F S).subtype.toMonoidHom

/-- Paper: (D.1.10.1), p. 783. An idele in the image is a unit at every finite place
outside S, and every such idele occurs.
Deviation: Sanity check on the domain of insertion, phrased using the integral
coordinates of an idele and its inverse. -/
theorem mem_range_integralIdeleInsertion (g : 𝕀[F]) :
    g ∈ range (integralIdeleInsertion F S) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        g.val.2 v ∈ v.adicCompletionIntegers F ∧
          g.inv.2 v ∈ v.adicCompletionIntegers F := by
  have hmem (a : 𝔸[F]) :
      a ∈ integralAdelesOutside F S ↔
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  constructor
  · rintro ⟨u, rfl⟩ v hv
    exact ⟨(hmem _).mp u.val.property v hv, (hmem _).mp u.inv.property v hv⟩
  · intro hg
    let u : (integralAdelesOutside F S)ˣ :=
      ⟨⟨g.val, (hmem _).mpr fun v hv ↦ (hg v hv).1⟩,
        ⟨g.inv, (hmem _).mpr fun v hv ↦ (hg v hv).2⟩,
        Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩
    exact ⟨u, Units.ext rfl⟩

/-- Paper: Lemma D.1.10.1(1), p. 784. Insertion from the full S-stage is a continuous
injective open map. -/
theorem integralIdeleInsertion_isOpenEmbedding :
    IsOpenEmbedding (integralIdeleInsertion F S) := by
  have hopen : IsOpen (integralAdelesOutside F S : Set 𝔸[F]) := by
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F)
      (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))
      (p := fun v ↦ v ∉ S)).preimage continuous_snd
  have h := hopen.isOpenEmbedding_subtypeVal
  have he : IsEmbedding (integralIdeleInsertion F S) := h.isEmbedding.units_map
  have ho : IsOpenMap (integralIdeleInsertion F S) :=
    Units.isOpenMap_map h.injective h.isOpenMap
  exact ⟨he, ho.isOpen_range⟩

/-- Paper: Lemma D.1.10.1(1), p. 784. The diagonal S-unit actions on the stage and
on the global ideles are continuous, and insertion intertwines left translation.
Deviation: The target diagonal is evaluated by mapping S-units to F-units. -/
theorem integralIdeleInsertion_equivariant :
    letI : TopologicalSpace SUnits := ⊥
    let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
    let e := (IdeleGroup.unitEmbedding (𝓞 F) F).comp
      (Units.map (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F).val.toRingHom.toMonoidHom)
    Continuous (fun x : SUnits × (integralAdelesOutside F S)ˣ ↦ d x.1 * x.2) ∧
    Continuous (fun x : SUnits × 𝕀[F] ↦ e x.1 * x.2) ∧
    ∀ u g, integralIdeleInsertion F S (d u * g) =
      e u * integralIdeleInsertion F S g := by
  let : TopologicalSpace SUnits := ⊥
  let : DiscreteTopology SUnits := discreteTopology_bot _
  intro d e
  have hd : Continuous d := continuous_of_discreteTopology
  have he : Continuous e := continuous_of_discreteTopology
  refine ⟨(hd.comp continuous_fst).mul continuous_snd,
    (he.comp continuous_fst).mul continuous_snd, ?_⟩
  intro u g
  rw [map_mul]
  exact congrArg (· * integralIdeleInsertion F S g) (Units.ext rfl)

-- TODO(paper-gap): D.1.10.1(2) names only GL₁(A_{F,S}). With the finite-product
-- convention of (A.1.5.1), inserting 1 off S misses ideles with infinitely many
-- nonidentity unit coordinates. The colimit below uses the full stages of (D.1.10.1).

/-- Paper: Lemma D.1.10.1(2), p. 784. Images of the full S-stages increase
with S and exhaust the global ideles.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_exhaustive :
    Monotone (fun T : Finset (HeightOneSpectrum (𝓞 F)) ↦
      range (integralIdeleInsertion F T)) ∧
    ∀ g : 𝕀[F], ∃ T, g ∈ range (integralIdeleInsertion F T) := by
  constructor
  · intro U T hUT g hg
    apply (mem_range_integralIdeleInsertion F T g).2
    intro v hv
    exact (mem_range_integralIdeleInsertion F U g).1 hg v (fun h ↦ hv (hUT h))
  · intro g
    have hfinite := Filter.eventually_cofinite.mp
      (g.val.2.cofinite_mem_adicCompletionIntegers.and
        g.inv.2.cofinite_mem_adicCompletionIntegers)
    refine ⟨hfinite.toFinset, (mem_range_integralIdeleInsertion F _ g).2 ?_⟩
    intro v hv
    exact not_not.mp (fun h ↦ hv (hfinite.mem_toFinset.mpr h))

/- The subring of adeles integral outside a finite set of finite places is open,
being the product of the infinite adeles with the cofinite distinguished sets of
the finite adeles. Used to make each full stage an open subgroup of the ideles. -/
private theorem isOpen_integralAdelesOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralAdelesOutside F S : Set 𝔸[F]) := by
  simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
  exact (isOpen_restrictedProduct_forall_mem (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ
    (fun v _ ↦ Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd

/- The insertion from the full stage into the ideles is continuous, injective and open
onto its image, and its image is the open set of ideles integral outside `S` with
integral inverse (helper for Lemma D.1.10.1(1), p. 784, and (2), p. 784). -/
private theorem integralIdeleInsertion_continuous_aux (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (integralIdeleInsertion F S) :=
  Units.continuous_map continuous_subtype_val

private theorem integralIdeleInsertion_isOpenEmbedding_aux
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpenEmbedding (integralIdeleInsertion F S) := by
  have hemb : IsEmbedding ((integralAdelesOutside F S).subtype.toMonoidHom) :=
    Topology.IsEmbedding.subtypeVal
  exact IsOpenEmbedding.of_isEmbedding_isOpenMap
    (Topology.IsEmbedding.units_map hemb)
    (Units.isOpenMap_map hemb.injective
      ((isOpen_integralAdelesOutside F S).isOpenEmbedding_subtypeVal.isOpenMap))

private theorem isOpen_range_integralIdeleInsertion_aux
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (Set.range (integralIdeleInsertion F S)) := by
  have hmem (a : 𝔸[F]) : a ∈ integralAdelesOutside F S ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  have heq : Set.range (integralIdeleInsertion F S) =
      (fun g : 𝕀[F] ↦ g.val) ⁻¹' (integralAdelesOutside F S : Set 𝔸[F]) ∩
        (fun g : 𝕀[F] ↦ g.inv) ⁻¹' (integralAdelesOutside F S : Set 𝔸[F]) := by
    ext g
    rw [mem_inter_iff, mem_preimage, mem_preimage, mem_range_integralIdeleInsertion F S g]
    constructor
    · intro h
      exact ⟨(hmem _).mpr fun v hv ↦ (h v hv).1, (hmem _).mpr fun v hv ↦ (h v hv).2⟩
    · intro h v hv
      exact ⟨(hmem _).mp h.1 v hv, (hmem _).mp h.2 v hv⟩
  rw [heq]
  exact ((isOpen_integralAdelesOutside F S).preimage Units.continuous_val).inter
    ((isOpen_integralAdelesOutside F S).preimage Units.continuous_coe_inv)

/- Every idele is integral outside a finite set of finite places with integral inverse,
so it lies in the image of the insertion from that stage (helper for the exhaustiveness
part of Lemma D.1.10.1(2), p. 784). -/
private theorem integralIdeleInsertion_exhaustive_aux (g : 𝕀[F]) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), g ∈ Set.range (integralIdeleInsertion F T) := by
  classical
  have hboth : ∀ᶠ v in Filter.cofinite,
      g.val.2 v ∈ v.adicCompletionIntegers F ∧ g.inv.2 v ∈ v.adicCompletionIntegers F := by
    filter_upwards [g.val.2.2, g.inv.2.2] with v h1 h2
    exact ⟨h1, h2⟩
  have hfin := Filter.eventually_cofinite.mp hboth
  refine ⟨hfin.toFinset, ?_⟩
  rw [mem_range_integralIdeleInsertion]
  intro v hv
  rw [hfin.mem_toFinset] at hv
  simp only [mem_setOf_eq, not_not] at hv
  exact hv

/-- Paper: Lemma D.1.10.1(2), p. 784. The topology on the union of the full S-stages
is final for their insertions. Their transition maps are the inclusions of the images.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_finalTopology (U : Set 𝕀[F]) :
    IsOpen U ↔ ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      IsOpen (integralIdeleInsertion F T ⁻¹' U) := by
  constructor
  · intro hU T
    exact hU.preimage (integralIdeleInsertion_continuous_aux F T)
  · intro h
    have heq : U = ⋃ T : Finset (HeightOneSpectrum (𝓞 F)),
        integralIdeleInsertion F T '' (integralIdeleInsertion F T ⁻¹' U) := by
      ext g
      simp only [mem_iUnion, mem_image, mem_preimage]
      constructor
      · intro hg
        obtain ⟨T, hu⟩ := integralIdeleInsertion_exhaustive_aux F g
        obtain ⟨u, rfl⟩ := hu
        exact ⟨T, u, mem_preimage.mpr hg, rfl⟩
      · rintro ⟨T, u, hu, rfl⟩
        exact hu
    rw [heq]
    exact isOpen_iUnion fun T ↦
      IsOpenEmbedding.isOpenMap (integralIdeleInsertion_isOpenEmbedding_aux F T)
        (integralIdeleInsertion F T ⁻¹' U) (h T)

/-- Paper: (D.1.10.2), p. 784. The composite of insertion with the global class map
kills the diagonal S-units. -/
theorem integralIdeleInsertion_descends :
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range ≤
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
        (integralIdeleInsertion F S)).ker := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rintro _ ⟨u, rfl⟩
  exact ⟨Units.map (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F).val.toRingHom.toMonoidHom u,
    Units.ext rfl⟩

/-- Paper: (D.1.10.2), p. 784. Insert an S-idele representative and take its global
idele class. The source is Appendix A's S-idele class group. -/
def sIdeleClassInsertion : SIdeleClassGroup F S →* C[F] :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
      (integralIdeleInsertion F S)) (integralIdeleInsertion_descends F S)

/-- Paper: (D.1.10.2), p. 784. The class insertion is determined by insertion on
representatives.
Deviation: Sanity check stated as the unique descent of the representative map. -/
theorem sIdeleClassInsertion_unique :
    (∀ u : (integralAdelesOutside F S)ˣ,
      sIdeleClassInsertion F S (QuotientGroup.mk u) =
        QuotientGroup.mk (integralIdeleInsertion F S u)) ∧
    ∀ j : SIdeleClassGroup F S →* C[F],
      (∀ u : (integralAdelesOutside F S)ˣ,
        j (QuotientGroup.mk u) = QuotientGroup.mk (integralIdeleInsertion F S u)) →
      j = sIdeleClassInsertion F S :=
  ⟨fun _ ↦ rfl, fun _ hj ↦ QuotientGroup.monoidHom_ext _ (MonoidHom.ext hj)⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. The induced map of class groups is
continuous, injective and open. -/
theorem sIdeleClassInsertion_isOpenEmbedding : IsOpenEmbedding (sIdeleClassInsertion F S) := by
  let D := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  have hsource := QuotientGroup.isOpenQuotientMap_mk (N := D)
  have htarget := QuotientGroup.isOpenQuotientMap_mk (N := P)
  have hinsertion := integralIdeleInsertion_isOpenEmbedding F S
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hsource.continuous_comp_iff.mp (htarget.continuous.comp hinsertion.continuous)) ?_
    (hsource.isOpenMap_iff.mpr (htarget.isOpenMap.comp hinsertion.isOpenMap))
  apply (QuotientGroup.injective_lift_iff _ _ (integralIdeleInsertion_descends F S)).2
  refine le_antisymm (integralIdeleInsertion_descends F S) ?_
  intro g hg
  change (QuotientGroup.mk (s := P) (integralIdeleInsertion F S g)) = 1 at hg
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hg
  have hval : algebraMap F 𝔸[F] u.val = g.val.val := congrArg Units.val hu
  have hinv : algebraMap F 𝔸[F] u.inv = g.inv.val := congrArg Units.inv hu
  -- The diagonal field element and its inverse are both S-integers.
  let x : SUnits :=
    ⟨⟨u.val, (diagonal_mem_integralAdelesOutside F S _).mp (hval.symm ▸ g.val.property)⟩,
      ⟨u.inv, (diagonal_mem_integralAdelesOutside F S _).mp (hinv.symm ▸ g.inv.property)⟩,
      Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
  exact ⟨x, hinsertion.injective (Units.ext hval)⟩

/-- The ideal classes of ideles that are units outside S are precisely the classes
that become trivial over the S-integers. -/
private theorem map_range_integralIdeleInsertion (p : 𝕀[F] →* CommRing.Pic (𝓞 F))
    (hp : ∀ g, p g = ideleIdealClass F g) :
    (integralIdeleInsertion F S).range.map p =
      (CommRing.Pic.mapAlgebra (𝓞 F) (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)).ker := by
  classical
  let A := Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
  let m := CommRing.Pic.mapAlgebra (𝓞 F) A
  ext c
  change c ∈ (integralIdeleInsertion F S).range.map p ↔ m c = 1
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [hp]
    exact sIdele_ideal_class_trivial F S u
  · intro hc
    have h := picard_localization_exact F ∅ S (Finset.empty_subset S)
    dsimp only at h
    rw [Finset.sdiff_empty] at h
    obtain ⟨j, _, hexact, _, hj⟩ := h
    let A₀ := Set.integer
      ((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))) F
    let m₀ := CommRing.Pic.mapAlgebra (𝓞 F) A₀
    have hc₀ := hc
    unfold m at hc₀
    rw [← CommRing.Pic.mapRingHom_algebraMap] at hc₀
    obtain ⟨z, hz⟩ := (hexact (m₀ c)).mp (by
      rw [show m₀ c = CommRing.Pic.mapRingHom (algebraMap (𝓞 F) A₀) c by
        rw [CommRing.Pic.mapRingHom_algebraMap],
        CommRing.Pic.mapRingHom_mapRingHom]
      exact hc₀)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    choose x hx using fun v : S ↦ QuotientGroup.mk_surjective (y v)
    have hy : (fun v : S ↦ QuotientGroup.mk (x v)) = y := funext hx
    rw [← hy, hj] at hz
    let a (v : S) := IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (x v)
    have ha (v : S) : a v ∈ (integralIdeleInsertion F S).range := by
      apply (mem_range_integralIdeleInsertion F S _).mpr
      intro w hw
      have hne : w ≠ v.val := fun e ↦ hw (e.symm ▸ v.property)
      constructor
      · change Pi.mulSingle v.val (x v).val w ∈ w.adicCompletionIntegers F
        rw [Pi.mulSingle_eq_of_ne hne]
        exact one_mem _
      · change ((a v)⁻¹).val.2 w ∈ w.adicCompletionIntegers F
        dsimp only [a]
        rw [← map_inv]
        change Pi.mulSingle v.val ((x v)⁻¹).val w ∈ w.adicCompletionIntegers F
        rw [Pi.mulSingle_eq_of_ne hne]
        exact one_mem _
    refine ⟨∏ v, a v, (integralIdeleInsertion F S).range.prod_mem (fun v _ ↦ ha v), ?_⟩
    rw [map_prod]
    calc
      (∏ v, p (a v)) = ∏ v, localIdealClass F v.val (x v) :=
        Finset.prod_congr rfl fun v _ ↦ (hp _).trans (ideleIdealClass_ofAdicCompletion F _ _)
      _ = c := by
        -- The base change to the empty stage is injective: its integer ring is the base ring.
        have hA : A₀ = ⊥ := by simp [A₀]
        let e := (Subalgebra.equivOfEq _ _ hA).trans
          (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F))
        have he : e.toRingHom.comp (algebraMap (𝓞 F) _) = RingHom.id (𝓞 F) :=
          RingHom.ext fun r ↦ (e.commutes r).trans (Algebra.algebraMap_self_apply r)
        have hleft : LeftInverse (CommRing.Pic.mapRingHom e.toRingHom) m₀ := by
          intro d
          dsimp only [m₀]
          rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom,
            he, CommRing.Pic.mapRingHom_id_apply]
        exact hleft.injective hz

/-- Paper: Lemma D.1.10.1(3), p. 784. The quotient by the image of the S-idele
classes is isomorphic to the finite Picard group of the S-integer ring. -/
theorem sIdeleClassInsertion_cokernel :
    Nonempty ((C[F] ⧸ (sIdeleClassInsertion F S).range) ≃*
      CommRing.Pic (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)) ∧
    Finite (C[F] ⧸ (sIdeleClassInsertion F S).range) := by
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let U := (integralIdeleInsertion F S).range
  let A := Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
  let m := CommRing.Pic.mapAlgebra (𝓞 F) A
  let : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
  obtain ⟨p, hp, _, hexact, hquot⟩ := idele_ideal_class_exact F
  have hpker : p.ker = P ⊔ (integralIdeleInsertion F ∅).range := by
    rw [hexact.monoidHom_ker_eq, Subgroup.range_subtype]
    rfl
  have hU : (integralIdeleInsertion F ∅).range ≤ U :=
    (integralIdeleInsertion_exhaustive F).1 (Finset.empty_subset S)
  have hk : (m.comp p).ker = P ⊔ U := by
    rw [← MonoidHom.comap_ker, ← map_range_integralIdeleInsertion F S p hp,
      Subgroup.comap_map_eq, hpker, ← sup_left_comm, sup_eq_left.mpr hU, sup_comm]
  have hP : P ≤ (m.comp p).ker := hk.symm ▸ le_sup_left
  let q := QuotientGroup.lift P (m.comp p) hP
  have hq : Surjective q := QuotientGroup.lift_surjective_of_surjective P _
    ((picMapAlgebra_surjective_of_isLocalization
      (Localization.submonoid (S : Set (HeightOneSpectrum (𝓞 F)))) A).comp hquot.surjective) hP
  have hker : (sIdeleClassInsertion F S).range = q.ker := by
    change (sIdeleClassInsertion F S).range = (QuotientGroup.lift P (m.comp p) hP).ker
    rw [QuotientGroup.ker_lift, hk, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    change (sIdeleClassInsertion F S).range = (integralIdeleInsertion F S).range.map _
    rw [← MonoidHom.range_comp]
    change (sIdeleClassInsertion F S).range =
      ((sIdeleClassInsertion F S).comp (QuotientGroup.mk' _)).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      Subgroup.map_top]
  let e := QuotientGroup.liftEquiv _ hq hker
  have : Finite (CommRing.Pic A) := (sIdeleClassGroup_finiteness F S).2.2.2.2.2
  exact ⟨⟨e⟩, Finite.of_injective e e.injective⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. Insertion restricts to a topological
group isomorphism between the identity components. -/
theorem sIdeleClassInsertion_connectedComponent :
    ∃ e : Subgroup.connectedComponentOfOne (SIdeleClassGroup F S) ≃ₜ*
        Subgroup.connectedComponentOfOne C[F],
      ∀ x, (e x).val = sIdeleClassInsertion F S x.val := by
  let f := sIdeleClassInsertion F S
  let A := Subgroup.connectedComponentOfOne (SIdeleClassGroup F S)
  let B := Subgroup.connectedComponentOfOne C[F]
  have hf : IsOpenEmbedding f := sIdeleClassInsertion_isOpenEmbedding F S
  have hrange : IsClopen (f.range : Set C[F]) :=
    ⟨f.range.isClosed_of_isOpen hf.isOpen_range, hf.isOpen_range⟩
  have hB : (B : Set C[F]) ⊆ range f := hrange.connectedComponent_subset f.range.one_mem
  have hpre : IsPreconnected (f ⁻¹' (B : Set C[F])) := by
    apply hf.isEmbedding.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hB]
    exact isPreconnected_connectedComponent
  have hpreA : f ⁻¹' (B : Set C[F]) ⊆ A :=
    hpre.subset_connectedComponent (show f 1 ∈ B from (map_one f).symm ▸ B.one_mem)
  have hmap (x : A) : f x.val ∈ B := by
    change f x.val ∈ connectedComponent (1 : C[F])
    simpa only [map_one] using hf.continuous.mapsTo_connectedComponent 1 x.property
  let g : A →* B := (f.comp A.subtype).codRestrict B hmap
  have hg : IsEmbedding g :=
    (hf.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict (B : Set C[F]) hmap
  have hsurj : Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hB y.property
    exact ⟨⟨x, hpreA (show f x ∈ B from hx.symm ▸ y.property)⟩, Subtype.ext hx⟩
  let e := MulEquiv.ofBijective g ⟨hg.injective, hsurj⟩
  exact ⟨{ e, e.toEquiv.toHomeomorphOfIsInducing hg.isInducing with }, fun _ ↦ rfl⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. For all sufficiently large finite sets the
insertion is surjective, and hence is an isomorphism by openness and injectivity. -/
theorem sIdeleClassInsertion_eventually_surjective :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ U, T ⊆ U →
      Surjective (sIdeleClassInsertion F U) := by
  classical
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let stage (U : Finset (HeightOneSpectrum (𝓞 F))) := (sIdeleClassInsertion F U).range
  have hstage (U : Finset (HeightOneSpectrum (𝓞 F))) :
      (stage U : Set C[F]) = q '' range (integralIdeleInsertion F U) := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact ⟨_, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk u, rfl⟩
  obtain ⟨hmono, hexhaust⟩ := integralIdeleInsertion_exhaustive F
  have hmonotone : Monotone (fun U ↦ (stage U : Set C[F])) := by
    intro U V hUV
    change (stage U : Set C[F]) ⊆ stage V
    rw [hstage U, hstage V]
    exact image_mono (hmono hUV)
  have hcover (c : C[F]) : c ∈ ⋃ U, (stage U : Set C[F]) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
    obtain ⟨U, hg⟩ := hexhaust g
    exact mem_iUnion.mpr ⟨U, (hstage U).symm ▸ mem_image_of_mem q hg⟩
  have hcompact : IsCompact ((ideleClassNorm F).ker : Set C[F]) :=
    isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness F).2.1
  obtain ⟨T, hT⟩ := hcompact.elim_directed_cover (fun U ↦ (stage U : Set C[F]))
    (fun U ↦ (sIdeleClassInsertion_isOpenEmbedding F U).isOpen_range)
    (fun c _ ↦ hcover c)
    (fun U V ↦ ⟨U ∪ V, hmonotone Finset.subset_union_left, hmonotone Finset.subset_union_right⟩)
  refine ⟨T, fun U hTU c ↦ ?_⟩
  obtain ⟨j, _, hjNorm, hjRep⟩ := sIdeleClassGroup_openEmbedding F U
  have hj : j = sIdeleClassInsertion F U := (sIdeleClassInsertion_unique F U).2 j hjRep
  obtain ⟨x, hx⟩ := (sIdeleClassNorm_descent F U).2.2.2.1 (ideleClassNorm F c)
  have hxc : ideleClassNorm F (j x) = ideleClassNorm F c := (hjNorm x).trans hx
  have hdiv : c / j x ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_div, hxc, div_self']
  have hmem : c / j x ∈ stage U := hmonotone hTU (hT hdiv)
  have hxmem : j x ∈ stage U := by
    rw [hj]
    exact ⟨x, rfl⟩
  exact div_mul_cancel c (j x) ▸ (stage U).mul_mem hmem hxmem

end IdeleInsertion

section SchwartzTopologies

/-- Paper: Proposition D.1.10.2, p. 784. A family of extended values generates
the topology when its values are exactly those of real generating seminorms.
Deviation: This common formulation also records finiteness of all the values. -/
def GeneratesSeminormTopology {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (v : ι → E → ℝ≥0∞) : Prop :=
  ∃ P : ι → Seminorm ℂ E, WithSeminorms P ∧ ∀ i f, ENNReal.ofReal (P i f) = v i f

/-- Paper: Proposition D.1.10.2, p. 784. Boundedness is equivalent to an upper bound
for the values of each generating seminorm on the set.
Deviation: Sanity check on the topology formulation, stated with finite bounds. -/
theorem GeneratesSeminormTopology.isVonNBounded_iff
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {v : ι → E → ℝ≥0∞} (hv : GeneratesSeminormTopology v) (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, v i f ≤ (C : ℝ≥0∞) := by
  obtain ⟨P, hP, hvalues⟩ := hv
  simp_rw [hP.isVonNBounded_iff_seminorm_bounded, ← hvalues, ENNReal.ofReal_le_coe]
  constructor
  · intro h i
    obtain ⟨r, hr, hbound⟩ := h i
    exact ⟨⟨r, hr.le⟩, fun f hf ↦ (hbound f hf).le⟩
  · intro h i
    obtain ⟨C, hbound⟩ := h i
    exact ⟨(C : ℝ) + 1, by positivity, fun f hf ↦ lt_of_le_of_lt (hbound f hf) (lt_add_one _)⟩

/-- Paper: Proposition D.1.10.2, p. 784. A family of function transforms gives a
generating Lᵖ family if the transforms belong to Lᵖ and their norms generate the topology.
Deviation: Membership is explicit so the extended norm cannot hide a measurability
or integrability condition. -/
def GeneratesLpSeminorms {E ι X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (u : ι → E → X → ℂ) : Prop :=
  (∀ i f, MemLp (u i f) p μ) ∧
    GeneratesSeminormTopology (fun i f ↦ eLpNorm (u i f) p μ)

/-- Paper: Proposition D.1.10.2, p. 784. Bounds on each Lᵖ norm characterize
bounded sets when the Lᵖ family generates.
Deviation: Sanity check stated in terms of the actual extended norms. -/
theorem GeneratesLpSeminorms.isVonNBounded_iff
    {E ι X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} {u : ι → E → X → ℂ}
    (h : GeneratesLpSeminorms μ p u) (B : Set E) :
    IsVonNBounded ℂ B ↔
      ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, eLpNorm (u i f) p μ ≤ (C : ℝ≥0∞) := by
  exact h.2.isVonNBounded_iff B

/-- Paper: (D.1.10.3), p. 784. Apply the nth derivative, Fourier transform,
and then apply the mth derivative. -/
def realSchwartzFourierDeriv (m n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[m] (𝓕 ((SchwartzMap.derivCLM ℂ ℂ)^[n] f))

/-- Paper: (D.1.10.3), p. 784. With both differentiation orders zero only
the Fourier transform remains.
Deviation: Sanity check on the differential orders. -/
theorem realSchwartzFourierDeriv_zero (f : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv 0 0 f = 𝓕 f := by
  rfl

section RealSchwartzFourierLp

open LineDeriv MeasureTheory.Measure SchwartzMap Complex Filter

/-! ### Iterated derivative and monomial multiplication on the real Schwartz space -/

/-- The `n`-th iterated derivative of a Schwartz map is the `n`-th iterated derivative
of its underlying function. -/
private theorem coe_derivIterate (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) x = iteratedDeriv n (f : ℝ → ℂ) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hfun : ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) =
        iteratedDeriv n (f : ℝ → ℂ) := funext ih
    rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, hfun, iteratedDeriv_succ]

/-- Iterating the multiplication-by-`x` operator gives multiplication by `x ^ j`. -/
private theorem smulLeftIterate (j : ℕ) (h : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j] h =
      SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ j) h := by
  induction j with
  | zero =>
    have h1 : (fun x : ℝ ↦ (x : ℂ) ^ 0) = (fun _ : ℝ ↦ (1 : ℂ)) := by funext x; simp
    rw [h1, SchwartzMap.smulLeftCLM_const]
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have hgrowth : (fun x : ℝ ↦ (x : ℂ) ^ j).HasTemperateGrowth := by fun_prop
    have hgrowth1 : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := by fun_prop
    have heq : ((fun x : ℝ ↦ (x : ℂ)) * (fun x : ℝ ↦ (x : ℂ) ^ j)) =
        fun x : ℝ ↦ (x : ℂ) ^ (j + 1) := by
      funext x; simp [pow_succ, mul_comm]
    rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply hgrowth1 hgrowth, heq]

/-! ### The Fourier transform turns monomials into derivatives -/

/-- `∂_{1}` on one real variable is the ordinary derivative. -/
private theorem lineDerivOp_one_eq_derivCLM (u : 𝓢(ℝ, ℂ)) :
    ∂_{(1:ℝ)} u = (SchwartzMap.derivCLM ℂ ℂ) u := by
  ext1 x
  have hd : Differentiable ℝ (u : ℝ → ℂ) := u.differentiable
  have h1 : (fderiv ℝ (u : ℝ → ℂ) x) 1 = deriv (u : ℝ → ℂ) x :=
    (hd x).hasFDerivAt.hasDerivAt.deriv
  rw [lineDerivOp_apply_eq_fderiv]
  show (fderiv ℝ (u : ℝ → ℂ) x) 1 = _
  rw [h1]
  rfl

/-- Differentiating a Fourier transform is the Fourier transform of multiplication
by `-(2 * Real.pi * I) * x`. -/
private theorem fourier_mul_step (g : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.derivCLM ℂ ℂ) (𝓕 g) =
      (-(2 * Real.pi * Complex.I)) • 𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g) := by
  have hgrowth : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := by fun_prop
  have hstep := SchwartzMap.fourierInv_lineDerivOp_eq (𝓕 g) (1 : ℝ)
  rw [lineDerivOp_one_eq_derivCLM] at hstep
  rw [FourierTransform.fourierInv_fourier_eq] at hstep
  have hinner : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ inner ℝ x 1) g) =
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g := by
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg := by fun_prop),
      SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth)]
    simp
  rw [hinner] at hstep
  have h2 := congrArg 𝓕 hstep
  rw [FourierTransform.fourier_fourierInv_eq, FourierTransform.fourier_smul] at h2
  exact h2

/-- One step of the commutation, in the useful direction. -/
private theorem fourier_smulLeft_step (g : 𝓢(ℝ, ℂ)) :
    𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g) =
      ((-(2 * Real.pi * Complex.I))⁻¹) • ((SchwartzMap.derivCLM ℂ ℂ) (𝓕 g)) := by
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_pos.ne')
    exact neg_ne_zero.2 (mul_ne_zero h2pi Complex.I_ne_zero)
  rw [eq_comm, inv_smul_eq_iff₀ hc]
  exact fourier_mul_step g

/-- The Fourier transform of the `j`-fold monomial multiplication is the
`j`-fold differentiation of the Fourier transform, up to the constant
`(-(2 * Real.pi * I))⁻¹`. -/
private theorem fourier_smulLeftIterate (j : ℕ) (h : 𝓢(ℝ, ℂ)) :
    𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j] h) =
      ((-(2 * Real.pi * Complex.I))⁻¹ ^ j) • ((SchwartzMap.derivCLM ℂ ℂ)^[j] (𝓕 h)) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) j h,
      fourier_smulLeft_step, ih, map_smul (SchwartzMap.derivCLM ℂ ℂ), smul_smul, pow_succ',
      Function.iterate_succ_apply']

/-- The Fourier transform is an isometry for the `L²` norm on Schwartz functions
(in `lpNorm` form). -/
private theorem lpNorm_fourier (h : 𝓢(ℝ, ℂ)) :
    lpNorm ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = lpNorm (h : ℝ → ℂ) 2 volume := by
  have h2 := SchwartzMap.norm_fourier_toL2_eq h
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h2
  exact h2

/-- Scalar multiplication scales the `L²` norm of a Schwartz function. -/
private theorem lpNorm_smul (c : ℂ) (h : 𝓢(ℝ, ℂ)) :
    lpNorm ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = ‖c‖ * lpNorm (h : ℝ → ℂ) 2 volume := by
  have hcoe : ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = c • (h : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe, lpNorm, eLpNorm_const_smul, ← toReal_eLpNorm, ENNReal.toReal_mul]
  simp

/-! ### The pointwise `sup ≤ L² + L²` estimate -/

private theorem lpNorm_sq_eq_integral_norm_sq (φ : 𝓢(ℝ, ℂ)) :
    ∫ y : ℝ, ‖φ y‖ ^ 2 = (lpNorm (φ : ℝ → ℂ) 2 volume) ^ 2 := by
  have hm : AEStronglyMeasurable (φ : ℝ → ℂ) volume := φ.continuous.aestronglyMeasurable
  have hpow : (fun y : ℝ ↦ ‖φ y‖ ^ (2 : ℝ)) = fun y ↦ ‖φ y‖ ^ 2 := by
    funext y
    exact Real.rpow_natCast ‖φ y‖ 2
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hm]
  simp only [ENNReal.toReal_ofNat]
  rw [hpow]
  have hexp : ((2 : ℝ) ⁻¹) = (1 / 2 : ℝ) := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)]

/-- A Schwartz function on the line is pointwise bounded by the L² norms of itself
and its derivative. -/
private theorem schwartz_norm_le_lpNorm_add_deriv (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖ψ x‖ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
      lpNorm ((SchwartzMap.derivCLM ℂ ℂ ψ) : ℝ → ℂ) 2 volume := by
  let d : ℝ → ℂ := SchwartzMap.derivCLM ℂ ℂ ψ
  let F : ℝ → ℝ := fun t ↦ ‖ψ t‖ ^ 2
  let F' : ℝ → ℝ := fun t ↦ 2 * inner ℝ (ψ t) (d t)
  have hd (y : ℝ) : d y = deriv (ψ : ℝ → ℂ) y := by
    simp [d]
  have hF (y : ℝ) : HasDerivAt F (F' y) y := by
    simpa [F, F', hd y] using (SchwartzMap.hasDerivAt ψ y).norm_sq
  have hsqψ : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2) volume := by
    have h := (ψ.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun y : ℝ ↦ ‖ψ y‖ ^ (2 : ℝ≥0∞).toReal) = fun y ↦ ‖ψ y‖ ^ 2 := by
      funext y
      simp only [ENNReal.toReal_ofNat]
      exact Real.rpow_natCast ‖ψ y‖ 2
    simpa [hfun] using h
  have hsqd : Integrable (fun y : ℝ ↦ ‖d y‖ ^ 2) volume := by
    have h := ((SchwartzMap.derivCLM ℂ ℂ ψ).memLp 2 volume).integrable_norm_rpow
      (by norm_num) (by norm_num)
    rw [show (fun y : ℝ ↦ ‖d y‖ ^ 2) =
        fun y ↦ ‖(SchwartzMap.derivCLM ℂ ℂ ψ) y‖ ^ (2 : ℝ≥0∞).toReal by
      funext y
      simp only [ENNReal.toReal_ofNat, d]
      exact (Real.rpow_natCast ‖d y‖ 2).symm]
    exact h
  have hsumsq : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) volume := hsqψ.add hsqd
  have hcs (y : ℝ) : |inner ℝ (ψ y) (d y)| ≤ ‖ψ y‖ * ‖d y‖ :=
    abs_real_inner_le_norm (ψ y) (d y)
  have hdom (y : ℝ) : ‖F' y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hyoung : 2 * ‖ψ y‖ * ‖d y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖ψ y‖ - ‖d y‖)]
    calc ‖F' y‖ = |2 * inner ℝ (ψ y) (d y)| := by simp [F', Real.norm_eq_abs]
      _ = 2 * |inner ℝ (ψ y) (d y)| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (‖ψ y‖ * ‖d y‖) := mul_le_mul_of_nonneg_left (hcs y) (by norm_num)
      _ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by simpa [mul_assoc] using hyoung
  have hFmeas : AEStronglyMeasurable F' volume := by
    apply Continuous.aestronglyMeasurable
    have hcψ : Continuous (fun t : ℝ ↦ (ψ t : ℂ)) := ψ.continuous
    have hcd : Continuous d := (SchwartzMap.derivCLM ℂ ℂ ψ).continuous
    exact continuous_const.mul (continuous_inner.comp (hcψ.prodMk hcd))
  have hF'int : Integrable F' volume :=
    hsumsq.mono' hFmeas (Eventually.of_forall hdom)
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x) (f := F) (f' := F')
      (fun y _ ↦ hF y) hF'int.integrableOn hsqψ.integrableOn
  have heq : ∫ y in Ioi x, F' y = - F x := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (f := F) (f' := F') (m := 0)
      (fun y _ ↦ hF y) hF'int.integrableOn hlim
  have hpoint (y : ℝ) : - F' y ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    (neg_le_abs _).trans (by simpa [Real.norm_eq_abs] using hdom y)
  have htail : ∫ y in Ioi x, - F' y ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    setIntegral_mono hF'int.neg.integrableOn hsumsq.integrableOn hpoint
  have hfull : ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hnonneg : 0 ≤ᵐ[volume] (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) :=
      Eventually.of_forall fun y ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa using integral_mono_measure (Measure.restrict_le_self (s := Ioi x))
      hnonneg hsumsq
  have hsqx : ‖ψ x‖ ^ 2 ≤ (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
    calc ‖ψ x‖ ^ 2 = - ∫ y in Ioi x, F' y := by rw [heq, neg_neg]
      _ = ∫ y in Ioi x, - F' y := (integral_neg _).symm
      _ ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := htail
      _ ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := hfull
      _ = (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
            (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
          rw [integral_add hsqψ hsqd, lpNorm_sq_eq_integral_norm_sq ψ,
            lpNorm_sq_eq_integral_norm_sq (SchwartzMap.derivCLM ℂ ℂ ψ)]
  have hsqrt : ‖ψ x‖ ≤ Real.sqrt ((lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsqx
  refine hsqrt.trans ?_
  have ha0 : 0 ≤ lpNorm (ψ : ℝ → ℂ) 2 volume := lpNorm_nonneg
  have hb0 : 0 ≤ lpNorm (d : ℝ → ℂ) 2 volume := lpNorm_nonneg
  rw [← Real.sqrt_sq (add_nonneg ha0 hb0)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-- Pointwise domination translates into a bound of `lpNorm` by the `√2`-multiple
of a combination of two `lpNorm`s. -/
private theorem lpNorm_le_add_of_pointwise {u g h : ℝ → ℂ} {c : ℝ}
    (hc : 0 ≤ c) (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hpt : ∀ y, ‖u y‖ ≤ c * ‖g y‖ + ‖h y‖) :
    lpNorm u 2 volume ≤
      Real.sqrt 2 * (c * lpNorm g 2 volume + lpNorm h 2 volume) := by
  classical
  have huI : Integrable (fun y : ℝ ↦ ‖u y‖ ^ 2) volume := by
    simpa using hu.integrable_norm_rpow (by norm_num) (by norm_num)
  have hgI : Integrable (fun y : ℝ ↦ ‖g y‖ ^ 2) volume := by
    simpa using hg.integrable_norm_rpow (by norm_num) (by norm_num)
  have hhI : Integrable (fun y : ℝ ↦ ‖h y‖ ^ 2) volume := by
    simpa using hh.integrable_norm_rpow (by norm_num) (by norm_num)
  set A : ℝ := ∫ y : ℝ, ‖g y‖ ^ 2 with hA
  set B : ℝ := ∫ y : ℝ, ‖h y‖ ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun y ↦ sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg fun y ↦ sq_nonneg _
  have hwmeas : AEStronglyMeasurable (fun y : ℝ ↦ (c * ‖g y‖ + ‖h y‖) ^ 2) volume :=
    (((hg.aestronglyMeasurable.norm).const_mul c).add
      hh.aestronglyMeasurable.norm).pow 2
  have hbig : Integrable (fun y : ℝ ↦ (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2) volume :=
    (hgI.const_mul (2 * c * c)).add (hhI.const_mul 2)
  have hwI : Integrable (fun y : ℝ ↦ (c * ‖g y‖ + ‖h y‖) ^ 2) volume :=
    hbig.mono' hwmeas (Eventually.of_forall fun y ↦ by
      have hsq := sq_nonneg (c * ‖g y‖ - ‖h y‖)
      have hpos : (0:ℝ) ≤ 2 * c * c * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 := by positivity
      have hnn : (0:ℝ) ≤ (c * ‖g y‖ + ‖h y‖) ^ 2 := sq_nonneg _
      simp only [Real.norm_eq_abs, abs_of_nonneg hnn]
      nlinarith)
  have hint : ∫ y : ℝ, ‖u y‖ ^ 2 ≤ ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 :=
    integral_mono huI hwI fun y ↦ pow_le_pow_left₀ (norm_nonneg _) (hpt y) 2
  have hsplit : ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 ≤ (2 * c * c) * A + 2 * B := by
    have hpt2 : ∀ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 ≤ (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 := by
      intro y
      have hyoung : (2:ℝ) * (c * ‖g y‖) * ‖h y‖ ≤ (c * ‖g y‖) ^ 2 + ‖h y‖ ^ 2 := by
        have hsq := sq_nonneg (c * ‖g y‖ - ‖h y‖)
        nlinarith
      nlinarith
    calc ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2
        ≤ ∫ y : ℝ, (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 :=
          integral_mono hwI hbig hpt2
      _ = (2 * c * c) * A + 2 * B := by
          have splitEq := integral_add (hgI.const_mul (2 * c * c)) (hhI.const_mul 2)
          simp only [splitEq, integral_const_mul, hA, hB]
  -- convert the `lpNorm`s to square roots of integrals
  have huN' : lpNorm u 2 volume = (∫ y : ℝ, ‖u y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hu.aestronglyMeasurable]
    simp
  have hgN' : lpNorm g 2 volume = (∫ y : ℝ, ‖g y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hg.aestronglyMeasurable]
    simp
  have hhN' : lpNorm h 2 volume = (∫ y : ℝ, ‖h y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hh.aestronglyMeasurable]
    simp
  have hexp : ((2:ℝ≥0∞).toReal)⁻¹ = ((1 / 2 : ℝ)) := by
    simp [ENNReal.toReal_ofNat]
  have hexp2 : ∀ z : ℝ, z ^ ((2:ℝ≥0∞).toReal⁻¹) = Real.sqrt z := by
    intro z
    rw [hexp, ← Real.sqrt_eq_rpow]
  have hint' : (∫ y : ℝ, ‖u y‖ ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [hexp2 (∫ y : ℝ, ‖u y‖ ^ 2), hexp2 (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2)]
    exact Real.sqrt_le_sqrt hint
  have hsplit' : (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [hexp2 (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2), hexp2 ((2 * c * c) * A + 2 * B)]
    exact Real.sqrt_le_sqrt hsplit
  have hfinal : ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      Real.sqrt 2 * (c * A ^ ((2:ℝ≥0∞).toReal⁻¹) + B ^ ((2:ℝ≥0∞).toReal⁻¹)) := by
    have hsplit2 : ((2 * c * c) * A + 2 * B) = 2 * (c * c * A + B) := by ring
    have hmain : Real.sqrt (c * c * A + B) ≤ c * Real.sqrt A + Real.sqrt B := by
      refine (Real.sqrt_le_iff (x := c * c * A + B)
        (y := c * Real.sqrt A + Real.sqrt B)).2
        ⟨add_nonneg (mul_nonneg hc (Real.sqrt_nonneg A)) (Real.sqrt_nonneg B), ?_⟩
      have e1 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
      have e2 : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
      have hsq : (c * Real.sqrt A + Real.sqrt B) ^ 2 =
          c * c * A + 2 * (c * (Real.sqrt A * Real.sqrt B)) + B := by
        rw [add_sq, mul_pow, e1, e2]
        ring
      rw [hsq]
      linarith [mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))]
    rw [hexp2 ((2 * c * c) * A + 2 * B),
      show ((2 * c * c) * A + 2 * B) = 2 * (c * c * A + B) from by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), hexp2 A, hexp2 B]
    exact mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg 2)
  calc lpNorm u 2 volume = (∫ y : ℝ, ‖u y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := huN'
    _ ≤ (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := hint'
    _ ≤ ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) := hsplit'
    _ ≤ Real.sqrt 2 * (c * A ^ ((2:ℝ≥0∞).toReal⁻¹) + B ^ ((2:ℝ≥0∞).toReal⁻¹)) := hfinal
    _ = Real.sqrt 2 * (c * lpNorm g 2 volume + lpNorm h 2 volume) := by
        rw [hA, hB, ← hgN', ← hhN']

/-! ### The core estimate -/

/-- The real Schwartz seminorm `(k, n)` is bounded by the three Fourier `L²`
seminorms with indices `(k, n), (k - 1, n), (k, n + 1)`. -/
private theorem schwartz_seminorm_le_l2 (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n f ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume +
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
  classical
  have hgrowth : ∀ j : ℕ, (fun x : ℝ ↦ (x : ℂ) ^ j).HasTemperateGrowth := by
    intro j; fun_prop
  -- the underlying function of `D ^[n] f` is the iterated derivative
  have hcoeg0 : ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) =
      iteratedDeriv n (f : ℝ → ℂ) :=
    funext (coe_derivIterate f n)
  have hnormcoe : ∀ y : ℝ, ‖(y : ℂ)‖ = |y| := by
    intro y
    exact RCLike.norm_ofReal (K := ℂ) y
  -- the monomially-multiplied iterated derivative
  set ψ : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
      ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) with hψdef
  have hcoepsi : ((ψ : ℝ → ℂ)) =
      fun y : ℝ ↦ (y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y := by
    funext y
    rw [hψdef, smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k)]
    simp [smul_eq_mul]
  -- the pointwise estimate on the derivative of `ψ`
  have hdiff : ∀ y : ℝ,
      ‖deriv (ψ : ℝ → ℂ) y‖ ≤
        (k : ℝ) * ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
            ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y‖ +
          ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
            ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y‖ := by
    intro y
    have hd1 : HasDerivAt (((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ))
        (((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f : ℝ → ℂ) y) y := by
      have h0 := SchwartzMap.hasDerivAt ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) y
      rw [hcoeg0, ← iteratedDeriv_succ] at h0
      rw [hcoeg0, coe_derivIterate f (n + 1)]
      exact h0
    have hpow : HasDerivAt (fun z : ℝ ↦ (z : ℂ) ^ k) ((k : ℂ) * ((y : ℂ) ^ (k - 1))) y :=
      HasDerivAt.comp_ofReal (hasDerivAt_pow k (y : ℂ))
    have hdψ := hpow.mul hd1
    have hdψeq : deriv ((ψ : ℝ → ℂ)) y =
        ((k : ℂ) * (y : ℂ) ^ (k - 1)) * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y +
          (y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n + 1] f : ℝ → ℂ) y := by
      rw [hcoepsi]
      exact hdψ.deriv
    rw [hdψeq]
    have hsmul1 : (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y =
        (y : ℂ) ^ (k - 1) • ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y := by
      rw [smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth (k-1))]
    have hsmul2 : (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y =
        (y : ℂ) ^ k • ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f : ℝ → ℂ) y := by
      rw [smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k)]
    have hy1 : ‖((k : ℂ) * (y : ℂ) ^ (k - 1)) * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y‖ ≤
        (k : ℝ) * ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
          ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y‖ := by
      rw [norm_mul, norm_mul, norm_natCast, hsmul1, norm_smul, norm_pow]
      exact le_of_eq (by ring)
    have hy2 : ‖(y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n + 1] f : ℝ → ℂ) y‖ ≤
        ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
          ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y‖ := by
      simp only [hsmul2, norm_mul, norm_smul, norm_pow]
      exact le_refl _
    exact le_trans (norm_add_le _ _) (add_le_add hy1 hy2)
  -- the two `L²` bounds from the fundamental lemma
  have hψbound : ∀ x : ℝ, ‖ψ x‖ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
      lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume :=
    schwartz_norm_le_lpNorm_add_deriv ψ
  have hψx : ∀ x : ℝ, ‖ψ x‖ = |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
    intro x
    rw [hψdef, smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k),
      norm_smul, norm_pow, hnormcoe x, coe_derivIterate f n]
  -- each monomial multiplication reduces (up to a constant of norm `≤ 1`) to a
  -- Fourier derivative, whose `L²` norm is one of the target seminorms
  have hcoef : ∀ j : ℕ, ‖((-(2 * Real.pi * Complex.I))⁻¹ ^ j : ℂ)‖ ≤ 1 := by
    intro j
    have hle : ‖(-(2 * Real.pi * Complex.I))⁻¹‖ ≤ 1 := by
      have h2 : ‖(-(2 * Real.pi * Complex.I))‖ = 2 * Real.pi := by
        rw [norm_neg, norm_mul, norm_mul, hnormcoe Real.pi, abs_of_pos Real.pi_pos,
          Complex.norm_I, mul_one]
        norm_num
      rw [norm_inv, h2, inv_eq_one_div]
      exact (div_le_one (by linarith [Real.pi_gt_three])).2 (by linarith [Real.pi_gt_three])
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hle j).trans (one_pow j).le
  have hfourier : ∀ (j i : ℕ),
      lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
        ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)) : ℝ → ℂ)) 2 volume ≤
        lpNorm ((realSchwartzFourierDeriv j i f : ℝ → ℂ)) 2 volume := by
    intro j i
    have hE := lpNorm_fourier ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
      ((SchwartzMap.derivCLM ℂ ℂ)^[i] f))
    rw [← hE, fourier_smulLeftIterate, lpNorm_smul]
    refine le_trans (mul_le_mul_of_nonneg_right (hcoef j) lpNorm_nonneg) ?_
    rw [one_mul]
    exact le_refl _
  -- assembly of the pointwise bound
  have h2 : lpNorm ((ψ : ℝ → ℂ)) 2 volume ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume := hfourier k n
  have h3 : lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume ≤
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
    have hmem1 : MemLp ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume :=
      ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)).memLp 2 volume
    have hmem2 : MemLp ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ)) 2 volume :=
      ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)).memLp 2 volume
    have hu0 : MemLp (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume :=
      (SchwartzMap.derivCLM ℂ ℂ ψ).memLp 2 volume
    have hbase := lpNorm_le_add_of_pointwise (Nat.cast_nonneg k) hu0 hmem1 hmem2 hdiff
    calc lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume
        ≤ Real.sqrt 2 * ((k : ℝ) * lpNorm ((((SchwartzMap.smulLeftCLM ℂ
                (fun x : ℝ ↦ (x : ℂ)))^[k-1]
              ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume +
            lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
              ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ)) 2 volume) := hbase
      _ ≤ Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
            lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hfourier (k - 1) n) (by norm_num : (0:ℝ) ≤ (k:ℝ)))
              (hfourier k (n + 1))) (Real.sqrt_nonneg 2)
  have hpoint : ∀ x : ℝ, |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume +
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
    intro x
    have h1 := hψbound x
    rw [hψx x] at h1
    linarith
  exact SchwartzMap.seminorm_le_bound' ℂ k n f
    (add_nonneg lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
      (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (k:ℝ)) lpNorm_nonneg)
        lpNorm_nonneg))) hpoint

private theorem iterateCLM_add (L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (n : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    L^[n] (f + g) = L^[n] f + L^[n] g := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

private theorem iterateCLM_smul (L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (n : ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    L^[n] (c • f) = c • L^[n] f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_smul]

private theorem realSchwartzFourierDeriv_add (m n : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv m n (f + g) =
      realSchwartzFourierDeriv m n f + realSchwartzFourierDeriv m n g := by
  simp only [realSchwartzFourierDeriv]
  rw [iterateCLM_add (SchwartzMap.derivCLM ℂ ℂ) n]
  have hF (g : 𝓢(ℝ, ℂ)) : 𝓕 g = fourierTransformCLM ℂ g := rfl
  rw [hF, (fourierTransformCLM ℂ).map_add, iterateCLM_add (SchwartzMap.derivCLM ℂ ℂ) m, hF, hF]

private theorem realSchwartzFourierDeriv_smul (m n : ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv m n (c • f) = c • realSchwartzFourierDeriv m n f := by
  simp only [realSchwartzFourierDeriv]
  rw [iterateCLM_smul (SchwartzMap.derivCLM ℂ ℂ) n]
  have hF (g : 𝓢(ℝ, ℂ)) : 𝓕 g = fourierTransformCLM ℂ g := rfl
  rw [hF, (fourierTransformCLM ℂ).map_smul, iterateCLM_smul (SchwartzMap.derivCLM ℂ ℂ) m, hF]

private theorem lpNorm_fourierDeriv_eq (j i : ℕ) (f : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume =
      (2 * Real.pi) ^ j *
        lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
          ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)) : ℝ → ℂ)) 2 volume := by
  set mono : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
      ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)
  have hE := lpNorm_fourier mono
  rw [fourier_smulLeftIterate, lpNorm_smul] at hE
  have hnorm : ‖((-(2 * Real.pi * Complex.I))⁻¹ ^ j : ℂ)‖ = (2 * Real.pi)⁻¹ ^ j := by
    rw [norm_pow]
    congr 1
    rw [norm_inv, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm] at hE
  have hpos : (2 * Real.pi)⁻¹ ^ j ≠ 0 := by positivity
  have hE' : (2 * Real.pi)⁻¹ ^ j *
      lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume =
      lpNorm (mono : ℝ → ℂ) 2 volume := by
    simpa [realSchwartzFourierDeriv] using hE
  apply mul_left_cancel₀ hpos
  calc (2 * Real.pi)⁻¹ ^ j * lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume
      = lpNorm (mono : ℝ → ℂ) 2 volume := hE'
    _ = (2 * Real.pi)⁻¹ ^ j * ((2 * Real.pi) ^ j * lpNorm (mono : ℝ → ℂ) 2 volume) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0),
          one_pow, one_mul]

private theorem lpNorm_monomial_le (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume ≤
      Real.sqrt Real.pi *
        (SchwartzMap.seminorm ℂ k n f + SchwartzMap.seminorm ℂ (k + 1) n f) := by
  set φ : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
      ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)
  set C : ℝ := SchwartzMap.seminorm ℂ k n f + SchwartzMap.seminorm ℂ (k + 1) n f
  have hC : 0 ≤ C := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hgrowth : (fun x : ℝ ↦ (x : ℂ) ^ k).HasTemperateGrowth := by fun_prop
  have hcoe : ∀ x : ℝ, φ x = (x : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) x := by
    intro x
    have hmap : φ = SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (y : ℂ) ^ k)
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) := by
      simpa [φ] using smulLeftIterate k ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)
    rw [hmap, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth)]
    simp [smul_eq_mul]
  have hnorm : ∀ x : ℝ, ‖φ x‖ = |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
    intro x
    rw [hcoe, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, coe_derivIterate]
  have hsum : ∀ x : ℝ, (1 + |x|) * ‖φ x‖ ≤ C := by
    intro x
    rw [show (1 + |x|) * ‖φ x‖ = ‖φ x‖ + |x| * ‖φ x‖ by ring, hnorm]
    have h1 := SchwartzMap.le_seminorm' ℂ k n f x
    have h2 := SchwartzMap.le_seminorm' ℂ (k + 1) n f x
    have hx : |x| * (|x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖) =
        |x| ^ (k + 1) * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
      rw [pow_succ, mul_assoc, mul_left_comm |x| (|x| ^ k)]
    simpa [hx] using add_le_add h1 h2
  have hdiv : ∀ x : ℝ, ‖φ x‖ ≤ C * (1 + |x|)⁻¹ := by
    intro x
    have hpos : 0 < 1 + |x| := by positivity
    have hx := hsum x
    rw [mul_comm] at hx
    rwa [← le_div_iff₀ hpos, div_eq_mul_inv] at hx
  have hsq : ∀ x : ℝ, ‖φ x‖ ^ 2 ≤ C ^ 2 * (1 + x ^ 2)⁻¹ := by
    intro x
    have hinv : (1 + |x|)⁻¹ ^ 2 ≤ (1 + x ^ 2)⁻¹ := by
      have hden : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
        calc 1 + x ^ 2 = 1 + |x| ^ 2 := by rw [sq_abs]
          _ ≤ 1 + 2 * |x| + |x| ^ 2 := by linarith [abs_nonneg x]
          _ = (1 + |x|) ^ 2 := by ring
      rw [inv_pow, ← one_div, ← one_div]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    calc ‖φ x‖ ^ 2 ≤ (C * (1 + |x|)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdiv x) 2
      _ = C ^ 2 * (1 + |x|)⁻¹ ^ 2 := by ring
      _ ≤ C ^ 2 * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
  have hsqφ : Integrable (fun y : ℝ ↦ ‖φ y‖ ^ 2) volume := by
    have h := (φ.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun y : ℝ ↦ ‖φ y‖ ^ (2 : ℝ≥0∞).toReal) = fun y ↦ ‖φ y‖ ^ 2 := by
      funext y
      simp only [ENNReal.toReal_ofNat]
      exact Real.rpow_natCast ‖φ y‖ 2
    simpa [hfun] using h
  have hintC : Integrable (fun y : ℝ ↦ C ^ 2 * (1 + y ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul (C ^ 2)
  have hint : ∫ y : ℝ, ‖φ y‖ ^ 2 ≤ ∫ y : ℝ, C ^ 2 * (1 + y ^ 2)⁻¹ :=
    integral_mono hsqφ hintC hsq
  have hrhs : ∫ y : ℝ, C ^ 2 * (1 + y ^ 2)⁻¹ = C ^ 2 * Real.pi := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hsqle : (lpNorm (φ : ℝ → ℂ) 2 volume) ^ 2 ≤ C ^ 2 * Real.pi := by
    rw [← lpNorm_sq_eq_integral_norm_sq φ]
    exact hint.trans_eq hrhs
  calc lpNorm (φ : ℝ → ℂ) 2 volume
      ≤ Real.sqrt (C ^ 2 * Real.pi) := by
        rw [← Real.sqrt_sq (lpNorm_nonneg : 0 ≤ lpNorm (φ : ℝ → ℂ) 2 volume)]
        exact Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt Real.pi * C := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC, mul_comm]

private theorem lpNorm_fourierDeriv_le_seminorm (f : 𝓢(ℝ, ℂ)) (m n : ℕ) :
    lpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤
      (2 * Real.pi) ^ m * Real.sqrt Real.pi *
        (SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f) := by
  rw [lpNorm_fourierDeriv_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (lpNorm_monomial_le f m n)
    (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)

private theorem lpNorm_fourierDeriv_add (i : ℕ × ℕ) (f g : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv i.1 i.2 (f + g) : ℝ → ℂ) 2 volume ≤
      lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume +
        lpNorm (realSchwartzFourierDeriv i.1 i.2 g : ℝ → ℂ) 2 volume := by
  rw [realSchwartzFourierDeriv_add]
  have hcoe :
      ((realSchwartzFourierDeriv i.1 i.2 f + realSchwartzFourierDeriv i.1 i.2 g : 𝓢(ℝ, ℂ)) :
        ℝ → ℂ) =
      (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) +
        (realSchwartzFourierDeriv i.1 i.2 g : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe]
  exact lpNorm_add_le ((realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private theorem lpNorm_fourierDeriv_smul (i : ℕ × ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv i.1 i.2 (c • f) : ℝ → ℂ) 2 volume =
      ‖c‖ * lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume := by
  rw [realSchwartzFourierDeriv_smul]
  have hcoe : ((c • realSchwartzFourierDeriv i.1 i.2 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      c • (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe, lpNorm_const_smul]
  rfl

/-- Paper: Proposition D.1.10.2, p. 784. L² norms of the differentiated real
Fourier transforms in (D.1.10.3) generate the Schwartz topology. -/
theorem realSchwartz_fourierLp_generates :
    GeneratesLpSeminorms (volume : Measure ℝ) 2
      (fun i : ℕ × ℕ ↦ fun f : 𝓢(ℝ, ℂ) ↦
        (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ)) := by
  classical
  let ν : ℕ × ℕ → 𝓢(ℝ, ℂ) → ℝ := fun i f ↦
    lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume
  let P : ℕ × ℕ → Seminorm ℂ 𝓢(ℝ, ℂ) := fun i ↦
    Seminorm.of (ν i) (fun f g ↦ lpNorm_fourierDeriv_add i f g)
      (fun c f ↦ lpNorm_fourierDeriv_smul i c f)
  refine ⟨fun i f ↦ (realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume, ⟨P, ?_, ?_⟩⟩
  · refine (schwartz_withSeminorms ℂ ℝ ℂ).congr ?_ ?_
    · refine Seminorm.IsBounded.of_real ?_
      rintro ⟨m, n⟩
      let s : Finset (ℕ × ℕ) := {(m, n), (m + 1, n)}
      refine ⟨s, (2 * Real.pi) ^ m * Real.sqrt Real.pi * 2, fun f ↦ ?_⟩
      have hle := lpNorm_fourierDeriv_le_seminorm f m n
      have h1 : SchwartzMap.seminorm ℂ m n f ≤ (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        simpa [s, schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ)
            (by simp [s] : (m, n) ∈ s))
      have h2 : SchwartzMap.seminorm ℂ (m + 1) n f ≤
          (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        simpa [s, schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ)
            (by simp [s] : (m + 1, n) ∈ s))
      have hsup : SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f ≤
          2 * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by linarith
      have hcoef : 0 ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi := by positivity
      calc P (m, n) f = ν (m, n) f := rfl
        _ ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi *
            (SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f) := hle
        _ ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi *
            (2 * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) :=
              mul_le_mul_of_nonneg_left hsup hcoef
        _ = ((2 * Real.pi) ^ m * Real.sqrt Real.pi * 2) *
            (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring
    · refine Seminorm.IsBounded.of_real ?_
      rintro ⟨k, n⟩
      let s : Finset (ℕ × ℕ) := {(k, n), (k - 1, n), (k, n + 1)}
      refine ⟨s, 1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2, fun f ↦ ?_⟩
      have hle := schwartz_seminorm_le_l2 f k n
      have hPeq (a b : ℕ) :
          P (a, b) f = lpNorm (realSchwartzFourierDeriv a b f : ℝ → ℂ) 2 volume := rfl
      have h1 : lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume ≤ (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have h2 : lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume ≤
          (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have h3 : lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume ≤
          (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have hS : 0 ≤ (s.sup P) f := apply_nonneg _ _
      have hgoal : SchwartzMap.seminorm ℂ k n f ≤
          (1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2) * (s.sup P) f := by
        set S : ℝ := (s.sup P) f
        have hmid : lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume +
            Real.sqrt 2 * ((k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
              lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume) ≤
            S + Real.sqrt 2 * ((k : ℝ) * S + S) := by
          have hB : (k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume ≤
              (k : ℝ) * S := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
          have hsum : (k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
              lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume ≤
              (k : ℝ) * S + S := add_le_add hB h3
          exact add_le_add h1 (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
        calc SchwartzMap.seminorm ℂ k n f ≤
            lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume +
              Real.sqrt 2 * ((k : ℝ) *
                lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
                lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume) := hle
          _ ≤ S + Real.sqrt 2 * ((k : ℝ) * S + S) := hmid
          _ = (1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2) * S := by ring
      simpa [schwartzSeminormFamily_apply] using hgoal
  · intro i f
    have hP : P i f = (eLpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume).toReal := by
      change ν i f = _
      rfl
    rw [hP, ENNReal.ofReal_toReal]
    exact ((realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume).eLpNorm_ne_top

end RealSchwartzFourierLp

open scoped LineDeriv in
/-- Paper: (D.1.10.4), p. 785. Differentiating the Fourier transform corresponds
to taking the Fourier transform after multiplication by a power of the coordinate. -/
private theorem realSchwartz_iterate_deriv_fourier (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.derivCLM ℂ ℂ)^[m] (𝓕 f) =
      𝓕 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ((-2 * π * Complex.I : ℂ) * x) ^ m) f) := by
  have hweight : (fun x : ℝ ↦ (-2 * π * Complex.I : ℂ) * x).HasTemperateGrowth := by fun_prop
  have hpow (k : ℕ) :
      (fun x : ℝ ↦ ((-2 * π * Complex.I : ℂ) * x) ^ k).HasTemperateGrowth := by
    exact hweight.pow k
  have hderiv (g : 𝓢(ℝ, ℂ)) :
      SchwartzMap.derivCLM ℂ ℂ (𝓕 g) =
        𝓕 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (-2 * π * Complex.I : ℂ) * x) g) := by
    have hline : ∂_{(1 : ℝ)} (𝓕 g) = SchwartzMap.derivCLM ℂ ℂ (𝓕 g) := by
      ext1 x
      let G : 𝓢(ℝ, ℂ) := 𝓕 g
      change fderiv ℝ (⇑G) x 1 = deriv (⇑G) x
      exact fderiv_apply_one_eq_deriv
    rw [← hline, SchwartzMap.lineDerivOp_fourier_eq]
    congr 1
    ext1 x
    have hinner : (fun y : ℝ ↦ inner ℝ y 1) = id := by
      funext y
      exact (Real.inner_apply y 1).trans (mul_one y)
    rw [hinner, SchwartzMap.smulLeftCLM_apply_apply hweight]
    have hid : (id : ℝ → ℝ).HasTemperateGrowth := by fun_prop
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hid]
    simp [Complex.real_smul]
    ring
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply]
    congr 1
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hpow 0)]
    simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, hderiv]
    congr 1
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply hweight,
      SchwartzMap.smulLeftCLM_apply_apply (hpow m),
      SchwartzMap.smulLeftCLM_apply_apply (hpow (m + 1))]
    simp only [smul_smul, pow_succ']

/-- The weighted derivative's L² norm is controlled by the corresponding Fourier
seminorm via Plancherel. -/
private theorem realSchwartz_weightedDeriv_eLpNorm (m n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x : ℝ ↦ ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖) 2 volume ≤
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume := by
  let g := (SchwartzMap.derivCLM ℂ ℂ)^[n] f
  have hg' (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ)^[k] f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', iteratedDeriv_succ, ← ih]
      rfl
  have hg (x : ℝ) : ‖g x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← hg']
  let w (x : ℝ) := ((-2 * π * Complex.I : ℂ) * x) ^ m
  let h := SchwartzMap.smulLeftCLM ℂ w g
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  have hFourier : realSchwartzFourierDeriv m n f = 𝓕 h :=
    realSchwartz_iterate_deriv_fourier m g
  have hPlancherel : eLpNorm ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = eLpNorm (⇑h) 2 volume := by
    have hL2 := SchwartzMap.norm_fourier_toL2_eq h
    simp only [SchwartzMap.norm_toLp] at hL2
    simpa only [ENNReal.ofReal_toReal ((𝓕 h : 𝓢(ℝ, ℂ)).eLpNorm_lt_top 2 volume).ne,
      ENNReal.ofReal_toReal (h.eLpNorm_lt_top 2 volume).ne] using congrArg ENNReal.ofReal hL2
  rw [hFourier, hPlancherel]
  apply eLpNorm_mono (f.integrable_pow_mul_iteratedFDeriv volume m n).aestronglyMeasurable
  intro x
  change ‖‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖‖ ≤ ‖h x‖
  rw [Real.norm_of_nonneg (by positivity)]
  dsimp [h]
  rw [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul]
  change _ ≤ ‖((-2 * π * Complex.I : ℂ) * x) ^ m‖ * ‖g x‖
  rw [hg, norm_pow, norm_mul, Complex.norm_real]
  have hc : 1 ≤ ‖(-2 * π * Complex.I : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
    linarith [Real.pi_gt_three]
  gcongr
  exact le_mul_of_one_le_left (abs_nonneg x) hc

/-- Bounds on Fourier L² seminorms give uniform bounds on the weighted L¹ norms
of the original derivatives by Cauchy–Schwarz. -/
private theorem realSchwartz_weightedDeriv_integral_bounded (B : Set (𝓢(ℝ, ℂ)))
    (hB : ∀ m n : ℕ, ∃ C : ℝ≥0, ∀ f ∈ B,
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤ (C : ℝ≥0∞)) :
    ∀ m n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ B,
      (∫ x : ℝ, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖) ≤ C := by
  let u (m n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) := ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖
  have hu (m n : ℕ) (f : 𝓢(ℝ, ℂ)) : Integrable (u m n f) :=
    f.integrable_pow_mul_iteratedFDeriv volume m n
  have hu_nonneg (m n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 0 ≤ u m n f x := by
    dsimp [u]
    positivity
  obtain ⟨k, hk⟩ := Measure.HasTemperateGrowth.exists_eLpNorm_lt_top 2
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth)
  let w (x : ℝ) := (1 + ‖x‖) ^ (-(k : ℝ))
  have hw : AEStronglyMeasurable w volume :=
    (Continuous.rpow_const (by fun_prop) (fun x ↦ Or.inl (by positivity))).aestronglyMeasurable
  let K : ℝ≥0 := (eLpNorm w 2 volume).toNNReal
  have hK : eLpNorm w 2 volume = (K : ℝ≥0∞) := (ENNReal.coe_toNNReal hk.ne).symm
  intro m n
  obtain ⟨C₀, hC₀⟩ := hB 0 n
  obtain ⟨C₁, hC₁⟩ := hB (m + k) n
  let C : ℝ≥0 := K * (2 ^ k * (C₀ + C₁))
  refine ⟨C, C.coe_nonneg, fun f hf ↦ ?_⟩
  let v : ℝ → ℝ := u 0 n f + u (m + k) n f
  have hv : AEStronglyMeasurable v volume := (hu 0 n f).aestronglyMeasurable.add
    (hu (m + k) n f).aestronglyMeasurable
  have hnorm : eLpNorm (u m n f) 1 volume ≤ (C : ℝ≥0∞) := calc
    _ ≤ eLpNorm (w • ((2 : ℝ) ^ k • v)) 1 volume := by
      refine eLpNorm_mono (hu m n f).aestronglyMeasurable fun x ↦ ?_
      rw [Real.norm_of_nonneg (hu_nonneg m n f x)]
      have h := pow_mul_le_of_le_of_pow_mul_le (k := m) (l := k)
        (norm_nonneg x) (norm_nonneg (iteratedFDeriv ℝ n f x)) (le_refl _)
        (le_refl (u (m + k) n f x))
      change u m n f x ≤ ‖w x * ((2 : ℝ) ^ k * (u 0 n f x + u (m + k) n f x))‖
      refine h.trans ?_
      rw [mul_comm _ (w x), Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))]
      simp [u, w]
    _ ≤ eLpNorm w 2 volume * eLpNorm ((2 : ℝ) ^ k • v) 2 volume :=
      eLpNorm_smul_le_mul_eLpNorm hw (hv.const_smul _)
    _ ≤ (C : ℝ≥0∞) := by
      have htwo : ‖(2 : ℝ)‖ₑ = 2 := by exact_mod_cast Real.eNorm_natCast 2
      rw [hK, eLpNorm_const_smul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_ofNat, ENNReal.coe_add, eNorm_pow, htwo]
      gcongr
      exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ((realSchwartz_weightedDeriv_eLpNorm 0 n f).trans (hC₀ f hf))
          ((realSchwartz_weightedDeriv_eLpNorm (m + k) n f).trans (hC₁ f hf)))
  change ∫ x, u m n f x ≤ (C : ℝ)
  calc
    _ = ∫ x, ‖u m n f x‖ := integral_congr_ae (ae_of_all _ fun x ↦
      (Real.norm_of_nonneg (hu_nonneg m n f x)).symm)
    _ = (eLpNorm (u m n f) 1 volume).toReal := by
      rw [integral_norm_eq_lintegral_eNorm (hu m n f).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_eNorm (hu m n f).aestronglyMeasurable]
    _ ≤ (C : ℝ) := ENNReal.toReal_le_of_le_ofReal C.coe_nonneg
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hnorm)

/-- Paper: Proposition D.1.10.2, p. 784. A set of real Schwartz functions is bounded
exactly when each Fourier L² seminorm is bounded on it. -/
theorem realSchwartz_fourierLp_bounded_iff (B : Set (𝓢(ℝ, ℂ))) :
    IsVonNBounded ℂ B ↔ ∀ m n : ℕ, ∃ C : ℝ≥0, ∀ f ∈ B,
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤ (C : ℝ≥0∞) := by
  constructor
  · intro hB m n
    let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    let D := SchwartzMap.derivCLM ℂ ℂ
    let T := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) ∘L
      ((D ^ m) ∘L SchwartzMap.fourierTransformCLM ℂ) ∘L (D ^ n)
    obtain ⟨R, hR⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).1 (hB.image T)
    refine ⟨Real.toNNReal R, fun f hf ↦ ?_⟩
    have hTf : T f = (realSchwartzFourierDeriv m n f).toLp 2 volume := by
      simp [T, D, realSchwartzFourierDeriv, FunLike.coe_pow_eq_iterate]
    have hRf := hR f hf
    rw [hTf, SchwartzMap.norm_toLp] at hRf
    rw [← ENNReal.ofReal_toReal ((realSchwartzFourierDeriv m n f).eLpNorm_lt_top 2 volume).ne]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hRf.trans (Real.le_coe_toNNReal R))
  · intro hB
    choose C hCpos hC using realSchwartz_weightedDeriv_integral_bounded B hB
    have h := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded
      (s := (𝓕 · : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) '' B)
    have hFB : IsVonNBounded ℂ ((𝓕 · : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) '' B) := h.mpr (fun (k, n) ↦ by
      let M := (2 * π) ^ n * (2 * (n : ℝ) + 2) ^ k *
        ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1), C p.1 p.2
      have hM : 0 ≤ M := by
        dsimp [M]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ ↦ hCpos p.1 p.2)
      refine ⟨M + 1, by linarith, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      apply lt_of_le_of_lt _ (lt_add_one M)
      apply SchwartzMap.seminorm_le_bound ℂ k n _ hM
      intro x
      rw [SchwartzMap.fourier_coe]
      apply (Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤) (f.smooth ⊤)
        (fun i j _ _ ↦ f.integrable_pow_mul_iteratedFDeriv volume i j) le_top le_top x).trans
      dsimp [M]
      gcongr with p _
      exact hC p.1 p.2 f hf)
    apply (hFB.image (FourierTransform.fourierInvCLM ℂ 𝓢(ℝ, ℂ))).subset
    intro f hf
    refine ⟨𝓕 f, ⟨f, hf, rfl⟩, ?_⟩
    rw [FourierTransform.fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq]

-- TODO(paper-gap): The last sum in (D.1.10.5) omits the constant term k = 0.
-- For m = n = 0 and N = 1, bumps concentrated at 0 disprove that estimate.

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. Multiply the coordinate mixed partial
of a Euclidean Schwartz function by the coordinate monomial. -/
def euclideanSchwartzMonomialPartial {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) : ℂ :=
  (∏ i, (x i : ℂ) ^ α i) *
    elementaryPartial (fun g : ElementaryLieGroup m 0 0 PUnit.{1} ↦ f g.1)
      β 0 (x, 0) 0 PUnit.unit

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. At zero multi-indices the weighted
partial is the original function.
Deviation: Sanity check on the weight and derivative. -/
theorem euclideanSchwartzMonomialPartial_zero {m : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzMonomialPartial 0 0 f x = f x := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 0)
  let directions : List X :=
    ((List.ofFn (fun _ : Fin m ↦ ([] : List X))).flatten ++
      (List.ofFn (fun _ : Fin 0 ↦ ([] : List X))).flatten)
  have hnil (k : ℕ) : (List.replicate k ([] : List X)).flatten = [] := by
    induction k with
    | zero => rfl
    | succ j ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl
  have hdir : directions = [] := by
    dsimp [directions]
    rw [List.ofFn_const, List.ofFn_const]
    rw [hnil m, hnil 0]
    rfl
  have hlen : directions.length = 0 := by rw [hdir]; rfl
  simp [euclideanSchwartzMonomialPartial, elementaryPartial]
  change (iteratedFDeriv ℝ directions.length
        (fun v ↦ f ((elementaryCover v ![] PUnit.unit).1)) (x, 0)) directions.get = f x
  have hiter (k : ℕ) (hk : k = 0) (d : Fin k → X) :
      (iteratedFDeriv ℝ k (fun v ↦ f ((elementaryCover v ![] PUnit.unit).1)) (x, 0)) d = f x := by
    subst k
    simp [elementaryCover]
  exact hiter directions.length hlen directions.get

/-- The derivative on the elementary cover reduces to the Euclidean coordinate derivative. -/
private theorem euclideanSchwartzMonomialPartial_eq {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    let directions := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
    euclideanSchwartzMonomialPartial α β f x =
      (∏ i, (x i : ℂ) ^ α i) *
        iteratedFDeriv ℝ directions.length f x
          (fun j ↦ EuclideanSpace.single (directions.get j) 1) := by
  let E := EuclideanSpace ℝ (Fin m)
  let X := E × EuclideanSpace ℝ (Fin 0)
  let P : X →L[ℝ] E := ContinuousLinearMap.fst ℝ E _
  let lift (i : Fin m) : X := (EuclideanSpace.single i 1, 0)
  let directions := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
  have hdirs : (List.ofFn (fun i ↦ List.replicate (β i) (lift i))).flatten ++
      (List.ofFn (fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
        ((0 : E), EuclideanSpace.single i 1))).flatten = directions.map lift := by
    simp [directions, List.ofFn_eq_map, List.flatMap, Function.comp_def]
  unfold euclideanSchwartzMonomialPartial elementaryPartial
  change (∏ i, (x i : ℂ) ^ α i) *
    (fun l : List X ↦ iteratedFDeriv ℝ l.length ((f : E → ℂ) ∘ P) (x, 0) l.get) _ = _
  rw [hdirs]
  have hderiv (l : List (Fin m)) :
      iteratedFDeriv ℝ (l.map lift).length ((f : E → ℂ) ∘ P) (x, 0) (l.map lift).get =
        iteratedFDeriv ℝ l.length f x (fun j ↦ EuclideanSpace.single (l.get j) 1) := by
    rw [P.iteratedFDeriv_comp_right (f := (f : E → ℂ)) f.smooth' (x, 0) (by simp),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    let eval (s : Σ n, Fin n → X) :=
      iteratedFDeriv ℝ s.1 f x (fun j ↦ P (s.2 j))
    have hl : l.map lift = List.ofFn (lift ∘ l.get) := by
      rw [← List.map_ofFn, List.ofFn_get]
    change eval (List.equivSigmaTuple (l.map lift)) = _
    rw [hl]
    exact congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨l.length, lift ∘ l.get⟩)
  exact congrArg (_ * ·) (hderiv directions)

/-- The weight in the Euclidean convergence criterion adds the unweighted derivative norm. -/
private theorem euclideanSchwartzWeightedDeriv_eq_norms {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzWeightedDeriv α β f x =
      ‖euclideanSchwartzMonomialPartial 0 β f x‖ +
        ‖euclideanSchwartzMonomialPartial α β f x‖ := by
  rw [euclideanSchwartzMonomialPartial_eq, euclideanSchwartzMonomialPartial_eq]
  simp [euclideanSchwartzWeightedDeriv, one_add_mul, ← Real.norm_eq_abs, norm_prod]

open Filter in
/-- Paper: Example D.1.10.3, p. 785. Supremum norms of the monomial-weighted
Euclidean partials generate the usual Schwartz topology. -/
theorem euclideanSchwartz_monomialSup_generates (m : ℕ) (hm : 1 ≤ m) :
    GeneratesSeminormTopology (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦
      fun f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ↦
        ⨆ x, (‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊ : ℝ≥0∞)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let S := 𝓢(E, ℂ)
  let I := (Fin m → ℕ) × (Fin m → ℕ)
  -- Pull back the seminorms of the elementary space with only Euclidean coordinates.
  let A : S →ₗ[ℂ] elementarySchwartzSubmodule m 0 0 PUnit.{1} :=
    { toFun := fun f ↦ ⟨fun g ↦ f g.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  let index (i : I) : ElementarySchwartzIndex m 0 0 := (i.1, i.2, 0, 0)
  let P : SeminormFamily ℂ S I := fun i ↦ (elementarySchwartzSeminorm (index i)).comp A
  have hvalues (i : I) (f : S) :
      ENNReal.ofReal (P i f) = ⨆ x, (‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊ : ℝ≥0∞) := by
    change ENNReal.ofReal (elementarySchwartzBound (A f).val (index i)).toReal = _
    rw [ENNReal.ofReal_toReal ((A f).property.2 (index i)).ne]
    have hfiber (xt : E × EuclideanSpace ℝ (Fin 0)) (a : Fin 0 → ℤ) (b : PUnit) :
        ((∏ k, (xt.1 k : ℂ) ^ (index i).1 k) * (∏ k, (a k : ℂ) ^ (index i).2.2.2 k)) *
          elementaryPartial (A f).val (index i).2.1 (index i).2.2.1 xt a b =
            euclideanSchwartzMonomialPartial i.1 i.2 f xt.1 := by
      obtain ⟨x, t⟩ := xt
      obtain rfl : t = 0 := Subsingleton.elim _ _
      obtain rfl : a = 0 := Subsingleton.elim _ _
      cases b
      simp only [Finset.univ_eq_empty (α := Fin 0), Finset.prod_empty, mul_one]
      rfl
    let b (x : E) : ℝ≥0∞ := ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊
    calc
      _ = ⨆ (xt : E × EuclideanSpace ℝ (Fin 0)) (_ : Fin 0 → ℤ) (_ : PUnit), b xt.1 :=
        iSup_congr fun xt ↦ iSup_congr fun a ↦ iSup_congr fun p ↦
          congrArg (fun z : ℂ ↦ (‖z‖₊ : ℝ≥0∞)) (hfiber xt a p)
      _ = _ := by
        simp only [iSup_const]
        exact (show Surjective (Prod.fst : E × EuclideanSpace ℝ (Fin 0) → E) from
          fun x ↦ ⟨(x, 0), rfl⟩).iSup_comp b
  have hbound (i : I) (f : S) {c : ℝ} (hc : 0 ≤ c) :
      P i f ≤ c ↔ ∀ x, ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤ c := by
    rw [← ENNReal.ofReal_le_ofReal_iff hc, hvalues, iSup_le_iff]
    simp only [ENNReal.coe_nnreal_eq, coe_nnNorm, ENNReal.ofReal_le_ofReal_iff hc]
  have hle (i : I) (f : S) (x : E) :
      ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤ P i f :=
    (hbound i f (apply_nonneg (P i) f)).mp le_rfl x
  refine ⟨P, ?_, hvalues⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  let lP : Filter S := ⨅ i, (𝓝 (0 : ℝ)).comap (P i)
  have hP (l : Filter S) :
      l ≤ lP ↔ ∀ (i : I) ε, 0 < ε → ∀ᶠ f in l, P i f < ε := by
    simp only [lP, le_iInf_iff, ← Filter.map_le_iff_le_comap]
    change (∀ i, Tendsto (P i) l (𝓝 0)) ↔ _
    simp only [Metric.tendsto_nhds, Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg (P _) _)]
  -- The two convergence criteria give the same neighborhood filter at zero.
  have ht (l : Filter S) : l ≤ 𝓝 (0 : S) ↔ l ≤ lP := by
    refine Filter.tendsto_id'.symm.trans
      ((schwartzMap_euclidean_tendsto_iff (m := m) l (id : S → S) 0).trans ?_)
    refine Iff.trans ?_ (hP l).symm
    simp only [id_eq, FunLike.coe_zero, sub_zero]
    constructor
    · intro h i ε hε
      filter_upwards [h i.1 i.2 (ε / 2) (half_pos hε)] with f hf
      apply ((hbound i f (half_pos hε).le).mpr fun x ↦ ?_).trans_lt (half_lt_self hε)
      have hfx := hf x
      rw [euclideanSchwartzWeightedDeriv_eq_norms] at hfx
      exact ((le_add_of_nonneg_left (norm_nonneg _)).trans_lt hfx).le
    · intro h α β ε hε
      filter_upwards [h (0, β) (ε / 2) (half_pos hε), h (α, β) (ε / 2) (half_pos hε)]
        with f hf₀ hf x
      rw [euclideanSchwartzWeightedDeriv_eq_norms]
      exact (add_lt_add ((hle (0, β) f x).trans_lt hf₀)
        ((hle (α, β) f x).trans_lt hf)).trans_eq (add_halves ε)
  exact le_antisymm ((ht _).mp le_rfl) ((ht _).mpr le_rfl)

section EuclideanSchwartzLp

open LineDeriv SchwartzMap

local notation "Euc[" m "]" => EuclideanSpace ℝ (Fin m)
local notation "Sch[" m "]" => 𝓢(Euc[m], ℂ)

private def coordDirections {m : ℕ} (β : Fin m → ℕ) : List (Euc[m]) :=
  (List.ofFn fun i ↦ List.replicate (β i) (EuclideanSpace.single i 1)).flatten

private def monomialPartialCLM {m : ℕ} (α β : Fin m → ℕ) : Sch[m] →L[ℂ] Sch[m] :=
  SchwartzMap.smulLeftCLM ℂ (fun x : Euc[m] ↦ ∏ i, (x i : ℂ) ^ α i) ∘L
    iteratedLineDerivOpCLM ℂ (Sch[m]) (coordDirections β).get

private theorem monomial_hasTemperateGrowth {m : ℕ} (α : Fin m → ℕ) :
    (fun x : Euc[m] ↦ ∏ i, (x i : ℂ) ^ α i).HasTemperateGrowth := by
  generalize Finset.univ (α := Fin m) = s
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const _
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasTemperateGrowth
    exact HasTemperateGrowth.fun_mul (HasTemperateGrowth.fun_pow h (α i)) ih

private theorem monomialPartialCLM_apply {m : ℕ} (α β : Fin m → ℕ) (f : Sch[m]) :
    (monomialPartialCLM α β f : Euc[m] → ℂ) = euclideanSchwartzMonomialPartial α β f := by
  funext x
  simp only [monomialPartialCLM, ContinuousLinearMap.comp_apply, iteratedLineDerivOpCLM_apply,
    smulLeftCLM_apply_apply (monomial_hasTemperateGrowth α), smul_eq_mul,
    iteratedLineDerivOp_eq_iteratedFDeriv, euclideanSchwartzMonomialPartial]
  congr 1
  let L : Euc[m] × Euc[0] →L[ℝ] Euc[m] := ContinuousLinearMap.fst ℝ (Euc[m]) (Euc[0])
  let d : List (Euc[m] × Euc[0]) :=
    (List.ofFn fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0)).flatten
  have hzero : (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : Euc[m]), EuclideanSpace.single i (1 : ℝ))).flatten = [] := rfl
  unfold elementaryPartial
  dsimp only
  have hdirs : d ++ (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : Euc[m]), EuclideanSpace.single i (1 : ℝ))).flatten = d := by
    rw [hzero, List.append_nil]
  refine Eq.trans ?_ (congrArg (fun w : List (Euc[m] × Euc[0]) ↦
    iteratedFDeriv ℝ w.length ((f : Euc[m] → ℂ) ∘ L) (x, 0) w.get) hdirs).symm
  change iteratedFDeriv ℝ (coordDirections β).length f x (coordDirections β).get =
    iteratedFDeriv ℝ d.length ((f : Euc[m] → ℂ) ∘ L) (x, 0) d.get
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) _ (by simp)]
  change _ = iteratedFDeriv ℝ d.length f x (fun i ↦ L (d.get i))
  have hd : d.map L = coordDirections β := by
    simp only [d, coordDirections, List.map_flatten, List.map_ofFn]
    congr 2
    funext i
    simp [List.map_replicate, L]
  rw [← hd]
  have hg : (d.map L).get = fun i ↦ L (d.get (i.cast (List.length_map L))) := by
    funext i
    simp [List.get_eq_getElem]
  rw [hg]
  have hcast {n k : ℕ} (h : n = k) (v : Fin k → Euc[m]) :
      iteratedFDeriv ℝ n f x (fun i ↦ v (i.cast h)) = iteratedFDeriv ℝ k f x v := by
    subst n
    rfl
  exact hcast (List.length_map L) (fun i ↦ L (d.get i))

/-- The closed unit cube with lower corner `x`, in Euclidean coordinates. -/
private def unitCube {m : ℕ} (x : Euc[m]) : Set Euc[m] :=
  WithLp.ofLp ⁻¹' Icc (WithLp.ofLp x) (fun j ↦ x j + 1)

/-- Integrating the norm of a Schwartz function over a unit cube is bounded by
its global Lᵖ norm, by Hölder on a set of measure one. -/
private theorem unitCube_integral_norm_le_toLp {m : ℕ} (x : Euc[m]) (g : Sch[m])
    (q : ℝ≥0∞) (hq : 1 ≤ q) :
    (∫ y in unitCube x, ‖g y‖) ≤ ‖g.toLp q volume‖ := by
  let ν := (volume : Measure Euc[m]).restrict (unitCube x)
  have hvol : ν univ = 1 := by
    rw [show ν univ = volume (unitCube x) from Measure.restrict_apply_univ _, unitCube,
      (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi]
    simp
  have hg : AEStronglyMeasurable (g : Euc[m] → ℂ) ν :=
    g.continuous.aestronglyMeasurable
  have hle : eLpNorm (g : Euc[m] → ℂ) 1 ν ≤ eLpNorm (g : Euc[m] → ℂ) q volume := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hg).trans ?_
    rw [hvol, ENNReal.one_rpow, mul_one]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [SchwartzMap.norm_toLp, integral_norm_eq_lintegral_eNorm hg,
    ← eLpNorm_one_eq_lintegral_eNorm hg]
  exact ENNReal.toReal_mono (g.eLpNorm_lt_top q volume).ne hle

/-- The multi-index with a derivative in each coordinate of `s` and order zero elsewhere. -/
private def squarefreeMultiIndex {m : ℕ} (s : Finset (Fin m)) : Fin m → ℕ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- Differentiating a coordinate mixed partial adds one to its multi-index. -/
private theorem euclideanPartial_fderiv_single {m : ℕ} (β : Fin m → ℕ) (g : Sch[m])
    (x : Euc[m]) (j : Fin m) :
    fderiv ℝ (euclideanSchwartzMonomialPartial 0 β g) x (EuclideanSpace.single j 1) =
      euclideanSchwartzMonomialPartial 0 (β + Pi.single j 1) g x := by
  let indices (δ : Fin m → ℕ) := (List.finRange m).flatMap fun i ↦ List.replicate (δ i) i
  let v (i : Fin m) := EuclideanSpace.single i (1 : ℝ)
  let D (l : List (Fin m)) (y : Euc[m]) :=
    iteratedFDeriv ℝ l.length g y (fun i ↦ v (l.get i))
  have hD (δ : Fin m → ℕ) : euclideanSchwartzMonomialPartial 0 δ g = D (indices δ) := by
    funext y
    simp [euclideanSchwartzMonomialPartial_eq, D, v, indices]
  have hcount (δ : Fin m → ℕ) (i : Fin m) : (indices δ).count i = δ i := by
    dsimp only [indices]
    rw [List.count_flatMap, ← Fin.sum_univ_def]
    simp [List.count_replicate]
  have hperm : (j :: indices β).Perm (indices (β + Pi.single j 1)) := by
    rw [List.perm_iff_count]
    intro i
    simp only [List.count_cons, hcount, beq_iff_eq, Pi.add_apply, Pi.single_apply, eq_comm (a := j)]
  rw [hD, hD]
  have hd := (g.smooth ⊤).differentiable_iteratedFDeriv
    (mod_cast ENat.natCast_lt_top (indices β).length) x
  exact (hd.iteratedFDeriv_succ_apply_left' (m := fun i ↦ v ((j :: indices β).get i))).symm.trans
    (iteratedFDeriv_apply_list_perm g.smooth' v hperm x)

/-- The fundamental theorem of calculus, averaged over a unit interval. -/
private theorem enorm_le_unitInterval {U V : ℝ → ℂ} (h : ∀ t, HasDerivAt U (V t) t)
    (hV : Continuous V) (a : ℝ) :
    ‖U a‖ₑ ≤ (∫⁻ t in Icc a (a+1), ‖U t‖ₑ) + ∫⁻ t in Icc a (a+1), ‖V t‖ₑ := by
  let μ := (volume : Measure ℝ).restrict (Icc a (a+1))
  have hvol : μ univ = 1 := by simp [μ, Real.volume_Icc]
  let : IsProbabilityMeasure μ := ⟨hvol⟩
  have hU : Continuous U := continuous_iff_continuousAt.mpr fun t ↦ (h t).continuousAt
  have hUi : Integrable U μ := hU.continuousOn.integrableOn_Icc
  have hVi : Integrable V μ := hV.continuousOn.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc a (a+1)) : ‖U a‖ ≤ ‖U t‖ + ∫ v, ‖V v‖ ∂μ := by
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := t)
      (fun v _ ↦ h v) (hV.intervalIntegrable _ _)
    have hd : ‖U t - U a‖ ≤ ∫ v, ‖V v‖ ∂μ := calc
      _ ≤ ∫ v in a..t, ‖V v‖ := heq ▸ intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ _ := by
        rw [intervalIntegral.integral_of_le ht.1]
        exact setIntegral_mono_set hVi.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
          (Filter.Eventually.of_forall (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)))
    exact (norm_le_insert' (U a) (U t)).trans (by rw [norm_sub_rev]; linarith)
  have hreal := integral_mono_ae (integrable_const (μ := μ) ‖U a‖)
    (hUi.norm.add (integrable_const (∫ v, ‖V v‖ ∂μ)))
    ((ae_restrict_mem measurableSet_Icc).mono hpoint)
  simp only [Pi.add_apply] at hreal
  rw [integral_add hUi.norm (integrable_const _)] at hreal
  simp only [integral_const, probReal_univ, one_smul] at hreal
  rw [← ofReal_integral_norm_eq_lintegral_eNorm hUi, ← ofReal_integral_norm_eq_lintegral_eNorm hVi,
    ← ENNReal.ofReal_add (integral_nonneg fun _ ↦ norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _),
    ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Inserting a new coordinate increments precisely that component of the multi-index. -/
private theorem squarefreeMultiIndex_insert {m : ℕ} {s : Finset (Fin m)} {i : Fin m}
    (hi : i ∉ s) : squarefreeMultiIndex (insert i s) = squarefreeMultiIndex s + Pi.single i 1 := by
  funext j
  by_cases hj : j = i
  · subst j; simp [squarefreeMultiIndex, hi]
  · simp [squarefreeMultiIndex, hj, Pi.single_eq_of_ne]

/-- Evaluation at the lower corner of a unit cube is bounded by the integrals
of the square-free partials over that cube. In one variable this is the
fundamental theorem of calculus averaged over the unit interval. In multiple
variables the one-variable bounds are iterated using Fubini. -/
private theorem euclideanSchwartz_norm_le_unitCube_integrals {m : ℕ} (g : Sch[m]) (x : Euc[m]) :
    ‖g x‖ ≤ ∑ s : Finset (Fin m),
      ∫ y in unitCube x, ‖euclideanSchwartzMonomialPartial 0 (squarefreeMultiIndex s) g y‖ := by
  classical
  let D (β : Fin m → ℕ) := euclideanSchwartzMonomialPartial 0 β g
  have hc (β : Fin m → ℕ) : Continuous (D β) := by
    rw [show D β = _ from (monomialPartialCLM_apply 0 β g).symm]
    exact (monomialPartialCLM 0 β g).continuous
  let u (β : Fin m → ℕ) (w : Fin m → ℝ) := ‖D β (WithLp.toLp 2 w)‖ₑ
  have hu (β : Fin m → ℕ) : Measurable (u β) :=
    ((hc β).comp (PiLp.continuous_toLp _ _)).eNorm.measurable
  let μ (i : Fin m) := (volume : Measure ℝ).restrict (Icc (x i) (x i + 1))
  have hslice (β : Fin m → ℕ) (w : Fin m → ℝ) (i : Fin m) (hw : w i = x i) :
      u β w ≤ (∫⁻ v, u β (update w i v) ∂(μ i)) +
        ∫⁻ v, u (β + Pi.single i 1) (update w i v) ∂(μ i) := by
    let path (t : ℝ) := WithLp.toLp 2 (update w i t)
    have hp (t : ℝ) : HasDerivAt path (EuclideanSpace.single i 1) t := by
      have heq : path = fun s : ℝ ↦ path 0 + s • EuclideanSpace.single i 1 := by
        funext s
        ext j
        by_cases hj : j = i
        · subst j
          simp [path]
        · simp [path, EuclideanSpace.single, hj]
      rw [heq]
      simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (path 0)
    have hd (t : ℝ) : HasDerivAt (fun s ↦ D β (path s)) (D (β + Pi.single i 1) (path t)) t := by
      have hdif : DifferentiableAt ℝ (D β) (path t) := by
        rw [show D β = _ from (monomialPartialCLM_apply 0 β g).symm]
        exact (monomialPartialCLM 0 β g).differentiableAt
      dsimp only [D]
      rw [← euclideanPartial_fderiv_single]
      exact hdif.hasFDerivAt.comp_hasDerivAt t (hp t)
    have h := enorm_le_unitInterval hd ((hc _).comp (continuous_iff_continuousAt.mpr
      fun t ↦ (hp t).continuousAt)) (x i)
    simpa only [u, μ, path, ← hw, update_eq_self] using h
  let (i : Fin m) : IsFiniteMeasure (μ i) := by dsimp [μ]; infer_instance
  have h (s : Finset (Fin m)) (β : Fin m → ℕ) (w : Fin m → ℝ)
      (hw : ∀ i ∈ s, w i = x i) :
      u β w ≤ ∑ t ∈ s.powerset, lmarginal μ s (u (β + squarefreeMultiIndex t)) w := by
    induction s using Finset.induction_on generalizing β w with
    | empty =>
      have hz : squarefreeMultiIndex (∅ : Finset (Fin m)) = 0 := by
        funext i
        simp [squarefreeMultiIndex]
      simp [hz]
    | @insert i s hi ih =>
      have hw' (v : ℝ) (j : Fin m) (hj : j ∈ s) : update w i v j = x j := by
        rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
        exact hw j (Finset.mem_insert_of_mem hj)
      apply (hslice β w i (hw i (Finset.mem_insert_self ..))).trans
      apply (add_le_add (lintegral_mono fun v ↦ ih _ _ (hw' v))
        (lintegral_mono fun v ↦ ih _ _ (hw' v))).trans_eq
      have hsum (δ : Fin m → ℕ) :
          (∫⁻ v, ∑ t ∈ s.powerset, lmarginal μ s (u (δ + squarefreeMultiIndex t))
            (update w i v) ∂(μ i)) =
            ∑ t ∈ s.powerset, lmarginal μ (insert i s) (u (δ + squarefreeMultiIndex t)) w := by
        rw [lintegral_finsetSum]
        · exact Finset.sum_congr rfl fun t _ ↦ (lmarginal_insert _ (hu _) hi w).symm
        · exact fun t _ ↦ ((hu _).lmarginal μ).comp (continuous_const.update i continuous_id).measurable
      rw [hsum, hsum, Finset.sum_powerset_insert hi]
      congr 1
      refine Finset.sum_congr rfl fun t ht ↦ ?_
      have hit : i ∉ t := fun hj ↦ hi (Finset.mem_powerset.mp ht hj)
      rw [squarefreeMultiIndex_insert hit, add_assoc, add_comm (Pi.single i 1)]
  have hl := h Finset.univ 0 x.ofLp (fun _ _ ↦ rfl)
  simp only [Finset.powerset_univ, lmarginal_univ, zero_add] at hl
  have hp : MeasurePreserving (WithLp.toLp 2) (Measure.pi μ) (volume.restrict (unitCube x)) := by
    have hset : MeasurableSet (unitCube x) :=
      measurableSet_Icc.preimage (PiLp.continuous_ofLp 2 _).measurable
    convert (PiLp.volume_preserving_toLp (Fin m)).restrict_preimage hset using 1
    change Measure.pi μ = (Measure.pi _).restrict (Icc x.ofLp (fun j ↦ x j + 1))
    rw [← pi_univ_Icc, Measure.restrict_pi_pi]
  have hterm (β : Fin m → ℕ) : (∫⁻ w, u β w ∂Measure.pi μ) =
      ENNReal.ofReal (∫ y in unitCube x, ‖D β y‖) := by
    have hInt : Integrable (D β) (volume.restrict (unitCube x)) := by
      rw [show D β = _ from (monomialPartialCLM_apply 0 β g).symm]
      exact (monomialPartialCLM 0 β g).integrable.integrableOn
    rw [ofReal_integral_norm_eq_lintegral_eNorm hInt]
    exact hp.lintegral_comp (hc β).eNorm.measurable
  simp_rw [hterm] at hl
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun _ _ ↦
    integral_nonneg fun _ ↦ norm_nonneg _)).mp (by
      simpa only [u, D, WithLp.toLp_ofLp, euclideanSchwartzMonomialPartial_zero, ofReal_norm] using hl)

/-- The product rule for one coordinate of a monomial-weighted mixed partial. -/
private theorem monomialPartial_fderiv_single {m : ℕ} (α β : Fin m → ℕ) (f : Sch[m])
    (y : Euc[m]) (i : Fin m) :
    fderiv ℝ (euclideanSchwartzMonomialPartial α β f) y (EuclideanSpace.single i 1) =
      euclideanSchwartzMonomialPartial α (β + Pi.single i 1) f y +
        (α i : ℂ) * euclideanSchwartzMonomialPartial (α - Pi.single i 1) β f y := by
  let M (δ : Fin m → ℕ) (z : Euc[m]) := ∏ j, (z j : ℂ) ^ δ j
  let D (δ : Fin m → ℕ) := euclideanSchwartzMonomialPartial 0 δ f
  have hMD (a b : Fin m → ℕ) :
      euclideanSchwartzMonomialPartial a b f = fun z ↦ M a z * D b z := by
    funext z
    simp [M, D, euclideanSchwartzMonomialPartial]
  let c (j : Fin m) := Complex.ofRealCLM.comp (EuclideanSpace.proj j : Euc[m] →L[ℝ] ℝ)
  have hc (j : Fin m) : HasFDerivAt (fun z : Euc[m] ↦ (z j : ℂ)) (c j) y := (c j).hasFDerivAt
  have hM := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ ↦ (hc j).pow (α j))
  have hweight : fderiv ℝ (M α) y (EuclideanSpace.single i 1) =
      (α i : ℂ) * M (α - Pi.single i 1) y := by
    rw [show fderiv ℝ (M α) y = _ from hM.fderiv, sum_apply,
      Finset.sum_eq_single i]
    · dsimp only [M]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      have hrest : (∏ j ∈ Finset.univ.erase i, (y j : ℂ) ^ ((α - Pi.single i 1 : Fin m → ℕ) j)) =
          ∏ j ∈ Finset.univ.erase i, (y j : ℂ) ^ α j := by
        exact Finset.prod_congr rfl fun j hj ↦ by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest]
      simp [c, nsmul_eq_mul]
      ring
    · intro j _ hji
      simp [c, EuclideanSpace.single, hji]
    · simp
  have hD : DifferentiableAt ℝ (D β) y := by
    rw [show D β = _ from (monomialPartialCLM_apply 0 β f).symm]
    exact (monomialPartialCLM 0 β f).differentiableAt
  rw [hMD, fderiv_fun_mul hM.differentiableAt hD]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hMD α (β + Pi.single i 1), hMD (α - Pi.single i 1) β]
  change M α y * fderiv ℝ (D β) y _ + D β y * fderiv ℝ (M α) y _ = _
  rw [hweight, show fderiv ℝ (D β) y (EuclideanSpace.single i 1) = _ from
    euclideanPartial_fderiv_single β f y i]
  dsimp only [D]
  ring

/-- The square-free partial in coordinates `s` of a monomial-weighted partial,
expanded by the product rule. Each subset `t` lists the coordinates in which
the derivative acts on the monomial. -/
private theorem euclideanSchwartz_monomialPartial_leibniz {m : ℕ}
    (α β : Fin m → ℕ) (s : Finset (Fin m)) (f : Sch[m]) (y : Euc[m]) :
    euclideanSchwartzMonomialPartial 0 (squarefreeMultiIndex s) (monomialPartialCLM α β f) y =
      ∑ t ∈ s.powerset, (∏ j ∈ t, (α j : ℂ)) *
        euclideanSchwartzMonomialPartial (α - squarefreeMultiIndex t)
          (β + squarefreeMultiIndex (s \ t)) f y := by
  classical
  induction s using Finset.induction_on generalizing y with
  | empty =>
    have hz : squarefreeMultiIndex (∅ : Finset (Fin m)) = 0 := by ext; simp [squarefreeMultiIndex]
    have hsub : α - 0 = α := funext fun j ↦ Nat.sub_zero _
    simp [hz, hsub, euclideanSchwartzMonomialPartial_zero, monomialPartialCLM_apply]
  | @insert i s hi ih =>
    let A (t : Finset (Fin m)) := α - squarefreeMultiIndex t
    let B (t : Finset (Fin m)) := β + squarefreeMultiIndex (s \ t)
    let c (t : Finset (Fin m)) : ℂ := ∏ j ∈ t, (α j : ℂ)
    let T (t : Finset (Fin m)) := euclideanSchwartzMonomialPartial (A t) (B t) f
    have hT (t : Finset (Fin m)) : DifferentiableAt ℝ (T t) y := by
      rw [show T t = _ from (monomialPartialCLM_apply ..).symm]
      exact (monomialPartialCLM (A t) (B t) f).differentiableAt
    have hfun : euclideanSchwartzMonomialPartial 0 (squarefreeMultiIndex s)
        (monomialPartialCLM α β f) = fun z ↦ ∑ t ∈ s.powerset, c t * T t z := funext ih
    rw [squarefreeMultiIndex_insert hi, ← euclideanPartial_fderiv_single, hfun,
      fderiv_fun_sum (fun t _ ↦ (hT t).const_mul (c t)), sum_apply, Finset.sum_powerset_insert hi,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    have hit : i ∉ t := fun h ↦ hi (Finset.mem_powerset.mp ht h)
    have hst : i ∉ s \ t := Finset.notMem_sdiff_of_notMem_left hi
    have hAi : A t i = α i := by simp [A, squarefreeMultiIndex, hit]
    have hA : α - squarefreeMultiIndex (insert i t) = A t - Pi.single i 1 := by
      rw [squarefreeMultiIndex_insert hit]
      funext j
      exact (Nat.sub_sub ..).symm
    rw [fderiv_const_mul (hT t), smul_apply, smul_eq_mul]
    change c t * fderiv ℝ (euclideanSchwartzMonomialPartial (A t) (B t) f) y _ = _
    rw [monomialPartial_fderiv_single, hAi, Finset.prod_insert hit, hA,
      Finset.insert_sdiff_of_notMem _ hit, squarefreeMultiIndex_insert hst, ← add_assoc,
      Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hi]
    dsimp only [A, B, c]
    ring

/-- The unit-cube evaluation bound for a monomial-weighted partial, with each
term expressed as the integral of another monomial-weighted partial. -/
private theorem euclideanSchwartz_monomialPartial_le_unitCube_integrals {m : ℕ}
    (α β : Fin m → ℕ) (f : Sch[m]) (x : Euc[m]) :
    ‖euclideanSchwartzMonomialPartial α β f x‖ ≤
      ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, (∏ j ∈ t, (α j : ℝ)) *
        ∫ y in unitCube x,
          ‖euclideanSchwartzMonomialPartial (α - squarefreeMultiIndex t)
            (β + squarefreeMultiIndex (s \ t)) f y‖ := by
  rw [← monomialPartialCLM_apply]
  apply (euclideanSchwartz_norm_le_unitCube_integrals _ x).trans
  refine Finset.sum_le_sum fun s _ ↦ ?_
  let a (t : Finset (Fin m)) : ℝ := ∏ j ∈ t, (α j : ℝ)
  let g (t : Finset (Fin m)) :=
    monomialPartialCLM (α - squarefreeMultiIndex t) (β + squarefreeMultiIndex (s \ t)) f
  have hint (t : Finset (Fin m)) :
      IntegrableOn (fun y ↦ a t * ‖g t y‖) (unitCube x) volume :=
    ((g t).integrable.norm.const_mul (a t)).integrableOn
  simp_rw [← monomialPartialCLM_apply]
  change _ ≤ ∑ t ∈ s.powerset, a t * ∫ y in unitCube x, ‖g t y‖
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun t _ ↦ hint t)]
  refine integral_mono (monomialPartialCLM 0 (squarefreeMultiIndex s)
    (monomialPartialCLM α β f)).integrable.norm.integrableOn
    (integrable_finsetSum _ fun t _ ↦ hint t) (fun y ↦ ?_)
  rw [show (monomialPartialCLM 0 (squarefreeMultiIndex s) (monomialPartialCLM α β f)) y =
      _ from congrFun (monomialPartialCLM_apply ..) y, euclideanSchwartz_monomialPartial_leibniz]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun t _ ↦ by
    simp [a, g, monomialPartialCLM_apply, norm_prod]

/-- Paper: Example D.1.10.3(1)–(2), p. 785. For every real p at least one,
the Lᵖ norms of the monomial-weighted Euclidean partials generate the topology.
Deviation: The same statement includes p = 1 and p > 1. -/
theorem euclideanSchwartz_monomialLp_generates (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (volume : Measure (EuclideanSpace ℝ (Fin m))) (ENNReal.ofReal p)
      (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦ euclideanSchwartzMonomialPartial i.1 i.2) := by
  classical
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hp
  let : Fact (1 ≤ q) := ⟨hq⟩
  let U (i : (Fin m → ℕ) × (Fin m → ℕ)) :=
    SchwartzMap.toLpCLM ℂ ℂ q (volume : Measure Euc[m]) ∘L monomialPartialCLM i.1 i.2
  let P (i : (Fin m → ℕ) × (Fin m → ℕ)) :=
    (normSeminorm ℂ (Lp ℂ q (volume : Measure Euc[m]))).comp (U i).toLinearMap
  have hP (i : (Fin m → ℕ) × (Fin m → ℕ)) (f : Sch[m]) :
      P i f = ‖(monomialPartialCLM i.1 i.2 f).toLp q volume‖ := by
    change ‖(U i) f‖ = _
    rw [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply]
  refine ⟨?_, ⟨P, ?_, ?_⟩⟩
  · intro i f
    change MemLp (euclideanSchwartzMonomialPartial i.1 i.2 f) q volume
    rw [← monomialPartialCLM_apply]
    exact (monomialPartialCLM i.1 i.2 f).memLp q volume
  · obtain ⟨Q, hQ, hvalues⟩ := euclideanSchwartz_monomialSup_generates m hm
    refine hQ.congr (fun i ↦ ?_) (Seminorm.IsBounded.of_real fun i ↦ ?_)
    · obtain ⟨s, C, _, h⟩ := Seminorm.bound_of_continuous hQ (P i)
        ((U i).continuous.norm : Continuous fun f ↦ ‖U i f‖)
      exact ⟨s, C, h⟩
    · let index (s t : Finset (Fin m)) :=
        (i.1 - squarefreeMultiIndex t, i.2 + squarefreeMultiIndex (s \ t))
      let support := (Finset.univ : Finset (Finset (Fin m) × Finset (Fin m))).image
        (fun j ↦ index j.1 j.2)
      let C : ℝ := ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, ∏ j ∈ t, (i.1 j : ℝ)
      have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      refine ⟨support, C, fun f ↦ ?_⟩
      have hterm (s t : Finset (Fin m)) :
          P (index s t) f ≤ support.sup P f :=
        Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, rfl⟩)
      have hle (x : Euc[m]) : ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤
          C * support.sup P f := calc
        _ ≤ _ := euclideanSchwartz_monomialPartial_le_unitCube_integrals i.1 i.2 f x
        _ ≤ ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, (∏ j ∈ t, (i.1 j : ℝ)) *
            support.sup P f := by
          refine Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun t _ ↦ ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          change (∫ y in unitCube x, ‖euclideanSchwartzMonomialPartial
            (index s t).1 (index s t).2 f y‖) ≤ support.sup P f
          rw [← monomialPartialCLM_apply]
          exact (unitCube_integral_norm_le_toLp x _ q hq).trans
            ((hP (index s t) f).symm ▸ hterm s t)
        _ = _ := by simp only [C, Finset.sum_mul]
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (apply_nonneg _ _))).mp
      rw [LinearMap.id_apply, hvalues]
      exact iSup_le fun x ↦ by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (hle x)
  · intro i f
    rw [hP, SchwartzMap.norm_toLp,
      ENNReal.ofReal_toReal ((monomialPartialCLM i.1 i.2 f).eLpNorm_lt_top q volume).ne,
      monomialPartialCLM_apply]

end EuclideanSchwartzLp

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. On the torus take the mixed partial
by differentiating the periodic lift.
Deviation: We evaluate the lifted partial at the representative in the unit cube. -/
def torusSchwartzPartial {n : ℕ} (β : Fin n → ℕ)
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) : ℂ :=
  elementaryPartial f 0 β
    (0, WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (z i)).val)) 0 PUnit.unit

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. The partial of order zero evaluates
the original function on the torus.
Deviation: Sanity check for the chosen lift. -/
theorem torusSchwartzPartial_zero {n : ℕ}
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) :
    torusSchwartzPartial 0 f z = f (0, z, 0, PUnit.unit) := by
  rw [torusSchwartzPartial, elementaryPartial_zero]
  have hz : (fun i ↦ (((AddCircle.equivIco (1 : ℝ) 0 (z i)).val : ℝ) : AddCircle (1 : ℝ))) = z :=
    funext fun i ↦ (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)
  simp only [elementaryCover]
  rw [hz]

/-- Paper: Example D.1.10.4, p. 785. Supremum norms of the torus partials
generate the smooth topology. -/
theorem torusSchwartz_sup_generates (n : ℕ) (hn : 1 ≤ n) :
    GeneratesSeminormTopology (fun β : Fin n → ℕ ↦
      fun f : ElementarySchwartz 0 n 0 PUnit ↦
        ⨆ z, (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞)) := by
  let idx (β : Fin n → ℕ) : ElementarySchwartzIndex 0 n 0 := (0, 0, β, 0)
  have hidx (i : ElementarySchwartzIndex 0 n 0) : idx i.2.2.1 = i := by
    rcases i with ⟨a, b, c, d⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    have hd : d = 0 := Subsingleton.elim _ _
    subst a; subst b; subst d
    rfl
  have hbound (β : Fin n → ℕ) (f : ElementarySchwartz 0 n 0 PUnit) :
      elementarySchwartzBound f.val (idx β) =
        ⨆ z, (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞) := by
    simp only [elementarySchwartzBound, idx, Finset.univ_eq_empty (α := Fin 0),
      Finset.prod_empty, one_mul]
    apply le_antisymm
    · refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
      have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = PUnit.unit := Subsingleton.elim _ _
      subst a; subst b
      let z : Fin n → AddCircle (1 : ℝ) := fun i ↦ (xt.2 i : AddCircle (1 : ℝ))
      have heq : elementaryPartial f.val 0 β xt 0 PUnit.unit = torusSchwartzPartial β f z := by
        unfold torusSchwartzPartial
        apply (elementaryPartial_descends f.val 0 β 0 PUnit.unit (f.property.1 0 PUnit.unit)).2
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · simp only [elementaryCover]
          apply Prod.ext
          · apply funext
            intro i
            exact ((AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)).symm
          · rfl
      rw [heq]
      exact le_iSup (fun z ↦ (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞)) z
    · refine iSup_le fun z ↦ ?_
      exact le_iSup_of_le (0, WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (z i)).val))
        (le_iSup_of_le 0 (le_iSup_of_le PUnit.unit le_rfl))
  refine ⟨fun β ↦ elementarySchwartzSeminorm (idx β), ?_, ?_⟩
  · let e : (Fin n → ℕ) ≃ ElementarySchwartzIndex 0 n 0 :=
      Equiv.ofBijective idx ⟨fun a b h ↦ congrArg (fun i : ElementarySchwartzIndex 0 n 0 ↦ i.2.2.1) h,
        fun i ↦ ⟨i.2.2.1, hidx i⟩⟩
    exact (elementarySchwartz_withSeminorms (m := 0) (n := n) (r := 0) (F := PUnit)).congr_equiv e
  · intro β f
    change ENNReal.ofReal (elementarySchwartzBound f.val (idx β)).toReal = _
    rw [ENNReal.ofReal_toReal (f.property.2 (idx β)).ne, hbound]

section TorusLp

open scoped ContDiff

local notation "Torus" n => (Fin n → AddCircle (1 : ℝ))
local notation "TorusSchwartz" n => (ElementarySchwartz 0 n 0 PUnit)
local notation "torusHaar" n =>
  (Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle (T := (1 : ℝ))))
local notation "circleHaar" => (AddCircle.haarAddCircle (T := (1 : ℝ)))

/-- Evaluating a torus partial on a real lift agrees with evaluating it on the quotient. -/
private theorem torusSchwartzPartial_coe {n : ℕ} (β : Fin n → ℕ)
    (f : TorusSchwartz n) (t : EuclideanSpace ℝ (Fin n)) :
    torusSchwartzPartial β f (fun i ↦ (t i : AddCircle (1 : ℝ))) =
      elementaryPartial f 0 β (0, t) 0 PUnit.unit := by
  let z : Torus n := fun i ↦ (t i : AddCircle (1 : ℝ))
  change torusSchwartzPartial β f z = _
  unfold torusSchwartzPartial
  apply (elementaryPartial_descends f 0 β 0 PUnit.unit (f.property.1 0 PUnit.unit)).2
  have hz : (fun i ↦ (((AddCircle.equivIco (1 : ℝ) 0 (z i)).val : ℝ) :
      AddCircle (1 : ℝ))) = z :=
    funext fun i ↦ (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)
  simp only [elementaryCover]
  rw [hz]

/-- Mixed partials descend continuously along the open quotient map from the real cover. -/
private theorem continuous_torusSchwartzPartial {n : ℕ} (β : Fin n → ℕ)
    (f : TorusSchwartz n) : Continuous (torusSchwartzPartial β f) := by
  have hq : IsOpenQuotientMap (fun t : EuclideanSpace ℝ (Fin n) ↦
      fun i ↦ (t i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  apply hq.continuous_comp_iff.mp
  simp only [Function.comp_def, torusSchwartzPartial_coe]
  have hs := (elementaryPartial_descends f 0 β 0 PUnit.unit (f.property.1 0 PUnit.unit)).1
  exact hs.continuous.comp (continuous_const.prodMk continuous_id)

/-- Varying a single circle coordinate in the real cover adds one derivative
in that coordinate to the mixed partial. -/
private theorem torusSchwartzPartial_hasDerivAt_update {n : ℕ} (β : Fin n → ℕ)
    (f : TorusSchwartz n) (z : Torus n) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ torusSchwartzPartial β f (update z j (s : AddCircle (1 : ℝ))))
      (torusSchwartzPartial (β + Pi.single j 1) f (update z j (t : AddCircle (1 : ℝ)))) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let X := EuclideanSpace ℝ (Fin 0) × E
  let v (i : Fin n) : X := (0, EuclideanSpace.single i 1)
  let dirs (γ : Fin n → ℕ) := (List.ofFn fun i ↦ List.replicate (γ i) (v i)).flatten
  let g (x : X) : ℂ := f (elementaryCover x 0 PUnit.unit)
  let D (γ : Fin n → ℕ) (x : X) :=
    iteratedFDeriv ℝ (dirs γ).length g x (dirs γ).get
  have hg : ContDiff ℝ (∞) g := f.property.1 0 PUnit.unit
  have hpartial (γ : Fin n → ℕ) (x : X) :
      elementaryPartial f 0 γ x 0 PUnit.unit = D γ x := rfl
  have hinsert : (v j :: dirs β).Perm (dirs (β + Pi.single j 1)) := by
    let indices (γ : Fin n → ℕ) := (List.finRange n).flatMap fun i ↦ List.replicate (γ i) i
    have hmap (γ : Fin n → ℕ) : (indices γ).map v = dirs γ := by
      simp only [indices, dirs, List.ofFn_eq_map, List.map_flatMap, List.map_replicate,
        List.flatten_eq_flatMap, List.flatMap_map, id_eq]
    have hcount (γ : Fin n → ℕ) (i : Fin n) : (indices γ).count i = γ i := by
      dsimp only [indices]
      rw [List.count_flatMap, ← Fin.sum_univ_def]
      simp [List.count_replicate]
    have hperm : (j :: indices β).Perm (indices (β + Pi.single j 1)) := by
      rw [List.perm_iff_count]
      intro i
      simp only [List.count_cons, hcount, beq_iff_eq, Pi.add_apply, Pi.single_apply,
        eq_comm (a := j)]
    simpa only [List.map_cons, hmap] using hperm.map v
  have hder (x : X) : fderiv ℝ (D β) x (v j) = D (β + Pi.single j 1) x := by
    have hdiff := hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top (dirs β).length) x
    have hcons := hdiff.iteratedFDeriv_succ_apply_left' (m := (v j :: dirs β).get)
    exact hcons.symm.trans (iteratedFDeriv_apply_list_perm hg id hinsert x)
  let r (i : Fin n) : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (z i)).val
  let b : X := (0, WithLp.toLp 2 (update r j 0))
  let path (s : ℝ) : X := b + s • v j
  have hpath : HasDerivAt path (v j) t := by
    simpa [path] using ((hasDerivAt_id t).smul_const (v j)).const_add b
  have hco (s : ℝ) : (fun i ↦ ((path s).2 i : AddCircle (1 : ℝ))) =
      update z j (s : AddCircle (1 : ℝ)) := by
    have hr (i : Fin n) : (r i : AddCircle (1 : ℝ)) = z i :=
      (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)
    funext i
    change ((update r j 0 i + s * (EuclideanSpace.single j (1 : ℝ)) i : ℝ) : AddCircle (1 : ℝ)) = _
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, EuclideanSpace.single, hr]
  have heq (γ : Fin n → ℕ) (s : ℝ) :
      D γ (path s) = torusSchwartzPartial γ f (update z j (s : AddCircle (1 : ℝ))) := by
    rw [← hco, torusSchwartzPartial_coe, hpartial]
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hD : ContDiff ℝ (∞) (D β) :=
    (ContinuousMultilinearMap.apply ℝ _ ℂ (dirs β).get).contDiff.comp
      (hg.iteratedFDeriv_right (by simp))
  have h := ((hD.differentiable (by simp) (path t)).hasFDerivAt).comp_hasDerivAt t hpath
  simpa only [Function.comp_def, hder, heq] using h

/-- The fundamental theorem of calculus bounds the norm at one point of a circle
slice by the integrals of the slice and its first derivative. -/
private theorem torusSchwartzPartial_slice_bound {n : ℕ} (β : Fin n → ℕ)
    (f : TorusSchwartz n) (z : Torus n) (j : Fin n) :
    ‖torusSchwartzPartial β f z‖ₑ ≤
      (∫⁻ u, ‖torusSchwartzPartial β f (update z j u)‖ₑ ∂circleHaar) +
      (∫⁻ u, ‖torusSchwartzPartial (β + Pi.single j 1) f (update z j u)‖ₑ ∂circleHaar) := by
  let U (u : AddCircle (1 : ℝ)) := torusSchwartzPartial β f (update z j u)
  let V (u : AddCircle (1 : ℝ)) := torusSchwartzPartial (β + Pi.single j 1) f (update z j u)
  have hupdate : Continuous (update z j) := continuous_const.update j continuous_id
  have hU : Continuous U := (continuous_torusSchwartzPartial β f).comp hupdate
  have hV : Continuous V := (continuous_torusSchwartzPartial _ f).comp hupdate
  have hUl : Integrable U circleHaar :=
    hU.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hVl : Integrable V circleHaar :=
    hV.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (z j)).val
  have ha : (a : AddCircle (1 : ℝ)) = z j :=
    (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z j)
  let D (s : ℝ) := V (s : AddCircle (1 : ℝ))
  have hD : Continuous D := hV.comp (AddCircle.continuous_mk' 1)
  have hfull :
      (∫ s in a..a + 1, ‖D s‖) = ∫ u, ‖V u‖ ∂circleHaar := by
    rw [AddCircle.integral_haarAddCircle]
    simpa [D] using AddCircle.intervalIntegral_preimage 1 a (fun u ↦ ‖V u‖)
  have hpoint (u : AddCircle (1 : ℝ)) :
      ‖U (z j)‖ ≤ ‖U u‖ + ∫ w, ‖V w‖ ∂circleHaar := by
    let b := AddCircle.equivIoc (1 : ℝ) a u
    have hb : ((b.val : ℝ) : AddCircle (1 : ℝ)) = u :=
      (AddCircle.equivIoc (1 : ℝ) a).symm_apply_apply u
    have hab : a ≤ b.val := b.property.1.le
    have hcalc : (∫ s in a..b.val, D s) = U u - U (z j) := by
      rw [← ha, ← hb]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ ↦ torusSchwartzPartial_hasDerivAt_update β f z j s)
        (hD.intervalIntegrable _ _)
    have hdiff : ‖U u - U (z j)‖ ≤ ∫ w, ‖V w‖ ∂circleHaar := calc
      _ ≤ ∫ s in a..b.val, ‖D s‖ := by
        rw [← hcalc]
        exact intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ s in a..a + 1, ‖D s‖ := by
        rw [intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_of_le (by linarith : a ≤ a + 1)]
        exact setIntegral_mono_set
          (hD.norm.intervalIntegrable a (a + 1)).1
          (ae_of_all _ fun s ↦ norm_nonneg (D s))
          (Filter.Eventually.of_forall (Ioc_subset_Ioc_right b.property.2))
      _ = _ := hfull
    exact (norm_le_insert' (U (z j)) (U u)).trans (by
      rw [norm_sub_rev]
      linarith)
  have hreal : ‖U (z j)‖ ≤ (∫ u, ‖U u‖ ∂circleHaar) + ∫ u, ‖V u‖ ∂circleHaar := by
    have h := integral_mono (integrable_const ‖U (z j)‖)
      (hUl.norm.add (integrable_const (∫ u, ‖V u‖ ∂circleHaar))) hpoint
    simpa [integral_add hUl.norm (integrable_const (∫ u, ‖V u‖ ∂circleHaar))] using h
  have hposU : 0 ≤ ∫ u, ‖U u‖ ∂circleHaar := integral_nonneg fun _ ↦ norm_nonneg _
  have hposV : 0 ≤ ∫ u, ‖V u‖ ∂circleHaar := integral_nonneg fun _ ↦ norm_nonneg _
  rw [← ofReal_integral_norm_eq_lintegral_eNorm hUl, ← ofReal_integral_norm_eq_lintegral_eNorm hVl,
    ← ENNReal.ofReal_add hposU hposV, ← ofReal_norm]
  simpa [U] using ENNReal.ofReal_le_ofReal hreal

/-- Averaging the one-coordinate estimate over each coordinate bounds the value
of a torus partial by the L¹ norms of its square-free further partials. -/
private theorem torusSchwartzPartial_norm_le_integrals {n : ℕ} (β : Fin n → ℕ)
    (f : TorusSchwartz n) (z : Torus n) :
    ‖torusSchwartzPartial β f z‖ ≤ ∑ s : Finset (Fin n),
      ∫ y, ‖torusSchwartzPartial (β + squarefreeMultiIndex s) f y‖ ∂(torusHaar n) := by
  classical
  have hc (γ : Fin n → ℕ) := continuous_torusSchwartzPartial γ f
  let u (γ : Fin n → ℕ) (w : Torus n) := ‖torusSchwartzPartial γ f w‖ₑ
  let μ (_ : Fin n) := circleHaar
  have hu (γ : Fin n → ℕ) : Measurable (u γ) := (hc γ).eNorm.measurable
  have h (s : Finset (Fin n)) (γ : Fin n → ℕ) (w : Torus n) :
      u γ w ≤ ∑ t ∈ s.powerset, lmarginal μ s (u (γ + squarefreeMultiIndex t)) w := by
    induction s using Finset.induction_on generalizing γ w with
    | empty =>
      have hzero : squarefreeMultiIndex (∅ : Finset (Fin n)) = 0 := by
        funext i
        simp [squarefreeMultiIndex]
      simp [hzero]
    | @insert i s hi ih =>
      calc
        u γ w ≤ (∫⁻ v, u γ (update w i v) ∂(μ i)) +
            (∫⁻ v, u (γ + Pi.single i 1) (update w i v) ∂(μ i)) :=
          torusSchwartzPartial_slice_bound γ f w i
        _ ≤ (∫⁻ v, ∑ t ∈ s.powerset,
              lmarginal μ s (u (γ + squarefreeMultiIndex t)) (update w i v) ∂(μ i)) +
            (∫⁻ v, ∑ t ∈ s.powerset,
              lmarginal μ s (u ((γ + Pi.single i 1) + squarefreeMultiIndex t))
                (update w i v) ∂(μ i)) :=
          add_le_add (lintegral_mono fun v ↦ ih _ _) (lintegral_mono fun v ↦ ih _ _)
        _ = _ := by
          have hsum (δ : Fin n → ℕ) :
              (∫⁻ v, ∑ t ∈ s.powerset,
                lmarginal μ s (u (δ + squarefreeMultiIndex t)) (update w i v) ∂(μ i)) =
                ∑ t ∈ s.powerset, lmarginal μ (insert i s) (u (δ + squarefreeMultiIndex t)) w := by
            rw [lintegral_finsetSum]
            · exact Finset.sum_congr rfl fun t _ ↦ (lmarginal_insert _ (hu _) hi w).symm
            · exact fun t _ ↦ ((hu _).lmarginal μ).comp
                (continuous_const.update i continuous_id).measurable
          rw [hsum, hsum, Finset.sum_powerset_insert hi]
          congr 1
          refine Finset.sum_congr rfl fun t ht ↦ ?_
          have hit : i ∉ t := fun hmem ↦ hi (Finset.mem_powerset.mp ht hmem)
          have hindex : Pi.single i 1 + squarefreeMultiIndex t =
              squarefreeMultiIndex (insert i t) := by
            funext j
            by_cases hji : j = i
            · subst j
              simp [squarefreeMultiIndex, hit]
            · simp [squarefreeMultiIndex, hji, Pi.single_eq_of_ne]
          rw [add_assoc, hindex]
  have hlin := h Finset.univ β z
  simp only [Finset.powerset_univ, lmarginal_univ] at hlin
  have hInt (s : Finset (Fin n)) :
      Integrable (torusSchwartzPartial (β + squarefreeMultiIndex s) f) (torusHaar n) :=
    (hc _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfin (s : Finset (Fin n)) :
      (∫⁻ y, u (β + squarefreeMultiIndex s) y ∂(torusHaar n)) ≠ ⊤ :=
    (hInt s).hasFiniteIntegral.ne
  have ht := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun s _ ↦ hfin s) hlin
  rw [ENNReal.toReal_sum (fun s _ ↦ hfin s)] at ht
  simpa only [u, toReal_eNorm, ← integral_norm_eq_lintegral_eNorm
    (Measurable.aestronglyMeasurable (hc _).measurable)] using ht

/-- On the pure torus stage, the canonical Schwartz seminorm is the supremum of
the corresponding mixed partial on the quotient. -/
private theorem torusSchwartzSeminorm_eq {n : ℕ}
    (i : ElementarySchwartzIndex 0 n 0) (f : TorusSchwartz n) :
    ENNReal.ofReal (elementarySchwartzSeminorm i f) =
      ⨆ z, (‖torusSchwartzPartial i.2.2.1 f z‖₊ : ℝ≥0∞) := by
  change ENNReal.ofReal (elementarySchwartzBound f.val i).toReal = _
  rw [ENNReal.ofReal_toReal (f.property.2 i).ne]
  obtain ⟨α, δ, β, γ⟩ := i
  obtain rfl : δ = 0 := Subsingleton.elim _ _
  simp only [elementarySchwartzBound, Finset.univ_eq_empty (α := Fin 0),
    Finset.prod_empty, one_mul]
  have h (xt : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n))
      (a : Fin 0 → ℤ) (b : PUnit) :
      elementaryPartial f 0 β xt a b =
        torusSchwartzPartial β f (fun j ↦ (xt.2 j : AddCircle (1 : ℝ))) := by
    obtain ⟨x, t⟩ := xt
    obtain rfl : x = 0 := Subsingleton.elim _ _
    obtain rfl : a = 0 := Subsingleton.elim _ _
    cases b
    exact (torusSchwartzPartial_coe β f t).symm
  simp only [h, iSup_const]
  refine (show Surjective (fun xt : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin n) ↦
    fun j ↦ (xt.2 j : AddCircle (1 : ℝ))) from ?_).iSup_comp
      (fun z ↦ (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞))
  intro z
  let t : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun j ↦ (AddCircle.equivIco (1 : ℝ) 0 (z j)).val)
  exact ⟨(0, t), funext fun j ↦ (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z j)⟩

/-- Paper: Example D.1.10.4, p. 785. With product probability Haar measure, the Lᵖ
norms of torus partials generate the smooth topology for each finite real p ≥ 1.
Deviation: The stage with only torus coordinates represents the smooth space. -/
theorem torusSchwartz_lp_generates (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle (T := (1 : ℝ))))
      (ENNReal.ofReal p) (torusSchwartzPartial (n := n)) := by
  -- The bounds also hold for the empty product.
  clear hn
  classical
  let μ := torusHaar n
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hp
  let : Fact (1 ≤ q) := ⟨hq⟩
  have hmem (i : Fin n → ℕ) (f : TorusSchwartz n) : MemLp (torusSchwartzPartial i f) q μ :=
    (continuous_torusSchwartzPartial i f).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let U (i : Fin n → ℕ) : (TorusSchwartz n) →ₗ[ℂ] Lp ℂ q μ :=
    { toFun := fun f ↦ (hmem i f).toLp (torusSchwartzPartial i f)
      map_add' := fun f g ↦ by
        rw [← MemLp.toLp_add]
        congr 1
        funext z
        exact elementaryPartial_add f.property.1 g.property.1 0 i _ 0 PUnit.unit
      map_smul' := fun c f ↦ by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        congr 1
        funext z
        exact elementaryPartial_smul c f.property.1 0 i _ 0 PUnit.unit }
  let P (i : Fin n → ℕ) := (normSeminorm ℂ (Lp ℂ q μ)).comp (U i)
  have hP (i : Fin n → ℕ) (f : TorusSchwartz n) :
      ENNReal.ofReal (P i f) = eLpNorm (torusSchwartzPartial i f) q μ := by
    change ENNReal.ofReal ‖(hmem i f).toLp _‖ = _
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal (hmem i f).eLpNorm_lt_top.ne]
  refine ⟨hmem, ⟨P, ?_, hP⟩⟩
  let Q : SeminormFamily ℂ (TorusSchwartz n) (ElementarySchwartzIndex 0 n 0) :=
    elementarySchwartzSeminorm
  have hQ : WithSeminorms Q := elementarySchwartz_withSeminorms
  have hQval (i : ElementarySchwartzIndex 0 n 0) (f : TorusSchwartz n) :
      ENNReal.ofReal (Q i f) = ⨆ z, (‖torusSchwartzPartial i.2.2.1 f z‖₊ : ℝ≥0∞) :=
    torusSchwartzSeminorm_eq i f
  refine hQ.congr (Seminorm.IsBounded.of_real fun i ↦ ?_)
    (Seminorm.IsBounded.of_real fun i ↦ ?_)
  · let j : ElementarySchwartzIndex 0 n 0 := (0, 0, i, 0)
    refine ⟨{j}, 1, fun f ↦ ?_⟩
    simp only [LinearMap.id_apply, Finset.sup_singleton, one_mul]
    apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg (Q j) f)).mp
    rw [hP]
    have hle := eLpNorm_le_of_ae_bound (μ := μ) (p := q) (hmem i f).aestronglyMeasurable
      (C := Q j f) (ae_of_all μ fun z ↦ ?_)
    · simpa only [measure_univ, ENNReal.one_rpow, one_mul] using hle
    · apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg (Q j) f)).mp
      rw [hQval]
      simpa only [ENNReal.coe_nnreal_eq, coe_nnNorm] using
        le_iSup (fun z ↦ (‖torusSchwartzPartial i f z‖₊ : ℝ≥0∞)) z
  · let index (s : Finset (Fin n)) := i.2.2.1 + squarefreeMultiIndex s
    let support := Finset.univ.image index
    refine ⟨support, Fintype.card (Finset (Fin n)), fun f ↦ ?_⟩
    have hterm (s : Finset (Fin n)) : P (index s) f ≤ support.sup P f :=
      Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
    have hL1 (j : Fin n → ℕ) : (∫ y, ‖torusSchwartzPartial j f y‖ ∂μ) ≤ P j f := by
      rw [← lpNorm_one_eq_integral_norm (hmem j f).aestronglyMeasurable, lpNorm]
      have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq (hmem j f).aestronglyMeasurable
      rw [measure_univ, ENNReal.one_rpow, mul_one, ← hP] at hle
      exact (ENNReal.toReal_mono (by finiteness) hle).trans_eq
        (ENNReal.toReal_ofReal (apply_nonneg _ _))
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))).mp
    rw [LinearMap.id_apply, hQval]
    apply iSup_le
    intro z
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∑ s : Finset (Fin n), ∫ y, ‖torusSchwartzPartial (index s) f y‖ ∂μ :=
        torusSchwartzPartial_norm_le_integrals i.2.2.1 f z
      _ ≤ ∑ _s : Finset (Fin n), support.sup P f :=
        Finset.sum_le_sum fun s _ ↦ (hL1 (index s)).trans (hterm s)
      _ = _ := by simp

end TorusLp

/-- Paper: (D.1.10.12), p. 786. Multiply a rapidly decreasing sequence
by the integer coordinate monomial. -/
def latticeSchwartzMonomial {r : ℕ} (γ : Fin r → ℕ)
    (f : RapidDecaySequence r) (a : Fin r → ℤ) : ℂ :=
  (∏ i, (a i : ℂ) ^ γ i) * f a

/-- Paper: (D.1.10.12), p. 786. The zero weight leaves the sequence unchanged.
Deviation: Sanity check on the weight. -/
theorem latticeSchwartzMonomial_zero {r : ℕ} (f : RapidDecaySequence r) (a : Fin r → ℤ) :
    latticeSchwartzMonomial 0 f a = f a := by
  simp [latticeSchwartzMonomial]

section LatticeSchwartzSupAux

open Finset Fintype

variable {r : ℕ}

/-- Sequences in the rapidly decreasing space add pointwise. -/
private theorem rapidDecay_add_apply (f g : RapidDecaySequence r) (a : Fin r → ℤ) :
    (f + g) a = f a + g a := rfl

/-- Scalars act pointwise on rapidly decreasing sequences. -/
private theorem rapidDecay_smul_apply (c : ℂ) (f : RapidDecaySequence r) (a : Fin r → ℤ) :
    (c • f) a = c * f a := rfl

/-- Unfolds the monomial-weighted sequence at a lattice point. -/
private theorem latticeSchwartzMonomial_apply (γ : Fin r → ℕ) (f : RapidDecaySequence r)
    (a : Fin r → ℤ) :
    latticeSchwartzMonomial γ f a = (∏ i, (a i : ℂ) ^ γ i) * f a := rfl

/-- The monomial weighting is additive in the sequence. -/
private theorem latticeSchwartzMonomial_add (γ : Fin r → ℕ) (f g : RapidDecaySequence r)
    (a : Fin r → ℤ) :
    latticeSchwartzMonomial γ (f + g) a =
      latticeSchwartzMonomial γ f a + latticeSchwartzMonomial γ g a := by
  simp only [latticeSchwartzMonomial, rapidDecay_add_apply, mul_add]

/-- The monomial weighting commutes with scalars. -/
private theorem latticeSchwartzMonomial_smul (γ : Fin r → ℕ) (c : ℂ) (f : RapidDecaySequence r)
    (a : Fin r → ℤ) :
    latticeSchwartzMonomial γ (c • f) a = c * latticeSchwartzMonomial γ f a := by
  simp only [latticeSchwartzMonomial, rapidDecay_smul_apply]
  ring

/-- For nonnegative reals, `1 + ∑ fᵢ ≤ ∏ (1 + fᵢ)`. -/
private theorem one_add_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : 1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hf' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (mem_insert_of_mem hi)
    have hfa : 0 ≤ f a := hf a (mem_insert_self a s)
    have hprod_ge : 1 ≤ ∏ i ∈ s, (1 + f i) := by
      have hineq := ih hf'
      have hsum0 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf'
      linarith
    calc
      1 + (f a + ∑ i ∈ s, f i) = 1 + ∑ i ∈ s, f i + f a := by ring
      _ ≤ (∏ i ∈ s, (1 + f i)) + f a := add_le_add (ih hf') le_rfl
      _ ≤ (∏ i ∈ s, (1 + f i)) + f a * ∏ i ∈ s, (1 + f i) :=
          add_le_add le_rfl (le_mul_of_one_le_right hfa hprod_ge)
      _ = (1 + f a) * ∏ i ∈ s, (1 + f i) := by ring

/-- One plus the Euclidean length of a lattice point is at most the product of
one plus the absolute values of its coordinates. -/
private theorem one_add_euclidean_le_prod_natAbs (a : Fin r → ℤ) :
    1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ≤
      ∏ i, (1 + ((a i).natAbs : ℝ)) := by
  let x : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (a i : ℝ))
  have hcoord (i : Fin r) : ‖x i‖ = (a i).natAbs := by
    simp [x]
  have hsq : ∑ i, ‖x i‖ ^ 2 ≤ (∑ i, ‖x i‖) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i, ‖x i‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hnorm : ‖x‖ ≤ ∑ i, ‖x i‖ := by
    rw [PiLp.norm_eq_sum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    simp only [ENNReal.toReal_ofNat]
    simp_rw [Real.rpow_two, ← Real.sqrt_eq_rpow]
    rw [← Real.sqrt_sq hsum_nonneg]
    exact Real.sqrt_le_sqrt hsq
  calc
    1 + ‖x‖ ≤ 1 + ∑ i, ‖x i‖ := add_le_add le_rfl hnorm
    _ = 1 + ∑ i, ((a i).natAbs : ℝ) := by simp [hcoord]
    _ ≤ ∏ i, (1 + ((a i).natAbs : ℝ)) :=
        one_add_sum_le_prod univ (fun i => ((a i).natAbs : ℝ)) fun _ _ => by positivity

/-- The comparison `1 + ‖a‖ ≤ ∏ (1 + |aᵢ|)` in extended nonnegative reals. -/
private theorem one_add_latticeNorm_le_prod (a : Fin r → ℤ) :
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ≤
      ∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) := by
  let x : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (a i : ℝ))
  have hL : (1 + (‖x‖₊ : ℝ≥0∞)) = ENNReal.ofReal (1 + ‖x‖) := by
    rw [ENNReal.coe_nnreal_eq ‖x‖₊, coe_nnNorm]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (norm_nonneg _)]
  have hfactor (i : Fin r) :
      (1 + ((a i).natAbs : ℝ≥0∞)) = ENNReal.ofReal (1 + ((a i).natAbs : ℝ)) := by
    rw [eq_comm, ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg _), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast]
  have hR : ∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) =
      ENNReal.ofReal (∏ i, (1 + ((a i).natAbs : ℝ))) := by
    simp_rw [hfactor, ← ENNReal.ofReal_prod_of_nonneg
      (fun _ _ => add_nonneg zero_le_one (Nat.cast_nonneg _))]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (one_add_euclidean_le_prod_natAbs a)

/-- The norm of an integer viewed as a complex number is its absolute value. -/
private theorem complex_nnnorm_eq_natAbs (n : ℤ) : ‖(n : ℂ)‖₊ = n.natAbs := by
  apply NNReal.coe_injective
  rw [coe_nnNorm, Complex.norm_intCast, NNReal.coe_natCast, Nat.cast_natAbs, Int.cast_abs]

/-- A coordinate monomial is bounded by the matching power of `1 + ‖a‖`. -/
private theorem latticeSchwartzMonomial_enorm_le (γ : Fin r → ℕ) (f : RapidDecaySequence r)
    (a : Fin r → ℤ) :
    (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞) ≤
      (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^
        (∑ i, γ i) * (‖f a‖₊ : ℝ≥0∞) := by
  let x : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (a i : ℝ))
  rw [latticeSchwartzMonomial_apply]
  rw [nnNorm_mul, ENNReal.coe_mul]
  gcongr
  rw [nnNorm_prod, ENNReal.ofNNReal_finsetProd]
  have hpow : ∏ i, (‖(a i : ℂ) ^ γ i‖₊ : ℝ≥0∞) =
      ∏ i, (‖(a i : ℂ)‖₊ : ℝ≥0∞) ^ γ i := by
    refine prod_congr rfl fun i _ => ?_
    rw [nnNorm_pow, ENNReal.coe_pow]
  rw [hpow]
  have hcoord (i : Fin r) : ‖(a i : ℂ)‖₊ ≤ ‖x‖₊ := by
    rw [complex_nnnorm_eq_natAbs]
    have hx : ‖x i‖₊ = (a i).natAbs := by
      apply NNReal.coe_injective
      simp [x, NNReal.coe_natCast, coe_nnNorm]
    rw [← hx]
    exact PiLp.nnNorm_apply_le x i
  calc
    ∏ i, (‖(a i : ℂ)‖₊ : ℝ≥0∞) ^ γ i ≤ ∏ i, (‖x‖₊ : ℝ≥0∞) ^ γ i := by
      gcongr with i
      exact hcoord i
    _ = (‖x‖₊ : ℝ≥0∞) ^ ∑ i, γ i := prod_pow_eq_pow_sum _ _ _
    _ ≤ (1 + (‖x‖₊ : ℝ≥0∞)) ^ ∑ i, γ i := by
      gcongr
      exact le_add_of_nonneg_left (zero_le_one : (0 : ℝ≥0∞) ≤ 1)

/-- Each weighted sup norm is at most the weighted absolute sum whose order is
the total degree of the monomial. -/
private theorem latticeSchwartzSup_le_bound (γ : Fin r → ℕ) (f : RapidDecaySequence r) :
    ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞) ≤
      rapidDecaySequenceBound (∑ i, γ i) f.1 := by
  unfold rapidDecaySequenceBound
  change ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞) ≤
    ∑' a, (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^
        (∑ i, γ i) * (‖f a‖₊ : ℝ≥0∞)
  refine iSup_le fun a => ?_
  exact (latticeSchwartzMonomial_enorm_le γ f a).trans (le_tsum
    (fun b => (1 + (‖(WithLp.toLp 2 (fun i ↦ (b i : ℝ)) :
      EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ (∑ i, γ i) * (‖f b‖₊ : ℝ≥0∞)) a)

/-- The weighted sup norms of a rapidly decreasing sequence are finite. -/
private theorem latticeSchwartzSup_lt_top (γ : Fin r → ℕ) (f : RapidDecaySequence r) :
    ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞) < ⊤ :=
  (latticeSchwartzSup_le_bound γ f).trans_lt (f.2 (∑ i, γ i))

/-- Splits off a factor `(1 + n)⁻²` from a power of `1 + n`. -/
private theorem one_add_pow_split (n j : ℕ) :
    (1 + (n : ℝ≥0∞)) ^ j =
      ((1 + (n : ℝ≥0∞))⁻¹) ^ 2 * (1 + (n : ℝ≥0∞)) ^ (j + 2) := by
  set x : ℝ≥0∞ := 1 + (n : ℝ≥0∞)
  have hx0 : x ≠ 0 := by simp [x]
  have hxt : x ≠ ⊤ := by simp [x]
  have hcancel : x⁻¹ ^ 2 * x ^ 2 = 1 := by
    rw [pow_two, pow_two, mul_assoc, ← mul_assoc x⁻¹ x x, ENNReal.inv_mul_cancel hx0 hxt,
      one_mul, ENNReal.inv_mul_cancel hx0 hxt]
  calc
    x ^ j = x ^ j * 1 := (mul_one _).symm
    _ = x ^ j * (x⁻¹ ^ 2 * x ^ 2) := by rw [hcancel]
    _ = x⁻¹ ^ 2 * (x ^ j * x ^ 2) := mul_left_comm _ _ _
    _ = x⁻¹ ^ 2 * x ^ (j + 2) := by rw [pow_add]

/-- Splits off the factor `∏ (1 + |aᵢ|)⁻²` from a product of powers. -/
private theorem prod_pow_split (j : ℕ) (a : Fin r → ℤ) :
    ∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ j =
      (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) *
        ∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ (j + 2) := by
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => one_add_pow_split (a i).natAbs j

/-- Binomial expansion of `(1 + n) ^ M`. -/
private theorem one_add_natAbs_pow (M n : ℕ) :
    (1 + (n : ℝ≥0∞)) ^ M =
      ∑ k ∈ range (M + 1), (n : ℝ≥0∞) ^ k * (M.choose k : ℝ≥0∞) := by
  rw [add_comm]
  simpa [one_pow, mul_one] using add_pow (n : ℝ≥0∞) (1 : ℝ≥0∞) M

/-- Rewrites a product of powers of coordinate absolute values times a norm as the
norm of the monomial times the value. -/
private theorem natAbs_pow_prod_nnnorm (a : Fin r → ℤ) (p : Fin r → ℕ) (z : ℂ) :
    (∏ i, ((a i).natAbs : ℝ≥0∞) ^ p i) * (‖z‖₊ : ℝ≥0∞) =
      (‖(∏ i, (a i : ℂ) ^ p i) * z‖₊ : ℝ≥0∞) := by
  have hpow (i : Fin r) :
      ((a i).natAbs : ℝ≥0∞) ^ p i = (‖(a i : ℂ) ^ p i‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.coe_natCast, ← ENNReal.coe_pow, nnNorm_pow, complex_nnnorm_eq_natAbs]
  simp_rw [hpow, ← ENNReal.ofNNReal_finsetProd, ← nnNorm_prod, ← ENNReal.coe_mul, ← nnNorm_mul]

/-- The sum over a box of products of binomial coefficients is `2 ^ (M * r)`. -/
private theorem choose_pi_sum (M : ℕ) :
    ∑ p ∈ piFinset (fun _ : Fin r ↦ range (M + 1)), ∏ i, (M.choose (p i) : ℝ≥0∞) =
      (2 : ℝ≥0∞) ^ (M * r) := by
  have hsum := sum_prod_piFinset (range (M + 1))
    (fun (_ : Fin r) (k : ℕ) => (M.choose k : ℝ≥0∞))
  rw [hsum]
  simp_rw [← Nat.cast_sum, Nat.sum_range_choose]
  rw [prod_const, Finset.card_fin, Nat.cast_pow, ← pow_mul]
  rfl

/-- Expands `∏ (1 + |aᵢ|) ^ M * ‖z‖` as a sum over the monomials of degree at most
`M` in each coordinate. -/
private theorem prod_one_add_pow_eq_sum (M : ℕ) (a : Fin r → ℤ) (z : ℂ) :
    (∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ M) * (‖z‖₊ : ℝ≥0∞) =
      ∑ p ∈ piFinset (fun _ : Fin r ↦ range (M + 1)),
        (∏ i, (M.choose (p i) : ℝ≥0∞)) *
          (‖(∏ i, (a i : ℂ) ^ p i) * z‖₊ : ℝ≥0∞) := by
  have hprod :
      ∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ M =
        ∑ p ∈ piFinset (fun _ : Fin r ↦ range (M + 1)),
          ∏ i, ((a i).natAbs : ℝ≥0∞) ^ p i * (M.choose (p i) : ℝ≥0∞) := by
    simp_rw [one_add_natAbs_pow]
    exact prod_univ_sum (fun _ : Fin r ↦ range (M + 1))
      (fun i k => ((a i).natAbs : ℝ≥0∞) ^ k * (M.choose k : ℝ≥0∞))
  rw [hprod, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  rw [prod_mul_distrib, mul_assoc, mul_left_comm
      (∏ i, ((a i).natAbs : ℝ≥0∞) ^ p i)
      (∏ i, (M.choose (p i) : ℝ≥0∞)), natAbs_pow_prod_nnnorm]

/-- Bounds `∏ (1 + |aᵢ|) ^ M * ‖z‖` by `2 ^ (M * r)` times the largest monomial
in the box of degrees at most `M`. -/
private theorem prod_one_add_pow_le_box (M : ℕ) (a : Fin r → ℤ) (z : ℂ) :
    (∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ M) * (‖z‖₊ : ℝ≥0∞) ≤
      (2 : ℝ≥0∞) ^ (M * r) *
        (piFinset (fun _ : Fin r ↦ range (M + 1))).sup
          (fun p => (‖(∏ i, (a i : ℂ) ^ p i) * z‖₊ : ℝ≥0∞)) := by
  rw [prod_one_add_pow_eq_sum]
  let s := piFinset (fun _ : Fin r ↦ range (M + 1))
  have hle :
      ∑ p ∈ s, (∏ i, (M.choose (p i) : ℝ≥0∞)) *
          (‖(∏ i, (a i : ℂ) ^ p i) * z‖₊ : ℝ≥0∞) ≤
        ∑ p ∈ s, (∏ i, (M.choose (p i) : ℝ≥0∞)) *
          s.sup (fun q => (‖(∏ i, (a i : ℂ) ^ q i) * z‖₊ : ℝ≥0∞)) := by
    refine sum_le_sum fun p hp => ?_
    let m : (Fin r → ℕ) → ℝ≥0∞ :=
      fun q => (‖(∏ i, (a i : ℂ) ^ q i) * z‖₊ : ℝ≥0∞)
    have hm : m p ≤ s.sup m := Finset.le_sup hp
    obtain ⟨d, hd⟩ := exists_add_of_le hm
    rw [hd, mul_add]
    exact le_self_add
  exact hle.trans (by rw [← sum_mul, choose_pi_sum])

/-- The series `∑ₖ (|k| + 1)⁻²` over the integers converges. -/
private theorem summable_inv_one_add_sq_int :
    Summable (fun k : ℤ ↦ (1 : ℝ) / ((k.natAbs + 1 : ℝ) ^ 2)) := by
  have hshift : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    refine summable_of_sum_range_le (c := 2) (fun n => by positivity) fun n => ?_
    have key : ∀ n : ℕ,
        ∑ i ∈ range n, (1 : ℝ) / ((i : ℝ) + 1) ^ 2 ≤ 2 - 2 / ((n : ℝ) + 1) := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [sum_range_succ]
        have h : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤
            2 / ((n : ℝ) + 1) - 2 / (((n + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          rw [div_sub_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith
    have : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
    linarith [key n]
  exact Summable.of_nat_of_neg (hshift.congr fun n => by simp [Int.natAbs_natCast])
    (hshift.congr fun n => by simp [Int.natAbs_neg, Int.natAbs_natCast])

/-- Rewrites `(1 + |k|)⁻²` in extended nonnegative reals as a real number. -/
private theorem inv_one_add_sq_ofReal (k : ℤ) :
    ((1 + (k.natAbs : ℝ≥0∞))⁻¹) ^ 2 =
      ENNReal.ofReal (1 / ((k.natAbs + 1 : ℝ) ^ 2)) := by
  have hpos : 0 < (k.natAbs + 1 : ℝ) := by positivity
  have hm : (1 + (k.natAbs : ℝ≥0∞)) = ENNReal.ofReal ((k.natAbs : ℝ) + 1) := by
    rw [eq_comm, ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one, add_comm]
  rw [hm, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_pow (inv_nonneg.mpr hpos.le)]
  rw [inv_eq_one_div, one_div_pow, ENNReal.ofReal_div_of_pos (pow_pos hpos 2), ENNReal.ofReal_one]

/-- The series `∑ₖ (1 + |k|)⁻²` over the integers is finite. -/
private theorem lattice_weight_base_lt_top :
    ∑' k : ℤ, ((1 + (k.natAbs : ℝ≥0∞))⁻¹) ^ 2 < ⊤ := by
  simp_rw [inv_one_add_sq_ofReal]
  exact summable_inv_one_add_sq_int.tsum_ofReal_lt_top

/-- The product weight `∏ (1 + |aᵢ|)⁻²` sums over the lattice to the `n`-th power
of the one-dimensional sum. -/
private theorem lattice_weight_tsum_eq (n : ℕ) :
    ∑' a : Fin n → ℤ, ∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2 =
      (∑' k : ℤ, ((1 + (k.natAbs : ℝ≥0∞))⁻¹) ^ 2) ^ n := by
  let g : ℤ → ℝ≥0∞ := fun k => ((1 + (k.natAbs : ℝ≥0∞))⁻¹) ^ 2
  induction n with
  | zero =>
    rw [pow_zero, tsum_eq_single (default : Fin 0 → ℤ)]
    · simp [Finset.univ_eq_empty]
    · intro a ha
      exact (ha (Subsingleton.elim a default)).elim
  | succ n ih =>
    let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) := Fin.snocEquiv (fun _ ↦ ℤ)
    have hfun (k : ℤ) (b : Fin n → ℤ) :
        ∏ i, g (e (k, b) i) = (∏ i, g (b i)) * g k := by
      rw [Fin.snocEquiv_apply, Fin.prod_univ_castSucc]
      congr 1
      · refine prod_congr rfl fun i _ => ?_
        rw [Fin.snoc_castSucc]
      · rw [Fin.snoc_last]
    rw [← e.tsum_eq (fun a => ∏ i, g (a i))]
    simp_rw [hfun]
    rw [tsum_prod']
    simp_rw [ENNReal.tsum_mul_right]
    rw [ih, ENNReal.tsum_mul_left, ← pow_succ]

/-- The product weight `∏ (1 + |aᵢ|)⁻²` has finite sum over the lattice. -/
private theorem lattice_weight_tsum_lt_top (n : ℕ) :
    ∑' a : Fin n → ℤ, ∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2 < ⊤ := by
  rw [lattice_weight_tsum_eq]
  exact ENNReal.pow_lt_top (n := n) lattice_weight_base_lt_top

/-- Pointwise bound of a term of the `j`-th weighted absolute sum by the product
weight times finitely many weighted sup norms. -/
private theorem rapidBound_term_le (j : ℕ) (f : RapidDecaySequence r) (a : Fin r → ℤ) :
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
        (‖f a‖₊ : ℝ≥0∞) ≤
      (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) * (2 : ℝ≥0∞) ^ ((j + 2) * r) *
        (piFinset (fun _ : Fin r ↦ range (j + 3))).sup
          (fun γ => ⨆ b, (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)) := by
  let M : ℕ := j + 2
  have hM : M + 1 = j + 3 := by simp [M]
  let s := piFinset (fun _ : Fin r ↦ range (M + 1))
  let Q : ℝ≥0∞ := s.sup fun γ => ⨆ b, (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)
  have hmono :
      (∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ M) * (‖f a‖₊ : ℝ≥0∞) ≤
        (2 : ℝ≥0∞) ^ (M * r) * Q := by
    refine (prod_one_add_pow_le_box M a (f a)).trans ?_
    gcongr
    refine Finset.sup_le fun p hp => ?_
    have hmonoeq : (‖(∏ i, (a i : ℂ) ^ p i) * f a‖₊ : ℝ≥0∞) =
        (‖latticeSchwartzMonomial p f a‖₊ : ℝ≥0∞) := by
      rw [latticeSchwartzMonomial_apply]
    have hp' : p ∈ s := hp
    exact (le_of_eq hmonoeq).trans
      ((le_iSup (fun b => (‖latticeSchwartzMonomial p f b‖₊ : ℝ≥0∞)) a).trans
        (Finset.le_sup (f := fun γ => ⨆ b, (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)) hp'))
  calc
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
          (‖f a‖₊ : ℝ≥0∞)
        ≤ (∏ i, (1 + ((a i).natAbs : ℝ≥0∞))) ^ j * (‖f a‖₊ : ℝ≥0∞) := by
          gcongr
          exact one_add_latticeNorm_le_prod a
    _ = (∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ j) * (‖f a‖₊ : ℝ≥0∞) := by
          rw [Finset.prod_pow]
    _ = (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) *
          ((∏ i, (1 + ((a i).natAbs : ℝ≥0∞)) ^ M) * (‖f a‖₊ : ℝ≥0∞)) := by
          rw [prod_pow_split, mul_assoc]
    _ ≤ (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) *
          ((2 : ℝ≥0∞) ^ (M * r) * Q) := by gcongr
    _ = (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) * (2 : ℝ≥0∞) ^ (M * r) * Q := by
          rw [← mul_assoc]
    _ = (∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) * (2 : ℝ≥0∞) ^ ((j + 2) * r) *
          (piFinset (fun _ : Fin r ↦ range (j + 3))).sup
            (fun γ => ⨆ b, (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)) := by
          simp [M, Q, s, hM]

/-- The `j`-th weighted absolute sum is bounded by a constant times the largest of
finitely many weighted sup norms. -/
private theorem rapidDecaySequenceBound_le_sup (j : ℕ) (f : RapidDecaySequence r) :
    rapidDecaySequenceBound j f.1 ≤
      (∑' a : Fin r → ℤ, ∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2) *
        (2 : ℝ≥0∞) ^ ((j + 2) * r) *
        (piFinset (fun _ : Fin r ↦ range (j + 3))).sup
          (fun γ => ⨆ b, (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)) := by
  unfold rapidDecaySequenceBound
  refine (tsum_le_tsum (fun a => rapidBound_term_le j f a)).trans ?_
  simp_rw [mul_assoc]
  rw [ENNReal.tsum_mul_right]

/-- Each weighted absolute-sum seminorm is dominated by a multiple of the supremum
of finitely many weighted sup seminorms. -/
private theorem rapidDecay_controlled_by_sup (j : ℕ)
    (P : (Fin r → ℕ) → Seminorm ℂ (RapidDecaySequence r))
    (hP : ∀ γ (f : RapidDecaySequence r),
      P γ f = (⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)).toReal) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ t : Finset (Fin r → ℕ),
      rapidDecaySequenceSeminorm j ≤ C • t.sup P := by
  classical
  let t := piFinset (fun _ : Fin r ↦ range (j + 3))
  let W := ∑' a : Fin r → ℤ, ∏ i, ((1 + ((a i).natAbs : ℝ≥0∞))⁻¹) ^ 2
  have hW : W < ⊤ := lattice_weight_tsum_lt_top r
  have hpow : (2 : ℝ≥0∞) ^ ((j + 2) * r) < ⊤ := ENNReal.pow_lt_top (by simp)
  have hCpos : 0 < Real.toNNReal (W.toReal * (2 : ℝ) ^ ((j + 2) * r)) := by
    have hone : (1 : ℝ≥0∞) ≤ W := by
      refine le_trans ?_ (le_tsum _ (0 : Fin r → ℤ))
      simp
    have hW1 : (1 : ℝ) ≤ W.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hW.ne hone
    exact Real.toNNReal_pos.mpr (mul_pos (lt_of_lt_of_le zero_lt_one hW1) (by positivity))
  refine ⟨_, hCpos, t, ?_⟩
  refine Seminorm.le_def.mpr fun f => ?_
  let Q : ℝ≥0∞ := t.sup fun γ => ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)
  have hfin : ∀ u : Finset (Fin r → ℕ),
      (u.sup fun γ => ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) ≠ ⊤ := by
    intro u
    induction u using Finset.induction with
    | empty => simp
    | insert γ s hγ ih =>
      rw [sup_insert]
      exact (max_lt (latticeSchwartzSup_lt_top γ f) (lt_of_le_of_ne le_top ih)).ne
  have hQ : Q ≠ ⊤ := hfin t
  have htne : t.Nonempty := ⟨fun _ => 0, by simp [t, mem_piFinset]⟩
  obtain ⟨γ0, hγ0, hmax⟩ :=
    Finset.exists_mem_eq_sup t htne (fun γ => ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞))
  have htop : W * (2 : ℝ≥0∞) ^ ((j + 2) * r) * Q < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hW hpow) (lt_top_iff_ne_top.mpr hQ)
  have hto := ENNReal.toReal_mono htop.ne (rapidDecaySequenceBound_le_sup j f)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at hto
  have hQto : Q.toReal = P γ0 f :=
    (congrArg ENNReal.toReal hmax).trans (hP γ0 f).symm
  have hto' : (rapidDecaySequenceBound j f.1).toReal ≤
      W.toReal * (2 : ℝ) ^ ((j + 2) * r) * P γ0 f := hQto ▸ hto
  have hge : P γ0 f ≤ (t.sup P) f := by
    have h1 := NNReal.coe_le_coe.mpr (Finset.le_sup
      (f := fun i => NNReal.mk (P i f) (apply_nonneg (P i) f)) hγ0)
    exact (Seminorm.finset_sup_apply P t f).symm ▸ h1
  have hK : (Real.toNNReal (W.toReal * (2 : ℝ) ^ ((j + 2) * r)) : ℝ) =
      W.toReal * (2 : ℝ) ^ ((j + 2) * r) :=
    Real.coe_toNNReal _ (by positivity)
  calc
    rapidDecaySequenceSeminorm j f = (rapidDecaySequenceBound j f.1).toReal := rfl
    _ ≤ W.toReal * (2 : ℝ) ^ ((j + 2) * r) * P γ0 f := hto'
    _ ≤ W.toReal * (2 : ℝ) ^ ((j + 2) * r) * (t.sup P) f :=
      mul_le_mul_of_nonneg_left hge (by positivity)
    _ = (Real.toNNReal (W.toReal * (2 : ℝ) ^ ((j + 2) * r)) : ℝ) * (t.sup P) f := by
      rw [hK]
    _ = (Real.toNNReal (W.toReal * (2 : ℝ) ^ ((j + 2) * r)) • t.sup P) f := rfl

/-- The weighted sup norms generate the topology of rapidly decreasing sequences:
each is dominated by one weighted absolute sum, and each weighted absolute sum is
dominated by finitely many of them. -/
private theorem latticeSchwartz_sup_generates_aux (r : ℕ) :
    GeneratesSeminormTopology (fun γ : Fin r → ℕ ↦ fun f : RapidDecaySequence r ↦
      ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) := by
  classical
  let P : (Fin r → ℕ) → Seminorm ℂ (RapidDecaySequence r) := fun γ =>
    Seminorm.of (fun f => (⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)).toReal)
      (fun f g => by
        have hf := latticeSchwartzSup_lt_top γ f
        have hg := latticeSchwartzSup_lt_top γ g
        have hle : (⨆ a, (‖latticeSchwartzMonomial γ (f + g) a‖₊ : ℝ≥0∞)) ≤
            (⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) +
              ⨆ a, (‖latticeSchwartzMonomial γ g a‖₊ : ℝ≥0∞) := by
          refine iSup_le fun a => ?_
          rw [latticeSchwartzMonomial_add]
          exact (ENNReal.coe_le_coe.mpr (nnNorm_add_le _ _)).trans (add_le_add
            (le_iSup (fun b => (‖latticeSchwartzMonomial γ f b‖₊ : ℝ≥0∞)) a)
            (le_iSup (fun b => (‖latticeSchwartzMonomial γ g b‖₊ : ℝ≥0∞)) a))
        rw [← ENNReal.toReal_add hf.ne hg.ne]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.ne, hg.ne⟩) hle)
      (fun c f => by
        have hmul : (⨆ a, (‖latticeSchwartzMonomial γ (c • f) a‖₊ : ℝ≥0∞)) =
            (‖c‖₊ : ℝ≥0∞) * ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞) := by
          simp_rw [latticeSchwartzMonomial_smul, nnNorm_mul, ENNReal.coe_mul, ENNReal.mul_iSup]
        rw [hmul, ENNReal.toReal_mul]
        rw [ENNReal.coe_nnreal_eq ‖c‖₊]
        simp only [coe_nnNorm]
        rw [ENNReal.toReal_ofReal (norm_nonneg _)])
  have hP : ∀ γ (f : RapidDecaySequence r),
      P γ f = (⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)).toReal := fun _ _ => rfl
  have hl1 (j : ℕ) := rapidDecay_controlled_by_sup j P hP
  have hsup_le : ∀ γ, P γ ≤ rapidDecaySequenceSeminorm (∑ i, γ i) := by
    intro γ
    refine Seminorm.le_def.mpr fun f => ?_
    exact ENNReal.toReal_mono (f.2 _).ne (latticeSchwartzSup_le_bound γ f)
  have hpW := rapidDecaySequence_withSeminorms (r := r)
  let pR : ℕ → Seminorm ℂ (RapidDecaySequence r) := rapidDecaySequenceSeminorm
  refine ⟨P, ?_, fun γ f => ENNReal.ofReal_toReal (latticeSchwartzSup_lt_top γ f).ne⟩
  apply SeminormFamily.withSeminorms_of_hasBasis
  refine hpW.hasBasis.to_hasBasis ?_ ?_
  · intro U hU
    obtain ⟨s, ε, hε, rfl⟩ :=
      (SeminormFamily.basisSets_iff (p := rapidDecaySequenceSeminorm (r := r)) (U := U)).mp hU
    obtain rfl | hs := s.eq_empty_or_nonempty
    · refine ⟨Set.univ, SeminormFamily.basisSets_univ_mem _, ?_⟩
      rw [Finset.sup_empty, Seminorm.bot_eq_zero, Seminorm.ball_zero' _ hε]
      exact subset_rfl
    · choose C hCpos t ht using hl1
      let C0 : ℝ≥0 := s.sup C
      let T : Finset (Fin r → ℕ) := s.biUnion t
      have hC0 : (0 : ℝ≥0) < C0 := by
        obtain ⟨j, hj⟩ := hs
        exact lt_of_lt_of_le (hCpos j) (Finset.le_sup hj)
      have hcontrol : s.sup pR ≤ C0 • T.sup P := by
        refine Seminorm.le_def.mpr fun f => ?_
        rw [Seminorm.finset_sup_apply]
        have hright : (C0 • T.sup P) f = (C0 : ℝ) * (T.sup P) f := rfl
        rw [hright]
        suffices (s.sup fun i => NNReal.mk (pR i f) (apply_nonneg (pR i) f)) ≤
            ⟨(C0 : ℝ) * (T.sup P) f, by positivity⟩ by
          exact NNReal.coe_le_coe.mpr this
        refine Finset.sup_le fun j hj => ?_
        have h1 := Seminorm.le_def.mp (ht j) f
        have hsubset := Finset.subset_biUnion_of_mem t hj
        have h2 := Seminorm.le_def.mp (Finset.sup_mono (f := P) hsubset) f
        have hC : (C j : ℝ) ≤ C0 := NNReal.coe_le_coe.mpr (Finset.le_sup hj)
        have hleft : pR j f ≤ (C j : ℝ) * ((t j).sup P) f := by
          have hsmul : (C j • (t j).sup P) f = (C j : ℝ) * ((t j).sup P) f := rfl
          exact hsmul ▸ h1
        have hmul : (C j : ℝ) * ((t j).sup P) f ≤ (C0 : ℝ) * (T.sup P) f :=
          mul_le_mul hC h2 (apply_nonneg _ _) (NNReal.coe_nonneg _)
        exact NNReal.coe_le_coe.mp (hleft.trans hmul)
      exact ⟨(T.sup P).ball 0 (ε / C0),
        SeminormFamily.basisSets_mem P T (div_pos hε (NNReal.coe_pos.mpr hC0)),
        by
          rw [← Seminorm.ball_smul (T.sup P) hC0 ε 0]
          exact Seminorm.ball_antitone hcontrol⟩
  · intro V hV
    obtain ⟨t, ε, hε, rfl⟩ :=
      (SeminormFamily.basisSets_iff (p := P) (U := V)).mp hV
    let w : (Fin r → ℕ) → ℕ := fun γ => ∑ i, γ i
    refine ⟨((t.image w).sup pR).ball 0 ε,
      SeminormFamily.basisSets_mem pR (t.image w) hε, ?_⟩
    exact Seminorm.ball_antitone <| Finset.sup_le fun γ hγ =>
      (hsup_le γ).trans (Finset.le_sup (Finset.mem_image.mpr ⟨γ, hγ, rfl⟩))

end LatticeSchwartzSupAux

/-- Paper: Example D.1.10.5, p. 786. The weighted sup norms generate the
rapidly decreasing sequence topology on the integer lattice. -/
theorem latticeSchwartz_sup_generates (r : ℕ) :
    GeneratesSeminormTopology (fun γ : Fin r → ℕ ↦ fun f : RapidDecaySequence r ↦
      ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) :=
  latticeSchwartz_sup_generates_aux r

/-- For counting measure, bound the monomial Lᵖ norm by its absolute sum and then by
the rapid-decay bound of the same total degree. -/
private theorem latticeSchwartz_lp_le_bound {r : ℕ} (p : ℕ) (hp : 1 ≤ p)
    (γ : Fin r → ℕ) (f : RapidDecaySequence r) :
    eLpNorm (latticeSchwartzMonomial γ f) p Measure.count ≤
      rapidDecaySequenceBound (∑ i, γ i) f.val := by
  let g := latticeSchwartzMonomial γ f
  let S := ∑' a, ‖g a‖ₑ
  have hS : S ≤ rapidDecaySequenceBound (∑ i, γ i) f.val :=
    tsum_le_tsum (latticeSchwartzMonomial_enorm_le γ f)
  refine le_trans ?_ hS
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hm : AEStronglyMeasurable g Measure.count := (measurable_of_countable g).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by positivity) (by simp) hm, lintegral_count,
    ENNReal.toReal_natCast, one_div, ENNReal.rpow_inv_le_iff (by positivity)]
  simp only [ENNReal.rpow_natCast, pow_succ]
  calc
    ∑' a, ‖g a‖ₑ ^ n * ‖g a‖ₑ ≤ ∑' a, S ^ n * ‖g a‖ₑ := by
      gcongr with a
      exact le_tsum (fun b ↦ ‖g b‖ₑ) a
    _ = S ^ n * S := ENNReal.tsum_mul_left

/-- Paper: Example D.1.10.5, p. 786. The counting-measure Lᵖ seminorms of
the monomial-weighted sequences generate the rapidly decreasing sequence topology. -/
theorem latticeSchwartz_lp_generates (r p : ℕ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.count : Measure (Fin r → ℤ)) (p : ℝ≥0∞)
      (latticeSchwartzMonomial (r := r)) := by
  classical
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  let μ : Measure (Fin r → ℤ) := Measure.count
  have hm (γ : Fin r → ℕ) (f : RapidDecaySequence r) : MemLp (latticeSchwartzMonomial γ f) p μ :=
    (latticeSchwartz_lp_le_bound p hp γ f).trans_lt (f.property _)
  let T (γ : Fin r → ℕ) : RapidDecaySequence r →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := fun f ↦ (hm γ f).toLp _
      map_add' := fun f g ↦ (hm γ (f + g)).toLp_congr ((hm γ f).add (hm γ g))
        (ae_of_all _ (latticeSchwartzMonomial_add γ f g))
      map_smul' := fun c f ↦ (hm γ (c • f)).toLp_congr ((hm γ f).const_smul c)
        (ae_of_all _ (latticeSchwartzMonomial_smul γ c f)) }
  let Q (γ : Fin r → ℕ) := (normSeminorm ℂ (Lp ℂ p μ)).comp (T γ)
  have hQ (γ : Fin r → ℕ) (f : RapidDecaySequence r) :
      ENNReal.ofReal (Q γ f) = eLpNorm (latticeSchwartzMonomial γ f) p μ := by
    exact (congrArg ENNReal.ofReal (Lp.norm_toLp _ (hm γ f))).trans (ENNReal.ofReal_toReal (hm γ f).eLpNorm_ne_top)
  obtain ⟨P, hP, hval⟩ := latticeSchwartz_sup_generates r
  have hval' γ f := congrArg ENNReal.toReal (hval γ f)
  simp only [ENNReal.toReal_ofReal (apply_nonneg _ _)] at hval'
  have hPQ (γ : Fin r → ℕ) : P γ ≤ Q γ := by
    intro f
    apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
    rw [hval, hQ]
    exact iSup_le fun a ↦ eNorm_le_eLpNorm_count (p := (p : ℝ≥0∞)) (latticeSchwartzMonomial γ f) a (by exact_mod_cast (by omega : p ≠ 0))
  refine ⟨hm, Q, hP.congr (Seminorm.IsBounded.of_real fun γ ↦ ?_)
    (Seminorm.IsBounded.of_real fun γ ↦ ?_), hQ⟩
  · obtain ⟨C, _, t, ht⟩ := rapidDecay_controlled_by_sup (∑ i, γ i) P hval'
    refine ⟨t, C, fun f ↦ le_trans ?_ (ht f)⟩
    have h := ENNReal.toReal_mono (f.property _).ne (latticeSchwartz_lp_le_bound p hp γ f)
    rwa [← hQ, ENNReal.toReal_ofReal (apply_nonneg _ _)] at h
  · exact ⟨{γ}, 1, fun f ↦ by simpa using hPQ γ f⟩

end SchwartzTopologies

section LpFamilies
variable {E X I J : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

omit [TopologicalSpace E] in
/-- A linear combination of transforms has Lᵖ norm bounded by the corresponding
finite maximum of seminorms times the sum of the coefficient norms. -/
private theorem lp_span_bound (hp : 1 ≤ p) (U : I → E →ₗ[ℂ] (X → ℂ))
    (hU : ∀ i f, MemLp (U i f) p μ) (L : E →ₗ[ℂ] (X → ℂ))
    (hL : L ∈ Submodule.span ℂ (range U)) :
    (∀ f, MemLp (L f) p μ) ∧ ∀ (P : I → Seminorm ℂ E)
      (_ : ∀ i f, P i f = lpNorm (U i f) p μ),
      ∃ (s : Finset I) (C : ℝ), ∀ f, lpNorm (L f) p μ ≤ C * s.sup P f := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hL
  have heq (f : E) : L f = ∑ i ∈ c.support, c i • U i f := by
    rw [← hc, Finsupp.sum, LinearMap.sum_apply]
    rfl
  have hm (i : I) (f : E) := (hU i f).const_smul (c i)
  constructor
  · intro f
    rw [heq]
    exact memLp_finsetSum' _ fun i _ ↦ hm i f
  · intro P hv
    refine ⟨c.support, ∑ i ∈ c.support, ‖c i‖, fun f ↦ ?_⟩
    rw [heq, Finset.sum_mul]
    exact (lpNorm_sum_le (fun i _ ↦ hm i f) hp).trans (Finset.sum_le_sum fun i hi ↦ by
      rw [lpNorm_const_smul, ← hv]
      exact mul_le_mul_of_nonneg_left (Seminorm.le_finset_sup_apply hi) (norm_nonneg _))

/-- Changing generators of the complex span of linear transforms preserves their
generating Lᵖ seminorms. -/
private theorem generatesLpSeminorms_of_span_eq (hp : 1 ≤ p)
    (U : I → E →ₗ[ℂ] (X → ℂ)) (V : J → E →ₗ[ℂ] (X → ℂ))
    (h : Submodule.span ℂ (range U) = Submodule.span ℂ (range V))
    (hU : GeneratesLpSeminorms μ p (fun i ↦ U i)) :
    GeneratesLpSeminorms μ p (fun j ↦ V j) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨hmU, P, hP, hval⟩ := hU
  have hPV (j : J) := lp_span_bound hp U hmU (V j) (h ▸ Submodule.subset_span (mem_range_self j))
  have hmV (j : J) := (hPV j).1
  let T (j : J) : E →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := fun f ↦ (hmV j f).toLp _
      map_add' := fun f g ↦ by
        simp only [map_add]
        rfl
      map_smul' := fun c f ↦ by
        simp only [map_smul, RingHom.id_apply]
        rfl }
  let Q (j : J) := (normSeminorm ℂ (Lp ℂ p μ)).comp (T j)
  have hQ (j : J) (f : E) : Q j f = lpNorm (V j f) p μ := by
    change ‖(hmV j f).toLp _‖ = _
    rw [Lp.norm_toLp, toReal_eLpNorm]
  have hvP (i : I) (f : E) : P i f = lpNorm (U i f) p μ := by
    rw [← toReal_eLpNorm]
    simpa only [ENNReal.toReal_ofReal (apply_nonneg _ _)] using congrArg ENNReal.toReal (hval i f)
  refine ⟨hmV, Q, hP.congr (Seminorm.IsBounded.of_real fun j ↦ ?_)
    (Seminorm.IsBounded.of_real fun i ↦ ?_), fun j f ↦ ?_⟩
  · obtain ⟨s, C, hs⟩ := (hPV j).2 P hvP
    exact ⟨s, C, fun f ↦ (hQ j f).trans_le (hs f)⟩
  · have hL := lp_span_bound hp V hmV (U i) (h ▸ ?_)
    · obtain ⟨s, C, hs⟩ := hL.2 Q hQ
      exact ⟨s, C, fun f ↦ (hvP i f).trans_le (hs f)⟩
    · exact Submodule.subset_span (mem_range_self i)
  · rw [hQ, ofReal_lpNorm (hmV j f)]
end LpFamilies

section WeightFamilies

variable {E X I : Type*} [AddCommGroup E] [Module ℂ E]

/-- Multiply a linear family of functions by a weight, linearly in each argument. -/
private def mulWeight (u : E →ₗ[ℂ] (X → ℂ)) : (X → ℂ) →ₗ[ℂ] E →ₗ[ℂ] (X → ℂ) where
  toFun w :=
    { toFun := fun f ↦ w * u f
      map_add' := fun f g ↦ by simp only [map_add, mul_add]
      map_smul' := fun c f ↦ by ext x; simp [mul_left_comm] }
  map_add' w v := by ext f x; exact add_mul _ _ _
  map_smul' c w := by ext f x; exact mul_assoc _ _ _

end WeightFamilies

section ElementaryOperators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. Repeat the first-order operator
in each direction according to its multi-index and compose the resulting operators. -/
def bruhatDiffMonomial {d : ℕ} (a : Fin d → LCATopologicalLie G) (α : Fin d → ℕ) :
    bruhatDiffAlgebra G :=
  bruhatDiffWord ((List.finRange d).flatMap fun j ↦ List.replicate (α j) (a j))

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. The multi-index of weight one in
one direction gives the corresponding first-order operator.
Deviation: Sanity check on repetition of directions. -/
theorem bruhatDiffMonomial_single {d : ℕ} (a : Fin d → LCATopologicalLie G) (j : Fin d) :
    bruhatDiffMonomial a (Pi.single j 1) = bruhatDiffGenerator (a j) := by
  rw [bruhatDiffMonomial, ← bruhatDiffWord_singleton]
  congr 1
  rw [← List.replicate_one, List.eq_replicate_iff]
  constructor
  · rw [List.length_flatMap]
    simp only [List.length_replicate]
    rw [← Fin.sum_univ_def]
    simp
  · intro x hx
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
    have hij : i = j := by
      by_contra h
      simp [Pi.single_eq_of_ne h] at hi
    subst hij
    exact List.eq_of_mem_replicate hi

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Differentiate a Schwartz–Bruhat
function and multiply it by the symbol of the dual operator through biduality. -/
def bruhatDiffSymbolWeightedApply (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G))
    (f : SchwartzBruhat G) (x : G) : ℂ :=
  bruhatDiffSymbol E (b x) *
    (D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩).val x

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Applying the pair of identity
operators returns the original function.
Deviation: Sanity check on the symbol and application conventions. -/
theorem bruhatDiffSymbolWeightedApply_one
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (f : SchwartzBruhat G) :
    bruhatDiffSymbolWeightedApply b 1 1 f = (f : G → ℂ) := by
  funext x
  simp [bruhatDiffSymbolWeightedApply, bruhatDiffSymbol_one]

section MonomialSpan

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] {d : ℕ}
  (a : Fin d → LCATopologicalLie G)

private theorem bruhatDiffMonomial_mul (α β : Fin d → ℕ) :
    bruhatDiffMonomial a (α + β) = bruhatDiffMonomial a α * bruhatDiffMonomial a β := by
  let : CommMonoid (bruhatDiffAlgebra G) :=
    { (inferInstance : Monoid (bruhatDiffAlgebra G)) with
      mul_comm := fun x y ↦ (bruhatDiffAlgebra_commute x y).eq }
  have h (δ : Fin d → ℕ) :
      bruhatDiffMonomial a δ = ∏ i, bruhatDiffGenerator (a i) ^ δ i := by
    simp only [bruhatDiffMonomial, bruhatDiffWord, List.map_reverse, List.prod_reverse,
      List.map_flatMap, List.map_replicate, Fin.prod_univ_def]
    induction List.finRange d with
    | nil => rfl
    | cons i l ih => simp [ih]
  simp only [h, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

/-- If the first-order directions span the real degree-one space, their ordered
monomials span the full complex algebra of differential operators. -/
private theorem bruhatDiffMonomial_mem_span
    (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) =
      bruhatDiffDegreeOneReal (G := G)) (D : bruhatDiffAlgebra G) :
    D ∈ Submodule.span ℂ (range (bruhatDiffMonomial a)) := by
  let M := Submodule.span ℂ (range (bruhatDiffMonomial a))
  have hgen (v : LCATopologicalLie G) : bruhatDiffGenerator v ∈ M := by
    have hv : bruhatFirstOrder v ∈ Submodule.span ℝ (range fun j ↦ bruhatFirstOrder (a j)) :=
      hspan ▸ Submodule.subset_span (mem_range_self v)
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
    have heq : bruhatDiffGenerator v = ∑ j ∈ c.support, (c j : ℂ) • bruhatDiffGenerator (a j) := by
      apply Subtype.ext
      have hs (r : ℝ) (x : Module.End ℂ (bruhatSmoothSubmodule (G := G))) :
          (r : ℂ) • x = r • x := IsScalarTower.algebraMap_smul ℂ r x
      simpa [Finsupp.sum, bruhatDiffGenerator, hs] using hc.symm
    rw [heq]
    exact M.sum_mem fun j _ ↦ M.smul_mem _ (Submodule.subset_span
      ⟨_, bruhatDiffMonomial_single a j⟩)
  have hmul (x y : bruhatDiffAlgebra G) (hx : x ∈ M) (hy : y ∈ M) : x * y ∈ M := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨α, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨β, rfl⟩ := hy
        exact Submodule.subset_span ⟨α + β, bruhatDiffMonomial_mul a α β⟩
      | zero => simpa only [mul_zero] using M.zero_mem
      | add _ _ _ _ h₁ h₂ => simpa only [mul_add] using M.add_mem h₁ h₂
      | smul c _ _ h => simpa only [mul_smul_comm] using M.smul_mem c h
    | zero => simpa only [zero_mul] using M.zero_mem
    | add _ _ _ _ h₁ h₂ => simpa only [add_mul] using M.add_mem h₁ h₂
    | smul c _ _ h => simpa only [smul_mul_assoc] using M.smul_mem c h
  have hword (w : List (LCATopologicalLie G)) : bruhatDiffWord w ∈ M := by
    induction w with
    | nil =>
      have h : (List.finRange d).flatMap (fun j ↦ List.replicate (0 : ℕ) (a j)) = [] :=
        List.flatMap_eq_nil_iff.mpr (by simp)
      exact Submodule.subset_span ⟨0, congrArg bruhatDiffWord h⟩
    | cons v w ih =>
      simpa [bruhatDiffWord] using hmul _ _ ih (hgen v)
  obtain ⟨c, hc⟩ := bruhatDiff_exists_presentation D
  rw [← hc]
  exact M.sum_mem fun w _ ↦ M.smul_mem _ (hword w)

end MonomialSpan

section WeightedOperators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

private def smoothIncl : SchwartzBruhat G →ₗ[ℂ] bruhatSmoothSubmodule (G := G) :=
  (schwartzBruhatSubmodule G).inclusion fun f hf ↦
    (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth ⟨f, hf⟩)

private def diffApplyLinear (D : bruhatDiffAlgebra G) : SchwartzBruhat G →ₗ[ℂ] (G → ℂ) :=
  bruhatSmoothSubmodule.subtype.comp (D.val.comp smoothIncl)

private def diffApplyWithWeights : bruhatDiffAlgebra G →ₗ[ℂ] (G → ℂ) →ₗ[ℂ] SchwartzBruhat G →ₗ[ℂ] (G → ℂ) where
  toFun D := mulWeight (diffApplyLinear D)
  map_add' D E := by ext w f x; exact mul_add ..
  map_smul' c D := by ext w f x; exact mul_left_comm ..

private def bruhatWeightedLinear (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) :
    bruhatDiffAlgebra G →ₗ[ℂ] bruhatDiffAlgebra (PontryaginDual G) →ₗ[ℂ]
      SchwartzBruhat G →ₗ[ℂ] (G → ℂ) :=
  let symbol : bruhatDiffAlgebra (PontryaginDual G) →ₗ[ℂ] (G → ℂ) :=
    { toFun D := fun x ↦ bruhatDiffSymbol D (b x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  { toFun D := (diffApplyWithWeights (G := G) D).comp symbol
    map_add' := fun D E ↦ by ext A f x; exact mul_add _ _ _
    map_smul' := fun c D ↦ by ext A f x; exact mul_left_comm _ _ _ }

private theorem span_bilinear_range {A B C I J : Type*}
    [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B] [AddCommMonoid C] [Module ℂ C]
    (T : A →ₗ[ℂ] B →ₗ[ℂ] C) (u : I → A) (v : J → B)
    (hu : ∀ x, x ∈ Submodule.span ℂ (range u)) (hv : ∀ y, y ∈ Submodule.span ℂ (range v)) :
    Submodule.span ℂ (range fun i : A × B ↦ T i.1 i.2) =
      Submodule.span ℂ (range fun i : I × J ↦ T (u i.1) (v i.2)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have h := Submodule.apply_mem_map₂ T (hu x) (hv y)
    rwa [Submodule.map₂_span_span, Set.image2_range] at h
  · exact Submodule.span_mono fun _ ⟨i, hi⟩ ↦ ⟨(u i.1, v i.2), hi⟩

private theorem bruhatWeightedLinear_monomial_span
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) {d d' : ℕ}
    (a : Fin d → LCATopologicalLie G) (a' : Fin d' → LCATopologicalLie (PontryaginDual G))
    (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) =
      bruhatDiffDegreeOneReal (G := G))
    (hspan' : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a' j))) =
      bruhatDiffDegreeOneReal (G := PontryaginDual G)) :
    Submodule.span ℂ (range fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      bruhatWeightedLinear b i.1 i.2) = Submodule.span ℂ (range fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
      bruhatWeightedLinear b (bruhatDiffMonomial a i.1) (bruhatDiffMonomial a' i.2)) :=
  span_bilinear_range _ _ _ (bruhatDiffMonomial_mem_span a hspan) (bruhatDiffMonomial_mem_span a' hspan')

end WeightedOperators

private theorem exists_basis_from_range {A I V : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (M : Submodule ℝ A)
    (L : V →ₗ[ℝ] M) (hL : Surjective L) (u : I → A) (hu : ∀ m : M, ∃ i, u i = m.val) :
    ∃ (d : ℕ) (a : Fin d → I), LinearIndependent ℝ (fun j ↦ u (a j)) ∧
      Submodule.span ℝ (range (fun j ↦ u (a j))) = M := by
  let : FiniteDimensional ℝ M := Module.Finite.of_surjective L hL
  let B := Module.finBasis ℝ M
  choose a ha using fun j ↦ hu (B j)
  have hfun : (fun j ↦ u (a j)) = M.subtype ∘ B := funext ha
  refine ⟨_, a, hfun ▸ B.linearIndependent.map' M.subtype M.ker_subtype, ?_⟩
  rw [hfun, Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top, Submodule.range_subtype]

/-- The vector cover of an elementary group parametrizes every one-parameter
subgroup. Its first-order operators therefore form a finite-dimensional space. -/
private theorem elementary_exists_firstOrder_basis {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (e : ElementaryLCAPresentation G) :
    ∃ (d : ℕ) (a : Fin d → LCATopologicalLie G),
      LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a j)) ∧
      Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) = bruhatDiffDegreeOneReal := by
  let V := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
  let M := bruhatDiffDegreeOneReal (G := G)
  let cover : V →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
    elementaryCoverZeroHom
  have hc : Continuous cover := elementaryCoverZeroHom_continuous_isOpenMap.1
  let a (v : V) : LCATopologicalLie G :=
    (e.equiv.symm : Multiplicative _ →ₜ* G).comp
      ⟨(cover.comp (LinearMap.toSpanSingleton ℝ V v).toAddMonoidHom).toMultiplicative,
        show Continuous (fun t : ℝ ↦ cover (t • v)) from hc.comp (continuous_id.smul continuous_const)⟩
  have hsurj : Surjective a := by
    intro b
    let c : ℝ →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor :=
      AddMonoidHom.toMultiplicative.symm (e.equiv.toMulEquiv.toMonoidHom.comp b.toMonoidHom)
    have hcont : Continuous c := e.equiv.continuous.comp b.continuous
    obtain ⟨v, hv⟩ := exists_elementaryCover_translation c hcont
    refine ⟨v, ContinuousMonoidHom.ext fun t ↦ e.equiv.injective ?_⟩
    change e.equiv (e.equiv.symm _) = _
    rw [e.equiv.apply_symm_apply]
    change cover (t.toAdd • v) = c t.toAdd
    have h := hv 0 0 0 t.toAdd
    change cover (0 + t.toAdd • v) = cover 0 + c t.toAdd at h
    simpa only [map_zero, zero_add] using h
  let L : V →ₗ[ℝ] M :=
    { toFun v := ⟨bruhatFirstOrder (a v), Submodule.subset_span (mem_range_self _)⟩
      map_add' v w := by
        apply Subtype.ext
        change bruhatFirstOrder (a (v + w)) = bruhatFirstOrder (a v) + bruhatFirstOrder (a w)
        rw [← bruhatFirstOrder_mul]
        congr 1
        apply ContinuousMonoidHom.ext
        intro t
        change e.equiv.symm (Multiplicative.ofAdd (cover (t.toAdd • (v + w)))) = _
        rw [smul_add, map_add, ofAdd_add, map_mul]
        rfl
      map_smul' r v := by
        apply Subtype.ext
        change bruhatFirstOrder (a (r • v)) = r • bruhatFirstOrder (a v)
        rw [← bruhatFirstOrder_scale]
        congr 1
        apply ContinuousMonoidHom.ext
        intro t
        change e.equiv.symm (Multiplicative.ofAdd (cover (t.toAdd • r • v))) =
          e.equiv.symm (Multiplicative.ofAdd (cover ((r * t.toAdd) • v)))
        rw [smul_smul, mul_comm] }
  have hL : Surjective L := by
    rintro ⟨D, hD⟩
    obtain ⟨b, rfl⟩ := (mem_bruhatDiffDegreeOneReal_iff _).mp hD
    obtain ⟨v, rfl⟩ := hsurj b
    exact ⟨v, rfl⟩
  exact exists_basis_from_range M L hL bruhatFirstOrder fun m ↦ by
    obtain ⟨b, hb⟩ := (mem_bruhatDiffDegreeOneReal_iff _).mp m.property
    exact ⟨b, hb.symm⟩

/-- Pointwise suprema are the L∞ norms for counting measure on the full
power-set σ-algebra, so they obey the same finite-span comparison. -/
private theorem generatesSupSeminorms_of_span_eq {E X I J : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (U : I → E →ₗ[ℂ] (X → ℂ)) (V : J → E →ₗ[ℂ] (X → ℂ))
    (h : Submodule.span ℂ (range U) = Submodule.span ℂ (range V))
    (hU : GeneratesSeminormTopology (fun i f ↦ ⨆ x, (‖U i f x‖₊ : ℝ≥0∞))) :
    GeneratesSeminormTopology (fun j f ↦ ⨆ x, (‖V j f x‖₊ : ℝ≥0∞)) := by
  let : MeasurableSpace X := ⊤
  have hm (g : X → ℂ) : AEStronglyMeasurable g Measure.count :=
    measurable_from_top.aestronglyMeasurable
  have hnorm (g : X → ℂ) : eLpNorm g ⊤ Measure.count = ⨆ x, (‖g x‖₊ : ℝ≥0∞) := by
    rw [eLpNorm_exponent_top (hm g), eLpNormEssSup_count]
    rfl
  have hs : GeneratesLpSeminorms Measure.count ⊤ (fun i ↦ U i) := by
    refine ⟨fun i f ↦ ?_, ?_⟩
    · obtain ⟨P, _, hP⟩ := hU
      exact ((hnorm _).trans (hP i f).symm).trans_lt ENNReal.ofReal_lt_top
    · simpa only [hnorm] using hU
  have hv := generatesLpSeminorms_of_span_eq le_top U V h hs
  simpa only [hnorm] using hv.2

section ElementaryProductMeasure
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
  [MeasurableSpace F] [BorelSpace F]
local notation "H" => ElementaryLieGroup m n r F
local notation "Dsc" => (Fin r → ℤ) × F
local notation "Torus" => Fin n → AddCircle (1 : ℝ)
local notation "Idx" => Fin m ⊕ Fin n
/-- Lebesgue measure on the real factor, normalized volume on the torus, and counting measure on the discrete factors. -/
private def elementaryProductMeasure : Measure H :=
  (volume : Measure (EuclideanSpace ℝ (Fin m))).prod ((volume : Measure Torus).prod (Measure.count : Measure Dsc))

private theorem elementaryProductMeasure_isHaar :
    (elementaryProductMeasure (m := m) (n := n) (r := r) (F := F)).IsAddHaarMeasure := by
  let : (Measure.count : Measure Dsc).IsAddHaarMeasure :=
    { lt_top_of_isCompact := fun {K} h ↦ by simp [Measure.count_apply_finite K (isCompact_iff_finite.mp h)]
      open_pos := fun U _ ⟨x, hx⟩ ↦ ne_of_gt <| lt_of_lt_of_le
        (by simp : 0 < Measure.count ({x} : Set Dsc)) (measure_mono (singleton_subset_iff.mpr hx)) }
  have : (volume : Measure Torus).IsAddHaarMeasure := inferInstance
  have : (volume : Measure (EuclideanSpace ℝ (Fin m))).IsAddHaarMeasure := inferInstance
  have : (Measure.count : Measure Dsc).IsAddLeftInvariant := inferInstance
  have : SigmaFinite (Measure.count : Measure Dsc) := inferInstance
  have : ((volume : Measure Torus).prod (Measure.count : Measure Dsc)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have : BorelSpace (Torus × Dsc) := inferInstance
  have : IsTopologicalAddGroup (Torus × Dsc) := inferInstance
  have : MeasurableAdd (Torus × Dsc) := inferInstance
  exact Measure.prod.instIsAddHaarMeasure _ _

private def cubeCover : (Idx → ℝ) →+ H where
  toFun u := (WithLp.toLp 2 (fun j ↦ u (Sum.inl j)), (fun j ↦ (u (Sum.inr j) : AddCircle (1 : ℝ))), 0, 0)
  map_zero' := by ext <;> simp
  map_add' := by intros; ext <;> simp

private theorem cubeCover_continuous : Continuous (cubeCover (m := m) (n := n) (r := r) (F := F)) := by
  apply Continuous.prodMk
  · exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun j ↦ continuous_apply (Sum.inl j))
  · exact (continuous_pi fun j ↦ (AddCircle.continuous_mk' _).comp (continuous_apply (Sum.inr j))).prodMk continuous_const

private def unitIntervalMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

/-- The unit cube maps into the elementary group with density bounded by one for the product measure. -/
private theorem cubeCover_map_le :
    (Measure.pi (fun _ : Idx ↦ unitIntervalMeasure)).map (cubeCover (F := F) (r := r)) ≤
      elementaryProductMeasure (m := m) (n := n) := by
  let I := unitIntervalMeasure
  let : IsFiniteMeasure I := by dsimp [I, unitIntervalMeasure]; infer_instance
  have hcir : MeasurePreserving (fun u : Fin n → ℝ ↦ fun j ↦ (u j : AddCircle (1 : ℝ)))
      (Measure.pi fun _ ↦ I) (volume : Measure Torus) :=
    measurePreserving_pi _ _ (fun _ ↦ by simpa [I, unitIntervalMeasure] using AddCircle.measurePreserving_mk 1 0)
  have ht : MeasurePreserving (fun u : Fin n → ℝ ↦ ((fun j ↦ (u j : AddCircle (1 : ℝ))), (0 : Dsc)))
      (Measure.pi fun _ ↦ I) ((volume : Measure Torus).prod (Measure.dirac 0)) := by
    refine ⟨hcir.measurable.prodMk measurable_const, ?_⟩
    rw [Measure.prod_dirac, ← hcir.map_eq, Measure.map_map measurable_prodMk_right hcir.measurable]
    rfl
  have he : MeasurePreserving (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m))
      (Measure.pi (fun _ ↦ I)) ((Measure.pi (fun _ : Fin m ↦ I)).map (WithLp.toLp 2)) :=
    ⟨(PiLp.continuous_toLp _ _).measurable, rfl⟩
  have h := (he.prod ht).comp (measurePreserving_sumPiEquivProdPi (fun _ : Idx ↦ I))
  change (Measure.pi fun _ : Idx ↦ I).map _ ≤ _
  rw [show (Measure.pi fun _ : Idx ↦ I).map (cubeCover (F := F) (r := r)) = _ from h.map_eq]
  apply Measure.prod_mono
  · rw [← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    apply Measure.map_mono
    · change Measure.pi (fun _ : Fin m ↦ (volume : Measure ℝ).restrict (Ioc 0 1)) ≤ volume
      rw [← Measure.restrict_pi_pi]
      exact Measure.restrict_le_self
    · exact (PiLp.continuous_toLp _ _).measurable
  · apply Measure.prod_mono le_rfl
    apply Measure.le_iff.mpr
    intro s hs
    by_cases h : (0 : Dsc) ∈ s
    · simpa [Measure.dirac_apply' _ hs, h] using
        (measure_mono (μ := Measure.count) (singleton_subset_iff.mpr h))
    · simp [Measure.dirac_apply' _ hs, h]
end ElementaryProductMeasure

section SymbolCalculus

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [LocallyCompactSpace H]

private def applyToCharacter (χ : PontryaginDual H) (x : H) : bruhatDiffAlgebra H →ₗ[ℂ] ℂ where
  toFun D := (D.val ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩).val x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem character_eigenvector (D : bruhatDiffAlgebra H) (χ : PontryaginDual H) :
    D.val ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩ =
      bruhatDiffSymbol D χ • (⟨_, pontryaginDual_mem_bruhatSmooth χ⟩ : bruhatSmoothSubmodule) := by
  obtain ⟨c, rfl⟩ := bruhatDiff_exists_presentation D
  apply Subtype.ext
  funext x
  change applyToCharacter χ x _ = applyToCharacter χ 1 _ * (χ x : ℂ)
  rw [Finsupp.sum, map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  simp only [map_smul, smul_eq_mul]
  change _ * ((bruhatDiffWord w).val _).val x =
    _ * ((bruhatDiffWord w).val _).val 1 * (χ x : ℂ)
  rw [bruhatDiffWord_character, bruhatDiffWord_character, map_one]
  simp [mul_assoc]

/-- An invariant differential operator acts on each character by its symbol. Composition multiplies the eigenvalues. -/
private def bruhatSymbolHom (χ : PontryaginDual H) : bruhatDiffAlgebra H →ₐ[ℂ] ℂ where
  toFun D := bruhatDiffSymbol D χ
  map_one' := bruhatDiffSymbol_one χ
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' D E := by
    change ((D.val (E.val _)).val 1) = _
    rw [character_eigenvector, map_smul]
    exact mul_comm _ _
  commutes' c := by
    change c * (χ 1 : ℂ) = c
    simp

private theorem exists_frequency_symbol (a : LCATopologicalLie H) :
    ∃ l : PontryaginDual H →ₜ* Multiplicative ℝ, ∀ χ,
      bruhatDiffSymbol (bruhatDiffGenerator a) χ = (2 * Real.pi * Complex.I) * (l χ).toAdd := by
  obtain ⟨σ, _, _, hσ⟩ := bruhatDiffDegreeOne_frequency (G := H)
  let D : bruhatDiffDegreeOneReal (G := H) := ⟨_, Submodule.subset_span (mem_range_self a)⟩
  exact ⟨σ D, fun χ ↦ bruhatDiffSymbol_generator a χ _ (hσ a D rfl χ)⟩

private theorem exists_operator_of_frequency (l : PontryaginDual H →ₜ* Multiplicative ℝ) :
    ∃ D : bruhatDiffAlgebra H, ∀ χ, bruhatDiffSymbol D χ = ((l χ).toAdd : ℂ) := by
  obtain ⟨σ, _, _, hσ⟩ := bruhatDiffDegreeOne_frequency (G := H)
  obtain ⟨A, hA⟩ := σ.surjective l
  obtain ⟨a, ha⟩ := (mem_bruhatDiffDegreeOneReal_iff _).mp A.property
  refine ⟨(2 * Real.pi * Complex.I : ℂ)⁻¹ • bruhatDiffGenerator a, fun χ ↦ ?_⟩
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ * bruhatDiffSymbol (bruhatDiffGenerator a) χ = _
  rw [bruhatDiffSymbol_generator a χ _ (hσ a A ha χ), hA, inv_mul_cancel_left₀]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
  (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (a : LCATopologicalLie G)

private theorem hasDerivAt_generatorSymbol (v : LCATopologicalLie (PontryaginDual G)) (x : G) :
    HasDerivAt (fun t : ℝ ↦ bruhatDiffSymbol (bruhatDiffGenerator v) (b (x * a (Multiplicative.ofAdd t))))
      (bruhatDiffSymbol (bruhatDiffGenerator v) (b (a (Multiplicative.ofAdd 1)))) 0 := by
  obtain ⟨l, hl⟩ := exists_frequency_symbol v
  let u : LCATopologicalLie (Multiplicative ℝ) := l.comp ((b : G →ₜ* _).comp a)
  have hu (t : ℝ) : (l (b (a (Multiplicative.ofAdd t)))).toAdd =
      t * (l (b (a (Multiplicative.ofAdd 1)))).toAdd := lcaTopologicalLie_real u t
  have heq (t : ℝ) : bruhatDiffSymbol (bruhatDiffGenerator v) (b (x * a (Multiplicative.ofAdd t))) =
      (2 * Real.pi * Complex.I) * ((l (b x)).toAdd + t * (l (b (a (Multiplicative.ofAdd 1)))).toAdd : ℝ) := by
    rw [hl, map_mul b, map_mul l, toAdd_mul, hu t]
  rw [funext heq, hl]
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const (l (b (a (Multiplicative.ofAdd 1)))).toAdd).const_add (l (b x)).toAdd
  simpa using h.ofReal_comp.const_mul (2 * Real.pi * Complex.I)


/-- The derivative of a symbol along a one-parameter subgroup is another symbol. -/
private theorem hasDerivAt_operatorSymbol (D : bruhatDiffAlgebra (PontryaginDual G)) :
    ∃ E : bruhatDiffAlgebra (PontryaginDual G), ∀ x : G,
      HasDerivAt (fun t : ℝ ↦ bruhatDiffSymbol D (b (x * a (Multiplicative.ofAdd t))))
        (bruhatDiffSymbol E (b x)) 0 := by
  classical
  let A : Type _ := bruhatDiffAlgebra (PontryaginDual G)
  let S (D : A) := ∃ E : A, ∀ x : G,
    HasDerivAt (fun t : ℝ ↦ bruhatSymbolHom (b (x * a (Multiplicative.ofAdd t))) D)
      (bruhatSymbolHom (b x) E) 0
  have hc (c : ℂ) : S (algebraMap ℂ A c) :=
    ⟨0, fun x ↦ by simpa only [A, AlgHom.commutes, Algebra.algebraMap_self_apply, map_zero] using
      (hasDerivAt_const (0 : ℝ) c)⟩
  have ha' (D E : A) (hd : S D) (he : S E) : S (D + E) := by
    obtain ⟨D', hD⟩ := hd
    obtain ⟨E', hE⟩ := he
    exact ⟨D' + E', fun x ↦ by simpa only [map_add] using! (hD x).fun_add (hE x)⟩
  have hm (D E : A) (hd : S D) (he : S E) : S (D * E) := by
    obtain ⟨D', hD⟩ := hd
    obtain ⟨E', hE⟩ := he
    refine ⟨D' * E + D * E', fun x ↦ ?_⟩
    simpa only [map_add, map_mul, ofAdd_zero, map_one, mul_one] using! (hD x).fun_mul (hE x)
  have hword (w : List (LCATopologicalLie (PontryaginDual G))) : S (bruhatDiffWord w) := by
    induction w with
    | nil => simpa [bruhatDiffWord] using hc 1
    | cons v w ih =>
      have hv : S (bruhatDiffGenerator v) :=
        ⟨algebraMap ℂ A (bruhatDiffSymbol (bruhatDiffGenerator v) (b (a (Multiplicative.ofAdd 1)))),
          fun x ↦ by dsimp only [A]; rw [AlgHom.commutes, Algebra.algebraMap_self_apply]; exact hasDerivAt_generatorSymbol b a v x⟩
      simpa [bruhatDiffWord] using hm _ _ ih hv
  obtain ⟨c, rfl⟩ := bruhatDiff_exists_presentation D
  change S (∑ w ∈ c.support, c w • bruhatDiffWord w)
  induction c.support using Finset.induction_on with
  | empty => simpa using hc 0
  | insert w s hw ih =>
    rw [Finset.sum_insert hw, Algebra.smul_def]
    exact ha' _ _ (hm _ _ (hc _) (hword w)) ih

end SymbolCalculus

section SpanDifferentiation
variable {G E I : Type*} [TopologicalSpace G] [AddCommGroup E] [Module ℂ E]
  (T : I → E →ₗ[ℂ] (G → ℂ))
private theorem continuous_of_mem_span (hc : ∀ i f, Continuous (T i f)) (L : E →ₗ[ℂ] (G → ℂ))
    (h : L ∈ Submodule.span ℂ (range T)) (f : E) : Continuous (L f) := by
  induction h using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hc i f
  | zero => exact continuous_const
  | add _ _ _ _ ih jh => exact ih.add jh
  | smul c _ _ ih => exact continuous_const.mul ih

private theorem deriv_of_mem_span (path : G → ℝ → G)
    (hd : ∀ i, ∃ D : Submodule.span ℂ (range T), ∀ f x,
      HasDerivAt (fun t ↦ T i f (path x t)) (D.val f x) 0)
    (L : E →ₗ[ℂ] (G → ℂ)) (h : L ∈ Submodule.span ℂ (range T)) :
    ∃ D : Submodule.span ℂ (range T), ∀ f x,
      HasDerivAt (fun t ↦ L f (path x t)) (D.val f x) 0 := by
  induction h using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hd i
  | zero => exact ⟨0, fun _ _ ↦ hasDerivAt_const 0 0⟩
  | add _ _ _ _ ih jh =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨B, hB⟩ := jh
    exact ⟨A+B, fun f x ↦ (hA f x).fun_add (hB f x)⟩
  | smul c _ _ ih =>
    obtain ⟨A, hA⟩ := ih
    exact ⟨c • A, fun f x ↦ (hA f x).const_mul c⟩
end SpanDifferentiation

section WeightedSpan
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
private def weightedSpan := Submodule.span ℂ (range fun i : bruhatDiffAlgebra G ×
    bruhatDiffAlgebra (PontryaginDual G) ↦ bruhatWeightedLinear b i.1 i.2)

private theorem weightedSpan_continuous (e : ElementaryLCAPresentation G) (hb : ∀ x χ, b x χ = χ x)
    (L : weightedSpan b) (f : SchwartzBruhat G) : Continuous (L.val f) := by
  refine continuous_of_mem_span _ (fun i f ↦ ?_) L.val L.property f
  let g : bruhatSmoothSubmodule (G := G) := ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  exact (((mem_schwartzBruhat_iff_bruhatDiff_bounded e b hb g).1 f.property) i.1 i.2).1

/-- The product rule preserves the linear span of symbol-weighted differential operators. -/
private theorem weightedSpan_hasDerivAt (a : LCATopologicalLie G) (L : weightedSpan b) :
    ∃ L' : weightedSpan b, ∀ (f : SchwartzBruhat G) (x : G),
    HasDerivAt (fun t : ℝ ↦ L.val f (x * a (Multiplicative.ofAdd t))) (L'.val f x) 0 := by
  apply deriv_of_mem_span _ (fun x t ↦ x * a (Multiplicative.ofAdd t)) _ L.val L.property
  rintro ⟨D, E⟩
  let symb := hasDerivAt_operatorSymbol b a E
  let E' := symb.choose
  have hE := symb.choose_spec
  let op (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) : weightedSpan b :=
    ⟨_, Submodule.subset_span (mem_range_self i)⟩
  refine ⟨op (D, E') + op (bruhatDiffGenerator a * D, E), fun f x ↦ ?_⟩
  let g : bruhatSmoothSubmodule (G := G) := ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  have hD := hasDerivAt_bruhatDirectionalDeriv a ((mem_bruhatSmoothSubmodule_iff _).1 (D.val g).property 1) x
  have h := (hE x).fun_mul hD
  simp only [ofAdd_zero, map_one, mul_one] at h
  exact h
end WeightedSpan

section ProductDecay
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F] [MeasurableSpace F] [BorelSpace F]
local notation "H" => ElementaryLieGroup m n r F
local notation "Torus" => Fin n → AddCircle (1 : ℝ)
local notation "Dsc" => (Fin r → ℤ) × F

private def realCoord (j : Fin m) : Multiplicative H →ₜ* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (x.toAdd.1 j)
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (PiLp.continuous_apply 2 _ j).comp continuous_fst

private def latticeCoord (j : Fin r) : Multiplicative H →ₜ* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd ((x.toAdd.2.2.1 j : ℤ) : ℝ)
  map_one' := by change ((0 : ℤ) : ℝ) = 0; simp
  map_mul' x y := by change ((x.toAdd.2.2.1 j + y.toAdd.2.2.1 j : ℤ) : ℝ) = _; push_cast; rfl
  continuous_toFun := (continuous_of_discreteTopology : Continuous (fun k : Fin r → ℤ ↦ (k j : ℝ))).comp
    (continuous_fst.comp (continuous_snd.comp continuous_snd))

private def positivePolyWeight (x : H) : ℝ :=
  (∏ i, (1 + x.1 i ^ 2)) * ∏ i, (1 + (x.2.2.1 i : ℝ) ^ 2)

private theorem positivePolyWeight_one_le (x : H) : 1 ≤ positivePolyWeight x :=
  one_le_mul_of_one_le_of_one_le (Finset.one_le_prod₀ fun _ _ ↦ le_add_of_nonneg_right (sq_nonneg _))
    (Finset.one_le_prod₀ fun _ _ ↦ le_add_of_nonneg_right (sq_nonneg _))

private theorem positivePolyWeight_continuous : Continuous (positivePolyWeight (m := m) (n := n) (r := r) (F := F)) :=
  (continuous_finsetProd _ fun i _ ↦ continuous_const.add ((PiLp.continuous_apply 2 _ i).comp continuous_fst |>.pow 2)).mul
  (continuous_finsetProd _ fun i _ ↦ continuous_const.add (((continuous_of_discreteTopology : Continuous (fun k : Fin r → ℤ ↦ (k i : ℝ))).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).pow 2))

private theorem int_inv_one_add_sq_integrable :
    Integrable (fun k : ℤ ↦ (1 + (k : ℝ)^2)⁻¹) Measure.count := by
  apply integrable_count_iff.mpr
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_ (summable_inv_one_add_sq_int.mul_left 2)
  intro k
  have he : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), he, inv_eq_one_div, ← mul_div_assoc, mul_one,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (|(k : ℝ)| - 1), sq_abs (k : ℝ)]

/-- The reciprocal product weight is integrable by separation of the real and lattice coordinates. -/
private theorem integrable_inv_positivePolyWeight :
    Integrable (fun x : H ↦ (positivePolyWeight x)⁻¹) elementaryProductMeasure := by
  have hE : Integrable (fun x : EuclideanSpace ℝ (Fin m) ↦ ∏ i, (1 + x i ^ 2)⁻¹) := by
    apply (PiLp.volume_preserving_toLp (Fin m)).integrable_comp_emb
      (PiLp.homeomorph 2 (fun _ : Fin m ↦ ℝ)).symm.measurableEmbedding |>.mp
    exact Integrable.fintype_prod fun _ ↦ integrable_inv_one_add_sq
  let δ := Measure.pi fun _ : Fin r ↦ (Measure.count : Measure ℤ)
  have hd : (Measure.count : Measure Dsc) = δ.prod Measure.count := by
    apply Measure.ext_of_singleton
    rintro ⟨x, y⟩
    simp only [Measure.count_singleton]
    rw [← singleton_prod_singleton, Measure.prod_prod]
    simp [δ]
  have hZ : Integrable (fun x : Fin r → ℤ ↦ ∏ i, (1 + (x i : ℝ)^2)⁻¹) δ :=
    Integrable.fintype_prod fun _ ↦ int_inv_one_add_sq_integrable
  have hF := integrable_const (μ := (Measure.count : Measure F)) (1 : ℝ)
  have hT := integrable_const (μ := (volume : Measure Torus)) (1 : ℝ)
  dsimp only [elementaryProductMeasure]
  rw [hd]
  simpa only [positivePolyWeight, mul_inv_rev, Finset.prod_inv_distrib, mul_one, one_mul, mul_comm] using
    hE.mul_prod (hT.mul_prod (hZ.mul_prod hF))
end ProductDecay

section ChartTransport
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] (e : ElementaryLCAPresentation G)
local notation "H" => ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
local notation "I" => Fin e.realDim ⊕ Fin e.torusDim
variable [MeasurableSpace G] [BorelSpace G]
local instance : MeasurableSpace e.finiteFactor := borel _
local instance : BorelSpace e.finiteFactor := ⟨rfl⟩

private def elementaryCubeCover : Multiplicative (I → ℝ) →ₜ* G :=
  (e.equiv.symm : Multiplicative H →ₜ* G).comp ⟨cubeCover.toMultiplicative, cubeCover_continuous⟩

private local instance : BorelSpace (Multiplicative H) := by
  have : BorelSpace ((Fin e.latticeRank → ℤ) × e.finiteFactor) := inferInstance
  have : BorelSpace ((Fin e.torusDim → AddCircle (1 : ℝ)) × (Fin e.latticeRank → ℤ) × e.finiteFactor) := inferInstance
  exact inferInstanceAs (BorelSpace H)

private def productHaar : Measure (Multiplicative H) :=
  elementaryProductMeasure

private theorem productHaar_isHaar : (productHaar e).IsHaarMeasure := by
  let ν := elementaryProductMeasure (m := e.realDim) (n := e.torusDim)
    (r := e.latticeRank) (F := e.finiteFactor)
  have : ν.IsAddHaarMeasure := elementaryProductMeasure_isHaar
  have : IsFiniteMeasureOnCompacts (productHaar e) := inferInstanceAs (IsFiniteMeasureOnCompacts ν)
  have : Measure.IsOpenPosMeasure (productHaar e) := inferInstanceAs (Measure.IsOpenPosMeasure ν)
  have : BorelSpace H := inferInstanceAs (BorelSpace (Multiplicative H))
  have : MeasurableAdd H := inferInstance
  have : (productHaar e).IsMulLeftInvariant :=
    ⟨fun x ↦ (measurePreserving_add_left ν x.toAdd).map_eq⟩
  constructor

/-- Every translated coordinate box is dominated by the same multiple of the given Haar measure. -/
private theorem elementaryCubeCover_bound (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ C : ℝ≥0, ∀ x : G,
      (Measure.pi fun _ : I ↦ (volume : Measure ℝ).restrict (Icc 0 1)).map
        (fun v ↦ x * elementaryCubeCover e (Multiplicative.ofAdd v)) ≤ C • μ := by
  let ν := productHaar e
  have : ν.IsHaarMeasure := productHaar_isHaar e
  let ν' := ν.map e.equiv.symm
  have : ν'.IsHaarMeasure := e.equiv.symm.isHaarMeasure_map ν
  let : SecondCountableTopology G := e.equiv.toHomeomorph.isInducing.secondCountableTopology
  refine ⟨ν'.haarScalarFactor μ, fun x ↦ ?_⟩
  rw [← Measure.isMulLeftInvariant_eq_smul ν' μ]
  have hm : (Measure.pi fun _ : I ↦ unitIntervalMeasure).map
      (fun v ↦ elementaryCubeCover e (Multiplicative.ofAdd v)) ≤ ν' := by
    have h := Measure.map_mono (f := e.equiv.symm) (μ := (Measure.pi fun _ : I ↦ unitIntervalMeasure).map
      (fun v ↦ Multiplicative.ofAdd (cubeCover (r := e.latticeRank) (F := e.finiteFactor) v)))
      (ν := ν) cubeCover_map_le e.equiv.symm.continuous.measurable
    have hcov : Measurable (fun v : I → ℝ ↦ Multiplicative.ofAdd (cubeCover (r := e.latticeRank) (F := e.finiteFactor) v)) :=
      (continuous_ofAdd.comp cubeCover_continuous).measurable
    rw [Measure.map_map (show Measurable e.equiv.symm from e.equiv.symm.continuous.measurable) hcov] at h
    exact h
  have ht := Measure.map_mono hm (measurable_const_mul x)
  have hcov : Measurable (fun v : I → ℝ ↦ elementaryCubeCover e (Multiplicative.ofAdd v)) :=
    ((elementaryCubeCover e).continuous.comp continuous_ofAdd).measurable
  rw [(measurePreserving_mul_left ν' x).map_eq, Measure.map_map (measurable_const_mul x)
    hcov] at ht
  have hI : (volume : Measure ℝ).restrict (Icc 0 1) = unitIntervalMeasure :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  simpa only [hI, Function.comp_apply, Function.comp_def] using ht
end ChartTransport

section WeightSymbol
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] (b : G ≃ₜ* PontryaginDual (PontryaginDual G))

private theorem exists_product_symbol {J : Type*} [Fintype J] (l : J → G →ₜ* Multiplicative ℝ) :
    ∃ D : bruhatDiffAlgebra (PontryaginDual G), ∀ x,
      bruhatSymbolHom (b x) D = ∏ j, ((1 + (l j x).toAdd ^ 2 : ℝ) : ℂ) := by
  classical
  have h (j : J) := exists_operator_of_frequency ((l j).comp (b.symm : PontryaginDual (PontryaginDual G) →ₜ* G))
  choose T hT using h
  have hval (j : J) (x : G) : bruhatSymbolHom (b x) (T j) = ((l j x).toAdd : ℂ) := by
    change bruhatDiffSymbol _ _ = _
    simpa using hT j (b x)
  generalize (Finset.univ : Finset J) = s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, fun x ↦ by simp⟩
  | insert i s hi ih =>
    obtain ⟨D, hD⟩ := ih
    exact ⟨(1 + T i ^ 2) * D, fun x ↦ by simp [hi, hval, hD]⟩

/-- A positive polynomial symbol has reciprocal in every integer Lᵠ space with q at least one. -/
private theorem elementary_decay_symbol (e : ElementaryLCAPresentation G) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    ∃ (W : bruhatDiffAlgebra (PontryaginDual G)) (w : G → ℝ),
      (∀ x, bruhatSymbolHom (b x) W = (w x : ℂ)) ∧
      (∀ x, 1 ≤ w x) ∧ MemLp (fun x ↦ (w x)⁻¹) (q : ℝ≥0∞) μ := by
  let H := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let : MeasurableSpace e.finiteFactor := borel _
  let : BorelSpace e.finiteFactor := ⟨rfl⟩
  let w (x : G) := positivePolyWeight (e.equiv x).toAdd
  have hw (x : G) : 1 ≤ w x := positivePolyWeight_one_le _
  let L (i : Fin e.realDim) := (realCoord (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor) i).comp (e.equiv : G →ₜ* _)
  let Z (i : Fin e.latticeRank) := (latticeCoord (m := e.realDim) (n := e.torusDim) (F := e.finiteFactor) i).comp (e.equiv : G →ₜ* _)
  obtain ⟨A, hA⟩ := exists_product_symbol b L
  obtain ⟨B, hB⟩ := exists_product_symbol b Z
  refine ⟨A * B, w, fun x ↦ ?_, hw, ?_⟩
  · rw [map_mul, hA, hB]
    simp only [w, positivePolyWeight, Complex.ofReal_mul, Complex.ofReal_prod]
    rfl
  let ν := productHaar e
  have : ν.IsHaarMeasure := productHaar_isHaar e
  have : BorelSpace ((Fin e.latticeRank → ℤ) × e.finiteFactor) := inferInstance
  have : BorelSpace ((Fin e.torusDim → AddCircle (1 : ℝ)) × (Fin e.latticeRank → ℤ) × e.finiteFactor) := inferInstance
  have : BorelSpace (Multiplicative H) := inferInstanceAs (BorelSpace H)
  have : SecondCountableTopology (Multiplicative H) := inferInstanceAs (SecondCountableTopology H)
  let ν' := ν.map e.equiv.symm
  have : ν'.IsHaarMeasure := e.equiv.symm.isHaarMeasure_map ν
  let : SecondCountableTopology G := e.equiv.toHomeomorph.isInducing.secondCountableTopology
  have hc : Continuous w := positivePolyWeight_continuous.comp (continuous_toAdd.comp e.equiv.continuous)
  have hwi : Continuous (fun x ↦ (w x)⁻¹) := hc.inv₀ fun x ↦ (zero_lt_one.trans_le (hw x)).ne'
  have hi : Integrable (fun x ↦ (w x)⁻¹) ν' := by
    apply (integrable_map_measure hwi.aestronglyMeasurable e.equiv.symm.continuous.aemeasurable).2
    change Integrable (fun x : Multiplicative H ↦ (positivePolyWeight (e.equiv (e.equiv.symm x)).toAdd)⁻¹) ν
    simpa only [e.equiv.apply_symm_apply] using!
      (integrable_inv_positivePolyWeight (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor))
  have hiμ := hi.smul_measure (c := (μ.haarScalarFactor ν' : ℝ≥0∞)) ENNReal.coe_ne_top
  change Integrable _ (μ.haarScalarFactor ν' • ν') at hiμ
  rw [← Measure.isMulLeftInvariant_eq_smul μ ν'] at hiμ
  apply (integrable_norm_rpow_iff hwi.aestronglyMeasurable (by exact_mod_cast (Nat.ne_zero_of_lt hq)) (by simp)).1
  apply hiμ.mono' (hwi.norm.measurable.pow_const _ |>.aestronglyMeasurable)
  refine ae_of_all _ fun x ↦ ?_
  have hpos := inv_nonneg.mpr (zero_le_one.trans (hw x))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    Real.norm_eq_abs, abs_of_nonneg hpos]
  exact Real.rpow_le_self_of_le_one hpos (inv_le_one_of_one_le₀ (hw x)) (by simpa using (show (1 : ℝ) ≤ q from by exact_mod_cast hq))
end WeightSymbol

section CubeEstimate
variable {G J A E : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Fintype J] [DecidableEq J]
  (ρ : Multiplicative (J → ℝ) →ₜ* G) (U : A → E → G → ℂ)
  (hc : ∀ l f, Continuous (U l f))
  (hd : ∀ (a : LCATopologicalLie G) l, ∃ l', ∀ f x,
    HasDerivAt (fun t : ℝ ↦ U l f (x * a (Multiplicative.ofAdd t))) (U l' f x) 0)

include hc hd in
/-- Iterating the one-coordinate fundamental theorem of calculus bounds evaluation by a finite sum of integrals over the cube. -/
private theorem cube_estimate (l : A) : ∃ (k : ℕ) (w : Fin k → A), ∀ f x,
    ‖U l f x‖ₑ ≤ ∑ j, ∫⁻ v : J → ℝ, ‖U (w j) f (x * ρ (Multiplicative.ofAdd v))‖ₑ
      ∂Measure.pi (fun _ ↦ (volume : Measure ℝ).restrict (Icc 0 1)) := by
  let μ (_ : J) := (volume : Measure ℝ).restrict (Icc 0 1)
  let (i : J) : IsFiniteMeasure (μ i) := by dsimp [μ]; infer_instance
  let u (l : A) (f : E) (x : G) (v : J → ℝ) := ‖U l f (x * ρ (Multiplicative.ofAdd v))‖ₑ
  have hu (l : A) (f : E) (x : G) : Measurable (u l f x) := ((hc l f).comp
    (continuous_const.mul (ρ.continuous.comp continuous_ofAdd))).eNorm.measurable
  let inc (i : J) := (LinearMap.single ℝ (fun _ : J ↦ ℝ) i).toAddMonoidHom
  let a (i : J) : LCATopologicalLie G := ρ.comp
    ⟨(inc i).toMultiplicative, show Continuous (fun t : ℝ ↦ Pi.single (M := fun _ : J ↦ ℝ) i t) from continuous_single (A := fun _ : J ↦ ℝ) i⟩
  choose D hD using fun i l ↦ hd (a i) l
  have hslice (l : A) (f : E) (x : G) (v : J → ℝ) (i : J) (hi : v i = 0) :
      u l f x v ≤ (∫⁻ t, u l f x (update v i t) ∂(μ i)) +
        ∫⁻ t, u (D i l) f x (update v i t) ∂(μ i) := by
    let p (t : ℝ) := x * ρ (Multiplicative.ofAdd (update v i t))
    have hp : Continuous p := continuous_const.mul (ρ.continuous.comp
      (continuous_ofAdd.comp (continuous_const.update i continuous_id)))
    have hh (t : ℝ) : HasDerivAt (fun s ↦ U l f (p s)) (U (D i l) f (p t)) t := by
      have h := (show HasDerivAt _ _ (t - t) from (sub_self t).symm ▸ hD i l f (p t)).comp_sub_const t t
      convert h using 1
      funext s
      congr 1
      change x * ρ _ = (x * ρ (Multiplicative.ofAdd (update v i t))) *
        ρ (Multiplicative.ofAdd (Pi.single i (s - t)))
      rw [mul_assoc, ← map_mul]
      congr 2
      change update v i s = update v i t + Pi.single i (s - t)
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj, Pi.single_eq_of_ne]
    have h := enorm_le_unitInterval hh ((hc _ f).comp hp) 0
    have hz : update v i 0 = v := hi ▸ update_eq_self i v
    simpa only [u, p, μ, zero_add, hz] using h
  have hs (s : Finset J) (l : A) : ∃ (k : ℕ) (w : Fin k → A), ∀ f x v
      (_ : ∀ i ∈ s, v i = 0), u l f x v ≤ ∑ j, lmarginal μ s (u (w j) f x) v := by
    induction s using Finset.induction_on generalizing l with
    | empty => exact ⟨1, fun _ ↦ l, fun _ _ _ _ ↦ by simp⟩
    | @insert i s hi ih =>
      obtain ⟨k, w, hw⟩ := ih l
      obtain ⟨k', w', hw'⟩ := ih (D i l)
      refine ⟨k + k', Fin.append w w', fun f x v hv ↦ ?_⟩
      have hz (t : ℝ) (j : J) (hj : j ∈ s) : update v i t j = 0 := by
        rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
        exact hv j (Finset.mem_insert_of_mem hj)
      apply (hslice l f x v i (hv i (Finset.mem_insert_self ..))).trans
      apply (add_le_add (lintegral_mono fun t ↦ hw f x _ (hz t))
        (lintegral_mono fun t ↦ hw' f x _ (hz t))).trans_eq
      have inner {p : ℕ} (z : Fin p → A) :
          (∫⁻ t, ∑ j, lmarginal μ s (u (z j) f x) (update v i t) ∂μ i) =
          ∑ j, lmarginal μ (insert i s) (u (z j) f x) v := by
        rw [lintegral_finsetSum]
        · exact Finset.sum_congr rfl fun j _ ↦ (lmarginal_insert _ (hu _ f x) hi v).symm
        · exact fun j _ ↦ ((hu _ f x).lmarginal μ).comp (continuous_const.update i continuous_id).measurable
      rw [inner, inner, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  obtain ⟨k, w, hw⟩ := hs Finset.univ l
  refine ⟨k, w, fun f x ↦ ?_⟩
  simpa only [lmarginal_univ, u, ofAdd_zero, map_one, mul_one] using hw f x 0 (fun _ _ ↦ rfl)
end CubeEstimate

section CubeIntegral
variable {G J : Type*} [Fintype J] [MeasurableSpace G]
private theorem cube_integral_le_eLpNorm (μ : Measure G) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (v : (J → ℝ) → G) (hv : Measurable v) (C : ℝ≥0)
    (h : (Measure.pi fun _ : J ↦ (volume : Measure ℝ).restrict (Icc 0 1)).map v ≤ C • μ)
    (g : G → ℂ) (hg : Measurable g) :
    (∫⁻ x, ‖g (v x)‖ₑ ∂Measure.pi fun _ : J ↦ (volume : Measure ℝ).restrict (Icc 0 1)) ≤
      ((C ^ (1 / p).toReal : ℝ≥0) : ℝ≥0∞) * eLpNorm g p μ := by
  let τ := (volume : Measure ℝ).restrict (Icc 0 1)
  have : IsProbabilityMeasure τ := ⟨by simp [τ, Real.volume_Icc]⟩
  let ν := Measure.pi fun _ : J ↦ τ
  have hm : AEStronglyMeasurable (g ∘ v) ν := (hg.comp hv).aestronglyMeasurable
  calc
    _ = eLpNorm (g ∘ v) 1 ν := (eLpNorm_one_eq_lintegral_eNorm hm).symm
    _ ≤ eLpNorm (g ∘ v) p ν := by simpa [ν] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hm
    _ = eLpNorm g p (ν.map v) := (eLpNorm_map_measure hg.aestronglyMeasurable hv.aemeasurable).symm
    _ ≤ eLpNorm g p ((C : ℝ≥0∞) • μ) := eLpNorm_mono_measure _ h
    _ = _ := by
      rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (zero_lt_one.trans_le hp).ne' hp',
        ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
      rfl
end CubeIntegral

section TopologyComparison
variable {X E I : Type*} [MeasurableSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  {μ : Measure X} {p : ℝ≥0∞} (U : I → E →ₗ[ℂ] (X → ℂ))

/-- Comparison with an integrable majorant and a finite sum of norms in the linear span. -/
private theorem generatesLp_of_weight_and_points (hp : 1 ≤ p)
    (hs : GeneratesSeminormTopology (fun i f ↦ ⨆ x, ‖U i f x‖ₑ))
    (hm : ∀ i f, AEStronglyMeasurable (U i f) μ)
    (w : X → ℝ) (hw : ∀ x, 1 ≤ w x) (hwLp : MemLp (fun x ↦ (w x)⁻¹) p μ)
    (hweight : ∀ i, ∃ j, ∀ f x, U j f x = (w x : ℂ) * U i f x)
    (hpoint : ∀ i, ∃ (k : ℕ) (L : Fin k → Submodule.span ℂ (range U)) (C : ℝ≥0), ∀ f x,
      ‖U i f x‖ₑ ≤ ∑ j, (C : ℝ≥0∞) * eLpNorm ((L j).val f) p μ) :
    GeneratesLpSeminorms μ p (fun i ↦ U i) := by
  classical
  let : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨P, hP, hval⟩ := hs
  change ∀ i f, ENNReal.ofReal (P i f) = ⨆ x, ‖U i f x‖ₑ at hval
  choose j hj using hweight
  have hbound (i : I) (f : E) (x : X) : ‖U i f x‖ ≤ P (j i) f * (w x)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (zero_lt_one.trans_le (hw x)), mul_comm]
    have h := le_iSup (fun y ↦ ‖U (j i) f y‖ₑ) x
    rw [← hval, hj, eNorm_eq_nnNorm] at h
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa [norm_mul, abs_of_nonneg (zero_le_one.trans (hw x)), ENNReal.toReal_ofReal (apply_nonneg _ _)] using hh
  have hmaj (i : I) (f : E) := hwLp.const_smul (P (j i) f)
  have hmem (i : I) (f : E) : MemLp (U i f) p μ :=
    (hmaj i f).of_le (hm i f) (ae_of_all _ fun x ↦ (hbound i f x).trans (le_abs_self _))
  let T (i : I) : E →ₗ[ℂ] Lp ℂ p μ :=
    { toFun := fun f ↦ (hmem i f).toLp _
      map_add' := fun _ _ ↦ by simp only [map_add]; rfl
      map_smul' := fun _ _ ↦ by simp only [map_smul, RingHom.id_apply]; rfl }
  let Q (i : I) := (normSeminorm ℂ (Lp ℂ p μ)).comp (T i)
  have hQ (i : I) (f : E) : Q i f = lpNorm (U i f) p μ := by
    change ‖(hmem i f).toLp _‖ = _
    rw [Lp.norm_toLp, toReal_eLpNorm]
  refine ⟨hmem, Q, hP.congr (Seminorm.IsBounded.of_real fun i ↦ ?_)
    (Seminorm.IsBounded.of_real fun i ↦ ?_), fun i f ↦ ?_⟩
  · refine ⟨{j i}, lpNorm (fun x ↦ (w x)⁻¹) p μ, fun f ↦ ?_⟩
    simp only [LinearMap.id_apply, Finset.sup_singleton, hQ]
    apply (lpNorm_mono_real (hmaj i f) (hbound i f)).trans_eq
    rw [lpNorm_const_smul, coe_nnNorm, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg _ _), mul_comm]
  · obtain ⟨k, L, C, hl⟩ := hpoint i
    have hspan (s : Fin k) := lp_span_bound hp U hmem (L s).val (L s).property
    choose t M hM using fun s ↦ (hspan s).2 Q hQ
    let support := Finset.univ.biUnion t
    let B := ∑ s, (C : ℝ) * |M s|
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ mul_nonneg C.coe_nonneg (abs_nonneg _)
    refine ⟨support, B, fun f ↦ ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (apply_nonneg _ _))).mp
    rw [LinearMap.id_apply, hval]
    apply iSup_le
    intro x
    apply (hl f x).trans
    have hc (s : Fin k) : (C : ℝ≥0∞) * eLpNorm ((L s).val f) p μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top ((hspan s).1 f).eLpNorm_ne_top
    rw [← ENNReal.ofReal_toReal (ENNReal.sum_ne_top.mpr fun s _ ↦ hc s)]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_sum fun s _ ↦ hc s, Finset.sum_mul]
    apply Finset.sum_le_sum fun s _ ↦ ?_
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_eLpNorm, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
    apply (hM s f).trans
    exact mul_le_mul (le_abs_self _) ((show (t s).sup Q ≤ support.sup Q from Finset.sup_mono (Finset.subset_biUnion_of_mem t (Finset.mem_univ s))) f)
      (apply_nonneg _ _) (abs_nonneg _)
  · rw [hQ, ofReal_lpNorm (hmem i f)]
end TopologyComparison

section ElementaryLpProof
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] (e : ElementaryLCAPresentation G)
  (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)

private theorem weighted_mul_symbol (W : bruhatDiffAlgebra (PontryaginDual G)) (w : G → ℝ)
    (hW : ∀ x, bruhatSymbolHom (b x) W = (w x : ℂ))
    (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) :
    ∃ j : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G), ∀ (f : SchwartzBruhat G) x,
      bruhatWeightedLinear b j.1 j.2 f x = (w x : ℂ) * bruhatWeightedLinear b i.1 i.2 f x := by
  refine ⟨(i.1, W * i.2), fun f x ↦ ?_⟩
  have heq : bruhatSymbolHom (b x) (W * i.2) = (w x : ℂ) * bruhatSymbolHom (b x) i.2 :=
    ((bruhatSymbolHom (b x)).map_mul W i.2).trans (congrArg (· * bruhatSymbolHom (b x) i.2) (hW x))
  exact (congrArg (· * _) heq).trans (mul_assoc _ _ _)

/-- The continuous action of the generators on Schwartz functions extends to their algebra. -/
private theorem bruhatDiff_continuousLift (D : bruhatDiffAlgebra G) :
    ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f,
      smoothIncl (G := G) (A f) = D.val (smoothIncl (G := G) f) := by
  refine Algebra.adjoin_induction (s := range (bruhatFirstOrder (G := G)))
    (p := fun B _ ↦ ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat G, ∀ f,
      smoothIncl (G := G) (A f) = B (smoothIncl (G := G) f)) ?_ ?_ ?_ ?_ D.property
  · rintro _ ⟨a, rfl⟩
    let h := bruhatFirstOrder_schwartz (G := G) a
    exact ⟨h.choose, fun f ↦ Subtype.ext (funext (h.choose_spec f))⟩
  · exact fun c ↦ ⟨c • ContinuousLinearMap.id ℂ _, fun _ ↦ rfl⟩
  · rintro B C _ _ ⟨A, hA⟩ ⟨A', hA'⟩
    exact ⟨A + A', fun f ↦ ((smoothIncl (G := G)).map_add _ _).trans (congrArg₂ (· + ·) (hA f) (hA' f))⟩
  · rintro B C _ _ ⟨A, hA⟩ ⟨A', hA'⟩
    exact ⟨A.comp A', fun f ↦ (hA (A' f)).trans (congrArg B (hA' f))⟩

/-- Barrelledness makes the supremum of the pointwise bounded family of weighted
evaluation seminorms continuous. -/
private theorem bruhatWeighted_sup_seminorm (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)) :
    ∃ q : Seminorm ℂ (SchwartzBruhat G), Continuous q ∧ ∀ f,
      ENNReal.ofReal (q f) = ⨆ x, (‖bruhatWeightedLinear b D E f x‖₊ : ℝ≥0∞) := by
  let : BarrelledSpace ℂ (SchwartzBruhat G) := schwartzBruhat_barrelled_of_stages
  let U := bruhatWeightedLinear b D E
  let p (x : G) := (normSeminorm ℂ ℂ).comp ((LinearMap.proj x).comp U)
  let lift := bruhatDiff_continuousLift (G := G) D
  let A := lift.choose
  have hA := lift.choose_spec
  let chart := elementarySchwartz_equiv_schwartzBruhat e
  let I := chart.choose
  have hI := chart.choose_spec
  have heval (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
    have h := elementarySchwartz_continuousEval.comp
      (I.symm.continuous.prodMk (continuous_const (y := (e.equiv x).toAdd)))
    exact h.congr fun f ↦ (hI (I.symm f) x).symm.trans
      (congrArg (fun g : SchwartzBruhat G ↦ g x) (I.apply_symm_apply f))
  have hpc (x : G) : Continuous (p x) := by
    apply (continuous_const.mul ((heval x).comp A.continuous)).norm.congr
    intro f
    exact congrArg (fun z : ℂ ↦ ‖bruhatDiffSymbol E (b x) * z‖)
      (congrArg (fun g : bruhatSmoothSubmodule (G := G) ↦ g.val x) (hA f))
  have hbdd (f : SchwartzBruhat G) : Continuous (U f) ∧ ∃ C : ℝ, ∀ x, ‖U f x‖ ≤ C :=
    (mem_schwartzBruhat_iff_bruhatDiff_bounded e b hb (smoothIncl (G := G) f)).1 f.property D E
  have hB : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr fun f ↦
    ⟨(hbdd f).2.choose, forall_mem_range.mpr (fun x ↦ (hbdd f).2.choose_spec x)⟩
  refine ⟨⨆ x, p x, (congrArg (fun q : SchwartzBruhat G → ℝ ↦ Continuous q) (Seminorm.coe_iSup_eq hB)).mpr
    (Seminorm.continuous_iSup p hpc hB), fun f ↦ ?_⟩
  let g := BoundedContinuousFunction.ofNormedAddCommGroup (U f) (hbdd f).1
    (hbdd f).2.choose (hbdd f).2.choose_spec
  have hv : (⨆ x, p x) f = ‖g‖ := (Seminorm.iSup_apply hB).trans g.norm_eq_iSup_norm.symm
  exact (congrArg ENNReal.ofReal hv).trans ((ofReal_norm g).trans g.eNorm_eq_iSup_eNorm)

/-- Each coordinate seminorm of the elementary presentation occurs among the symbol-weighted
operator suprema, by lifting its mixed partial and its coordinate monomial separately. -/
private theorem elementarySchwartz_coordinate_le_operator (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (I : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhat G)
    (hI : ∀ f (x : G), I f x = f (e.equiv x).toAdd)
    (i : ElementarySchwartzIndex e.realDim e.torusDim e.latticeRank) :
    ∃ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
      ∀ f : SchwartzBruhatStage e, elementarySchwartzBound f.val i ≤
        ⨆ x, (‖bruhatWeightedLinear b D E (I f) x‖₊ : ℝ≥0∞) := by
  let dirs := (List.ofFn fun j ↦ List.replicate (i.2.1 j)
    ((EuclideanSpace.single j (1 : ℝ), 0) :
      EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim))).flatten ++
    (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
  let diff := exists_diff_cover_word e dirs
  let D := diff.choose
  have hD := diff.choose_spec
  let wt := exists_elementary_weight e b hb i.1 i.2.2.2
  let E := wt.choose
  have hE := wt.choose_spec
  refine ⟨D, E, fun f ↦ iSup_le fun u ↦ iSup_le fun z ↦ iSup_le fun t ↦ ?_⟩
  let y := elementaryCover u z t
  let x := e.equiv.symm (.ofAdd y)
  apply le_iSup_of_le x
  have hd := hD (smoothIncl (G := G) (I f)) u z t
  have he (w) : (smoothIncl (G := G) (I f)).val (e.equiv.symm (.ofAdd (elementaryCover w z t))) =
      f (elementaryCover w z t) := by
    change I f _ = _
    rw [hI, e.equiv.apply_symm_apply]
    rfl
  simp only [he] at hd
  change _ ≤ (‖bruhatDiffSymbol E (b x) * (D.val (smoothIncl (G := G) (I f))).val x‖₊ : ℝ≥0∞)
  exact (congrArg (fun v : ℂ ↦ (‖v‖₊ : ℝ≥0∞)) (congrArg₂ (· * ·) (hE y) hd)).symm.le

private theorem bruhatWeighted_sup_generates (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x) :
    GeneratesSeminormTopology (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      fun f : SchwartzBruhat G ↦ ⨆ x, (‖bruhatDiffSymbolWeightedApply b i.1 i.2 f x‖₊ : ℝ≥0∞)) := by
  classical
  choose Q hQ hv using fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
    bruhatWeighted_sup_seminorm e b hb i.1 i.2
  let chart := elementarySchwartz_equiv_schwartzBruhat e
  let I := chart.choose
  have hI := chart.choose_spec
  have hP := I.symm.toHomeomorph.isInducing.withSeminorms
    (f := I.symm.toLinearMap) elementarySchwartz_withSeminorms
  refine ⟨Q, hP.congr (fun i ↦ ?_) (fun i ↦ ?_), hv⟩
  · let h := Seminorm.bound_of_continuous hP (Q i) (hQ i)
    exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩
  · let ub := elementarySchwartz_coordinate_le_operator e b hb I hI i
    let D := ub.choose
    let E := ub.choose_spec.choose
    have h := ub.choose_spec.choose_spec
    have heq : (1 : ℝ≥0) • ({(D, E)} : Finset _).sup Q = Q (D, E) :=
      (one_smul _ _).trans (Finset.sup_singleton : _)
    refine ⟨{(D, E)}, 1, le_trans ?_ heq.ge⟩
    intro f
    change (elementarySchwartzBound (I.symm f).val i).toReal ≤ Q (D, E) f
    have hb := h (I.symm f)
    have he := congrArg (fun g : SchwartzBruhat G ↦ ⨆ x, (‖bruhatWeightedLinear b D E g x‖₊ : ℝ≥0∞))
      (I.apply_symm_apply f)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.trans_eq (he.trans (hv (D, E) f).symm))).trans_eq
      (ENNReal.toReal_ofReal (apply_nonneg _ _))

end ElementaryLpProof


variable (e : ElementaryLCAPresentation G)
variable (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)

include e hb

variable {d d' : ℕ}
variable (a : Fin d → LCATopologicalLie G) (a' : Fin d' → LCATopologicalLie (PontryaginDual G))
variable
  (ha : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) =
    bruhatDiffDegreeOneReal (G := G))
  (ha' : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a' j)))
  (hspan' : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a' j))) =
    bruhatDiffDegreeOneReal (G := PontryaginDual G))

include ha hspan ha' hspan'

/-- Paper: Proposition D.1.10.6(3), p. 787. The monomials in any pair of real
first-order bases suffice for the sup family. -/
theorem elementarySchwartz_basisSup_generates :
    GeneratesSeminormTopology (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
      fun f : SchwartzBruhat G ↦ ⨆ x,
        (‖bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2) f x‖₊ : ℝ≥0∞)) := by
  exact generatesSupSeminorms_of_span_eq _ _ (bruhatWeightedLinear_monomial_span b a a' hspan hspan')
    (bruhatWeighted_sup_generates e b hb)

omit ha hspan ha' hspan' in
/-- Paper: Proposition D.1.10.6(1), p. 787. The sup norms of the symbol-weighted
derivatives for arbitrary pairs of invariant operators generate the Schwartz topology. -/
theorem elementarySchwartz_operatorSup_generates :
    GeneratesSeminormTopology (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      fun f : SchwartzBruhat G ↦
        ⨆ x, (‖bruhatDiffSymbolWeightedApply b i.1 i.2 f x‖₊ : ℝ≥0∞)) := by
  let hE := (lca_elementary_iff (G := G)).mpr ⟨e⟩
  let e' := Classical.choice ((lca_elementary_iff (G := PontryaginDual G)).mp
    ⟨isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean hE.2,
      isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
        (isCompactlyGeneratedGroup_of_continuousMulEquiv b hE.1)⟩)
  let P := elementary_exists_firstOrder_basis e
  let Q := elementary_exists_firstOrder_basis e'
  let d := P.choose
  let d' := Q.choose
  let a := P.choose_spec.choose
  let a' := Q.choose_spec.choose
  have ha := P.choose_spec.choose_spec
  have ha' := Q.choose_spec.choose_spec
  let T (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) :=
    bruhatWeightedLinear b i.1 i.2
  let U (i : (Fin d → ℕ) × (Fin d' → ℕ)) :=
    bruhatWeightedLinear b (bruhatDiffMonomial a i.1) (bruhatDiffMonomial a' i.2)
  have hU := elementarySchwartz_basisSup_generates e b hb a a' ha.1 ha.2 ha'.1 ha'.2
  change GeneratesSeminormTopology (fun i f ↦ ⨆ x, (‖U i f x‖₊ : ℝ≥0∞)) at hU
  change GeneratesSeminormTopology (fun i f ↦ ⨆ x, (‖T i f x‖₊ : ℝ≥0∞))
  exact generatesSupSeminorms_of_span_eq U T (bruhatWeightedLinear_monomial_span b a a' ha.2 ha'.2).symm hU

omit ha hspan ha' hspan' in
/-- The cube estimate applies to every finite real exponent at least one. -/
private theorem elementarySchwartz_operatorLp_finite [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ⊤) :
    GeneratesLpSeminorms μ p
      (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
        bruhatDiffSymbolWeightedApply b i.1 i.2) := by
  classical
  let U (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) := bruhatWeightedLinear b i.1 i.2
  let gen (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) : weightedSpan b :=
    ⟨U i, Submodule.subset_span (mem_range_self i)⟩
  let V (L : weightedSpan b) (f : SchwartzBruhat G) := L.val f
  have hCts (L : weightedSpan b) (f : SchwartzBruhat G) : Continuous (V L f) :=
    weightedSpan_continuous b e hb L f
  let h := elementary_decay_symbol b e μ 1 le_rfl
  let W := h.choose
  let w := h.choose_spec.choose
  have hW := h.choose_spec.choose_spec.1
  have hw := h.choose_spec.choose_spec.2
  have h1 : MemLp (fun x ↦ (w x)⁻¹) 1 μ := by simpa using hw.2
  have hi : Integrable (fun x ↦ (w x)⁻¹) μ := memLp_one_iff_integrable.mp h1
  have hwLp : MemLp (fun x ↦ (w x)⁻¹) p μ := by
    apply (integrable_norm_rpow_iff h1.aestronglyMeasurable (zero_lt_one.trans_le hp).ne' hfin).mp
    apply hi.mono' ((h1.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable)
    refine ae_of_all _ fun x ↦ ?_
    have hn := inv_nonneg.mpr (zero_le_one.trans (hw.1 x))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.norm_eq_abs, abs_of_nonneg hn]
    exact Real.rpow_le_self_of_le_one hn (inv_le_one_of_one_le₀ (hw.1 x))
      (by simpa using ENNReal.toReal_mono hfin hp)
  refine generatesLp_of_weight_and_points U hp (elementarySchwartz_operatorSup_generates e b hb)
    (fun i f ↦ (hCts (gen i) f).aestronglyMeasurable) w hw.1 hwLp (weighted_mul_symbol b W w hW) (fun i ↦ ?_)
  let ρ := elementaryCubeCover e
  let cube := cube_estimate ρ V hCts (weightedSpan_hasDerivAt b) (gen i)
  let k := cube.choose
  let L := cube.choose_spec.choose
  have hL := cube.choose_spec.choose_spec
  let bound := elementaryCubeCover_bound e μ
  let C := bound.choose
  have hC := bound.choose_spec
  refine ⟨k, L, C ^ (1 / p).toReal, fun f x ↦ (hL f x).trans ?_⟩
  apply Finset.sum_le_sum fun j _ ↦ ?_
  exact cube_integral_le_eLpNorm μ hp hfin _
    (continuous_const.mul (ρ.continuous.comp continuous_ofAdd)).measurable C (hC x) _ (hCts _ f).measurable

omit ha hspan ha' hspan' in
/-- Paper: Proposition D.1.10.6(2), p. 787. For each integer q at least one,
the Lᵠ norms of the symbol-weighted derivatives generate the Schwartz topology. -/
theorem elementarySchwartz_operatorLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
        bruhatDiffSymbolWeightedApply b i.1 i.2) := by
  exact elementarySchwartz_operatorLp_finite e b hb μ q (by exact_mod_cast hq) (by simp)

/-- Paper: Proposition D.1.10.6(4), p. 787. The monomials in any pair of real
first-order bases suffice for each finite integer Lᵠ family. -/
theorem elementarySchwartz_basisLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
        bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2)) := by
  exact generatesLpSeminorms_of_span_eq (by exact_mod_cast hq) _ _
    (bruhatWeightedLinear_monomial_span b a a' hspan hspan')
    (elementarySchwartz_operatorLp_generates e b hb μ q hq)

-- TODO(paper-gap): On p. 789 the proof uses convergence in the new seminorm
-- to identify its value at the limit before proving its continuity.

end ElementaryOperators

section IdeleClassSeminorms

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.7, p. 789. Realize the space of k-invariant
Schwartz–Bruhat functions as a submodule with the inherited topology. -/
def schwartzBruhatInvariantSubmodule (k : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  let ev (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  ⨅ (g : G) (u : k), (ev (g * u.val) - ev g).ker

/-- Paper: Proposition D.1.10.7, p. 789. The fixed submodule consists exactly
of the functions invariant under translation by the subgroup.
Deviation: Sanity check on the fixed subspace used for S(k,G). -/
theorem mem_schwartzBruhatInvariantSubmodule_iff
    (k : Subgroup G) (f : SchwartzBruhat G) :
    f ∈ schwartzBruhatInvariantSubmodule k ↔
      ∀ (x : G) (u : k), f (x * u.val) = f x := by
  simp only [schwartzBruhatInvariantSubmodule, Submodule.mem_iInf]
  refine forall_congr' fun x ↦ forall_congr' fun u ↦ ?_
  rw [LinearMap.mem_ker]
  exact sub_eq_zero

/-- Paper: (D.1.10.15), p. 789. The helper takes the compact-direction and norm-section
derivatives at `x` and multiplies by a weight evaluated at the absolute logarithm of `t`.

Deviation: The weight parameter is independent of `x`. Taking `t = n x` and
`weight u = 1 + u ^ r` gives the weighted derivative used under the printed supremum.
The radial derivatives use the exponential coordinate, so differentiation with respect
to its parameter is the operator t∂t. -/
def ideleClassWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (t : ℝ≥0ˣ) (x : G) : ℂ :=
  let j : n.ker →ₜ* G := ⟨n.ker.subtype, continuous_subtype_val⟩
  let D := bruhatDiffMonomial (fun i ↦ j.comp (γ i)) α
  let Df := D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  (weight |Real.log (t.val : ℝ)| : ℂ) *
    iteratedDeriv m (fun s : ℝ ↦
      Df.val (τ (Units.mk0 (Real.exp s).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos s)))) * x)) 0

/-- The monomial of multi-index zero is the identity operator. -/
theorem bruhatDiffMonomial_zero {d : ℕ} (a : Fin d → LCATopologicalLie G) :
    bruhatDiffMonomial a 0 = 1 := by
  have h : (List.finRange d).flatMap (fun j ↦ List.replicate ((0 : Fin d → ℕ) j) (a j)) = [] :=
    List.flatMap_eq_nil_iff.2 (by simp)
  rw [bruhatDiffMonomial, h]
  rfl

/-- Paper: (D.1.10.15), p. 789. At zero differential orders the value at `x` is
multiplied by the weight at the absolute logarithm of `t`. Taking `t = n x` gives the
norm argument in the printed expression. -/
theorem ideleClassWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (weight : ℝ → ℝ) (f : SchwartzBruhat G)
    (t : ℝ≥0ˣ) (x : G) :
    ideleClassWeightedDeriv n τ γ 0 0 weight f t x =
      (weight |Real.log (t.val : ℝ)| : ℂ) * f x := by
  simp only [ideleClassWeightedDeriv, iteratedDeriv_zero, bruhatDiffMonomial_zero]
  congr 1
  have h1 : Units.mk0 (Real.exp 0).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos 0))) = (1 : ℝ≥0ˣ) :=
    Units.ext (by simp)
  rw [h1, map_one, one_mul]
  rfl

universe u

variable (F : Type u) [Field F] [NumberField F]

local instance : T2Space C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.1
local instance : LocallyCompactSpace C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.2.1

local notation "C₀[" F "]" => Subgroup.connectedComponentOfOne C[F]
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "d[" F "]" => (Module.finrank ℚ F - 1)

local instance : LocallyCompactSpace C₀[F] := isClosed_connectedComponent.locallyCompactSpace
local instance : LocallyCompactSpace C₁[F] :=
  (ideleClassGroup_finiteness F).1.locallyCompactSpace

/-- Paper: Remark D.1.10.8, p. 789. Every continuous one-parameter subgroup
of the norm-one idele classes has image in their identity component. -/
theorem normOneIdeleClass_direction_mem_connectedComponent
    (γ : LCATopologicalLie C₁[F]) (t : ℝ) :
    γ (Multiplicative.ofAdd t) ∈ Subgroup.connectedComponentOfOne C₁[F] := by
  have : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
  exact (isPreconnected_range γ.continuous).subset_connectedComponent
    ⟨1, map_one γ⟩ ⟨_, rfl⟩

-- TODO(paper-gap): In D.1.10.9 the subgroup Γ is unbound. The stage S(k,C_F) in
-- the title and conclusion uses the full group, which is compactly generated.
-- TODO(paper-gap): On p. 791 the proof claims generation on the entire LF-space.
-- Over ℚ, fixed radial bumps times indicators of shrinking open subgroups of
-- the norm-one group tend to zero in the listed Lᵖ norms but retain their value at 1.

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. Evaluate the weighted
directional derivative in the product chart of a norm section and its kernel. -/
def ideleClassProductWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) : ℂ :=
  ideleClassWeightedDeriv n τ γ m α weight f z.1 (τ z.1 * z.2.val)

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. At zero differential orders
and unit weight evaluation is at the idele class represented by the product chart.
Deviation: Sanity check on the section and kernel factors. -/
theorem ideleClassProductWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) :
    ideleClassProductWeightedDeriv n τ γ 0 0 (fun _ ↦ 1) f z = f (τ z.1 * z.2.val) := by
  rw [ideleClassProductWeightedDeriv, ideleClassWeightedDeriv_zero]
  simp

section WeightFamilies

variable {E X I : Type*} [AddCommGroup E] [Module ℂ E]
variable [TopologicalSpace E] [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞}

omit [MeasurableSpace X] [TopologicalSpace E] in
/-- The shifted and unshifted powers span the same transforms. At order zero the
shifted weight is two, so one can subtract half of it to recover any pure power. -/
private theorem mulWeight_shiftedPowers_span (u : I → E →ₗ[ℂ] (X → ℂ)) (t : X → ℂ) :
    Submodule.span ℂ (range fun i : ℕ × I ↦ mulWeight (u i.2) (1 + t ^ i.1)) =
      Submodule.span ℂ (range fun i : ℕ × I ↦ mulWeight (u i.2) (t ^ i.1)) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨m, j⟩, rfl⟩
    change mulWeight (u j) (1 + t ^ m) ∈ Submodule.span ℂ _
    rw [map_add]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨(0, j), by simp⟩
    · exact Submodule.subset_span ⟨(m, j), rfl⟩
  · rintro _ ⟨⟨m, j⟩, rfl⟩
    have hm := @Submodule.subset_span ℂ _ _ _ _ (range fun i : ℕ × I ↦
      mulWeight (u i.2) (1 + t ^ i.1)) _ (mem_range_self (m, j))
    have h0 := @Submodule.subset_span ℂ _ _ _ _ (range fun i : ℕ × I ↦
      mulWeight (u i.2) (1 + t ^ i.1)) _ (mem_range_self (0, j))
    change mulWeight (u j) (t ^ m) ∈ Submodule.span ℂ _
    convert Submodule.sub_mem _ hm (Submodule.smul_mem _ (1 / 2 : ℂ) h0) using 1
    ext f x
    simp [mulWeight, add_mul]
    ring

/-- The degree-zero weight recovers the constant term in each shifted power. -/
private theorem generatesLp_powers (hp : 1 ≤ p) (u : I → E →ₗ[ℂ] (X → ℂ)) (t : X → ℂ)
    (h : GeneratesLpSeminorms μ p (fun i : ℕ × I ↦ (mulWeight (u i.2) (1 + t ^ i.1)))) :
    GeneratesLpSeminorms μ p (fun i : ℕ × I ↦ (mulWeight (u i.2) (t ^ i.1))) := by
  exact generatesLpSeminorms_of_span_eq hp _ _ (mulWeight_shiftedPowers_span u t) h

/-- Polynomial weights and powers span the same family. Taking the absolute
value of a polynomial preserves its Lᵖ norm after multiplication. -/
private theorem generatesLp_polynomials (hp : 1 ≤ p) (u : I → E →ₗ[ℂ] (X → ℂ))
    (t : X → ℂ) (ht : Measurable t)
    (h : GeneratesLpSeminorms μ p (fun i : ℕ × I ↦ (mulWeight (u i.2) (t ^ i.1)))) :
    GeneratesLpSeminorms μ p (fun i : Polynomial ℂ × I ↦
      (mulWeight (u i.2) (fun x ↦ (‖i.1.eval (t x)‖ : ℂ)))) := by
  let V (i : Polynomial ℂ × I) := mulWeight (u i.2) (fun x ↦ i.1.eval (t x))
  have hv : GeneratesLpSeminorms μ p (fun i ↦ V i) := by
    apply generatesLpSeminorms_of_span_eq hp _ _ _ h
    apply le_antisymm <;> apply Submodule.span_le.mpr
    · rintro _ ⟨⟨m, j⟩, rfl⟩
      exact Submodule.subset_span ⟨(Polynomial.X ^ m, j), by simp [V, Pi.pow_def]⟩
    · rintro _ ⟨⟨P, j⟩, rfl⟩
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ =>
        change V (P + Q, j) ∈ Submodule.span ℂ _
        convert Submodule.add_mem _ hP hQ using 1
        ext f x
        simp [V, mulWeight, add_mul]
      | monomial m c =>
        have hm := @Submodule.subset_span ℂ _ _ _ _ (range fun i : ℕ × I ↦
          mulWeight (u i.2) (t ^ i.1)) _ (mem_range_self (m, j))
        change V (Polynomial.monomial m c, j) ∈ Submodule.span ℂ _
        convert Submodule.smul_mem _ c hm using 1
        ext f x
        simp [V, mulWeight, mul_assoc]
  obtain ⟨hmem, Q, hQ, hval⟩ := hv
  have hbase (j : I) (f : E) : AEStronglyMeasurable (u j f) μ := by
    simpa [V, mulWeight, Pi.mul_def] using (hmem (1, j) f).aestronglyMeasurable
  have hmeas (i : Polynomial ℂ × I) (f : E) :
      AEStronglyMeasurable ((mulWeight (u i.2) (fun x ↦ (‖i.1.eval (t x)‖ : ℂ))) f) μ := by
    apply AEStronglyMeasurable.mul _ (hbase _ f)
    exact (Complex.continuous_ofReal.comp (continuous_norm.comp i.1.continuous)).measurable.comp ht
      |>.aestronglyMeasurable
  have heq (i : Polynomial ℂ × I) (f : E) : ∀ x, ‖V i f x‖ =
      ‖mulWeight (u i.2) (fun y ↦ (‖i.1.eval (t y)‖ : ℂ)) f x‖ := by
    intro x
    simp [V, mulWeight]
  refine ⟨fun i f ↦ (hmem i f).congr_norm (hmeas i f) ?_, Q, hQ, fun i f ↦ (hval i f).trans ?_⟩
  · exact .of_forall (heq i f)
  · exact eLpNorm_congr_norm_ae (hmem i f).aestronglyMeasurable (hmeas i f) (.of_forall (heq i f))

end WeightFamilies

section RadialDerivatives

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Iterating the first-order operator along a one-parameter subgroup
differentiates its translated orbit in the real parameter. -/
private theorem iteratedDeriv_orbit (a : LCATopologicalLie G) (m : ℕ)
    (f : bruhatSmoothSubmodule (G := G)) (x : G) (s : ℝ) :
    iteratedDeriv m (fun r : ℝ ↦ f.val (a (Multiplicative.ofAdd r) * x)) s =
      ((bruhatFirstOrder a ^ m) f).val (a (Multiplicative.ofAdd s) * x) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    have hd : deriv (fun r : ℝ ↦ f.val (a (Multiplicative.ofAdd r) * x)) =
        fun r : ℝ ↦ (bruhatFirstOrder a f).val (a (Multiplicative.ofAdd r) * x) := by
      funext r
      change _ = deriv (fun t : ℝ ↦ f.val ((a (Multiplicative.ofAdd r) * x) *
        a (Multiplicative.ofAdd t))) 0
      have h := deriv_comp_const_add (fun t : ℝ ↦ f.val (a (Multiplicative.ofAdd t) * x)) r 0
      have hadd (t : ℝ) : a (Multiplicative.ofAdd (r + t)) =
          a (Multiplicative.ofAdd r) * a (Multiplicative.ofAdd t) := map_mul a _ _
      simpa only [add_zero, hadd, mul_right_comm] using h.symm
    rw [iteratedDeriv_succ', hd, ih, pow_succ]
    rfl

/-- The exponential coordinate used by the norm section as a one-parameter subgroup. -/
private def positiveRealExpHom : Multiplicative ℝ →ₜ* ℝ≥0ˣ :=
  let e := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  { toFun := fun t ↦ e t.toAdd
    continuous_toFun := e.continuous
    map_one' := Units.ext (NNReal.eq Real.exp_zero)
    map_mul' := fun x y ↦ Units.ext (NNReal.eq (Real.exp_add x.toAdd y.toAdd)) }

private theorem positiveRealExpHom_apply (s : ℝ) :
    positiveRealExpHom (Multiplicative.ofAdd s) =
      Units.mk0 (Real.exp s).toNNReal (by positivity) :=
  Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos s).le).symm)

variable {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (γ : Fin d → LCATopologicalLie n.ker)
  (k : Subgroup G)

private def ideleClassProductDerivLinear (i : ℕ × (Fin d → ℕ)) :
    schwartzBruhatInvariantSubmodule k →ₗ[ℂ] (ℝ≥0ˣ × n.ker → ℂ) :=
  let j : n.ker →ₜ* G := ⟨n.ker.subtype, continuous_subtype_val⟩
  let D := bruhatDiffMonomial (fun l ↦ j.comp (γ l)) i.2
  let A := bruhatFirstOrder (τ.comp positiveRealExpHom) ^ i.1
  LinearMap.pi fun z ↦ (LinearMap.proj (τ z.1 * z.2.val)).comp
    (bruhatSmoothSubmodule.subtype.comp (A.comp (D.val.comp (smoothIncl.comp (schwartzBruhatInvariantSubmodule k).subtype))))

private theorem ideleClassProductWeightedDeriv_eq (i : ℕ × (Fin d → ℕ)) (w : ℝ → ℝ)
    (f : schwartzBruhatInvariantSubmodule k) (z : ℝ≥0ˣ × n.ker) :
    ideleClassProductWeightedDeriv n τ γ i.1 i.2 w f.val z =
      (w |Real.log (z.1.val : ℝ)| : ℂ) * ideleClassProductDerivLinear n τ γ k i f z := by
  let j : n.ker →ₜ* G := ⟨n.ker.subtype, continuous_subtype_val⟩
  let D := bruhatDiffMonomial (fun l ↦ j.comp (γ l)) i.2
  let g := D.val ⟨f.val, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f.val)⟩
  let a := τ.comp positiveRealExpHom
  have ha (s : ℝ) : a (Multiplicative.ofAdd s) =
      τ (Units.mk0 (Real.exp s).toNNReal (by positivity)) := congrArg τ (positiveRealExpHom_apply s)
  unfold ideleClassProductWeightedDeriv ideleClassWeightedDeriv
  apply congrArg (fun v : ℂ ↦ (w |Real.log (z.1.val : ℝ)| : ℂ) * v)
  change iteratedDeriv i.1 (fun s : ℝ ↦ g.val (τ (Units.mk0 (Real.exp s).toNNReal
    (by positivity)) * (τ z.1 * z.2.val))) 0 = ((bruhatFirstOrder a ^ i.1) g).val (τ z.1 * z.2.val)
  have h0 : a (Multiplicative.ofAdd (0 : ℝ)) = 1 := map_one a
  simpa only [h0, one_mul, ha] using
    iteratedDeriv_orbit a i.1 g (τ z.1 * z.2.val) 0

end RadialDerivatives

section LogWeights

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] {d : ℕ} {n : G →* ℝ≥0ˣ} {τ : ℝ≥0ˣ →ₜ* G}
  {γ : Fin d → LCATopologicalLie n.ker} {k : Subgroup G} [MeasurableSpace n.ker]
  {μ : Measure (ℝ≥0ˣ × n.ker)} {p : ℝ≥0∞}

private def absLogParameter {K : Type*} (z : ℝ≥0ˣ × K) : ℂ := (|Real.log (z.1.val : ℝ)| : ℝ)

omit [MeasurableSpace n.ker] in
private theorem ideleClass_power_mulWeight (i : ℕ × ℕ × (Fin d → ℕ))
    (f : schwartzBruhatInvariantSubmodule k) :
    ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun r ↦ r ^ i.1) f.val =
      mulWeight (ideleClassProductDerivLinear n τ γ k i.2) (absLogParameter ^ i.1) f := by
  funext z
  refine (ideleClassProductWeightedDeriv_eq n τ γ k i.2 _ f z).trans ?_
  simp [mulWeight, absLogParameter]

private theorem ideleClassStage_logPower (hp : 1 ≤ p)
    (h : GeneratesLpSeminorms μ p (fun i : ℕ × ℕ × (Fin d → ℕ) ↦
      fun f : schwartzBruhatInvariantSubmodule k ↦ ideleClassProductWeightedDeriv n τ γ
        i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val)) :
    GeneratesLpSeminorms μ p (fun i : ℕ × ℕ × (Fin d → ℕ) ↦
      fun f : schwartzBruhatInvariantSubmodule k ↦ ideleClassProductWeightedDeriv n τ γ
        i.2.1 i.2.2 (fun t ↦ t ^ i.1) f.val) := by
  have hshift (i : ℕ × ℕ × (Fin d → ℕ)) (f : schwartzBruhatInvariantSubmodule k) :
      ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun r ↦ 1 + r ^ i.1) f.val =
        mulWeight (ideleClassProductDerivLinear n τ γ k i.2) (1 + absLogParameter ^ i.1) f := by
    funext z
    refine (ideleClassProductWeightedDeriv_eq n τ γ k i.2 _ f z).trans ?_
    simp [mulWeight, absLogParameter]
  simp_rw [hshift] at h
  simp_rw [ideleClass_power_mulWeight]
  exact generatesLp_powers hp _ absLogParameter h

private theorem ideleClassStage_logPolynomial (hp : 1 ≤ p)
    (h : GeneratesLpSeminorms μ p (fun i : ℕ × ℕ × (Fin d → ℕ) ↦
      fun f : schwartzBruhatInvariantSubmodule k ↦ ideleClassProductWeightedDeriv n τ γ
        i.2.1 i.2.2 (fun t ↦ t ^ i.1) f.val)) :
    GeneratesLpSeminorms μ p (fun i : Polynomial ℂ × ℕ × (Fin d → ℕ) ↦
      fun f : schwartzBruhatInvariantSubmodule k ↦ ideleClassProductWeightedDeriv n τ γ
        i.2.1 i.2.2 (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by
  have ht : Measurable (absLogParameter (K := n.ker)) := by
    have hv : Measurable (Units.val : ℝ≥0ˣ → ℝ≥0) := MeasurableSpace.le_map_comap
    exact Complex.continuous_ofReal.measurable.comp (continuous_abs.measurable.comp
      (Real.measurable_log.comp (NNReal.continuous_coe.measurable.comp
        (hv.comp measurable_fst))))
  have hpoly (i : Polynomial ℂ × ℕ × (Fin d → ℕ)) (f : schwartzBruhatInvariantSubmodule k) :
      ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun r ↦ ‖i.1.eval (r : ℂ)‖) f.val =
        mulWeight (ideleClassProductDerivLinear n τ γ k i.2) (fun z ↦ (‖i.1.eval (absLogParameter z)‖ : ℂ)) f := by
    funext z
    exact ideleClassProductWeightedDeriv_eq n τ γ k i.2 _ f z
  simp_rw [ideleClass_power_mulWeight] at h
  simp_rw [hpoly]
  exact generatesLp_polynomials hp _ absLogParameter ht h

/-- Change the seminorms on each admissible stage using the same cofinal bound. -/
private theorem ideleClassStages_mono {G : Type*} [CommGroup G] [TopologicalSpace G]
    {P Q : Subgroup G → ℝ → Prop} (hPQ : ∀ k p, 1 ≤ p → P k p → Q k p)
    (h : ∃ k₀ : Subgroup G, IsCompact (k₀ : Set G) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup G, k ≤ k₀ → IsCompact (k : Set G) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → P k p) :
    ∃ k₀ : Subgroup G, IsCompact (k₀ : Set G) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup G, k ≤ k₀ → IsCompact (k : Set G) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → Q k p := by
  obtain ⟨k₀, hc, hg, hs⟩ := h
  exact ⟨k₀, hc, hg, fun k hk hck hgk p hp ↦ hPQ k p hp (hs k hk hck hgk p hp)⟩

end LogWeights

section OpenGood
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]
/-- For a compact subgroup, goodness is equivalent to the quotient being locally Euclidean. -/
private theorem good_iff_quotient (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    IsBruhatGoodSubgroup K ↔ IsLocallyEuclidean (G ⧸ K) := by
  have : IsClosed (K : Set G) := hK.isClosed
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator K hK.isClosed
  constructor
  · intro h
    exact isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
      (isCompactlyGeneratedGroup_of_continuousMulEquiv e.symm h.2.2)
  · intro h
    exact ⟨hK.isClosed, isOpen_lcaAnnihilator K hK, isCompactlyGeneratedGroup_of_continuousMulEquiv e
      (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean h)⟩

private theorem locallyEuclidean_openEmbedding (j : H →ₜ* G) (hj : IsOpenEmbedding j) :
    IsLocallyEuclidean H ↔ IsLocallyEuclidean G := by
  constructor
  · intro h
    obtain ⟨V, hV, hv⟩ := exists_nhds_one_of_isLocallyEuclidean h
    have hU : j '' V ∈ 𝓝 (1 : G) := map_one j ▸ hj.isOpenMap.image_mem_nhds hV
    apply isLocallyEuclidean_of_noSmallCyclicSubgroups hU
    intro x hx
    obtain ⟨y, _, heq⟩ := (show x ∈ j '' V by simpa using hx 1)
    subst x
    rw [hv y (fun n ↦ ?_), map_one]
    obtain ⟨z, hz, heq⟩ := hx n
    rwa [show y ^ n = z from hj.injective ((map_pow j y n).trans heq.symm)]
  · intro h
    obtain ⟨V, hV, hv⟩ := exists_nhds_one_of_isLocallyEuclidean h
    have hU : j ⁻¹' V ∈ 𝓝 (1 : H) := j.continuous.continuousAt.preimage_mem_nhds (by simpa using hV)
    apply isLocallyEuclidean_of_noSmallCyclicSubgroups hU
    intro x hx
    apply hj.injective
    rw [map_one]
    exact hv (j x) fun n ↦ map_pow j x n ▸ hx n

private def inducedQuotientHom (j : H →ₜ* G) (K : Subgroup G) :
    H ⧸ K.comap j.toMonoidHom →ₜ* G ⧸ K :=
  ⟨QuotientGroup.lift _ ((QuotientGroup.mk' K).comp j.toMonoidHom) (by intro x hx; exact (QuotientGroup.eq_one_iff _).mpr hx),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (QuotientGroup.continuous_mk.comp j.continuous)⟩

private theorem inducedQuotientHom_openEmbedding (j : H →ₜ* G) (hj : IsOpenEmbedding j) (K : Subgroup G) :
    IsOpenEmbedding (inducedQuotientHom j K) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (inducedQuotientHom j K).continuous
  · apply (QuotientGroup.injective_lift_iff (K.comap j.toMonoidHom) ((QuotientGroup.mk' K).comp j.toMonoidHom) (fun x hx ↦ (QuotientGroup.eq_one_iff _).mpr hx)).mpr
    ext x
    exact (QuotientGroup.eq_one_iff (N := K) (j x)).symm
  · intro s hs
    let q : H → H ⧸ K.comap j.toMonoidHom := QuotientGroup.mk
    have heq : inducedQuotientHom j K '' s = (QuotientGroup.mk : G → G ⧸ K) '' (j '' (q ⁻¹' s)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective z
        exact ⟨j u, ⟨u, hz, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨q u, hu, rfl⟩
    change IsOpen (inducedQuotientHom j K '' s)
    rw [heq]
    exact QuotientGroup.isOpenMap_coe _ (hj.isOpenMap _ (hs.preimage QuotientGroup.continuous_mk))

private theorem compact_comap_openEmbedding (j : H →ₜ* G) (hj : IsOpenEmbedding j) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) : IsCompact ((K.comap j.toMonoidHom : Subgroup H) : Set H) := by
  have hr : IsClosed (range j) := j.toMonoidHom.range.isClosed_of_isOpen hj.isOpen_range
  exact (show IsClosedEmbedding j from ⟨hj.isEmbedding, hr⟩).isCompact_preimage hK

/-- An open embedding detects the Bruhat goodness of a compact subgroup on its preimage. -/
theorem openEmbedding_good_comap (j : H →ₜ* G) (hj : IsOpenEmbedding j) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) : IsBruhatGoodSubgroup (K.comap j.toMonoidHom) ↔ IsBruhatGoodSubgroup K := by
  have hL := compact_comap_openEmbedding j hj K hK
  have : IsClosed (K : Set G) := hK.isClosed
  have : IsClosed ((K.comap j.toMonoidHom : Subgroup H) : Set H) := hL.isClosed
  rw [good_iff_quotient _ hL, good_iff_quotient _ hK]
  exact locallyEuclidean_openEmbedding _ (inducedQuotientHom_openEmbedding j hj K)

end OpenGood

section OpenStage
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

private theorem compactlyGenerated_of_split (n : H →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* H) (hτ : RightInverse τ n)
    (hk : IsCompact (n.ker : Set H)) : IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hne⟩ := exists_compact_mem_nhds (1 : H)
  let K := U ∪ (n.ker : Set H)
  let J := Subgroup.closure K
  have hK : K ∈ 𝓝 (1 : H) := Filter.mem_of_superset hne subset_union_left
  have hJ : IsOpen (J : Set H) := J.isOpen_of_mem_nhds (Filter.mem_of_superset hK Subgroup.subset_closure)
  have hker : n.ker ≤ J := subset_union_right.trans Subgroup.subset_closure
  have : ConnectedSpace ℝ≥0ˣ := (Real.expOrderIso.toHomeomorph.trans
    (Nonneg.unitsHomeomorphPos ℝ).symm).surjective.connectedSpace (by fun_prop)
  have ht (t : ℝ≥0ˣ) : τ t ∈ J := by
    have hpre : IsClopen (τ ⁻¹' (J : Set H)) := ⟨(J.isClosed_of_isOpen hJ).preimage τ.continuous, hJ.preimage τ.continuous⟩
    change t ∈ τ ⁻¹' (J : Set H)
    rw [hpre.eq_univ ⟨1, by change τ 1 ∈ J; rw [map_one]; exact J.one_mem⟩]
    exact mem_univ t
  refine ⟨K, hK, hU.union hk, top_unique (fun x _ ↦ ?_)⟩
  have hx : x / τ (n x) ∈ n.ker := by simp [MonoidHom.mem_ker, hτ (n x)]
  exact div_mul_cancel x (τ (n x)) ▸ J.mul_mem (hker hx) (ht _)

private def rangeEquivOpen (j : H →ₜ* G) (hj : IsOpenEmbedding j) : H ≃ₜ* j.toMonoidHom.range :=
  let e := j.toMonoidHom.ofInjective hj.injective
  { e, e.toEquiv.toHomeomorphOfIsInducing (hj.isEmbedding.codRestrict (j.toMonoidHom.range : Set G) (fun x ↦ ⟨x, rfl⟩)).isInducing with }

private def topSubgroupEquiv (H : Type*) [CommGroup H] [TopologicalSpace H] : (⊤ : Subgroup H) ≃ₜ* H :=
  { Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk _ }

private def quotientCongr (K : Subgroup H) (N : Subgroup G) (e : H ≃ₜ* G) (he : K.map e.toMulEquiv = N) :
    H ⧸ K ≃ₜ* G ⧸ N :=
  let φ := QuotientGroup.congr K N e.toMulEquiv he
  { φ with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.continuous)
    continuous_invFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp e.symm.continuous) }

private theorem stageInclusion_invariant (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) :
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f) ∈
      schwartzBruhatInvariantSubmodule (OrderDual.ofDual a.val.2) := by
  classical
  apply (mem_schwartzBruhatInvariantSubmodule_iff ..).mpr
  intro x u
  have hu : u.val ∈ a.val.1 := a.property.2.2.2 u.property
  change schwartzBruhatStageRealization a e f _ = schwartzBruhatStageRealization a e f _
  rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply]
  by_cases hx : x ∈ a.val.1
  · rw [dite_eq_left (a.val.1.mul_mem hx hu), dite_eq_left hx]
    apply congrArg (fun z : a.quotient ↦ f (e.equiv z).toAdd)
    let quotMap := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
    change quotMap (⟨x, hx⟩ * ⟨u.val, hu⟩) = quotMap ⟨x, hx⟩
    have he : quotMap ⟨u.val, hu⟩ = 1 := (a.quotient_mk_eq_one ⟨u.val, hu⟩).mpr u.property
    rw [map_mul, he, mul_one]
  · rw [dite_eq_right hx, dite_eq_right (fun h ↦ hx ((a.val.1.mul_mem_cancel_right hu).mp h))]

private theorem stageAverage_fixed (a : BruhatStructuralPair G) (f : SchwartzBruhat G)
    (hi : f ∈ schwartzBruhatInvariantSubmodule (OrderDual.ofDual a.val.2))
    (x : G) (hx : x ∈ a.val.1) : schwartzBruhatStageAverage a f x = f x := by
  classical
  unfold schwartzBruhatStageAverage
  simp only [ite_eq_left hx]
  let K := OrderDual.ofDual a.val.2
  have heq (u : K) : f (u.val * x) = f x := mul_comm u.val x ▸
    (mem_schwartzBruhatInvariantSubmodule_iff _ _).mp hi x u
  simp only [heq, integral_const, Measure.real]
  let : MeasurableSpace K := borel _
  let : BorelSpace K := ⟨rfl⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp (by
    rw [← lcaDualAnnihilator_annihilator K a.property.2.2.1.1]
    exact isCompact_lcaDualAnnihilator _ a.property.2.2.1.2.1)
  let V : TopologicalSpace.PositiveCompacts K := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  have he : Measure.haarMeasure V univ = 1 := Measure.haarMeasure_self (K₀ := V)
  change (Measure.haarMeasure V univ).toReal • f x = f x
  rw [he, ENNReal.toReal_one, one_smul]
end OpenStage

section FixedExtension
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

private def transportedPresentation {P Q : Type*} [CommGroup P] [TopologicalSpace P] [CommGroup Q] [TopologicalSpace Q]
    (φ : P ≃ₜ* Q) (e : ElementaryLCAPresentation P) : ElementaryLCAPresentation Q where
  realDim := e.realDim
  torusDim := e.torusDim
  latticeRank := e.latticeRank
  finiteFactor := e.finiteFactor
  equiv := φ.symm.trans e.equiv

/-- Matching quotient coordinates transfer a fixed stage by zero extension. The two averaging retractions give its induced topology. -/
private theorem fixedStage_extension_of_coordinates (j : H →ₜ* G)
    (a : BruhatStructuralPair H) (b : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (e' : ElementaryLCAPresentation b.quotient) (r : SchwartzBruhatStage e ≃L[ℂ] SchwartzBruhatStage e')
    (ha : ∀ x : H, x ∈ a.val.1)
    (he : ∀ v, (∀ x, schwartzBruhatStageRealization b e' (r v) (j x) = schwartzBruhatStageRealization a e v x) ∧
      ∀ y ∉ range j, schwartzBruhatStageRealization b e' (r v) y = 0) :
    ∃ E : schwartzBruhatInvariantSubmodule (OrderDual.ofDual a.val.2) →ₗ[ℂ] schwartzBruhatInvariantSubmodule (OrderDual.ofDual b.val.2),
      IsInducing E ∧ ∀ f, (∀ x, (E f).val (j x) = f.val x) ∧ ∀ y ∉ range j, (E f).val y = 0 := by
  let K := OrderDual.ofDual a.val.2
  let N := OrderDual.ofDual b.val.2
  let RA := (schwartzBruhatStage_average_retraction a e).choose
  have hRA := (schwartzBruhatStage_average_retraction a e).choose_spec
  let RB := (schwartzBruhatStage_average_retraction b e').choose
  have hRB := (schwartzBruhatStage_average_retraction b e').choose_spec
  let IA : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat H :=
    ⟨schwartzBruhatStageInclusion a e, continuous_schwartzBruhatStageInclusion a e⟩
  let IB : SchwartzBruhatStage e' →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion b e', continuous_schwartzBruhatStageInclusion b e'⟩
  have hID (f : schwartzBruhatInvariantSubmodule K) (x : H) : IA (RA f.val) x = f.val x :=
    (hRA.2 f.val x).trans (stageAverage_fixed a f.val f.property x (ha x))
  let E₀ := (IB.toLinearMap.comp (r.toLinearMap.comp RA.toLinearMap)).comp (schwartzBruhatInvariantSubmodule K).subtype
  let E := E₀.codRestrict (schwartzBruhatInvariantSubmodule N) (fun f ↦ stageInclusion_invariant b e' _)
  have hE : Continuous E := (IB.continuous.comp (r.continuous.comp (RA.continuous.comp continuous_subtype_val))).subtype_mk _
  have hF : Continuous (fun z : schwartzBruhatInvariantSubmodule N ↦ IA (r.symm (RB z.val))) :=
    IA.continuous.comp (r.symm.continuous.comp (RB.continuous.comp continuous_subtype_val))
  have hleft : (fun z : schwartzBruhatInvariantSubmodule N ↦ IA (r.symm (RB z.val))) ∘ E =
      (Subtype.val : schwartzBruhatInvariantSubmodule K → SchwartzBruhat H) := by
    funext f
    change IA (r.symm (RB (schwartzBruhatStageInclusion b e' (r (RA f.val))))) = f.val
    exact (congrArg (fun v ↦ IA (r.symm v)) (hRB.1 (r (RA f.val)))).trans ((congrArg IA (r.symm_apply_apply _)).trans (Subtype.ext (funext (hID f))))
  have hI : IsInducing ((fun z : schwartzBruhatInvariantSubmodule N ↦ IA (r.symm (RB z.val))) ∘ E) :=
    Eq.mpr (congrArg IsInducing hleft) IsInducing.subtypeVal
  exact ⟨E, IsInducing.of_comp hE hF hI, fun f ↦
    ⟨fun x ↦ ((he (RA f.val)).1 x).trans (hID f x), (he (RA f.val)).2⟩⟩

/-- Realize both fixed stages in the same elementary coordinates, extending the local functions by zero off the open subgroup. -/
private theorem fixedStage_extension (j : H →ₜ* G) (hj : IsOpenEmbedding j)
    (hc : IsCompactlyGeneratedGroup H) (K : Subgroup H) (hk : IsCompact (K : Set H)) (hg : IsBruhatGoodSubgroup K) :
    ∃ E : schwartzBruhatInvariantSubmodule K →ₗ[ℂ] schwartzBruhatInvariantSubmodule (K.map j.toMonoidHom),
      IsInducing E ∧ ∀ f, (∀ x, (E f).val (j x) = f.val x) ∧
        ∀ y ∉ range j, (E f).val y = 0 := by
  classical
  let N := K.map j.toMonoidHom
  let J := j.toMonoidHom.range
  let ξ := rangeEquivOpen j hj
  let a : BruhatStructuralPair H := ⟨(⊤, OrderDual.toDual K), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv (topSubgroupEquiv H).symm hc, hg, le_top⟩
  have hN : IsBruhatGoodSubgroup N := by
    apply (openEmbedding_good_comap j hj N (hk.image j.continuous)).mp
    simpa only [N, Subgroup.comap_map_eq_self_of_injective hj.injective] using hg
  let b : BruhatStructuralPair G := ⟨(J, OrderDual.toDual N), hj.isOpen_range,
    isCompactlyGeneratedGroup_of_continuousMulEquiv ξ hc, hN, Subgroup.map_le_range j.toMonoidHom K⟩
  let σ : a.val.1 ≃ₜ* b.val.1 := (topSubgroupEquiv H).trans ξ
  let A := K.comap a.val.1.subtype
  let B := N.comap b.val.1.subtype
  have heq : A.map σ.toMulEquiv = B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.val, hz, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨⟨z, Subgroup.mem_top _⟩, hz, Subtype.ext he⟩
  let φ : a.quotient ≃ₜ* b.quotient := quotientCongr A B σ heq
  let e := Classical.choice a.elementary
  let e' := transportedPresentation φ e
  apply fixedStage_extension_of_coordinates j a b e e' (ContinuousLinearEquiv.refl ℂ (SchwartzBruhatStage e))
    (fun _ ↦ Subgroup.mem_top _)
  intro v
  constructor
  · intro x
    rw [schwartzBruhatStageRealization_apply, schwartzBruhatStageRealization_apply,
      dite_eq_left (show j x ∈ b.val.1 from ⟨x, rfl⟩), dite_eq_left (show x ∈ a.val.1 from Subgroup.mem_top _)]
    let z : a.val.1 := ⟨x, Subgroup.mem_top _⟩
    exact congrArg (fun u : a.quotient ↦ v (e.equiv u).toAdd) (φ.symm_apply_apply (QuotientGroup.mk z))
  · intro y hy
    have hnot : y ∉ b.val.1 := hy
    exact (schwartzBruhatStageRealization_apply b e' v y).trans (dite_eq_right hnot)
end FixedExtension

section OpenLie
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

private def directionOperator (a : LCATopologicalLie H) : bruhatDiffDegreeOneReal (G := H) :=
  ⟨bruhatFirstOrder a, Submodule.subset_span (mem_range_self a)⟩

private theorem directionOperator_bijective : Bijective (directionOperator (H := H)) := by
  constructor
  · intro a b hab
    obtain ⟨σ, _, _, hσ⟩ := bruhatDiffDegreeOne_frequency (G := H)
    apply ContinuousMonoidHom.ext
    intro t
    apply pontryaginDual_pairing_separates.1
    funext χ
    have ha := hσ a (directionOperator a) rfl χ t.toAdd
    have hb := hσ b (directionOperator b) rfl χ t.toAdd
    rw [hab] at ha
    exact ha.symm.trans hb
  · intro D
    obtain ⟨a, ha⟩ := (mem_bruhatDiffDegreeOneReal_iff _).mp D.property
    exact ⟨a, Subtype.ext ha.symm⟩

private theorem openEmbedding_lie_bijective (j : H →ₜ* G) (hj : IsOpenEmbedding j) :
    Bijective (fun a : LCATopologicalLie H ↦ j.comp a) := by
  constructor
  · intro a b h
    exact ContinuousMonoidHom.ext fun t ↦ hj.injective (congrArg (fun f : LCATopologicalLie G ↦ f t) h)
  · intro a
    let ξ := rangeEquivOpen j hj
    let J := j.toMonoidHom.range
    have hJ : IsClopen (J : Set G) := ⟨J.isClosed_of_isOpen hj.isOpen_range, hj.isOpen_range⟩
    have : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
    have hmem (t : Multiplicative ℝ) : a t ∈ J := hJ.connectedComponent_subset J.one_mem
      ((isPreconnected_range a.continuous).subset_connectedComponent ⟨1, map_one a⟩ ⟨t, rfl⟩)
    let ar : LCATopologicalLie J := ⟨a.toMonoidHom.codRestrict J hmem, a.continuous.subtype_mk _⟩
    refine ⟨(ξ.symm : J →ₜ* H).comp ar, ContinuousMonoidHom.ext fun t ↦ ?_⟩
    exact congrArg Subtype.val (ξ.apply_symm_apply (ar t))

/-- An open embedding induces an isomorphism of first-order operator spaces because every one-parameter subgroup stays in the open image. -/
private theorem directionOperator_openEquiv (j : H →ₜ* G) (hj : IsOpenEmbedding j) :
    ∃ T : bruhatDiffDegreeOneReal (G := H) ≃ₗ[ℝ] bruhatDiffDegreeOneReal (G := G),
      ∀ a, T (directionOperator a) = directionOperator (j.comp a) := by
  let φH := Equiv.ofBijective (directionOperator (H := H)) directionOperator_bijective
  let φG := Equiv.ofBijective (directionOperator (H := G)) directionOperator_bijective
  let T := φH.symm.trans ((Equiv.ofBijective _ (openEmbedding_lie_bijective j hj)).trans φG)
  have h (a : LCATopologicalLie H) : T (directionOperator a) = directionOperator (j.comp a) := by
    change directionOperator (j.comp (φH.symm (φH a))) = _
    rw [φH.symm_apply_apply]
  let M : bruhatDiffDegreeOneReal (G := H) →ₗ[ℝ] bruhatDiffDegreeOneReal (G := G) :=
    { toFun := T
      map_add' := fun D E ↦ by
        obtain ⟨a, rfl⟩ := directionOperator_bijective.2 D
        obtain ⟨b, rfl⟩ := directionOperator_bijective.2 E
        have he : directionOperator a + directionOperator b = directionOperator (a*b) :=
          Subtype.ext (bruhatFirstOrder_mul a b).symm
        rw [he, h, h, h]
        have hab : j.comp (a * b) = j.comp a * j.comp b := ContinuousMonoidHom.ext fun t ↦ j.map_mul (a t) (b t)
        exact Subtype.ext (hab ▸ bruhatFirstOrder_mul _ _)
      map_smul' := fun c D ↦ by
        obtain ⟨a, rfl⟩ := directionOperator_bijective.2 D
        let s : LCATopologicalLie (Multiplicative ℝ) :=
          ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative, continuous_const_mul c⟩
        have he : c • directionOperator a = directionOperator (a.comp s) :=
          Subtype.ext (bruhatFirstOrder_scale a c).symm
        rw [he, h, h]
        exact Subtype.ext (bruhatFirstOrder_scale (j.comp a) c) }
  exact ⟨LinearEquiv.ofBijective M T.bijective, h⟩

private theorem openEmbedding_transport_basis {d : ℕ} (j : H →ₜ* G) (hj : IsOpenEmbedding j)
    (γ : Fin d → LCATopologicalLie H) (hγ : LinearIndependent ℝ (fun i ↦ bruhatFirstOrder (γ i)))
    (hs : Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (γ i)) = bruhatDiffDegreeOneReal) :
    LinearIndependent ℝ (fun i ↦ bruhatFirstOrder (j.comp (γ i))) ∧
      Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (j.comp (γ i))) = bruhatDiffDegreeOneReal := by
  let S := bruhatDiffDegreeOneReal (G := H)
  let R := bruhatDiffDegreeOneReal (G := G)
  let h := directionOperator_openEquiv j hj
  let M := h.choose
  let u (i : Fin d) := directionOperator (γ i)
  have hu : LinearIndependent ℝ u := LinearIndependent.of_comp S.subtype hγ
  have hv : Submodule.span ℝ (range u) = ⊤ := by
    apply Submodule.map_injective_of_injective S.subtype_injective
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    exact hs
  have heq : (fun i ↦ bruhatFirstOrder (j.comp (γ i))) = R.subtype ∘ M.toLinearMap ∘ u :=
    funext fun i ↦ congrArg Subtype.val (h.choose_spec (γ i)).symm
  rw [heq]
  refine ⟨(hu.map' M.toLinearMap M.ker).map' R.subtype R.ker_subtype, ?_⟩
  rw [Set.range_comp, Set.range_comp, ← Submodule.map_span, ← Submodule.map_span, hv,
    Submodule.map_top, M.range, Submodule.map_top, Submodule.range_subtype]
end OpenLie

section ExtensionDerivatives
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H]

private def ExtendsByZero {X Y : Type*} (j : X → Y) (f : X → ℂ) (g : Y → ℂ) : Prop :=
  (∀ x, g (j x) = f x) ∧ ∀ y ∉ range j, g y = 0

private theorem extends_firstOrder (j : H →ₜ* G) (a : LCATopologicalLie H) {f : bruhatSmoothSubmodule (G := H)}
    {g : bruhatSmoothSubmodule (G := G)} (h : ExtendsByZero j f.val g.val) :
    ExtendsByZero j (bruhatFirstOrder a f).val (bruhatFirstOrder (j.comp a) g).val := by
  constructor
  · intro x
    change deriv (fun t : ℝ ↦ g.val (j x * j (a (Multiplicative.ofAdd t)))) 0 = _
    simp only [← map_mul, h.1]
    rfl
  · intro y hy
    have heq (t : ℝ) : g.val (y * j (a (Multiplicative.ofAdd t))) = 0 := by
      apply h.2
      intro hmem
      exact hy ((j.toMonoidHom.range.mul_mem_cancel_right (show j (a _) ∈ j.toMonoidHom.range from ⟨_, rfl⟩)).mp hmem)
    change deriv (fun t : ℝ ↦ g.val (y * j (a (Multiplicative.ofAdd t)))) 0 = 0
    simp only [heq, deriv_const]

private theorem extends_word (j : H →ₜ* G) (v : List (LCATopologicalLie H)) (f : bruhatSmoothSubmodule (G := H))
    (g : bruhatSmoothSubmodule (G := G)) (h : ExtendsByZero j f.val g.val) :
    ExtendsByZero j ((bruhatDiffWord v).val f).val ((bruhatDiffWord (v.map (j.comp ·))).val g).val := by
  induction v generalizing f g with
  | nil => simpa [bruhatDiffWord] using h
  | cons a v ih =>
    have h' := ih (bruhatFirstOrder a f) (bruhatFirstOrder (j.comp a) g) (extends_firstOrder j a h)
    simpa only [List.map_cons, bruhatDiffWord, List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using! h'

private def normKernelMap (j : H →ₜ* G) (n : H →* ℝ≥0ˣ) (m : G →* ℝ≥0ˣ) (hj : ∀ x, m (j x) = n x) :
    n.ker →ₜ* m.ker :=
  ⟨(j.toMonoidHom.comp n.ker.subtype).codRestrict _ (fun x ↦ (hj x.val).trans x.property),
    (j.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem normKernelMap_openEmbedding (j : H →ₜ* G) (hj : IsOpenEmbedding j)
    (n : H →* ℝ≥0ˣ) (m : G →* ℝ≥0ˣ) (hn : ∀ x, m (j x) = n x) :
    IsOpenEmbedding (normKernelMap j n m hn) := by
  let k := normKernelMap j n m hn
  have he : IsEmbedding k :=
    (hj.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict (m.ker : Set G) (fun x ↦ (hn x.val).trans x.property)
  have hr : range k = Subtype.val ⁻¹' range j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.val, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (hn x).symm.trans (hx ▸ y.property)⟩, Subtype.ext hx⟩
  exact ⟨he, hr ▸ hj.isOpen_range.preimage continuous_subtype_val⟩

/-- Zero extension intertwines every compact-direction derivative and every radial derivative in the product coordinates. -/
private theorem extends_productWeightedDeriv (j : H →ₜ* G) (n : H →* ℝ≥0ˣ) (m : G →* ℝ≥0ˣ)
    (hj : ∀ x, m (j x) = n x) (τ : ℝ≥0ˣ →ₜ* H) {d : ℕ} (γ : Fin d → LCATopologicalLie n.ker)
    (r : ℕ) (α : Fin d → ℕ) (w : ℝ → ℝ) (f : SchwartzBruhat H) (g : SchwartzBruhat G)
    (h : ExtendsByZero j (f : H → ℂ) (g : G → ℂ)) :
    ExtendsByZero (Prod.map id (normKernelMap j n m hj)) (ideleClassProductWeightedDeriv n τ γ r α w f)
      (ideleClassProductWeightedDeriv m (j.comp τ) (fun i ↦ (normKernelMap j n m hj).comp (γ i)) r α w g) := by
  let a (i : Fin d) := (⟨n.ker.subtype, continuous_subtype_val⟩ : n.ker →ₜ* H).comp (γ i)
  let v := (List.finRange d).flatMap fun i ↦ List.replicate (α i) (a i)
  let f' : bruhatSmoothSubmodule (G := H) := ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  let g' : bruhatSmoothSubmodule (G := G) := ⟨g, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth g)⟩
  let F := ((bruhatDiffWord v).val f').val
  let P := ((bruhatDiffWord (v.map (j.comp ·))).val g').val
  have hD : ExtendsByZero j F P := extends_word j v f' g' h
  let k := normKernelMap j n m hj
  let b (i : Fin d) := (⟨m.ker.subtype, continuous_subtype_val⟩ : m.ker →ₜ* G).comp (k.comp (γ i))
  have hword : bruhatDiffMonomial b α = bruhatDiffWord (v.map (j.comp ·)) := by
    simp only [v, List.map_flatMap, List.map_replicate]
    rfl
  have hval (t : ℝ≥0ˣ) (y : m.ker) : ideleClassProductWeightedDeriv m (j.comp τ) (fun i ↦ k.comp (γ i)) r α w g (t,y) =
      (w |Real.log (t.val : ℝ)| : ℂ) * iteratedDeriv r (fun s : ℝ ↦ P (j (τ (positiveRealExpHom (Multiplicative.ofAdd s))) * (j (τ t) * y.val))) 0 := by
    change _ * iteratedDeriv r (fun s : ℝ ↦ ((bruhatDiffMonomial b α).val g').val _) 0 = _
    rw [hword]
    simp only [positiveRealExpHom_apply]
    rfl
  constructor
  · rintro ⟨t,y⟩
    rw [show Prod.map id k (t,y) = (t,k y) from rfl, hval]
    change _ * iteratedDeriv r (fun s : ℝ ↦ P (j _ * (j _ * j y.val))) 0 = _
    simp only [← map_mul, hD.1, positiveRealExpHom_apply]
    rfl
  · rintro ⟨t,y⟩ hy
    rw [hval]
    have hnot : y.val ∉ j.toMonoidHom.range := by
      rintro ⟨x, hx⟩
      have hx' : x ∈ n.ker := (hj x).symm.trans (hx ▸ y.property)
      exact hy ⟨(t, ⟨x, hx'⟩), Prod.ext rfl (Subtype.ext hx)⟩
    have hz (s : ℝ) : P (j (τ (positiveRealExpHom (Multiplicative.ofAdd s))) * (j (τ t) * y.val)) = 0 :=
      hD.2 _ fun h ↦ hnot ((j.toMonoidHom.range.mul_mem_cancel_left ⟨_, rfl⟩).mp
        ((j.toMonoidHom.range.mul_mem_cancel_left ⟨_, rfl⟩).mp h))
    simp [hz]
end ExtensionDerivatives

section OpenMeasure
variable {T X Y : Type*} [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace Y]
  {E F I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
private theorem generatesLp_smul_measure {μ : Measure X} {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    {u : I → E → X → ℂ} (c : ℝ≥0) (hc : c ≠ 0) (h : GeneratesLpSeminorms μ p u) :
    GeneratesLpSeminorms (c • μ) p u := by
  obtain ⟨hm, P, hP, hval⟩ := h
  let a := c ^ (1 / p).toReal
  have ha : 0 < a := NNReal.rpow_pos (pos_iff_ne_zero.mpr hc)
  let Q (i : I) := a • P i
  refine ⟨fun i f ↦ (hm i f).smul_measure ENNReal.coe_ne_top, Q, hP.congr ?_ ?_, fun i f ↦ ?_⟩
  · refine Seminorm.IsBounded.of_real (fun i ↦ ⟨{i}, (a : ℝ), fun f ↦ ?_⟩)
    simp only [Q, Finset.sup_singleton, LinearMap.id_apply]
    rfl
  · refine Seminorm.IsBounded.of_real (fun i ↦ ⟨{i}, ((a : ℝ)⁻¹), fun f ↦ ?_⟩)
    simp only [Finset.sup_singleton, LinearMap.id_apply]
    change P i f ≤ (a : ℝ)⁻¹ * ((a : ℝ) * P i f)
    rw [inv_mul_cancel_left₀ (show (a : ℝ) ≠ 0 from by exact_mod_cast ha.ne')]
  · change ENNReal.ofReal ((a : ℝ) * P i f) = eLpNorm _ _ ((c : ℝ≥0∞) • μ)
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top hp hp', ENNReal.ofReal_mul a.coe_nonneg,
      hval, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
    rfl

/-- An inducing linear map pulls a generating family back when the transforms extend by zero across a measure-preserving embedding onto the range. -/
private theorem generatesLp_extendByZero {μ : Measure X} {ν : Measure Y}
    (j : X → Y) (hj : Measurable j) (hm : μ.map j = ν.restrict (range j)) (p : ℝ≥0∞)
    (L : E →ₗ[ℂ] F) (hL : IsInducing L) (u : I → E → X → ℂ) (v : I → F → Y → ℂ)
    (h : ∀ i f, ExtendsByZero j (u i f) (v i (L f))) (hv : GeneratesLpSeminorms ν p v) :
    GeneratesLpSeminorms μ p u := by
  obtain ⟨hmv, P, hP, hval⟩ := hv
  have hn (i : I) (f : E) : eLpNorm (u i f) p μ = eLpNorm (v i (L f)) p ν := by
    have hv := (hmv i (L f)).aestronglyMeasurable
    have heq : u i f = v i (L f) ∘ j := (funext (h i f).1).symm
    rw [heq, ← eLpNorm_map_measure (hm ▸ hv.restrict) hj.aemeasurable, hm]
    apply eLpNorm_restrict_eq_of_support_subset hv
    exact fun x hx ↦ by_contra (fun h' ↦ hx ((h i f).2 x h'))
  exact ⟨fun i f ↦ (hn i f).trans_lt (hmv i _).eLpNorm_lt_top,
    (fun i ↦ (P i).comp L), hL.withSeminorms hP, fun i f ↦ (hval i _).trans (hn i f).symm⟩

private theorem prod_map_comap_open {H G : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
    (j : H →ₜ* G) (hj : IsOpenEmbedding j) (dt : Measure T) [SFinite dt] (ν : Measure G) [ν.IsHaarMeasure] :
    (dt.prod (ν.comap j)).map (Prod.map id j) = (dt.prod ν).restrict (range (Prod.map (id : T → T) j)) := by
  have : (ν.comap j).IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := (inferInstance : MeasurableMul G)) ν (f := j.toMonoidHom) hj
  have hr : range (Prod.map (id : T → T) j) = univ ×ˢ range j := by
    ext ⟨t, y⟩
    constructor
    · rintro ⟨⟨s,x⟩, he⟩
      exact ⟨trivial, ⟨x, congrArg Prod.snd he⟩⟩
    · rintro ⟨_, x, hx⟩
      exact ⟨(t,x), Prod.ext rfl hx⟩
  rw [← Measure.map_prod_map dt (ν.comap j) measurable_id hj.continuous.measurable,
    Measure.map_id, hj.measurableEmbedding.map_comap, hr, ← Measure.prod_restrict, Measure.restrict_univ]
end OpenMeasure

section OpenStageTransfer
variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [LocallyCompactSpace H] {d : ℕ}

private def weightedFixedStages (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) [MeasurableSpace n.ker] (ν : Measure n.ker) :=
  ∃ k₀ : Subgroup G, IsCompact (k₀ : Set G) ∧ IsBruhatGoodSubgroup k₀ ∧
    ∀ k : Subgroup G, k ≤ k₀ → IsCompact (k : Set G) → IsBruhatGoodSubgroup k →
      ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod ν) (ENNReal.ofReal p)
        (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
          ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val)

private theorem generatesLp_change_compactHaar {K : Type*} [CommGroup K] [TopologicalSpace K]
    [IsTopologicalGroup K] [T2Space K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    {X E I : Type*} [MeasurableSpace X] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (dt : Measure X) (μ ν : Measure K) [μ.IsHaarMeasure] [ν.IsHaarMeasure]
    (p : ℝ) (hp : 1 ≤ p) (v : I → E → X × K → ℂ) (h : GeneratesLpSeminorms (dt.prod ν) (ENNReal.ofReal p) v) :
    GeneratesLpSeminorms (dt.prod μ) (ENNReal.ofReal p) v := by
  let c := μ.haarScalarFactor ν
  have hμ : μ = c • ν := Measure.isMulInvariant_eq_smul_of_compactSpace μ ν
  have he : dt.prod μ = c • dt.prod ν := (congrArg (dt.prod ·) hμ).trans (Measure.prod_smul_right ..)
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  exact he ▸ generatesLp_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans_le hp))
    ENNReal.ofReal_ne_top c hc h

/-- A fixed stage inherits the global Lᵖ topology by zero extension and uniqueness of Haar measure on the compact norm-one subgroup. -/
private theorem openEmbedding_weightedStage (j : H →ₜ* G) (hj : IsOpenEmbedding j)
    (n : H →* ℝ≥0ˣ) (m : G →* ℝ≥0ˣ) (hn : ∀ x, m (j x) = n x)
    [CompactSpace n.ker] [CompactSpace m.ker] [MeasurableSpace n.ker] [BorelSpace n.ker]
    [MeasurableSpace m.ker] [BorelSpace m.ker] (μ : Measure n.ker) [μ.IsHaarMeasure]
    (ν : Measure m.ker) [ν.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* H) (hτ : RightInverse τ n)
    (γ : Fin d → LCATopologicalLie n.ker)
    (K : Subgroup H) (hcomp : IsCompact (K : Set H)) (hgood : IsBruhatGoodSubgroup K)
    (p : ℝ) (hp : 1 ≤ p)
    (hg : GeneratesLpSeminorms (positiveRealHaar.prod ν) (ENNReal.ofReal p)
      (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule (K.map j.toMonoidHom) ↦
        ideleClassProductWeightedDeriv m (j.comp τ) (fun z ↦ (normKernelMap j n m hn).comp (γ z)) i.2.1 i.2.2
          (fun t ↦ 1 + t ^ i.1) f.val)) :
    GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
      (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule K ↦
        ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val) := by
  let k := normKernelMap j n m hn
  have hk : IsOpenEmbedding k := normKernelMap_openEmbedding j hj n m hn
  let μ' := ν.comap k
  have : μ'.IsHaarMeasure := Measure.IsHaarMeasure.comap (mH := (inferInstance : MeasurableMul m.ker)) ν (f := k.toMonoidHom) hk
  have : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let hE := fixedStage_extension j hj (compactlyGenerated_of_split n τ hτ (isCompact_iff_compactSpace.mpr inferInstance)) K hcomp hgood
  let E := hE.choose
  have hE' := hE.choose_spec
  have fext (i : ℕ × ℕ × (Fin d → ℕ)) (f : schwartzBruhatInvariantSubmodule K) :=
    extends_productWeightedDeriv j n m hn τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val (E f).val (hE'.2 f)
  have htransfer := generatesLp_extendByZero (Prod.map id k) (measurable_id.prodMap hk.continuous.measurable)
    (prod_map_comap_open k hk positiveRealHaar ν) (ENNReal.ofReal p) E hE'.1 _ _ fext hg
  exact generatesLp_change_compactHaar positiveRealHaar μ μ' p hp _ htransfer

private theorem openEmbedding_weightedStages (j : H →ₜ* G) (hj : IsOpenEmbedding j)
    (n : H →* ℝ≥0ˣ) (m : G →* ℝ≥0ˣ) (hn : ∀ x, m (j x) = n x)
    [CompactSpace n.ker] [CompactSpace m.ker] [MeasurableSpace n.ker] [BorelSpace n.ker]
    [MeasurableSpace m.ker] [BorelSpace m.ker] (μ : Measure n.ker) [μ.IsHaarMeasure]
    (ν : Measure m.ker) [ν.IsHaarMeasure] (τ : ℝ≥0ˣ →ₜ* H) (hτ : RightInverse τ n)
    (γ : Fin d → LCATopologicalLie n.ker)
    (hγ : LinearIndependent ℝ (fun i ↦ bruhatFirstOrder (γ i)))
    (hs : Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (γ i)) = bruhatDiffDegreeOneReal)
    (hglob : ∀ τ' : ℝ≥0ˣ →ₜ* G, RightInverse τ' m → ∀ γ' : Fin d → LCATopologicalLie m.ker,
      LinearIndependent ℝ (fun i ↦ bruhatFirstOrder (γ' i)) →
      Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (γ' i)) = bruhatDiffDegreeOneReal →
      weightedFixedStages m τ' γ' ν) : weightedFixedStages n τ γ μ := by
  let k := normKernelMap j n m hn
  have hk : IsOpenEmbedding k := normKernelMap_openEmbedding j hj n m hn
  have hb := openEmbedding_transport_basis k hk γ hγ hs
  let h := hglob (j.comp τ) (fun t ↦ (hn _).trans (hτ t)) (fun i ↦ k.comp (γ i)) hb.1 hb.2
  let Kg := h.choose
  have hK := h.choose_spec
  refine ⟨Kg.comap j.toMonoidHom, compact_comap_openEmbedding j hj Kg hK.1,
    (openEmbedding_good_comap j hj Kg hK.1).mpr hK.2.1, fun K hle hcomp hgood p hp ↦ ?_⟩
  let N := K.map j.toMonoidHom
  have hN : IsBruhatGoodSubgroup N := by
    apply (openEmbedding_good_comap j hj N (hcomp.image j.continuous)).mp
    simpa only [N, Subgroup.comap_map_eq_self_of_injective hj.injective] using hgood
  have hglob' := hK.2.2 N ((Subgroup.map_le_iff_le_comap).mpr hle) (hcomp.image j.continuous) hN p hp
  exact openEmbedding_weightedStage j hj n m hn μ ν τ hτ γ K hcomp hgood p hp hglob'
end OpenStageTransfer

section ComponentDirections

/-- One-parameter subgroups form a real vector space. Addition is pointwise multiplication and
scalar multiplication rescales the parameter. -/
private abbrev OneParameterSpace (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :=
  Additive (LCATopologicalLie G)

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

private def timeScale (c : ℝ) : LCATopologicalLie (Multiplicative ℝ) :=
  ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative, continuous_const_mul c⟩

private local instance : SMul ℝ (OneParameterSpace G) := ⟨fun c a ↦ Additive.ofMul (a.toMul.comp (timeScale c))⟩
private local instance : Module ℝ (OneParameterSpace G) where
  one_smul a := ContinuousMonoidHom.ext fun t ↦ congrArg a.toMul (one_mul t.toAdd)
  mul_smul c d a := by
    apply ContinuousMonoidHom.ext
    intro t
    apply congrArg a.toMul
    change (c * d) * t.toAdd = d * (c * t.toAdd)
    ring
  smul_zero c := rfl
  smul_add c a b := rfl
  add_smul c d a := by
    apply ContinuousMonoidHom.ext
    intro t
    have h : timeScale (c + d) t = timeScale c t * timeScale d t := by
      change (c + d) * t.toAdd = c * t.toAdd + d * t.toAdd
      exact add_mul ..
    exact (congrArg a.toMul h).trans (map_mul a.toMul _ _)
  zero_smul a := by
    apply ContinuousMonoidHom.ext
    intro t
    have h : timeScale 0 t = 1 := by
      change 0 * t.toAdd = 0
      exact zero_mul _
    exact (congrArg a.toMul h).trans (map_one a.toMul)

private def oneParameterMap (j : G →ₜ* H) : OneParameterSpace G →ₗ[ℝ] OneParameterSpace H where
  toFun a := Additive.ofMul (j.comp a.toMul)
  map_add' a b := ContinuousMonoidHom.ext fun t ↦ map_mul j (a.toMul t) (b.toMul t)
  map_smul' _ _ := rfl

/-- A based lift of a real one-parameter subgroup is multiplicative by uniqueness of lifts on
the real plane. -/
private theorem oneParameterMap_surjective_of_covering (q : G →ₜ* H) (hq : IsCoveringMap q) :
    Surjective (oneParameterMap q) := by
  intro a
  let f : C(ℝ, H) := ⟨fun t ↦ a.toMul (Multiplicative.ofAdd t), a.toMul.continuous⟩
  obtain ⟨g, ⟨hg0, hg⟩, _⟩ := hq.existsUnique_continuousMap_lifts f 0 1 ((map_one q).trans (map_one a.toMul).symm)
  have hv (t : ℝ) : q (g t) = a.toMul (Multiplicative.ofAdd t) := congrFun hg t
  have hmul (s t : ℝ) : g (s + t) = g s * g t := by
    let l (p : ℝ × ℝ) := g (p.1 + p.2)
    let r (p : ℝ × ℝ) := g p.1 * g p.2
    have h := hq.eq_of_comp_eq (g₁ := l) (g₂ := r) (g.continuous.comp (continuous_fst.add continuous_snd))
      ((g.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd))
      (funext fun p ↦ (hv _).trans ((map_mul a.toMul _ _).trans ((map_mul q _ _).trans (congrArg₂ (· * ·) (hv p.1) (hv p.2))).symm))
      (0, 0) (show g (0 + 0) = g 0 * g 0 by rw [zero_add, hg0, one_mul])
    exact congrFun h (s, t)
  let lift : LCATopologicalLie G :=
    { toFun t := g t.toAdd, map_one' := hg0, map_mul' s t := hmul s.toAdd t.toAdd, continuous_toFun := g.continuous }
  exact ⟨Additive.ofMul lift, ContinuousMonoidHom.ext fun t ↦ hv t.toAdd⟩

section ClassVelocity

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V]

private def lieCurve (j : G →* V) (a : OneParameterSpace G) (t : ℝ) : V := j (a.toMul (Multiplicative.ofAdd t))
private theorem lieCurve_zero (j : G →* V) (a : OneParameterSpace G) : lieCurve j a 0 = 1 :=
  (congrArg j (map_one a.toMul)).trans (map_one j)
private theorem lieCurve_add (j : G →* V) (a : OneParameterSpace G) (s t : ℝ) :
    lieCurve j a (s + t) = lieCurve j a s * lieCurve j a t :=
  (congrArg j (map_mul a.toMul _ _)).trans (map_mul j _ _)

private def velocityMap (j : G →* V) (hd : ∀ a, DifferentiableAt ℝ (lieCurve j a) 0) :
    OneParameterSpace G →ₗ[ℝ] V where
  toFun a := deriv (lieCurve j a) 0
  map_add' a b := by
    have he (t : ℝ) : lieCurve j (a + b) t = lieCurve j a t * lieCurve j b t := map_mul j _ _
    rw [funext he, deriv_fun_mul (hd a) (hd b), lieCurve_zero, lieCurve_zero, mul_one, one_mul]
  map_smul' c a := by
    change deriv (fun t : ℝ ↦ lieCurve j a (c * t)) 0 = c • deriv (lieCurve j a) 0
    simpa only [mul_zero] using deriv_comp_mul_left c (lieCurve j a) 0

/-- Translation gives the derivative at every time from the derivative at zero. Zero velocity
therefore makes the whole curve constant. -/
private theorem velocityMap_injective (j : G →* V) (hd : ∀ a, DifferentiableAt ℝ (lieCurve j a) 0)
    (hinj : ∀ a, (∀ t, lieCurve j a t = 1) → a = 0) : Injective (velocityMap j hd) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro a ha
  have hv : deriv (lieCurve j a) 0 = 0 := ha
  have h (s : ℝ) : HasDerivAt (lieCurve j a) 0 s := by
    have hh : HasDerivAt (lieCurve j a) 0 (s - s) := by simpa [hv] using (hd a).hasDerivAt
    have hcomp := (hh.scomp (h := fun y : ℝ ↦ y - s) s ((hasDerivAt_id s).sub_const s)).const_mul (lieCurve j a s)
    simpa only [Function.comp_def, id_eq, one_smul, mul_zero, zero_mul, ← lieCurve_add, add_sub_cancel] using hcomp
  apply hinj
  exact fun t ↦ (is_const_of_deriv_eq_zero (fun x ↦ (h x).differentiableAt) (fun x ↦ (h x).deriv) t 0).trans (lieCurve_zero j a)

private def posExpEquiv : Multiplicative ℝ ≃ₜ* ℝ≥0ˣ :=
  ContinuousMulEquiv.mk' (show Multiplicative ℝ ≃ₜ ℝ≥0ˣ from
    Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm) (map_mul positiveRealExpHom)

variable (F : Type*) [Field F] [NumberField F]
/-- An idele direction is determined by its archimedean velocity. Its finite component is
constant along the connected parameter line. -/
private theorem ideleVelocity : ∃ L : OneParameterSpace 𝕀[F] →ₗ[ℝ] mixedEmbedding.mixedSpace F, Injective L := by
  classical
  let M := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let j : 𝕀[F] →* mixedEmbedding.mixedSpace F :=
    M.toMonoidHom.comp ((MonoidHom.fst _ _).comp (Units.coeHom _))
  have hd (a : OneParameterSpace 𝕀[F]) : DifferentiableAt ℝ (lieCurve (V := mixedEmbedding.mixedSpace F) j a) 0 := by
    let b := a.toMul.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
    have he (t : ℝ) : b (posExpEquiv (Multiplicative.ofAdd t)) = a.toMul (Multiplicative.ofAdd t) :=
      congrArg a.toMul (posExpEquiv.symm_apply_apply _)
    have hh := adeleOneParameter_archimedean_differentiable b
    change DifferentiableAt ℝ (fun t : ℝ ↦ M (b (posExpEquiv (Multiplicative.ofAdd t))).val.1) 0 at hh
    change DifferentiableAt ℝ (fun t : ℝ ↦ M (a.toMul (Multiplicative.ofAdd t)).val.1) 0
    simpa only [he] using hh
  refine ⟨velocityMap j hd, velocityMap_injective j hd fun a h ↦ ?_⟩
  apply ContinuousMonoidHom.ext
  intro t
  apply Units.ext
  apply Prod.ext
  · apply M.injective
    exact (h t.toAdd).trans (map_one M).symm
  · let b := a.toMul.comp (posExpEquiv.symm : ℝ≥0ˣ →ₜ* Multiplicative ℝ)
    have he : b (posExpEquiv t) = a.toMul t := congrArg a.toMul (posExpEquiv.symm_apply_apply t)
    exact (congrArg (fun g : 𝕀[F] ↦ g.val.2) he.symm).trans (adeleOneParameter_finite_eq_one b _)

end ClassVelocity

section ClassRankBound

variable (F : Type*) [Field F] [NumberField F]
/-- Principal ideles are discrete, so every idele class direction lifts through the quotient
covering. Archimedean velocities bound the resulting dimension by the field degree. -/
private theorem component_rank_bound :
    Module.Finite ℝ (OneParameterSpace C₀[F]) ∧ Module.finrank ℝ (OneParameterSpace C₀[F]) ≤ Module.finrank ℚ F := by
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  let q : 𝕀[F] →ₜ* C[F] := ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩
  have hcov : IsCoveringMap q := (N.isQuotientCoveringMap ((ideleGroup_quotient.{_, 0} F).2.2.1)).isCoveringMap
  have hq := oneParameterMap_surjective_of_covering q hcov
  let i : C₀[F] →ₜ* C[F] := ⟨(C₀[F]).subtype, continuous_subtype_val⟩
  have hi : Injective (oneParameterMap i) := fun a b he ↦ ContinuousMonoidHom.ext fun t ↦
    Subtype.val_injective (congrArg (fun z : OneParameterSpace C[F] ↦ z.toMul t) he)
  obtain ⟨L, hL⟩ := ideleVelocity F
  have : Module.Finite ℝ (OneParameterSpace 𝕀[F]) := Module.Finite.of_injective L hL
  have : Module.Finite ℝ (OneParameterSpace C[F]) := Module.Finite.of_surjective (oneParameterMap q) hq
  refine ⟨Module.Finite.of_injective (oneParameterMap i) hi, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_injective hi).trans
    ((LinearMap.finrank_le_finrank_of_surjective hq).trans
      ((LinearMap.finrank_le_finrank_of_injective hL).trans_eq (mixedEmbedding.finrank F)))

end ClassRankBound

section SplitRank

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
private def kernelIncl (n : X →* ℝ≥0ˣ) : n.ker →ₜ* X := ⟨n.ker.subtype, continuous_subtype_val⟩
private def logNormHom (n : X →* ℝ≥0ˣ) (hn : Continuous n) : X →ₜ* Multiplicative ℝ :=
  (posExpEquiv.symm : ℝ≥0ˣ →ₜ* _).comp ⟨n, hn⟩

private theorem radial_ker_decompose (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) (a : OneParameterSpace X) :
    ∃ (c : ℝ) (b : OneParameterSpace n.ker), a = c • Additive.ofMul (τ.comp positiveRealExpHom) + oneParameterMap (kernelIncl n) b := by
  let c := (logNormHom n hn (a.toMul (Multiplicative.ofAdd 1))).toAdd
  let r : OneParameterSpace X := Additive.ofMul (τ.comp positiveRealExpHom)
  have hn' (t) : n (a.toMul t) = positiveRealExpHom (timeScale c t) := by
    apply posExpEquiv.symm.injective
    exact (lcaTopologicalLie_real ((logNormHom n hn).comp a.toMul) t.toAdd).trans
      ((mul_comm t.toAdd c).trans (posExpEquiv.symm_apply_apply (timeScale c t)).symm)
  let v := (a - c • r).toMul
  have hv (t) : v t ∈ n.ker := by
    change n (a.toMul t / τ (positiveRealExpHom (timeScale c t))) = 1
    rw [map_div, hτ, hn', div_self']
  let b : OneParameterSpace n.ker := Additive.ofMul (⟨v.toMonoidHom.codRestrict _ hv, v.continuous.subtype_mk _⟩ : LCATopologicalLie n.ker)
  refine ⟨c, b, ?_⟩
  change a = c • r + (a - c • r)
  abel

/-- The radial direction and the norm-one directions inject as a direct sum into the full space
of directions. -/
private theorem kernel_rank_bound (n : X →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n)
    [Module.Finite ℝ (OneParameterSpace X)] :
    Module.Finite ℝ (OneParameterSpace n.ker) ∧ Module.finrank ℝ (OneParameterSpace n.ker) + 1 ≤ Module.finrank ℝ (OneParameterSpace X) := by
  let j := oneParameterMap (kernelIncl n)
  let r : OneParameterSpace X := Additive.ofMul (τ.comp positiveRealExpHom)
  let L : (OneParameterSpace n.ker × ℝ) →ₗ[ℝ] OneParameterSpace X := j.coprod (LinearMap.toSpanSingleton ℝ _ r)
  have hL : Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    rintro ⟨a, c⟩ ha
    have he : j a + c • r = 0 := ha
    have h (t : Multiplicative ℝ) : (a.toMul t).val * τ (positiveRealExpHom (timeScale c t)) = 1 :=
      congrArg (fun v : OneParameterSpace X ↦ v.toMul t) he
    have hc : c = 0 := by
      have h' := congrArg n (h (Multiplicative.ofAdd 1))
      rw [map_mul, (a.toMul _).property, one_mul, hτ, map_one n] at h'
      have hc' := posExpEquiv.injective (h'.trans posExpEquiv.map_one.symm)
      change c * 1 = 0 at hc'
      simpa using hc'
    subst c
    have hja : j a = 0 := by simpa using he
    have h0 : a = 0 := ContinuousMonoidHom.ext fun t ↦ Subtype.ext <| congrArg (fun v : OneParameterSpace X ↦ v.toMul t) hja
    subst a
    rfl
  have hi : Injective j := fun a b h ↦ ContinuousMonoidHom.ext fun t ↦
    Subtype.val_injective (congrArg (fun v : OneParameterSpace X ↦ v.toMul t) h)
  have : Module.Finite ℝ (OneParameterSpace n.ker) := Module.Finite.of_injective j hi
  refine ⟨this, ?_⟩
  simpa only [Module.finrank_prod, Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective hL

private theorem exists_padded_spanning {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {d : ℕ} (hd : Module.finrank ℝ V ≤ d) :
    ∃ u : Fin d → V, Submodule.span ℝ (range u) = ⊤ := by
  let B := Module.finBasis ℝ V
  let u (i : Fin d) := if hi : i.val < Module.finrank ℝ V then B ⟨i, hi⟩ else 0
  refine ⟨u, top_unique (B.span_eq ▸ Submodule.span_mono ?_)⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨Fin.castLE hd i, dite_eq_left i.isLt⟩

end SplitRank

section LiftLie

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
/-- A real-valued homomorphism extends algebraically by divisibility. Continuity on the open
subgroup gives continuity at the identity of the whole group. -/
private theorem openSubgroup_extend_real (J : Subgroup X) (hJ : IsOpen (J : Set X))
    (g : J →ₜ* Multiplicative ℝ) : ∃ f : X →ₜ* Multiplicative ℝ, ∀ x : J, f x.val = g x := by
  let i : Additive J →+ Additive X := MonoidHom.toAdditive J.subtype
  let l : Additive J →+ ℝ := MonoidHom.toAdditive g.toMonoidHom
  obtain ⟨v, hv⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom i Subtype.val_injective l
  let f : X →* Multiplicative ℝ := AddMonoidHom.toMultiplicative v
  have he (x : J) : f x.val = g x := DFunLike.congr_fun hv (Additive.ofMul x)
  refine ⟨⟨f, continuous_of_continuousAt_one f ?_⟩, he⟩
  have hc : ContinuousAt (f ∘ Subtype.val : J → Multiplicative ℝ) 1 :=
    by rw [show (f ∘ Subtype.val : J → _) = g from funext he]; exact g.continuous.continuousAt
  exact hJ.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hc

variable [T2Space X] [LocallyCompactSpace X]
private theorem quotient_t2_of_compact (K : Subgroup X) (hk : IsCompact (K : Set X)) : T2Space (X ⧸ K) :=
  IsTopologicalGroup.t2Space_iff_one_closed.mpr <| by
    rw [← (QuotientGroup.isQuotientMap_mk K).isCoinducing.isClosed_preimage]
    convert hk.isClosed using 1
    simpa only [QuotientGroup.mk_one] using QuotientGroup.preimage_mk_one K

/-- Duality identifies a direction on the quotient with a real homomorphism on the open
annihilator, which extends to the whole dual group. -/
private theorem oneParameterMap_quotient_surjective (K : Subgroup X) (hk : IsCompact (K : Set X)) :
    Surjective (oneParameterMap (show X →ₜ* X ⧸ K from ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩)) := by
  have : T2Space (X ⧸ K) := quotient_t2_of_compact K hk
  let q : X →ₜ* X ⧸ K := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  obtain ⟨Z, hZ⟩ := lcaQuotientDual_equiv_annihilator K hk.isClosed
  obtain ⟨ea, hea⟩ := lcaTopologicalLie_dual (G := X)
  obtain ⟨eb, heb⟩ := lcaTopologicalLie_dual (G := X ⧸ K)
  let e := exists_realPontryaginDualEquiv.choose
  intro a
  let g := (e.symm : PontryaginDual (Multiplicative ℝ) →ₜ* Multiplicative ℝ).comp
    ((eb a.toMul).comp (Z.symm : lcaAnnihilator K →ₜ* _))
  obtain ⟨f, hf⟩ := openSubgroup_extend_real (lcaAnnihilator K) (isOpen_lcaAnnihilator K hk) g
  let u := (e : Multiplicative ℝ →ₜ* PontryaginDual (Multiplicative ℝ)).comp f
  let b := ea.symm u
  have hb : PontryaginDual.map b = u := (hea _).symm.trans (ea.apply_symm_apply u)
  refine ⟨Additive.ofMul b, ?_⟩
  change q.comp b = a.toMul
  apply eb.injective
  rw [heb]
  apply ContinuousMonoidHom.ext
  intro χ
  apply PontryaginDual.ext
  intro t
  have he : PontryaginDual.map q χ = (Z χ).val :=
    PontryaginDual.ext fun x ↦ (hZ χ x).symm
  change χ (q (b t)) = eb a.toMul χ t
  calc χ (q (b t)) = PontryaginDual.map b (PontryaginDual.map q χ) t := rfl
    _ = e (f (Z χ).val) t := by rw [hb, he]; rfl
    _ = eb a.toMul χ t := by
      rw [hf]
      change e (e.symm (eb a.toMul (Z.symm (Z χ)))) t = _
      rw [e.apply_symm_apply, Z.symm_apply_apply]

end LiftLie

section DirSpan

variable {X Y : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X]
  [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
private def combinedDirections {d : ℕ} (n : X →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* X) (γ : Fin d → LCATopologicalLie n.ker) :
    Fin (d + 1) → LCATopologicalLie X :=
  Fin.cons (τ.comp positiveRealExpHom) (fun i ↦ (kernelIncl n).comp (γ i))

private theorem combinedDirections_span {d : ℕ} (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) (γ : Fin d → OneParameterSpace n.ker)
    (hγ : Submodule.span ℝ (range γ) = ⊤) :
    Submodule.span ℝ (range fun i ↦ Additive.ofMul (combinedDirections n τ (fun j ↦ (γ j).toMul) i)) = ⊤ := by
  let a := combinedDirections n τ (fun j ↦ (γ j).toMul)
  let M := Submodule.span ℝ (range fun i ↦ Additive.ofMul (a i))
  apply top_unique
  intro x _
  obtain ⟨c, b, hb⟩ := radial_ker_decompose n hn τ hτ x
  have h₁ : Additive.ofMul (τ.comp positiveRealExpHom) ∈ M := Submodule.subset_span ⟨0, rfl⟩
  have h₂ : oneParameterMap (kernelIncl n) b ∈ M := by
    have hb' : b ∈ Submodule.span ℝ (range γ) := hγ ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun b _ ↦ oneParameterMap (kernelIncl n) b ∈ M) ?_ ?_ ?_ ?_ hb'
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.succ, rfl⟩
    · rw [map_zero]; exact M.zero_mem
    · intro x y _ _ hx hy; rw [map_add]; exact M.add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact M.smul_mem c hx
  exact hb ▸ M.add_mem (M.smul_mem c h₁) h₂

variable [T2Space Y] [LocallyCompactSpace Y]
private def firstOrderLinear : OneParameterSpace Y →ₗ[ℝ] bruhatDiffDegreeOneReal (G := Y) where
  toFun v := directionOperator v.toMul
  map_add' a b := Subtype.ext (bruhatFirstOrder_mul a.toMul b.toMul)
  map_smul' c a := Subtype.ext (bruhatFirstOrder_scale a.toMul c)

private theorem image_firstOrder_span {I : Type*} (a : I → LCATopologicalLie X)
    (ha : Submodule.span ℝ (range (fun i ↦ Additive.ofMul (a i))) = ⊤)
    (q : X →ₜ* Y) (hq : Surjective (oneParameterMap q)) :
    Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (q.comp (a i))) = bruhatDiffDegreeOneReal := by
  let M := bruhatDiffDegreeOneReal (G := Y)
  let L := (M.subtype.comp firstOrderLinear).comp (oneParameterMap q)
  let v (i : I) : OneParameterSpace X := Additive.ofMul (a i)
  change Submodule.span ℝ (range (L ∘ v)) = M
  rw [Set.range_comp, ← Submodule.map_span, show Submodule.span ℝ (range v) = ⊤ from ha]
  rw [Submodule.map_top, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hq),
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr directionOperator_bijective.2),
    Submodule.range_subtype]

end DirSpan

section CompactReal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
private theorem compact_killed_by_real (K : Subgroup G) (hK : IsCompact (K : Set G))
    (l : G →ₜ* Multiplicative ℝ) : K ≤ l.toMonoidHom.ker := by
  have hc : Continuous (fun g : G ↦ (l g).toAdd) := continuous_toAdd.comp l.continuous
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hK.image hc).isBounded
  intro x hx
  by_contra h
  have hp : 0 < |(l x).toAdd| := abs_pos.mpr (show (l x).toAdd ≠ 0 from h)
  obtain ⟨k, hk⟩ := exists_nat_gt (C / |(l x).toAdd|)
  have hh := hC _ (mem_image_of_mem _ (K.pow_mem hx k))
  change ‖(l (x ^ k)).toAdd‖ ≤ C at hh
  rw [map_pow, toAdd_pow, nsmul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)] at hh
  exact ((div_lt_iff₀ hp).mp hk).not_ge hh

private theorem realHom_factors (l : G →ₜ* Multiplicative ℝ) (r : LCATopologicalLie G)
    (hr : RightInverse r l) (hk : IsCompact (l.toMonoidHom.ker : Set G))
    (u : G →ₜ* Multiplicative ℝ) : ∃ c : ℝ, ∀ x, (u x).toAdd = c * (l x).toAdd := by
  refine ⟨(u (r (Multiplicative.ofAdd 1))).toAdd, fun x ↦ ?_⟩
  have hx : x / r (l x) ∈ l.toMonoidHom.ker := by simp [MonoidHom.mem_ker, hr (l x)]
  have he : u (x / r (l x)) = 1 := compact_killed_by_real _ hk u hx
  rw [map_div, div_eq_one] at he
  exact (congrArg Multiplicative.toAdd he).trans ((lcaTopologicalLie_real (u.comp r) (l x).toAdd).trans (mul_comm ..))

private def quotientLog (K : Subgroup G) (hk : IsCompact (K : Set G)) (l : G →ₜ* Multiplicative ℝ) :
    G ⧸ K →ₜ* Multiplicative ℝ :=
  ⟨QuotientGroup.lift K l.toMonoidHom (compact_killed_by_real _ hk l),
   (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr l.continuous⟩

private theorem quotientLog_compact (K : Subgroup G) (hk : IsCompact (K : Set G))
    (l : G →ₜ* Multiplicative ℝ) (hl : IsCompact (l.toMonoidHom.ker : Set G)) :
    IsCompact ((quotientLog K hk l).toMonoidHom.ker : Set (G ⧸ K)) := by
  have he : ((quotientLog K hk l).toMonoidHom.ker : Set (G ⧸ K)) = QuotientGroup.mk '' (l.toMonoidHom.ker : Set G) := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨fun h ↦ ⟨x, h, rfl⟩, fun ⟨z, hz, he⟩ ↦ he ▸ hz⟩
  exact he ▸ hl.image QuotientGroup.continuous_mk

end CompactReal

section SplitSymbol

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
/-- On a split extension of the line by a compact kernel, each first-order symbol is a scalar
multiple of the real coordinate. Its powers generate all polynomial symbols. -/
private theorem split_symbol_span (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (l : G →ₜ* Multiplicative ℝ) (r : LCATopologicalLie G) (hr : RightInverse r l)
    (hk : IsCompact (l.toMonoidHom.ker : Set G)) :
    Submodule.span ℂ (range fun E : bruhatDiffAlgebra (PontryaginDual G) ↦ fun x ↦ bruhatSymbolHom (b x) E) =
    Submodule.span ℂ (range fun k : ℕ ↦ fun x : G ↦ ((l x).toAdd : ℂ) ^ k) := by
  classical
  let A := bruhatDiffAlgebra (PontryaginDual G)
  let W (k : ℕ) (x : G) := ((l x).toAdd : ℂ) ^ k
  let S (E : A) := ∃ (c : ℂ) (k : ℕ), ∀ x, bruhatSymbolHom (b x) E = c * W k x
  have hgen (v : LCATopologicalLie (PontryaginDual G)) : S (bruhatDiffGenerator v) := by
    obtain ⟨u, hu⟩ := exists_frequency_symbol v
    obtain ⟨c, hc⟩ := realHom_factors l r hr hk (u.comp (b : G →ₜ* _))
    refine ⟨(2 * Real.pi * Complex.I) * c, 1, fun x ↦ ?_⟩
    change bruhatDiffSymbol (bruhatDiffGenerator v) (b x) = _ * ((l x).toAdd : ℂ) ^ 1
    have hx : (u (b x)).toAdd = c * (l x).toAdd := hc x
    rw [hu, hx, Complex.ofReal_mul, pow_one]
    ring
  have hword (w : List (LCATopologicalLie (PontryaginDual G))) : S (bruhatDiffWord w) := by
    induction w with
    | nil => exact ⟨1, 0, fun x ↦ by simp [bruhatDiffWord, W]⟩
    | cons a w ih =>
      obtain ⟨c, k, hc⟩ := ih
      obtain ⟨e, m, he⟩ := hgen a
      refine ⟨c * e, k + m, fun x ↦ ?_⟩
      have heq : bruhatDiffWord (a::w) = bruhatDiffWord w * bruhatDiffGenerator a := by simp [bruhatDiffWord]
      rw [heq, map_mul, hc, he]
      simp only [W, pow_add]
      ring
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨E, rfl⟩
    let M := Submodule.span ℂ (range W)
    have hmem (w : List (LCATopologicalLie (PontryaginDual G))) :
        (fun x ↦ bruhatSymbolHom (b x) (bruhatDiffWord w)) ∈ M := by
      obtain ⟨c, k, hc⟩ := hword w
      exact funext hc ▸ M.smul_mem c (Submodule.subset_span (mem_range_self k))
    obtain ⟨p, hp⟩ := bruhatDiff_exists_presentation E
    rw [← hp]
    have he : (fun x ↦ bruhatSymbolHom (b x) (p.sum fun w z ↦ z • bruhatDiffWord w)) =
        ∑ w ∈ p.support, p w • (fun x ↦ bruhatSymbolHom (b x) (bruhatDiffWord w)) := by
      funext x
      simp [Finsupp.sum, Finset.sum_apply]
    change (fun x ↦ bruhatSymbolHom (b x) (p.sum fun w z ↦ z • bruhatDiffWord w)) ∈ M
    rw [he]
    exact M.sum_mem fun w _ ↦ M.smul_mem _ (hmem w)
  · rintro _ ⟨k, rfl⟩
    obtain ⟨E, hE⟩ := exists_operator_of_frequency (l.comp (b.symm : PontryaginDual (PontryaginDual G) →ₜ* G))
    refine Submodule.subset_span ⟨E ^ k, funext fun x ↦ ?_⟩
    change bruhatSymbolHom (b x) (E ^ k) = _
    rw [map_pow]
    exact congrArg (· ^ k) ((hE (b x)).trans (congrArg (fun y ↦ ((l y).toAdd : ℂ)) (b.symm_apply_apply x)))

end SplitSymbol

section SupSpan

variable {A B C I J I' J' : Type*} [AddCommMonoid A] [Module ℂ A]
  [AddCommMonoid B] [Module ℂ B] [AddCommMonoid C] [Module ℂ C]
private theorem span_pairs_congr (T : A →ₗ[ℂ] B →ₗ[ℂ] C)
    (u : I → A) (v : J → B) (u' : I' → A) (v' : J' → B)
    (hu : Submodule.span ℂ (range u) = Submodule.span ℂ (range u'))
    (hv : Submodule.span ℂ (range v) = Submodule.span ℂ (range v')) :
    Submodule.span ℂ (range fun i : I × J ↦ T (u i.1) (v i.2)) =
      Submodule.span ℂ (range fun i : I' × J' ↦ T (u' i.1) (v' i.2)) := by
  simpa only [Submodule.map₂_span_span, Set.image2_range] using
    congrArg₂ (Submodule.map₂ T) hu hv

end SupSpan

section SplitSupTopology

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
private theorem generatesSup_shiftedPowers {E X I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (u : I → E →ₗ[ℂ] (X → ℂ)) (t : X → ℝ)
    (h : GeneratesSeminormTopology (fun i : ℕ × I ↦ fun f ↦ ⨆ x, (‖((t x : ℂ) ^ i.1) * u i.2 f x‖₊ : ℝ≥0∞))) :
    GeneratesSeminormTopology (fun i : ℕ × I ↦ fun f ↦ ⨆ x, (‖((1 + |t x| ^ i.1 : ℝ) : ℂ) * u i.2 f x‖₊ : ℝ≥0∞)) := by
  let v : X → ℂ := fun x ↦ (|t x| : ℝ)
  let U (i : ℕ × I) := mulWeight (u i.2) (v ^ i.1)
  let V (i : ℕ × I) := mulWeight (u i.2) (1 + v ^ i.1)
  have hU : GeneratesSeminormTopology (fun i f ↦ ⨆ x, (‖U i f x‖₊ : ℝ≥0∞)) := by
    convert h using 1
    funext i f
    congr 1
    funext x
    change (‖((|t x| : ℝ) : ℂ) ^ i.1 * _‖₊ : ℝ≥0∞) = _
    simp
  have hV : GeneratesSeminormTopology (fun i f ↦ ⨆ x, (‖V i f x‖₊ : ℝ≥0∞)) := by
    exact generatesSupSeminorms_of_span_eq U V (mulWeight_shiftedPowers_span u v).symm hU
  convert hV using 1
  funext i f
  congr 1
  funext x
  change (‖((1 + |t x| ^ i.1 : ℝ) : ℂ) * _‖₊ : ℝ≥0∞) = (‖(1 + ((|t x| : ℝ) : ℂ) ^ i.1) * _‖₊ : ℝ≥0∞)
  simp

/-- On a compact-by-real elementary group, the weighted operator span is generated
by powers of the real coordinate times monomials in any spanning set of directions. -/
private theorem split_monomial_weight_span (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (l : G →ₜ* Multiplicative ℝ) (r : LCATopologicalLie G) (hr : RightInverse r l)
    (hker : IsCompact (l.toMonoidHom.ker : Set G)) {d : ℕ} (a : Fin d → LCATopologicalLie G)
    (hs : Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (a i)) = bruhatDiffDegreeOneReal) :
    Submodule.span ℂ (range fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      bruhatWeightedLinear b i.1 i.2) =
    Submodule.span ℂ (range fun i : ℕ × (Fin d → ℕ) ↦
      mulWeight (diffApplyLinear (bruhatDiffMonomial a i.2)) (fun x ↦ ((l x).toAdd : ℂ) ^ i.1)) := by
  let V (i : ℕ × (Fin d → ℕ)) := mulWeight (diffApplyLinear (bruhatDiffMonomial a i.2))
    (fun x ↦ ((l x).toAdd : ℂ) ^ i.1)
  have hD : Submodule.span ℂ (range (id : bruhatDiffAlgebra G → _)) =
      Submodule.span ℂ (range (bruhatDiffMonomial a)) := by
    apply le_antisymm (Submodule.span_le.mpr (fun D _ ↦ bruhatDiffMonomial_mem_span a hs D))
    exact Submodule.span_mono (by simp)
  have h := span_pairs_congr (diffApplyWithWeights (G := G)) id
    (fun E x ↦ bruhatSymbolHom (b x) E) (bruhatDiffMonomial a)
    (fun k x ↦ ((l x).toAdd : ℂ) ^ k) hD (split_symbol_span b l r hr hker)
  refine h.trans (congrArg (Submodule.span ℂ) ?_)
  exact (Equiv.prodComm (Fin d → ℕ) ℕ).surjective.range_comp V

private theorem elementary_splitSup (e : ElementaryLCAPresentation G) (l : G →ₜ* Multiplicative ℝ)
    (r : LCATopologicalLie G) (hr : RightInverse r l) (hker : IsCompact (l.toMonoidHom.ker : Set G))
    {d : ℕ} (a : Fin d → LCATopologicalLie G)
    (hs : Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (a i)) = bruhatDiffDegreeOneReal) :
    GeneratesSeminormTopology (fun i : ℕ × (Fin d → ℕ) ↦ fun f : SchwartzBruhat G ↦
      ⨆ x, (‖((1 + |(l x).toAdd|^i.1 : ℝ) : ℂ) * (diffApplyLinear (bruhatDiffMonomial a i.2) f x)‖₊ : ℝ≥0∞)) := by
  apply generatesSup_shiftedPowers (fun α ↦ diffApplyLinear (bruhatDiffMonomial a α))
  let hb₀ := pontryaginDual_bidual (G := G)
  let b := hb₀.choose
  have hb := hb₀.choose_spec
  let U (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) := bruhatWeightedLinear b i.1 i.2
  let V (i : ℕ × (Fin d → ℕ)) := mulWeight (diffApplyLinear (bruhatDiffMonomial a i.2))
    (fun x ↦ ((l x).toAdd : ℂ) ^ i.1)
  exact generatesSupSeminorms_of_span_eq U V (split_monomial_weight_span b l r hr hker a hs)
    (elementarySchwartz_operatorSup_generates e b hb)

private theorem elementary_splitLp (e : ElementaryLCAPresentation G) (l : G →ₜ* Multiplicative ℝ)
    (r : LCATopologicalLie G) (hr : RightInverse r l) (hker : IsCompact (l.toMonoidHom.ker : Set G))
    {d : ℕ} (a : Fin d → LCATopologicalLie G)
    (hs : Submodule.span ℝ (range fun i ↦ bruhatFirstOrder (a i)) = bruhatDiffDegreeOneReal)
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ⊤) :
    GeneratesLpSeminorms μ p (fun i : ℕ × (Fin d → ℕ) ↦ fun f : SchwartzBruhat G ↦
      fun x ↦ ((1 + |(l x).toAdd|^i.1 : ℝ) : ℂ) * diffApplyLinear (bruhatDiffMonomial a i.2) f x) := by
  let hb₀ := pontryaginDual_bidual (G := G)
  let b := hb₀.choose
  have hb := hb₀.choose_spec
  let U (i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G)) := bruhatWeightedLinear b i.1 i.2
  let V (i : ℕ × (Fin d → ℕ)) := mulWeight (diffApplyLinear (bruhatDiffMonomial a i.2))
    (fun x ↦ ((l x).toAdd : ℂ) ^ i.1)
  have hV := generatesLpSeminorms_of_span_eq (μ := μ) hp U V
    (split_monomial_weight_span b l r hr hker a hs) (elementarySchwartz_operatorLp_finite e b hb μ p hp hfin)
  let u (α : Fin d → ℕ) := diffApplyLinear (bruhatDiffMonomial a α)
  let t (x : G) : ℂ := (|(l x).toAdd| : ℝ)
  let W (i : ℕ × (Fin d → ℕ)) := mulWeight (u i.2) (t ^ i.1)
  have hm (i : ℕ × (Fin d → ℕ)) (f : SchwartzBruhat G) : AEStronglyMeasurable (W i f) μ := by
    have h0 := (hV.1 (0,i.2) f).aestronglyMeasurable
    have hu : AEStronglyMeasurable (u i.2 f) μ := by
      simpa [V, u, mulWeight, Pi.mul_def] using h0
    have ht : Continuous t := Complex.continuous_ofReal.comp
      (continuous_abs.comp (continuous_toAdd.comp l.continuous))
    exact (ht.pow i.1).aestronglyMeasurable.mul hu
  have he (i : ℕ × (Fin d → ℕ)) (f : SchwartzBruhat G) (x : G) : ‖V i f x‖ = ‖W i f x‖ := by
    change ‖(((l x).toAdd : ℂ) ^ i.1) * u i.2 f x‖ =
      ‖((|(l x).toAdd| : ℝ) : ℂ) ^ i.1 * u i.2 f x‖
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have hW : GeneratesLpSeminorms μ p (fun i ↦ W i) :=
    ⟨fun i f ↦ (hV.1 i f).congr_norm (hm i f) (.of_forall (he i f)),
      hV.2.choose, hV.2.choose_spec.1, fun i f ↦ (hV.2.choose_spec.2 i f).trans
        (eLpNorm_congr_norm_ae (hV.1 i f).aestronglyMeasurable (hm i f) (.of_forall (he i f)))⟩
  have h := generatesLpSeminorms_of_span_eq hp W _ (mulWeight_shiftedPowers_span u t).symm hW
  convert h using 1
  funext i f x
  change ((1 + |(l x).toAdd| ^ i.1 : ℝ) : ℂ) * _ =
    (1 + ((|(l x).toAdd| : ℝ) : ℂ) ^ i.1) * _
  simp [u]

end SplitSupTopology

section StageQuot

variable {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H]
private def topWithKernel (hc : IsCompactlyGeneratedGroup H) (K : Subgroup H) (hg : IsBruhatGoodSubgroup K) :
    BruhatStructuralPair H := ⟨(⊤, OrderDual.toDual K), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv (topSubgroupEquiv H).symm hc, hg, le_top⟩

private def topQuotEquiv (hc : IsCompactlyGeneratedGroup H) (K : Subgroup H) (hg : IsBruhatGoodSubgroup K) :
    (topWithKernel hc K hg).quotient ≃ₜ* H ⧸ K :=
  quotientCongr _ K (topSubgroupEquiv H) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩)

private def quotientBotEquiv (H : Type*) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] :
    H ⧸ (⊥ : Subgroup H) ≃ₜ* H :=
  { QuotientGroup.quotientBot with
    continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_id
    continuous_invFun := QuotientGroup.continuous_mk }

private theorem stageRealization_of_mem (a : BruhatStructuralPair H) (e : ElementaryLCAPresentation a.quotient)
    (f : SchwartzBruhatStage e) (x : H) (hx : x ∈ a.val.1) :
    schwartzBruhatStageRealization a e f x = f (e.equiv (QuotientGroup.mk (⟨x, hx⟩ : a.val.1))).toAdd :=
  (schwartzBruhatStageRealization_apply a e f x).trans (dite_eq_left hx)

/-- Identify functions fixed by the compact subgroup with functions on the elementary quotient,
using the averaging retractions for the two full stages. -/
private theorem fixedStage_quotient (hc : IsCompactlyGeneratedGroup H) (K : Subgroup H)
    (hk : IsCompact (K : Set H)) (hg : IsBruhatGoodSubgroup K) :
    Nonempty (ElementaryLCAPresentation (H ⧸ K)) ∧
    ∃ E : schwartzBruhatInvariantSubmodule K →ₗ[ℂ] SchwartzBruhat (H ⧸ K),
      IsInducing E ∧ ∀ f x, (E f) (QuotientGroup.mk x) = f.val x := by
  let Q := H ⧸ K
  have : T2Space Q := quotient_t2_of_compact K hk
  let a := topWithKernel hc K hg
  let e := Classical.choice a.elementary
  let A := topQuotEquiv hc K hg
  let en := transportedPresentation A e
  have hq := (lca_elementary_iff (G := Q)).mpr ⟨en⟩
  let b := topWithKernel hq.1 (⊥ : Subgroup Q) (isBruhatGoodSubgroup_bot_iff.mpr hq.2)
  let B : b.quotient ≃ₜ* Q := (topQuotEquiv hq.1 (⊥ : Subgroup Q) (isBruhatGoodSubgroup_bot_iff.mpr hq.2)).trans (quotientBotEquiv Q)
  let φ := A.trans B.symm
  let e' := transportedPresentation φ e
  let q : H →ₜ* Q := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  have hm (v : SchwartzBruhatStage e) : (∀ x, schwartzBruhatStageRealization b e' v (q x) =
      schwartzBruhatStageRealization a e v x) ∧ ∀ y ∉ range q, schwartzBruhatStageRealization b e' v y = 0 := by
    refine ⟨fun x ↦ ?_, fun y hy ↦ (hy (QuotientGroup.mk_surjective y)).elim⟩
    refine (stageRealization_of_mem b e' v (q x) (Subgroup.mem_top _)).trans (Eq.trans ?_
      (stageRealization_of_mem a e v x (Subgroup.mem_top _)).symm)
    let z : a.val.1 := ⟨x, Subgroup.mem_top _⟩
    let w : b.val.1 := ⟨q x, Subgroup.mem_top _⟩
    have he : B (QuotientGroup.mk w) = A (QuotientGroup.mk z) := rfl
    exact congrArg (fun u : a.quotient ↦ v (e.equiv u).toAdd)
      ((congrArg A.symm he).trans (A.symm_apply_apply (QuotientGroup.mk z)))
  let hF := fixedStage_extension_of_coordinates q a b e e'
    (ContinuousLinearEquiv.refl ℂ (SchwartzBruhatStage e)) (fun _ ↦ Subgroup.mem_top _) hm
  let E := hF.choose
  have hE := hF.choose_spec.1
  have hev := hF.choose_spec.2
  refine ⟨⟨en⟩, (schwartzBruhatInvariantSubmodule (⊥ : Subgroup Q)).subtype.comp E,
    IsInducing.subtypeVal.comp hE, fun f x ↦ (hev f).1 x⟩

end StageQuot

section MonomialRadial

variable {X Y : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
  [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y]
private theorem bruhatDiffMonomial_cons (a : LCATopologicalLie X) {d : ℕ} (v : Fin d → LCATopologicalLie X)
    (m : ℕ) (α : Fin d → ℕ) : bruhatDiffMonomial (Fin.cons a v) (Fin.cons m α) =
      bruhatDiffGenerator a ^ m * bruhatDiffMonomial v α := by
  rw [(bruhatDiffAlgebra_commute (bruhatDiffGenerator a ^ m) (bruhatDiffMonomial v α)).eq]
  simp [bruhatDiffMonomial, List.finRange_succ, List.flatMap_map, bruhatDiffWord]

private theorem monomial_pullback (q : X →ₜ* Y) (hq : Surjective q) {d : ℕ} (a : Fin d → LCATopologicalLie X)
    (α : Fin d → ℕ) (f : SchwartzBruhat X) (g : SchwartzBruhat Y) (hg : ∀ x, g (q x) = f x) (x : X) :
    diffApplyLinear (bruhatDiffMonomial (fun i ↦ q.comp (a i)) α) g (q x) =
    diffApplyLinear (bruhatDiffMonomial a α) f x := by
  let v := (List.finRange d).flatMap fun i ↦ List.replicate (α i) (a i)
  have he : bruhatDiffMonomial (fun i ↦ q.comp (a i)) α = bruhatDiffWord (v.map (q.comp ·)) := by
    simp only [bruhatDiffMonomial, v, List.map_flatMap, List.map_replicate]
  refine (congrArg (fun D : bruhatDiffAlgebra Y ↦ diffApplyLinear (G := Y) D g (q x)) he).trans ?_
  exact (extends_word q v (smoothIncl (G := X) f) (smoothIncl (G := Y) g) ⟨hg, fun y hy ↦ (hy (hq y)).elim⟩).1 x

private theorem weightedDeriv_as_monomial {d : ℕ} (n : X →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* X)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (w : ℝ → ℝ)
    (f : SchwartzBruhat X) (x : X) :
    ideleClassWeightedDeriv n τ γ m α w f (n x) x = (w |Real.log ((n x).val : ℝ)| : ℂ) *
      diffApplyLinear (bruhatDiffMonomial (combinedDirections n τ γ) (Fin.cons m α)) f x := by
  let v := fun i ↦ (kernelIncl n).comp (γ i)
  let D := bruhatDiffMonomial v α
  let g := D.val (smoothIncl (G := X) f)
  let a := τ.comp positiveRealExpHom
  have he (s : ℝ) : a (Multiplicative.ofAdd s) = τ (Units.mk0 (Real.exp s).toNNReal (by positivity)) :=
    congrArg τ (positiveRealExpHom_apply s)
  have hz : a (Multiplicative.ofAdd (0 : ℝ)) = 1 := map_one a
  apply congrArg (fun z : ℂ ↦ (w |Real.log ((n x).val : ℝ)| : ℂ) * z)
  refine Eq.trans ?_ (congrArg (fun D : bruhatDiffAlgebra X ↦ diffApplyLinear (G := X) D f x) (bruhatDiffMonomial_cons a v m α)).symm
  change iteratedDeriv m (fun s : ℝ ↦ g.val (τ (Units.mk0 (Real.exp s).toNNReal (by positivity)) * x)) 0 =
    ((bruhatFirstOrder a ^ m) g).val x
  simpa only [hz, one_mul, he] using iteratedDeriv_orbit a m g x 0

end MonomialRadial

section ComponentStage

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
private theorem logNorm_compact_kernel (n : X →* ℝ≥0ˣ) (hn : Continuous n) (hk : IsCompact (n.ker : Set X)) :
    IsCompact ((logNormHom n hn).toMonoidHom.ker : Set X) := by
  have he : (logNormHom n hn).toMonoidHom.ker = n.ker := by
    ext x
    change posExpEquiv.symm (n x) = 1 ↔ n x = 1
    exact ⟨fun h ↦ posExpEquiv.symm.injective (h.trans posExpEquiv.symm.map_one.symm),
      fun h ↦ (congrArg posExpEquiv.symm h).trans posExpEquiv.symm.map_one⟩
  exact he ▸ hk

/-- Pull the elementary seminorms back along the quotient and split their multi-index into its
radial and norm-one orders. -/
private theorem component_stage_of_presentation {Y : Type*} [CommGroup Y] [TopologicalSpace Y]
    [IsTopologicalGroup Y] [T2Space Y] [LocallyCompactSpace Y] {d : ℕ}
    (n : X →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* X) (γ : Fin d → LCATopologicalLie n.ker)
    (K : Subgroup X) (q : X →ₜ* Y) (hq : Surjective q)
    (E : schwartzBruhatInvariantSubmodule K →ₗ[ℂ] SchwartzBruhat Y) (hE : IsInducing E)
    (he : ∀ f x, (E f) (q x) = f.val x)
    (l : Y →ₜ* Multiplicative ℝ) (hl : ∀ x, (l (q x)).toAdd = Real.log ((n x).val : ℝ))
    (h : GeneratesSeminormTopology (fun i : ℕ × (Fin (d + 1) → ℕ) ↦ fun f : SchwartzBruhat Y ↦
      ⨆ y, (‖((1 + |(l y).toAdd| ^ i.1 : ℝ) : ℂ) *
        diffApplyLinear (bruhatDiffMonomial (fun j ↦ q.comp (combinedDirections n τ γ j)) i.2) f y‖₊ : ℝ≥0∞))) :
    GeneratesSeminormTopology (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule K ↦
      ⨆ x, (‖ideleClassWeightedDeriv n τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by
  obtain ⟨P, hP, hval⟩ := h
  let A := Equiv.prodCongr (Equiv.refl ℕ) (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ℕ))
  have hP' := (hE.withSeminorms hP).congr_equiv A
  refine ⟨_, hP', fun i f ↦ ?_⟩
  change ENNReal.ofReal (P (A i) (E f)) = _
  refine (hval (A i) (E f)).trans ?_
  let v := combinedDirections n τ γ
  let α : Fin (d + 1) → ℕ := Fin.cons i.2.1 i.2.2
  let u (y : Y) := (‖((1 + |(l y).toAdd| ^ i.1 : ℝ) : ℂ) *
      diffApplyLinear (bruhatDiffMonomial (fun j ↦ q.comp (v j)) α) (E f) y‖₊ : ℝ≥0∞)
  change (⨆ y, u y) = _
  refine (hq.iSup_comp u).symm.trans ?_
  apply iSup_congr
  intro x
  apply congrArg (fun z : ℂ ↦ (‖z‖₊ : ℝ≥0∞))
  let w (t : ℝ) := 1 + t ^ i.1
  have hw := congrArg (fun t : ℝ ↦ (w |t| : ℂ)) (hl x)
  have hd := monomial_pullback q hq v α f.val (E f) (he f) x
  exact (congrArg₂ (· * ·) hw hd).trans (weightedDeriv_as_monomial n τ γ i.2.1 i.2.2 w f.val x).symm

private theorem component_fixed_stage {d : ℕ} (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) (hker : IsCompact (n.ker : Set X))
    (γ : Fin d → OneParameterSpace n.ker) (hγ : Submodule.span ℝ (range γ) = ⊤)
    (K : Subgroup X) (hk : IsCompact (K : Set X)) (hg : IsBruhatGoodSubgroup K) :
    GeneratesSeminormTopology (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule K ↦
      ⨆ x, (‖ideleClassWeightedDeriv n τ (fun j ↦ (γ j).toMul) i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by
  let Q := X ⧸ K
  have : T2Space Q := quotient_t2_of_compact K hk
  let hF := fixedStage_quotient (compactlyGenerated_of_split n τ hτ hker) K hk hg
  let e := Classical.choice hF.1
  let E := hF.2.choose
  let q : X →ₜ* Q := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  let l := logNormHom n hn
  let l' := quotientLog K hk l
  let r := τ.comp positiveRealExpHom
  have hr : RightInverse (q.comp r) l' := fun t ↦
    (congrArg posExpEquiv.symm (hτ (positiveRealExpHom t))).trans (posExpEquiv.symm_apply_apply t)
  let a := combinedDirections n τ (fun j ↦ (γ j).toMul)
  have hs := image_firstOrder_span a (combinedDirections_span n hn τ hτ γ hγ) q (oneParameterMap_quotient_surjective K hk)
  have ht := elementary_splitSup e l' (q.comp r) hr (quotientLog_compact K hk l (logNorm_compact_kernel n hn hker))
    (fun j ↦ q.comp (a j)) hs
  exact component_stage_of_presentation n τ _ K q QuotientGroup.mk_surjective E hF.2.choose_spec.1
    hF.2.choose_spec.2 l' (fun x ↦ (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n x)))).symm) ht

private theorem generatesLp_pullback_chart {X Y E T I J : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T] {μ : Measure X} {p : ℝ≥0∞}
    (φ : X → Y) (hφ : Measurable φ) (A : E →ₗ[ℂ] T) (hA : IsInducing A) (j : I ≃ J)
    (U : J → T → Y → ℂ) (V : I → E → X → ℂ)
    (heq : ∀ i f, V i f = (U (j i) (A f)) ∘ φ)
    (hu : GeneratesLpSeminorms (μ.map φ) p U) : GeneratesLpSeminorms μ p V := by
  obtain ⟨hm, P, hP, hval⟩ := hu
  refine ⟨fun i f ↦ heq i f ▸ (hm (j i) (A f)).comp_of_map hφ.aemeasurable,
    _, (hA.withSeminorms hP).congr_equiv j, fun i f ↦ ?_⟩
  change ENNReal.ofReal (P (j i) (A f)) = eLpNorm (V i f) p μ
  rw [heq]
  exact (hval (j i) (A f)).trans (eLpNorm_map_measure (hm _ _).aestronglyMeasurable hφ.aemeasurable)

private theorem directions_span_of_firstOrder {I : Type*} (v : I → LCATopologicalLie X)
    (hs : Submodule.span ℝ (range (fun i ↦ bruhatFirstOrder (v i))) = bruhatDiffDegreeOneReal) :
    Submodule.span ℝ (range (fun i ↦ Additive.ofMul (v i))) = ⊤ := by
  let M := bruhatDiffDegreeOneReal (G := X)
  let L := M.subtype.comp (firstOrderLinear (Y := X))
  have hinj : Injective L := M.injective_subtype.comp directionOperator_bijective.1
  apply Submodule.map_injective_of_injective hinj
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top]
  change _ = LinearMap.range (M.subtype.comp firstOrderLinear)
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr directionOperator_bijective.2), Submodule.range_subtype]
  exact hs

/-- The splitting product maps properly onto the elementary quotient. Its logarithmic
coordinate recovers the first projection, whose fibers are compact. -/
private theorem splitQuotient_productHaar (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) [CompactSpace n.ker]
    (K : Subgroup X) (hk : IsCompact (K : Set X))
    [MeasurableSpace n.ker] [BorelSpace n.ker] [SecondCountableTopology n.ker]
    (ν : Measure n.ker) [ν.IsHaarMeasure] :
    letI : MeasurableSpace (X ⧸ K) := borel _
    ((positiveRealHaar.prod ν).map (fun z : ℝ≥0ˣ × n.ker ↦
      (QuotientGroup.mk (τ z.1 * z.2.val) : X ⧸ K))).IsHaarMeasure := by
  let Q := X ⧸ K
  let : MeasurableSpace Q := borel _
  have : BorelSpace Q := ⟨rfl⟩
  have : T2Space Q := quotient_t2_of_compact K hk
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let q : X →ₜ* Q := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  let φ := q.comp (τ.coprod (kernelIncl n))
  have hs : Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x / τ (n x) ∈ n.ker := by simp [MonoidHom.mem_ker, hτ (n x)]
    exact ⟨(n x, ⟨_, hx⟩), congrArg q ((mul_comm _ _).trans (div_mul_cancel _ _))⟩
  let l := quotientLog K hk (logNormHom n hn)
  have he : l ∘ φ = posExpEquiv.symm ∘ Prod.fst := by
    funext z
    change posExpEquiv.symm (n (τ z.1 * z.2.val)) = _
    rw [map_mul, hτ z.1, z.2.property, mul_one]
    rfl
  have hproper : IsProperMap φ := isProperMap_of_comp_of_t2 φ.continuous l.continuous
    (he ▸ (posExpEquiv.symm.toHomeomorph.isProperMap.comp isProperMap_fst_of_compactSpace))
  exact Measure.isHaarMeasure_map (positiveRealHaar.prod ν) φ.toMonoidHom φ.continuous hs
    (isProperMap_iff_tendsto_cocompact.mp hproper).2

/-- Pull the logarithmically weighted Lᵖ family on the elementary quotient back to
the fixed subspace in the norm splitting. -/
private theorem split_fixed_stage_lp {d : ℕ} (n : X →* ℝ≥0ˣ) (hn : Continuous n)
    (τ : ℝ≥0ˣ →ₜ* X) (hτ : RightInverse τ n) [CompactSpace n.ker]
    [MeasurableSpace n.ker] [BorelSpace n.ker] [SecondCountableTopology n.ker]
    (ν : Measure n.ker) [ν.IsHaarMeasure] (γ : Fin d → LCATopologicalLie n.ker)
    (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) = bruhatDiffDegreeOneReal)
    (K : Subgroup X) (hk : IsCompact (K : Set X)) (hg : IsBruhatGoodSubgroup K)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hfin : p ≠ ⊤) :
    GeneratesLpSeminorms (positiveRealHaar.prod ν) p
      (fun i : ℕ × ℕ × (Fin d → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule K ↦
        ideleClassProductWeightedDeriv n τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val) := by
  let Q := X ⧸ K
  let : MeasurableSpace Q := borel _
  have : BorelSpace Q := ⟨rfl⟩
  have : T2Space Q := quotient_t2_of_compact K hk
  have hker : IsCompact (n.ker : Set X) := isCompact_iff_compactSpace.mpr inferInstance
  let hF := fixedStage_quotient (compactlyGenerated_of_split n τ hτ hker) K hk hg
  let e := hF.1.some
  let E := hF.2.choose
  let q : X →ₜ* Q := ⟨QuotientGroup.mk' K, QuotientGroup.continuous_mk⟩
  let split := τ.coprod (kernelIncl n)
  let φ := q.comp split
  let l := logNormHom n hn
  let l' := quotientLog K hk l
  let r := τ.comp positiveRealExpHom
  have hr : RightInverse (q.comp r) l' := fun t ↦
    (congrArg posExpEquiv.symm (hτ (positiveRealExpHom t))).trans (posExpEquiv.symm_apply_apply t)
  let a := combinedDirections n τ γ
  have hs := image_firstOrder_span a (combinedDirections_span n hn τ hτ (fun j ↦ Additive.ofMul (γ j))
    (directions_span_of_firstOrder γ hspan)) q (oneParameterMap_quotient_surjective K hk)
  let μ := positiveRealHaar.prod ν
  have : (μ.map φ).IsHaarMeasure := splitQuotient_productHaar n hn τ hτ K hk ν
  have h := elementary_splitLp e l' (q.comp r) hr (quotientLog_compact K hk l (logNorm_compact_kernel n hn hker))
    (fun j ↦ q.comp (a j)) hs (μ.map φ) p hp hfin
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let A := Equiv.prodCongr (Equiv.refl ℕ) (Fin.consEquiv (fun _ : Fin (d + 1) ↦ ℕ))
  apply generatesLp_pullback_chart φ φ.continuous.measurable E hF.2.choose_spec.1 A _ _ _ h
  intro i f
  funext z
  have hnorm : n (split z) = z.1 := by
    change n (τ z.1 * z.2.val) = _
    rw [map_mul, hτ z.1, z.2.property, mul_one]
  let w (t : ℝ) := 1 + t ^ i.1
  change ideleClassWeightedDeriv n τ γ i.2.1 i.2.2 w f.val z.1 (split z) = _
  have hd := weightedDeriv_as_monomial n τ γ i.2.1 i.2.2 w f.val (split z)
  refine (congrArg (fun t ↦ ideleClassWeightedDeriv n τ γ i.2.1 i.2.2 w f.val t (split z)) hnorm.symm).trans
    (hd.trans (congrArg₂ (· * ·) ?_ ?_))
  · apply congrArg (fun t : ℝ ↦ (w |t| : ℂ))
    exact Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (n (split z))))
  · exact (monomial_pullback q QuotientGroup.mk_surjective a (Fin.cons i.2.1 i.2.2)
      f.val (E f) (hF.2.choose_spec.2 f) (split z)).symm

end ComponentStage

section ComponentStages

variable {X : Type*} [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [LocallyCompactSpace X]
private theorem component_stages_of_rank (n : X →* ℝ≥0ˣ) (hn : Continuous n) (τ : ℝ≥0ˣ →ₜ* X)
    (hτ : RightInverse τ n) (hker : IsCompact (n.ker : Set X)) (d : ℕ)
    [Module.Finite ℝ (OneParameterSpace X)] (hbound : Module.finrank ℝ (OneParameterSpace X) ≤ d) :
    ∃ k₀ : Subgroup X, IsCompact (k₀ : Set X) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup X, k ≤ k₀ → IsCompact (k : Set X) → IsBruhatGoodSubgroup k →
        ∃ γ : Fin (d - 1) → LCATopologicalLie n.ker,
          GeneratesSeminormTopology (fun i : ℕ × ℕ × (Fin (d - 1) → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ⨆ x, (‖ideleClassWeightedDeriv n τ γ i.2.1 i.2.2 (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by
  let k₀ := (exists_bruhatGoodSubgroup (G := X)).choose
  have hk₀ := (exists_bruhatGoodSubgroup (G := X)).choose_spec
  have hk : IsCompact (k₀ : Set X) := by
    rw [← lcaDualAnnihilator_annihilator k₀ hk₀.1]
    exact isCompact_lcaDualAnnihilator _ hk₀.2.1
  let : Module.Finite ℝ (OneParameterSpace n.ker) := (kernel_rank_bound n τ hτ).1
  have hcount := (kernel_rank_bound n τ hτ).2
  have hle : Module.finrank ℝ (OneParameterSpace n.ker) ≤ d - 1 := by omega
  let h := exists_padded_spanning (V := OneParameterSpace n.ker) hle
  exact ⟨k₀, hk, hk₀, fun k _ hkc hkg ↦ ⟨fun i ↦ (h.choose i).toMul,
    component_fixed_stage n hn τ hτ hker h.choose h.choose_spec k hkc hkg⟩⟩

end ComponentStages

/-- Paper: Proposition D.1.10.7, p. 789. On all sufficiently small compact
good-subgroup stages of the identity component, weighted sup norms of the radial
and norm-one directional derivatives generate the Schwartz–Bruhat topology.
Deviation: The section and directions take values directly in the identity
component, since their domains are connected. The supremum is over all
representatives of the quotient. -/
theorem ideleClassComponent_weightedSup_generates
    (τ : ℝ≥0ˣ →ₜ* C₀[F]) (hτ : RightInverse τ ((ideleClassNorm F).comp (C₀[F]).subtype)) :
    let n := (ideleClassNorm F).comp (C₀[F]).subtype
    ∃ k₀ : Subgroup C₀[F], IsCompact (k₀ : Set C₀[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C₀[F], k ≤ k₀ → IsCompact (k : Set C₀[F]) → IsBruhatGoodSubgroup k →
        ∃ γ : Fin d[F] → LCATopologicalLie n.ker,
          GeneratesSeminormTopology
            (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
              ⨆ x : C₀[F], (‖ideleClassWeightedDeriv n τ γ i.2.1 i.2.2
                (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by
  let n := (ideleClassNorm F).comp (C₀[F]).subtype
  have hn : Continuous n := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.2.2.2.1.comp continuous_subtype_val
  have hker : IsCompact (n.ker : Set C₀[F]) :=
    isClosed_connectedComponent.isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness F).2.1)
  have h := component_rank_bound F
  let : Module.Finite ℝ (OneParameterSpace C₀[F]) := h.1
  exact component_stages_of_rank n hn τ hτ hker (Module.finrank ℚ F) h.2

end ComponentDirections

section Global
local instance : MeasurableSpace C[F] := borel _

variable (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
variable (γ : Fin d[F] → LCATopologicalLie C₁[F])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := C₁[F]))

include hτ hγ hspan

local notation "μ₁[" F "]" => positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)

/-- Paper: Proposition D.1.10.9(1), p. 790. For sufficiently small compact
good subgroups, the weighted Lᵖ norms using one plus powers of the absolute
log norm generate the topology on the fixed subspace.
Deviation: The norm-one directions are specified by their real basis property
and the integration measure is the product in (D.1.10.17). -/
theorem ideleClass_weightedLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by
  let n := ideleClassNorm F
  have hn : Continuous n := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.2.2.2.1
  have : CompactSpace n.ker := (ideleClassGroup_finiteness F).2.1
  have : SecondCountableTopology (IdeleGroup (𝓞 F) F) := idele_secondCountable F
  have : SecondCountableTopology C[F] := inferInstanceAs (SecondCountableTopology
    ((IdeleGroup (𝓞 F) F) ⧸ (IdeleGroup.unitEmbedding (𝓞 F) F).range))
  have : SecondCountableTopology n.ker := IsInducing.subtypeVal.secondCountableTopology
  have : BorelSpace C[F] := ⟨rfl⟩
  have : BorelSpace n.ker := inferInstanceAs (BorelSpace (ideleClassNorm F).ker)
  have : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let k₀ := (exists_bruhatGoodSubgroup (G := C[F])).choose
  have hk₀ := (exists_bruhatGoodSubgroup (G := C[F])).choose_spec
  have hkc : IsCompact (k₀ : Set C[F]) := by
    rw [← lcaDualAnnihilator_annihilator k₀ hk₀.1]
    exact isCompact_lcaDualAnnihilator _ hk₀.2.1
  exact ⟨k₀, hkc, hk₀, fun k _ hk hg p hp ↦ split_fixed_stage_lp n hn τ hτ
    (normOneIdeleClassTamagawaMeasure F) γ hspan k hk hg (ENNReal.ofReal p)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp) ENNReal.ofReal_ne_top⟩

/-- Paper: Proposition D.1.10.9(2), p. 790. Powers of the absolute log norm
alone give an Lᵖ seminorm family generating the same fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by
  exact ideleClassStages_mono (G := C[F]) (fun k p hp ↦
    ideleClassStage_logPower (n := ideleClassNorm F) (τ := τ) (γ := γ) (k := k)
      (μ := μ₁[F]) (p := ENNReal.ofReal p)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))
    (ideleClass_weightedLp_generates F τ hτ γ hγ hspan)

/-- Paper: Proposition D.1.10.9(3), p. 790. Absolute values of arbitrary complex
polynomials in the absolute log norm give a generating Lᵖ family on the fixed stage.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by
  exact ideleClassStages_mono (G := C[F]) (fun k p hp ↦
    ideleClassStage_logPolynomial (n := ideleClassNorm F) (τ := τ) (γ := γ) (k := k)
      (μ := μ₁[F]) (p := ENNReal.ofReal p)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))
    (ideleClass_logPowerLp_generates F τ hτ γ hγ hspan)

end Global

section SLocal

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Cₛ[" F ", " S "]" => SIdeleClassGroup F S
local notation "Cₛ₁[" F ", " S "]" => MonoidHom.ker (sIdeleClassNorm F S)

local instance : T2Space Cₛ[F, S] := (sIdeleClassNorm_descent F S).1
local instance : LocallyCompactSpace Cₛ[F, S] := (sIdeleClassNorm_descent F S).2.1
local instance : LocallyCompactSpace Cₛ₁[F, S] :=
  (sIdeleClassGroup_finiteness F S).1.locallyCompactSpace
local instance : MeasurableSpace Cₛ₁[F, S] := borel _

variable (τ : ℝ≥0ˣ →ₜ* Cₛ[F, S]) (hτ : RightInverse τ (sIdeleClassNorm F S))
variable (γ : Fin d[F] → LCATopologicalLie Cₛ₁[F, S])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := Cₛ₁[F, S]))
variable (μ : Measure Cₛ₁[F, S]) [hμ : μ.IsHaarMeasure]

include hτ hγ hspan hμ

-- TODO(paper-gap): The normalization of the measure in (D.1.10.20) refers
-- to (A.3.4.1)(3), which omits the outside-S unit factors from the numerator.
-- The topology assertions below hold for any Haar measure on the full kernel.

/-- Paper: Proposition D.1.10.10(1), p. 791. For sufficiently small compact
good subgroups, the Lᵖ family with weights one plus powers of the absolute log
S-norm generates the fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property
and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_weightedLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by
  let h := sIdeleClassGroup_openEmbedding F S
  let j : Cₛ[F, S] →ₜ* C[F] := ⟨h.choose, h.choose_spec.1.continuous⟩
  let : CompactSpace Cₛ₁[F, S] := (sIdeleClassGroup_finiteness F S).2.1
  let : CompactSpace C₁[F] := (ideleClassGroup_finiteness F).2.1
  let : BorelSpace Cₛ₁[F, S] := ⟨rfl⟩
  let : MeasurableSpace C[F] := borel _
  let : BorelSpace C[F] := ⟨rfl⟩
  have : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact openEmbedding_weightedStages j h.choose_spec.1 (sIdeleClassNorm F S) (ideleClassNorm F)
    h.choose_spec.2.1 μ (normOneIdeleClassTamagawaMeasure F) τ hτ γ hγ hspan
    (fun τ' hτ' γ' hγ' hs' ↦ ideleClass_weightedLp_generates F τ' hτ' γ' hγ' hs')

/-- Paper: Proposition D.1.10.10(2), p. 791. Powers of the absolute log S-norm
give a generating family on the fixed subspace.
Deviation: The directions satisfy the real basis property and the compact
kernel carries any Haar measure. -/
theorem sIdeleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by
  exact ideleClassStages_mono (G := Cₛ[F, S]) (fun k p hp ↦
    ideleClassStage_logPower (n := sIdeleClassNorm F S) (τ := τ) (γ := γ) (k := k)
      (μ := positiveRealHaar.prod μ) (p := ENNReal.ofReal p)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))
    (sIdeleClass_weightedLp_generates F S τ hτ γ hγ hspan μ)

/-- Paper: Proposition D.1.10.10(3), p. 792. Absolute values of polynomials in
the absolute log S-norm give a generating family on the fixed subspace.
Deviation: The coefficients are complex as in D.1.10.9(3). The directions
satisfy the real basis property and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by
  exact ideleClassStages_mono (G := Cₛ[F, S]) (fun k p hp ↦
    ideleClassStage_logPolynomial (n := sIdeleClassNorm F S) (τ := τ) (γ := γ) (k := k)
      (μ := positiveRealHaar.prod μ) (p := ENNReal.ofReal p)
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp))
    (sIdeleClass_logPowerLp_generates F S τ hτ γ hγ hspan μ)

-- TODO(paper-gap): The equality after D.1.10.10(3) also requires compatible
-- section and Haar choices. Even for identical classes, Haar rescaling changes
-- the seminorms.

end SLocal

end IdeleClassSeminorms

end RiemannMasullo
