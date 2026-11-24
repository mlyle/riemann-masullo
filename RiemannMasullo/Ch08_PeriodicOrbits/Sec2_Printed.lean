module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec2
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # §8.2. Statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField Topology
open scoped NNReal NumberField.AdeleRing

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global norm-one orbit map is a quotient map
for the adelic subspace topology on the target. See ERRATA R12. -/
def Printed.adeleNormOneOrbitMap_isQuotientMap : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], IsQuotientMap (adeleNormOneOrbitMap F)

/-- The base point with zero at an infinite place of ℚ has zero there and finite part 1. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint
    (v : InfinitePlace ℚ) :
    (adeleOrbitBasepoint ℚ (some (.inl v))).1 v = (0 : v.Completion) ∧
      (adeleOrbitBasepoint ℚ (some (.inl v))).2 = 1 := by
  refine ⟨?_, rfl⟩
  change (InfiniteAdeleRing.ofCompletion v (0 : v.Completion)) v = 0
  rw [InfiniteAdeleRing.ofCompletion_apply]
  let := Classical.decEq (InfinitePlace ℚ)
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace ℚ ↦ w.Completion) v 0

/-- Each completion of ℚ at a finite place has a nonzero element of valuation below 1. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_nonunit
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ x : w.adicCompletion ℚ, x ≠ 0 ∧ Valued.v x < 1 := by
  let val : Valuation (w.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨π, hπ.ne_zero, hπ.val_lt_one⟩

/-- Replacing the finite part of the real-zero base point by a finite adele with nonzero
components, almost all of valuation 1, gives a point of the norm-one orbit union. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_mem
    (v : InfinitePlace ℚ) (y : FiniteAdeleRing (𝓞 ℚ) ℚ) (hy : ∀ w, y w ≠ 0)
    (hy' : ∀ᶠ w in Filter.cofinite, Valued.v (y w) = 1) :
    ((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) ∈ adeleNormOneOrbitUnion ℚ := by
  have hu : IsUnit (((1 : InfiniteAdeleRing ℚ), y) : 𝔸[ℚ]) :=
    AdeleRing.isUnit_iff.mpr ⟨fun _ ↦ one_ne_zero, hy, hy'⟩
  refine Set.mem_iUnion.mpr ⟨some (.inl v), ?_⟩
  rw [adeleNormOneOrbit_infinite_eq_full]
  refine ⟨hu.unit, Prod.ext ?_ ?_⟩
  · change (1 : InfiniteAdeleRing ℚ) * (adeleOrbitBasepoint ℚ (some (.inl v))).1 = _
    exact one_mul _
  · change y * (adeleOrbitBasepoint ℚ (some (.inl v))).2 = y
    rw [(Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint v).2, mul_one]

/-- A neighbourhood of an integral finite adele contains every integral finite adele
that agrees with it on a suitable finite set of places. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_nhds
    (y₀ : FiniteAdeleRing (𝓞 ℚ) ℚ) (hy₀ : ∀ w, y₀ w ∈ w.adicCompletionIntegers ℚ)
    (W : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hW : W ∈ 𝓝 y₀) :
    ∃ I : Set (HeightOneSpectrum (𝓞 ℚ)), I.Finite ∧
      ∀ y : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ w, y w ∈ w.adicCompletionIntegers ℚ) →
        (∀ w ∈ I, y w = y₀ w) → y ∈ W := by
  have hc : Continuous (RestrictedProduct.structureMap
      (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ)
      (fun w ↦ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hpre : RestrictedProduct.structureMap
      (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ)
      (fun w ↦ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite ⁻¹' W ∈
      𝓝 (fun w ↦ ⟨y₀ w, hy₀ w⟩) := hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, hI, t, ht, hsub⟩ := hpre
  refine ⟨I, hI, fun y hy hyI ↦ ?_⟩
  refine hsub (a := fun w ↦ ⟨y w, hy w⟩) fun w hw ↦ ?_
  have h2 : (⟨y w, hy w⟩ : (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) =
      ⟨y₀ w, hy₀ w⟩ := Subtype.ext (hyI w hw)
  change (⟨y w, hy w⟩ : (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) ∈ t w
  rw [h2]
  exact mem_of_mem_nhds (ht w)

/-- A base point whose coordinate at the given infinite place differs from 1 has zero
there and finite part 1. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint_ne_one
    (v : InfinitePlace ℚ) (z : 𝔸[ℚ]) (hz : z ∈ adeleOrbitBasepoints ℚ)
    (h : z.1 v ≠ (1 : v.Completion)) : z.1 v = (0 : v.Completion) ∧ z.2 = 1 := by
  obtain ⟨i, rfl⟩ := hz
  rcases i with _ | v' | w
  · exact absurd rfl h
  · obtain rfl : v' = v := Subsingleton.elim _ _
    exact Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint v'
  · exact absurd rfl h

/-- The orbit map pulls the set of points with zero coordinate at the given infinite place
and finite components of valuation 1 back to an open set. -/
private theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false_isOpen
    (v : InfinitePlace ℚ) :
    IsOpen (adeleNormOneOrbitMap ℚ ⁻¹'
      {x | x.val.1 v = (0 : v.Completion) ∧ ∀ w, Valued.v (x.val.2 w) = 1}) := by
  have hI : IsOpen {y : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ w, y w ∈ w.adicCompletionIntegers ℚ} :=
    RestrictedProduct.isOpen_forall_mem fun w ↦ Valued.isOpen_valuationSubring _
  have c1 : Continuous fun p : MonoidHom.ker (ideleNorm ℚ) × adeleOrbitBasepoints ℚ ↦
      (p.2.val.1 v : v.Completion) :=
    (continuous_apply v).comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have c2 : Continuous fun p : MonoidHom.ker (ideleNorm ℚ) × adeleOrbitBasepoints ℚ ↦
      p.1.val.val.2 :=
    continuous_snd.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))
  have c3 : Continuous fun p : MonoidHom.ker (ideleNorm ℚ) × adeleOrbitBasepoints ℚ ↦
      p.1.val.inv.2 :=
    continuous_snd.comp
      (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst))
  have hO := ((isOpen_ne (x := (1 : v.Completion))).preimage c1).inter
    ((hI.preimage c2).inter (hI.preimage c3))
  convert hO using 1
  ext ⟨g, z⟩
  have hgv : g.val.val.1 v * g.val.inv.1 v = (1 : v.Completion) :=
    congrArg (fun x : 𝔸[ℚ] ↦ (x.1 v : v.Completion)) g.val.val_inv
  have hgw (w : HeightOneSpectrum (𝓞 ℚ)) : g.val.val.2 w * g.val.inv.2 w = 1 :=
    congrArg (fun x : 𝔸[ℚ] ↦ x.2 w) g.val.val_inv
  have hab (w : HeightOneSpectrum (𝓞 ℚ)) :
      Valued.v (g.val.val.2 w) * Valued.v (g.val.inv.2 w) = 1 := by
    rw [← map_mul, hgw w, map_one]
  constructor
  · rintro ⟨h1, h2⟩
    change g.val.val.1 v * z.val.1 v = (0 : v.Completion) at h1
    have hz0 : z.val.1 v = (0 : v.Completion) := by
      rcases mul_eq_zero.mp h1 with h | h
      · rw [h, zero_mul] at hgv
        exact absurd hgv zero_ne_one
      · exact h
    have hz1 : z.val.1 v ≠ (1 : v.Completion) := by
      rw [hz0]
      exact zero_ne_one
    have hz := Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint_ne_one v z.val
      z.prop hz1
    have h2' (w : HeightOneSpectrum (𝓞 ℚ)) : Valued.v (g.val.val.2 w) = 1 := by
      have h3 := h2 w
      change Valued.v (g.val.val.2 w * z.val.2 w) = 1 at h3
      rw [hz.2] at h3
      change Valued.v (g.val.val.2 w * 1) = 1 at h3
      rwa [mul_one] at h3
    refine ⟨hz1, fun w ↦ ?_, fun w ↦ ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mpr (h2' w).le
    · have h3 := hab w
      rw [h2' w, one_mul] at h3
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mpr h3.le
  · rintro ⟨h1, h2, h3⟩
    have hz := Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint_ne_one v z.val
      z.prop h1
    refine ⟨?_, fun w ↦ ?_⟩
    · change g.val.val.1 v * z.val.1 v = (0 : v.Completion)
      rw [hz.1, mul_zero]
    · change Valued.v (g.val.val.2 w * z.val.2 w) = 1
      rw [hz.2]
      change Valued.v (g.val.val.2 w * 1) = 1
      rw [mul_one]
      have ha := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mp (h2 w)
      have hb := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mp (h3 w)
      refine le_antisymm ha ?_
      calc (1 : WithZero (Multiplicative ℤ))
          = Valued.v (g.val.val.2 w) * Valued.v (g.val.inv.2 w) := (hab w).symm
        _ ≤ Valued.v (g.val.val.2 w) * 1 := mul_le_mul' le_rfl hb
        _ = Valued.v (g.val.val.2 w) := mul_one _

/-- Paper: Lemma 8.2.0.3(2), p. 385. Over ℚ, let U be the norm-one orbit points
with real component zero and all finite components in the local unit groups.
The preimage of U is open because the real-zero base point is isolated among the
base points and the integral finite ideles form an open subgroup. Replacing the
p-coordinate of the real-zero base point by p gives points outside U that tend
to that base point. They are norm-one translates via ideles with real coordinate p. -/
theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false :
    ¬ Printed.adeleNormOneOrbitMap_isQuotientMap.{0} := by
  intro h
  have hq := h ℚ
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
  have hinf : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_injective _ Rat.HeightOneSpectrum.primesEquiv.symm.injective
  have hU := hq.isOpen_preimage.mp (Printed.adeleNormOneOrbitMap_isQuotientMap_false_isOpen v)
  obtain ⟨W, hW, hWU⟩ := isOpen_induced_iff.mp hU
  have he := Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint v
  have heD : adeleOrbitBasepoint ℚ (some (.inl v)) ∈ adeleNormOneOrbitUnion ℚ :=
    Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩
  have heW : adeleOrbitBasepoint ℚ (some (.inl v)) ∈ W := by
    have h1 : (⟨_, heD⟩ : adeleNormOneOrbitUnion ℚ) ∈ Subtype.val ⁻¹' W := by
      rw [hWU]
      refine ⟨he.1, fun w ↦ ?_⟩
      change Valued.v ((adeleOrbitBasepoint ℚ (some (.inl v))).2 w) = 1
      rw [he.2]
      exact map_one _
    exact h1
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ ↦
      (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) :=
    continuous_const.prodMk continuous_id
  have hW1 : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ ↦
      (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ])) ⁻¹' W ∈
      𝓝 (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine hc.continuousAt.preimage_mem_nhds (hW.mem_nhds ?_)
    rw [← he.2]
    exact heW
  obtain ⟨I, hI, hIW⟩ := Printed.adeleNormOneOrbitMap_isQuotientMap_false_nhds 1
    (fun w ↦ one_mem _) _ hW1
  obtain ⟨w0, hw0⟩ := hI.infinite_compl.nonempty
  obtain ⟨π, hπ0, hπ1⟩ := Printed.adeleNormOneOrbitMap_isQuotientMap_false_nonunit w0
  let := Classical.decEq (HeightOneSpectrum (𝓞 ℚ))
  let y : FiniteAdeleRing (𝓞 ℚ) ℚ := FiniteAdeleRing.ofAdicCompletion ℚ w0 π
  have hy0 : y w0 = π := RestrictedProduct.mulSingle_eq_same
    (A := fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ) w0 π
  have hy1 (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ w0) : y w = 1 :=
    RestrictedProduct.mulSingle_eq_of_ne
      (A := fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ) π hw
  have hyint (w : HeightOneSpectrum (𝓞 ℚ)) : y w ∈ w.adicCompletionIntegers ℚ := by
    by_cases hw : w = w0
    · subst hw
      rw [hy0]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mpr hπ1.le
    · rw [hy1 w hw]
      exact one_mem _
  have hyne (w : HeightOneSpectrum (𝓞 ℚ)) : y w ≠ 0 := by
    by_cases hw : w = w0
    · subst hw
      rw [hy0]
      exact hπ0
    · rw [hy1 w hw]
      exact one_ne_zero
  have hyW : (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) ∈ W :=
    hIW y hyint fun w hw ↦ hy1 w (by rintro rfl; exact hw0 hw)
  have hyD := Printed.adeleNormOneOrbitMap_isQuotientMap_false_mem v y hyne (by
    filter_upwards [Filter.eventually_cofinite_ne w0] with w hw
    rw [hy1 w hw]
    exact map_one _)
  have h2 : (⟨_, hyD⟩ : adeleNormOneOrbitUnion ℚ) ∈ Subtype.val ⁻¹' W := hyW
  rw [hWU] at h2
  have h3 := h2.2 w0
  change Valued.v (y w0) = 1 at h3
  rw [hy0] at h3
  exact hπ1.ne h3

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally
compact in the adelic subspace topology. See ERRATA R13. -/
def Printed.adeleNormOneOrbitUnion_locallyCompactSpace : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], LocallyCompactSpace (adeleNormOneOrbitUnion F)

/-- Every point of the norm-one orbit union over ℚ has finite components of valuation 1
at almost all places. -/
private theorem Printed.adeleNormOneOrbitUnion_locallyCompactSpace_false_unit (x : 𝔸[ℚ])
    (hx : x ∈ adeleNormOneOrbitUnion ℚ) :
    ∀ᶠ w in Filter.cofinite, Valued.v (x.2 w) = 1 := by
  obtain ⟨i, g, rfl⟩ := Set.mem_iUnion.mp hx
  have hg := (AdeleRing.isUnit_iff.mp g.val.isUnit).2.2
  rcases i with _ | v | w0
  · filter_upwards [hg] with w hw
    change Valued.v (g.val.val.2 w * (1 : w.adicCompletion ℚ)) = 1
    rw [mul_one, hw]
  · filter_upwards [hg] with w hw
    change Valued.v (g.val.val.2 w * (1 : w.adicCompletion ℚ)) = 1
    rw [mul_one, hw]
  · filter_upwards [hg, Filter.eventually_cofinite_ne w0] with w hw hne
    change Valued.v (g.val.val.2 w * (FiniteAdeleRing.ofAdicCompletion ℚ w0 0) w) = 1
    have h1 : (FiniteAdeleRing.ofAdicCompletion ℚ w0 (0 : w0.adicCompletion ℚ)) w = 1 := by
      let := Classical.decEq (HeightOneSpectrum (𝓞 ℚ))
      exact RestrictedProduct.mulSingle_eq_of_ne
        (A := fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ)
        (0 : w0.adicCompletion ℚ) hne
    rw [h1, mul_one, hw]

/-- Paper: Lemma 8.2.0.3, p. 385. Over ℚ, take the real-zero base point. In any
basic neighbourhood choose infinitely many distinct unrestricted primes p₁, p₂, …
and replace the components at p₁, …, pₙ by p₁, …, pₙ. These are norm-one translates
using ideles with real coordinate p₁⋯pₙ. Their limit in the adeles has infinitely
many finite nonunit components and lies outside the orbit union. A compact
neighbourhood would be closed in the ambient Hausdorff space and contain this limit. -/
theorem Printed.adeleNormOneOrbitUnion_locallyCompactSpace_false :
    ¬ Printed.adeleNormOneOrbitUnion_locallyCompactSpace.{0} := by
  intro h
  have hlc := h ℚ
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace ℚ))
  have hinf : Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
    Infinite.of_injective _ Rat.HeightOneSpectrum.primesEquiv.symm.injective
  have he := Printed.adeleNormOneOrbitMap_isQuotientMap_false_basepoint v
  have heD : adeleOrbitBasepoint ℚ (some (.inl v)) ∈ adeleNormOneOrbitUnion ℚ :=
    Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩
  obtain ⟨K, hK, hKe⟩ := exists_compact_mem_nhds (⟨_, heD⟩ : adeleNormOneOrbitUnion ℚ)
  obtain ⟨W, hW, hWK⟩ := (mem_nhds_subtype _ _ _).mp hKe
  have hT2 : T2Space 𝔸[ℚ] := by
    change T2Space (((u : InfinitePlace ℚ) → u.Completion) ×
      RestrictedProduct (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ)
        (fun w ↦ (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite)
    infer_instance
  have hKcl : IsClosed (Subtype.val '' K) := (hK.image continuous_subtype_val).isClosed
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ ↦
      (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) :=
    continuous_const.prodMk continuous_id
  have hW1 : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ ↦
      (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ])) ⁻¹' W ∈
      𝓝 (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
    refine hc.continuousAt.preimage_mem_nhds ?_
    rw [← he.2]
    exact hW
  obtain ⟨I₁, hI₁, hI₁W⟩ := Printed.adeleNormOneOrbitMap_isQuotientMap_false_nhds 1
    (fun w ↦ one_mem _) _ hW1
  choose π hπ0 hπ1 using Printed.adeleNormOneOrbitMap_isQuotientMap_false_nonunit
  classical
  have hpint (w : HeightOneSpectrum (𝓞 ℚ)) :
      (if w ∈ I₁ then (1 : w.adicCompletion ℚ) else π w) ∈ w.adicCompletionIntegers ℚ := by
    split_ifs
    · exact one_mem _
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ w).mpr (hπ1 w).le
  let y₀ : FiniteAdeleRing (𝓞 ℚ) ℚ :=
    RestrictedProduct.mk (fun w ↦ if w ∈ I₁ then (1 : w.adicCompletion ℚ) else π w)
      (Filter.Eventually.of_forall hpint)
  have hmemK : (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y₀) : 𝔸[ℚ]) ∈ Subtype.val '' K := by
    by_contra hnot
    have hW2 : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ ↦
        (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ])) ⁻¹' (Subtype.val '' K)ᶜ ∈
        𝓝 y₀ :=
      hc.continuousAt.preimage_mem_nhds (hKcl.isOpen_compl.mem_nhds hnot)
    obtain ⟨I₂, hI₂, hI₂W⟩ := Printed.adeleNormOneOrbitMap_isQuotientMap_false_nhds y₀
      hpint _ hW2
    have hqint (w : HeightOneSpectrum (𝓞 ℚ)) :
        (if w ∈ I₂ then y₀ w else (1 : w.adicCompletion ℚ)) ∈ w.adicCompletionIntegers ℚ := by
      split_ifs
      · exact hpint w
      · exact one_mem _
    let y : FiniteAdeleRing (𝓞 ℚ) ℚ :=
      RestrictedProduct.mk (fun w ↦ if w ∈ I₂ then y₀ w else (1 : w.adicCompletion ℚ))
        (Filter.Eventually.of_forall hqint)
    have h1 : (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) ∉ Subtype.val '' K :=
      hI₂W y hqint fun w hw ↦ ite_eq_left hw
    have h2 : (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) ∈ W := by
      refine hI₁W y hqint fun w hw ↦ ?_
      change (if w ∈ I₂ then (if w ∈ I₁ then (1 : w.adicCompletion ℚ) else π w) else 1) = 1
      rw [ite_eq_left hw, ite_self]
    have h3 : (((adeleOrbitBasepoint ℚ (some (.inl v))).1, y) : 𝔸[ℚ]) ∈
        adeleNormOneOrbitUnion ℚ := by
      refine Printed.adeleNormOneOrbitMap_isQuotientMap_false_mem v y (fun w ↦ ?_) ?_
      · change (if w ∈ I₂ then (if w ∈ I₁ then (1 : w.adicCompletion ℚ) else π w) else 1) ≠ 0
        split_ifs
        · exact one_ne_zero
        · exact hπ0 w
        · exact one_ne_zero
      · have hfin : ∀ᶠ w in Filter.cofinite, w ∉ I₂ := hI₂.compl_mem_cofinite
        filter_upwards [hfin] with w hw
        change Valued.v (if w ∈ I₂ then y₀ w else (1 : w.adicCompletion ℚ)) = 1
        rw [ite_eq_right hw]
        exact map_one _
    exact h1 ⟨⟨_, h3⟩, hWK h2, rfl⟩
  obtain ⟨x, -, hx⟩ := hmemK
  have hunit := Printed.adeleNormOneOrbitUnion_locallyCompactSpace_false_unit x.val x.prop
  rw [hx] at hunit
  refine hI₁.infinite_compl ((Filter.eventually_cofinite.mp hunit).subset fun w hw ↦ ?_)
  change ¬ Valued.v (if w ∈ I₁ then (1 : w.adicCompletion ℚ) else π w) = 1
  rw [ite_eq_right hw]
  exact (hπ1 w).ne

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point of the full S-local
finite-place orbit admits a full-idele transporter into the half-open section,
unique up to embedded local valuation-ring units. See ERRATA R1. -/
def Printed.sAdeleFiniteOrbit_transporter : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (v : S)
    (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ), Continuous τ → RightInverse τ (sIdeleNorm F S) →
    ∀ x ∈ sAdeleFullOrbit F S (some (.inr v)),
      ∃ g : (SAdeleRing F S)ˣ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
        ∀ h : (SAdeleRing F S)ˣ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
          g⁻¹ * h ∈ (embeddedFiniteLocalUnits F v.val).map
            (Units.map (adeleProjection F S).toMonoidHom)

/-- Paper: Proposition 8.2.0.4(1), p. 386. Over ℚ take the real and 2-adic places,
the section t ↦ (t, 1), and x = (1, 0). Both (1, 1) and (1, 2) are transporters
because they fix x and x is at the included left endpoint. Their ratio has
2-adic component 2, which fails to be a valuation-ring unit. -/
theorem Printed.sAdeleFiniteOrbit_transporter_false :
    ¬ Printed.sAdeleFiniteOrbit_transporter.{0} := by
  intro h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField ℚ)⟩
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v}
  let vS : S := ⟨v, Finset.mem_singleton_self v⟩
  let proj : 𝔸[ℚ]ˣ →* (SAdeleRing ℚ S)ˣ := Units.map (adeleProjection ℚ S).toMonoidHom
  let τ : ℝ≥0ˣ →* (SAdeleRing ℚ S)ˣ := proj.comp ratIdeleNormSection
  have hτ_cont : Continuous τ :=
    ((continuous_fst.prodMk (continuous_pi fun w : S ↦
      (RestrictedProduct.continuous_eval w.val).comp continuous_snd)).units_map
      (adeleProjection ℚ S).toMonoidHom).comp ratIdeleNormSection_continuous
  have hτ_rinv : RightInverse τ (sIdeleNorm ℚ S) := by
    intro t
    have hmem (y : 𝔸[ℚ]) (hy : ∀ w : HeightOneSpectrum (𝓞 ℚ), y.2 w = 1) :
        y ∈ integralAdelesOutside ℚ S := by
      delta integralAdelesOutside
      rw [Subring.mem_iInf]
      intro w
      rw [Subring.mem_iInf]
      intro _
      change y.2 w ∈ w.adicCompletionIntegers ℚ
      rw [hy w]
      exact (w.adicCompletionIntegers ℚ).one_mem
    let uval : integralAdelesOutside ℚ S := ⟨(ratIdeleNormSection t).val, hmem _ fun _ ↦ rfl⟩
    let uinv : integralAdelesOutside ℚ S := ⟨(ratIdeleNormSection t).inv, hmem _ fun _ ↦ rfl⟩
    let u : (integralAdelesOutside ℚ S)ˣ :=
      ⟨uval, uinv, Subtype.ext (ratIdeleNormSection t).val_inv,
        Subtype.ext (ratIdeleNormSection t).inv_val⟩
    have h1 : Units.map (integralAdelesOutside ℚ S).subtype.toMonoidHom u =
        ratIdeleNormSection t := Units.ext rfl
    have h2 : Units.map ((adeleProjection ℚ S).comp
        (integralAdelesOutside ℚ S).subtype).toMonoidHom u = τ t := Units.ext rfl
    rw [← h2, ← (sIdeleNorm_spec ℚ S).1 u, h1]
    exact ratIdeleNormSection_rightInverse t
  obtain ⟨g, hg, huniq⟩ := h ℚ S vS τ hτ_cont hτ_rinv
    (sAdeleOrbitBasepoint ℚ S (some (.inr vS))) (MulAction.mem_orbit_self _)
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (v.adicCompletion ℚ)ˣ := Units.mk0 (π : v.adicCompletion ℚ) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion ℚ)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  let e₀ : 𝔸[ℚ]ˣ := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u
  let e : (SAdeleRing ℚ S)ˣ := proj e₀
  have hfix : e⁻¹ • sAdeleOrbitBasepoint ℚ S (some (.inr vS)) =
      sAdeleOrbitBasepoint ℚ S (some (.inr vS)) := by
    rw [Units.smul_def, ← map_inv]
    change adeleProjection ℚ S
        (AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : _)) *
        adeleProjection ℚ S (AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v 0) =
      adeleProjection ℚ S (AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v 0)
    rw [← map_mul, ← map_mul, mul_zero]
  have hmem := huniq (g * e) (by
    rw [mul_inv, mul_smul, hfix]
    exact hg)
  rw [inv_mul_cancel_left] at hmem
  obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hmem
  rw [mem_embeddedFiniteLocalUnits_iff] at hk
  obtain ⟨_, hn, _⟩ := hk
  have hkv : k.val.2 v = (u : v.adicCompletion ℚ) := by
    have hc := congrArg (fun z : (SAdeleRing ℚ S)ˣ ↦ z.val.2 vS) hke
    change k.val.2 v = e₀.val.2 v at hc
    rw [hc]
    change (FiniteAdeleRing.ofAdicCompletion ℚ v (u : v.adicCompletion ℚ)) v = _
    let := Classical.decEq (HeightOneSpectrum (𝓞 ℚ))
    exact RestrictedProduct.mulSingle_eq_same
      (A := fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ) v
      (u : v.adicCompletion ℚ)
  rw [hkv, hnorm] at hn
  have h1 : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have : (v.asIdeal.absNorm : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point of the full global
finite-place orbit admits a full-idele transporter into the half-open section,
unique up to embedded local valuation-ring units. See ERRATA R1. -/
def Printed.adeleFiniteOrbit_transporter : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ), Continuous τ → RightInverse τ (ideleNorm F) →
    ∀ x ∈ adeleFullOrbit F (some (.inr v)),
      ∃ g : 𝔸[F]ˣ, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
        ∀ h : 𝔸[F]ˣ, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
          g⁻¹ * h ∈ embeddedFiniteLocalUnits F v

/-- Paper: Proposition 8.2.0.4(2), p. 386. Over ℚ take the norm section with real
coordinate t and finite coordinates 1, and take x to be the 2-adic-zero base
point. Both 1 and the idele with 2-adic coordinate 2 and all other coordinates 1
fix x at the included left endpoint. Their ratio is outside the embedded local
valuation-ring units. -/
theorem Printed.adeleFiniteOrbit_transporter_false :
    ¬ Printed.adeleFiniteOrbit_transporter.{0} := by
  intro h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField ℚ)⟩
  obtain ⟨g, hg, huniq⟩ := h ℚ v (canonicalIdeleNormSection ℚ)
    (canonicalIdeleNormSection_continuous ℚ) (canonicalIdeleNormSection_rightInverse ℚ)
    (adeleOrbitBasepoint ℚ (some (.inr v))) (MulAction.mem_orbit_self _)
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (v.adicCompletion ℚ)ˣ := Units.mk0 (π : v.adicCompletion ℚ) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion ℚ)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  let e : 𝔸[ℚ]ˣ := IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u
  have hfix : e⁻¹ • adeleOrbitBasepoint ℚ (some (.inr v)) =
      adeleOrbitBasepoint ℚ (some (.inr v)) := by
    rw [Units.smul_def, ← map_inv]
    change AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : _) *
        AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v 0 = AdeleRing.ofAdicCompletion (𝓞 ℚ) ℚ v 0
    rw [← map_mul, mul_zero]
  have hmem := huniq (g * e) (by
    rw [mul_inv, mul_smul, hfix]
    exact hg)
  rw [inv_mul_cancel_left, mem_embeddedFiniteLocalUnits_iff] at hmem
  obtain ⟨_, hn, _⟩ := hmem
  have he : e.val.2 v = (u : v.adicCompletion ℚ) := by
    change (FiniteAdeleRing.ofAdicCompletion ℚ v (u : v.adicCompletion ℚ)) v = _
    let := Classical.decEq (HeightOneSpectrum (𝓞 ℚ))
    exact RestrictedProduct.mulSingle_eq_same
      (A := fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletionIntegers ℚ) v
      (u : v.adicCompletion ℚ)
  rw [he, hnorm] at hn
  have h1 : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have : (v.asIdeal.absNorm : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  linarith

end RiemannMasullo
