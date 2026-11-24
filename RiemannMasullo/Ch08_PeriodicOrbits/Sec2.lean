module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.GDelta

/-! # §8.2. Stack-theoretic periodic orbits and fixed points

The parameter `S` records the finite part of the paper's set of places. Every
infinite place is already included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField TopologicalSpace Topology
open scoped NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point $e_v$ has zero at $v$
and one elsewhere. The index `none` denotes the ordinary base point 1. -/
def adeleOrbitBasepoint : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) → 𝔸[F]
  | none => 1
  | some (.inl v) => AdeleRing.ofCompletion (𝓞 F) F v 0
  | some (.inr v) => AdeleRing.ofAdicCompletion (𝓞 F) F v 0

/-- Paper: Definition 8.2.0.1(1), p. 384. Coordinate formulas for the global base points. -/
theorem adeleOrbitBasepoint_coordinates :
    adeleOrbitBasepoint F none = 1 ∧
      (∀ v : InfinitePlace F,
        (adeleOrbitBasepoint F (some (.inl v))).1 v = 0 ∧
        (∀ w : InfinitePlace F, w ≠ v → (adeleOrbitBasepoint F (some (.inl v))).1 w = 1) ∧
        (adeleOrbitBasepoint F (some (.inl v))).2 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (adeleOrbitBasepoint F (some (.inr v))).1 = 1 ∧
        (adeleOrbitBasepoint F (some (.inr v))).2 v = 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
          (adeleOrbitBasepoint F (some (.inr v))).2 w = 1) := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The S-local base points keep all infinite
places and the finite places in S. -/
def sAdeleOrbitBasepoint (i : Option (InfinitePlace F ⊕ S)) : Aₛ :=
  adeleProjection F S (adeleOrbitBasepoint F (i.map (Sum.map id Subtype.val)))

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point at a selected finite place
has zero at that place, including after projection to the S-adeles. -/
theorem sAdeleOrbitBasepoint_finite (v : S) :
    (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0 := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_{F,S}$ in (8.2.0.1)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def sAdeleOrbitBasepoints : Set Aₛ :=
  Set.range (sAdeleOrbitBasepoint F S)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_{F,S}$. -/
theorem one_mem_sAdeleOrbitBasepoints : 1 ∈ sAdeleOrbitBasepoints F S := by
  sorry

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_F$ in (8.2.0.2)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def adeleOrbitBasepoints : Set 𝔸[F] :=
  Set.range (adeleOrbitBasepoint F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_F$. -/
theorem one_mem_adeleOrbitBasepoints : 1 ∈ adeleOrbitBasepoints F := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.3) consists of the
S-local full-idele orbits with their adelic subspace topologies. -/
def sAdeleFullOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit 𝕀ₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary S-local orbit consists of
the $S$-adeles that are units. -/
theorem mem_sAdeleFullOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbit F S none ↔ IsUnit x := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.4) consists of the
global full-idele orbits with their adelic subspace topologies. -/
def adeleFullOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) : Set 𝔸[F] :=
  MulAction.orbit 𝔸[F]ˣ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary global orbit consists of
the adeles that are units. -/
theorem mem_adeleFullOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbit F none ↔ IsUnit x := by
  sorry

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local set $D_{F,S}$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def sAdeleFullOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleFullOrbit F S i

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local full-orbit union is the
set of translates of the special S-adeles by full ideles. -/
theorem mem_sAdeleFullOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbitUnion F S ↔
      ∃ (g : 𝕀ₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  sorry

/-- Paper: Definition 8.2.0.1(3), p. 385. The global set $D_F$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def adeleFullOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleFullOrbit F i

/-- Paper: Definition 8.2.0.1(3), p. 385. The global full-orbit union is the
set of translates of the special adeles by full ideles. -/
theorem mem_adeleFullOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbitUnion F ↔
      ∃ (g : 𝔸[F]ˣ) (z : adeleOrbitBasepoints F), g • z.val = x := by
  sorry

-- Read the full-group stability sentence on p. 385 with (8.2.0.3)–(8.2.0.5).
-- The norm-one orbits in (8.2.0.6)–(8.2.0.8) are stable under the norm kernel.

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.6) consists of the
S-local norm-one orbits with their adelic subspace topologies. -/
def sAdeleNormOneOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit Nₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary S-local norm-one orbit
is the image of the norm kernel in the S-adeles. -/
theorem mem_sAdeleNormOneOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbit F S none ↔
      ∃ g : 𝕀ₛ, sIdeleNorm F S g = 1 ∧ g.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.7) consists of the
global norm-one orbits with their adelic subspace topologies. -/
def adeleNormOneOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    Set 𝔸[F] :=
  MulAction.orbit N₁ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary global norm-one orbit is the
image of the norm kernel in the adeles. -/
theorem mem_adeleNormOneOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbit F none ↔ ∃ g : 𝔸[F]ˣ, ideleNorm F g = 1 ∧ g.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(2), p. 385. The S-local set $D^1_{F,S}$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def sAdeleNormOneOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleNormOneOrbit F S i

/-- Paper: Definition 8.2.0.2(2), p. 385. An S-adele lies in the union exactly when
it is a norm-one translate of a special S-adele. -/
theorem mem_sAdeleNormOneOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbitUnion F S ↔
      ∃ (g : Nₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  sorry

/-- Paper: Definition 8.2.0.2(2), p. 385. The global set $D^1_F$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def adeleNormOneOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleNormOneOrbit F i

/-- Paper: Definition 8.2.0.2(2), p. 385. An adele lies in the union exactly when
it is a norm-one translate of a special adele. -/
theorem mem_adeleNormOneOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbitUnion F ↔
      ∃ (g : N₁) (z : adeleOrbitBasepoints F), g • z.val = x := by
  sorry

/-- Paper: Lemma 8.2.0.3(1), p. 385. The S-local orbit map applies the norm-one
idele to the given special S-adele. -/
def sAdeleNormOneOrbitMap (gz : Nₛ × sAdeleOrbitBasepoints F S) :
    sAdeleNormOneOrbitUnion F S :=
  ⟨gz.1 • gz.2.val, (mem_sAdeleNormOneOrbitUnion_iff F S _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The underlying S-adele of the orbit map
is given by the norm-one action. -/
theorem sAdeleNormOneOrbitMap_val (g : Nₛ) (z : sAdeleOrbitBasepoints F S) :
    (sAdeleNormOneOrbitMap F S (g, z)).val = g • z.val := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map applies the norm-one
idele to the given special adele. -/
def adeleNormOneOrbitMap (gz : N₁ × adeleOrbitBasepoints F) : adeleNormOneOrbitUnion F :=
  ⟨gz.1 • gz.2.val, (mem_adeleNormOneOrbitUnion_iff F _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The underlying adele of the orbit map is
given by the norm-one action. -/
theorem adeleNormOneOrbitMap_val (g : N₁) (z : adeleOrbitBasepoints F) :
    (adeleNormOneOrbitMap F (g, z)).val = g • z.val := by
  sorry

/-- Paper: Lemma 8.2.0.3(1), p. 385. The adelic subspace topology on the S-local
norm-one orbit union is the quotient topology of the S-local orbit map. -/
theorem sAdeleNormOneOrbitMap_isQuotientMap : IsQuotientMap (sAdeleNormOneOrbitMap F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is continuous for the
adelic subspace topology on the target.
Deviation: The adelic subspace topology is coarser than the quotient topology.
The equality of topologies fails by ERRATA R12. -/
theorem adeleNormOneOrbitMap_continuous : Continuous (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. Every point in the global norm-one orbit union
has a preimage under the orbit map. -/
theorem adeleNormOneOrbitMap_surjective : Surjective (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is an open quotient map
for its coinduced topology.
Deviation: The target carries the quotient topology of the global orbit map.
ERRATA R12 distinguishes this topology from the adelic subspace topology. -/
theorem adeleNormOneOrbitMap_isOpenQuotientMap :
    @IsOpenQuotientMap _ _ inferInstance
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance)
      (adeleNormOneOrbitMap F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is Hausdorff. -/
theorem sAdeleNormOneOrbitUnion_t2Space : T2Space (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is Hausdorff. -/
theorem adeleNormOneOrbitUnion_t2Space : T2Space (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is metrizable. -/
theorem sAdeleNormOneOrbitUnion_metrizableSpace :
    MetrizableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is metrizable. -/
theorem adeleNormOneOrbitUnion_metrizableSpace : MetrizableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is second-countable. -/
theorem sAdeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is second-countable. -/
theorem adeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is perfectly normal. -/
theorem sAdeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is perfectly normal. -/
theorem adeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is separable. -/
theorem sAdeleNormOneOrbitUnion_separableSpace : SeparableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is separable. -/
theorem adeleNormOneOrbitUnion_separableSpace : SeparableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is locally compact. -/
theorem sAdeleNormOneOrbitUnion_locallyCompactSpace :
    LocallyCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally compact
in the quotient topology of the orbit map.
Deviation: The adelic subspace topology fails to be locally compact by ERRATA R13. -/
theorem adeleNormOneOrbitUnion_locallyCompactSpace :
    @LocallyCompactSpace (adeleNormOneOrbitUnion F)
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is σ-compact. -/
theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is σ-compact
in the adelic subspace topology. -/
theorem adeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is paracompact. -/
theorem sAdeleNormOneOrbitUnion_paracompactSpace :
    ParacompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is paracompact. -/
theorem adeleNormOneOrbitUnion_paracompactSpace : ParacompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Proposition 8.2.0.4, p. 386. The subgroup of global ideles obtained by
inserting the units of the local valuation ring at the specified finite place. -/
def embeddedFiniteLocalUnits (v : HeightOneSpectrum (𝓞 F)) : Subgroup 𝔸[F]ˣ :=
  ((IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)).range

/-- Paper: Proposition 8.2.0.4, p. 386. The inserted local units have norm one at
the specified place and value one at all other places. -/
theorem mem_embeddedFiniteLocalUnits_iff (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g ∈ embeddedFiniteLocalUnits F v ↔
      g.val.1 = 1 ∧ ‖g.val.2 v‖ = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → g.val.2 w = 1 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = 1
      rw [AdeleRing.ofAdicCompletion_apply]
    · have h := FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val v
      have hval := h.trans (Pi.mulSingle_eq_same v _)
      refine (congrArg norm hval).trans ?_
      rw [Valued.toNormedField.norm_eq_one_iff]
      exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := F) (v := v)).mp u.isUnit
    · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans
        (Pi.mulSingle_eq_of_ne (i := v) (i' := w) hw _)
  · rintro ⟨h1, h2, h3⟩
    let x : v.adicCompletion F := g.val.2 v
    have hxval : Valued.v x = 1 := Valued.toNormedField.norm_eq_one_iff.mp h2
    have hxne : x ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hxval]; exact one_ne_zero)
    have hxm : x ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxval]
    have hxim : x⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hxval, inv_one]
    let u : (v.adicCompletionIntegers F)ˣ :=
      Units.mk ⟨x, hxm⟩ ⟨x⁻¹, hxim⟩
        (Subtype.ext (mul_inv_cancel₀ hxne)) (Subtype.ext (inv_mul_cancel₀ hxne))
    refine ⟨u, Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext F fun w => ?_))⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = g.val.1
      rw [AdeleRing.ofAdicCompletion_apply, h1]
    · refine (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans ?_
      obtain rfl | hw := eq_or_ne w v
      · exact Pi.mulSingle_eq_same _ _
      · rw [Pi.mulSingle_eq_of_ne hw, h3 w hw]

/-- Paper: Equation (8.2.0.9), p. 386. The S-local section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def sAdeleFiniteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) : Set Aₛ :=
  (fun t : ℝ≥0ˣ ↦ τ t • sAdeleOrbitBasepoint F S (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.9), p. 386. The included left endpoint gives the S-local
single-zero base point. -/
theorem sAdeleOrbitBasepoint_mem_finiteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) :
    sAdeleOrbitBasepoint F S (some (.inr v)) ∈ sAdeleFiniteOrbitSection F S v τ := by
  sorry

/-- Paper: Equation (8.2.0.10), p. 386. The global section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def adeleFiniteOrbitSection (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    Set 𝔸[F] :=
  (fun t : ℝ≥0ˣ ↦ τ t • adeleOrbitBasepoint F (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.10), p. 386. The included left endpoint gives the global
single-zero base point. -/
theorem adeleOrbitBasepoint_mem_finiteOrbitSection (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    adeleOrbitBasepoint F (some (.inr v)) ∈ adeleFiniteOrbitSection F v τ := by
  sorry

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point in the full S-local finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem sAdeleFiniteOrbit_transporter (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) (hτ : Continuous τ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : Aₛ)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
      ∀ h : Nₛ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
        g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
          (Units.map (adeleProjection F S).toMonoidHom) := by
  sorry

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point in the full global finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem adeleFiniteOrbit_transporter (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ)
    (hτ : Continuous τ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
      ∀ h : N₁, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
        g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  sorry

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full S-local orbit is
already the norm-one orbit of the distinguished base point. -/
theorem sAdeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    sAdeleNormOneOrbit F S (some (.inl v)) = sAdeleFullOrbit F S (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let s := singlePlaceIdeleNormSection F v
    let p := Units.map (adeleProjection F S).toMonoidHom
    have hτ (t : ℝ≥0ˣ) : sIdeleNorm F S (p (s t)) = t := by
      let A := integralAdelesOutside F S
      have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
        change (s u).val ∈ integralAdelesOutside F S
        delta integralAdelesOutside
        rw [Subring.mem_iInf]
        intro w
        rw [Subring.mem_iInf]
        intro _
        exact (w.adicCompletionIntegers F).one_mem
      have ht : s t ∈ A.toSubmonoid.units :=
        ⟨hmem t, by
          change ((s t)⁻¹).val ∈ A
          rw [← map_inv]
          exact hmem t⁻¹⟩
      let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
      exact ((sIdeleNorm_spec F S).1 g).symm.trans
        (singlePlaceIdeleNormSection_rightInverse F v t)
    let c := p (s (sIdeleNorm F S g)⁻¹)
    have hfix : c • sAdeleOrbitBasepoint F S (some (.inl v)) =
        sAdeleOrbitBasepoint F S (some (.inl v)) := by
      rw [Units.smul_def]
      change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (sIdeleNorm F S g)⁻¹).val) *
          adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
      rw [← map_mul, ← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hτ, mul_inv_cancel]
    · change (g * c) • sAdeleOrbitBasepoint F S (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full global orbit is
already the norm-one orbit of the distinguished base point. -/
theorem adeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    adeleNormOneOrbit F (some (.inl v)) = adeleFullOrbit F (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let c := singlePlaceIdeleNormSection F v (ideleNorm F g)⁻¹
    have hc : ideleNorm F c = (ideleNorm F g)⁻¹ :=
      singlePlaceIdeleNormSection_rightInverse F v _
    have hfix : c • adeleOrbitBasepoint F (some (.inl v)) =
        adeleOrbitBasepoint F (some (.inl v)) := by
      rw [Units.smul_def]
      change AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (ideleNorm F g)⁻¹).val *
          AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0
      rw [← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hc, mul_inv_cancel]
    · change (g * c) • adeleOrbitBasepoint F (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- The idele inserted at an infinite place has norm one exactly when the inserted
unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    ideleNorm F (IdeleGroup.ofCompletion (𝓞 F) F v u) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  classical
  rw [Units.ext_iff, Units.val_one, ← NNReal.coe_eq_one, ((ideleNorm_spec F).1 _).2]
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v (u : v.Completion) w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = 1 ↔ _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · exact pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_pos.ne'
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- At a real place the units of norm one are the two signs. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_unit (v : InfinitePlace F)
    (hv : v.IsReal) (u : v.Completionˣ) : ‖u.val‖ = 1 ↔ (u.val = 1 ∨ u.val = -1) := by
  let φ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
  rw [← hiso.norm_map_of_map_zero (map_zero φ) u.val, Real.norm_eq_abs, abs_eq zero_le_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (hiso.injective (h.trans (map_one φ).symm))
    · exact Or.inr (hiso.injective (h.trans (by rw [map_neg, map_one])))
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, map_neg, map_one])

/-- An S-idele fixes the S-local base point at an infinite place exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inl v)) = sAdeleOrbitBasepoint F S (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : ∀ w : S, g.val.2 w = 1 := by
      intro w
      have hc := congrFun (congrArg Prod.snd h) w
      change g.val.2 w * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))⟩
    · change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
    · change g.val.2 w = 1
      exact h2 w
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v u.val) *
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
      adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projected idele inserted at an infinite place has S-norm one exactly when the
inserted unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofCompletion (𝓞 F) F v u)) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofCompletion (𝓞 F) F v
  have hmem (y : v.Completionˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro w
    rw [Subring.mem_iInf]
    intro _
    exact (w.adicCompletionIntegers F).one_mem
  have ht : s u ∈ A.toSubmonoid.units :=
    ⟨hmem u, by
      change ((s u)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem u⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s u, ht⟩
  have hg : sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (s u)) =
      ideleNorm F (s u) := ((sIdeleNorm_spec F S).1 g).symm
  rw [hg]
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u

/-- At an infinite place the S-local norm-one stabilizer of an orbit point consists of
the projected ideles inserted at that place with a unit of norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : SAdeleRing F S) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v)))
    (g : (SAdeleRing F S)ˣ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  obtain ⟨h, rfl⟩ := hx
  change sIdeleNorm F S g = 1 ∧ g • h • sAdeleOrbitBasepoint F S (some (.inl v)) =
    h • sAdeleOrbitBasepoint F S (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    sAdeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the S-local orbit is the image of the two local signs. -/
theorem sAdeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  rw [sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- A global idele fixes the base point at an infinite place exactly when it is inserted
at that place. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inl v)) = adeleOrbitBasepoint F (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0 at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : g.val.2 = 1 := by
      have hc := congrArg Prod.snd h
      change g.val.2 * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) h2)⟩
    change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofCompletion (𝓞 F) F v u.val * AdeleRing.ofCompletion (𝓞 F) F v 0 =
      AdeleRing.ofCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- At an infinite place the global norm-one stabilizer of an orbit point consists of
the ideles inserted at that place with a unit of norm one. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧ g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  obtain ⟨h, rfl⟩ := hx
  change ideleNorm F g = 1 ∧ g • h • adeleOrbitBasepoint F (some (.inl v)) =
    h • adeleOrbitBasepoint F (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    adeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the global orbit is the image of the two local signs. -/
theorem adeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  rw [adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the S-local orbit is the image of the local unit circle. -/
theorem sAdeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the global orbit is the image of the local unit circle. -/
theorem adeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  exact adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g

/-- Paper: Proposition 8.2.0.6(1), p. 387. The closure of the positive section ray
relative to the S-local full-orbit union adds the single-zero base point. -/
theorem sAdeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set Aₛ := Set.range fun t : ℝ≥0ˣ ↦
      adeleProjection F S (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ sAdeleFullOrbitUnion F S =
      ray ∪ {sAdeleOrbitBasepoint F S (some (.inl v))} := by
  sorry

/-- Paper: Proposition 8.2.0.6(2), p. 387. The closure of the positive section ray
relative to the global full-orbit union adds the single-zero base point. -/
theorem adeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set 𝔸[F] := Set.range fun t : ℝ≥0ˣ ↦ (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ adeleFullOrbitUnion F = ray ∪ {adeleOrbitBasepoint F (some (.inl v))} := by
  sorry

end RiemannMasullo
