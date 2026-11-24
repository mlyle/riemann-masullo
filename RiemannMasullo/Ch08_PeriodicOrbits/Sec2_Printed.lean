module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec2
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # §8.2. Statements that are false as printed -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField Topology
open scoped NNReal NumberField.AdeleRing

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global norm-one orbit map is a quotient map
for the adelic subspace topology on the target. See ERRATA R12. -/
def Printed.adeleNormOneOrbitMap_isQuotientMap : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], IsQuotientMap (adeleNormOneOrbitMap F)

/-- Paper: Lemma 8.2.0.3(2), p. 385. Over ℚ, let U be the norm-one orbit points
with real component zero and all finite components in the local unit groups.
The preimage of U is open because the real-zero base point is isolated among the
base points and the integral finite ideles form an open subgroup. Replacing the
p-coordinate of the real-zero base point by p gives points outside U that tend
to that base point. They are norm-one translates via ideles with real coordinate p. -/
theorem Printed.adeleNormOneOrbitMap_isQuotientMap_false :
    ¬ Printed.adeleNormOneOrbitMap_isQuotientMap.{0} := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally
compact in the adelic subspace topology. See ERRATA R13. -/
def Printed.adeleNormOneOrbitUnion_locallyCompactSpace : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F], LocallyCompactSpace (adeleNormOneOrbitUnion F)

/-- Paper: Lemma 8.2.0.3, p. 385. Over ℚ, take the real-zero base point. In any
basic neighbourhood choose infinitely many distinct unrestricted primes p₁, p₂, …
and replace the components at p₁, …, pₙ by p₁, …, pₙ. These are norm-one translates
using ideles with real coordinate p₁⋯pₙ. Their limit in the adeles has infinitely
many finite nonunit components and lies outside the orbit union. A compact
neighbourhood would be closed in the ambient Hausdorff space and contain this limit. -/
theorem Printed.adeleNormOneOrbitUnion_locallyCompactSpace_false :
    ¬ Printed.adeleNormOneOrbitUnion_locallyCompactSpace.{0} := by
  sorry

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
