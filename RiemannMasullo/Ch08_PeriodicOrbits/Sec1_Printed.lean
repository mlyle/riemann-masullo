module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec1

/-! # Printed claims from §8.1 that fail -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set
open scoped BigOperators NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 1000000

universe u

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "PicTrivial(" F ", " S ")" => Subsingleton (CommRing.Pic ((S : Set V(F)).integer F))
local notation "fullFibre(" S ", " p ")" => (∀ v ∉ S, HeightOneSpectrum.under (𝓞 ℚ) v ≠ p)
local notation "zeroExtension(" g ")" => Function.extend Units.val g (fun _ ↦ 0)

local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "res(" F ", " χ ")" => (χ : PontryaginDual C(F)).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C(F))

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
The projective tensor product identifies by pointwise multiplication with a closed
subspace of the additive tests. The predicate specifies what is claimed of that subspace.
The tensor factors are grouped in the order archimedean, punctured, additive, using the
canonical permutation in (8.1.0.4). -/
def Printed.orbitalSupportTensorImage {F : Type u} [Field F] [NumberField F]
    (S T : Finset V(F)) (claim : Submodule ℂ ℬ(SAdeleRing F S) → Prop) : Prop :=
  let A := ↥(sLocalOrbitalArchimedeanFlatTests F)
  let H := FiniteProjectiveTensor (fun v : {v : S // v.val ∉ T} ↦
    SchwartzBruhat (v.val.val.adicCompletion F)ˣ)
  let G := FiniteProjectiveTensor (fun v : {v : S // v.val ∈ T} ↦ ℬ(v.val.val.adicCompletion F))
  ∃ U : Submodule ℂ ℬ(SAdeleRing F S), IsClosed (U : Set ℬ(SAdeleRing F S)) ∧
    (∃ e : ProjectiveTensor (ProjectiveTensor A H) G ≃L[ℂ] U,
      ∀ (a : A) (h : ∀ v : {v : S // v.val ∉ T}, SchwartzBruhat (v.val.val.adicCompletion F)ˣ)
        (g : ∀ v : {v : S // v.val ∈ T}, ℬ(v.val.val.adicCompletion F)) (x : SAdeleRing F S),
        (e ((show ProjectiveTensor A H from a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, h v)) ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))).val
            (Multiplicative.ofAdd x) = a.val (Multiplicative.ofAdd x.1) *
          (∏ v : {v : S // v.val ∉ T}, zeroExtension(h v) (x.2 v.val)) *
          (∏ v : {v : S // v.val ∈ T}, g v (Multiplicative.ofAdd (x.2 v.val)))) ∧ claim U

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The inclusion of the displayed tensor subspace induces an equivalence modulo principal
value on homogeneous theta classes. Its action on representatives specifies the map.
Deviation: Both source denominators use the source numerator, as in the intersection on
p. 384. Literally (8.1.0.1) has a global denominator and (8.1.0.3) has a free index p. -/
def Printed.orbitalSupportQuotientEquiv {F : Type u} [Field F] [NumberField F]
    {S T : Finset V(F)} (hT : T ⊆ S) (η : PontryaginDual J₁(F, S))
    (U : Submodule ℂ ℬ(SAdeleRing F S)) : Prop :=
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S η
  let P := sAdelePrincipalValue F hT
  let D := (sLocalHomogeneousThetaPrincipalValue hT η).range
  ∃ h : ∀ f : U, P f.val ∈ U,
    let P' := LinearMap.codRestrict U (P.domRestrict U) h
    let R := (θ.domRestrict U).ker ⊔ P'.range
    ∃ e : (↥U ⧸ R) ≃L[ℂ] (SLocalHomogeneousThetaSpace F S η ⧸ D),
      ∀ f : U, e (R.mkQ f) = D.mkQ (θ.ker.mkQ f.val)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
The printed tensor product with full multiplicative factors off the primary fibre
embeds as a closed subspace of the additive tests with its projective tensor topology. -/
def Printed.sLocalPrimaryOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)), NormOneCharacterUnramifiedOutside (res(F, χ)) S →
      Printed.orbitalSupportTensorImage S (sLocalPrimaryPlaces S p) (fun _ ↦ True)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
Use ℚ with S = {∞, 2, 3}, p = 2 and the trivial character. Use a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the multiplicative 3-adic
test h(3ᵏu) = exp(−k²) for k ∈ ℤ and u ∈ ℤ₃ˣ. At a point where the real test is
nonzero and the 2-adic coordinate is 1, the zero extension of the product fails
local constancy at the 3-adic origin. See ERRATA R11. -/
theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportTests_inclusion.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
The printed tensor product with full multiplicative factors away from v embeds
as a closed subspace of the additive tests with its projective tensor topology. -/
def Printed.sLocalPlaceOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)), NormOneCharacterUnramifiedOutside (res(F, χ)) S →
      Printed.orbitalSupportTensorImage S {v.val} (fun _ ↦ True)

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
Use ℚ with S = {∞, 2, 3}, v = 2 and the trivial character. Take a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the unit-invariant
3-adic test with profile k ↦ exp(−k²). The 3-adic slice is nonzero on 3ᵏ for
every k, but zero at the origin, so it fails local constancy there. -/
theorem Printed.sLocalPlaceOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPlaceOrbitalSupportTests_inclusion.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
The printed tensor product is a closed subspace and its canonical primary
comparison is a continuous linear equivalence.
Deviation: The source denominator uses the same restricted numerator, as on p. 384. -/
def Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)) (hω : NormOneCharacterUnramifiedOutside (res(F, χ)) S),
      let T := sLocalPrimaryPlaces S p
      let hT := sLocalPrimaryPlaces_subset S p
      let η := sLocalNormOneCharacter S (res(F, χ)) hω
      Printed.orbitalSupportTensorImage S T (Printed.orbitalSupportQuotientEquiv hT η)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
For ℚ with S = {∞, 2}, p = 2 and the trivial character, the zeta transform
of the real Gaussian times 1_{ℤ₂} has a double pole at zero. Restricted tests
have at most a simple pole there, and PV₂ lowers the pole order by one.
Thus this Gaussian class lies outside the comparison's range. -/
theorem Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
The printed tensor product is a closed subspace and its canonical single-place
comparison is a continuous linear equivalence.
Deviation: The source denominator uses the same restricted numerator, as on p. 384. -/
def Printed.sLocalPlaceOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)) (hω : NormOneCharacterUnramifiedOutside (res(F, χ)) S),
      let T : Finset V(F) := {v.val}
      let hT : T ⊆ S := Finset.singleton_subset_iff.mpr v.property
      let η := sLocalNormOneCharacter S (res(F, χ)) hω
      Printed.orbitalSupportTensorImage S T (Printed.orbitalSupportQuotientEquiv hT η)

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
For ℚ with S = {∞, 2}, v = 2 and the trivial character, the real Gaussian
times 1_{ℤ₂} gives the same double-pole obstruction as in part (1). -/
theorem Printed.sLocalPlaceOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPlaceOrbitalSupportComparison_isomorphism.{u} := by sorry

/-- Paper: Theorem 8.1.0.1(1)–(2), p. 382, and the intersection on p. 384.
Even for the repaired comparison, both properties fail over ℚ with one selected prime.
For injectivity take (h(x) − h(2x)) times the 2-adic integer indicator, with h even,
smooth, compactly supported and one near zero. Diagonal translation by 2 identifies
its theta class with the principal value of the unrestricted tensor with real factor h.
Its Mellin transform has a simple pole at zero, whereas a restricted principal value
has holomorphic transform there. The Gaussian double pole witnesses nonsurjectivity. -/
theorem sLocalOrbitalSupportComparison_rat_two_fails :
    let v : Vℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
    let S : Finset Vℚ := {v}
    let A := sLocalOrbitalSupportComparison (F := ℚ) (Finset.Subset.refl S) 1
    ¬ Function.Injective A ∧ ¬ Function.Surjective A := by sorry

end RiemannMasullo
