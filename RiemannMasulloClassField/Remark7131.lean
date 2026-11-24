module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClosedFiniteIndexClassFieldConstruction
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal

/-! # The class field of a finite-order character in Remark 7.1.3.1 -/

public noncomputable section

open IsDedekindDomain NumberField
open GlobalClassFieldTheory.GlobalClassFields

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "U𝔽" => PontryaginDual (NumberField.IdeleClassGroup (𝓞 F) F)
local notation "degree" => Module.finrank ℚ F
local notation "overₚ(" T "," p ")" =>
  @Finset.filter Primes (fun v : Primes ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p)
    (Classical.decPred _) T

/-- The image of a finite-order character embeds in the complex roots of unity
of the same order. -/
private theorem finiteOrderCharacter_splitsInClassField_finiteRange
    (χ : U𝔽) (hχ : IsOfFinOrder χ) : Finite χ.toMonoidHom.range := by
  obtain ⟨n, hn, hpow⟩ := hχ.exists_pow_eq_one
  let : NeZero n := ⟨hn.ne'⟩
  let f (z : χ.toMonoidHom.range) : rootsOfUnity n ℂ :=
    ⟨Circle.toUnits z.val, by
      obtain ⟨c, hc⟩ := z.property
      apply (mem_rootsOfUnity ..).mpr
      rw [← map_pow]
      have hc' : χ c ^ n = 1 := calc
        χ c ^ n = (χ ^ n) c := (ContinuousMonoidHom.pow_apply χ n c).symm
        _ = 1 := by rw [hpow, PontryaginDual.one_apply]
      rw [← hc, show χ.toMonoidHom c ^ n = 1 from hc', map_one]⟩
  exact Finite.of_injective f fun a b h ↦ Subtype.ext (Circle.ext
    (congrArg (fun z : rootsOfUnity n ℂ ↦ (z.val : ℂ)) h))

/-- At a prime with ramification index and inertia degree one, the stabilizer
has order one, so the prime below splits completely in the Galois extension. -/
private theorem finiteOrderCharacter_splitsInClassField_split
    (L : Type*) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (v : Primes) (w : v.asIdeal.primesOver (𝓞 L))
    (he : w.val.ramificationIdx (𝓞 F) = 1) (hf : w.val.inertiaDeg (𝓞 F) = 1) :
    FinitePlaceSplitsCompletely (K := F) (L := L) v := by
  let W : HeightOneSpectrum (𝓞 L) :=
    ⟨w.val, w.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot w.property⟩
  have hW : finitePlaceBelow (K := F) W = v := HeightOneSpectrum.ext w.property.2.over.symm
  let := finitePlaceMulAction F L
  apply (finitePlaceSplitsCompletely_iff_stabilizer_eq_bot v W hW).mpr
  apply (MulAction.stabilizer (L ≃ₐ[F] L) W).eq_bot_iff_card.mpr
  rw [finitePlace_stabilizer_card_eq_localDegree F L W]
  change (w.val.under (𝓞 F)).ramificationIdxIn (𝓞 L) *
    (w.val.under (𝓞 F)).inertiaDegIn (𝓞 L) = 1
  rw [← w.property.2.over, Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.val (L ≃ₐ[F] L),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.val (L ≃ₐ[F] L), he, hf, one_mul]

/-- Yamaguchi's idèlic existence theorem gives the class field of the character
kernel. Every one-place idèle class at a completely split prime is a norm. -/
theorem finiteOrderCharacter_splitsInClassField.{u} (F : Type u) [Field F] [NumberField F] :
    FiniteOrderCharacterSplitsInClassField F := by
  intro χ hχ
  let := finiteOrderCharacter_splitsInClassField_finiteRange χ hχ
  have hclosed : IsClosed (χ.toMonoidHom.ker : Set (NumberField.IdeleClassGroup (𝓞 F) F)) := by
    change IsClosed (χ ⁻¹' {1})
    exact isClosed_singleton.preimage (map_continuous χ)
  obtain ⟨L, hfin, hab, hnorm⟩ :=
    exists_closedFiniteIndexClassField_original χ.toMonoidHom.ker hclosed
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  intro v w he hf
  have hsplit := finiteOrderCharacter_splitsInClassField_split L v w he hf
  have hker := finitePlaceIdeleClass_range_le_ideleClassNorm_range_of_splitsCompletely v hsplit
  rw [hnorm] at hker
  have hlocal (x : (v.adicCompletion F)ˣ) : (ideleClassNormTwist χ 0).restrict v x = 1 := by
    have hx : χ (_root_.IdeleGroup.finitePlaceIdeleClass v x) = 1 := hker ⟨x, rfl⟩
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (χ (_root_.IdeleGroup.finitePlaceIdeleClass v x) : ℂ) * _ ^ (0 : ℂ) = 1
    rw [hx, Complex.cpow_zero, mul_one, Circle.coe_one]
  have hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦
      hlocal (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
  obtain ⟨π, hπ⟩ :=
    (Valued.v : Valuation (v.adicCompletion F) _).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨hu, (hu.localValue_eq π hπ).trans (hlocal (Units.mk0 π hπ.ne_zero))⟩

/-- Paper: Remark 7.1.3.1, p. 324.
For a Galois-type unitary character there are infinitely many completely split primes
where the full reciprocal Euler polynomial is a degree power in the translated coordinate.
Deviation: The right side uses exponent s + ix for the character χ₀ |·|^(ix).
The proof is `infinite_split_primes_reciprocalEulerProduct_normTwist_of_classField` applied to the
classical input `finiteOrderCharacter_splitsInClassField`. -/
theorem infinite_split_primes_reciprocalEulerProduct_normTwist
    (χ χ₀ : U𝔽) (hχ₀ : IsOfFinOrder χ₀) (x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I)) :
    {p : RatPrimes | rationalPrimeSplitsCompletely F p ∧
      ∀ S₀ : Finset Primes, (∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-(s + (x : ℂ) * Complex.I))) ^ degree}.Infinite :=
  infinite_split_primes_reciprocalEulerProduct_normTwist_of_classField
    (finiteOrderCharacter_splitsInClassField F) χ χ₀ hχ₀ x hχ

end RiemannMasullo
