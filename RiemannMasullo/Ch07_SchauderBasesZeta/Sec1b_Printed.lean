module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # §7.1.3–7.1.4 Statements that are false as printed -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "RatPrimes" => HeightOneSpectrum (𝓞 ℚ)
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽(" F ")" => PontryaginDual C𝔽(F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "normₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) normₛ(F, S) (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "overₚ(" T "," p ")" =>
  ((T).filter (fun v ↦ HeightOneSpectrum.under (𝓞 ℚ) v = p))
local notation "Bergman" => SchwartzBergman (univ : Set ℝ)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "Entire" => Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra)
local notation "Zeros(" L ")" => {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
local notation "Jet(" L ", " ρ ")" =>
  entireJetSpace ρ (meromorphicOrderAt L ρ).untop₀.toNat

local instance printedCh07Sec1bStrongDualTopology : TopologicalSpace (StrongDual ℂ Entire) :=
  ContinuousLinearMap.topologicalSpace (σ := RingHom.id ℂ) (E := Entire) (F := ℂ)

open Classical in
/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
As printed: For a finite-order character twisted by an imaginary norm power, infinitely
many rational primes satisfy the product identity with unshifted exponent once the
selected places contain all places above the prime. The translated formula is
`infinite_split_primes_reciprocalEulerProduct_normTwist` in
`RiemannMasulloClassField/Remark7131.lean`, which proves the classical input from
Yamaguchi's class field theory. See ERRATA F95. -/
def Printed.infinite_split_primes_reciprocalEulerProduct_normTwist : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ χ₀ : U𝔽(F)),
    IsOfFinOrder χ₀ → ∀ x : ℝ,
      ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I) →
      {p : RatPrimes | ∀ S₀ : Finset Places(F),
        (∀ v : Places(F), v.under (𝓞 ℚ) = p → v ∈ S₀) →
        ∀ s : ℂ, reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p) s =
          (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ Module.finrank ℚ F}.Infinite

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_char (F : Type*) [Field F] [NumberField F] (x : ℝ) : ∃ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I) := by
  let c := ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I)
  have hn (g : IdeleClassGroup (𝓞 F) F) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : PontryaginDual (IdeleClassGroup (𝓞 F) F) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun a b ↦ Subtype.ext (map_mul c a b)
      continuous_toFun := c.continuous.subtype_mk _ }
  refine ⟨χ, ?_⟩
  ext1 g
  change c g * _ ^ (0 : ℂ) = c g
  simp

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_local (F : Type*) [Field F] [NumberField F] (x : ℝ) (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) ((x : ℂ) * Complex.I))
    (p : HeightOneSpectrum (𝓞 F)) (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt p) :
    (ideleClassNormTwist χ 0).localValue p = (p.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) * Complex.I)) := by
  let val : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : p.adicCompletion F) hπ.ne_zero
  rw [hu.localValue_eq u hπ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe, hχ]
  change (1 : ℂ) * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F p u) : ℝ≥0) : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I) = _
  rw [one_mul, ideleClassNorm_ofAdicCompletion]
  change (‖(π : p.adicCompletion F)‖ : ℂ) ^ _ = _
  have hn : ‖(π : p.adicCompletion F)‖ = (p.asIdeal.absNorm : ℝ)⁻¹ := by
    have hval : Valued.v (π : p.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (p.valuedAdicCompletion_surjective F)))
    rw [FinitePlace.norm_def, hval, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  rw [hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) , ← Complex.cpow_neg, Complex.ofReal_natCast]

private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_generic : ∃ x : ℝ, ∀ n : ℕ, 1 < n → (n : ℂ) ^ (-((x : ℂ) * Complex.I)) ≠ 1 := by
  -- A generic twist avoids even the exceptional prime in the explicit example:
  -- for each possible norm n > 1, only countably many x give n^(-ix) = 1.
  let bad : ℕ → Set ℝ := fun n ↦ {x | 1 < n ∧ (n : ℂ) ^ (-((x : ℂ) * Complex.I)) = 1}
  have hc (n : ℕ) : (bad n).Countable := by
    by_cases hn : 1 < n
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hlog : Complex.log (n : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        apply Complex.ofReal_ne_zero.mpr
        exact (Real.log_pos (by exact_mod_cast hn)).ne'
      have hi : Function.Injective (fun x : ℝ ↦ Complex.log (n : ℂ) * (-((x : ℂ) * Complex.I))) := by
        intro a b h
        apply Complex.ofReal_injective
        have h' := mul_left_cancel₀ hlog h
        have h'' : (a : ℂ) * Complex.I = (b : ℂ) * Complex.I := neg_injective h'
        exact mul_right_cancel₀ Complex.I_ne_zero h''
      have he : (Complex.exp ⁻¹' ({1} : Set ℂ)).Countable := (Set.countable_singleton 1).preimage_cexp
      apply (he.preimage hi).mono
      intro x hx
      change Complex.exp (Complex.log (n : ℂ) * (-((x : ℂ) * Complex.I))) = 1
      exact (Complex.cpow_def_of_ne_zero hn0 _).symm.trans hx.2
    · have : bad n = ∅ := by ext x; simp [bad, hn]
      simp [this]
  have hall := Set.countable_iUnion hc
  have hne : (⋃ n, bad n) ≠ Set.univ := fun h ↦ Set.not_countable_univ (h ▸ hall)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ ⋃ n, bad n := by simpa [Set.eq_univ_iff_forall] using hne
  refine ⟨x, ?_⟩
  intro n hn he
  exact hx (Set.mem_iUnion.mpr ⟨n, ⟨hn, he⟩⟩)

open Classical in
private theorem infinite_split_primes_reciprocalEulerProduct_normTwist_aux (F : Type*) [Field F] [NumberField F]
    (h : ∀ (χ χ₀ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
      IsOfFinOrder χ₀ → ∀ x : ℝ,
        ideleClassNormTwist χ 0 = ideleClassNormTwist χ₀ ((x : ℂ) * Complex.I) →
        {p : HeightOneSpectrum (𝓞 ℚ) | ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
          (∀ v, v.under (𝓞 ℚ) = p → v ∈ S₀) → ∀ s : ℂ,
          reciprocalPartialHeckeEulerProduct χ (S₀.filter (fun v ↦ v.under (𝓞 ℚ) = p)) s =
            (1 - (p.asIdeal.absNorm : ℂ) ^ (-s)) ^ Module.finrank ℚ F}.Infinite) : False := by
  classical
  obtain ⟨x, hx⟩ := infinite_split_primes_reciprocalEulerProduct_normTwist_generic
  obtain ⟨χ, hχ⟩ := infinite_split_primes_reciprocalEulerProduct_normTwist_char F x
  have hi := h χ 1 IsOfFinOrder.one x hχ
  obtain ⟨p, hp⟩ := hi.nonempty
  let A : Set (HeightOneSpectrum (𝓞 F)) := {v | v.under (𝓞 ℚ) = p}
  have hf : A.Finite := by
    let f : A → p.asIdeal.primesOver (𝓞 F) := fun v ↦ ⟨v.1.asIdeal, v.1.isPrime,
      ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
    have hfi : Function.Injective f := by
      intro a b hab
      exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val hab))
    let : Finite A := Finite.of_injective f hfi
    exact Set.toFinite A
  let S := hf.toFinset
  have hs := hp S (fun v hv ↦ hf.mem_toFinset.mpr hv) 0
  have hd : Module.finrank ℚ F ≠ 0 := (Module.finrank_pos (R := ℚ) (M := F)).ne'
  simp only [neg_zero, Complex.cpow_zero, sub_self, zero_pow hd] at hs
  change (∏ v ∈ S.filter (fun v ↦ v.under (𝓞 ℚ) = p), (finiteHeckeEulerFactor χ v 0)⁻¹) = 0 at hs
  obtain ⟨v, hv, hz⟩ := Finset.prod_eq_zero_iff.mp hs
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, inv_inv] at hz
    simp only [neg_zero, Complex.cpow_zero, mul_one, sub_eq_zero] at hz
    have he := infinite_split_primes_reciprocalEulerProduct_normTwist_local F x χ hχ v hu
    exact hx v.asIdeal.absNorm (HeightOneSpectrum.one_lt_absNorm v) (he.symm.trans hz.symm)
  · simp [finiteHeckeEulerFactor, hu] at hz

/-- Paper: Remark 7.1.3.1, equation (7.1.3.1), p. 324.
Use ℚ, the trivial finite-order character, and x = 2π/log 2. At s = 0 the
identity requires p^(-ix) = 1, so the rational prime p is an integral power
of 2. Only the prime 2 can satisfy the identity. -/
theorem Printed.infinite_split_primes_reciprocalEulerProduct_normTwist_false :
    ¬ Printed.infinite_split_primes_reciprocalEulerProduct_normTwist := by
  intro h
  -- Lift ℚ to the universe quantified over by the printed claim.
  let : Field (ULift ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact infinite_split_primes_reciprocalEulerProduct_normTwist_aux (ULift ℚ) (h (ULift ℚ))


open Classical in
/-- Paper: Theorem 7.1.3.2(2), p. 324.
As printed: At an archimedean point of the stated pole list whose real part is a
negative odd integer, the pole order of the correcting factor is bounded by the number
of complex places. The repaired bound is `sLocalRhoPoleOrder_le_of_re_neg_odd`.
See ERRATA F97. -/
def Printed.sLocalRhoPoleOrder_le_of_re_neg_odd : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : U𝔽(F))
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (w : InfinitePlace F) (n : ℕ),
    let chart := twistₛ(F, S) (sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩)
    let c := sLocalInfiniteRestriction w (chart 0)
    let m : ℝ := -((2 * n + 1 : ℕ) : ℝ)
    let r₂ := (Finset.univ.filter (fun v : InfinitePlace F ↦ v.IsComplex)).card
    (∀ hw : w.IsReal,
      let p := (realLocalEulerParameters w hw c).exists.choose
      p.2.val = 1 → sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂) ∧
    (∀ hw : w.IsComplex,
      let p := (complexLocalEulerParameters w hw c).exists.choose
      (∃ j : ℕ, m = (p.2.natAbs : ℝ) / 2 - j) →
        sLocalRhoPoleOrder (chart ((m : ℂ) - p.1)) ≤ r₂)

/-- At a singleton finite stage, a unitary character detects the idele with
value minus one at the chosen infinite place and one everywhere else. -/
private theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_exists_character
    (F : Type u) [Field F] [NumberField F] (v : Places(F)) (w : InfinitePlace F) :
    ∃ η : PontryaginDual Jₛ(F, {v}),
      sLocalInfiniteRestriction w ((circleToComplex).comp η) (-1) ≠ 1 := by
  classical
  let S : Finset Places(F) := {v}
  let signs : (t : InfinitePlace F) → t.Completionˣ := Pi.mulSingle w (-1)
  let g : (SAdeleRing F S)ˣ :=
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((i : S) → i.val.adicCompletion F)).symm
      (ContinuousMulEquiv.piUnits.symm signs, 1)
  -- Its finite coordinate forces a diagonal representative to be one.
  have hg : (QuotientGroup.mk g : Jₛ(F, S)) ≠ 1 := by
    intro he
    obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one F S g).mp he
    let i : S := ⟨v, Finset.mem_singleton_self _⟩
    have hf := congrArg (fun a : (SAdeleRing F S)ˣ ↦ a.val.2 i) hu
    change 1 = algebraMap F (v.adicCompletion F) (u.val : F) at hf
    have hu1 : (u.val : F) = 1 := (algebraMap F (v.adicCompletion F)).injective
      (hf.symm.trans (map_one _).symm)
    have ha := congrArg (fun a : (SAdeleRing F S)ˣ ↦ a.val.1 w) hu
    change (signs w : w.Completion) = algebraMap F w.Completion (u.val : F) at ha
    have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F _).injective
    norm_num [signs, hu1] at ha
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨η, hη⟩ := exists_pontryaginDual_apply_ne_one hg
  exact ⟨η, fun h ↦ hη (Subtype.ext h)⟩

/-- Over a degree-one field the first pole of an odd real factor contradicts
the bound by the number of complex places. -/
private theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_of_degree_one
    (F : Type u) [Field F] [NumberField F] (hd : Module.finrank ℚ F = 1)
    (h : Printed.sLocalRhoPoleOrder_le_of_re_neg_odd.{u}) : False := by
  classical
  have hcard := InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd
  let w : InfinitePlace F := Classical.arbitrary _
  have hw := (nrComplexPlaces_eq_zero_iff.mp hcard).isReal w
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Places(F) := {v}
  obtain ⟨η, hsign⟩ :=
    Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_exists_character F v w
  let c := (circleToComplex).comp η
  let chart := twistₛ(F, S) c
  have hzero : chart 0 = c := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨χ, hχ, hext, -⟩ := sLocal_character_extension η
  have hbase : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩ = c := hext.trans hzero
  let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chart 0))).exists.choose
  have hp : p.2.val = 1 := by
    have he := (realLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart 0))).exists.choose_spec (-1 : ℝˣ)
    have hneg : Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
        (-1 : ℝˣ) = -1 := Units.ext (by simp)
    by_contra hne
    have hp0 : p.2.val = 0 := by
      have := p.2.isLt
      omega
    change _ = _ * _ ^ p.2.val at he
    rw [hneg, hp0, hzero] at he
    exact hsign (by simpa using he)
  let s : ℂ := -1 - p.1
  have hpole : meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart z)) s < 0 := by
    apply (sLocalRhoFactor_poles_iff η s).2
    refine Or.inl ⟨w, hw, 0, ?_⟩
    change s = -p.1 - ((2 * 0 + p.2.val : ℕ) : ℂ)
    rw [hp]
    dsimp [s]
    ring
  have bound := (h F S χ hχ w 0).1 hw
  simp only [hbase] at bound
  specialize bound hp
  have hbound : sLocalRhoPoleOrder (chart s) ≤ 0 := by
    simpa [s, p, chart, S, ← Fintype.card_subtype, hcard] using bound
  have hord := sLocalIdelicOrderBound_eq_neg_poleOrder (chart s)
  rw [Nat.le_zero.mp hbound] at hord
  rw [sLocalOrderBound_chart η s, min_eq_right hpole.le] at hord
  simp [hord] at hpole

/-- Paper: Theorem 7.1.3.2(2), p. 324.
Over ℚ the odd Dirichlet character modulo 4 has real factor Γℝ(s + 1)
and a pole at −1, while there are zero complex places. The proof obtains an
odd character by separating the sign idele with any one finite place included. -/
theorem Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false :
    ¬ Printed.sLocalRhoPoleOrder_le_of_re_neg_odd := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact Printed.sLocalRhoPoleOrder_le_of_re_neg_odd_false_of_degree_one (ULift ℚ) (by simp) h

/-- Paper: Corollary 7.1.3.3, p. 326.
As printed: There is a highest positive pole order and a highest positive order
strictly below it for the continued zeta transform of every test in the setting of
the corollary. This is the clause defining the remainder exponent.
The least-bound formulation is in `sLocalHomogeneousAdelicTheta_log_bound`.
See ERRATA F98. -/
def Printed.sLocalPolarMultiplicity_greatest_smaller : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)),
    Fintype.card (InfinitePlace F) = 1 →
    ∀ (χ : PontryaginDual Jₛ(F, S)) (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
      let chart := twistₛ(F, S) ((circleToComplex).comp χ)
      let orders : Set ℕ := {m | 0 < m ∧ ∃ s : ℂ, sLocalPolarMultiplicity f (chart s) = m}
      ∃ M m : ℕ, IsGreatest orders M ∧ IsGreatest (orders ∩ Iio M) m

/-- The S-local Z-function of the zero test is identically zero: the zero function is
meromorphic in normal form and agrees with the zero integral, and the continuation is unique. -/
private theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false_zFunction_zero
    (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) :
    sLocalIdelicZFunction (F := F) (S := S) 0 = 0 :=
  (sLocalIdelicZetaIntegral_exists_continuation (F := F) (S := S) 0).unique
    (sLocalIdelicZetaIntegral_exists_continuation (F := F) (S := S) 0).exists.choose_spec
    ⟨fun _ ↦ analyticOnNhd_const.meromorphicNFOn, fun c _ ↦ by
      simp only [Pi.zero_apply, sLocalIdelicZetaIntegral]
      exact (integral_eq_zero_of_ae (Eventually.of_forall fun _ ↦ zero_mul _)).symm⟩

/-- The zero test has polar multiplicity zero at every quasi-character. -/
private theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false_zero
    (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (c : QuasiCharacter Jₛ(F, S)) :
    sLocalPolarMultiplicity (0 : SchwartzBruhat (Multiplicative (SAdeleRing F S))) c = 0 := by
  rw [sLocalPolarMultiplicity_eq_zero_iff]
  refine le_top.trans_eq (meromorphicOrderAt_eq_top_iff.mpr (Eventually.of_forall fun z ↦ ?_)).symm
  rw [Printed.sLocalPolarMultiplicity_greatest_smaller_false_zFunction_zero F S]
  rfl

/-- Paper: Corollary 7.1.3.3, p. 326.
Use ℚ with only the real place, the trivial character and the zero test, for which
the set of pole orders is empty. The Gaussian `exp(-πx²)` gives a second example:
Γℝ(s) has only simple poles, so there is no positive order below one. -/
theorem Printed.sLocalPolarMultiplicity_greatest_smaller_false :
    ¬ Printed.sLocalPolarMultiplicity_greatest_smaller := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  have hd : Module.finrank ℚ (ULift ℚ) = 1 := by simp
  have hcard : Fintype.card (InfinitePlace (ULift ℚ)) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hd,
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hd]
  obtain ⟨M, m, hM, -⟩ := h (ULift ℚ) ∅ hcard 1 0
  obtain ⟨hpos, s, hs⟩ := hM.1
  rw [Printed.sLocalPolarMultiplicity_greatest_smaller_false_zero] at hs
  omega

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
As printed: The strong annihilator of the regularized completed Hecke ideal is linearly
and topologically isomorphic to the product of the jet spaces at the completed Hecke zeros.
The direct-sum statement is `spectralAnnihilator_directSum`. See ERRATA F99. -/
def Printed.spectralAnnihilator_product : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let Λ := regularizedCompletedHeckeL χ τ hτ L hL hEq
    Nonempty ((∀ ρ : Zeros(L), ↥(Jet(L, ρ.val))) ≃L[ℂ] entireIdealAnnihilator Λ)

/-- An infinite product of nonzero finite-dimensional complex vector spaces has
strictly larger algebraic dimension than their direct sum. -/
private theorem spectralAnnihilator_product_false_no_equiv
    (ι : Type) [Infinite ι] (E : ι → Type)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    [∀ i, FiniteDimensional ℂ (E i)] [∀ i, Nontrivial (E i)] :
    ¬ Nonempty ((∀ i, E i) ≃ₗ[ℂ] (DirectSum ι E)) := by
  classical
  choose v hv using fun i ↦ exists_ne (0 : E i)
  let T : (ι → ℂ) →ₗ[ℂ] (∀ i, E i) :=
    { toFun := fun f i ↦ f i • v i
      map_add' := fun f g ↦ by funext i; exact add_smul _ _ _
      map_smul' := fun c f ↦ by funext i; exact mul_smul _ _ _ }
  have hT : Function.Injective T := by
    intro f g h
    funext i
    exact smul_left_injective ℂ (hv i) (congrFun h i)
  have hsum : Module.rank ℂ (DirectSum ι E) ≤ Cardinal.mk ι := by
    rw [rank_directSum]
    calc
      Cardinal.sum (fun i ↦ Module.rank ℂ (E i)) ≤
          Cardinal.sum (fun _ : ι ↦ Cardinal.aleph0) :=
        Cardinal.sum_le_sum _ _ fun i ↦ (Module.rank_lt_aleph0 ℂ (E i)).le
      _ = Cardinal.mk ι := by
        rw [Cardinal.sum_const', Cardinal.mk_mul_aleph0_eq]
  have hprod : Cardinal.mk ι < Module.rank ℂ (∀ i, E i) := by
    refine lt_of_lt_of_le ?_ (T.rank_le_of_injective hT)
    rw [rank_fun_infinite, ← Cardinal.power_def]
    exact Cardinal.cantor' _ (Cardinal.one_lt_iff_nontrivial.mpr inferInstance)
  rintro ⟨e⟩
  exact hprod.not_ge (e.rank_eq.trans_le hsum)

/-- A completed Hecke continuation has finite meromorphic order everywhere:
infinite order would propagate to the zero-free point `2`. -/
private theorem spectralAnnihilator_product_false_order_ne_top
    (F : Type u) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L Set.univ)
    (hEq : ∀ s : Complex.re ⁻¹' Set.Ioi (1 : ℝ), L s = completedHeckeL χ s)
    (z : ℂ) : meromorphicOrderAt L z ≠ ⊤ := by
  intro hz
  have ht : meromorphicOrderAt L (2 : ℂ) = ⊤ :=
    hL.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ z) (Set.mem_univ 2) hz
  have hpos : 0 < meromorphicOrderAt L (2 : ℂ) := by rw [ht]; exact WithTop.coe_lt_top 0
  have h := completedHeckeL_continuation_zeros χ L hL hEq (by norm_num) hpos
  norm_num at h

/-- Once a completed Hecke continuation has infinitely many zeros, its product
of jet spaces cannot be isomorphic to the annihilator's direct-sum model. -/
private theorem spectralAnnihilator_product_false_of_infinite
    (F : Type u) [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : Function.RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L Set.univ)
    (hEq : ∀ s : Complex.re ⁻¹' Set.Ioi (1 : ℝ), L s = completedHeckeL χ s)
    (hInfinite : Infinite {ρ : ℂ // 0 < meromorphicOrderAt L ρ}) :
    ¬ Nonempty ((∀ ρ : {ρ : ℂ // 0 < meromorphicOrderAt L ρ},
      ↥(entireJetSpace ρ.val (meromorphicOrderAt L ρ.val).untop₀.toNat)) ≃L[ℂ]
      entireIdealAnnihilator (regularizedCompletedHeckeL χ τ hτ L hL hEq)) := by
  classical
  let Z := {ρ : ℂ // 0 < meromorphicOrderAt L ρ}
  let J (ρ : Z) := entireJetSpace ρ.val (meromorphicOrderAt L ρ.val).untop₀.toNat
  let : Infinite Z := hInfinite
  let : ∀ ρ : Z, AddCommGroup ↥(J ρ) := fun ρ ↦ Submodule.addCommGroup (J ρ)
  let : ∀ ρ : Z, Module ℂ ↥(J ρ) := fun ρ ↦ Submodule.module (J ρ)
  let : ∀ ρ : Z, FiniteDimensional ℂ ↥(J ρ) := fun ρ ↦
    FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun m : Fin (meromorphicOrderAt L ρ.val).untop₀.toNat ↦ entireJet ρ.val m.val))
  have hmult (ρ : Z) : 0 < (meromorphicOrderAt L ρ.val).untop₀.toNat := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (spectralAnnihilator_product_false_order_ne_top F χ L hL hEq ρ.val)
    have hpos := ρ.property
    rw [← hn] at hpos ⊢
    rw [WithTop.untop₀_coe]
    have : (0 : ℤ) < n := WithTop.coe_lt_coe.mp hpos
    omega
  let : ∀ ρ : Z, Nontrivial ↥(J ρ) := fun ρ ↦
    Module.nontrivial_of_finrank_pos (by
      change 0 < Module.finrank ℂ (entireJetSpace ρ.val _)
      rw [entireJetSpace_finrank]
      exact hmult ρ)
  let inclusion := DirectSum.lof ℂ Z (fun ρ ↦ ↥(J ρ))
  let : TopologicalSpace (DirectSum Z (fun ρ ↦ ↥(J ρ))) := locallyConvexFinalTopology inclusion
  obtain ⟨eSum, _⟩ := spectralAnnihilator_directSum χ τ hτ L hL hEq
  rintro ⟨eProd⟩
  exact spectralAnnihilator_product_false_no_equiv Z (fun ρ ↦ ↥(J ρ))
    ⟨eProd.toLinearEquiv.trans eSum.symm.toLinearEquiv⟩

/-- The completed trivial Hecke functions of a degree-one field and of ℚ agree
on the convergence half-plane. The isomorphism of rings of integers preserves ideal norms. -/
private theorem spectralAnnihilator_product_false_degree_one_eq_rat
    (F : Type u) [Field F] [NumberField F] (hF : Module.finrank ℚ F = 1) (s : halfPlane) :
    completedHeckeL (1 : U𝔽(F)) s = completedHeckeL (1 : U𝔽(ℚ)) s := by
  let e := RingEquiv.ofBijective (algebraMap ℚ F)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hF)
  let i := RingOfIntegers.mapRingEquiv e.symm
  have hnorm (I : Ideal (𝓞 F)) : (I.map i).absNorm = I.absNorm := by
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map i) i rfl).toEquiv).symm
  have hcoeff (n : ℕ) : Nat.card {I : Ideal (𝓞 F) // I.absNorm = n} =
      Nat.card {I : Ideal (𝓞 ℚ) // I.absNorm = n} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv i.idealComapOrderIso.symm.toEquiv fun I ↦ ?_
    change I.absNorm = n ↔ (I.map i).absNorm = n
    rw [hnorm]
  simp only [completedHeckeL_one_eq_dedekindZeta,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one hF,
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one hF,
    InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
    InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
    dedekindZeta, hcoeff]

/-- Paper: Theorem 7.1.4.2(1), p. 326. Analytic input for the product refutation.
The trivial completed Hecke function over a degree-one number field has
infinitely many distinct positive-order zeros. This is the remaining analytic
input: under the unique rational-field isomorphism it is the classical
infinitude of nontrivial Riemann-zeta zeros. Finite meromorphic orders are proved
separately above, so this statement asks only for the infinite zero set. -/
private theorem spectralAnnihilator_product_false_degree_one_zeros
    (F : Type u) [Field F] [NumberField F] (hF : Module.finrank ℚ F = 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L Set.univ)
    (hEq : ∀ s : Complex.re ⁻¹' Set.Ioi (1 : ℝ),
      L s = completedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) s) :
    Infinite {ρ : ℂ // 0 < meromorphicOrderAt L ρ} := by
  have hRat := continuedCompletedHeckeL_spec (F := ℚ) 1
  have he : L = continuedCompletedHeckeL (F := ℚ) 1 := by
    apply eq_of_agree_rightHalf hL hRat.1 1
    intro z hz
    let s : halfPlane := ⟨z, hz⟩
    exact (hEq s).trans ((spectralAnnihilator_product_false_degree_one_eq_rat F hF s).trans
      (hRat.2 s).symm)
  subst L
  refine (Equiv.subtypeEquivRight (fun z ↦ ?_)).infinite_iff.mp
    introTrace_rat_positive_divisor_infinite
  rw [MeromorphicOn.divisor_apply hRat.1.meromorphicOn (mem_univ z), ← WithTop.coe_lt_coe,
    WithTop.coe_zero, WithTop.coe_untop₀_of_ne_top
      (spectralAnnihilator_product_false_order_ne_top ℚ 1 _ hRat.1 hRat.2 z)]

/-- The degree-one zero infinitude and the dimension obstruction contradict
an instance of the printed product assertion in the same universe. -/
private theorem spectralAnnihilator_product_false_contra
    (h : Printed.spectralAnnihilator_product.{u}) : False := by
  have : CharZero (ULift.{u} ℚ) :=
    ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  let χ : PontryaginDual (IdeleClassGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ)) := 1
  obtain ⟨L, hL, hEq⟩ := completedHeckeL_exists_continuation χ
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ) :=
    ⟨canonicalIdeleNormSection _, canonicalIdeleNormSection_continuous _⟩
  have hτ : Function.RightInverse τ (ideleNorm (ULift.{u} ℚ)) :=
    canonicalIdeleNormSection_rightInverse _
  have hInf := spectralAnnihilator_product_false_degree_one_zeros
    (ULift.{u} ℚ) (by simp) L hL hEq
  exact spectralAnnihilator_product_false_of_infinite
    (ULift.{u} ℚ) χ τ hτ L hL hEq hInf (h (ULift.{u} ℚ) χ τ hτ L hL hEq)

/-- Paper: Theorem 7.1.4.2(1), equation (7.1.4.2), p. 326.
Take the trivial rational character and the meromorphic normal form of the completed
Riemann zeta function. There are countably infinitely many distinct zeros and
each jet space is nonzero and
finite-dimensional. The annihilator consists of finite-support jets and has countable
algebraic dimension. The product has uncountable dimension, as seen by embedding
complex sequences and using the independent sequences `(a^n)ₙ` for distinct a. -/
theorem Printed.spectralAnnihilator_product_false :
    ¬ Printed.spectralAnnihilator_product := by
  intro h
  exact spectralAnnihilator_product_false_contra h

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
As printed: The derivative functional at a completed Hecke zero is the moment of the
inverse Mellin transform in the coordinate (7.1.4.1), with exponent shifted by the
section frequency x₀. The formula of `schwartzBergman_jet_eq_mellinInv_moment`
uses the unshifted exponent. See ERRATA F100. -/
def Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
    ∀ f : Bergman,
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let φ : ℂ → ℂ := f.val
      let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ m * mellinInv 0 φ t
      iteratedDeriv m φ ρ.val = mellin moment (ρ.val + (x₀ : ℂ) * Complex.I)

/-- A universe lift of the rationals is a number field. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_numberField :
    NumberField (ULift.{u} ℚ) := by
  let e : ULift.{u} ℚ ≃+* ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} ℚ) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have : FiniteDimensional ℚ (ULift.{u} ℚ) :=
    Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- A universe lift of the rationals has the Dedekind zeta function of the rationals. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_dedekindZeta
    [NumberField (ULift.{u} ℚ)] (s : ℂ) :
    dedekindZeta (ULift.{u} ℚ) s = dedekindZeta ℚ s := by
  let e : 𝓞 (ULift.{u} ℚ) ≃+* 𝓞 ℚ := RingOfIntegers.mapRingEquiv ULift.ringEquiv
  have hnorm (I : Ideal (𝓞 (ULift.{u} ℚ))) : Ideal.absNorm (I.map e) = Ideal.absNorm I := by
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 (ULift.{u} ℚ)) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.idealComapOrderIso.symm.toEquiv fun I ↦ ?_)
    change _ ↔ Ideal.absNorm (I.map e) = n
    rw [hnorm]
  change LSeries _ s = LSeries _ s
  congr 1
  funext n
  rw [hc]

/-- Over the rationals the Dedekind zeta series is the Riemann zeta function
to the right of one. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_rat {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 ℚ) // I.absNorm = n} = 1 := by
    let : Unique {I : Ideal (𝓞 ℚ) // I.absNorm = n} :=
      { default := ⟨_, RatRingOfIntegers.absNorm_span_natCast n⟩
        uniq := fun I ↦ by
          apply Subtype.ext
          obtain ⟨m, hm⟩ := RatRingOfIntegers.exists_eq_span_natCast I.val
          have hmn : m = n := by
            simpa only [hm, RatRingOfIntegers.absNorm_span_natCast] using I.property
          simpa only [hmn] using hm }
    exact Nat.card_unique
  simpa only [dedekindZeta, hc, Nat.cast_one, Pi.one_def] using LSeries_one_eq_riemannZeta hs

/-- The Riemann zeta function is meromorphic on the plane. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_meromorphic :
    MeromorphicOn riemannZeta univ := by
  intro s _
  have ha := (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt s
  have hm : MeromorphicAt (fun z : ℂ ↦ DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1)) s :=
    ha.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  apply hm.congr
  filter_upwards [(eventually_cofinite_ne (1 : ℂ)).filter_mono (nhdsNE_le_cofinite s)] with z hz
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz)]
  simp [DirichletCharacter.LFunctionTrivChar]

/-- The finite L-function of the trivial character is the Dedekind zeta series. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_one (F : Type*) [Field F] [NumberField F]
    (s : halfPlane) : finiteHeckeL (1 : U𝔽(F)) s = dedekindZeta F s := by
  have he := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at he
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U𝔽(F))
    (zero_lt_one.trans s.property)) he

/-- The norm twist evaluates to the character times a power of the idelic norm. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_apply (F : Type*) [Field F] [NumberField F]
    (χ : U𝔽(F)) (s : ℂ) (g : IdeleClassGroup (𝓞 F) F) :
    ideleClassNormTwist χ s g = (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ s :=
  rfl

/-- An imaginary translation of the Euler product is the Euler product of the translated
unitary character. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_twist (F : Type*) [Field F] [NumberField F]
    (χ ψ : U𝔽(F)) (a : ℂ) (ha : a.re = 0)
    (hψ : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ a) (s : halfPlane) :
    finiteHeckeL ψ s = finiteHeckeL χ ⟨(s : ℂ) + a, by
      change 1 < (s : ℂ).re + a.re
      rw [ha, add_zero]
      exact s.property⟩ := by
  let w : halfPlane := ⟨(s : ℂ) + a, by
    change 1 < (s : ℂ).re + a.re
    rw [ha, add_zero]
    exact s.property⟩
  apply (finiteHeckeL_hasProd ψ s).unique ((finiteHeckeL_hasProd χ w).congr_fun ?_)
  intro v
  have hval (t : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v t =
        (ideleClassNormTwist χ 0).restrict v t * (‖(t : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [hψ, HeckeCharacter.restrict, HeckeCharacter.restrict,
      MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, MonoidHom.coe_toHomUnits, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass]
    rw [schwartzBergman_jet_eq_mellinInv_shifted_moment_apply, schwartzBergman_jet_eq_mellinInv_shifted_moment_apply,
      Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : (ideleClassNormTwist ψ 0).IsUnramifiedAt v ↔
      (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff, HeckeCharacter.isUnramifiedAt_iff]
    apply forall_congr'
    intro t
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom t
    have hn : ‖(u : v.adicCompletion F)‖ = 1 := by
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      exact IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (show u ∈ (v.adicCompletionIntegers F).units from ⟨t.val.property, t.inv.property⟩)
    change (ideleClassNormTwist ψ 0).restrict v u = 1 ↔
      (ideleClassNormTwist χ 0).restrict v u = 1
    rw [hval, hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  by_cases hx : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
    have hn := norm_uniformizer_adicCompletion v _ hπ
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, ite_eq_left hx, ite_eq_left (hu.mpr hx),
      hx.localValue_eq u hπ, (hu.mpr hx).localValue_eq u hπ, hval]
    change (1 - (_ * (‖(π : v.adicCompletion F)‖ : ℂ) ^ a) * _)⁻¹ =
      (1 - _ * _ ^ (-((s : ℂ) + a)))⁻¹
    rw [hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
      ← Complex.cpow_neg, Complex.ofReal_natCast, mul_assoc, ← Complex.cpow_add _ _ hq]
    rw [show -a + -(s : ℂ) = -((s : ℂ) + a) by ring]
  · simp [finiteHeckeEulerFactor, hx, hu.not.mpr hx]

/-- The imaginary power `|·|^i` of the idelic norm is a unitary character. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_char (F : Type*) [Field F] [NumberField F] :
    ∃ χ : U𝔽(F), (∀ g : C𝔽(F),
      (χ g : ℂ) = (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I) ∧
      ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U𝔽(F)) Complex.I := by
  let c := ideleClassNormTwist (1 : U𝔽(F)) Complex.I
  have hnorm (g : C𝔽(F)) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Complex.I_re, Real.rpow_zero]
  let χ : U𝔽(F) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hc (g : C𝔽(F)) :
      (χ g : ℂ) = (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I := by
    change (1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I = _
    rw [one_mul]
  refine ⟨χ, hc, ?_⟩
  ext g
  rw [schwartzBergman_jet_eq_mellinInv_shifted_moment_apply, schwartzBergman_jet_eq_mellinInv_shifted_moment_apply, hc, Complex.cpow_zero, mul_one]
  change _ = (1 : ℂ) * _
  rw [one_mul]

/-- The printed shifted moment fails over a universe lift of the rationals. -/
private theorem schwartzBergman_jet_eq_mellinInv_shifted_moment_contra
    (h : Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment.{u}) : False := by
  have : NumberField (ULift.{u} ℚ) := schwartzBergman_jet_eq_mellinInv_shifted_moment_numberField
  obtain ⟨γ, hγ, hz⟩ := HardyFirstZero.first_zero_on_line
  obtain ⟨χ, hχv, hχ⟩ := schwartzBergman_jet_eq_mellinInv_shifted_moment_char (ULift.{u} ℚ)
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ) :=
    ⟨canonicalIdeleNormSection _, canonicalIdeleNormSection_continuous _⟩
  have hτ : Function.RightInverse τ (ideleNorm (ULift.{u} ℚ)) :=
    canonicalIdeleNormSection_rightInverse _
  let b : ℂ := Complex.I
  have hb : b.re = 0 := Complex.I_re
  let f : ℂ → ℂ := fun s ↦ riemannZeta (s + b)
  have hfa (s : ℂ) (hs : s + b ≠ 1) : AnalyticAt ℂ f s := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | z + b ≠ 1})
      (fun z hz ↦ ((differentiableAt_riemannZeta hz).comp z
        (differentiableAt_id.add_const b)).differentiableWithinAt)
    exact (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).mem_nhds hs
  have hf : MeromorphicOn f univ := fun s _ ↦
    MeromorphicAt.comp_analyticAt (g := fun z : ℂ ↦ z + b) (x := s)
      (schwartzBergman_jet_eq_mellinInv_shifted_moment_meromorphic (s + b) (mem_univ _)) (analyticAt_id.add analyticAt_const)
  have hfeq : ∀ s : halfPlane, f s = finiteHeckeL χ s := by
    intro s
    have hre : 1 < ((s : ℂ) + b).re := by
      rw [Complex.add_re, hb, add_zero]
      exact s.property
    rw [schwartzBergman_jet_eq_mellinInv_shifted_moment_twist (ULift.{u} ℚ) 1 χ b hb hχ s, schwartzBergman_jet_eq_mellinInv_shifted_moment_one]
    change riemannZeta ((s : ℂ) + b) = dedekindZeta (ULift.{u} ℚ) ((s : ℂ) + b)
    rw [schwartzBergman_jet_eq_mellinInv_shifted_moment_dedekindZeta, schwartzBergman_jet_eq_mellinInv_shifted_moment_rat hre]
  have hΓa (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor χ) s := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  let P : ℂ → ℂ := fun s ↦ heckeGammaFactor χ s * f s
  have hP : MeromorphicOn P univ := fun s _ ↦
    (meromorphic_heckeGammaFactor χ s).mul (hf s (mem_univ s))
  let L := toMeromorphicNFOn P univ
  have hL : MeromorphicNFOn L univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hLe : ∀ s : halfPlane, L s = completedHeckeL χ s := by
    intro s
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hre : 1 < ((s : ℂ) + b).re := by
      rw [Complex.add_re, hb, add_zero]
      exact s.property
    have hne : (s : ℂ) + b ≠ 1 := fun h1 ↦ by
      rw [h1] at hre
      norm_num at hre
    have hPa : AnalyticAt ℂ P s := (hΓa s hs).mul (hfa s hne)
    change toMeromorphicNFOn P univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hPa.meromorphicNFAt]
    change heckeGammaFactor χ s * f s = _
    rw [hfeq s]
    rfl
  let ρ₀ : ℂ := 1 / 2 + γ * Complex.I - Complex.I
  have hρre : ρ₀.re = 1 / 2 := by simp [ρ₀]
  have hρne : ρ₀ + b ≠ 1 := fun h1 ↦ by
    have := congrArg Complex.re h1
    rw [Complex.add_re, hb, add_zero, hρre, Complex.one_re] at this
    norm_num at this
  have hord_f : 0 < meromorphicOrderAt f ρ₀ := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hf _ (mem_univ _))).mp
    have h0 : f ρ₀ = 0 := by
      change riemannZeta (1 / 2 + γ * Complex.I - Complex.I + Complex.I) = 0
      rw [sub_add_cancel]
      exact hz
    rw [← h0]
    exact (hfa _ hρne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt f 2 ≠ ⊤ := by
    have hne2 : (2 : ℂ) + b ≠ 1 := fun h1 ↦ by
      have := congrArg Complex.re h1
      rw [Complex.add_re, hb, add_zero] at this
      norm_num at this
    have hv : f 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simp [b])
    rw [(hfa 2 hne2).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hv]
    exact WithTop.zero_ne_top
  have hfin : meromorphicOrderAt f ρ₀ ≠ ⊤ := fun ht ↦ htwo
    (hf.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (mem_univ _)
      (mem_univ _) ht)
  have hρpos : 0 < ρ₀.re := by
    rw [hρre]
    norm_num
  have hordL : meromorphicOrderAt f ρ₀ = meromorphicOrderAt L ρ₀ := by
    rw [meromorphicOrderAt_congr (hP.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ ρ₀))]
    exact (meromorphicOrderAt_mul_of_ne_zero (hΓa ρ₀ hρpos)
      (heckeGammaFactor_ne_zero_of_re_pos χ hρpos)).symm
  let ρ : {ρ : ℂ // 0 < meromorphicOrderAt L ρ} := ⟨ρ₀, hordL ▸ hord_f⟩
  have hm : 0 < (meromorphicOrderAt L ρ.val).untop₀.toNat := by
    change 0 < (meromorphicOrderAt L ρ₀).untop₀.toNat
    rw [← hordL]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hn] at hord_f ⊢
    rw [WithTop.untop₀_coe]
    have : 0 < n := WithTop.coe_lt_coe.mp hord_f
    omega
  have hmem : (fun z : ℂ ↦ Complex.exp (z ^ 2)) ∈ schwartzBergmanSubmodule univ := by
    simpa only [preimage_univ, indicator_univ] using
      gaussian_mem_schwartzBergmanSubmodule univ isOpen_univ
  let g : Bergman := ⟨_, hmem⟩
  have key := h (ULift.{u} ℚ) χ τ hτ L hL hLe ρ 0 hm g
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hx : hphase.exists.choose = 1 := by
    refine hphase.unique hphase.exists.choose_spec fun t ↦ ?_
    rw [hχv, Complex.ofReal_one, one_mul]
    change (((↑(ideleNorm (ULift.{u} ℚ) (τ t)) : NNReal) : ℝ) : ℂ) ^ Complex.I = _
    rw [hτ t]
  have hmom := (schwartzBergman_jet_eq_mellinInv_moment g (ρ₀ + Complex.I) 0).2.2
  simp only [] at key hmom
  rw [hx, Complex.ofReal_one, one_mul, ← hmom] at key
  simp only [iteratedDeriv_zero] at key
  change Complex.exp (ρ₀ ^ 2) = Complex.exp ((ρ₀ + Complex.I) ^ 2) at key
  have hn := congrArg (fun z : ℂ ↦ ‖z‖) key
  simp only [Complex.norm_exp] at hn
  have hre := Real.exp_injective hn
  have hγ1 : 1 < γ := by linarith [hγ.1]
  simp [ρ₀, sq, Complex.mul_re, Complex.mul_im] at hre
  nlinarith

/-- Paper: Theorem 7.1.4.2(2), equation (7.1.4.6), p. 327.
Take ℚ, the pure norm character with exponent i and x₀ = 1. Use the meromorphic
normal form of the shifted completed zeta, with a zero ρ obtained by shifting
a completed zeta zero by −i.
At m = 0 take `φ(s) = (s - ρ) exp(s²)`. The derivative functional is zero, while
the convergent shifted moment is `φ(ρ + i) = i exp((ρ + i)²) ≠ 0`. -/
theorem Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment_false :
    ¬ Printed.schwartzBergman_jet_eq_mellinInv_shifted_moment := by
  intro h
  exact schwartzBergman_jet_eq_mellinInv_shifted_moment_contra h

/-- Paper: Theorem 7.1.4.2(4), p. 327.
As printed: The jet functionals are continuous on the ordinary Schwartz quotient.
The chosen section identifies the isotype with ordinary Schwartz norm profiles.
The denominator consists of the profiles of homogeneous theta functions of polar
tests. On every exponentially decaying profile the functional is the jet in the
Mellin coordinate (7.1.4.1). The repaired estimate
`schwartzBergman_normalizedJets` uses the exponentially decaying tests.
See ERRATA F101, also for the analogous topology in Theorem 7.1.4.3(3). -/
def Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hEq : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : Zeros(L)) (m : ℕ), m < (meromorphicOrderAt L ρ.val).untop₀.toNat →
      let x₀ := (existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose
      let expUnit := fun s : ℝ ↦ (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso s)
      let ω := χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm F).ker →ₜ* C𝔽(F))
      let H := Submodule.span ℂ {f : SchwartzBruhat ℝ≥0ˣ | ∃ a : adelePolarSubspace F,
        ∀ t, f t = homogeneousAdelicThetaLinearMap F ω a.val (QuotientGroup.mk (τ t))}
      ∃ ℓ : (SchwartzBruhat ℝ≥0ˣ ⧸ H) →L[ℂ] ℂ,
        ∀ f : SchwartzBruhat ℝ≥0ˣ, (fun u ↦ f (expUnit u)) ∈ logExponentialDecaySubmodule univ →
          ℓ (Submodule.Quotient.mk f) =
            ∫ u : ℝ, f (expUnit u) * Complex.exp ((ρ.val + (x₀ : ℂ) * Complex.I) * u) *
              (u : ℂ) ^ m


/-- Pullback along the logarithm carries ordinary Schwartz functions continuously
to Schwartz–Bruhat functions on the positive reals. -/
private theorem schwartzBergman_jet_continuous_on_ordinary_schwartz_false_coordinate :
    ∃ T : SchwartzMap ℝ ℂ →L[ℂ] SchwartzBruhat ℝ≥0ˣ,
      ∀ (f : SchwartzMap ℝ ℂ) (u : ℝ),
        T f ((Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso u)) = f u := by
  let I : Set ℝ := {0}
  let P := PositiveRealExponentialDecay I
  have hmem (f : SchwartzMap ℝ ℂ) : (f : ℝ → ℂ) ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).mpr
    intro a
    have ha : (a : ℝ) = 0 := a.property
    change logExponentialWeight a (f : ℝ → ℂ) ∈ realSchwartzCoe.range
    rw [ha, logExponentialWeight_zero]
    exact ⟨f, rfl⟩
  let A : SchwartzMap ℝ ℂ →ₗ[ℂ] P :=
    { toFun := fun f ↦ ⟨f, hmem f⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hA : Continuous A := by
    apply (positiveRealExponentialDecay_isEmbedding I (singleton_nonempty _)).isInducing.continuous_iff.mpr
    apply continuous_pi
    intro a
    have he : (fun f : SchwartzMap ℝ ℂ ↦ logExponentialDecayTwist I a (A f)) = id := by
      funext f
      ext x
      change logExponentialDecayTwist I a ⟨f, hmem f⟩ x = f x
      rw [logExponentialDecayTwist_apply]
      have ha : (a : ℝ) = 0 := a.property
      simp only [ha, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    exact he ▸ continuous_id
  obtain ⟨e, he⟩ := identityModulationExponentialDecay_equiv I ordConnected_singleton (singleton_nonempty _)
  have hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
    ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
      intro h
      have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
      norm_num at this⟩⟩
  obtain ⟨s, hs⟩ := modulatedExponentialDecay_singleton_schwartz
    (ContinuousMonoidHom.id ℝ≥0ˣ) hm surjective_id 0
  refine ⟨s.toContinuousLinearMap.comp (e.toContinuousLinearMap.comp ⟨A, hA⟩), ?_⟩
  intro f u
  change s (e (A f)) _ = _
  let t : ℝ≥0ˣ := (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso u)
  calc
    s (e (A f)) t = modulationWeight (ContinuousMonoidHom.id ℝ≥0ˣ) 0 (e (A f)).val t :=
      congrFun (hs (e (A f))) t
    _ = (e (A f)).val t := congrFun (modulationWeight_zero _ _) t
    _ = (A f).val (Real.log (t.val : ℝ)) := he (A f) t
    _ = f u := by change f (Real.log (Real.exp u)) = f u; rw [Real.log_exp]

/-- Translates of a fixed Schwartz function by `n`, damped by `exp (-c n)` with `c > 0`,
form a bounded set: the polynomial growth of the seminorms in `n` loses to the damping. -/
private theorem schwartzBergman_jet_continuous_on_ordinary_schwartz_false_damped_bounded (c : ℝ) (hc : 0 < c)
    (h : SchwartzMap ℝ ℂ) (G : ℕ → SchwartzMap ℝ ℂ)
    (hG : ∀ (n : ℕ) (x : ℝ), G n x = (Real.exp (-(c * n)) : ℂ) * h (x - n)) :
    Bornology.IsVonNBounded ℂ (range G) := by
  refine (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr ?_
  rintro ⟨k, l⟩
  let Ch := 2 ^ k * (Finset.Iic (k, l)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) h
  have hCh : 0 ≤ Ch := by positivity
  let M := (k.factorial : ℝ) * Real.exp c / c ^ k * Ch
  refine ⟨M + 1, by positivity, ?_⟩
  rintro _ ⟨n, rfl⟩
  refine lt_of_le_of_lt ?_ (lt_add_one M)
  refine SchwartzMap.seminorm_le_bound ℂ k l (G n) (by positivity) fun x ↦ ?_
  have hfun : (G n : ℝ → ℂ) = fun x ↦ (Real.exp (-(c * n)) : ℂ) • h (x - n) :=
    funext fun x ↦ hG n x
  have hd : iteratedFDeriv ℝ l (G n : ℝ → ℂ) x =
      (Real.exp (-(c * n)) : ℂ) • iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n) := by
    have hsm : ContDiffAt ℝ l (fun z : ℝ ↦ h (z - n)) x :=
      ((h.smooth ⊤).comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le
        (by exact_mod_cast le_top)
    rw [hfun, iteratedFDeriv_const_smul_apply' hsm, iteratedFDeriv_comp_sub]
  rw [hd, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hx : ‖x‖ ≤ (1 + n) * (1 + ‖x - n‖) := by
    have : ‖x‖ ≤ ‖x - n‖ + n := by
      have := norm_add_le (x - n) (n : ℝ)
      rwa [sub_add_cancel, Real.norm_natCast] at this
    nlinarith [norm_nonneg (x - n), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, l)) le_rfl le_rfl h
    (x - n)
  have hpow : ‖x‖ ^ k ≤ (1 + n) ^ k * (1 + ‖x - n‖) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hx k
  have hexp : (1 + (n : ℝ)) ^ k * Real.exp (-(c * n)) ≤ (k.factorial : ℝ) * Real.exp c / c ^ k := by
    have h1 := Real.pow_div_factorial_le_exp (x := c * (1 + n)) (by positivity) k
    rw [div_le_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    have h4 : Real.exp (c * (1 + n)) * Real.exp (-(c * n)) = Real.exp c := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + (n : ℝ)) ^ k * Real.exp (-(c * n)) * c ^ k
        = (c * (1 + n)) ^ k * Real.exp (-(c * n)) := by rw [mul_pow]; ring
      _ ≤ (Real.exp (c * (1 + n)) * k.factorial) * Real.exp (-(c * n)) := by gcongr
      _ = k.factorial * Real.exp c := by rw [mul_right_comm, h4, mul_comm]
  calc ‖x‖ ^ k * (Real.exp (-(c * n)) * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖)
      ≤ (1 + n) ^ k * (1 + ‖x - n‖) ^ k *
          (Real.exp (-(c * n)) * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖) := by
        gcongr
    _ = ((1 + n) ^ k * Real.exp (-(c * n))) *
          ((1 + ‖x - n‖) ^ k * ‖iteratedFDeriv ℝ l (h : ℝ → ℂ) (x - n)‖) := by ring
    _ ≤ ((k.factorial : ℝ) * Real.exp c / c ^ k) * Ch := by
        gcongr
    _ = M := rfl

/-- Evaluation of the bilateral Laplace transform at a point of positive real part
cannot extend continuously to the ordinary real-line Schwartz space. -/
private theorem schwartzBergman_jet_continuous_on_ordinary_schwartz_false_moment
    (z : ℂ) (hz : 0 < z.re) (A : SchwartzMap ℝ ℂ →L[ℂ] ℂ)
    (hA : ∀ f : SchwartzMap ℝ ℂ, HasCompactSupport (f : ℝ → ℂ) →
      A f = ∫ x : ℝ, f x * Complex.exp (z * x)) : False := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let h (x : ℝ) : ℂ := (b x : ℂ) * Complex.exp (-z * x)
  have hs : HasCompactSupport h :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hd : ContDiff ℝ (⊤ : ℕ∞) h :=
    (Complex.ofRealCLM.contDiff.comp b.contDiff).mul
      ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  let hS : SchwartzMap ℝ ℂ := hs.toSchwartzMap hd
  let c : ℝ := z.re / 2
  have hc : 0 < c := half_pos hz
  let G (n : ℕ) : SchwartzMap ℝ ℂ :=
    (Real.exp (-(c * n)) : ℂ) • (hS.compSubConstCLM ℂ (n : ℝ))
  have hG (n : ℕ) (x : ℝ) : G n x =
      (Real.exp (-(c * n)) : ℂ) * hS (x - n) := rfl
  have hGs (n : ℕ) : HasCompactSupport (G n : ℝ → ℂ) := by
    have ht := hs.comp_homeomorph (Homeomorph.addRight (-(n : ℝ)))
    change HasCompactSupport (fun x : ℝ ↦ h (x + -(n : ℝ))) at ht
    have ht' : HasCompactSupport (fun x : ℝ ↦ h (x - n)) := by
      simpa only [sub_eq_add_neg] using ht
    exact ht'.mul_left
  have hbounded := schwartzBergman_jet_continuous_on_ordinary_schwartz_false_damped_bounded
    c hc hS G hG
  let B : ℝ := ∫ x : ℝ, b x
  have hB : 0 < B := b.integral_pos
  have hmoment (n : ℕ) : A (G n) =
      (Real.exp (-(c * n)) : ℂ) * Complex.exp (z * (n : ℂ)) * (B : ℂ) := by
    rw [hA (G n) (hGs n)]
    rw [← integral_add_right_eq_self
      (fun x : ℝ ↦ G n x * Complex.exp (z * x)) (n : ℝ)]
    have he (x : ℝ) : G n (x + n) * Complex.exp (z * ((x + n : ℝ) : ℂ)) =
        ((Real.exp (-(c * n)) : ℂ) * Complex.exp (z * (n : ℂ))) * (b x : ℂ) := by
      change (Real.exp (-(c * n)) : ℂ) *
        ((b (x + n - n) : ℂ) * Complex.exp (-z * ((x + n - n : ℝ) : ℂ))) *
        Complex.exp (z * ((x + n : ℝ) : ℂ)) = _
      rw [add_sub_cancel_right]
      simp only [Complex.ofReal_add, Complex.ofReal_natCast]
      have hexp : Complex.exp (-z * (x : ℂ)) *
          Complex.exp (z * ((x : ℂ) + (n : ℂ))) = Complex.exp (z * (n : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        _ = (Real.exp (-(c * n)) : ℂ) * (b x : ℂ) *
            (Complex.exp (-z * (x : ℂ)) *
              Complex.exp (z * ((x : ℂ) + (n : ℂ)))) := by ring
        _ = _ := by rw [hexp]; ring
    rw [integral_congr_ae (ae_of_all volume he), integral_const_mul,
      integral_complex_ofReal]
  have hnorm (n : ℕ) : ‖A (G n)‖ = Real.exp (c * n) * B := by
    rw [hmoment, norm_mul, norm_mul,
      Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp,
      Complex.norm_of_nonneg hB.le]
    have hre : (z * (n : ℂ)).re = z.re * (n : ℝ) := by simp
    rw [hre, ← Real.exp_add]
    have hx : -(c * (n : ℝ)) + z.re * n = c * n := by dsimp [c]; ring
    rw [hx]
  obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' (𝕜 := ℂ)).mp
    (hbounded.image A)
  obtain ⟨n, hn⟩ := exists_nat_gt (R / (c * B))
  have hRlt : R < c * (n : ℝ) * B := by
    have hh := (div_lt_iff₀ (mul_pos hc hB)).mp hn
    nlinarith
  have he : c * (n : ℝ) ≤ Real.exp (c * n) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hRle : Real.exp (c * n) * B ≤ R := by
    rw [← hnorm n]
    exact hR _ ⟨G n, mem_range_self n, rfl⟩
  exact (not_lt_of_ge hRle) (hRlt.trans_le (mul_le_mul_of_nonneg_right he hB.le))

/-- The completed L-function of the trivial character over a universe lift of the
rationals has a finite positive-order zero with real part one half. The witness
comes from the kernel-checked first zero of the Riemann zeta function. -/
private theorem schwartzBergman_jet_continuous_on_ordinary_schwartz_false_zero
    [NumberField (ULift.{u} ℚ)] :
    ∃ L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      (∀ s : Complex.re ⁻¹' Ioi (1 : ℝ),
        L s = completedHeckeL
          (1 : PontryaginDual (IdeleClassGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ))) s) ∧
      ∃ ρ : ℂ, ρ.re = 1 / 2 ∧ 0 < meromorphicOrderAt L ρ ∧
        0 < (meromorphicOrderAt L ρ).untop₀.toNat := by
  let χ : PontryaginDual (IdeleClassGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ)) := 1
  obtain ⟨γ, -, hz⟩ := HardyFirstZero.first_zero_on_line
  have hf : MeromorphicOn riemannZeta univ :=
    schwartzBergman_jet_eq_mellinInv_shifted_moment_meromorphic
  have hfa (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
    apply DifferentiableOn.analyticAt
      (s := {z : ℂ | z ≠ 1})
      (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt)
    exact (isOpen_ne_fun continuous_id continuous_const).mem_nhds hs
  have hfeq (s : Complex.re ⁻¹' Ioi (1 : ℝ)) :
      riemannZeta s = finiteHeckeL χ s := by
    rw [schwartzBergman_jet_eq_mellinInv_shifted_moment_one,
      schwartzBergman_jet_eq_mellinInv_shifted_moment_dedekindZeta,
      schwartzBergman_jet_eq_mellinInv_shifted_moment_rat s.property]
  have hΓa (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor χ) s := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  let f : ℂ → ℂ := fun s ↦ heckeGammaFactor χ s * riemannZeta s
  have hf' : MeromorphicOn f univ := fun s _ ↦
    (meromorphic_heckeGammaFactor χ s).mul (hf s (mem_univ s))
  let L := toMeromorphicNFOn f univ
  have hL : MeromorphicNFOn L univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hLe (s : Complex.re ⁻¹' Ioi (1 : ℝ)) : L s = completedHeckeL χ s := by
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hne : (s : ℂ) ≠ 1 := fun h1 ↦ by
      have hh : 1 < (s : ℂ).re := s.property
      rw [h1, Complex.one_re] at hh
      exact lt_irrefl _ hh
    have ha : AnalyticAt ℂ f s := (hΓa s hs).mul (hfa s hne)
    change toMeromorphicNFOn f univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf' (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ha.meromorphicNFAt]
    change heckeGammaFactor χ s * riemannZeta s = _
    rw [hfeq s]
    rfl
  let ρ : ℂ := 1 / 2 + γ * Complex.I
  have hρre : ρ.re = 1 / 2 := by simp [ρ]
  have hρne : ρ ≠ 1 := fun h1 ↦ by
    have hh := congrArg Complex.re h1
    rw [hρre, Complex.one_re] at hh
    norm_num at hh
  have hρpos : 0 < ρ.re := by rw [hρre]; norm_num
  have hzρ : riemannZeta ρ = 0 := hz
  have hord : 0 < meromorphicOrderAt riemannZeta ρ := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hf _ (mem_univ _))).mp
    rw [← hzρ]
    exact (hfa ρ hρne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta 2 ≠ ⊤ := by
    have hv : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
    rw [(hfa 2 (by norm_num)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hv]
    exact WithTop.zero_ne_top
  have hfin : meromorphicOrderAt riemannZeta ρ ≠ ⊤ := fun ht ↦ htwo
    (hf.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (mem_univ _)
      (mem_univ _) ht)
  have hordL : meromorphicOrderAt riemannZeta ρ = meromorphicOrderAt L ρ := by
    rw [meromorphicOrderAt_congr (hf'.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ ρ))]
    exact (meromorphicOrderAt_mul_of_ne_zero (hΓa ρ hρpos)
      (heckeGammaFactor_ne_zero_of_re_pos χ hρpos)).symm
  have hm : 0 < (meromorphicOrderAt L ρ).untop₀.toNat := by
    rw [← hordL]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfin
    rw [← hn] at hord ⊢
    rw [WithTop.untop₀_coe]
    have : 0 < n := WithTop.coe_lt_coe.mp hord
    omega
  exact ⟨L, hL, hLe, ρ, hρre, hordL ▸ hord, hm⟩

/-- A continuous functional with the printed jet moments contradicts the
bounded family of damped translates at a completed-zeta zero. -/
private theorem schwartzBergman_jet_continuous_on_ordinary_schwartz_false_contra
    (h : Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz.{u}) : False := by
  have : NumberField (ULift.{u} ℚ) :=
    schwartzBergman_jet_eq_mellinInv_shifted_moment_numberField
  obtain ⟨L, hL, hEq, ρ₀, hρre, hord, hm⟩ :=
    schwartzBergman_jet_continuous_on_ordinary_schwartz_false_zero.{u}
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ) :=
    ⟨canonicalIdeleNormSection _, canonicalIdeleNormSection_continuous _⟩
  have hτ : Function.RightInverse τ (ideleNorm (ULift.{u} ℚ)) :=
    canonicalIdeleNormSection_rightInverse _
  let ρ : {z : ℂ // 0 < meromorphicOrderAt L z} := ⟨ρ₀, hord⟩
  obtain ⟨ℓ, hℓ⟩ := h (ULift.{u} ℚ) 1 τ hτ L hL hEq ρ 0 hm
  obtain ⟨T, hT⟩ :=
    schwartzBergman_jet_continuous_on_ordinary_schwartz_false_coordinate
  let x₀ := (existsUnique_ideleNormSection_character_phase
    (1 : PontryaginDual (IdeleClassGroup (𝓞 (ULift.{u} ℚ)) (ULift.{u} ℚ))) τ hτ).exists.choose
  let z : ℂ := ρ₀ + (x₀ : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z, hρre]
  let A : SchwartzMap ℝ ℂ →L[ℂ] ℂ :=
    ℓ.comp ((Submodule.mkQL _).comp T)
  apply schwartzBergman_jet_continuous_on_ordinary_schwartz_false_moment z hz A
  intro f hf
  have hmem : (fun u : ℝ ↦ T f
      ((Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso u))) ∈
      logExponentialDecaySubmodule univ := by
    simpa only [hT] using
      mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hf (f.smooth ⊤)
  change ℓ (Submodule.Quotient.mk (T f)) = _
  simpa only [hT, pow_zero, mul_one] using hℓ (T f) hmem

/-- Paper: Theorem 7.1.4.2(4), p. 327.
Take the trivial rational character, a completed zeta zero ρ with a = Re ρ > 0,
and m = 0. For a nonzero nonnegative compactly supported smooth bump b, the
profile `h(u) = b(u) exp(-ρu)` has positive ρ-moment. The damped translates
`exp(-an/2) h(u - n)` form a bounded set in ordinary Schwartz space, while their
ρ-moments have unbounded modulus. -/
theorem Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz_false :
    ¬ Printed.schwartzBergman_jet_continuous_on_ordinary_schwartz := by
  intro h
  exact schwartzBergman_jet_continuous_on_ordinary_schwartz_false_contra h


/-- Paper: Estimate after equation (7.1.4.22), p. 330.
As printed: The norm of the normalized derivative throughout the closed critical strip
is at most 1/(2π) times the larger of the two vertical L¹ norms. The equicontinuity
statement is `schwartzBergman_normalizedJets`. See ERRATA F102. -/
def Printed.schwartzBergman_normalizedJet_le_max : Prop :=
  ∀ (f : Bergman) (s : ℂ), s.re ∈ Icc 0 1 → ∀ k : ℕ,
    let lineNorm (σ : ℝ) :=
      ∫ y : ℝ, ‖f.val ((σ : ℂ) + (y : ℂ) * Complex.I)‖
    ‖iteratedDeriv k f.val s / (k.factorial : ℂ)‖ ≤
      (2 * Real.pi)⁻¹ * max (lineNorm (-1)) (lineNorm 2)

private theorem schwartzBergman_normalizedJet_le_max_mem :
    (fun z : ℂ ↦ Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)) ∈ schwartzBergmanSubmodule univ := by
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, ?_, ?_⟩
  · exact (by fun_prop : Differentiable ℂ (fun z : ℂ ↦ Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)))
      |>.differentiableOn
  · intro a b _ _ N
    let M := max |a| |b|
    refine ⟨N.factorial * Real.exp (M + 9 / 8 + 2 / 9 * (2 * M ^ 2 + 1 / 2)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hstrip : z.re ∈ Icc a b := hz
    have hM : |z.re| ≤ M := abs_le_max_abs_abs hstrip.1 hstrip.2
    have hsq : z.re ^ 2 ≤ M ^ 2 := by
      simpa using pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hweight : ‖z‖ ^ N ≤ N.factorial * Real.exp ‖z‖ := by
      have h := (div_le_iff₀ (show 0 < (N.factorial : ℝ) by positivity)).mp
        (Real.pow_div_factorial_le_exp ‖z‖ (norm_nonneg z) N)
      simpa [mul_comm] using h
    have hz' : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : (2 / 9 * (z - 1 / 2) ^ 2 : ℂ).re = 2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2) := by
      simp [sq, Complex.mul_re, Complex.mul_im]
    change ‖z ^ N * Complex.exp (2 / 9 * (z - 1 / 2) ^ 2)‖ ≤ _
    rw [norm_mul, norm_pow, Complex.norm_exp, hre]
    calc
      _ ≤ (N.factorial * Real.exp ‖z‖) * Real.exp (2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = N.factorial * Real.exp (‖z‖ + 2 / 9 * ((z.re - 1 / 2) ^ 2 - z.im ^ 2)) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        have h1 : |z.im| - 2 / 9 * z.im ^ 2 ≤ 9 / 8 := by
          nlinarith [sq_nonneg (|z.im| - 9 / 4), sq_abs z.im]
        nlinarith [sq_nonneg (z.re + 1 / 2)]

private theorem schwartzBergman_normalizedJet_le_max_line (σ : ℝ) (hσ : (σ - 1 / 2) ^ 2 = 9 / 4) :
    ∫ y : ℝ, ‖Complex.exp (2 / 9 * (((σ : ℂ) + (y : ℂ) * Complex.I) - 1 / 2) ^ 2)‖ =
      Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) := by
  have hpt (y : ℝ) : ‖Complex.exp (2 / 9 * (((σ : ℂ) + (y : ℂ) * Complex.I) - 1 / 2) ^ 2)‖ =
      Real.exp (1 / 2) * Real.exp (-(2 / 9) * y ^ 2) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [sq, Complex.mul_re, Complex.mul_im]
    nlinarith [hσ]
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian]

private theorem schwartzBergman_normalizedJet_le_max_num :
    (2 * Real.pi)⁻¹ * (Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9))) < 1 := by
  have hpi := Real.pi_gt_d2
  have he := Real.exp_one_lt_d9
  have hpos : 0 < Real.pi := Real.pi_pos
  rw [inv_mul_lt_iff₀ (by positivity), mul_one]
  have hx : 0 ≤ Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) := by positivity
  apply lt_of_pow_lt_pow_left₀ 2 (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
  norm_num
  nlinarith

/-- Paper: Estimate after equation (7.1.4.22), p. 330.
Use `Φ(s) = exp(2 (s - 1/2)^2 / 9)`, s = 1/2, and k = 0. The left side is 1.
Each line norm is `3 √(π e/2)`, so the right side is `√(9 e/(8π)) < 1`. -/
theorem Printed.schwartzBergman_normalizedJet_le_max_false :
    ¬ Printed.schwartzBergman_normalizedJet_le_max := by
  intro h
  let f : schwartzBergmanSubmodule univ := ⟨_, schwartzBergman_normalizedJet_le_max_mem⟩
  have key := h f ((1 / 2 : ℝ) : ℂ) (by norm_num) 0
  have hl : ∀ σ : ℝ, (σ - 1 / 2) ^ 2 = 9 / 4 →
      ∫ y : ℝ, ‖f.val ((σ : ℂ) + (y : ℂ) * Complex.I)‖ =
        Real.exp (1 / 2) * Real.sqrt (Real.pi / (2 / 9)) :=
    schwartzBergman_normalizedJet_le_max_line
  have h1 : ‖iteratedDeriv 0 f.val ((1 / 2 : ℝ) : ℂ) / ((Nat.factorial 0 : ℕ) : ℂ)‖ = 1 := by
    simp [f]
  simp only [] at key
  rw [h1, hl (-1) (by norm_num), hl 2 (by norm_num), max_self] at key
  exact absurd key (not_le.mpr schwartzBergman_normalizedJet_le_max_num)

section Orbital

variable {F : Type u} [Field F] [NumberField F]

open Classical in
/-- Paper: Equation (7.1.4.24), p. 331.
The prime block spans the derivative evaluations over all zeros of that prime's
Euler polynomial, with the order cutoff taken from that polynomial alone. -/
def Printed.orbitalPrimeJetSpace (χ : U𝔽(F)) (S₀ : Finset Places(F)) (p : RatPrimes) :
    Submodule ℂ (StrongDual ℂ Entire) :=
  let P := reciprocalPartialHeckeEulerProduct χ overₚ(S₀, p)
  Submodule.span ℂ {ℓ | ∃ (ε : ℂ) (m : ℕ),
    m < (meromorphicOrderAt P ε).untop₀.toNat ∧ ℓ = entireJet ε m}

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
As printed: The orbital strong annihilator is linearly and topologically isomorphic
to the product of the separate prime blocks and the product of the completed Hecke jets.
Each prime block uses the zeros of its own Euler polynomial. The corrected decomposition
`orbitalAnnihilator_directSum` uses the order of the full generator at each point.
See ERRATA F99 and F103. -/
def Printed.orbitalAnnihilator_prime_products : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hEq : ∀ s : halfPlane, L s = completedHeckeL χ s),
    let g := orbitalHeckeGenerator χ τ hτ L hL hEq S₀
    let primes := {p : RatPrimes // ∃ v ∈ S₀, HeightOneSpectrum.under (𝓞 ℚ) v = p}
    Nonempty (((∀ p : primes, ↥(Printed.orbitalPrimeJetSpace χ S₀ p.val)) ×
      (∀ ρ : Zeros(L), ↥(Jet(L, ρ.val)))) ≃L[ℂ] entireIdealAnnihilator g)

/-- Paper: Theorem 7.1.4.3(1), equations (7.1.4.23)–(7.1.4.25), p. 331.
Take ℚ, the trivial character and S₀ consisting of the places above 2 and 3. The
annihilator of the entire generator consists of finite-support jets at countably
many zeros, while the product of the completed zeta jets has uncountable dimension.
At the origin the regularized completed zeta is nonzero, and each prime block
contributes the same value functional. Their difference vanishes under the jet
identification, and the first derivative at the resulting double zero is missing. -/
theorem Printed.orbitalAnnihilator_prime_products_false :
    ¬ Printed.orbitalAnnihilator_prime_products := by
  intro h
  apply Printed.spectralAnnihilator_product_false
  intro F _ _ χ τ hτ L hL hEq
  let P := {p : RatPrimes // ∃ v ∈ (∅ : Finset Places(F)),
    HeightOneSpectrum.under (𝓞 ℚ) v = p}
  let A := ∀ p : P, ↥(Printed.orbitalPrimeJetSpace χ ∅ p.val)
  let B := ∀ ρ : Zeros(L), ↥(Jet(L, ρ.val))
  have : IsEmpty P := ⟨fun p => by obtain ⟨v, hv, _⟩ := p.property; simp at hv⟩
  let : Unique A := { default := 0, uniq := fun a => Subsingleton.elim _ _ }
  obtain ⟨e⟩ := h F χ ∅ τ hτ L hL hEq
  rw [orbitalHeckeGenerator_empty] at e
  exact ⟨(ContinuousLinearEquiv.uniqueProd ℂ B A).symm.trans e⟩

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
As printed: The space of all jets associated with a rational prime block is
finite-dimensional. The fixed-zero dimension is computed by `entireJetSpace_finrank`,
and `orbitalAnnihilator_directSum` uses one space per zero. See ERRATA F104. -/
def Printed.orbitalPrimeJetSpace_finite : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (χ : U𝔽(F)) (S₀ : Finset Places(F))
    (p : RatPrimes), (∃ v ∈ S₀, v.under (𝓞 ℚ) = p) →
      Module.Finite ℂ (Printed.orbitalPrimeJetSpace χ S₀ p)

private theorem orbitalPrimeJetSpace_finite_order (q : ℝ) (hq : 1 < q) (z : ℂ)
    (hz : (q : ℂ) ^ (-z) = 1) :
    0 < (meromorphicOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z).untop₀.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have han : AnalyticAt ℂ (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z :=
    Differentiable.analyticAt (fun w ↦
      (((hasDerivAt_neg w).const_cpow (Or.inl hq0)).const_sub 1).differentiableAt) z
  have hd : HasDerivAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s))
      (-((q : ℂ) ^ (-z) * Complex.log q * (-1))) z :=
    ((hasDerivAt_neg z).const_cpow (Or.inl hq0)).const_sub 1
  have hlog : Complex.log (q : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_log (by linarith)]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have hne : analyticOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have h0 : deriv (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z = 0 := by
      rw [Filter.EventuallyEq.deriv_eq (show (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) =ᶠ[𝓝 z]
        fun _ ↦ (0 : ℂ) from htop)]
      simp
    rw [hd.deriv, hz] at h0
    simp [hlog] at h0
  have hpos : analyticOrderAt (fun s : ℂ ↦ 1 - (q : ℂ) ^ (-s)) z ≠ 0 := by
    rw [ne_eq, han.analyticOrderAt_eq_zero, not_not]
    simp [hz]
  rw [han.meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hpos ⊢
  have : n ≠ 0 := by exact_mod_cast hpos
  simp
  omega

private theorem orbitalPrimeJetSpace_finite_linearIndependent (z : ℕ → ℂ) (hz : Injective z) :
    LinearIndependent ℂ (fun k ↦ entireJet (z k) 0) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  let p : Subtype (fun f : C(ℂ, ℂ) ↦ f ∈ entireContinuousMapSubalgebra) :=
    ⟨⟨fun w ↦ ∏ j ∈ s.erase i, (w - z j), by fun_prop⟩,
      (by fun_prop : Differentiable ℂ (fun w : ℂ ↦ ∏ j ∈ s.erase i, (w - z j)))⟩
  have hp := congrArg (fun ℓ : StrongDual ℂ _ ↦ ℓ p) hg
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, entireJet_apply, iteratedDeriv_zero, smul_eq_mul] at hp
  rw [Finset.sum_eq_single i] at hp
  · have hne : (∏ j ∈ s.erase i, (z i - z j)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj
      exact sub_ne_zero.mpr fun h ↦ (Finset.ne_of_mem_erase hj) (hz h).symm
    exact (mul_eq_zero.mp hp).resolve_right hne
  · intro j hj hji
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, hj⟩) (sub_self _)
  · intro h; exact absurd hi h

open Classical in
private theorem orbitalPrimeJetSpace_finite_aux (F : Type*) [Field F] [NumberField F]
    (h : ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
      (p : HeightOneSpectrum (𝓞 ℚ)), (∃ v ∈ S₀, v.under (𝓞 ℚ) = p) →
        Module.Finite ℂ (Printed.orbitalPrimeJetSpace χ S₀ p)) : False := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hone :
      ∀ g, ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 g = 1 := by
    intro g
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).restrict v x =
        1 := by
    intro x hx
    rw [show x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
      HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    simp [hone]
  have hunr :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).IsUnramifiedAt
        v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro x
    exact hres _ (by simp)
  let p := v.under (𝓞 ℚ)
  have hfin := h 1 {v} p ⟨v, Finset.mem_singleton_self v, rfl⟩
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hP : reciprocalPartialHeckeEulerProduct (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
      (({v} : Finset (HeightOneSpectrum (𝓞 F))).filter (fun w ↦ w.under (𝓞 ℚ) = p)) =
      fun s ↦ 1 - (q : ℂ) ^ (-s) := by
    rw [Finset.filter_singleton, ite_eq_left rfl]
    funext s
    rw [reciprocalPartialHeckeEulerProduct_singleton _ v hunr,
      hunr.localValue_eq _ Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
      hres _ (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)]
    simp [q]
  have hlog : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  let c : ℂ := 2 * Real.pi * Complex.I / Real.log q
  have hc : c ≠ 0 := div_ne_zero (by simp [Real.pi_ne_zero]) hlog
  let z : ℕ → ℂ := fun k ↦ (k : ℂ) * c
  have hz : Injective z := fun a b hab ↦ by
    exact_mod_cast mul_right_cancel₀ hc hab
  have hzq (k : ℕ) : (q : ℂ) ^ (-z k) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)),
      ← Complex.ofReal_log (by linarith), Complex.exp_eq_one_iff]
    refine ⟨-(k : ℤ), ?_⟩
    simp only [z, c]
    field_simp
    push_cast
    ring
  have hmem (k : ℕ) : entireJet (z k) 0 ∈
      Printed.orbitalPrimeJetSpace (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {v} p := by
    apply Submodule.subset_span
    refine ⟨z k, 0, ?_, rfl⟩
    rw [hP]
    exact orbitalPrimeJetSpace_finite_order q hq (z k) (hzq k)
  have hli := orbitalPrimeJetSpace_finite_linearIndependent z hz
  have hli' : LinearIndependent ℂ (fun k ↦ (⟨entireJet (z k) 0, hmem k⟩ :
      Printed.orbitalPrimeJetSpace (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) {v} p)) :=
    LinearIndependent.of_comp (Submodule.subtype _) hli
  have := hli'.finite
  exact not_finite ℕ

/-- Paper: Theorem 7.1.4.3(1), equation (7.1.4.24), p. 331.
Take the trivial rational character and S₀ consisting of the place above 2.
The polynomial `1 - 2^(-s)` has a simple zero at each `2πim/log 2`. Evaluations
at these distinct points are linearly independent by interpolation with polynomials
on any finite subset. -/
theorem Printed.orbitalPrimeJetSpace_finite_false :
    ¬ Printed.orbitalPrimeJetSpace_finite := by
  intro h
  -- Lift ℚ to the universe quantified over by the printed claim.
  let : Field (ULift ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact orbitalPrimeJetSpace_finite_aux (ULift ℚ) (h (ULift ℚ))

end Orbital

end RiemannMasullo
