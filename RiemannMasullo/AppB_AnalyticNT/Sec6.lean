module

public import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.ForMathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Basic
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.WienerIkehara
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.External.Grh.Lemmas.AnalyticGoodHeightDisk
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.EulerProduct.Basic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction

/-!
# Classical zero-free regions for Hecke L-functions

Masullo, §B.6, pp. 636–643. The finite Hecke L-function is represented by a
meromorphic continuation in normal form, as in §B.1.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "𝒳[" F "]" => HeckeCharacter (𝓞 F) F
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "atHeight" => comap (abs ∘ Complex.im) atTop
local notation "atAbsTop" => comap (abs : ℝ → ℝ) atTop

/-- Paper: §B.6.1.2, p. 636. The value at a nonzero integral ideal is the
product of local uniformizer values with the ideal's prime exponents. At a
ramified prime the local value used in this product is zero.
Deviation: The value at the zero ideal is set to zero. -/
def heckeIdealValue (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  open Classical in
  if I = ⊥ then 0 else
    ∏ᶠ v : HeightOneSpectrum (𝓞 F),
      (if χ.IsUnramifiedAt v then χ.localValue v else 0) ^ multiplicity v.asIdeal I

open Classical in
/-- Paper: §B.6.1.2, p. 636. The value on a positive power of a prime ideal
is the corresponding power of the local value, or zero at a ramified prime. -/
theorem heckeIdealValue_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    {k : ℕ} (hk : 0 < k) :
    heckeIdealValue χ (v.asIdeal ^ k) =
      if χ.IsUnramifiedAt v then χ.localValue v ^ k else 0 := by
  have hne : v.asIdeal ^ k ≠ ⊥ := pow_ne_zero _ v.ne_bot
  unfold heckeIdealValue
  rw [ite_eq_right hne, finprod_eq_single _ v, multiplicity_pow_self_of_prime v.prime]
  · split_ifs <;> simp [hk.ne']
  · intro w hw
    rw [multiplicity_eq_zero_of_not_dvd fun hd ↦ hw (HeightOneSpectrum.eq_of_dvd_pow hd), pow_zero]

/-- Paper: Equation (B.6.1.2), p. 636. To the right of one, the series indexed
by nonzero integral ideals converges absolutely to the finite Hecke L-function. -/
theorem finiteHeckeL_hasSum_ideals (χ : U[F]) (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealValue (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ))
      (finiteHeckeL χ s) := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor, multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero),
        pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have ha (v : HeightOneSpectrum (𝓞 F)) : ‖a v‖ ≤ 1 := by
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [a, h, norm_ideleClassNormTwist_zero_localValue]
  have hc (I : Ideal (𝓞 F)) : ‖c I‖ ≤ 1 := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      exact zero_le_one
    change ‖value I‖ ≤ 1
    rw [hvalue hI, finprod_eq_prod _ (hsupport I), norm_prod]
    exact Finset.prod_le_one₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ by
      simp only [factor, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (ha v)
  let term : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := fun I ↦ c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
      map_zero' := by rw [map_zero c, zero_mul]
      map_one' := by rw [map_one c, map_one, Nat.cast_one, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      map_mul' := by
        intro I J
        rw [map_mul c, map_mul, Nat.cast_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg I.absNorm) (Nat.cast_nonneg J.absNorm)]
        ring }
  have hr : 1 < (s : ℂ).re := s.property
  have hbound (I : Ideal (𝓞 F)) : ‖term I‖ ≤ (I.absNorm : ℝ) ^ (-(s : ℂ).re) := by
    by_cases hI : I = 0
    · rw [hI, map_zero, norm_zero]
      positivity
    have hN : (0 : ℝ) < I.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (by simpa only [Ideal.zero_eq_bot] using hI))
    change ‖c I * ((I.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.neg_re]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hN.le _) (hc I)
  have hsum : Summable (fun I ↦ ‖term I‖) :=
    (summable_absNorm_rpow F hr).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbound
  have hprod := hasProd_eulerFactors_of_summable
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal) (fun v ↦ v.prime) hd
    (fun I hI h1 ↦ by
      obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal (by simpa only [Ideal.one_eq_top] using h1)
      exact ⟨⟨J, hJ.isPrime, fun h ↦ hI (le_bot_iff.mp (h ▸ hIJ))⟩, Ideal.dvd_iff_le.mpr hIJ⟩)
    term hsum (fun v ↦ by
      have hv : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      have hlt := (hbound v.asIdeal).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith : -(s : ℂ).re < 0))
      exact fun h ↦ (ne_of_lt hlt) (by rw [h, norm_one]))
  have hlocal (v : HeightOneSpectrum (𝓞 F)) :
      finiteHeckeEulerFactor χ v s = (1 - term v.asIdeal)⁻¹ := by
    change _ = (1 - c v.asIdeal * ((v.asIdeal.absNorm : ℝ) : ℂ) ^ (-(s : ℂ)))⁻¹
    rw [hcPrime, Complex.ofReal_natCast]
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, a, h]
  have hEq : (∑' I, term I) = finiteHeckeL χ s :=
    (hprod.congr_fun hlocal).unique (finiteHeckeL_hasProd χ s)
  have hsupport' : Function.support (term : Ideal (𝓞 F) → ℂ) ⊆ {I | I ≠ ⊥} := by
    intro I hI hBot
    exact hI ((show I = 0 by simpa only [Ideal.zero_eq_bot] using hBot) ▸ term.map_zero)
  refine ((hasSum_subtype_iff_of_support_subset hsupport').mpr
    (hEq ▸ hsum.of_norm.hasSum)).congr_fun fun I ↦ ?_
  change value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ) =
    value I.val * ((I.val.absNorm : ℝ) : ℂ) ^ (-(s : ℂ))
  rw [Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

/-- Paper: Equation (B.6.1.3), p. 636. The summatory function adds the values
at nonzero integral ideals of norm at most `x`. -/
def heckeIdealSummatory (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.3), p. 636. At `x = 1` only the unit ideal contributes. -/
theorem heckeIdealSummatory_one (χ : 𝒳[F]) : heckeIdealSummatory χ 1 = 1 := by
  have hmem : ∀ I : Ideal (𝓞 F), I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1 ↔ I = ⊤ := fun I ↦ by
    constructor
    · rintro ⟨h0, h1⟩
      have h1' : Ideal.absNorm I ≤ 1 := by exact_mod_cast h1
      have h0' : Ideal.absNorm I ≠ 0 := fun h ↦ h0 (Ideal.absNorm_eq_zero_iff.mp h)
      exact Ideal.absNorm_eq_one_iff.mp (by omega)
    · rintro rfl
      exact ⟨top_ne_bot, by simp⟩
  let : Unique {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ 1} :=
    { default := ⟨⊤, (hmem ⊤).mpr rfl⟩
      uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
  unfold heckeIdealSummatory
  rw [finsum_unique]
  show heckeIdealValue χ ⊤ = 1
  unfold heckeIdealValue
  rw [ite_eq_right top_ne_bot]
  refine finprod_eq_one_of_forall_eq_one fun w ↦ ?_
  rw [← Ideal.one_eq_top, multiplicity_one_right, pow_zero]

/-- Paper: Equation (B.6.1.4), p. 636. The coefficient at `x` sums the
values at nonzero integral ideals of norm exactly `x`. The sum is zero if
there are no such ideals. -/
def heckeNormCoefficient (χ : 𝒳[F]) (x : ℝ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = x}, heckeIdealValue χ I.val

/-- Paper: Equation (B.6.1.4), p. 636. At natural numbers the coefficients
agree with the coefficients of Mathlib's formal Euler product. -/
theorem heckeNormCoefficient_natCast (χ : 𝒳[F]) (m : ℕ) :
    heckeNormCoefficient χ (m : ℝ) = χ.LFunction m := by
  classical
  let a (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
    if χ.IsUnramifiedAt v then χ.localValue v else 0
  let factor (I : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) :=
    a v ^ multiplicity v.asIdeal I
  let value := heckeIdealValue χ
  have hzero : value 0 = 0 := by simp [value, heckeIdealValue]
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ 0) : value I = ∏ᶠ v, factor I v := by
    have hI' : I ≠ ⊥ := by simpa only [Ideal.zero_eq_bot] using hI
    simp only [value, heckeIdealValue, ite_eq_right hI', factor, a]
  have hsupport (I : Ideal (𝓞 F)) : (factor I).HasFiniteMulSupport :=
    UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity a
      HeightOneSpectrum.asIdeal_injective HeightOneSpectrum.irreducible
  let c : Ideal (𝓞 F) →*₀ ℂ :=
    { toFun := value
      map_zero' := hzero
      map_one' := by
        rw [hvalue one_ne_zero]
        exact finprod_eq_one_of_forall_eq_one fun v ↦ by
          simp only [factor, multiplicity_one_right, pow_zero]
      map_mul' := by
        intro I J
        by_cases hI : I = 0
        · simp only [hI, zero_mul, hzero]
        by_cases hJ : J = 0
        · simp only [hJ, mul_zero, hzero]
        rw [hvalue (mul_ne_zero hI hJ), hvalue hI, hvalue hJ,
          ← finprod_mul_distrib (hsupport I) (hsupport J)]
        apply finprod_congr
        intro v
        simp only [factor, multiplicity_mul v.prime
          (FiniteMultiplicity.of_prime_left v.prime (mul_ne_zero hI hJ)), pow_add] }
  have hd (v w : HeightOneSpectrum (𝓞 F)) (h : v.asIdeal ∣ w.asIdeal) : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp h)).symm
  have hcPrime (v : HeightOneSpectrum (𝓞 F)) : c v.asIdeal = a v := by
    change value v.asIdeal = _
    rw [hvalue v.prime.ne_zero, finprod_eq_single _ v]
    · simp only [factor,
        multiplicity_self (FiniteMultiplicity.of_prime_left v.prime v.prime.ne_zero), pow_one]
    · intro w hw
      simp only [factor, multiplicity_eq_zero_of_not_dvd (fun h ↦ hw (hd w v h)), pow_zero]
  have hN (v : HeightOneSpectrum (𝓞 F)) : 1 < v.asIdeal.absNorm :=
    NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hE (v : HeightOneSpectrum (𝓞 F)) : χ.localEulerFactor v =
      ArithmeticFunction.ofPowerSeries v.asIdeal.absNorm (PowerSeries.mk fun k ↦ a v ^ k) := by
    rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
      hecke_localPowerSeries_eq_mk]
  have hEpow (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) :
      χ.localEulerFactor v (v.asIdeal.absNorm ^ k) = a v ^ k := by
    rw [hE, ArithmeticFunction.ofPowerSeries_apply_pow (hN v), PowerSeries.coeff_mk]
  have hEne (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (h : χ.localEulerFactor v d ≠ 0) :
      v.asIdeal.absNorm ^ Nat.log v.asIdeal.absNorm d = d := by
    by_contra hk
    apply h
    rw [hE, ArithmeticFunction.ofPowerSeries_apply (hN v), Function.extend_apply']
    · rfl
    rintro ⟨k, rfl⟩
    exact hk (by rw [Nat.log_pow (hN v)])
  let U (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) : Finset (Ideal (𝓞 F)) :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).toFinset.filter fun I ↦ ∀ v, v.asIdeal ∣ I → v ∈ S
  have hmemU {S : Finset (HeightOneSpectrum (𝓞 F))} {n : ℕ} {I : Ideal (𝓞 F)} :
      I ∈ U S n ↔ I.absNorm = n ∧ ∀ v, v.asIdeal ∣ I → v ∈ S := by
    simp [U]
  have key (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) :
      (∏ v ∈ S, χ.localEulerFactor v) n = ∑ I ∈ U S n, c I := by
    induction S using Finset.induction_on generalizing n with
    | empty =>
      have hU (I : Ideal (𝓞 F)) (hI : I ∈ U ∅ n) : I = ⊥ ∨ I = ⊤ := by
        by_contra! h
        obtain ⟨J, hJ, hIJ⟩ := I.exists_le_maximal h.2
        have hv := (hmemU.mp hI).2 ⟨J, hJ.isPrime, fun hJ0 ↦ h.1 (le_bot_iff.mp (hJ0 ▸ hIJ))⟩
          (Ideal.dvd_iff_le.mpr hIJ)
        simp at hv
      rw [Finset.prod_empty]
      by_cases hn : n = 1
      · subst hn
        rw [ArithmeticFunction.one_one,
          Finset.sum_eq_single_of_mem ⊤ (hmemU.mpr ⟨Ideal.absNorm_top, by
          intro v hv
          exact absurd (Ideal.dvd_iff_le.mp hv) (fun h ↦ v.isPrime.ne_top (top_le_iff.mp h))⟩)]
        · rw [← Ideal.one_eq_top, map_one]
        · intro I hI hIt
          rcases hU I hI with rfl | rfl
          · rw [← Ideal.zero_eq_bot, _root_.map_zero]
          · exact absurd rfl hIt
      · rw [ArithmeticFunction.one_apply_ne hn]
        refine (Finset.sum_eq_zero fun I hI ↦ ?_).symm
        rcases hU I hI with rfl | rfl
        · rw [← Ideal.zero_eq_bot, _root_.map_zero]
        · exact absurd ((hmemU.mp hI).1.symm.trans Ideal.absNorm_top) hn
    | insert w S hw ih =>
      have hw0 : w.asIdeal ≠ 0 := w.prime.ne_zero
      rw [Finset.prod_insert hw, ArithmeticFunction.mul_apply]
      simp_rw [ih, Finset.mul_sum]
      rw [Finset.sum_sigma']
      refine Finset.sum_bij_ne_zero
        (fun p _ _ ↦ w.asIdeal ^ Nat.log w.asIdeal.absNorm p.1.1 * p.2) ?_ ?_ ?_ ?_
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp
        have hk := hEne w d (left_ne_zero_of_mul hne)
        refine hmemU.mpr ⟨?_, fun v hv ↦ ?_⟩
        · rw [map_mul, map_pow, hk, hp.2.1, hp.1.1]
        · rcases v.prime.dvd_or_dvd hv with h | h
          · exact Finset.mem_insert.mpr (Or.inl (hd v w (v.prime.dvd_of_dvd_pow h)))
          · exact Finset.mem_insert_of_mem (hp.2.2 v h)
      · have hmult (k : ℕ) (J : Ideal (𝓞 F)) (hJ : J ≠ 0) (hwJ : ¬ w.asIdeal ∣ J) :
            multiplicity w.asIdeal (w.asIdeal ^ k * J) = k := by
          rw [multiplicity_mul w.prime (FiniteMultiplicity.of_prime_left w.prime
            (mul_ne_zero (pow_ne_zero _ hw0) hJ)), multiplicity_pow_self_of_prime w.prime,
            multiplicity_eq_zero_of_not_dvd hwJ, add_zero]
        rintro ⟨⟨d, e⟩, J⟩ hp hne ⟨⟨d', e'⟩, J'⟩ hp' hne' heq
        rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU] at hp hp'
        have hJ : J ≠ 0 := fun h ↦ hne (by rw [h, _root_.map_zero, mul_zero])
        have hJ' : J' ≠ 0 := fun h ↦ hne' (by rw [h, _root_.map_zero, mul_zero])
        have hwJ : ¬ w.asIdeal ∣ J := fun h ↦ hw (hp.2.2 w h)
        have hwJ' : ¬ w.asIdeal ∣ J' := fun h ↦ hw (hp'.2.2 w h)
        dsimp only at heq
        have hkk := (hmult _ J hJ hwJ).symm.trans ((congrArg _ heq).trans (hmult _ J' hJ' hwJ'))
        have hJJ : J = J' := mul_left_cancel₀ (pow_ne_zero _ hw0) (hkk ▸ heq)
        have hdd : d = d' := by
          rw [← hEne w d (left_ne_zero_of_mul hne), ← hEne w d' (left_ne_zero_of_mul hne'), hkk]
        have hee : e = e' := hp.2.1.symm.trans (hJJ ▸ hp'.2.1)
        subst hJJ hdd hee
        rfl
      · intro I hI hcI
        rw [hmemU] at hI
        have hI0 : I ≠ 0 := fun h ↦ hcI (by rw [h, _root_.map_zero])
        obtain ⟨k, J, hwJ, rfl⟩ := WfDvdMonoid.max_power_factor hI0 w.irreducible
        refine ⟨⟨(w.asIdeal.absNorm ^ k, J.absNorm), J⟩, ?_, ?_, ?_⟩
        · rw [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, hmemU]
          refine ⟨⟨by rw [← hI.1, map_mul, map_pow], ?_⟩, rfl, fun v hv ↦ ?_⟩
          · rw [← hI.1, Ne, Ideal.absNorm_eq_zero_iff, ← Ideal.zero_eq_bot]
            exact hI0
          · rcases Finset.mem_insert.mp (hI.2 v (dvd_mul_of_dvd_right hv _)) with rfl | h
            · exact absurd hv hwJ
            · exact h
        · rw [map_mul, map_pow, hcPrime] at hcI
          rwa [hEpow]
        · dsimp only
          rw [Nat.log_pow (hN w)]
      · rintro ⟨⟨d, e⟩, J⟩ hp hne
        dsimp only
        rw [map_mul, map_pow, hcPrime, ← hEpow, hEne w d (left_ne_zero_of_mul hne)]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [ArithmeticFunction.map_zero, heckeNormCoefficient]
    have : IsEmpty {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = ((0 : ℕ) : ℝ)} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp (by exact_mod_cast I.2.2))⟩
    exact finsum_of_isEmpty _
  obtain ⟨S, hS, hSm⟩ := ((heckeLocalEulerFactor_eventually_prod_eq χ m).and
    (eventually_ge_atTop ((Ring.HasFiniteQuotients.finite_absNorm_le m).preimage
      HeightOneSpectrum.asIdeal_injective.injOn).toFinset)).exists
  rw [← hS, key S m]
  have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m} = ↑(U S m) := by
    ext I
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, hmemU]
    constructor
    · rintro ⟨-, hIm⟩
      have hIm' : I.absNorm = m := by exact_mod_cast hIm
      refine ⟨hIm', fun v hv ↦ hSm ?_⟩
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_ofPred_eq, ← hIm']
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (hIm' ▸ hm)) (map_dvd Ideal.absNorm hv)
    · rintro ⟨hIm, -⟩
      exact ⟨fun h ↦ hm (by rw [← hIm, h, Ideal.absNorm_bot]), by exact_mod_cast hIm⟩
  change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m}, value I = _
  rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset]
  rfl

/-- Paper: Equation (B.6.1.5), p. 637. Grouping the terms by their integral
norm gives the absolutely convergent Dirichlet series with coefficients `aₘ`. -/
theorem finiteHeckeL_hasSum_normCoefficients (χ : U[F]) (s : halfPlane) :
    LSeriesHasSum (fun m : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) (m : ℝ))
      (s : ℂ) (finiteHeckeL χ s) := by
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  let value := heckeIdealValue (ideleClassNormTwist χ 0)
  have hs : (s : ℂ) ≠ 0 := by
    intro h
    have hr : 1 < (s : ℂ).re := s.property
    norm_num [h] at hr
  refine ((finiteHeckeL_hasSum_ideals χ s).tsum_fiberwise normIndex).congr_fun ?_
  intro n
  symm
  rw [LSeries.term_of_ne_zero' hs]
  let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ (I.absNorm : ℝ) = (n : ℝ)}
  let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property,
        by exact_mod_cast (show I.val.val.absNorm = n from I.property)⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, by
        change I.val.absNorm = n
        exact_mod_cast I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hnorm (I : normFiber) : I.val.absNorm = n := by exact_mod_cast I.property.2
  rw [← e.symm.tsum_eq]
  change (∑' I : normFiber, value I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) =
    heckeNormCoefficient (ideleClassNormTwist χ 0) (n : ℝ) / (n : ℂ) ^ (s : ℂ)
  let : Finite normFiber :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
      (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hnorm ⟨I, hI⟩)).to_subtype
  simp_rw [hnorm, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
  rfl

/-- Paper: Equation (B.6.1.6), p. 637. For each positive `ε`, the summatory
function is bounded by a constant times `x^(1 + ε)`, uniformly in unitary characters. -/
theorem heckeIdealSummatory_bound (F : Type*) [Field F] [NumberField F] {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ χ : U[F],
      ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ C * x ^ (1 + ε) := by
  classical
  have hvalue (χ : U[F]) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    rw [heckeIdealValue, ite_eq_right hI]
    refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp) (fun _ w hz hw ↦ ?_) (fun v ↦ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans hw
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]
  obtain ⟨B, hB⟩ := (NumberField.Ideal.tendsto_norm_le_div_atTop F).isBoundedUnder_le.eventually_le
  have hC : 0 < max 1 B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨max 1 B, hC, ?_⟩
  filter_upwards [hB, eventually_ge_atTop (1 : ℝ)] with x hcount hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let ideals := {I : Ideal (𝓞 F) | (I.absNorm : ℝ) ≤ x}
  let nonzeroIdeals := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}
  have hfinite : ideals.Finite := by
    simp only [ideals, ← Nat.le_floor_iff hxpos.le]
    exact Ring.HasFiniteQuotients.finite_absNorm_le _
  have hsub : nonzeroIdeals ⊆ ideals := fun _ hI ↦ hI.2
  let : Fintype nonzeroIdeals := (hfinite.subset hsub).fintype
  intro χ
  calc
    ‖heckeIdealSummatory (ideleClassNormTwist χ 0) x‖ ≤ ∑ _ : nonzeroIdeals, (1 : ℝ) := by
      change ‖∑ᶠ I : nonzeroIdeals, heckeIdealValue (ideleClassNormTwist χ 0) I.1‖ ≤ _
      rw [finsum_eq_sum_of_fintype]
      exact norm_sum_le_of_le _ fun I _ ↦ hvalue χ I.2.1
    _ = (nonzeroIdeals.ncard : ℝ) := by simp
    _ ≤ (ideals.ncard : ℝ) := by exact_mod_cast Set.ncard_le_ncard hsub hfinite
    _ ≤ max 1 B * x := (div_le_iff₀ hxpos).mp (hcount.trans (le_max_right 1 B))
    _ ≤ max 1 B * x ^ (1 + ε) := mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_one_le hx (le_add_of_nonneg_right hε.le)) hC.le

-- TODO(paper-gap): Equation (B.6.1.7) multiplies the norm-one class volume by an
-- extra inverse square root of the discriminant under the normalization in §A.3.

/-- A unitary character trivial on the norm-one subgroup is a unique imaginary power of
the norm. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ∃! t : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * (t : ℂ)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let c : NNRealˣ →ₜ* ℂ := (ideleClassNormTwist χ 0).comp ⟨σ, hσ⟩
  have hunit (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ 0 g = (χ g : ℂ) := by
    change (χ g : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ :=
    existsUnique_unitaryComplexPower c (fun u ↦ by
      change ‖ideleClassNormTwist χ 0 (σ u)‖ = 1
      rw [hunit, Circle.norm_coe])
  have hparam : -Complex.I * ((-z.im : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hzre]
  refine ⟨-z.im, ?_, ?_⟩
  · change ideleClassNormTwist χ 0 =
      ideleClassNormTwist (1 : U[F]) (-Complex.I * ((-z.im : ℝ) : ℂ))
    rw [hparam]
    ext1 g
    let u := ideleClassNorm F g
    have hk : g / σ u ∈ (ideleClassNorm F).ker := MonoidHom.mem_ker.mpr (by
      rw [map_div, hnorm u, div_self'])
    have hkχ : χ (g / σ u) = 1 :=
      DFunLike.congr_fun hχ (⟨g / σ u, hk⟩ : (ideleClassNorm F).ker)
    have he : ideleClassNormTwist χ 0 (g / σ u) = 1 := by rw [hunit, hkχ, Circle.coe_one]
    calc
      ideleClassNormTwist χ 0 g = ideleClassNormTwist χ 0 (g / σ u) * c u := by
        change ideleClassNormTwist χ 0 g =
          ideleClassNormTwist χ 0 (g / σ u) * ideleClassNormTwist χ 0 (σ u)
        rw [← map_mul, div_mul_cancel]
      _ = ideleClassNormTwist (1 : U[F]) z g := by
        change ideleClassNormTwist χ 0 (g / σ u) * c u =
          1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ z
        rw [he, hz u]
  · intro t ht
    have he : -Complex.I * (t : ℂ) = z := huniq _ ⟨by simp [Complex.mul_re], fun u ↦ by
      change ideleClassNormTwist χ 0 (σ u) = _
      rw [ht]
      change (1 : ℂ) * (((ideleClassNorm F (σ u) : NNReal) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) = _
      rw [one_mul, hnorm u]⟩
    apply neg_eq_iff_eq_neg.mp
    simpa [Complex.mul_im] using congrArg Complex.im he

/-- Undoing the imaginary norm twist of such a character gives the trivial character. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one (χ : U[F]) (t₀ : ℝ)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist χ (Complex.I * t₀) g = 1 := by
  have h := DFunLike.congr_fun ht g
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (0 : ℂ) =
    1 * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (-Complex.I * t₀) at h
  change (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (Complex.I * t₀) = 1
  have hne : (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ideleClassNorm F g).ne_zero
  rw [Complex.cpow_zero, mul_one, one_mul] at h
  rw [h, ← Complex.cpow_add _ _ hne, neg_mul, neg_add_cancel, Complex.cpow_zero]

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_value (χ : 𝒳[F])
    (hχ : ∀ g, χ g = 1) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Lemma B.6.1.2(1), p. 637. For a unitary character trivial on
norm-one classes, undoing its imaginary norm twist gives the ideal-counting
limit at the residue of Dedekind zeta.
Deviation: Uses Mathlib's `dedekindZeta_residue`, the class volume in §A.3,
with the extra printed inverse square root of the discriminant removed. -/
theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    (∃! t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) ∧
      ∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
        Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
          atTop (𝓝 (dedekindZeta_residue F : ℂ)) := by
  refine ⟨heckeIdealSummatory_tendsto_of_trivial_on_normOne_existsUnique χ hχ, fun t₀ ht ↦ ?_⟩
  have hval {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      heckeIdealValue (ideleClassNormTwist χ (Complex.I * t₀)) I = 1 :=
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_value _
      (heckeIdealSummatory_tendsto_of_trivial_on_normOne_eq_one χ t₀ ht) hI
  have hlim := (Complex.continuous_ofReal.tendsto _).comp (Ideal.tendsto_norm_le_div_atTop₀ F)
  rw [← dedekindZeta_residue_def] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [Function.comp_apply, Complex.ofReal_div, Complex.ofReal_natCast]
  congr 1
  let e : {I : nonZeroDivisors (Ideal (𝓞 F)) // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x} ≃
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} :=
    { toFun := fun I ↦ ⟨I.1.1, by simpa using mem_nonZeroDivisors_iff_ne_zero.mp I.1.2, I.2⟩
      invFun := fun I ↦ ⟨⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by simpa using I.2.1)⟩, I.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x} := Fintype.ofFinite _
  unfold heckeIdealSummatory
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun I _ ↦ hval I.2.1, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Conjugating the coefficients of a Dirichlet series conjugates its sum at the
conjugate point. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj (f : ℕ → ℂ)
    (s a : ℂ) (h : LSeriesHasSum f ((starRingEnd ℂ) s) a) :
    LSeriesHasSum (fun n ↦ (starRingEnd ℂ) (f n)) s ((starRingEnd ℂ) a) := by
  have h' := h.star
  unfold LSeriesHasSum
  convert h' using 1
  · funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    change _ = (starRingEnd ℂ) _
    rw [map_div₀, ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity),
      Complex.conj_natCast]
  · rfl

/-- The summatory function groups by integral norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum (χ : 𝒳[F])
    (x : ℝ) (hx : 0 ≤ x) :
    heckeIdealSummatory χ x = ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, heckeNormCoefficient χ n := by
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  let T := hfin.toFinset
  have hfib (n : ℕ) (hn : n ∈ Finset.Icc 0 ⌊x⌋₊) :
      heckeNormCoefficient χ n = ∑ I ∈ T with I.absNorm = n, heckeIdealValue χ I := by
    have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} =
        ↑(T.filter fun I ↦ I.absNorm = n) := by
      ext I
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, T, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨h0, h1⟩
        have h1' : I.absNorm = n := by exact_mod_cast h1
        refine ⟨⟨h0, ?_⟩, h1'⟩
        rw [h1]
        exact (Nat.le_floor_iff hx).mp (Finset.mem_Icc.mp hn).2
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, by exact_mod_cast h1⟩
    unfold heckeNormCoefficient
    change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n}, heckeIdealValue χ I = _
    rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset]
  unfold heckeIdealSummatory
  change ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, heckeIdealValue χ I = _
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl hfib]
  refine (Finset.sum_fiberwise_of_maps_to (fun I hI ↦ ?_) _).symm
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
  exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hI.2⟩


/-- The norm-one-twisted trivial character has coefficient equal to the number of
nonzero ideals of the given norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one (n : ℕ) :
    heckeNormCoefficient (ideleClassNormTwist (1 : U[F]) 0) n =
      ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ) := by
  classical
  have hone (g : IdeleClassGroup (𝓞 F) F) : ideleClassNormTwist (1 : U[F]) 0 g = 1 := by
    change ((1 : U[F]) g : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ by exact_mod_cast hI.2)).to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} := Fintype.ofFinite _
  unfold heckeNormCoefficient
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun I _ ↦
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_value _ hone I.2.1, Finset.sum_const,
    Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  norm_cast

/-- Each coefficient of a unitary character is bounded by the number of ideals of that norm. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_norm_le (χ : U[F])
    (n : ℕ) : ‖heckeNormCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) := by
  classical
  have hvalue {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
      ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    rw [heckeIdealValue, ite_eq_right hI]
    refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp) (fun _ w hz hw ↦ ?_) (fun v ↦ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg w) hz).trans hw
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      split_ifs <;> simp [norm_ideleClassNormTwist_zero_localValue]
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ by exact_mod_cast hI.2)).to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} := Fintype.ofFinite _
  unfold heckeNormCoefficient
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  refine (norm_sum_le_of_le _ fun I _ ↦ hvalue I.2.1).trans ?_
  simp

/-- The ideal counts have a linear summatory bound. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_bound :
    ∃ C : ℝ, ∀ n : ℕ, ∑ i ∈ Finset.range n,
      (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = i} : ℝ) ≤ C * n := by
  set N : ℕ → ℝ := fun i ↦ (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = i} : ℝ)
    with hN
  set S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.Icc 0 n, N i with hS
  have hN0 (i : ℕ) : 0 ≤ N i := Nat.cast_nonneg _
  have h1 : (1 : U[F]).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  have hlim := (heckeIdealSummatory_tendsto_of_trivial_on_normOne (1 : U[F]) h1).2 0 (by simp)
  have e : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  rw [e] at hlim
  have hR : Tendsto (fun n : ℕ ↦ S n / n) atTop (𝓝 (dedekindZeta_residue F)) := by
    have := ((Complex.continuous_re.tendsto _).comp hlim).comp tendsto_natCast_atTop_atTop
    refine this.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum _ _ (Nat.cast_nonneg n),
      Nat.floor_natCast]
    simp_rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (hR.eventually (gt_mem_nhds (lt_add_one (dedekindZeta_residue F))))
  have hres := dedekindZeta_residue_pos F
  have hSmono {m n : ℕ} (h : m ≤ n) : S m ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl h)
      fun i _ _ ↦ hN0 i
  have hS0 (n : ℕ) : 0 ≤ S n := Finset.sum_nonneg fun i _ ↦ hN0 i
  refine ⟨dedekindZeta_residue F + 1 + S n₀, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : ∑ i ∈ Finset.range n, N i ≤ S n :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_range.mp hi).le⟩)
      fun i _ _ ↦ hN0 i
  refine hle.trans ?_
  rcases le_or_gt n₀ n with h | h
  · have := hn₀ n h
    rw [div_lt_iff₀ (by linarith)] at this
    nlinarith [hS0 n₀]
  · have := hSmono h.le
    nlinarith [hS0 n₀]

/-- On the right half-plane the ideal-count Dirichlet series has the sum given by the
finite Dedekind zeta function. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦
      ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ)) s
      (finiteHeckeL (1 : U[F]) ⟨s, hs⟩) := by
  have := finiteHeckeL_hasSum_normCoefficients (1 : U[F]) ⟨s, hs⟩
  simp_rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_one] at this
  exact this

/-- The ideal-count Dirichlet series minus a real multiple of `1 / (s - 1)` extends
continuously to the closed half-plane `1 ≤ re s`. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_zeta :
    ∃ c : ℝ, ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧
      EqOn G (fun s ↦ LSeries (fun n : ℕ ↦
        ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ)) s -
          c / (s - 1)) {s | 1 < s.re} := by
  set a : ℕ → ℂ := fun n ↦
    ((Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ) : ℂ) with ha
  obtain ⟨Λ, hΛ, hEq⟩ := completedHeckeL_exists_continuation (1 : U[F])
  have h1 : (1 : U[F]).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  obtain ⟨t, ⟨ht, -, hord, han⟩, -⟩ :=
    completedHeckeL_continuation_simplePoles (1 : U[F]) Λ hΛ hEq h1
  have ht0 : t = 0 := by
    have := congrArg Complex.im (trivial_normTwist_injective (F := F) ht)
    simpa using this.symm
  subst ht0
  have hord' : meromorphicOrderAt Λ 1 = -1 := by simpa using hord
  let γ : ℂ → ℂ := fun s ↦ (heckeGammaFactor (1 : U[F]) s)⁻¹
  have hγ : Differentiable ℂ γ := differentiable_inv_heckeGammaFactor _
  have hLS (s : ℂ) (hs : 1 < s.re) : γ s * Λ s = LSeries a s := by
    have hne := heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (s := s) (by linarith)
    rw [hEq ⟨s, hs⟩,
      (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one s hs).LSeries_eq]
    change γ s * (heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) ⟨s, hs⟩) = _
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hreal (s : ℂ) (hs : 1 < s.re) (hsr : s.im = 0) : (LSeries a s).im = 0 := by
    have hc : (starRingEnd ℂ) s = s := Complex.conj_eq_iff_im.mpr hsr
    have hsum (s' : ℂ) (hs' : 1 < s'.re) : LSeriesHasSum a s' (LSeries a s') :=
      (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one (F := F) s'
        hs').LSeriesSummable.LSeriesHasSum
    have h₂ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj a s _
      (hsum _ (by rwa [Complex.conj_re]))
    have hfa : (fun n ↦ (starRingEnd ℂ) (a n)) = a := funext fun n ↦ Complex.conj_ofReal _
    rw [hc, hfa] at h₂
    rw [← Complex.conj_eq_iff_im]
    exact HasSum.unique h₂ (hsum s hs)
  obtain ⟨g, hg, -, hgeq⟩ :=
    (meromorphicOrderAt_eq_int_iff (hΛ (mem_univ 1)).meromorphicAt).1 hord'
  let h : ℂ → ℂ := fun s ↦ γ s * g s
  have hh : DifferentiableAt ℂ h 1 := (hγ 1).mul hg.differentiableAt
  have hnear : ∀ᶠ z in 𝓝[≠] (1 : ℂ), γ z * Λ z = (z - 1)⁻¹ * h z := by
    filter_upwards [hgeq] with z hz
    simp only [zpow_neg, zpow_one, smul_eq_mul] at hz
    rw [hz]
    ring
  have hh1 : (h 1).im = 0 := by
    have hto : Tendsto (fun σ : ℝ ↦ (σ : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 1 1 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact fun h' ↦ (ne_of_gt (Set.mem_Ioi.mp hσ))
          (by exact_mod_cast (Set.mem_singleton_iff.mp h'))
    have hlim : Tendsto (fun σ : ℝ ↦ (h σ).im) (𝓝[>] 1) (𝓝 (h 1).im) :=
      (Complex.continuous_im.tendsto _).comp
        ((hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hto)
    refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
    filter_upwards [hto.eventually hnear, self_mem_nhdsWithin] with σ hσ hσ1
    have hσ1' : (1 : ℝ) < σ := hσ1
    have hre : 1 < (σ : ℂ).re := by simpa using hσ1'
    have hne : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hσ1'.ne')
    have : h σ = ((σ : ℂ) - 1) * LSeries a σ := by
      rw [← hLS _ hre, hσ, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.im_ofReal_mul,
      hreal _ hre (by simp), mul_zero]
  set c : ℝ := (h 1).re with hc
  have hcc : (c : ℂ) = h 1 := Complex.ext (by simp [hc]) (by simp [hh1])
  let G : ℂ → ℂ := Function.update (fun s ↦ γ s * Λ s - c / (s - 1)) 1 (deriv h 1)
  refine ⟨c, G, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · apply ContinuousAt.continuousWithinAt
    by_cases hs1 : s = 1
    · subst hs1
      have hev : G =ᶠ[𝓝 1] dslope h 1 := by
        filter_upwards [eventually_nhdsWithin_iff.mp hnear] with z hz
        by_cases hz1 : z = 1
        · subst hz1
          simp only [G, Function.update_self, dslope_same]
        · have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
          simp only [G, Function.update_of_ne hz1]
          rw [hz hz1, dslope_of_ne _ hz1, slope_def_field, hcc]
          field_simp
      exact (continuousAt_dslope_same.mpr hh).congr hev.symm
    · have hs0 : s ≠ 0 := by
        rintro rfl
        norm_num at hs
      have hΛs : ContinuousAt Λ s := (han s (by simp [hs0, hs1])).continuousAt
      have hcont : ContinuousAt (fun s ↦ γ s * Λ s - c / (s - 1)) s :=
        ((hγ s).continuousAt.mul hΛs).sub
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
            (sub_ne_zero.mpr hs1))
      refine hcont.congr ?_
      filter_upwards [eventually_ne_nhds hs1] with z hz
      simp [G, Function.update_of_ne hz]
  · have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hs
    simp only [G, Function.update_of_ne hs1]
    rw [hLS s hs]

/-- If the character is nontrivial on norm-one classes, the Dirichlet series of its
coefficients has an entire continuation. -/
private theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_entire (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ M : ℂ → ℂ, Differentiable ℂ M ∧ ∀ s : ℂ, 1 < s.re →
      LSeriesHasSum (fun n : ℕ ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) n) s (M s) := by
  obtain ⟨Λ, hΛ, hEq⟩ := completedHeckeL_exists_continuation χ
  have hd := completedHeckeL_continuation_entire χ Λ hΛ hEq hχ
  refine ⟨fun s ↦ (heckeGammaFactor χ s)⁻¹ * Λ s,
    (differentiable_inv_heckeGammaFactor χ).mul hd, fun s hs ↦ ?_⟩
  have hne := heckeGammaFactor_ne_zero_of_re_pos χ (s := s) (by linarith)
  convert finiteHeckeL_hasSum_normCoefficients χ ⟨s, hs⟩ using 1
  change (heckeGammaFactor χ s)⁻¹ * Λ s = _
  rw [show Λ s = completedHeckeL χ ⟨s, hs⟩ from hEq ⟨s, hs⟩]
  change _ * (heckeGammaFactor χ s * finiteHeckeL χ ⟨s, hs⟩) = _
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- Paper: Lemma B.6.1.2(2), p. 637. If the character is nontrivial on norm-one
classes, its summatory function divided by `x` tends to zero. -/
theorem heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ 0) x / x) atTop (𝓝 0) := by
  set N : ℕ → ℝ := fun n ↦ (Nat.card {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = n} : ℝ)
    with hN
  set a : ℕ → ℂ := fun n ↦ heckeNormCoefficient (ideleClassNormTwist χ 0) n with ha
  have hN0 (n : ℕ) : 0 ≤ N n := Nat.cast_nonneg _
  have haN (n : ℕ) : ‖a n‖ ≤ N n :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_norm_le χ n
  obtain ⟨C, hC⟩ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_bound (F := F)
  obtain ⟨c, G, hG, hGeq⟩ := heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_zeta (F := F)
  obtain ⟨M, hM, hMsum⟩ :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_entire χ hχ
  have hNsum (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (N n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s) :=
    (heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_hasSum_one (F := F) s
      hs).LSeriesSummable.LSeriesHasSum
  have hWI (u : ℕ → ℝ) (H : ℂ → ℂ) (hu : 0 ≤ u) (hu2 : ∀ n, u n ≤ 2 * N n)
      (hH : ContinuousOn H {s | 1 ≤ s.re})
      (hsum : ∀ s : ℂ, 1 < s.re →
        LSeriesHasSum (fun n ↦ (u n : ℂ)) s (LSeries (fun n ↦ (N n : ℂ)) s + H s)) :
      Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 c) := by
    refine WienerIkehara.tendsto_sum_div (C := 2 * C) (G := fun s ↦ G s + H s)
      (fun n ↦ ?_) (hG.add hH) (fun s hs ↦ ?_) hu
    · calc ∑ i ∈ Finset.range n, u i ≤ ∑ i ∈ Finset.range n, 2 * N i :=
            Finset.sum_le_sum fun i _ ↦ hu2 i
        _ = 2 * ∑ i ∈ Finset.range n, N i := by rw [Finset.mul_sum]
        _ ≤ 2 * (C * n) := by linarith [hC n]
        _ = 2 * C * n := by ring
    · simp only
      rw [hGeq hs, (hsum s hs).LSeries_eq]
      ring
  have hT0 := hWI N 0 (fun n ↦ hN0 n) (fun n ↦ by linarith [hN0 n]) continuousOn_const
    fun s hs ↦ by simpa using hNsum s hs
  have hconj (s : ℂ) (hs : 1 < s.re) :
      LSeriesHasSum (fun n ↦ (starRingEnd ℂ) (a n)) s ((starRingEnd ℂ) (M ((starRingEnd ℂ) s))) :=
    heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_conj a s _
      (hMsum _ (by rwa [Complex.conj_re]))
  have hMc : Continuous fun s ↦ (starRingEnd ℂ) (M ((starRingEnd ℂ) s)) :=
    Complex.continuous_conj.comp (hM.continuous.comp Complex.continuous_conj)
  have hT1 := hWI (fun n ↦ N n + (a n).re) (fun s ↦ (M s + (starRingEnd ℂ) (M ((starRingEnd ℂ) s))) / 2)
    (fun n ↦ by
      have h1 := abs_le.mp (Complex.abs_re_le_norm (a n))
      have h2 := haN n
      simp only [Pi.zero_apply]
      linarith [h1.1])
    (fun n ↦ by linarith [Complex.re_le_norm (a n), haN n])
    ((hM.continuous.add hMc).div_const 2).continuousOn
    fun s hs ↦ by
      have := (hNsum s hs).add (((hMsum s hs).add (hconj s hs)).smul (1 / 2 : ℂ))
      convert this using 1
      · funext n
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [Complex.re_eq_add_conj]
        ring
      · ring
  have hT2 := hWI (fun n ↦ N n + (a n).im)
    (fun s ↦ (M s - (starRingEnd ℂ) (M ((starRingEnd ℂ) s))) / (2 * Complex.I))
    (fun n ↦ by
      have h1 := abs_le.mp (Complex.abs_im_le_norm (a n))
      have h2 := haN n
      simp only [Pi.zero_apply]
      linarith [h1.1])
    (fun n ↦ by linarith [Complex.im_le_norm (a n), haN n])
    ((hM.continuous.sub hMc).div_const _).continuousOn
    fun s hs ↦ by
      have := (hNsum s hs).add (((hMsum s hs).sub (hconj s hs)).smul (1 / (2 * Complex.I)))
      convert this using 1
      · funext n
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [Complex.im_eq_sub_conj]
        ring
      · ring
  have hdiff (u : ℕ → ℝ) (hu : Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (N n + u n)) / x)
      atTop (𝓝 c)) : Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, u n) / x) atTop (𝓝 0) := by
    have := hu.sub hT0
    rw [sub_self] at this
    refine this.congr fun x ↦ ?_
    rw [Finset.sum_add_distrib]
    ring
  have hre := hdiff _ hT1
  have him := hdiff _ hT2
  have hlim := ((Complex.continuous_ofReal.tendsto 0).comp hre).add
    (((Complex.continuous_ofReal.tendsto 0).comp him).mul_const Complex.I)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  rw [heckeIdealSummatory_tendsto_zero_of_nontrivial_on_normOne_sum _ x hx]
  have hsplit : ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, heckeNormCoefficient (ideleClassNormTwist χ 0) n =
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((a n).re : ℂ) + (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ((a n).im : ℂ)) *
        Complex.I := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ (Complex.re_add_im _).symm
  simp only [Function.comp_apply]
  push_cast
  rw [hsplit]
  ring

/-- Paper: Equation (B.6.1.13), p. 638. The ideal von Mangoldt function is
`log (N p)` on positive powers of a nonzero prime ideal `p` and zero elsewhere. -/
def idealVonMangoldt (I : Ideal (𝓞 F)) : ℝ :=
  open Classical in
  if h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k then
    Real.log (h.choose.asIdeal.absNorm : ℝ)
  else 0

/-- Paper: Equation (B.6.1.13), p. 638. The value at a positive prime-ideal
power is the logarithm of the prime's norm, independently of the exponent. -/
theorem idealVonMangoldt_prime_pow (v : HeightOneSpectrum (𝓞 F)) {k : ℕ} (hk : 0 < k) :
    idealVonMangoldt (v.asIdeal ^ k) = Real.log (v.asIdeal.absNorm : ℝ) := by
  have h : ∃ w : HeightOneSpectrum (𝓞 F), ∃ j : ℕ, 0 < j ∧ v.asIdeal ^ k = w.asIdeal ^ j :=
    ⟨v, k, hk, rfl⟩
  unfold idealVonMangoldt
  split_ifs with h'
  · obtain ⟨hj, hw⟩ := h'.choose_spec.choose_spec
    rw [HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ hj.ne').trans hw.symm.dvd)]
  · exact absurd h h'

/-- Paper: §B.6.1.2, p. 638. The twisted von Mangoldt value is the product
of the ideal character value and the ideal von Mangoldt weight. -/
def heckeIdealVonMangoldt (χ : 𝒳[F]) (I : Ideal (𝓞 F)) : ℂ :=
  heckeIdealValue χ I * (idealVonMangoldt I : ℂ)

/-- Paper: §B.6.1.2, p. 638. At a positive power of an unramified prime, the
twisted weight is the character power times the logarithm of the prime norm. -/
theorem heckeIdealVonMangoldt_prime_pow (χ : 𝒳[F]) (v : HeightOneSpectrum (𝓞 F))
    (hv : χ.IsUnramifiedAt v) {k : ℕ} (hk : 0 < k) :
    heckeIdealVonMangoldt χ (v.asIdeal ^ k) =
      χ.localValue v ^ k * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
  classical
  rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow χ v hk, ite_eq_left hv,
    idealVonMangoldt_prime_pow v hk]

/-- A positive prime power has twisted weight of norm at most the logarithm of its norm.
The weight vanishes on all other ideals. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_weight (χ : U[F])
    (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ Real.log I.absNorm := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    have hq : (1 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hq), map_pow, Nat.cast_pow]
    split_ifs <;> simp only [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul,
      norm_zero, zero_mul]
    · exact Real.log_le_log (zero_lt_one.trans_le hq) (le_self_pow₀ hq hk.ne')
    · exact Real.log_nonneg (one_le_pow₀ hq)
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h, Real.log_natCast_nonneg]

/-- The logarithmic weight is absorbed by the difference between two exponents greater than one. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_summable (χ : U[F]) (s : halfPlane) :
    Summable (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) := by
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let ε := (s : ℂ).re - r
  have hε : 0 < ε := sub_pos.mpr hrs
  have hs := ((summable_absNorm_rpow F hr).subtype (fun I ↦ I ≠ ⊥)).div_const ε
  apply hs.of_norm_bounded
  intro I
  let q : ℝ := I.val.absNorm
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  change ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ (s : ℂ)‖ ≤ q ^ (-r) / ε
  rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hq]
  calc
    _ ≤ (q ^ ε / ε) / q ^ (s : ℂ).re := by
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hq.le _)
      exact (finiteHeckeL_logDeriv_hasSum_ideals_weight χ I.val).trans
        (Real.log_le_rpow_div hq.le hε)
    _ = q ^ (-r) / ε := by
      rw [div_right_comm, ← Real.rpow_sub hq]
      congr 2
      dsimp [ε]
      ring

/-- At one finite place, the logarithmic derivative sums the weights of its positive powers. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_local (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (s : halfPlane) :
    DifferentiableAt ℂ (finiteHeckeEulerFactor χ v) s ∧ finiteHeckeEulerFactor χ v s ≠ 0 ∧
      HasSum (fun k : ℕ ↦ -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
        ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ (s : ℂ)) (logDeriv (finiteHeckeEulerFactor χ v) s) := by
  classical
  let ψ := ideleClassNormTwist χ 0
  let a := if ψ.IsUnramifiedAt v then ψ.localValue v else 0
  let q := v.asIdeal.absNorm
  let z (w : ℂ) := a * (q : ℂ) ^ (-w)
  have hq : (1 : ℝ) < q := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have ha : ‖a‖ ≤ 1 := by
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h, ψ, norm_ideleClassNormTwist_zero_localValue]
  have hz : ‖z s‖ < 1 := by
    change ‖a * ((q : ℝ) : ℂ) ^ (-(s : ℂ))‖ < 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq), Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) ha).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr (zero_lt_one.trans s.property)))
  have hden : 1 - z s ≠ 0 := fun h ↦ hz.ne (by rw [← sub_eq_zero.mp h, norm_one])
  have hfactor : finiteHeckeEulerFactor χ v = fun w ↦ (1 - z w)⁻¹ := by
    funext w
    by_cases h : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;>
      simp [finiteHeckeEulerFactor, z, a, q, ψ, h]
  rw [hfactor]
  have dz := ((hasDerivAt_id (s : ℂ)).neg.const_cpow (Or.inl hq₀)).const_mul a
  change HasDerivAt z _ (s : ℂ) at dz
  have df := (dz.const_sub 1).inv hden
  change HasDerivAt (fun w ↦ (1 - z w)⁻¹) _ (s : ℂ) at df
  refine ⟨df.differentiableAt, inv_ne_zero hden, ?_⟩
  have hlog : logDeriv (fun w ↦ (1 - z w)⁻¹) s =
      (-Complex.log q * z s) * (1 - z s)⁻¹ := by
    rw [logDeriv_apply, df.deriv]
    change _ / (1 - z s)⁻¹ = _
    field_simp [hden]
    dsimp [z]
    ring
  rw [hlog]
  apply ((hasSum_geometric_of_norm_lt_one hz).mul_left (-Complex.log q * z s)).congr_fun
  intro k
  have hv : heckeIdealValue ψ (v.asIdeal ^ (k + 1)) = a ^ (k + 1) := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    by_cases h : ψ.IsUnramifiedAt v <;> simp [a, h]
  rw [heckeIdealVonMangoldt, hv, idealVonMangoldt_prime_pow v (Nat.succ_pos k),
    map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
    Complex.natCast_log]
  change -(a ^ (k + 1) * Complex.log q) / ((q : ℂ) ^ (s : ℂ)) ^ (k + 1) =
    (-Complex.log q * z s) * z s ^ k
  rw [mul_assoc (-Complex.log q), ← pow_succ',
    show z s = a * ((q : ℂ) ^ (s : ℂ))⁻¹ by simp [z, Complex.cpow_neg],
    mul_pow, inv_pow, div_eq_mul_inv]
  ring

/-- On the right half-plane, the logarithmic derivatives of the local Euler factors sum
to the logarithmic derivative of the continuation. -/
private theorem finiteHeckeL_logDeriv_hasSum_ideals_places (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (s : halfPlane) :
    L s ≠ 0 ∧ HasSum (fun v ↦ logDeriv (finiteHeckeEulerFactor χ v) s) (logDeriv L s) := by
  have hlocal := finiteHeckeL_logDeriv_hasSum_ideals_local χ
  have hn : L s ≠ 0 := by
    rw [hSeries s]
    exact finiteHeckeL_ne_zero_of_one_lt_re χ s
  refine ⟨hn, ?_⟩
  obtain ⟨r, hr, hrs⟩ := exists_between (show 1 < (s : ℂ).re from s.property)
  let D := Complex.re ⁻¹' Ioi r
  have hD : IsOpen D := isOpen_Ioi.preimage Complex.continuous_re
  have hconv := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ hr).mono
    (show D ⊆ {w : ℂ | r ≤ w.re} from fun w (hw : r < w.re) ↦ show r ≤ w.re from hw.le)
  have hconvL := hconv.congr_right
    (show EqOn _ L D from fun w hw ↦ (hSeries ⟨w, hr.trans hw⟩).symm)
  have hd (v : HeightOneSpectrum (𝓞 F)) : DifferentiableOn ℂ (finiteHeckeEulerFactor χ v) D :=
    fun w hw ↦ (hlocal v ⟨w, hr.trans hw⟩).1.differentiableWithinAt
  apply (Complex.logDeriv_tendsto hD hrs hconvL.tendstoLocallyUniformlyOn
    (.of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun v _ ↦ hd v) hn).congr
  intro S
  exact logDeriv_fun_prod (fun v _ ↦ (hlocal v s).2.1) (fun v _ ↦ (hlocal v s).1)

/-- Paper: Equation (B.6.1.12), p. 638. To the right of one, the negative of
the Dirichlet series weighted by the ideal von Mangoldt function converges
absolutely to the logarithmic derivative of the finite Hecke L-function. -/
theorem finiteHeckeL_logDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    AnalyticAt ℂ L (s : ℂ) ∧ L s ≠ 0 ∧
      HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
        -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
          (I.val.absNorm : ℂ) ^ (s : ℂ)) (logDeriv L s) := by
  obtain ⟨hne, hplaces⟩ := finiteHeckeL_logDeriv_hasSum_ideals_places χ L hSeries s
  have hNF := hL (mem_univ (s : ℂ))
  refine ⟨hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hNF.meromorphicOrderAt_eq_zero_iff.mpr hne).ge, hne, ?_⟩
  let P (p : HeightOneSpectrum (𝓞 F) × ℕ) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨p.1.asIdeal ^ (p.2 + 1), pow_ne_zero _ p.1.ne_bot⟩
  have hP : Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  let f (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) :=
    -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)
  have hout (I) (hI : I ∉ range P) : f I = 0 := by
    have h : ¬ ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · exact hI ⟨(v, k), Subtype.ext he.symm⟩
    simp [f, heckeIdealVonMangoldt, idealVonMangoldt, h]
  have hsum : Summable (f ∘ P) :=
    (finiteHeckeL_logDeriv_hasSum_ideals_summable χ s).comp_injective hP
  have hvalue := hsum.hasSum.prod_fiberwise fun v ↦
    (finiteHeckeL_logDeriv_hasSum_ideals_local χ v s).2.2
  exact (hP.hasSum_iff hout).mp (hvalue.unique hplaces ▸ hsum.hasSum)

/-- Paper: Equation (B.6.1.14), p. 638. The coefficient `Aₘ` sums the
character-weighted von Mangoldt values over nonzero ideals of norm `m`.
Deviation: The empty sum at `m = 0` is also defined. -/
def heckeLogDerivCoefficient (χ : 𝒳[F]) (m : ℕ) : ℂ :=
  ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, heckeIdealVonMangoldt χ I.val

/-- Over `ℚ`, the ideal von Mangoldt function at the ideal generated by `n` is `Λ n`. -/
private theorem idealVonMangoldt_ratSpan (n : ℕ) :
    idealVonMangoldt (Ideal.span {(n : 𝓞 ℚ)}) = ArithmeticFunction.vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      { asIdeal := Ideal.span {(p : 𝓞 ℚ)}
        isPrime := (Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp.ne_zero)).mpr
          (RatRingOfIntegers.prime_natCast_iff.mpr hp)
        ne_bot := by
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hp.ne_zero }
    have hv : Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} = v.asIdeal ^ k := by
      simp [v, Ideal.span_singleton_pow]
    rw [hv, idealVonMangoldt_prime_pow v hk, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    show Real.log ((Ideal.absNorm (Ideal.span {(p : 𝓞 ℚ)}) : ℕ) : ℝ) = _
    rw [RatRingOfIntegers.absNorm_span_natCast]
  · rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_right hn, idealVonMangoldt, dite_eq_right]
    rintro ⟨v, k, hk, hvk⟩
    apply hn
    obtain ⟨p, hp⟩ := RatRingOfIntegers.exists_eq_span_natCast v.asIdeal
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact v.ne_bot (by simpa using hp)
    have hprime : Nat.Prime p := RatRingOfIntegers.prime_natCast_iff.mp
      ((Ideal.span_singleton_prime (RatRingOfIntegers.natCast_ne_zero hp0)).mp (hp ▸ v.isPrime))
    have hpow : Ideal.span {(n : 𝓞 ℚ)} = Ideal.span {((p ^ k : ℕ) : 𝓞 ℚ)} := by
      rw [hvk, hp, Ideal.span_singleton_pow]
      simp
    have := congrArg Ideal.absNorm hpow
    rw [RatRingOfIntegers.absNorm_span_natCast, RatRingOfIntegers.absNorm_span_natCast] at this
    exact this ▸ (isPrimePow_nat_iff _).mpr ⟨p, k, hprime, hk, rfl⟩

/-- A character that is identically one has value one at every nonzero ideal. -/
private theorem heckeIdealValue_of_forall_eq_one (χ : 𝒳[F]) (hχ : ∀ g, χ g = 1)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : heckeIdealValue χ I = 1 := by
  classical
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      χ.restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hχ, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F), χ.IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), χ.localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- Paper: Equation (B.6.1.14), p. 638. Over the rationals with trivial
character these coefficients recover the classical von Mangoldt function. -/
theorem heckeLogDerivCoefficient_trivial_rat (m : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[ℚ]) 0) m =
      (ArithmeticFunction.vonMangoldt m : ℂ) := by
  have hχ : ∀ g, ideleClassNormTwist (1 : U[ℚ]) 0 g = 1 := fun g ↦ by
    simp only [ideleClassNormTwist, Complex.cpow_zero]
    change ((1 : U[ℚ]) g : ℂ) * 1 = 1
    simp
  unfold heckeLogDerivCoefficient
  rcases eq_or_ne m 0 with rfl | hm
  · have : IsEmpty {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = 0} :=
      ⟨fun I ↦ I.2.1 (Ideal.absNorm_eq_zero_iff.mp I.2.2)⟩
    rw [finsum_of_isEmpty]
    simp
  · have hmem : ∀ I : Ideal (𝓞 ℚ), I ≠ ⊥ ∧ I.absNorm = m ↔ I = Ideal.span {(m : 𝓞 ℚ)} :=
      fun I ↦ by
        constructor
        · rintro ⟨-, h⟩
          obtain ⟨n, rfl⟩ := RatRingOfIntegers.exists_eq_span_natCast I
          rw [RatRingOfIntegers.absNorm_span_natCast] at h
          rw [h]
        · rintro rfl
          refine ⟨?_, RatRingOfIntegers.absNorm_span_natCast m⟩
          rw [Ne, Ideal.span_singleton_eq_bot]
          exact RatRingOfIntegers.natCast_ne_zero hm
    let : Unique {I : Ideal (𝓞 ℚ) // I ≠ ⊥ ∧ I.absNorm = m} :=
      { default := ⟨_, (hmem _).mpr rfl⟩
        uniq := fun I ↦ Subtype.ext ((hmem I.val).mp I.2) }
    rw [finsum_unique]
    show heckeIdealVonMangoldt _ (Ideal.span {(m : 𝓞 ℚ)}) = _
    rw [heckeIdealVonMangoldt, heckeIdealValue_of_forall_eq_one _ hχ ((hmem _).mpr rfl).1,
      idealVonMangoldt_ratSpan, one_mul]

/-- A unitary character twisted by the trivial norm power has values of norm at most one,
so the twisted von Mangoldt weight is bounded by the ideal von Mangoldt weight. -/
private theorem heckeLogDerivCoefficient_bound_norm_le (χ : U[F]) (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ idealVonMangoldt I := by
  classical
  have hΛ : 0 ≤ idealVonMangoldt I := by
    unfold idealVonMangoldt
    split_ifs
    exacts [Real.log_natCast_nonneg _, le_rfl]
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    unfold heckeIdealValue
    split_ifs
    · simp
    · refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp)
        (fun x y hx hy ↦ (norm_mul_le x y).trans (by nlinarith [norm_nonneg x, norm_nonneg y]))
        fun v ↦ ?_
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      split_ifs
      · exact (norm_ideleClassNormTwist_zero_localValue χ v).le
      · simp
  rw [heckeIdealVonMangoldt, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ]
  exact mul_le_of_le_one_left hΛ hval

/-- A nonzero prime ideal lies over a rational prime `q`, and its norm is a positive
power of `q`. -/
private theorem heckeLogDerivCoefficient_bound_liesOver (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q f : ℕ, q.Prime ∧ 0 < f ∧ v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      v.asIdeal.absNorm = q ^ f := by
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  set q := Ideal.absNorm (v.asIdeal.under ℤ)
  have hl : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := Int.liesOver_span_absNorm _
  refine ⟨q, v.asIdeal.inertiaDeg ℤ, Nat.absNorm_under_prime v.asIdeal,
    Ideal.inertiaDeg_pos _ _, hl, ?_⟩
  rw [← Ideal.natAbs_pow_inertiaDeg (q : ℤ) v.asIdeal, Int.natAbs_natCast]

/-- At most `[F : ℚ]` positive prime-ideal powers have a given norm `m ≥ 2`, and each
has von Mangoldt weight at most `log m`. -/
private theorem heckeLogDerivCoefficient_bound_finsum_le {m : ℕ} (hm : 2 ≤ m) :
    ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≤
      Module.finrank ℚ F * Real.log m := by
  classical
  set p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have : Fintype (P.primesOver (𝓞 F)) := (primesOver_finite P (𝓞 F)).fintype
  -- The ideals with nonzero weight are positive powers of primes over `p`.
  have hpow : ∀ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}, idealVonMangoldt I.val ≠ 0 →
      ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k := by
    intro I hI
    by_contra h
    exact hI (by rw [idealVonMangoldt, dite_eq_right_iff.mpr fun h' ↦ absurd h' h])
  have hover : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → v.asIdeal ∈ P.primesOver (𝓞 F) := by
    intro v k hk hvk
    obtain ⟨q, f, hq, hf, hlies, hnorm⟩ := heckeLogDerivCoefficient_bound_liesOver v
    rw [map_pow, hnorm, ← pow_mul] at hvk
    have hqp : q = p := by
      have h : m.minFac = q := by rw [← hvk, hq.pow_minFac (Nat.mul_ne_zero hf.ne' hk.ne')]
      exact h.symm
    subst hqp
    exact ⟨v.isPrime, hlies⟩
  have hle : ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), 0 < k →
      (v.asIdeal ^ k).absNorm = m → Real.log (v.asIdeal.absNorm : ℝ) ≤ Real.log m := by
    intro v k hk hvk
    have h0 : 0 < v.asIdeal.absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
    refine Real.log_le_log (by exact_mod_cast h0) ?_
    rw [← hvk, map_pow]
    exact_mod_cast Nat.le_self_pow hk.ne' _
  -- Weighted ideals inject into the primes over `p` through their radicals.
  set s := Finset.univ.filter fun I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} ↦
    idealVonMangoldt I.val ≠ 0
  have hrad : ∀ I ∈ s, ∃ v : HeightOneSpectrum (𝓞 F), ∃ k, 0 < k ∧ I.val = v.asIdeal ^ k ∧
      I.val.radical = v.asIdeal := by
    intro I hI
    obtain ⟨v, k, hk, hI'⟩ := hpow I (Finset.mem_filter.mp hI).2
    exact ⟨v, k, hk, hI', by rw [hI', Ideal.radical_pow v.asIdeal hk.ne', v.isPrime.radical]⟩
  have hcard : s.card ≤ Fintype.card (P.primesOver (𝓞 F)) := by
    rw [← Fintype.card_coe s]
    refine Fintype.card_le_of_injective (fun I ↦ ⟨I.1.1.radical, ?_⟩) ?_
    · obtain ⟨v, k, hk, hI, hr⟩ := hrad I.1 I.2
      rw [hr]
      exact hover v k hk (hI ▸ I.1.2.2)
    · rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
      obtain ⟨v, k, hk, hI', hrI⟩ := hrad I hI
      obtain ⟨w, j, hj, hJ', hrJ⟩ := hrad J hJ
      have hvw : v.asIdeal = w.asIdeal := by
        have := congrArg Subtype.val hIJ
        simp only at this
        rw [← hrI, ← hrJ, this]
      have h2 : 2 ≤ v.asIdeal.absNorm := by
        have h0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
        have h1 : v.asIdeal.absNorm ≠ 1 := by
          rw [Ne, Ideal.absNorm_eq_one_iff]
          exact v.isPrime.ne_top
        omega
      have hkj : k = j := by
        have hI2 := I.2.2
        have hJ2 := J.2.2
        rw [hI', map_pow] at hI2
        rw [hJ', ← hvw, map_pow] at hJ2
        exact Nat.pow_right_injective h2 (hI2.trans hJ2.symm)
      have : I = J := Subtype.ext (by rw [hI', hJ', hvw, hkj])
      subst this
      rfl
  have hprimes : Fintype.card (P.primesOver (𝓞 F)) ≤ Module.finrank ℚ F := by
    rw [← RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank P (𝓞 F),
      Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have : q.1.IsPrime := q.2.1
    have : q.1.LiesOver P := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter_ne_zero]
  have hlogm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  calc ∑ I ∈ s, idealVonMangoldt I.val ≤ ∑ _I ∈ s, Real.log m := by
        refine Finset.sum_le_sum fun I hI ↦ ?_
        obtain ⟨v, k, hk, hI', -⟩ := hrad I hI
        rw [hI', idealVonMangoldt_prime_pow v hk]
        exact hle v k hk (hI' ▸ I.2.2)
    _ = s.card * Real.log m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Module.finrank ℚ F * Real.log m := by
        gcongr
        exact_mod_cast hcard.trans hprimes

/-- Paper: Lemma B.6.1.4, p. 638. The logarithmic-derivative coefficients are
bounded by a constant times `log m`, with the constant depending only on the field degree. -/
theorem heckeLogDerivCoefficient_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [NumberField F], Module.finrank ℚ F = d →
        ∀ᶠ m : ℕ in atTop, ∀ χ : U[F],
          ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ ≤ C * Real.log (m : ℝ) := by
  refine ⟨d + 1, by positivity, fun F _ _ hd ↦ ?_⟩
  subst hd
  filter_upwards [eventually_ge_atTop 2] with m hm χ
  classical
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := hfin.to_subtype
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m} := Fintype.ofFinite _
  have hsum := heckeLogDerivCoefficient_bound_finsum_le (F := F) hm
  rw [finsum_eq_sum_of_fintype] at hsum
  unfold heckeLogDerivCoefficient
  rw [finsum_eq_sum_of_fintype]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun I _ ↦
    heckeLogDerivCoefficient_bound_norm_le χ I.val).trans (hsum.trans ?_))
  gcongr
  linarith

-- TODO(paper-gap): In (B.6.1.16) a pure norm twist can have a pole in Ω.
-- Restrict the logarithm to heights above the pole. After (B.6.1.19) the
-- summand must retain the power m in N(p)^(m * (1 + αη(T))).
-- TODO(paper-gap): Substituting the radii from (B.6.1.18) into the first
-- coefficient in (B.6.1.20) gives 4(1 + 3α) / ((1 - α)^2 η(T)).

open Complex in
/-- The inequality for the three Euler factors with a common radius and a unit phase. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product {r : ℝ} (hr : 0 ≤ r) (hr₁ : r < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - (r : ℂ) * z)⁻¹ ^ 4 *
      (1 - (r : ℂ) * z ^ 2)⁻¹‖ := by
  have h₀ : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hr]; exact hr₁
  have h₁ : ‖(r : ℂ) * z‖ < 1 := by simpa [norm_mul, hz] using h₀
  have h₂ : ‖(r : ℂ) * z ^ 2‖ < 1 := by simpa [norm_mul, norm_pow, hz] using h₀
  have hinv {w : ℂ} (hw : ‖w‖ < 1) : (1 - w)⁻¹ = exp (-log (1 - w)) := by
    rw [exp_neg, exp_log (fun h ↦ hw.ne (by rw [← sub_eq_zero.mp h, norm_one]))]
  rw [hinv h₀, hinv h₁, hinv h₂, ← exp_nat_mul, ← exp_nat_mul, ← exp_add, ← exp_add,
    norm_exp, Real.one_le_exp_iff]
  simp only [add_re, mul_re, re_ofNat, im_ofNat, Nat.cast_ofNat, zero_mul, sub_zero]
  rw [← ((hasSum_re (hasSum_taylorSeries_neg_log h₀)).mul_left 3 |>.add
    ((hasSum_re (hasSum_taylorSeries_neg_log h₁)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h₂))).tsum_eq]
  apply tsum_nonneg
  intro n
  simp only [mul_pow, ← ofReal_pow, div_natCast_re, ofReal_re, mul_re, ofReal_im, zero_mul,
    sub_zero, ← mul_div_assoc, ← add_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hnorm : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have him := sq_norm_sub_sq_re (z ^ n)
  rw [hnorm, one_pow] at him
  rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, pow_two (z ^ n), mul_re]
  have hident :
      3 * r ^ n + 4 * (r ^ n * (z ^ n).re) + r ^ n *
        ((z ^ n).re * (z ^ n).re - (z ^ n).im * (z ^ n).im) =
      2 * r ^ n * ((z ^ n).re + 1) ^ 2 := by
    rw [← sq ((z ^ n).im), ← him]
    ring
  rw [hident]
  positivity

/-- The de la Vallée Poussin Euler-product inequality for the trivial character, a unitary
character, and its square at ordinates in the ratio zero, one, and two. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (a : ℂ) (ha : a.re = 0) :
    1 ≤ ‖(ideleClassNormTwist (1 : U[F]) 0).LSeries (x : ℂ) ^ 3 * (ideleClassNormTwist χ 0).LSeries ((x : ℂ) + a) ^ 4 *
      (ideleClassNormTwist (χ ^ 2) 0).LSeries ((x : ℂ) + 2 * a)‖ := by
  classical
  have h₂a : (2 * a).re = 0 := by simp [Complex.mul_re, ha]
  let s₀ : halfPlane := ⟨(x : ℂ), hx⟩
  let s₁ : halfPlane := ⟨(x : ℂ) + a, by simpa [mem_preimage, Complex.add_re, ha]⟩
  let s₂ : halfPlane := ⟨(x : ℂ) + 2 * a, by simpa [mem_preimage, Complex.add_re, h₂a]⟩
  have hp := (((finiteHeckeL_hasProd (1 : U[F]) s₀).pow 3).mul
    ((finiteHeckeL_hasProd χ s₁).pow 4)).mul (finiteHeckeL_hasProd (χ ^ 2) s₂)
  apply ge_of_tendsto' hp.norm
  intro T
  simp only [norm_prod]
  refine Finset.one_le_prod₀ fun v _ ↦ ?_
  change 1 ≤ ‖finiteHeckeEulerFactor (1 : U[F]) v x ^ 3 *
    finiteHeckeEulerFactor χ v ((x : ℂ) + a) ^ 4 *
    finiteHeckeEulerFactor (χ ^ 2) v ((x : ℂ) + 2 * a)‖
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (χ ^ 2) 0).restrict v (u : v.adicCompletion F) =
        ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  have hu₀ : (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v := HeckeCharacter.isUnramifiedAt_iff.mpr
    fun u ↦ hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)
  have hu₂ (hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v) : (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ by
      rw [show (ideleClassNormTwist (χ ^ 2) 0).restrict v u = ((ideleClassNormTwist χ 0).restrict v u) ^ 2 from
        hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
        hu.restrict_apply_unit_eq_one, one_pow]
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hv₀ : (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 := hres_one u
  have hv₂ : (ideleClassNormTwist (χ ^ 2) 0).localValue v = ((ideleClassNormTwist χ 0).localValue v) ^ 2 := hres_sq u
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  let r := q ^ (-x)
  have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
  have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let z (ψ : U[F]) (b : ℂ) := (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-b)
  have hz (ψ : U[F]) (b : ℂ) (hb : b.re = 0) : ‖z ψ b‖ = 1 := by
    simp [z, norm_ideleClassNormTwist_zero_localValue,
      Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re, hb]
  have hphase (ψ : U[F]) (b : ℂ) :
      (ideleClassNormTwist ψ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-((x : ℂ) + b)) =
        (r : ℂ) * z ψ b := by
    change (ideleClassNormTwist ψ 0).localValue v * (q : ℂ) ^ (-((x : ℂ) + b)) = _
    rw [neg_add, Complex.cpow_add _ _ hqC, ← Complex.ofReal_neg,
      ← Complex.ofReal_cpow hq₀.le]
    exact mul_left_comm ..
  have hsq : z (χ ^ 2) (2 * a) = z χ a ^ 2 := by
    simp only [z, hv₂, mul_pow, neg_mul_eq_mul_neg]
    rw [show (2 : ℂ) = (↑(2 : ℕ) : ℂ) by norm_num, Complex.cpow_nat_mul]
  rw [finiteHeckeEulerFactor, ite_eq_left hu₀, hv₀, one_mul]
  change 1 ≤ ‖(1 - (q : ℂ) ^ (-(x : ℂ)))⁻¹ ^ 3 * _ * _‖
  rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · rw [finiteHeckeEulerFactor, ite_eq_left hu, finiteHeckeEulerFactor, ite_eq_left (hu₂ hu),
      hphase χ a, hphase (χ ^ 2) (2 * a), hsq]
    exact finiteHeckeL_inv_isBigO_oneLine_one_le_norm_eulerFactor_product hr hr₁ (hz χ a ha)
  · rw [finiteHeckeEulerFactor, ite_eq_right hu, one_pow, mul_one, finiteHeckeEulerFactor]
    have hrnorm : ‖(1 : ℂ) - (r : ℂ)‖ = 1 - r := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    split_ifs
    · rw [hphase (χ ^ 2) (2 * a)]
      let w := (r : ℂ) * z (χ ^ 2) (2 * a)
      change 1 ≤ ‖(1 - (r : ℂ))⁻¹ ^ 3 * (1 - w)⁻¹‖
      have hw : ‖w‖ = r := by
        rw [show ‖w‖ = ‖(r : ℂ)‖ * ‖z (χ ^ 2) (2 * a)‖ from norm_mul _ _,
          hz _ _ h₂a, Complex.norm_of_nonneg hr, mul_one]
      have hpos : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr fun h ↦
        hr₁.ne (by rw [← hw, ← sub_eq_zero.mp h, norm_one])
      rw [norm_mul, norm_pow, norm_inv, norm_inv, hrnorm, inv_pow, ← mul_inv,
        one_le_inv₀ (mul_pos (pow_pos (sub_pos.mpr hr₁) 3) hpos)]
      have hle : ‖(1 : ℂ) - w‖ ≤ 1 + r := by
        simpa only [hw, norm_one] using norm_sub_le (1 : ℂ) w
      calc
        (1 - r) ^ 3 * ‖(1 : ℂ) - w‖ ≤ (1 - r) ^ 3 * (1 + r) :=
          mul_le_mul_of_nonneg_left hle (pow_nonneg (sub_nonneg.mpr hr₁.le) _)
        _ = (1 - r) ^ 2 * (1 - r ^ 2) := by ring
        _ ≤ (1 - r) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) (sq_nonneg _)
        _ ≤ 1 := by
          rw [mul_one]
          exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)
    · rw [mul_one, norm_pow, norm_inv, hrnorm, inv_pow,
        one_le_inv₀ (pow_pos (sub_pos.mpr hr₁) 3)]
      exact pow_le_one₀ (sub_nonneg.mpr hr₁.le) (by linarith)

/-- Euler product inequality in the exact variables used in the bound. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_euler (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {x : ℝ} (hx : 1 < x) (t : ℝ) :
    1 ≤ ‖dedekindZeta F x‖ ^ 3 * ‖L ⟨x,t⟩‖ ^ 4 *
      ‖finiteHeckeL (χ ^ 2) ⟨⟨x,2*t⟩,hx⟩‖ := by
  let a : ℂ := ⟨0,t⟩
  have h := finiteHeckeL_inv_isBigO_oneLine_norm_finiteHeckeL_product_ge_one χ hx a rfl
  have h1 : (x : ℂ) + a = ⟨x,t⟩ := by apply Complex.ext <;> simp [a]
  have h2 : (x : ℂ) + 2 * a = ⟨x,2*t⟩ := by apply Complex.ext <;> simp [a, Complex.mul_re, Complex.mul_im]
  have hζ := completedHeckeL_one_eq_dedekindZeta (F := F) (⟨x,hx⟩ : halfPlane)
  change heckeGammaFactor (1 : U[F]) x * _ = _ at hζ
  rw [← heckeGammaFactor_one] at hζ
  have hz := mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (zero_lt_one.trans hx)) hζ
  rw [h1, h2, norm_mul, norm_mul, norm_pow, norm_pow] at h
  rw [hSeries ⟨⟨x,t⟩,hx⟩]
  simpa only [finiteHeckeL, hz] using h

private theorem finiteHeckeL_inv_isBigO_oneLine_scalar {V B X L Q : ℝ} (hV : 3 ≤ V) (hB : 0 ≤ B) (hX : 0 ≤ X) (hQ : 0 ≤ Q)
    (hzeta : B ≤ V ^ 13) (hsq : Q ≤ V) (hdiff : X ≤ L + (V ^ 11)⁻¹)
    (hprod : 1 ≤ B ^ 3 * X ^ 4 * Q) : (V ^ 11)⁻¹ ≤ L := by
  by_contra! hbad
  have hpos : 0 < V := by linarith
  have ht : X ≤ 2 / V ^ 11 := by rw [div_eq_mul_inv]; linarith
  have h := calc
    1 ≤ B ^ 3 * X ^ 4 * Q := hprod
    _ ≤ (V ^ 13) ^ 3 * (2 / V ^ 11) ^ 4 * V := by gcongr
    _ = 16 / V ^ 4 := by field_simp; ring
  have hh : 3 ^ 4 ≤ V ^ 4 := by gcongr
  have := (le_div_iff₀ (pow_pos hpos 4)).mp h
  norm_num at hh
  linarith

/-- A local version of the strip bounds sufficient for the reciprocal estimate. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds (χ : U[F]) (L : ℂ → ℂ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (m : ℕ) (hm : m ≠ 0)
    (ha : ∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩)
    (h₁ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1,
      ‖L ⟨1 + d,t⟩ - L ⟨1,t⟩‖ ≤ |t| ^ m * d)
    (h₂ : ∀ᶠ t : ℝ in atAbsTop, ∀ d ∈ Ioc (0:ℝ) 1, ∀ hd : 1 < 1+d,
      ‖finiteHeckeL (χ ^ 2) ⟨⟨1+d,2*t⟩,hd⟩‖ ≤ |t| ^ m) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  let V (t : ℝ) := |t| ^ m
  let d (t : ℝ) := (V t ^ 12)⁻¹
  have hV : Tendsto V atAbsTop atTop :=
    (tendsto_pow_atTop (α := ℝ) hm).comp tendsto_comap
  have hd : Tendsto d atAbsTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (α := ℝ) (by decide : 12 ≠ 0)).comp hV)
  have hx : Tendsto (fun t ↦ 1+d t) atAbsTop (𝓝[>] (1:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hd.const_add 1, ?_⟩
    filter_upwards [hV.eventually_gt_atTop 0] with t ht
    change 1 < 1 + (V t ^ 12)⁻¹
    exact lt_add_of_pos_right _ (inv_pos.mpr (pow_pos ht 12))
  obtain ⟨C,hC⟩ := ((NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm.comp hx).isBoundedUnder_le.eventually_le
  have hbound : ∀ᶠ t : ℝ in atAbsTop, (V t ^ 11)⁻¹ ≤ ‖L ⟨1,t⟩‖ := by
    filter_upwards [hC, hV.eventually_ge_atTop C, hV.eventually_ge_atTop 3,
      hd.eventually_le_const zero_lt_one, h₁, h₂] with t hζ hCV hv hdle hdiff hsq
    have hv' : 0 < V t := by linarith
    have hdt : 0 < d t := inv_pos.mpr (pow_pos hv' 12)
    have hxt : 1 < 1 + d t := lt_add_of_pos_right _ hdt
    have hz : d t * ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ C := by
      simpa [Function.comp_def, norm_mul, Real.norm_of_nonneg hdt.le] using hζ
    apply finiteHeckeL_inv_isBigO_oneLine_scalar hv (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) _ (hsq (d t) ⟨hdt,hdle⟩ hxt) _
      (finiteHeckeL_inv_isBigO_oneLine_euler χ L hSeries hxt t)
    · have hvBound : ‖dedekindZeta F (1 + d t : ℝ)‖ ≤ V t / d t :=
        (le_div_iff₀ hdt).mpr (by simpa only [mul_comm (d t)] using hz.trans hCV)
      exact hvBound.trans_eq (show V t / d t = V t ^ 13 by dsimp only [d]; rw [div_inv_eq_mul, pow_succ (V t) 12, mul_comm])
    · calc
        _ ≤ ‖L ⟨1,t⟩‖ + ‖L ⟨1+d t,t⟩ - L ⟨1,t⟩‖ := by
          linarith [norm_sub_norm_le (L ⟨1+d t,t⟩) (L ⟨1,t⟩)]
        _ ≤ ‖L ⟨1,t⟩‖ + V t * d t := add_le_add_right (hdiff _ ⟨hdt,hdle⟩) _
        _ = _ := by dsimp [d]; field_simp
  refine ⟨?_, m*11, Nat.mul_pos (Nat.pos_of_ne_zero hm) (by decide), Asymptotics.IsBigO.of_bound 1 ?_⟩
  · filter_upwards [ha, hbound, hV.eventually_gt_atTop 0] with t ht hb hv
    exact ⟨ht, norm_pos_iff.mp ((inv_pos.mpr (pow_pos hv 11)).trans_le hb)⟩
  · filter_upwards [hbound, hV.eventually_gt_atTop 0] with t ht hv
    rw [norm_inv, Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _), one_mul, pow_mul]
    exact (inv_le_comm₀ ((inv_pos.mpr (pow_pos hv 11)).trans_le ht) (pow_pos hv 11)).mpr ht


private theorem finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat (G : ℂ → ℂ) (a b M : ℝ)
    (hO : G =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M) :
    ∃ n : ℕ, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖G z‖ ≤ |z.im| ^ n := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  obtain ⟨c,hc⟩ := Asymptotics.isBigO_iff.mp hO
  simp only [eventually_inf_principal, eventually_comap, eventually_atTop] at hc
  obtain ⟨T,hT⟩ := hc
  refine ⟨n+1, max T (max 1 c), fun z hz htz ↦ ?_⟩
  have hz₁ : 1 ≤ |z.im| := (le_max_left 1 c).trans ((le_max_right ..).trans htz)
  have hzc : c ≤ |z.im| := (le_max_right 1 c).trans ((le_max_right ..).trans htz)
  have h := hT |z.im| ((le_max_left ..).trans htz) z rfl hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  calc
    ‖G z‖ ≤ c * |z.im| ^ M := h
    _ ≤ |z.im| * |z.im| ^ M := by gcongr
    _ ≤ |z.im| * |z.im| ^ (n:ℝ) := by gcongr
    _ = _ := by rw [Real.rpow_natCast, pow_succ, mul_comm]

private theorem finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    {n : ℕ} {T : ℝ} (hT : ∀ z : ℂ, z.re ∈ Icc (-1:ℝ) 4 → T ≤ |z.im| → ‖L z‖ ≤ |z.im| ^ n)
    (t : ℝ) (ht : max 2 (T + 2) ≤ |t|) {σ : ℝ} (hσ : σ ∈ Icc (1:ℝ) 2) :
    AnalyticAt ℂ L ⟨σ,t⟩ ∧ ‖deriv L ⟨σ,t⟩‖ ≤ (2*|t|)^n := by
  let s : ℂ := ⟨σ,t⟩
  have him := (le_max_left 2 (T+2)).trans ht
  have hlarge := (le_max_right 2 (T+2)).trans ht
  have hDisk {w : ℂ} (hw : w ∈ Metric.closedBall s 1) :
      w.re ∈ Ioo (-1:ℝ) 4 ∧ T < |w.im| ∧ |w.im| ≤ 2 * |t| := by
    have dist := mem_closedBall_iff_norm.mp hw
    have hre := (Complex.abs_re_le_norm (w - s)).trans dist
    have him' := (Complex.abs_im_le_norm (w - s)).trans dist
    change |w.re - σ| ≤ 1 at hre
    change |w.im - t| ≤ 1 at him'
    rw [abs_le] at hre
    refine ⟨⟨by linarith [hre.1,hσ.1], by linarith [hre.2,hσ.2]⟩, ?_, ?_⟩
    · linarith [(abs_sub_abs_le_abs_sub t w.im).trans (by simpa [abs_sub_comm] using him')]
    · linarith [(abs_sub_abs_le_abs_sub w.im t).trans him']
  have han {w : ℂ} (hw : w ∈ Metric.closedBall s 1) : AnalyticAt ℂ L w := by
    obtain ⟨hRe,hLo,hHi⟩ := hDisk hw
    apply (hL (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hp
    have hre := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hRe
    have him := (isOpen_Ioo.preimage Complex.continuous_im.abs).mem_nhds
      (show w ∈ (fun z : ℂ ↦ |z.im|) ⁻¹' Ioo T (|w.im|+1) from ⟨hLo, by linarith⟩)
    have hb : ∀ᶠ z in 𝓝 w, ‖L z‖ ≤ (|w.im|+1)^n := by
      filter_upwards [hre,him] with z hz h'z
      exact (hT z (Ioo_subset_Icc_self hz) h'z.1.le).trans (pow_le_pow_left₀ (abs_nonneg _) h'z.2.le _)
    have hp' := (tendsto_norm_cobounded_atTop.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop ((|w.im|+1)^n)
    obtain ⟨_,h,h'⟩ := ((hb.filter_mono nhdsWithin_le_nhds).and hp').exists
    exact h'.not_ge h
  refine ⟨han (Metric.mem_closedBall_self zero_le_one), ?_⟩
  have hDiff : DiffContOnCl ℂ L (Metric.ball s 1) :=
    (show DifferentiableOn ℂ L (Metric.closedBall s 1) from fun w hw ↦
      (han hw).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
  have hCircle : ∀ w ∈ Metric.sphere s 1, ‖L w‖ ≤ (2 * |t|)^n := by
    intro w hw
    obtain ⟨hRe,hLo,hHi⟩ := hDisk (Metric.sphere_subset_closedBall hw)
    exact (hT w (Ioo_subset_Icc_self hRe) hLo.le).trans (pow_le_pow_left₀ (abs_nonneg _) hHi _)
  simpa only [div_one] using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hDiff hCircle

/-- Reduction to polynomial *upper* bounds. No log derivative or zero-free region is needed. -/
private theorem finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hG : ∃ M : ℝ, L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (-1:ℝ) 4)] fun s ↦ |s.im| ^ M)
    (hG₂ : ∃ n : ℕ, ∃ T : ℝ, ∀ z : halfPlane, (z:ℂ).re ≤ 2 → T ≤ |(z:ℂ).im| →
      ‖finiteHeckeL (χ^2) z‖ ≤ |(z:ℂ).im| ^ n) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1,t⟩ ∧ L ⟨1,t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1,t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  obtain ⟨M,hM⟩ := hG
  obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat L _ _ _ hM
  obtain ⟨k,T₂,hT₂⟩ := hG₂
  let m := 2 * (n+k) + 1
  have hb {x : ℝ} (hx : 2 ≤ x) {j : ℕ} (hj : j ≤ n + k) : (2 * x) ^ j ≤ x ^ m := by
    have hx₁ : 1 ≤ x := by linarith
    calc
      (2*x) ^ j ≤ (x*x) ^ j := by gcongr
      _ = x ^ (2*j) := by rw [← sq, pow_mul]
      _ ≤ x ^ m := pow_le_pow_right₀ hx₁ (by dsimp [m]; omega)
  have hlim : Tendsto abs atAbsTop atTop := tendsto_comap
  have hev := hlim.eventually_ge_atTop (max 2 (T+2))
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_bounds χ L hSeries m (Nat.succ_ne_zero _)
  · filter_upwards [hev] with t ht
    exact (finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht ⟨le_rfl,one_le_two⟩).1
  · filter_upwards [hev] with t ht
    have hs (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) := finiteHeckeL_inv_isBigO_oneLine_analytic_and_deriv_strip L hL hT t ht hσ
    have hd (σ : ℝ) (hσ : σ ∈ Icc (1:ℝ) 2) : HasDerivAt (fun u : ℝ ↦ L ⟨u,t⟩) (deriv L ⟨σ,t⟩) σ := by
      have he (u : ℝ) : (u:ℂ) + ⟨0,t⟩ = ⟨u,t⟩ := by apply Complex.ext <;> simp
      have hd := ((hs σ hσ).1.differentiableAt.hasDerivAt.comp_of_eq (x := (σ:ℂ))
        ((hasDerivAt_id (σ:ℂ)).add_const (⟨0,t⟩:ℂ)) (he σ).symm).comp_ofReal
      simpa only [he,mul_one,id_eq,Function.comp_def] using hd
    intro d hd'
    have hu : 1+d ∈ Icc (1:ℝ) 2 := ⟨by linarith [hd'.1], by linarith [hd'.2]⟩
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a := 1) (b := 2)
      (fun σ hσ ↦ (hd σ hσ).hasDerivWithinAt)
      (fun σ hσ ↦ (hs σ (Ico_subset_Icc_self hσ)).2.trans (hb ((le_max_left ..).trans ht) (by omega))) _ hu
    simpa using h
  · filter_upwards [hev, hlim.eventually_ge_atTop T₂] with t ht ht₂
    intro d hd hd'
    have h := hT₂ (⟨⟨1+d,2*t⟩,hd'⟩ : halfPlane) (by change 1+d ≤ 2; linarith [hd.2])
      (by change T₂ ≤ |2*t|; rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]; linarith [abs_nonneg t])
    change _ ≤ |2*t| ^ k at h
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at h
    exact h.trans (hb ((le_max_left ..).trans ht) (by omega))


/-- Paper: Theorem B.6.1.6, p. 640. The reciprocal of the finite Hecke
L-function grows at most polynomially on `Re(s) = 1` at large absolute heights.
Deviation: Eventual analyticity and nonvanishing make the reciprocal well-defined. -/
theorem finiteHeckeL_inv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      ∃ N : ℕ, 0 < N ∧ (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) =O[atAbsTop] (fun t ↦ |t| ^ N) := by
  apply finiteHeckeL_inv_isBigO_oneLine_reciprocal_of_strip_growth χ L hL hSeries
  · obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (-1) 4 (by norm_num)
    exact ⟨M,hM⟩
  · obtain ⟨G,hG,hAgree⟩ := finiteHeckeL_exists_continuation (χ^2)
    obtain ⟨M,_,hM⟩ := finiteHeckeL_continuation_isBigO_rpow (χ^2) G hG hAgree 1 2 one_lt_two
    obtain ⟨n,T,hT⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat G _ _ _ hM
    exact ⟨n,T,fun z hz ht ↦ hAgree z ▸ hT z ⟨z.2.le,hz⟩ ht⟩

-- TODO(paper-gap): Equation (B.6.1.23) uses the finite L-factors. Its χ²
-- argument has height 2t, which (B.6.1.28) must retain.
-- TODO(paper-gap): The upper bound in (B.6.1.28) uses the critical-strip exponent
-- for σ > 1, where that exponent can be negative and the Euler factors need not decay.

/-- A continuation of the completed L-function with the same order as `L` on `Re s > 0`. -/
private theorem finiteHeckeL_zeroFreeRegion_completed (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ Λ : ℂ → ℂ, MeromorphicNFOn Λ univ ∧ (∀ s : halfPlane, Λ s = completedHeckeL χ s) ∧
      ∀ s : ℂ, 0 < s.re → meromorphicOrderAt Λ s = meromorphicOrderAt L s := by
  have hΓ (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor χ) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  let M : ℂ → ℂ := fun w ↦ heckeGammaFactor χ w * L w
  have hM : MeromorphicOn M univ := fun x _ ↦
    (meromorphic_heckeGammaFactor χ x).mul (hL (mem_univ x)).meromorphicAt
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn _ _, fun s ↦ ?_,
    fun s hs ↦ ?_⟩
  · have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hMan : AnalyticAt ℂ M s :=
      (hΓ s hs).mul (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    simp [M, hSeries s, completedHeckeL, finiteHeckeL]
  · rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hΓ s hs) (heckeGammaFactor_ne_zero_of_re_pos χ hs)

/-- No zero on or to the right of `Re s = 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_order_nonpos (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) : meromorphicOrderAt L s ≤ 0 := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := finiteHeckeL_zeroFreeRegion_completed F χ L hL hSeries
  by_contra! h
  rw [← hord s (by linarith)] at h
  exact (completedHeckeL_continuation_zeros χ Λ hΛ hΛs (by linarith) h).not_ge hs

/-- On `Re s > 0` the continuation has at most one pole, and it is simple. -/
private theorem finiteHeckeL_zeroFreeRegion_poles (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ p : ℂ, ∀ s : ℂ, 0 < s.re →
      (-1 ≤ meromorphicOrderAt L s) ∧ (s ≠ p → AnalyticAt ℂ L s) := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := finiteHeckeL_zeroFreeRegion_completed F χ L hL hSeries
  have hgood (p : ℂ) (hΛp : -1 ≤ meromorphicOrderAt Λ p)
      (han : ∀ s, 0 < s.re → s ≠ p → AnalyticAt ℂ Λ s) :
      ∀ s : ℂ, 0 < s.re → (-1 ≤ meromorphicOrderAt L s) ∧ (s ≠ p → AnalyticAt ℂ L s) := by
    intro s hs
    by_cases hsp : s = p
    · subst hsp
      exact ⟨hord s hs ▸ hΛp, fun h ↦ (h rfl).elim⟩
    · have h0 : 0 ≤ meromorphicOrderAt L s := hord s hs ▸ (han s hs hsp).meromorphicOrderAt_nonneg
      exact ⟨le_trans (by decide) h0,
        fun _ ↦ (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp h0⟩
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨-, -, h1, han⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Λ hΛ hΛs hχ
    refine ⟨1 + Complex.I * t, hgood _ h1.ge fun s hs hsp ↦ han s ?_⟩
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨fun h ↦ ?_, hsp⟩
    rw [h] at hs
    simp at hs
  · have hD := completedHeckeL_continuation_entire χ Λ hΛ hΛs hχ
    exact ⟨0, hgood 0 (le_trans (by decide) (hD.analyticAt 0).meromorphicOrderAt_nonneg)
      fun s _ _ ↦ hD.analyticAt s⟩

/-- Comparison of Euler products with Dedekind zeta at a real point to the left:
for `1 < y ≤ Re s`, `‖L(s, ψ)‖ ≤ ‖ζ_F(y)‖` and `1 ≤ ‖L(s, ψ)‖ * ‖ζ_F(y)‖`.
Public for the horizontal estimates of §1.4.7 (`Ch01_Introduction/Sec4.lean`). -/
theorem finiteHeckeL_zeroFreeRegion_euler (F : Type*) [Field F] [NumberField F]
    (ψ : U[F]) (s : halfPlane) {y : ℝ} (hy : 1 < y) (hys : y ≤ (s : ℂ).re) :
    ‖finiteHeckeL ψ s‖ ≤ ‖dedekindZeta F y‖ ∧
      1 ≤ ‖finiteHeckeL ψ s‖ * ‖dedekindZeta F y‖ := by
  classical
  have hZ := dedekindZeta_hasProd F (s := (y : ℂ)) (by simpa using hy)
  have hP := finiteHeckeL_hasProd ψ s
  have hfac (v : HeightOneSpectrum (𝓞 F)) :
      ‖finiteHeckeEulerFactor ψ v s‖ ≤ ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ ∧
        1 ≤ ‖finiteHeckeEulerFactor ψ v s‖ * ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ := by
    let q : ℝ := v.asIdeal.absNorm
    have hq : 1 < q := by
      dsimp only [q]
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hq₀ : 0 < q := zero_lt_one.trans hq
    let r : ℝ := q ^ (-y)
    have hr : 0 ≤ r := Real.rpow_nonneg hq₀.le _
    have hr₁ : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
    have hZr : (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)) = (r : ℂ) := by
      change ((q : ℝ) : ℂ) ^ (-(y : ℂ)) = _
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hq₀.le]
    have hZn : ‖(1 - (v.asIdeal.absNorm : ℂ) ^ (-(y : ℂ)))⁻¹‖ = (1 - r)⁻¹ := by
      rw [hZr, norm_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_of_nonneg (sub_nonneg.mpr hr₁.le)]
    rw [hZn]
    have h1r : 0 < 1 - r := sub_pos.mpr hr₁
    have hge : 1 ≤ (1 - r)⁻¹ := (one_le_inv₀ h1r).mpr (by linarith)
    unfold finiteHeckeEulerFactor
    split_ifs with hu
    · let w : ℂ := (ideleClassNormTwist ψ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ))
      have hw : ‖w‖ ≤ r := by
        change ‖_ * ((q : ℝ) : ℂ) ^ (-(s : ℂ))‖ ≤ _
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos hq₀, Complex.neg_re]
        exact Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)
      have hlo : 1 - r ≤ ‖1 - w‖ := by
        have := norm_sub_norm_le (1 : ℂ) w
        rw [norm_one] at this
        linarith
      have hhi : ‖1 - w‖ ≤ 1 + r := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      have hpos : 0 < ‖1 - w‖ := h1r.trans_le hlo
      change ‖(1 - w)⁻¹‖ ≤ _ ∧ 1 ≤ ‖(1 - w)⁻¹‖ * _
      rw [norm_inv]
      refine ⟨inv_anti₀ h1r hlo, ?_⟩
      rw [← mul_inv, one_le_inv₀ (mul_pos hpos h1r)]
      calc ‖1 - w‖ * (1 - r) ≤ (1 + r) * (1 - r) := by gcongr
        _ ≤ 1 := by nlinarith
    · simp only [norm_one, one_mul]
      exact ⟨hge, hge⟩
  constructor
  · apply le_of_tendsto_of_tendsto' hP.norm hZ.norm
    intro T
    simp only [norm_prod]
    gcongr with v
    exact (hfac v).1
  · apply ge_of_tendsto' (hP.norm.mul hZ.norm)
    intro T
    simp only [norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.one_le_prod₀ fun v _ ↦ (hfac v).2

/-- `-1 ≤ x < 0` in `WithTop ℤ` forces `x = -1`. -/
private theorem finiteHeckeL_zeroFreeRegion_eq_neg_one (x : WithTop ℤ) (h₁ : -1 ≤ x) (h₂ : x < 0) :
    x = -1 := by
  induction x using WithTop.recTopCoe with
  | top => exact absurd h₂ (by simp)
  | coe n =>
    have h₁' : (-1 : ℤ) ≤ n := WithTop.coe_le_coe.mp h₁
    have h₂' : n < 0 := WithTop.coe_lt_coe.mp h₂
    have : n = -1 := by omega
    rw [this]
    rfl

/-- A polynomial bound with exponent `d / 4 + 2` on the strip `1/2 ≤ Re s ≤ 5/2` at large
heights, obtained by convexity of the growth order. -/
private theorem finiteHeckeL_zeroFreeRegion_growth (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C T : ℝ, 0 < C ∧ 1 ≤ T ∧ ∀ u : ℂ, u.re ∈ Icc (1 / 2 : ℝ) (5 / 2) → T ≤ |u.im| →
      ‖L u‖ ≤ C * |u.im| ^ ((Module.finrank ℚ F : ℝ) / 4 + 2) := by
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F χ L hL hSeries
  have hf : MeromorphicNFOn L (Complex.re ⁻¹' Ioi (1 / 4 : ℝ)) := fun x _ ↦ hL (mem_univ x)
  have hFinite : {s : ℂ | (1 / 4 : ℝ) < s.re ∧ meromorphicOrderAt L s < 0}.Finite := by
    apply (finite_singleton p).subset
    rintro s ⟨hs, hneg⟩
    by_contra hsp
    have := ((hp s (by linarith)).2 hsp).meromorphicOrderAt_nonneg
    exact hneg.not_ge this
  have hSimple : ∀ s : ℂ, (1 / 4 : ℝ) < s.re → meromorphicOrderAt L s < 0 →
      meromorphicOrderAt L s = -1 := fun s hs hneg ↦
    finiteHeckeL_zeroFreeRegion_eq_neg_one _ (hp s (by linarith)).1 hneg
  -- bound to the right of `Re s = 1`
  have hRight (s : ℂ) (y : ℝ) (hy : 1 < y) (hys : y ≤ s.re) : ‖L s‖ ≤ ‖dedekindZeta F y‖ := by
    have hs : s ∈ halfPlane := show 1 < s.re by linarith
    rw [show L s = finiteHeckeL χ ⟨s, hs⟩ from hSeries ⟨s, hs⟩]
    exact (finiteHeckeL_zeroFreeRegion_euler F χ ⟨s, hs⟩ hy hys).1
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  have hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
      L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi (1 / 4 : ℝ))] fun s ↦ |s.im| ^ ξ := by
    obtain ⟨M, hM, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (1 / 4) 3
      (by norm_num)
    refine ⟨M, hM, ?_⟩
    have hO' : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ici 3)] fun s ↦ |s.im| ^ M := by
      refine Asymptotics.IsBigO.of_bound ‖dedekindZeta F 3‖ ?_
      rw [eventually_inf_principal]
      filter_upwards [hHeight.eventually_ge_atTop 1] with s hs hs3
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      calc ‖L s‖ ≤ ‖dedekindZeta F 3‖ := hRight s 3 (by norm_num) hs3
        _ ≤ ‖dedekindZeta F 3‖ * |s.im| ^ M :=
          le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hs hM.le)
    refine (hO.sup hO').mono ?_
    rw [← inf_sup_left, sup_principal, ← preimage_union]
    refine inf_le_inf_left _ (principal_mono.mpr (preimage_mono fun x (hx : 1 / 4 < x) ↦ ?_))
    rcases le_or_gt x 3 with h | h
    · exact Or.inl ⟨hx.le, h⟩
    · exact Or.inr (show 3 ≤ x from h.le)
  have hO := isBigO_verticalGrowthOrder_add hf hFinite hSimple hGrowth (1 / 2) (5 / 2)
    (by norm_num) (by norm_num) 1 one_pos
  -- the growth order is at most `d / 4 + 1` on the strip
  have hμ (σ : ℝ) (hσ : σ ∈ Icc (1 / 2 : ℝ) (5 / 2)) :
      (verticalGrowthOrder L σ).toReal ≤ d / 4 + 1 := by
    rcases le_or_gt σ 1 with h1 | h1
    · obtain ⟨C, -, hC⟩ := finiteHeckeL_continuation_convexity_bound χ L hL hSeries
      have hline := (hC 1 one_pos).isBigO.mono (inf_le_inf_left _ (principal_mono.mpr
        (preimage_mono (show ({σ} : Set ℝ) ⊆ Icc 0 1 from
          singleton_subset_iff.mpr ⟨by linarith [hσ.1], h1⟩))))
      have hline' : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})]
          fun s ↦ |s.im| ^ (d * ((1 - σ) / 2) + 1) := by
        refine hline.congr' EventuallyEq.rfl ?_
        rw [EventuallyEq, eventually_inf_principal]
        exact Eventually.of_forall fun s (hs : s.re = σ) ↦ by rw [hs]
      refine (verticalGrowthOrder_toReal_le_of_isBigO (by nlinarith [hσ.1]) hline').trans ?_
      nlinarith [hσ.1]
    · have hline : L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (0 : ℝ) := by
        refine Asymptotics.IsBigO.of_bound ‖dedekindZeta F σ‖ ?_
        rw [eventually_inf_principal]
        refine Eventually.of_forall fun s (hs : s.re = σ) ↦ ?_
        rw [Real.rpow_zero, norm_one, mul_one]
        exact hRight s σ h1 hs.ge
      exact (verticalGrowthOrder_toReal_le_of_isBigO le_rfl hline).trans (by positivity)
  obtain ⟨C, hC, hC'⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC'
  obtain ⟨T, hT⟩ := hC'
  refine ⟨C, max T 1, hC, le_max_right _ _, fun u hu huT ↦ ?_⟩
  have h1 : 1 ≤ |u.im| := (le_max_right _ _).trans huT
  have h := hT |u.im| ((le_max_left _ _).trans huT) u rfl hu
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 ?_) hC.le)
  linarith [hμ u.re hu]

/-- The trivial character is unramified with local value one, and the local value of `χ ^ 2`
is the square of that of `χ`. -/
private theorem finiteHeckeL_zeroFreeRegion_local (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (v : HeightOneSpectrum (𝓞 F)) :
    (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 ∧
      ((ideleClassNormTwist χ 0).IsUnramifiedAt v →
        (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v) ∧
      (ideleClassNormTwist (χ ^ 2) 0).localValue v =
        ((ideleClassNormTwist χ 0).localValue v) ^ 2 := by
  have hres (ψ : U[F]) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F) =
        (ψ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : ℂ) := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
  have hres_one (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v (u : v.adicCompletion F) = 1 := by
    rw [hres, PontryaginDual.one_apply, Circle.coe_one]
  have hres_sq (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (χ ^ 2) 0).restrict v (u : v.adicCompletion F) =
        ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F)) ^ 2 := by
    rw [hres, hres]
    rfl
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0 (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  refine ⟨HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦
      hres_one (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u), hres_one u,
    fun hu ↦ HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦ ?_, hres_sq u⟩
  rw [show (ideleClassNormTwist (χ ^ 2) 0).restrict v u =
      ((ideleClassNormTwist χ 0).restrict v u) ^ 2 from
    hres_sq (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u),
    hu.restrict_apply_unit_eq_one, one_pow]

/-- The elementary inequality `3 + 4 cos θ + cos 2θ ≥ 0`, with a possibly ramified phase. -/
private theorem finiteHeckeL_zeroFreeRegion_trig (x : ℝ) (hx : 0 ≤ x) (a a₂ e : ℂ)
    (he : ‖e‖ = 1) (h : (‖a‖ = 1 ∧ a₂ = a ^ 2) ∨ (a = 0 ∧ ‖a₂‖ ≤ 1)) :
    0 ≤ 3 * x + 4 * ((x : ℂ) * (a * e)).re + ((x : ℂ) * (a₂ * e ^ 2)).re := by
  rcases h with ⟨ha, rfl⟩ | ⟨rfl, ha₂⟩
  · obtain ⟨w, hw⟩ : ∃ w, w = a * e := ⟨_, rfl⟩
    have hw1 : ‖w‖ = 1 := by rw [hw, norm_mul, ha, he, one_mul]
    have hsq : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, ← Complex.sq_norm, hw1, one_pow]
    have h2 : a ^ 2 * e ^ 2 = w ^ 2 := by rw [hw, mul_pow]
    rw [h2, ← hw, Complex.re_ofReal_mul, Complex.re_ofReal_mul, sq, Complex.mul_re]
    nlinarith [mul_nonneg hx (sq_nonneg (1 + w.re))]
  · have hn : ‖(x : ℂ) * (a₂ * e ^ 2)‖ ≤ x := by
      rw [norm_mul, norm_mul, norm_pow, he, one_pow, mul_one, Complex.norm_of_nonneg hx]
      exact mul_le_of_le_one_right hx ha₂
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
    simp only [zero_mul, mul_zero, Complex.zero_re]
    linarith

/-- The termwise de la Vallée Poussin inequality for the ideal series of `-L'/L`. -/
private theorem finiteHeckeL_zeroFreeRegion_term (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (σ γ : ℝ) :
    (3 * (-heckeIdealVonMangoldt (ideleClassNormTwist (1 : U[F]) 0) I /
        (I.absNorm : ℂ) ^ (σ : ℂ)) +
      4 * (-heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I /
        (I.absNorm : ℂ) ^ (⟨σ, γ⟩ : ℂ)) +
      -heckeIdealVonMangoldt (ideleClassNormTwist (χ ^ 2) 0) I /
        (I.absNorm : ℂ) ^ (⟨σ, 2 * γ⟩ : ℂ)).re ≤ 0 := by
  classical
  by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
  · obtain ⟨v, k, hk, rfl⟩ := h
    obtain ⟨hu₀, hv₀, hu₂, hv₂⟩ := finiteHeckeL_zeroFreeRegion_local F χ v
    set N : ℕ := (v.asIdeal ^ k).absNorm with hNdef
    have hN : 0 < N := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    set lam : ℝ := Real.log (v.asIdeal.absNorm : ℝ)
    have hlam : 0 ≤ lam := Real.log_natCast_nonneg _
    have hc (ψ : U[F]) : heckeIdealVonMangoldt (ideleClassNormTwist ψ 0) (v.asIdeal ^ k) =
        (if (ideleClassNormTwist ψ 0).IsUnramifiedAt v then
          (ideleClassNormTwist ψ 0).localValue v ^ k else 0) * (lam : ℂ) := by
      rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk]
    set x : ℝ := (N : ℝ) ^ (-σ)
    have hx : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    set e : ℂ := (N : ℂ) ^ (-((γ : ℂ) * Complex.I))
    have he : ‖e‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hN]
      simp
    have hpow (τ : ℝ) : ((N : ℂ) ^ (⟨σ, τ⟩ : ℂ))⁻¹ =
        (x : ℂ) * (N : ℂ) ^ (-((τ : ℂ) * Complex.I)) := by
      have hsplit : (⟨σ, τ⟩ : ℂ) = (σ : ℂ) + (τ : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hsplit, Complex.cpow_add _ _ hNC, mul_inv, Complex.cpow_neg]
      congr 1
      rw [← Complex.cpow_neg, show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_neg,
        ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    have h0 : ((N : ℂ) ^ (σ : ℂ))⁻¹ = (x : ℂ) := by
      have := hpow 0
      rw [show (⟨σ, 0⟩ : ℂ) = (σ : ℂ) from rfl] at this
      simpa using this
    have h1 : ((N : ℂ) ^ (⟨σ, γ⟩ : ℂ))⁻¹ = (x : ℂ) * e := hpow γ
    have h2 : ((N : ℂ) ^ (⟨σ, 2 * γ⟩ : ℂ))⁻¹ = (x : ℂ) * e ^ 2 := by
      rw [hpow, ← Complex.cpow_nat_mul]
      congr 2
      push_cast
      ring
    simp only [div_eq_mul_inv, h0, h1, h2, hc, hv₀, one_pow, ite_eq_left hu₀]
    set a : ℂ := if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v ^ k else 0
    set a₂ : ℂ := if (ideleClassNormTwist (χ ^ 2) 0).IsUnramifiedAt v then
      (ideleClassNormTwist (χ ^ 2) 0).localValue v ^ k else 0
    have hcase : (‖a‖ = 1 ∧ a₂ = a ^ 2) ∨ (a = 0 ∧ ‖a₂‖ ≤ 1) := by
      by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
      · left
        simp only [a, a₂, ite_eq_left hu, ite_eq_left (hu₂ hu), hv₂, norm_pow,
          norm_ideleClassNormTwist_zero_localValue, one_pow, true_and]
        ring
      · right
        refine ⟨ite_eq_right hu, ?_⟩
        simp only [a₂]
        split_ifs
        · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
        · simp
    have key := finiteHeckeL_zeroFreeRegion_trig x hx a a₂ e he hcase
    have hexp : 3 * (-(1 * (lam : ℂ)) * (x : ℂ)) + 4 * (-(a * (lam : ℂ)) * ((x : ℂ) * e)) +
        -(a₂ * (lam : ℂ)) * ((x : ℂ) * e ^ 2) =
        -((lam : ℂ) * (3 * (x : ℂ) + 4 * ((x : ℂ) * (a * e)) + (x : ℂ) * (a₂ * e ^ 2))) := by
      ring
    rw [hexp, Complex.neg_re, Complex.re_ofReal_mul, neg_nonpos]
    apply mul_nonneg hlam
    simpa [Complex.add_re, Complex.mul_re] using key
  · simp [heckeIdealVonMangoldt, idealVonMangoldt, h]

/-- The de la Vallée Poussin inequality for logarithmic derivatives:
`Re (3 L₀'/L₀(σ) + 4 L'/L(σ + iγ) + L₂'/L₂(σ + 2iγ)) ≤ 0` for `σ > 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_three_four_one (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L L₀ L₂ : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s)
    (hL₂ : MeromorphicNFOn L₂ univ) (hS₂ : ∀ s : halfPlane, L₂ s = finiteHeckeL (χ ^ 2) s)
    (σ : ℝ) (hσ : 1 < σ) (γ : ℝ) :
    0 ≤ 3 * -(logDeriv L₀ σ).re + 4 * -(logDeriv L ⟨σ, γ⟩).re +
      -(logDeriv L₂ ⟨σ, 2 * γ⟩).re := by

  let s₀ : halfPlane := ⟨(σ : ℂ), show 1 < (σ : ℂ).re by simpa using hσ⟩
  let s₁ : halfPlane := ⟨⟨σ, γ⟩, show 1 < σ from hσ⟩
  let s₂ : halfPlane := ⟨⟨σ, 2 * γ⟩, show 1 < σ from hσ⟩
  have h₀ := (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) L₀ hL₀ hS₀ s₀).2.2
  have h₁ := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s₁).2.2
  have h₂ := (finiteHeckeL_logDeriv_hasSum_ideals (χ ^ 2) L₂ hL₂ hS₂ s₂).2.2
  have H := Complex.hasSum_re (((h₀.mul_left 3).add (h₁.mul_left 4)).add h₂)
  have hle : (3 * logDeriv L₀ (s₀ : ℂ) + 4 * logDeriv L (s₁ : ℂ) +
      logDeriv L₂ (s₂ : ℂ)).re ≤ 0 := H.nonpos fun I ↦ by
    have := finiteHeckeL_zeroFreeRegion_term F χ I.1 I.2 σ γ
    exact this
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero] at hle
  change 0 ≤ 3 * -(logDeriv L₀ (s₀ : ℂ)).re + 4 * -(logDeriv L (s₁ : ℂ)).re +
    -(logDeriv L₂ (s₂ : ℂ)).re
  linarith

/-- Near `s = 1` from the right, `-Re L₀'/L₀(σ) ≤ 1/(σ - 1) + C` for the trivial character:
the pole at one is at most simple. -/
private theorem finiteHeckeL_zeroFreeRegion_zeta (F : Type*) [Field F] [NumberField F]
    (L₀ : ℂ → ℂ)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s) :
    ∃ η C : ℝ, 0 < η ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + η →
      -(logDeriv L₀ σ).re ≤ 1 / (σ - 1) + C := by
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F 1 L₀ hL₀ hS₀
  have hge := (hp 1 (by simp)).1
  have hreal : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa using (show 1 < r from hr).ne'
  have hne (r : ℝ) (hr : 1 < r) : L₀ r ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) L₀ hL₀ hS₀
      ⟨(r : ℂ), show 1 < (r : ℂ).re by simpa using hr⟩).2.1
  have htop : meromorphicOrderAt L₀ 1 ≠ ⊤ := by
    intro h
    obtain ⟨r, hr, hr1⟩ := ((hreal.eventually (meromorphicOrderAt_eq_top_iff.mp h)).and
      self_mem_nhdsWithin).exists
    exact hne r hr1 hr
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  have hm1 : -1 ≤ m := by
    rw [← hm] at hge
    exact WithTop.coe_le_coe.mp hge
  obtain ⟨g, hg, hg1, hEq⟩ := (meromorphicOrderAt_eq_int_iff (hL₀ (mem_univ 1)).meromorphicAt).mp
    hm.symm
  have hcont : ContinuousAt (logDeriv g) 1 :=
    hg.deriv.continuousAt.div hg.continuousAt hg1
  have hbound : ∀ᶠ z in 𝓝 (1 : ℂ), ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖logDeriv g 1‖))] with z hz
    exact hz.le
  have hlog := logDeriv_congr_nhdsNE hEq
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ),
      logDeriv L₀ z = (m : ℂ) / (z - 1) + logDeriv g z ∧
        ‖logDeriv g z‖ ≤ ‖logDeriv g 1‖ + 1 := by
    filter_upwards [hlog, nhdsWithin_le_nhds hbound, nhdsWithin_le_nhds hg.eventually_analyticAt,
      nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg1), self_mem_nhdsWithin]
      with z hz hb han hgz hz1
    refine ⟨?_, hb⟩
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z := differentiableAt_id.sub_const 1
    rw [hz, show (fun w : ℂ ↦ (w - 1) ^ m • g w) = (fun w ↦ (w - 1) ^ m) * g from rfl,
      logDeriv_mul (f := fun w : ℂ ↦ (w - 1) ^ m) z (zpow_ne_zero _ hz1') hgz
      (hd.zpow (Or.inl hz1')) han.differentiableAt, logDeriv_fun_zpow hd]
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (hreal.eventually hev)
  refine ⟨u - 1, ‖logDeriv g 1‖ + 1, by linarith [hu.out], fun σ hσ hσu ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hsub ⟨hσ, by linarith⟩
  rw [h1, Complex.add_re]
  have hre : ((m : ℂ) / ((σ : ℂ) - 1)).re = m / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, show (m : ℂ) = ((m : ℝ) : ℂ) by
      norm_cast, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre]
  have hσ1 : 0 < σ - 1 := by linarith
  have hm' : -(m : ℝ) / (σ - 1) ≤ 1 / (σ - 1) := by
    apply div_le_div_of_nonneg_right _ hσ1.le
    have : (-1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
  rw [neg_div] at hm'
  linarith

/-- Landau's lemma on the disc of radius one about `c`, with the radii `1/2 < 3/4 < 7/8 < 1`,
an upper bound `M` on the disc and a lower bound `δ` at the centre. -/
private theorem finiteHeckeL_zeroFreeRegion_landau (f : ℂ → ℂ) (c z : ℂ) (M δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ u ∈ Metric.closedBall c 1, AnalyticAt ℂ f u)
    (hM : ∀ u ∈ Metric.closedBall c 1, ‖f u‖ ≤ M) (hc : δ ≤ ‖f c‖)
    (hz : z ∈ Metric.closedBall c (1 / 2)) (hfz : f z ≠ 0)
    (hS : ∀ ρ ∈ Metric.closedBall c (3 / 4), f ρ = 0 → ρ.re ≤ z.re) :
    -(logDeriv f z).re ≤
        landauConstant (1 / 2) (3 / 4) (7 / 8) 1 * Real.log (max (M / δ) 2) ∧
      ∀ ρ₀ ∈ Metric.closedBall c (3 / 4), f ρ₀ = 0 →
        -(logDeriv f z).re ≤ -(1 / (z - ρ₀)).re +
          landauConstant (1 / 2) (3 / 4) (7 / 8) 1 * Real.log (max (M / δ) 2) := by
  have hB : 1 < max (M / δ) 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hfc : f c ≠ 0 := norm_pos_iff.mp (hδ.trans_le hc)
  have hbound : ∀ u ∈ Metric.closedBall c 1, ‖f u / f c‖ ≤ max (M / δ) 2 := by
    intro u hu
    rw [norm_div]
    refine le_trans ?_ (le_max_left _ _)
    calc ‖f u‖ / ‖f c‖ ≤ ‖f u‖ / δ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hc
      _ ≤ M / δ := div_le_div_of_nonneg_right (hM u hu) hδ.le
  exact ⟨landau_neg_re_logDeriv_le_of_forall_re_le hB (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hf hfc hbound hz hfz hS,
    fun ρ₀ hρ₀ hfρ₀ ↦ landau_neg_re_logDeriv_le_of_zero hB (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hf hfc hbound hz hfz hS hρ₀ hfρ₀⟩

/-- `log max(C Z g^E, 2) ≤ log max(C Z, 2) + E log g` for `g ≥ 1`. -/
private theorem finiteHeckeL_zeroFreeRegion_log_le (x E g : ℝ) (hE : 0 ≤ E)
    (hg : 1 ≤ g) :
    Real.log (max (x * g ^ E) 2) ≤ Real.log (max x 2) + E * Real.log g := by
  have hgE : 1 ≤ g ^ E := Real.one_le_rpow hg hE
  have hm : 0 < max x 2 := lt_of_lt_of_le two_pos (le_max_right _ _)
  calc Real.log (max (x * g ^ E) 2) ≤ Real.log (max x 2 * g ^ E) := by
        apply Real.log_le_log (lt_of_lt_of_le two_pos (le_max_right _ _))
        apply max_le
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        · exact (le_max_right x 2).trans (le_mul_of_one_le_right hm.le hgE)
    _ = Real.log (max x 2) + E * Real.log g := by
        rw [Real.log_mul hm.ne' (by positivity), Real.log_rpow (by linarith)]

/-- The final inequality of de la Vallée Poussin's argument. -/
private theorem finiteHeckeL_zeroFreeRegion_final (M Lg σ β : ℝ) (hM : 0 < M) (hLg : 0 < Lg)
    (hσ : σ = 1 + 1 / (2 * M) / Lg) (hβ : 1 - 1 / (15 * M) / Lg ≤ β) (hβ1 : β < 1)
    (h : 0 ≤ 3 / (σ - 1) - 4 / (σ - β) + M * Lg) : False := by
  have hx : 0 < σ - β := by
    rw [hσ]
    have : 0 < 1 / (2 * M) / Lg := by positivity
    linarith
  have hx' : σ - β ≤ 17 / (30 * M * Lg) := by
    have : 1 / (2 * M) / Lg + 1 / (15 * M) / Lg = 17 / (30 * M * Lg) := by
      field_simp
      ring
    rw [hσ]
    linarith
  have h3 : 3 / (σ - 1) = 6 * M * Lg := by
    rw [hσ]
    field_simp
    ring
  have h4 : 120 * M * Lg / 17 ≤ 4 / (σ - β) := by
    rw [le_div_iff₀ hx]
    calc 120 * M * Lg / 17 * (σ - β) ≤ 120 * M * Lg / 17 * (17 / (30 * M * Lg)) :=
          mul_le_mul_of_nonneg_left hx' (by positivity)
      _ = 4 := by field_simp; ring
  have : 0 < M * Lg := by positivity
  nlinarith

/-- Geometry of the discs: a point of `closedBall ⟨3/2, τ⟩ 1` has real part in `[1/2, 5/2]`
and imaginary part within one of `τ`. -/
private theorem finiteHeckeL_zeroFreeRegion_disc (τ : ℝ) (u : ℂ)
    (hu : u ∈ Metric.closedBall (⟨3 / 2, τ⟩ : ℂ) 1) :
    u.re ∈ Icc (1 / 2 : ℝ) (5 / 2) ∧ |u.im - τ| ≤ 1 := by
  have h := mem_closedBall_iff_norm.mp hu
  have hre := (Complex.abs_re_le_norm _).trans h
  have him := (Complex.abs_im_le_norm _).trans h
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rw [abs_le] at hre
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, him⟩

/-- A real point `⟨x, τ⟩` lies in `closedBall ⟨3/2, τ⟩ r` when `|x - 3/2| ≤ r`. -/
private theorem finiteHeckeL_zeroFreeRegion_mem_ball (τ x r : ℝ) (h : |x - 3 / 2| ≤ r) :
    (⟨x, τ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, τ⟩ : ℂ) r := by
  rw [mem_closedBall_iff_norm]
  have : (⟨x, τ⟩ : ℂ) - ⟨3 / 2, τ⟩ = ((x - 3 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rwa [this, Complex.norm_real, Real.norm_eq_abs]

/-- At a point with `Re s ≥ 1` where `L` is analytic, `L` does not vanish. -/
private theorem finiteHeckeL_zeroFreeRegion_ne_zero (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (x : ℂ) (hx : 1 ≤ x.re) (han : AnalyticAt ℂ L x) : L x ≠ 0 :=
  (hL (mem_univ x)).meromorphicOrderAt_eq_zero_iff.mp (le_antisymm
    (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries x hx) han.meromorphicOrderAt_nonneg)

/-- At large heights, zeros of `L` satisfy `β < 1 - c / (d log |γ|)` with an absolute `c`. -/
private theorem finiteHeckeL_zeroFreeRegion_eventual (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ ρ : ℂ, T₀ ≤ |ρ.im| → 0 < meromorphicOrderAt L ρ →
      ρ.re < 1 - 1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)) /
        ((Module.finrank ℚ F : ℝ) * Real.log |ρ.im|) := by
  set K := landauConstant (1 / 2) (3 / 4) (7 / 8) 1 with hKdef
  have hK : 0 < K := landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  set M := 30 * K + 1 with hMdef
  have hM : 0 < M := by positivity
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  obtain ⟨L₀, hL₀, hS₀⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  obtain ⟨L₂, hL₂, hS₂⟩ := finiteHeckeL_exists_continuation (χ ^ 2)
  obtain ⟨η, C₀, hη, hzeta⟩ := finiteHeckeL_zeroFreeRegion_zeta F L₀ hL₀ hS₀
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F χ L hL hSeries
  obtain ⟨p₂, hp₂⟩ := finiteHeckeL_zeroFreeRegion_poles F (χ ^ 2) L₂ hL₂ hS₂
  obtain ⟨C₁, T₁, hC₁, hT₁, hgr₁⟩ := finiteHeckeL_zeroFreeRegion_growth F χ L hL hSeries
  obtain ⟨C₂, T₂, hC₂, hT₂, hgr₂⟩ := finiteHeckeL_zeroFreeRegion_growth F (χ ^ 2) L₂ hL₂ hS₂
  set Z := ‖dedekindZeta F ((3 / 2 : ℝ) : ℂ)‖ with hZdef
  set E : ℝ := d / 4 + 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEd : E ≤ 3 * d := by rw [hE]; linarith
  -- lower bound at the centres
  have hlow (ψ : U[F]) (G : ℂ → ℂ) (hG : ∀ s : halfPlane, G s = finiteHeckeL ψ s) (τ : ℝ) :
      0 < Z ∧ 1 / Z ≤ ‖G ⟨3 / 2, τ⟩‖ := by
    have hs : (⟨3 / 2, τ⟩ : ℂ) ∈ halfPlane := show (1 : ℝ) < 3 / 2 by norm_num
    have h := (finiteHeckeL_zeroFreeRegion_euler F ψ ⟨_, hs⟩ (y := 3 / 2) (by norm_num)
      le_rfl).2
    rw [← hG ⟨_, hs⟩, ← hZdef] at h
    have hZ : 0 < Z := by
      rcases (show (0 : ℝ) ≤ Z from norm_nonneg _).lt_or_eq with hZ | hZ
      · exact hZ
      · rw [← hZ, mul_zero] at h
        linarith
    exact ⟨hZ, (div_le_iff₀ hZ).mpr (by simpa using h)⟩
  have hZ : 0 < Z := (hlow 1 L₀ hS₀ 0).1
  set c₁ := Real.log (max (C₁ * Z) 2) with hc₁
  set c₂ := Real.log (max (C₂ * Z) 2) with hc₂
  set Cst := 3 * C₀ + 4 * K * c₁ + K * c₂ with hCst
  refine ⟨max (max 3 (Real.exp 4)) (max (max (T₁ + 1) (T₂ + 1))
    (max (max (|p.im| + 2) (|p₂.im| + 2)) (max (Real.exp Cst) (Real.exp (1 / η))))),
    le_max_of_le_left (le_max_left _ _), ?_⟩
  rintro ⟨β, γ⟩ hγ hord
  simp only [max_le_iff] at hγ
  obtain ⟨⟨hγ3, hγ4⟩, ⟨hγT₁, hγT₂⟩, ⟨hγp, hγp₂⟩, hγC, hγη⟩ := hγ
  change 3 ≤ |γ| at hγ3
  change Real.exp 4 ≤ |γ| at hγ4
  change T₁ + 1 ≤ |γ| at hγT₁
  change T₂ + 1 ≤ |γ| at hγT₂
  change |p.im| + 2 ≤ |γ| at hγp
  change |p₂.im| + 2 ≤ |γ| at hγp₂
  change Real.exp Cst ≤ |γ| at hγC
  change Real.exp (1 / η) ≤ |γ| at hγη
  change β < 1 - 1 / (15 * M) / (d * Real.log |γ|)
  have hγ0 : 0 < |γ| := by linarith
  have hlog4 : 4 ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγ4
  have hlogC : Cst ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγC
  have hlogη : 1 / η ≤ Real.log |γ| := (Real.le_log_iff_exp_le hγ0).mpr hγη
  set Lg := d * Real.log |γ| with hLg
  have hLg4 : 4 ≤ Lg := by rw [hLg]; nlinarith
  have hLg0 : 0 < Lg := by linarith
  by_contra! hβ
  -- the zero lies left of one
  have hβ1 : β < 1 := by
    by_contra! h
    exact (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries ⟨β, γ⟩ h).not_gt hord
  have ha : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hc : 1 / (15 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hβ34 : 3 / 4 ≤ β := by
    have : 1 / (15 * M) / Lg ≤ 1 / 4 := by
      rw [div_le_iff₀ hLg0]; linarith
    linarith
  set σ := 1 + 1 / (2 * M) / Lg with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / (2 * M) / Lg := by positivity
    linarith
  have hσ2 : σ ≤ 2 := by
    have : 1 / (2 * M) / Lg ≤ 1 := by
      rw [div_le_iff₀ hLg0]; linarith
    linarith
  have hση : σ ≤ 1 + η := by
    have : 1 / (2 * M) / Lg ≤ η := by
      rw [div_le_iff₀ hLg0]
      have h1 : 1 ≤ η * Real.log |γ| := by
        rw [div_le_iff₀ hη] at hlogη; linarith
      nlinarith
    linarith
  -- the three bounds
  have h341 := finiteHeckeL_zeroFreeRegion_three_four_one F χ L L₀ L₂ hL hSeries hL₀ hS₀ hL₂ hS₂
    σ hσ1 γ
  have hX₀ := hzeta σ hσ1 hση
  have hγsq : 3 * |γ| ≤ |γ| ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right hγ3 (abs_nonneg γ)
  have hγ2 : |γ| + 1 ≤ |γ| ^ 2 := by linarith
  have hγ2' : 2 * |γ| + 1 ≤ |γ| ^ 2 := by linarith
  have hdisc₁ : ∀ u ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) 1,
      AnalyticAt ℂ L u ∧ ‖L u‖ ≤ C₁ * (|γ| ^ 2) ^ E := by
    intro u hu
    obtain ⟨hre, him⟩ := finiteHeckeL_zeroFreeRegion_disc γ u hu
    have hlo : |γ| - 1 ≤ |u.im| := by
      have := abs_sub_abs_le_abs_sub γ u.im
      rw [abs_sub_comm] at this
      linarith
    have hhi : |u.im| ≤ |γ| + 1 := by
      have := abs_sub_abs_le_abs_sub u.im γ
      linarith
    refine ⟨(hp u (by linarith [hre.1])).2 fun h ↦ ?_, ?_⟩
    · rw [h] at hlo
      linarith
    · refine (hgr₁ u hre (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC₁.le)
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) hE0
  have hdisc₂ : ∀ u ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) 1,
      AnalyticAt ℂ L₂ u ∧ ‖L₂ u‖ ≤ C₂ * (|γ| ^ 2) ^ E := by
    intro u hu
    obtain ⟨hre, him⟩ := finiteHeckeL_zeroFreeRegion_disc (2 * γ) u hu
    have h2γ : |2 * γ| = 2 * |γ| := by rw [abs_mul, abs_two]
    have hlo : 2 * |γ| - 1 ≤ |u.im| := by
      have := abs_sub_abs_le_abs_sub (2 * γ) u.im
      rw [abs_sub_comm] at this
      linarith
    have hhi : |u.im| ≤ 2 * |γ| + 1 := by
      have := abs_sub_abs_le_abs_sub u.im (2 * γ)
      linarith
    refine ⟨(hp₂ u (by linarith [hre.1])).2 fun h ↦ ?_, ?_⟩
    · rw [h] at hlo
      linarith
    · refine (hgr₂ u hre (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hC₂.le)
      exact Real.rpow_le_rpow (abs_nonneg _) (by linarith) hE0
  obtain ⟨-, hlow₁⟩ := hlow χ L hSeries γ
  obtain ⟨-, hlow₂⟩ := hlow (χ ^ 2) L₂ hS₂ (2 * γ)
  have hz₁ : (⟨σ, γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (1 / 2) :=
    finiteHeckeL_zeroFreeRegion_mem_ball γ σ (1 / 2) (by rw [abs_le]; constructor <;> linarith)
  have hz₂ : (⟨σ, 2 * γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) (1 / 2) :=
    finiteHeckeL_zeroFreeRegion_mem_ball (2 * γ) σ (1 / 2)
      (by rw [abs_le]; constructor <;> linarith)
  have hρ₁ : (⟨β, γ⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (3 / 4) :=
    finiteHeckeL_zeroFreeRegion_mem_ball γ β (3 / 4) (by rw [abs_le]; constructor <;> linarith)
  have h34 (c : ℂ) : Metric.closedBall c (3 / 4) ⊆ Metric.closedBall c 1 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hLz : L ⟨σ, γ⟩ ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨⟨σ, γ⟩, hσ1⟩).2.1
  have hLz₂ : L₂ ⟨σ, 2 * γ⟩ ≠ 0 :=
    (finiteHeckeL_logDeriv_hasSum_ideals (χ ^ 2) L₂ hL₂ hS₂ ⟨⟨σ, 2 * γ⟩, hσ1⟩).2.1
  have hLρ : L ⟨β, γ⟩ = 0 := by
    by_contra h
    exact hord.ne' ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr h)
  have hS₁ : ∀ ρ' ∈ Metric.closedBall (⟨3 / 2, γ⟩ : ℂ) (3 / 4), L ρ' = 0 →
      ρ'.re ≤ (⟨σ, γ⟩ : ℂ).re := by
    intro ρ' hρ' h0
    by_contra! hlt
    exact finiteHeckeL_zeroFreeRegion_ne_zero F χ L hL hSeries ρ'
      (by change σ < ρ'.re at hlt; linarith) (hdisc₁ ρ' (h34 _ hρ')).1 h0
  have hS₂' : ∀ ρ' ∈ Metric.closedBall (⟨3 / 2, 2 * γ⟩ : ℂ) (3 / 4), L₂ ρ' = 0 →
      ρ'.re ≤ (⟨σ, 2 * γ⟩ : ℂ).re := by
    intro ρ' hρ' h0
    by_contra! hlt
    exact finiteHeckeL_zeroFreeRegion_ne_zero F (χ ^ 2) L₂ hL₂ hS₂ ρ'
      (by change σ < ρ'.re at hlt; linarith) (hdisc₂ ρ' (h34 _ hρ')).1 h0
  have hX₁ := (finiteHeckeL_zeroFreeRegion_landau L _ _ (C₁ * (|γ| ^ 2) ^ E) (1 / Z)
    (by positivity) (fun u hu ↦ (hdisc₁ u hu).1) (fun u hu ↦ (hdisc₁ u hu).2) hlow₁ hz₁ hLz
    hS₁).2 _ hρ₁ hLρ
  have hX₂ := (finiteHeckeL_zeroFreeRegion_landau L₂ _ _ (C₂ * (|γ| ^ 2) ^ E) (1 / Z)
    (by positivity) (fun u hu ↦ (hdisc₂ u hu).1) (fun u hu ↦ (hdisc₂ u hu).2) hlow₂ hz₂ hLz₂
    hS₂').1
  have hre : (1 / ((⟨σ, γ⟩ : ℂ) - ⟨β, γ⟩)).re = 1 / (σ - β) := by
    have : (⟨σ, γ⟩ : ℂ) - ⟨β, γ⟩ = ((σ - β : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hre] at hX₁
  rw [← hKdef] at hX₁ hX₂
  have hg1 : 1 ≤ |γ| ^ 2 := by linarith
  have hlogsq : Real.log (|γ| ^ 2) = 2 * Real.log |γ| := by
    rw [Real.log_pow]; norm_num
  have hB (C : ℝ) : Real.log (max (C * (|γ| ^ 2) ^ E / (1 / Z)) 2) ≤
      Real.log (max (C * Z) 2) + E * (2 * Real.log |γ|) := by
    rw [div_div_eq_mul_div, div_one, mul_right_comm, ← hlogsq]
    exact finiteHeckeL_zeroFreeRegion_log_le (C * Z) E (|γ| ^ 2) hE0 hg1
  have hB₁ := mul_le_mul_of_nonneg_left (hB C₁) hK.le
  have hB₂ := mul_le_mul_of_nonneg_left (hB C₂) hK.le
  rw [← hc₁] at hB₁
  rw [← hc₂] at hB₂
  have hlg0 : 0 ≤ Real.log |γ| := by linarith
  have hKE : 10 * K * (E * Real.log |γ|) ≤ 30 * K * (d * Real.log |γ|) := by
    have := mul_le_mul_of_nonneg_left hEd (by positivity : 0 ≤ 10 * K * Real.log |γ|)
    linarith
  have hdlg : Real.log |γ| ≤ d * Real.log |γ| := le_mul_of_one_le_left hlg0 hd1
  have hmain : 0 ≤ 3 / (σ - 1) - 4 / (σ - β) + M * Lg := by
    rw [hMdef, hLg]
    have e2 : K * (c₁ + E * (2 * Real.log |γ|)) = K * c₁ + 2 * (K * (E * Real.log |γ|)) := by
      ring
    have e3 : K * (c₂ + E * (2 * Real.log |γ|)) = K * c₂ + 2 * (K * (E * Real.log |γ|)) := by
      ring
    have e4 : (30 * K + 1) * (d * Real.log |γ|) = 30 * K * (d * Real.log |γ|) +
      d * Real.log |γ| := by ring
    have e5 : 10 * K * (E * Real.log |γ|) = 10 * (K * (E * Real.log |γ|)) := by ring
    have e6 : 3 / (σ - 1) - 4 / (σ - β) = 3 * (1 / (σ - 1)) + 4 * -(1 / (σ - β)) := by ring
    rw [e2] at hB₁
    rw [e3] at hB₂
    rw [e4, e6]
    rw [e5] at hKE
    have hCst' : Cst = 3 * C₀ + 4 * (K * c₁) + K * c₂ := by rw [hCst]; ring
    linarith only [h341, hX₀, hX₁, hX₂, hB₁, hB₂, hKE, hdlg, hlogC, hCst']
  exact finiteHeckeL_zeroFreeRegion_final M Lg σ β hM hLg0 hσ hβ hβ1 hmain

/-- Two continuations in normal form agreeing on `Re s > 1` are equal. -/
private theorem finiteHeckeL_zeroFreeRegion_unique {U V : ℂ → ℂ} (hU : MeromorphicNFOn U univ)
    (hV : MeromorphicNFOn V univ) (h : ∀ z : ℂ, 1 < z.re → U z = V z) : U = V := by
  let b : ℂ := (2 : ℝ)
  have hb : ∀ᶠ z : ℂ in 𝓝 b, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num [b])
  have ho : meromorphicOrderAt (U - V) b = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((hb.filter_mono nhdsWithin_le_nhds).mono
      fun z hz ↦ sub_eq_zero.mpr (h z hz))
  funext z
  have hz := (hU.meromorphicOn.sub hV.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ b) (mem_univ z) ho
  exact (((hU (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hV (mem_univ z))).mp (eventuallyEq_iff_sub.mpr
      (meromorphicOrderAt_eq_top_iff.mp hz))).eq_of_nhds

/-- Below a fixed height, a strip to the left of `Re s = 1` is free of zeros. -/
private theorem finiteHeckeL_zeroFreeRegion_low (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, |s.im| ≤ T → 1 - δ ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  have hnear (x : ℂ) (hx : meromorphicOrderAt L x ≤ 0) :
      ∀ᶠ w in 𝓝 x, meromorphicOrderAt L w ≤ 0 := by
    have hM := (hL (mem_univ x)).meromorphicAt
    have hne := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hM).mp
      (ne_top_of_le_ne_top (by simp) hx)
    have hev : ∀ᶠ w in 𝓝[≠] x, meromorphicOrderAt L w ≤ 0 := by
      filter_upwards [hne, hM.eventually_analyticAt] with w hw han
      exact ((hL (mem_univ w)).meromorphicOrderAt_eq_zero_iff.mpr hw).le
    filter_upwards [eventually_nhdsWithin_iff.mp hev] with w hw
    by_cases hwx : w = x
    · rw [hwx]; exact hx
    · exact hw hwx
  let K := (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) '' Icc (-T) T
  have hc : Continuous (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) := by
    have : (fun τ : ℝ ↦ (⟨1, τ⟩ : ℂ)) = fun τ : ℝ ↦ (1 : ℂ) + (τ : ℂ) * Complex.I := by
      funext τ
      apply Complex.ext <;> simp
    rw [this]
    fun_prop
  have hK : IsCompact K := isCompact_Icc.image hc
  have hKt : K ⊆ {w | ∀ᶠ z in 𝓝 w, meromorphicOrderAt L z ≤ 0} := by
    rintro _ ⟨τ, -, rfl⟩
    exact hnear _ (finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries _ le_rfl)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open isOpen_setOfPred_eventually_nhds hKt
  refine ⟨δ / 2, half_pos hδ, fun s hs hre ↦ ?_⟩
  by_cases h1 : 1 ≤ s.re
  · exact finiteHeckeL_zeroFreeRegion_order_nonpos F χ L hL hSeries s h1
  rw [not_le] at h1
  have hmem : s ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨⟨1, s.im⟩, ⟨s.im, abs_le.mp hs, rfl⟩, ?_⟩
    rw [Complex.dist_eq]
    have : s - ⟨1, s.im⟩ = ((s.re - 1 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact (hsub hmem).self_of_nhds

/-- Paper: Proposition B.6.1.1, p. 636. An absolute constant gives a
zero-free region for each finite Hecke L-function, with a scale depending on
the field and character. Meromorphic order distinguishes poles from zeros.
Deviation: The scale is chosen greater than `1/3` so the logarithm in the
denominator is positive at every height. It is an existential scale and may be
enlarged to exclude an exceptional zero. The separate real-zero clause is false. -/
theorem finiteHeckeL_zeroFreeRegion :
    ∃ A : ℝ, 0 < A ∧
      ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
        ∃ B : ℝ, 1 / 3 < B ∧
          ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ →
            (∀ s : halfPlane, L s = finiteHeckeL χ s) →
            ∀ s : ℂ, 1 - A / ((Module.finrank ℚ F : ℝ) ^ 4 *
              Real.log (B * (|s.im| + 3))) ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  have hK : 0 < landauConstant (1 / 2) (3 / 4) (7 / 8) 1 :=
    landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)), by positivity,
    fun F _ _ χ ↦ ?_⟩
  set A := 1 / (15 * (30 * landauConstant (1 / 2) (3 / 4) (7 / 8) 1 + 1)) with hA
  have hA0 : 0 < A := by positivity
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  have hd4 : d ≤ d ^ 4 := by
    calc d = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ 4 := pow_le_pow_right₀ hd1 (by norm_num)
  obtain ⟨L₁, hL₁, hS₁⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨T₀, hT₀, hev⟩ := finiteHeckeL_zeroFreeRegion_eventual F χ L₁ hL₁ hS₁
  obtain ⟨δ, hδ, hlow⟩ := finiteHeckeL_zeroFreeRegion_low F χ L₁ hL₁ hS₁ T₀
  set B := max 1 (Real.exp (A / δ)) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  refine ⟨B, by linarith, fun L hL hSeries s hs ↦ ?_⟩
  have hLL : L = L₁ := finiteHeckeL_zeroFreeRegion_unique hL hL₁ fun z hz ↦ by
    rw [hSeries ⟨z, hz⟩, hS₁ ⟨z, hz⟩]
  subst hLL
  have hB3 : B ≤ B * (|s.im| + 3) := le_mul_of_one_le_right (by linarith) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (B * (|s.im| + 3)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  by_cases ht : |s.im| ≤ T₀
  · apply hlow s ht
    have hlogB : A / δ ≤ Real.log (B * (|s.im| + 3)) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact (le_max_right _ _).trans hB3
    have : A / (d ^ 4 * Real.log (B * (|s.im| + 3))) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hδ] at hlogB
      nlinarith
    linarith
  · rw [not_le] at ht
    by_contra hpos
    rw [not_le] at hpos
    have h := hev s ht.le hpos
    have hlogt : 0 < Real.log |s.im| := Real.log_pos (by linarith)
    have hle : d * Real.log |s.im| ≤ d ^ 4 * Real.log (B * (|s.im| + 3)) := by
      apply mul_le_mul hd4 _ hlogt.le (by positivity)
      exact Real.log_le_log (by linarith) (by nlinarith [abs_nonneg s.im])
    have : A / (d ^ 4 * Real.log (B * (|s.im| + 3))) ≤ A / (d * Real.log |s.im|) :=
      div_le_div_of_nonneg_left hA0.le (by positivity) hle
    rw [← hA] at h
    linarith

/-- Landau's lemma on a zero-free closed disc: the logarithmic derivative on the inner disc is
bounded by the Landau constant times the logarithm of the modulus ratio. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_landau (f : ℂ → ℂ) (c z : ℂ)
    (r' r R' R M m : ℝ) (hr' : 0 < r') (hr'r : r' < r) (hrR' : r < R') (hR'R : R' < R)
    (hf : ∀ u ∈ Metric.closedBall c R, AnalyticAt ℂ f u)
    (hne : ∀ u ∈ Metric.closedBall c R, f u ≠ 0)
    (hM : ∀ u ∈ Metric.closedBall c R, ‖f u‖ ≤ M) (hm : 0 < m) (hc : m ≤ ‖f c‖)
    (hz : z ∈ Metric.closedBall c r') :
    ‖logDeriv f z‖ ≤ landauConstant r' r R' R * Real.log (max (M / m) 2) := by
  have hR : 0 < R := by linarith
  have hcR : c ∈ Metric.closedBall c R := Metric.mem_closedBall_self hR.le
  have hzR : z ∈ Metric.closedBall c R :=
    Metric.closedBall_subset_closedBall (by linarith) hz
  have hB : 1 < max (M / m) 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c hcR)
  have hbound : ∀ u ∈ Metric.closedBall c R, ‖f u / f c‖ ≤ max (M / m) 2 := fun u hu ↦ by
    rw [norm_div]
    exact (div_le_div₀ hM0 (hM u hu) hm hc).trans (le_max_left _ _)
  have h := landau_norm_logDeriv_sub_le hB hr' hr'r hrR' hR'R hf (hne c hcR) hbound hz (hne z hzR)
  have hsum : ∑ᶠ ρ ∈ Metric.closedBall c r, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) = 0 := by
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro ρ hρ
    have hρR : ρ ∈ Metric.closedBall c R :=
      Metric.closedBall_subset_closedBall (by linarith) hρ
    have : analyticOrderAt f ρ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (hne ρ hρR))
    simp [analyticOrderNatAt, this]
  rwa [hsum, sub_zero] at h

/-- Mean value estimate: once the derivative of `η` is eventually below `ε`, `η` cannot drop by
more than `ε` times the distance. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_slack (η : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ η (Ici 0))
    (hderiv : Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t t' : ℝ, T ≤ t → t ≤ t' → η t - ε * (t' - t) ≤ η t' := by
  have hev : ∀ᶠ x in atTop, ‖derivWithin η (Ici 0) x‖ < ε := by
    have := (Metric.tendsto_nhds.mp hderiv) ε hε
    simpa [dist_zero_right] using this
  rw [eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨max T₀ 1, le_max_right _ _, fun t t' ht htt' ↦ ?_⟩
  have hT1 : (1 : ℝ) ≤ t := (le_max_right _ _).trans ht
  have hT0 : T₀ ≤ t := (le_max_left _ _).trans ht
  have hd : ∀ x ∈ Ici t, DifferentiableAt ℝ η x := fun x hx ↦
    hdiff.differentiableAt (Ici_mem_nhds (by linarith [mem_Ici.mp hx]))
  have hb : ∀ x ∈ Ici t, ‖deriv η x‖ ≤ ε := fun x hx ↦ by
    have hx' : (0 : ℝ) < x := by linarith [mem_Ici.mp hx]
    rw [← derivWithin_of_mem_nhds (Ici_mem_nhds hx')]
    exact (hT₀ x (hT0.trans (mem_Ici.mp hx))).le
  have := (convex_Ici t).norm_image_sub_le_of_norm_deriv_le hd hb (mem_Ici.mpr le_rfl) (mem_Ici.mpr htt')
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htt')] at this
  linarith [neg_abs_le (η t' - η t)]

/-- The canonical zero-free region of Proposition B.6.1.1 contains a region of width
`c₀ / log |t|` at large height, with `c₀` depending only on the field and the character. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_canonical (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ c₀ T : ℝ, 0 < c₀ ∧ 3 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1 - c₀ / Real.log |s.im| ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
  obtain ⟨A, hA, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hzf⟩ := hF F χ
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  refine ⟨A / (2 * d ^ 4), max 3 (B + 3), by positivity, le_max_left _ _, fun s hs hre ↦ ?_⟩
  apply hzf L hL hSeries s
  have ht3 : 3 ≤ |s.im| := (le_max_left _ _).trans hs
  have htB : B + 3 ≤ |s.im| := (le_max_right _ _).trans hs
  have hlogt : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hBpos : 0 < B := by linarith
  have hBt : 0 < B * (|s.im| + 3) := by positivity
  have hlog2 : Real.log (B * (|s.im| + 3)) ≤ 2 * Real.log |s.im| := by
    rw [show (2 : ℝ) * Real.log |s.im| = Real.log (|s.im| ^ 2) by rw [Real.log_pow]; norm_num]
    apply Real.log_le_log hBt
    nlinarith
  have hlogB : 0 < Real.log (B * (|s.im| + 3)) := Real.log_pos (by nlinarith)
  refine le_trans ?_ hre
  rw [div_div]
  have hmul := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ d ^ 4)
  exact sub_le_sub_left (div_le_div_of_nonneg_left hA.le (by positivity) (by linarith)) 1

/-- The trivial character twisted by the zeroth norm power is the constant one. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_twist_one (g : IdeleClassGroup (𝓞 F) F) :
    ideleClassNormTwist (1 : U[F]) 0 g = 1 := by
  change (1 : ℂ) * ((((ideleClassNorm F g : NNReal) : ℝ)) : ℂ) ^ (0 : ℂ) = 1
  simp

/-- The width `max (η t) (c₀ / log t)` is at most `1/2` and loses less than the factor `1 - θ`
over a displacement of its own size, for all large `t`. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_delta (η : ℝ → ℝ)
    (hmaps : MapsTo η (Ici 0) (Ioc 0 (1 / 2)))
    (hdiff : DifferentiableOn ℝ η (Ici 0)) (hanti : AntitoneOn η (Ici 0))
    (hderiv : Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0))
    (θ c₀ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (hc₀ : 0 < c₀) :
    ∃ T : ℝ, 3 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      0 < max (η t) (c₀ / Real.log t) ∧ max (η t) (c₀ / Real.log t) ≤ 1 / 2 ∧
      ∀ t' : ℝ, |t' - t| ≤ max (η t) (c₀ / Real.log t) →
        (1 - θ) * max (η t) (c₀ / Real.log t) < max (η t') (c₀ / Real.log t') := by
  obtain ⟨T₁, hT₁, hslack⟩ :=
    finiteHeckeL_logDeriv_isBigO_of_zeroFree_slack η hdiff hderiv (θ / 2) (by positivity)
  refine ⟨max (max 3 T₁) (max (Real.exp (2 * c₀)) (Real.exp (1 / θ))),
    (le_max_left 3 T₁).trans (le_max_left _ _), fun t ht ↦ ?_⟩
  have ht3 : 3 ≤ t := (le_max_left 3 T₁).trans ((le_max_left _ _).trans ht)
  have htT₁ : T₁ ≤ t := (le_max_right 3 T₁).trans ((le_max_left _ _).trans ht)
  have hlog2c : 2 * c₀ ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hlogθ : 1 / θ ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  obtain ⟨hη0, hη2⟩ := hmaps (mem_Ici.mpr (by linarith : (0 : ℝ) ≤ t))
  have hδ₁0 : 0 < c₀ / Real.log t := by positivity
  have hδ₁2 : c₀ / Real.log t ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogt]
    linarith
  have hδ0 : 0 < max (η t) (c₀ / Real.log t) := lt_max_of_lt_left hη0
  have hδ2 : max (η t) (c₀ / Real.log t) ≤ 1 / 2 := max_le hη2 hδ₁2
  refine ⟨hδ0, hδ2, fun t' ht' ↦ ?_⟩
  obtain ⟨ht'lo, ht'hi⟩ := abs_le.mp ht'
  have ht'0 : 0 < t' := by linarith
  have hlogt' : 0 < Real.log t' := Real.log_pos (by linarith)
  have hlog_le : Real.log t' ≤ Real.log t + 1 / 6 := by
    have h1 : Real.log t' - Real.log t = Real.log (t' / t) :=
      (Real.log_div ht'0.ne' (by linarith)).symm
    have h2 : Real.log (t' / t) ≤ t' / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : t' / t - 1 ≤ 1 / 6 := by
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hδ₁slack : (1 - θ / 2) * (c₀ / Real.log t) ≤ c₀ / Real.log t' := by
    rw [← mul_div_assoc, div_le_div_iff₀ hlogt hlogt']
    have hθlog : 1 ≤ θ * Real.log t := by
      rw [div_le_iff₀ hθ] at hlogθ
      linarith
    have : (1 - θ / 2) * Real.log t' ≤ Real.log t := by nlinarith
    nlinarith
  have hηslack : η t - θ / 2 * max (η t) (c₀ / Real.log t) ≤ η t' := by
    rcases le_total t' t with h | h
    · have := hanti (mem_Ici.mpr ht'0.le) (mem_Ici.mpr (by linarith)) h
      nlinarith
    · have := hslack t t' htT₁ h
      nlinarith
  rcases le_total (c₀ / Real.log t) (η t) with h | h
  · rw [max_eq_left h] at hηslack ⊢
    exact lt_max_of_lt_left (by nlinarith)
  · rw [max_eq_right h]
    exact lt_max_of_lt_right (by nlinarith)

/-- Comparison of the logarithmic-derivative series with the one of the trivial character at a
smaller real part: `‖L'/L(s)‖ ≤ -Re L₀'/L₀(σ₀)` for `1 < σ₀ ≤ Re s`. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_series (χ : U[F]) (L L₀ : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s)
    (s : ℂ) (σ₀ : ℝ) (hσ₀ : 1 < σ₀) (hs : σ₀ ≤ s.re) :
    ‖logDeriv L s‖ ≤ -(logDeriv L₀ σ₀).re := by
  classical
  have hs1 : 1 < s.re := hσ₀.trans_le hs
  have h₁ := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨s, hs1⟩).2.2
  have h₀ := (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) L₀ hL₀ hS₀
    ⟨(σ₀ : ℂ), show 1 < (σ₀ : ℂ).re by simpa using hσ₀⟩).2.2
  refine h₁.norm_le_of_bounded (Complex.hasSum_re h₀).neg fun I ↦ ?_
  obtain ⟨I, hI⟩ := I
  have hNpos : 0 < I.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hN1 : (1 : ℝ) ≤ I.absNorm := by exact_mod_cast hNpos
  have hΛ0 : 0 ≤ idealVonMangoldt I := by
    unfold idealVonMangoldt
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  have hone : heckeIdealVonMangoldt (ideleClassNormTwist (1 : U[F]) 0) I =
      (idealVonMangoldt I : ℂ) := by
    rw [heckeIdealVonMangoldt, heckeIdealValue_of_forall_eq_one _
      finiteHeckeL_logDeriv_isBigO_of_zeroFree_twist_one hI, one_mul]
  have hnormχ : ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ idealVonMangoldt I := by
    by_cases h : ∃ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, 0 < k ∧ I = v.asIdeal ^ k
    · obtain ⟨v, k, hk, rfl⟩ := h
      rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v hk, idealVonMangoldt_prime_pow v hk,
        norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
      split_ifs
      · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul]
      · simp [Real.log_natCast_nonneg]
    · simp [heckeIdealVonMangoldt, idealVonMangoldt, h]
  have hR : (((idealVonMangoldt I : ℝ) : ℂ) / (I.absNorm : ℂ) ^ (σ₀ : ℂ)).re =
      idealVonMangoldt I / (I.absNorm : ℝ) ^ σ₀ := by
    rw [show (I.absNorm : ℂ) = ((I.absNorm : ℝ) : ℂ) from (Complex.ofReal_natCast _).symm,
      ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNpos, hone, neg_div,
    Complex.neg_re, neg_neg, hR]
  exact div_le_div₀ hΛ0 hnormχ (Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _)
    (Real.rpow_le_rpow_of_exponent_le hN1 hs)

/-- The pointwise estimate behind Theorem B.6.1.3. At a point of large height in the region
`Re s ≥ 1 - α η |Im s|` the continuation is analytic and nonzero, and its logarithmic
derivative is bounded by a squared logarithm with a constant built from `α`, the polynomial
growth exponents, the canonical width `c₀` and the pole data of `L₀`, none of which depend on
`η`. The height thresholds are hypotheses. -/
private theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree_pointwise (χ : U[F]) (L L₀ : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hL₀ : MeromorphicNFOn L₀ univ) (hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL (1 : U[F]) s)
    (α θ : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) (hθ : θ = (1 - α) / 2)
    (η : ℝ → ℝ) (hmaps : MapsTo η (Ici 0) (Ioc 0 (1 / 2)))
    (hzero : ∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0)
    (n : ℕ) (T₁ : ℝ) (hup : ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 2 → T₁ ≤ |z.im| → ‖L z‖ ≤ |z.im| ^ n)
    (N : ℕ) (c₂ T₂ : ℝ) (hc₂ : 0 < c₂)
    (hlow : ∀ t : ℝ, T₂ ≤ |t| → L ⟨1, t⟩ ≠ 0 ∧ ‖(L ⟨1, t⟩)⁻¹‖ ≤ c₂ * |t| ^ N)
    (c₀ T₃ : ℝ) (hc₀ : 0 < c₀)
    (hcanon : ∀ s : ℂ, T₃ ≤ |s.im| → 1 - c₀ / Real.log |s.im| ≤ s.re →
      meromorphicOrderAt L s ≤ 0)
    (p : ℂ) (hp : ∀ s : ℂ, 0 < s.re → (-1 ≤ meromorphicOrderAt L s) ∧ (s ≠ p → AnalyticAt ℂ L s))
    (η₀ C₀ : ℝ) (hη₀ : 0 < η₀)
    (hzeta : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + η₀ → -(logDeriv L₀ σ).re ≤ 1 / (σ - 1) + C₀)
    (T₄ : ℝ) (hdelta : ∀ t : ℝ, T₄ ≤ t →
      0 < max (η t) (c₀ / Real.log t) ∧ max (η t) (c₀ / Real.log t) ≤ 1 / 2 ∧
      ∀ t' : ℝ, |t' - t| ≤ max (η t) (c₀ / Real.log t) →
        (1 - θ) * max (η t) (c₀ / Real.log t) < max (η t') (c₀ / Real.log t'))
    (s : ℂ) (hT₁ : T₁ + 1 ≤ |s.im|) (hT₂ : T₂ ≤ |s.im|) (hT₃ : T₃ + 1 ≤ |s.im|)
    (hT₄ : T₄ ≤ |s.im|) (hpim : |p.im| + 1 ≤ |s.im|) (hexp : Real.exp 1 ≤ |s.im|)
    (hc₂t : c₂ ≤ |s.im|) (h3 : 3 ≤ |s.im|) (hsre : 1 - α * η |s.im| ≤ s.re) :
    (AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
      ‖logDeriv L s‖ ≤ (landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) *
        ((2 * n + N + 1 : ℕ) : ℝ) / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀|) *
          (Real.log |s.im|) ^ 2 := by
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hαθ : α + θ = 1 - θ := by rw [hθ]; ring
  set K : ℝ := landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) with hK
  have hK0 : 0 < K := landauConstant_pos hα₀ (by linarith) (by linarith) (by linarith)
  set e : ℕ := 2 * n + N + 1 with he
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = |s.im| := ⟨_, rfl⟩
  rw [← hτ] at hT₁ hT₂ hT₃ hT₄ hpim hexp hc₂t h3 hsre ⊢
  have hτ0 : 0 < τ := by linarith
  have hlogτ : 1 ≤ Real.log τ := by
    rw [Real.le_log_iff_exp_le hτ0]
    exact hexp
  have hlogτ0 : 0 < Real.log τ := by linarith
  obtain ⟨hδ0, hδ2, hslack⟩ := hdelta τ hT₄
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = max (η τ) (c₀ / Real.log τ) := ⟨_, rfl⟩
  rw [← hδ] at hδ0 hδ2 hslack
  obtain ⟨hη0, hη2⟩ := hmaps (mem_Ici.mpr (hτ ▸ abs_nonneg s.im))
  have hηδ : η τ ≤ δ := hδ ▸ le_max_left _ _
  have hδ₁ : c₀ / Real.log τ ≤ δ := hδ ▸ le_max_right _ _
  have hc₀δ : c₀ ≤ δ * Real.log τ := by rwa [div_le_iff₀ hlogτ0] at hδ₁
  have hinvδ : δ⁻¹ ≤ Real.log τ / c₀ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hδ0 hc₀]
    linarith
  have hαη : 0 < (1 - α) * η τ := mul_pos (by linarith) hη0
  have hαη' : (1 - α) * η τ = η τ - α * η τ := by ring
  have hαη2 : α * η τ ≤ 1 * (1 / 2) := mul_le_mul hα₁.le hη2 hη0.le zero_le_one
  have hαηδ : α * η τ ≤ α * δ := mul_le_mul_of_nonneg_left hηδ hα₀.le
  have hθδ : 0 < θ * δ := mul_pos hθ0 hδ0
  have hord_s : meromorphicOrderAt L s ≤ 0 := hzero s (by rw [← hτ]; linarith)
  have hsp : s ≠ p := fun h ↦ by
    rw [hτ, h] at hpim
    linarith
  have han_s : AnalyticAt ℂ L s := (hp s (by linarith)).2 hsp
  have hne_s : L s ≠ 0 := (hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mp
    (le_antisymm hord_s han_s.meromorphicOrderAt_nonneg)
  refine ⟨⟨han_s, hne_s⟩, ?_⟩
  have hαθ1 : (α + θ) * δ ≤ δ := by
    rw [hαθ]
    linarith [show (1 - θ) * δ = δ - θ * δ by ring]
  have hdisc : ∀ u ∈ Metric.closedBall (⟨1, s.im⟩ : ℂ) ((α + θ) * δ),
      AnalyticAt ℂ L u ∧ L u ≠ 0 ∧ ‖L u‖ ≤ (τ + 1) ^ n := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    have hre := Complex.abs_re_le_norm (u - ⟨1, s.im⟩)
    have him := Complex.abs_im_le_norm (u - ⟨1, s.im⟩)
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    obtain ⟨hre₁, hre₂⟩ := abs_le.mp (hre.trans hu)
    have him' : |(|u.im|) - τ| ≤ δ := by
      rw [hτ]
      exact (abs_abs_sub_abs_le_abs_sub _ _).trans (him.trans (hu.trans hαθ1))
    obtain ⟨him₁, him₂⟩ := abs_le.mp him'
    have hure : 1 - (1 - θ) * δ ≤ u.re := by
      rw [← hαθ]
      linarith
    have hord : meromorphicOrderAt L u ≤ 0 := by
      rcases lt_max_iff.mp (hslack |u.im| him') with h | h
      · exact hzero u (by linarith)
      · exact hcanon u (by linarith) (by linarith)
    have hure0 : 0 < u.re := by linarith
    have hup_ne : u ≠ p := fun h ↦ by
      rw [h] at him₁
      linarith
    have han : AnalyticAt ℂ L u := (hp u hure0).2 hup_ne
    have hne : L u ≠ 0 := (hL (mem_univ u)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm hord han.meromorphicOrderAt_nonneg)
    refine ⟨han, hne, (hup u ⟨hure0.le, by linarith⟩ (by linarith)).trans ?_⟩
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) n
  obtain ⟨hcne, hcinv⟩ := hlow s.im (by rw [← hτ]; exact hT₂)
  rw [← hτ] at hcinv
  have hm : 1 / (c₂ * τ ^ N) ≤ ‖L ⟨1, s.im⟩‖ := by
    have hpos : 0 < ‖L ⟨1, s.im⟩‖ := norm_pos_iff.mpr hcne
    rw [norm_inv] at hcinv
    rw [one_div_le (by positivity) hpos, one_div]
    exact hcinv
  have hlogB : Real.log (max ((τ + 1) ^ n / (1 / (c₂ * τ ^ N))) 2) ≤ e * Real.log τ := by
    rw [← Real.log_pow]
    apply Real.log_le_log (lt_max_of_lt_right two_pos)
    have hτ2 : τ + 1 ≤ τ ^ 2 := by nlinarith
    have h1 : (τ + 1) ^ n * (c₂ * τ ^ N) ≤ τ ^ e := by
      calc (τ + 1) ^ n * (c₂ * τ ^ N) ≤ (τ ^ 2) ^ n * (τ * τ ^ N) := by gcongr
        _ = τ ^ e := by rw [he]; ring
    apply max_le
    · rwa [div_div_eq_mul_div, div_one]
    · calc (2 : ℝ) ≤ τ := by linarith
        _ = τ ^ 1 := (pow_one τ).symm
        _ ≤ τ ^ e := pow_le_pow_right₀ (by linarith) (by omega)
  have hlog2 : 0 ≤ (Real.log τ) ^ 2 := sq_nonneg _
  have hCrest : 0 ≤ 1 / (α * c₀) + 1 / η₀ + |C₀| := by positivity
  rcases le_or_gt s.re (1 + α * δ) with hcase | hcase
  · have hz : s ∈ Metric.closedBall (⟨1, s.im⟩ : ℂ) (α * δ) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : s - ⟨1, s.im⟩ = ((s.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have h := finiteHeckeL_logDeriv_isBigO_of_zeroFree_landau L ⟨1, s.im⟩ s (α * δ)
      ((α + θ / 3) * δ) ((α + 2 * θ / 3) * δ) ((α + θ) * δ) ((τ + 1) ^ n) (1 / (c₂ * τ ^ N))
      (by positivity) (mul_lt_mul_of_pos_right (by linarith) hδ0)
      (mul_lt_mul_of_pos_right (by linarith) hδ0) (mul_lt_mul_of_pos_right (by linarith) hδ0)
      (fun u hu ↦ (hdisc u hu).1) (fun u hu ↦ (hdisc u hu).2.1) (fun u hu ↦ (hdisc u hu).2.2)
      (by positivity) hm hz
    have hKδ : landauConstant (α * δ) ((α + θ / 3) * δ) ((α + 2 * θ / 3) * δ) ((α + θ) * δ) =
        δ⁻¹ * K := by
      have := landauConstant_div (r' := α) (r := α + θ / 3) (R' := α + 2 * θ / 3) (R := α + θ)
        (s := δ⁻¹) (inv_pos.mpr hδ0) (by linarith) (by linarith) (by linarith)
      simpa only [div_inv_eq_mul] using this
    rw [hKδ] at h
    calc ‖logDeriv L s‖ ≤ δ⁻¹ * K * (e * Real.log τ) :=
          h.trans (mul_le_mul_of_nonneg_left hlogB (by positivity))
      _ ≤ (Real.log τ / c₀) * K * (e * Real.log τ) := by gcongr
      _ = K * e / c₀ * (Real.log τ) ^ 2 := by ring
      _ ≤ (K * e / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀|) * (Real.log τ) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hlog2
        linarith
  · have hmin0 : 0 < min (α * δ) η₀ := lt_min (mul_pos hα₀ hδ0) hη₀
    have hσ₀ : 1 < 1 + min (α * δ) η₀ := by linarith
    have hσs : 1 + min (α * δ) η₀ ≤ s.re := by linarith [min_le_left (α * δ) η₀]
    have h := finiteHeckeL_logDeriv_isBigO_of_zeroFree_series χ L L₀ hL hSeries hL₀ hS₀ s _
      hσ₀ hσs
    have hz := hzeta (1 + min (α * δ) η₀) hσ₀ (by linarith [min_le_right (α * δ) η₀])
    have hmin : 1 / (1 + min (α * δ) η₀ - 1) ≤ 1 / (α * δ) + 1 / η₀ := by
      rw [add_sub_cancel_left]
      have h1 : 0 < 1 / (α * δ) := by positivity
      have h2 : 0 < 1 / η₀ := by positivity
      rcases min_choice (α * δ) η₀ with hm | hm <;> rw [hm] <;> linarith
    have h1 : 1 / (α * δ) ≤ 1 / (α * c₀) * Real.log τ := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hc₀δ hα₀.le
      linarith [show Real.log τ * (α * δ) = α * (δ * Real.log τ) by ring]
    have h1sq : 1 ≤ (Real.log τ) ^ 2 := one_le_pow₀ hlogτ
    have hsq : Real.log τ ≤ (Real.log τ) ^ 2 := le_self_pow₀ hlogτ two_ne_zero
    have hA : 1 / (α * c₀) * Real.log τ ≤ 1 / (α * c₀) * (Real.log τ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have hB : 1 / η₀ ≤ 1 / η₀ * (Real.log τ) ^ 2 := le_mul_of_one_le_right (by positivity) h1sq
    have hC : |C₀| ≤ |C₀| * (Real.log τ) ^ 2 := le_mul_of_one_le_right (abs_nonneg _) h1sq
    have hD : 0 ≤ K * e / c₀ * (Real.log τ) ^ 2 := by positivity
    have hexpand : (K * e / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀|) * (Real.log τ) ^ 2 =
        K * e / c₀ * (Real.log τ) ^ 2 + 1 / (α * c₀) * (Real.log τ) ^ 2 +
          1 / η₀ * (Real.log τ) ^ 2 + |C₀| * (Real.log τ) ^ 2 := by ring
    calc ‖logDeriv L s‖ ≤ 1 / (1 + min (α * δ) η₀ - 1) + C₀ := h.trans hz
      _ ≤ 1 / (α * c₀) * Real.log τ + 1 / η₀ + |C₀| := by linarith [le_abs_self C₀]
      _ ≤ (K * e / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀|) * (Real.log τ) ^ 2 := by
        rw [hexpand]
        linarith

/-- Paper: Theorem B.6.1.3, p. 637. The logarithmic derivative is bounded by
a squared logarithm for large absolute heights, uniformly over the narrower
region defined by `α * η`. The Dedekind zeta continuation is the one for the
trivial character. For fixed field, character and `α`, the implied constant
works for every admissible width. Its height threshold may depend on the width.
Deviation: The width is represented by a real function restricted to `t ≥ 0`.
Decreasing is expressed as nonincreasing, and the logarithm uses absolute height.
Eventual analyticity and nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_of_zeroFree (χ : U[F]) (L Z : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hZ : MeromorphicNFOn Z univ) (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hα : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ → ℝ,
      MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
      DifferentiableOn ℝ η (Ici 0) → AntitoneOn η (Ici 0) →
      Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0) →
      ((fun t ↦ (η t)⁻¹) =O[atTop] Real.log) →
      (∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0) →
      let l := atHeight ⊓ 𝓟 {s : ℂ | 1 - α * η |s.im| ≤ s.re}
      (∀ᶠ s in l, AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
        Asymptotics.IsBigOWith C l (logDeriv L) (fun s ↦ (Real.log |s.im|) ^ 2) := by
  obtain ⟨L₀, hL₀, hS₀⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  obtain ⟨η₀, C₀, hη₀, hzeta⟩ := finiteHeckeL_zeroFreeRegion_zeta F L₀ hL₀ hS₀
  obtain ⟨c₀, T₃, hc₀, hT₃, hcanon⟩ :=
    finiteHeckeL_logDeriv_isBigO_of_zeroFree_canonical χ L hL hSeries
  obtain ⟨M₁, -, hM₁⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries 0 2 (by norm_num)
  obtain ⟨n, T₁, hup⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat L 0 2 M₁ hM₁
  obtain ⟨hev₁, N, -, hinv⟩ := finiteHeckeL_inv_isBigO_oneLine χ L hL hSeries
  obtain ⟨c₂, T₂, hc₂, hlow⟩ : ∃ c₂ T₂ : ℝ, 0 < c₂ ∧ ∀ t : ℝ, T₂ ≤ |t| →
      L ⟨1, t⟩ ≠ 0 ∧ ‖(L ⟨1, t⟩)⁻¹‖ ≤ c₂ * |t| ^ N := by
    obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hinv
    have hboth := hev₁.and hc
    simp only [eventually_comap, eventually_atTop] at hboth
    obtain ⟨T₂, hT₂⟩ := hboth
    refine ⟨max c 1, T₂, by positivity, fun t ht ↦ ?_⟩
    obtain ⟨⟨-, hne⟩, hb⟩ := hT₂ |t| ht t rfl
    refine ⟨hne, hb.trans ?_⟩
    rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) _)
  obtain ⟨p, hp⟩ := finiteHeckeL_zeroFreeRegion_poles F χ L hL hSeries
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 - α) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; linarith
  have hK0 : 0 < landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) :=
    landauConstant_pos hα₀ (by linarith) (by linarith) (by linarith)
  have hC : 0 < landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) *
      ((2 * n + N + 1 : ℕ) : ℝ) / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀| := by
    have h1 : 0 < landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) *
        ((2 * n + N + 1 : ℕ) : ℝ) / c₀ := div_pos (mul_pos hK0 (by positivity)) hc₀
    linarith [abs_nonneg C₀, one_div_pos.mpr (mul_pos hα₀ hc₀), one_div_pos.mpr hη₀]
  refine ⟨_, hC, fun η hmaps hdiff hanti hderiv _ hzero ↦ ?_⟩
  obtain ⟨T₄, hT₄, hdelta⟩ :=
    finiteHeckeL_logDeriv_isBigO_of_zeroFree_delta η hmaps hdiff hanti hderiv θ c₀ hθ0 hθ1 hc₀
  have hev : ∀ᶠ s : ℂ in atHeight ⊓ 𝓟 {s : ℂ | 1 - α * η |s.im| ≤ s.re},
      max (max (max (T₁ + 1) T₂) (max (T₃ + 1) T₄))
        (max (max (|p.im| + 1) (Real.exp 1)) (max c₂ 3)) ≤ |s.im| ∧
        1 - α * η |s.im| ≤ s.re := by
    rw [eventually_inf_principal]
    filter_upwards [(tendsto_comap (f := abs ∘ Complex.im)).eventually_ge_atTop
      (max (max (max (T₁ + 1) T₂) (max (T₃ + 1) T₄))
        (max (max (|p.im| + 1) (Real.exp 1)) (max c₂ 3)))] with s hs hs'
    exact ⟨hs, hs'⟩
  have key : ∀ s : ℂ, max (max (max (T₁ + 1) T₂) (max (T₃ + 1) T₄))
        (max (max (|p.im| + 1) (Real.exp 1)) (max c₂ 3)) ≤ |s.im| → 1 - α * η |s.im| ≤ s.re →
      (AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
        ‖logDeriv L s‖ ≤ (landauConstant α (α + θ / 3) (α + 2 * θ / 3) (α + θ) *
          ((2 * n + N + 1 : ℕ) : ℝ) / c₀ + 1 / (α * c₀) + 1 / η₀ + |C₀|) *
            (Real.log |s.im|) ^ 2 := fun s hsT hsre ↦
    finiteHeckeL_logDeriv_isBigO_of_zeroFree_pointwise χ L L₀ hL hSeries hL₀ hS₀ α θ hα₀ hα₁ hθ
      η hmaps hzero n T₁ hup N c₂ T₂ hc₂ hlow c₀ T₃ hc₀ hcanon p hp η₀ C₀ hη₀ hzeta T₄ hdelta s
      ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hsT)))
      ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hsT)))
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hsT)))
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hsT)))
      ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hsT)))
      ((le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hsT)))
      ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hsT)))
      ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hsT))) hsre
  refine ⟨hev.mono fun s hs ↦ (key s hs.1 hs.2).1, ?_⟩
  rw [Asymptotics.isBigOWith_iff]
  refine hev.mono fun s hs ↦ ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (key s hs.1 hs.2).2

/-- On the half-plane of absolute convergence the finite L-function of the trivial character is
the Dedekind zeta function. -/
private theorem finiteHeckeL_logDeriv_isBigO_oneLine_zeta (s : halfPlane) :
    finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- An explicit admissible width `A / (d⁴ log (B' (t + 3)))` with `B' ≥ B` large enough that the
width is at most `1/2`: positive, differentiable, nonincreasing, derivative tending to zero,
reciprocal `O(log t)`, and below the canonical width `A / (d⁴ log (B (t + 3)))`. -/
private theorem finiteHeckeL_logDeriv_isBigO_oneLine_width (A B d : ℝ) (hA : 0 < A)
    (hB : 1 / 3 < B) (hd : 1 ≤ d) :
    ∃ η : ℝ → ℝ, MapsTo η (Ici 0) (Ioc 0 (1 / 2)) ∧ DifferentiableOn ℝ η (Ici 0) ∧
      AntitoneOn η (Ici 0) ∧ Tendsto (derivWithin η (Ici 0)) atTop (𝓝 0) ∧
      ((fun t ↦ (η t)⁻¹) =O[atTop] Real.log) ∧
      ∀ t : ℝ, 0 ≤ t → η t ≤ A / (d ^ 4 * Real.log (B * (t + 3))) := by
  obtain ⟨B', hB'⟩ : ∃ B' : ℝ, B' = max (max B (Real.exp (2 * A / d ^ 4))) (Real.exp 1) :=
    ⟨_, rfl⟩
  have hB'B : B ≤ B' := hB' ▸ (le_max_left _ _).trans (le_max_left _ _)
  have hB'e : Real.exp (2 * A / d ^ 4) ≤ B' := hB' ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hB'1' : Real.exp 1 ≤ B' := hB' ▸ le_max_right _ _
  have hB'1 : 1 ≤ B' := (Real.one_le_exp zero_le_one).trans hB'1'
  have hB'0 : 0 < B' := by linarith
  have hB0 : 0 < B := by linarith
  have hd0 : 0 < d := by linarith
  have hd4 : 1 ≤ d ^ 4 := one_le_pow₀ hd
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t ↦ d ^ 4 * Real.log (B' * (t + 3)) := ⟨_, rfl⟩
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < B' * (t + 3) := fun t ht ↦ by positivity
  have hlog1 : ∀ t : ℝ, 0 ≤ t → 1 ≤ Real.log (B' * (t + 3)) := fun t ht ↦ by
    rw [Real.le_log_iff_exp_le (hpos t ht)]
    exact hB'1'.trans (le_mul_of_one_le_right hB'0.le (by linarith))
  have hlog2 : ∀ t : ℝ, 0 ≤ t → 2 * A / d ^ 4 ≤ Real.log (B' * (t + 3)) := fun t ht ↦ by
    rw [Real.le_log_iff_exp_le (hpos t ht)]
    calc Real.exp (2 * A / d ^ 4) ≤ B' := hB'e
      _ ≤ B' * (t + 3) := le_mul_of_one_le_right hB'0.le (by linarith)
  have hgval : ∀ t : ℝ, g t = d ^ 4 * Real.log (B' * (t + 3)) := fun t ↦ by rw [hg]
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 < g t := fun t ht ↦ by
    rw [hgval]
    exact mul_pos (by positivity) (by linarith [hlog1 t ht])
  have hgd : ∀ t : ℝ, 0 ≤ t → HasDerivAt g (d ^ 4 * (B' / (B' * (t + 3)))) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun t : ℝ ↦ B' * (t + 3)) (B' * 1) t :=
      ((hasDerivAt_id t).add_const 3).const_mul B'
    rw [mul_one] at h1
    rw [hg]
    exact (h1.log (hpos t ht).ne').const_mul _
  have hηd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t ↦ A / g t)
      (A * (-(d ^ 4 * (B' / (B' * (t + 3)))) / g t ^ 2)) t := fun t ht ↦ by
    have := ((hgd t ht).inv (hg0 t ht).ne').const_mul A
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
    simp [div_eq_mul_inv]
  refine ⟨fun t ↦ A / g t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht : 0 ≤ t := ht
    refine ⟨div_pos hA (hg0 t ht), ?_⟩
    rw [div_le_iff₀ (hg0 t ht), hgval]
    have := hlog2 t ht
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  · exact fun t ht ↦ (hηd t ht).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    have ha : 0 ≤ a := ha
    have hb : 0 ≤ b := hb
    apply div_le_div_of_nonneg_left hA.le (hg0 a ha)
    rw [hgval, hgval]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (hpos a ha) (by nlinarith)) (by positivity)
  · have hbound : ∀ᶠ t : ℝ in atTop, ‖derivWithin (fun t ↦ A / g t) (Ici 0) t‖ ≤ A / (t + 3) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht), (hηd t ht.le).deriv]
      have hBt : B' / (B' * (t + 3)) = 1 / (t + 3) := by
        field_simp
      have hL := hlog1 t ht.le
      have hgt : d ^ 4 ≤ g t ^ 2 := by
        rw [hgval]
        have h1 : d ^ 4 ≤ (d ^ 4) ^ 2 := le_self_pow₀ hd4 two_ne_zero
        have h2 : (d ^ 4) ^ 2 ≤ (d ^ 4 * Real.log (B' * (t + 3))) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact le_mul_of_one_le_right (by positivity) hL
        linarith
      have hval : A * (-(d ^ 4 * (1 / (t + 3))) / g t ^ 2) = -(A * d ^ 4 / (t + 3) / g t ^ 2) := by
        ring
      have hgt0 : 0 < g t ^ 2 := pow_pos (hg0 t ht.le) 2
      have ht3 : 0 < t + 3 := by linarith
      rw [hBt, hval, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), div_div,
        div_le_div_iff₀ (mul_pos ht3 hgt0) ht3]
      have := mul_le_mul_of_nonneg_left hgt (by positivity : (0 : ℝ) ≤ A * (t + 3))
      nlinarith
    exact squeeze_zero_norm' hbound
      (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id))
  · apply Asymptotics.IsBigO.of_bound (2 * d ^ 4 / A)
    filter_upwards [eventually_ge_atTop (max 3 (B' + 3))] with t ht
    have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
    have htB : B' + 3 ≤ t := (le_max_right _ _).trans ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hgt0 : 0 < g t := hg0 t (by linarith)
    rw [inv_div, Real.norm_of_nonneg (div_pos hgt0 hA).le, Real.norm_of_nonneg hlogt.le,
      div_le_iff₀ hA, hgval]
    have hlog : Real.log (B' * (t + 3)) ≤ 2 * Real.log t := by
      rw [show (2 : ℝ) * Real.log t = Real.log (t ^ 2) by rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      nlinarith
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ d ^ 4)
    have hA' : 2 * d ^ 4 / A * Real.log t * A = d ^ 4 * (2 * Real.log t) := by
      field_simp
    linarith
  · intro t ht
    have hBt : 0 < B * (t + 3) := by positivity
    have hlogB : 0 < Real.log (B * (t + 3)) := Real.log_pos (by nlinarith)
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    rw [hgval]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hBt (by nlinarith)) (by positivity)

/-- Paper: Corollary B.6.1.5, p. 639. On the line `Re(s) = 1`, the logarithmic
derivative is bounded by a squared logarithm as the absolute height grows.
Deviation: The logarithm uses absolute height. Eventual analyticity and
nonvanishing make the logarithmic derivative well-defined. -/
theorem finiteHeckeL_logDeriv_isBigO_oneLine (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    (∀ᶠ t : ℝ in atAbsTop, AnalyticAt ℂ L ⟨1, t⟩ ∧ L ⟨1, t⟩ ≠ 0) ∧
      (fun t : ℝ ↦ logDeriv L ⟨1, t⟩) =O[atAbsTop] (fun t ↦ (Real.log |t|) ^ 2) := by
  obtain ⟨Z, hZ, hZS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s := fun s ↦ by
    rw [hZS s, finiteHeckeL_logDeriv_isBigO_oneLine_zeta]
  obtain ⟨A, hA, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B₁, hB₁, hzf₁⟩ := hF F (1 : U[F])
  obtain ⟨B, hB, hzf⟩ := hF F χ
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Module.finrank ℚ F : ℝ) := ⟨_, rfl⟩
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact_mod_cast Module.finrank_pos
  rw [← hd] at hzf₁ hzf
  have hB₁0 : 0 < B₁ := by linarith
  have h4B : 1 < 4 * B₁ := by linarith
  obtain ⟨α₀, hα₀def⟩ : ∃ α₀ : ℝ, α₀ = A / (d ^ 4 * Real.log (4 * B₁)) := ⟨_, rfl⟩
  have hα₀ : 0 < α₀ := hα₀def ▸ div_pos hA (mul_pos (by positivity) (Real.log_pos h4B))
  have hα0 : 0 < min α₀ (1 / 2) := lt_min hα₀ (by norm_num)
  have hα1 : min α₀ (1 / 2) < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hα : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < min α₀ (1 / 2) → meromorphicOrderAt Z z ≤ 0 :=
    fun z _ hz ↦ by
    apply hzf₁ Z hZ hZS z
    have hre := Complex.abs_re_le_norm (z - 1)
    have him := Complex.abs_im_le_norm (z - 1)
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at hre him
    have hz₀ : ‖z - 1‖ < α₀ := hz.trans_le (min_le_left _ _)
    have hz₂ : ‖z - 1‖ < 1 / 2 := hz.trans_le (min_le_right _ _)
    have him1 : |z.im| ≤ 1 := by linarith
    have hlog : Real.log (B₁ * (|z.im| + 3)) ≤ Real.log (4 * B₁) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hlogpos : 0 < Real.log (B₁ * (|z.im| + 3)) := Real.log_pos (by nlinarith [abs_nonneg z.im])
    have : α₀ ≤ A / (d ^ 4 * Real.log (B₁ * (|z.im| + 3))) := by
      rw [hα₀def]
      exact div_le_div_of_nonneg_left hA.le (by positivity)
        (mul_le_mul_of_nonneg_left hlog (by positivity))
    linarith [(abs_le.mp (hre.trans hz₀.le)).1]
  obtain ⟨η, hmaps, hdiff, hanti, hderiv, hO, hle⟩ :=
    finiteHeckeL_logDeriv_isBigO_oneLine_width A B d hA hB hd1
  have hzero : ∀ s : ℂ, 1 - η |s.im| < s.re → meromorphicOrderAt L s ≤ 0 := fun s hs ↦
    hzf L hL hSeries s (by linarith [hle |s.im| (abs_nonneg _)])
  obtain ⟨C, -, hmain⟩ := finiteHeckeL_logDeriv_isBigO_of_zeroFree χ L Z hL hSeries hZ hZSeries
    (min α₀ (1 / 2)) hα0 hα1 hα
  obtain ⟨hev, hbig⟩ := hmain η hmaps hdiff hanti hderiv hO hzero
  have hmap : Tendsto (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) atAbsTop
      (atHeight ⊓ 𝓟 {s : ℂ | 1 - min α₀ (1 / 2) * η |s.im| ≤ s.re}) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr (Eventually.of_forall fun t ↦ ?_)⟩
    · rw [tendsto_comap_iff]
      exact tendsto_comap
    · show 1 - min α₀ (1 / 2) * η |t| ≤ 1
      have := (hmaps (mem_Ici.mpr (abs_nonneg t))).1
      nlinarith
  exact ⟨hmap.eventually hev, hbig.isBigO.comp_tendsto hmap⟩

-- TODO(paper-gap): The paragraph after (B.6.1.1) identifies two different conductors.
-- A pure imaginary norm twist preserves the finite conductor but changes the
-- archimedean parameter. No conductor-uniform exceptional-zero assertion is made here.
-- TODO(paper-gap): The real-zero clause of Proposition B.6.1.1 is false on [1/2, 1].
-- If ζ(1/2 + iγ) = 0 with γ ≠ 0, the nonquadratic norm character |·|^(iγ)
-- over ℚ has finite L-function ζ(s + iγ), which vanishes at the real point 1/2.
-- The square of this character has finite L-function ζ(s + 2iγ), with a pole.

-- Helpers for `finiteHeckeL_outside_horizontal_lower_bound_off_small_set` (Theorem B.6.1.7).
-- The Euler product outside `S`, times a polynomial clearing the finitely many poles, is entire;
-- Patel's disk factorization (External/Grh) at `3/2 + i(T + 1/2)` bounds its zero count and the
-- zero-free quotient, and Markov's inequality for the logarithmic losses of the zero ordinates
-- gives the exceptional set, enlarged to measure exactly `1 / B`.

/-- The continuation has finitely many poles, all of order at most one. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_poles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ Z : Finset ℂ, (∀ s ∉ Z, AnalyticAt ℂ L s) ∧ ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt L s := by
  classical
  obtain ⟨Λ, hΛ, hΛSeries⟩ := completedHeckeL_exists_continuation χ
  let R (s : ℂ) := (heckeGammaFactor χ s)⁻¹
  let H := Λ * R
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun s hs ↦
    (hΛ hs).meromorphicAt.mul (hR.analyticAt s).meromorphicAt
  have hAgree : ∀ s : halfPlane, (L - H) s = 0 := by
    intro s
    have hne := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans s.property)
    change L s - Λ s * (heckeGammaFactor χ s)⁻¹ = 0
    rw [hSeries s, hΛSeries s, completedHeckeL, finiteHeckeL]
    rw [mul_comm (heckeGammaFactor χ s), mul_assoc, mul_inv_cancel₀ hne, mul_one, sub_self]
  have hAtTwo : meromorphicOrderAt (L - H) (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun s hs ↦ hAgree ⟨s, hs⟩
  have hCompare (s : ℂ) : meromorphicOrderAt Λ s ≤ meromorphicOrderAt L s := by
    have ho := (hL.meromorphicOn.sub hH).meromorphicOrderAt_eq_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) hAtTwo
    have he : L =ᶠ[𝓝[≠] s] H := (meromorphicOrderAt_eq_top_iff.mp ho).mono fun z hz ↦
      sub_eq_zero.mp hz
    rw [meromorphicOrderAt_congr he,
      meromorphicOrderAt_mul (hΛ (mem_univ s)).meromorphicAt (hR.analyticAt s).meromorphicAt]
    exact le_add_of_nonneg_right (hR.analyticAt s).meromorphicOrderAt_nonneg
  have hNeg : (-1 : WithTop ℤ) ≤ 0 := by decide
  have hPoles : ∃ Z : Finset ℂ,
      (∀ s ∉ Z, AnalyticAt ℂ Λ s) ∧ ∀ s, (-1 : WithTop ℤ) ≤ meromorphicOrderAt Λ s := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨_, hp, hq, ha⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ Λ hΛ hΛSeries hχ
      refine ⟨{Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}, fun s hs ↦ ha s (by simpa using hs),
        fun s ↦ ?_⟩
      by_cases h : s = Complex.I * (t : ℂ)
      · rw [h, hp]
      by_cases h' : s = 1 + Complex.I * (t : ℂ)
      · rw [h', hq]
      exact hNeg.trans (ha s (by simp [h, h'])).meromorphicOrderAt_nonneg
    · have h := completedHeckeL_continuation_entire χ Λ hΛ hΛSeries hχ
      exact ⟨∅, fun s _ ↦ h.analyticAt s, fun s ↦
        hNeg.trans (h.analyticAt s).meromorphicOrderAt_nonneg⟩
  obtain ⟨Z, hAway, hLower⟩ := hPoles
  exact ⟨Z, fun s hs ↦ (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((hAway s hs).meromorphicOrderAt_nonneg.trans (hCompare s)),
    fun s ↦ (hLower s).trans (hCompare s)⟩


/-- Each reciprocal Euler factor is entire. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_eulerInv_differentiable (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) :
    Differentiable ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) := by
  intro s
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp only [inv_inv]
    have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
    exact (differentiableAt_const _).sub ((differentiableAt_const _).mul
      ((differentiableAt_id.neg).const_cpow (Or.inl hq)))
  · simp

/-- Size of a reciprocal Euler factor. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_eulerInv_norm (χ : U[F])
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    ‖(finiteHeckeEulerFactor χ v s)⁻¹‖ ≤ 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ∧
      1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ ‖(finiteHeckeEulerFactor χ v s)⁻¹‖ := by
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hr : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := Real.rpow_nonneg hq.le _
  unfold finiteHeckeEulerFactor
  split_ifs
  · rw [inv_inv]
    have hw : ‖(ideleClassNormTwist χ 0).localValue v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        show ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) : ℂ) by
          push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re]
    constructor
    · exact (norm_sub_le _ _).trans (by rw [norm_one, hw])
    · have := norm_sub_norm_le (1 : ℂ) ((ideleClassNormTwist χ 0).localValue v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      rw [norm_one, hw] at this
      exact this
  · simp only [inv_one, norm_one]
    constructor <;> linarith

/-- Clearing the poles of the Euler product outside `S` gives an entire function. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_entire (χ : U[F]) (L : ℂ → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ (f : ℂ → ℂ) (Z : Finset ℂ), AnalyticOnNhd ℂ f univ ∧
      ∀ s ∉ Z, f s = (∏ p ∈ Z, (s - p)) *
        ((∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s) := by
  classical
  obtain ⟨Z, hAway, hLower⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_poles χ L hL hSeries
  let Q : ℂ → ℂ := fun s ↦ ∏ p ∈ Z, (s - p)
  let P : ℂ → ℂ := fun s ↦ ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹
  let G : ℂ → ℂ := Q * (P * L)
  have hQ : Differentiable ℂ Q := by
    intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
  have hP : Differentiable ℂ P := by
    intro s
    exact DifferentiableAt.fun_finsetProd fun v _ ↦
      finiteHeckeL_outside_horizontal_lower_bound_off_small_set_eulerInv_differentiable χ v s
  have hG : MeromorphicOn G univ := fun s _ ↦
    (hQ.analyticAt s).meromorphicAt.mul
      ((hP.analyticAt s).meromorphicAt.mul (hL (mem_univ s)).meromorphicAt)
  have hGan (s : ℂ) (hs : s ∉ Z) : AnalyticAt ℂ G s :=
    (hQ.analyticAt s).mul ((hP.analyticAt s).mul (hAway s hs))
  refine ⟨toMeromorphicNFOn G univ, Z, fun x _ ↦ ?_, fun s hs ↦ ?_⟩
  · apply ((meromorphicNFOn_toMeromorphicNFOn G univ) (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hG (mem_univ x)]
    by_cases hx : x ∈ Z
    · let Q' : ℂ → ℂ := fun s ↦ ∏ p ∈ Z.erase x, (s - p)
      have hQ' : Differentiable ℂ Q' := by
        intro s; exact DifferentiableAt.fun_finsetProd fun p _ ↦ differentiableAt_id.sub_const p
      have hGeq : G = (fun s ↦ s - x) * (Q' * (P * L)) := by
        funext s
        simp only [G, Q, Q', Pi.mul_apply, ← mul_assoc]
        rw [Finset.mul_prod_erase Z (fun p ↦ s - p) hx]
      rw [hGeq, meromorphicOrderAt_mul (by fun_prop) ((hQ'.analyticAt x).meromorphicAt.mul
          ((hP.analyticAt x).meromorphicAt.mul (hL (mem_univ x)).meromorphicAt)),
        meromorphicOrderAt_id_sub_const,
        meromorphicOrderAt_mul (hQ'.analyticAt x).meromorphicAt
          ((hP.analyticAt x).meromorphicAt.mul (hL (mem_univ x)).meromorphicAt),
        meromorphicOrderAt_mul (hP.analyticAt x).meromorphicAt (hL (mem_univ x)).meromorphicAt]
      have h1 := (hQ'.analyticAt x).meromorphicOrderAt_nonneg
      have h2 := (hP.analyticAt x).meromorphicOrderAt_nonneg
      have h3 := hLower x
      have h4 : (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := by
        have := add_le_add_right h3 (1 : WithTop ℤ)
        exact le_of_eq_of_le (by rfl) this
      calc (0 : WithTop ℤ) ≤ 1 + meromorphicOrderAt L x := h4
        _ ≤ 1 + (meromorphicOrderAt Q' x + (meromorphicOrderAt P x + meromorphicOrderAt L x)) := by
          gcongr
          exact le_add_of_nonneg_left h1 |>.trans' (le_add_of_nonneg_left h2)
    · exact (hGan x hx).meromorphicOrderAt_nonneg
  · rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hG (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (hGan s hs).meromorphicNFAt]
    rfl


/-- Growth on the radius-6 circle about `3/2 + i(T + 1/2)`, size at its center, and the
factor relating the entire function to the Euler product outside `S` on the segments. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_local (χ : U[F]) (L : ℂ → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ (f : ℂ → ℂ) (C K δ T₀ : ℝ), AnalyticOnNhd ℂ f univ ∧ 1 ≤ C ∧ 0 ≤ K ∧ 0 < δ ∧ δ ≤ 1 ∧
      1 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
        (∀ z ∈ Metric.sphere (⟨3 / 2, T + 1 / 2⟩ : ℂ) 6, ‖f z‖ ≤ C * T ^ K) ∧
        δ ≤ ‖f ⟨3 / 2, T + 1 / 2⟩‖ ∧
        ∀ t ∈ Icc T (T + 1), ∀ σ ∈ Icc (-1 : ℝ) 2, ∃ q : ℂ, ‖q‖ ≤ C * T ^ K ∧
          f ⟨σ, t⟩ = q * ((∏ v ∈ S, (finiteHeckeEulerFactor χ v ⟨σ, t⟩)⁻¹) * L ⟨σ, t⟩) := by
  classical
  obtain ⟨f, Z, hf, hfeq⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_entire χ L S hL hSeries
  -- growth of `L`
  obtain ⟨M₀, hM₀, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (-5) 8
    (by norm_num)
  obtain ⟨C₀, hC₀, hC₀'⟩ := Asymptotics.isBigO_iff'.mp hO
  rw [eventually_inf_principal, eventually_comap, eventually_atTop] at hC₀'
  obtain ⟨T₁, hT₁⟩ := hC₀'
  have hLbd (z : ℂ) (hre : z.re ∈ Icc (-5 : ℝ) 8) (him : T₁ ≤ |z.im|) :
      ‖L z‖ ≤ C₀ * |z.im| ^ M₀ := by
    have h := hT₁ |z.im| him z rfl hre
    rwa [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
  -- constants
  set R : ℝ := ∑ p ∈ Z, ‖p‖ with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hpR (p : ℂ) (hp : p ∈ Z) : ‖p‖ ≤ R :=
    Finset.single_le_sum (f := fun p ↦ ‖p‖) (fun _ _ ↦ norm_nonneg _) hp
  let q (v : HeightOneSpectrum (𝓞 F)) : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
  have hq (v : HeightOneSpectrum (𝓞 F)) : 1 < q v := by
    show (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  set CP : ℝ := ∏ v ∈ S, (1 + q v ^ (5 : ℝ)) with hCP
  set δP : ℝ := ∏ v ∈ S, (1 - q v ^ (-(3 / 2 : ℝ))) with hδP
  have hCP1 : 1 ≤ CP := Finset.one_le_prod₀ fun v _ ↦
    le_add_of_nonneg_right (Real.rpow_nonneg (zero_lt_one.trans (hq v)).le _)
  have hδP0 : 0 < δP := Finset.prod_pos fun v _ ↦
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (hq v) (by norm_num))
  have hδP1 : δP ≤ 1 := Finset.prod_le_one₀ (fun v _ ↦
      sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (hq v).le (by norm_num)))
    fun v _ ↦ sub_le_self _ (Real.rpow_nonneg (zero_lt_one.trans (hq v)).le _)
  have hPup (z : ℂ) (hz : -5 ≤ z.re) :
      ‖∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹‖ ≤ CP := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro v _
    refine
      (finiteHeckeL_outside_horizontal_lower_bound_off_small_set_eulerInv_norm χ v z).1.trans ?_
    gcongr
    · exact (hq v).le
    · linarith
  have hPlow (z : ℂ) (hz : z.re = 3 / 2) :
      δP ≤ ‖∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹‖ := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro v _
      exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (hq v).le (by norm_num))
    · intro v _
      have := (finiteHeckeL_outside_horizontal_lower_bound_off_small_set_eulerInv_norm χ v z).2
      rw [hz] at this
      exact this
  -- the value of `L` at real part `3 / 2`
  set ζ : ℝ := ‖dedekindZeta F (3 / 2 : ℝ)‖ with hζ
  have hLlow (z : ℂ) (hz : z.re = 3 / 2) : 1 ≤ ‖L z‖ * ζ := by
    have hs : z ∈ halfPlane := show 1 < z.re by rw [hz]; norm_num
    rw [show L z = finiteHeckeL χ ⟨z, hs⟩ from hSeries ⟨z, hs⟩]
    exact (finiteHeckeL_zeroFreeRegion_euler F χ ⟨z, hs⟩ (y := 3 / 2) (by norm_num)
      (by rw [show ((⟨z, hs⟩ : halfPlane) : ℂ) = z from rfl, hz])).2
  have hζ0 : 0 < ζ := by
    have h := hLlow ⟨3 / 2, 0⟩ rfl
    rcases (norm_nonneg (dedekindZeta F (3 / 2 : ℝ))).lt_or_eq with h' | h'
    · exact h'
    · rw [← hζ] at h'; rw [← h', mul_zero] at h; norm_num at h
  -- the polynomial factor
  have hQlow (z : ℂ) (hz : R + 1 ≤ |z.im|) : z ∉ Z ∧ 1 ≤ ‖∏ p ∈ Z, (z - p)‖ := by
    have hzp (p : ℂ) (hp : p ∈ Z) : 1 ≤ ‖z - p‖ := by
      have h1 := Complex.abs_im_le_norm (z - p)
      have h2 := Complex.abs_im_le_norm p
      rw [Complex.sub_im] at h1
      have h3 := abs_sub_abs_le_abs_sub z.im p.im
      linarith [hpR p hp]
    refine ⟨fun hzZ ↦ ?_, ?_⟩
    · have := hzp z hzZ
      rw [sub_self, norm_zero] at this
      norm_num at this
    · rw [norm_prod]
      exact Finset.one_le_prod₀ fun p hp ↦ hzp p hp
  have hQup (z : ℂ) (X : ℝ) (hX : 1 ≤ X) (hre : |z.re| ≤ 8) (him : |z.im| ≤ X) :
      ‖∏ p ∈ Z, (z - p)‖ ≤ ((9 + R) * X) ^ Z.card := by
    rw [norm_prod, ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro p hp
    have h1 := norm_sub_le z p
    have h2 := Complex.norm_le_abs_re_add_abs_im z
    have h3 := hpR p hp
    nlinarith
  set n : ℕ := Z.card with hn
  set C₁ : ℝ := max C₀ 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  set K : ℝ := (n : ℝ) + M₀ with hK
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := (9 + R) ^ n * CP * C₁ * (2 : ℝ) ^ K with hC
  have h9R : 1 ≤ (9 + R) ^ n := one_le_pow₀ (by linarith)
  have hC1 : 1 ≤ C := by
    have h2K : 1 ≤ (2 : ℝ) ^ K := Real.one_le_rpow (by norm_num) hK0
    have := mul_le_mul h9R hCP1 zero_le_one (by positivity)
    have := mul_le_mul this hC₁1 zero_le_one (by positivity)
    have := mul_le_mul this h2K zero_le_one (by positivity)
    simpa [hC] using this
  set δ : ℝ := min 1 (δP / ζ) with hδ
  refine ⟨f, C, K, δ, max (max 7 (T₁ + 6)) (R + 7), hf, hC1, hK0,
    lt_min one_pos (div_pos hδP0 hζ0), min_le_left _ _,
    le_trans (by norm_num) ((le_max_left _ _).trans (le_max_left _ _)), fun T hT ↦ ?_⟩
  have hT7 : 7 ≤ T := le_trans (le_max_left _ _) ((le_max_left _ _).trans hT)
  have hT1 : T₁ + 6 ≤ T := le_trans (le_max_right _ _) ((le_max_left _ _).trans hT)
  have hTR : R + 7 ≤ T := (le_max_right _ _).trans hT
  have hCT : C * T ^ K = (9 + R) ^ n * CP * C₁ * (2 * T) ^ K := by
    rw [Real.mul_rpow (by norm_num) (by linarith), hC]; ring
  have h2T : (2 * T) ^ K = (2 * T) ^ n * (2 * T) ^ M₀ := by
    rw [hK, Real.rpow_add (by linarith), Real.rpow_natCast]
  refine ⟨fun z hz ↦ ?_, ?_, fun t ht σ hσ ↦ ?_⟩
  · rw [mem_sphere_iff_norm] at hz
    have hre := Complex.abs_re_le_norm (z - ⟨3 / 2, T + 1 / 2⟩)
    have him := Complex.abs_im_le_norm (z - ⟨3 / 2, T + 1 / 2⟩)
    rw [hz, Complex.sub_re] at hre
    rw [hz, Complex.sub_im] at him
    simp only at hre him
    obtain ⟨hre1, hre2⟩ := abs_le.mp hre
    obtain ⟨him1, him2⟩ := abs_le.mp him
    have hzim : |z.im| = z.im := abs_of_pos (by linarith)
    obtain ⟨hzZ, -⟩ := hQlow z (by rw [hzim]; linarith)
    rw [hfeq z hzZ, norm_mul, norm_mul]
    have hQ := hQup z (2 * T) (by linarith) (abs_le.mpr ⟨by linarith, by linarith⟩)
      (by rw [hzim]; linarith)
    have hP := hPup z (by linarith)
    have hLz := hLbd z ⟨by linarith, by linarith⟩ (by rw [hzim]; linarith)
    have hLz' : ‖L z‖ ≤ C₁ * (2 * T) ^ M₀ := by
      refine hLz.trans (mul_le_mul (le_max_left _ _) ?_ (by positivity) (by positivity))
      rw [hzim]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hM₀.le
    rw [hCT, h2T]
    calc ‖∏ p ∈ Z, (z - p)‖ * (‖∏ v ∈ S, (finiteHeckeEulerFactor χ v z)⁻¹‖ * ‖L z‖)
        ≤ ((9 + R) * (2 * T)) ^ n * (CP * (C₁ * (2 * T) ^ M₀)) := by
          gcongr
      _ = _ := by rw [mul_pow]; ring
  · have hc : (⟨3 / 2, T + 1 / 2⟩ : ℂ).im = T + 1 / 2 := rfl
    obtain ⟨hcZ, hQc⟩ := hQlow ⟨3 / 2, T + 1 / 2⟩ (by rw [hc, abs_of_pos (by linarith)]; linarith)
    rw [hfeq _ hcZ, norm_mul, norm_mul]
    have hP := hPlow ⟨3 / 2, T + 1 / 2⟩ rfl
    have hLc : 1 / ζ ≤ ‖L ⟨3 / 2, T + 1 / 2⟩‖ := by
      rw [div_le_iff₀ hζ0]; exact hLlow _ rfl
    calc δ ≤ δP / ζ := min_le_right _ _
      _ = 1 * (δP * (1 / ζ)) := by ring
      _ ≤ _ := by gcongr
  · have hzim : |(⟨σ, t⟩ : ℂ).im| = t := abs_of_pos (by simp only; linarith [ht.1])
    obtain ⟨hzZ, -⟩ := hQlow ⟨σ, t⟩ (by rw [hzim]; linarith [ht.1])
    refine ⟨∏ p ∈ Z, ((⟨σ, t⟩ : ℂ) - p), ?_, hfeq _ hzZ⟩
    have hQ := hQup ⟨σ, t⟩ (2 * T) (by linarith)
      (abs_le.mpr ⟨by simp only; linarith [hσ.1], by simp only; linarith [hσ.2]⟩)
      (by rw [hzim]; linarith [ht.2])
    refine hQ.trans ?_
    rw [hCT, mul_pow, h2T]
    have h1 : 1 ≤ (2 * T) ^ M₀ := Real.one_le_rpow (by linarith) hM₀.le
    have h2 : 1 ≤ CP * C₁ := one_le_mul_of_one_le_of_one_le hCP1 hC₁1
    have h3 : 0 ≤ (9 + R) ^ n * (2 * T) ^ n := by positivity
    calc (9 + R) ^ n * (2 * T) ^ n = ((9 + R) ^ n * (2 * T) ^ n) * 1 * 1 := by ring
      _ ≤ ((9 + R) ^ n * (2 * T) ^ n) * (CP * C₁) * (2 * T) ^ M₀ := by gcongr
      _ = _ := by ring

/-- A measurable subset of `[T, T + 1]` of measure at most `r ≤ 1` lies in one of measure `r`. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_enlarge
    {E₀ : Set ℝ} {T r : ℝ} (hE₀ : MeasurableSet E₀) (hsub : E₀ ⊆ Icc T (T + 1))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hvol : volume E₀ ≤ ENNReal.ofReal r) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E₀ ⊆ E ∧ E ⊆ Icc T (T + 1) ∧
      volume E = ENNReal.ofReal r := by
  let φ : ℝ → ℝ := fun u ↦ (volume (E₀ ∪ Icc T u)).toReal
  have hfin (u : ℝ) (hu : u ≤ T + 1) : volume (E₀ ∪ Icc T u) ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_Icc_lt_top (a := T) (b := T + 1)).ne
      (measure_mono (union_subset hsub (Icc_subset_Icc_right hu)))
  have hmono (u v : ℝ) (huv : u ≤ v) (hv : v ≤ T + 1) : φ u ≤ φ v ∧ φ v ≤ φ u + (v - u) := by
    have h1 : volume (E₀ ∪ Icc T u) ≤ volume (E₀ ∪ Icc T v) :=
      measure_mono (union_subset_union_right _ (Icc_subset_Icc_right huv))
    have h2 : volume (E₀ ∪ Icc T v) ≤ volume (E₀ ∪ Icc T u) + ENNReal.ofReal (v - u) := by
      calc volume (E₀ ∪ Icc T v) ≤ volume ((E₀ ∪ Icc T u) ∪ Ioc u v) := by
            apply measure_mono
            rintro x (hx | ⟨hx1, hx2⟩)
            · exact Or.inl (Or.inl hx)
            · rcases le_or_gt x u with h | h
              · exact Or.inl (Or.inr ⟨hx1, h⟩)
              · exact Or.inr ⟨h, hx2⟩
        _ ≤ _ := by rw [← Real.volume_Ioc]; exact measure_union_le _ _
    refine ⟨ENNReal.toReal_mono (hfin v hv) h1, ?_⟩
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin u (huv.trans hv), ENNReal.ofReal_ne_top⟩) h2
    rwa [ENNReal.toReal_add (hfin u (huv.trans hv)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at this
  have hcont : ContinuousOn φ (Icc T (T + 1)) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun u hu v hv ↦ ?_).continuousOn
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq]
    rcases le_total u v with h | h
    · have := hmono u v h hv.2
      rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have := hmono v u h hu.2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hT : φ T ≤ r := by
    have h : volume (E₀ ∪ Icc T T) ≤ volume E₀ := by
      rw [Icc_self]
      exact (measure_union_le _ _).trans (by simp)
    calc φ T ≤ (volume E₀).toReal :=
          ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol) h
      _ ≤ r := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
          rwa [ENNReal.toReal_ofReal hr0] at this
  have hT1 : r ≤ φ (T + 1) := by
    have : E₀ ∪ Icc T (T + 1) = Icc T (T + 1) := union_eq_right.mpr hsub
    simp only [φ, this, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one,
      ENNReal.toReal_one]
    exact hr1
  obtain ⟨u, hu, hφu⟩ := intermediate_value_Icc (by linarith) hcont ⟨hT, hT1⟩
  refine ⟨E₀ ∪ Icc T u, hE₀.union measurableSet_Icc, subset_union_left,
    union_subset hsub (Icc_subset_Icc_right hu.2), ?_⟩
  rw [← hφu, ENNReal.ofReal_toReal (hfin u hu.2)]


section LogLoss

/-- The logarithmic loss `max 0 (-log |x|)`. This definition and the three lemmas after it are
copied unchanged from `Proofs/Lemmas/LogLossGoodHeight.lean` of Neal Patel's `thatnealpatel/grh`
(MIT), where they are private; see `External/ATTRIBUTION.md`. -/
private noncomputable def logLoss (x : ℝ) : ℝ := max 0 (-Real.log |x|)

private theorem logLoss_nonneg (x : ℝ) : 0 ≤ logLoss x := le_max_left _ _

private theorem logLoss_integrable_and_integral :
    Integrable logLoss ∧ (∫ x, logLoss x) = 2 := by
  -- `Real.log_abs` holds also at zero, where Lean sets `Real.log 0 = 0`.
  have hcut : logLoss = (Icc (-1 : ℝ) 1).indicator (fun x ↦ -Real.log x) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · have hn := Real.log_nonpos (abs_nonneg x) (abs_le.mpr hx)
      rw [indicator_of_mem hx, logLoss, max_eq_right (neg_nonneg.mpr hn), Real.log_abs]
    · have hx' : 1 ≤ |x| := le_of_not_gt fun h ↦ hx ⟨(abs_lt.mp h).1.le, (abs_lt.mp h).2.le⟩
      rw [indicator_of_notMem hx, logLoss, max_eq_left (neg_nonpos.mpr (Real.log_nonneg hx'))]
  rw [hcut]
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hlog : IntervalIntegrable (fun x ↦ -Real.log x) volume (-1) 1 :=
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).neg
  refine ⟨((intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hlog).integrable_indicator
    measurableSet_Icc, ?_⟩
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_neg, integral_log]
  norm_num [Real.log_neg_eq_log]

private theorem logLoss_translate (a : ℝ) :
    Integrable (fun t ↦ logLoss (t - a)) ∧ (∫ t, logLoss (t - a)) = 2 := by
  have hp := measurePreserving_sub_right (volume : Measure ℝ) a
  have he : MeasurableEmbedding (fun t : ℝ ↦ t - a) :=
    (Homeomorph.subRight a).isClosedEmbedding.measurableEmbedding
  exact ⟨(hp.integrable_comp_emb he).2 logLoss_integrable_and_integral.1,
    (hp.integral_comp he logLoss).trans logLoss_integrable_and_integral.2⟩

end LogLoss

/-- Markov's inequality for the multiplicity-weighted logarithmic losses of finitely many
ordinates. The integral bound is adapted from Patel's `exists_goodHeight_sum_posLog`. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_markov
    (A : Finset ℂ) (n : ℂ → ℕ) (T B : ℝ) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, (∀ ρ ∈ A, t ≠ ρ.im) ∧
        ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|) <
          2 * B * (∑ ρ ∈ A, (n ρ : ℝ) + 1) := by
  classical
  set N : ℝ := ∑ ρ ∈ A, (n ρ : ℝ) with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  let I := Icc T (T + 1)
  let F : ℝ → ℝ := fun t ↦ ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|)
  set c : ℝ := 2 * B * (N + 1) with hc
  have hc0 : 0 < c := by positivity
  have hFm : Measurable F := by
    refine Finset.measurable_sum _ fun ρ _ ↦ measurable_const.mul ?_
    exact measurable_const.max (Real.measurable_log.comp
      (continuous_abs.measurable.comp (measurable_id.sub_const _))).neg
  have hterm (ρ : ℂ) : Integrable (fun t ↦ (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|))
      (volume.restrict I) :=
    ((logLoss_translate ρ.im).1.const_mul (n ρ : ℝ)).integrableOn
  have hFi : Integrable F (volume.restrict I) := integrable_finsetSum A fun ρ _ ↦ hterm ρ
  have hF0 : ∀ t, 0 ≤ F t := fun t ↦
    Finset.sum_nonneg fun ρ _ ↦ mul_nonneg (Nat.cast_nonneg _) (le_max_left _ _)
  have hbound : (∫ t in I, F t) ≤ 2 * N := calc
    (∫ t in I, F t) = ∑ ρ ∈ A, ∫ t in I, (n ρ : ℝ) * max 0 (-Real.log |t - ρ.im|) :=
      integral_finsetSum A fun ρ _ ↦ hterm ρ
    _ ≤ ∑ ρ ∈ A, (n ρ : ℝ) * 2 := by
      apply Finset.sum_le_sum
      intro ρ _
      rw [integral_const_mul, ← (logLoss_translate ρ.im).2]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Eventually.of_forall fun t ↦ logLoss_nonneg (t - ρ.im))
          (logLoss_translate ρ.im).1) (Nat.cast_nonneg _)
    _ = 2 * N := by rw [hN, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict I)
    (Eventually.of_forall hF0) hFi c
  let E₁ := I ∩ {t | c ≤ F t}
  let E₂ : Set ℝ := (fun ρ : ℂ ↦ ρ.im) '' (A : Set ℂ)
  have hE₂ : volume E₂ = 0 := ((A.finite_toSet.image _).measure_zero _)
  have hE₁m : MeasurableSet E₁ := measurableSet_Icc.inter (measurableSet_le measurable_const hFm)
  have hE₁ : volume E₁ ≤ ENNReal.ofReal (1 / B) := by
    have hres : volume E₁ = (volume.restrict I) {t | c ≤ F t} := by
      rw [Measure.restrict_apply (measurableSet_le measurable_const hFm), inter_comm]
    have hlt : (volume.restrict I) {t | c ≤ F t} ≠ ⊤ := by
      rw [← hres]
      exact ne_top_of_le_ne_top (measure_Icc_lt_top (a := T) (b := T + 1)).ne
        (measure_mono inter_subset_left)
    rw [hres, ← ENNReal.ofReal_toReal hlt]
    apply ENNReal.ofReal_le_ofReal
    change ((volume.restrict I).real {t | c ≤ F t}) ≤ 1 / B
    have h2 : c * (volume.restrict I).real {t | c ≤ F t} ≤ 2 * N := hmk.trans hbound
    rw [le_div_iff₀ (by linarith)]
    have : (volume.restrict I).real {t | c ≤ F t} ≤ 2 * N / c := by
      rw [le_div_iff₀ hc0]; linarith
    calc (volume.restrict I).real {t | c ≤ F t} * B ≤ 2 * N / c * B := by
          gcongr
      _ ≤ 1 := by
          rw [hc, div_mul_eq_mul_div, div_le_one hc0]
          nlinarith
  obtain ⟨E, hEm, hE₀E, hEI, hEv⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_enlarge
      (E₀ := E₁ ∪ (I ∩ E₂)) (T := T) (r := 1 / B)
      (hE₁m.union (measurableSet_Icc.inter ((A.finite_toSet.image _).measurableSet)))
      (union_subset inter_subset_left inter_subset_left)
      (by positivity) (by rw [div_le_one (by linarith)]; exact hB.le)
      ((measure_union_le _ _).trans (by
        rw [measure_mono_null inter_subset_right hE₂, add_zero]; exact hE₁))
  refine ⟨E, hEm, hEI, hEv, fun t ⟨htI, htE⟩ ↦ ⟨fun ρ hρ hteq ↦ ?_, ?_⟩⟩
  · exact htE (hE₀E (Or.inr ⟨htI, ρ, hρ, hteq.symm⟩))
  · by_contra h
    rw [not_lt] at h
    exact htE (hE₀E (Or.inl ⟨htI, h⟩))


/-- Lower bound for `log ‖f‖` on the radius-3 disk off the zero ordinates. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_disk
    {f : ℂ → ℂ} {c : ℂ} {M δ : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f c‖) (hM : 1 ≤ M) (hbd : ∀ z ∈ Metric.sphere c 6, ‖f z‖ ≤ M) :
    ∃ (A : Finset ℂ) (n : ℂ → ℕ),
      (∑ ρ ∈ A, (n ρ : ℝ)) ≤ Real.log (M / δ) / Real.log (6 / 5 : ℝ) ∧
      ∀ z ∈ Metric.closedBall c 3, (∀ ρ ∈ A, z.im ≠ ρ.im) →
        f z ≠ 0 ∧ Real.log δ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) *
          Real.log (M / δ) - ∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |z.im - ρ.im|) ≤
            Real.log ‖f z‖ := by
  have hfc0 : 0 < ‖f c‖ := hδ.trans_le hfc
  obtain ⟨A, n, g, hfac, hN, hg⟩ :=
    External.Grh.exists_goodHeight_disk_factorization hf (norm_pos_iff.mp hfc0) hM hbd
  have hratio : Real.log (M / ‖f c‖) ≤ Real.log (M / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by linarith) hδ hfc)
  have hk1 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hk2 : 0 ≤ 8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ)) := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
    positivity
  refine ⟨A, n, hN.trans (div_le_div_of_nonneg_right hratio hk1.le), fun z hz hne ↦ ?_⟩
  obtain ⟨hgz, hgl⟩ := hg z hz
  have hρ (ρ : ℂ) (hρA : ρ ∈ A) : 0 < |z.im - ρ.im| := abs_pos.mpr (sub_ne_zero.mpr (hne ρ hρA))
  have hρ' (ρ : ℂ) (hρA : ρ ∈ A) : 0 < ‖z - ρ‖ :=
    (hρ ρ hρA).trans_le (by simpa using Complex.abs_im_le_norm (z - ρ))
  have hnorm : ‖f z‖ = (∏ ρ ∈ A, ‖z - ρ‖ ^ n ρ) * ‖g z‖ := by
    rw [hfac z, norm_mul, norm_prod]
    simp only [norm_pow]
  have hprod : 0 < ∏ ρ ∈ A, ‖z - ρ‖ ^ n ρ :=
    Finset.prod_pos fun ρ hρ ↦ pow_pos (hρ' ρ hρ) _
  have hgz0 : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
  refine ⟨norm_pos_iff.mp (hnorm ▸ mul_pos hprod hgz0), ?_⟩
  rw [hnorm, Real.log_mul hprod.ne' hgz0.ne',
    Real.log_prod (fun ρ hρ ↦ (pow_pos (hρ' ρ hρ) _).ne')]
  have hsum : -∑ ρ ∈ A, (n ρ : ℝ) * max 0 (-Real.log |z.im - ρ.im|) ≤
      ∑ ρ ∈ A, Real.log (‖z - ρ‖ ^ n ρ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro ρ hρA
    rw [Real.log_pow, ← mul_neg]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 : Real.log |z.im - ρ.im| ≤ Real.log ‖z - ρ‖ :=
      Real.log_le_log (hρ ρ hρA) (by simpa using Complex.abs_im_le_norm (z - ρ))
    have h2 : -max 0 (-Real.log |z.im - ρ.im|) ≤ Real.log |z.im - ρ.im| := by
      rw [neg_le]; exact le_max_right _ _
    linarith
  have hlogfc : Real.log δ ≤ Real.log ‖f c‖ := Real.log_le_log hδ hfc
  nlinarith [mul_le_mul_of_nonneg_left hratio hk2]


/-- The small-set lower bound for an entire function with given growth. -/
private theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set_generic
    {f : ℂ → ℂ} {T M δ B : ℝ} (hf : AnalyticOnNhd ℂ f univ) (hδ : 0 < δ)
    (hfc : δ ≤ ‖f ⟨3 / 2, T + 1 / 2⟩‖) (hM : 1 ≤ M)
    (hbd : ∀ z ∈ Metric.sphere (⟨3 / 2, T + 1 / 2⟩ : ℂ) 6, ‖f z‖ ≤ M) (hB : 1 < B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E = ENNReal.ofReal (1 / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (-1 : ℝ) 2, f ⟨σ, t⟩ ≠ 0 ∧
        Real.log δ - 8 - (8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ))) * Real.log (M / δ) -
          2 * B * (Real.log (M / δ) / Real.log (6 / 5 : ℝ) + 1) ≤ Real.log ‖f ⟨σ, t⟩‖ := by
  obtain ⟨A, n, hN, hlow⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_disk hf hδ hfc hM hbd
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_markov A n T B hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  obtain ⟨hne, hsum⟩ := hgood t ht
  have hz : (⟨σ, t⟩ : ℂ) ∈ Metric.closedBall (⟨3 / 2, T + 1 / 2⟩ : ℂ) 3 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have h1 : |σ - 3 / 2| ≤ 5 / 2 := abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have h2 : |t - (T + 1 / 2)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
    linarith
  obtain ⟨hfz, hlog⟩ := hlow _ hz hne
  refine ⟨hfz, le_trans ?_ hlog⟩
  have hB0 : 0 < 2 * B := by linarith
  have := mul_le_mul_of_nonneg_left (add_le_add_right hN 1) hB0.le
  linarith

section OutsideEulerProduct

variable (χ : U[F]) (L : ℂ → ℂ) (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)

-- TODO(later): needs §6.3 to compare with the S-local quotient in (6.3.1.6).
-- Compare as meromorphic germs, or after normalizing the quotient at removable
-- singularities. The factors agree via sLocalHeckeL_eq_partialEulerProduct on
-- descended characters. The finite-factor expression already occurs in §3.4.
local notation "Loutside" => (fun s : ℂ ↦ (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s)

include hL hSeries

/-- Paper: Theorem B.6.1.7, p. 641. The polynomial lower bound holds on a
closed unit interval outside a measurable set of length `1 / B`, with the
large-height threshold independent of `B > 1`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_horizontal_lower_bound_off_small_set :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∀ B : ℝ, 1 < B →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧
        volume E = ENNReal.ofReal (1 / B) ∧
        ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (-1 : ℝ) 2,
          T ^ (-(A * B)) < ‖Loutside ⟨σ, t⟩‖ := by
  obtain ⟨f, C, K, δ, T₀, hf, hC, hK, hδ, hδ1, hT₀, hloc⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_local χ L S hL hSeries
  have hl65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  set k2 : ℝ := 8 + 9 * (Real.log 5 / Real.log (6 / 5 : ℝ)) with hk2
  have hk20 : 0 ≤ k2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)
    positivity
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  set a : ℝ := K + Real.log C - Real.log δ with ha
  have ha0 : 0 ≤ a := by linarith
  set a' : ℝ := a / Real.log (6 / 5 : ℝ) with ha'
  have ha'0 : 0 ≤ a' := div_nonneg ha0 hl65.le
  set A : ℝ := 2 * a' + k2 * a + a + 11 with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A, hA0, ?_⟩
  filter_upwards [eventually_ge_atTop (max T₀ (Real.exp 1))] with T hT B hB
  have hTT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hTe : Real.exp 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hTe
  have hT1 : 1 ≤ T := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hTe
  set ℓ : ℝ := Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ, Real.le_log_iff_exp_le hT0]; exact hTe
  obtain ⟨hsph, hfc, hq⟩ := hloc T hTT₀
  set M : ℝ := C * T ^ K with hM
  have hTK : 1 ≤ T ^ K := Real.one_le_rpow hT1 hK
  have hM1 : 1 ≤ M := one_le_mul_of_one_le_of_one_le hC hTK
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set_generic hf hδ hfc hM1 hsph hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  obtain ⟨hfz, hlow⟩ := hgood t ht σ hσ
  obtain ⟨q, hqn, hfeq⟩ := hq t ht.1 σ hσ
  set w : ℂ := (∏ v ∈ S, (finiteHeckeEulerFactor χ v ⟨σ, t⟩)⁻¹) * L ⟨σ, t⟩ with hw
  have hfn : ‖f ⟨σ, t⟩‖ = ‖q‖ * ‖w‖ := by rw [hfeq, norm_mul]
  have hfpos : 0 < ‖f ⟨σ, t⟩‖ := norm_pos_iff.mpr hfz
  have hqpos : 0 < ‖q‖ := by
    rcases (norm_nonneg q).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hfn; linarith
  have hwpos : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hfn; linarith
  have hlogq : Real.log ‖q‖ ≤ Real.log C + K * ℓ := by
    have := Real.log_le_log hqpos hqn
    rwa [Real.log_mul (by linarith) (by linarith), Real.log_rpow hT0] at this
  have hlogf : Real.log ‖f ⟨σ, t⟩‖ = Real.log ‖q‖ + Real.log ‖w‖ := by
    rw [hfn, Real.log_mul hqpos.ne' hwpos.ne']
  set X : ℝ := Real.log (M / δ) with hX
  have hXa : X ≤ a * ℓ := by
    rw [hX, Real.log_div (by linarith) hδ.ne', hM, Real.log_mul (by linarith) (by linarith),
      Real.log_rpow hT0]
    have := mul_le_mul_of_nonneg_left hℓ1 (by linarith : (0 : ℝ) ≤ Real.log C - Real.log δ)
    rw [ha]
    linarith
  have hY : X / Real.log (6 / 5 : ℝ) ≤ a' * ℓ := by
    rw [ha', div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hXa hl65.le
  have hBℓ : ℓ ≤ B * ℓ := le_mul_of_one_le_left (by linarith) hB.le
  have h1 : B * (X / Real.log (6 / 5 : ℝ)) ≤ a' * (B * ℓ) := by
    have := mul_le_mul_of_nonneg_left hY (by linarith : (0 : ℝ) ≤ B)
    linarith [show B * (a' * ℓ) = a' * (B * ℓ) by ring]
  have h2 : a * ℓ ≤ a * (B * ℓ) := mul_le_mul_of_nonneg_left hBℓ ha0
  have h3 : k2 * X ≤ k2 * (a * (B * ℓ)) := mul_le_mul_of_nonneg_left (hXa.trans h2) hk20
  have h4 : 1 ≤ B * ℓ := one_le_mul_of_one_le_of_one_le hB.le hℓ1
  have hKℓ : K * ℓ + Real.log C - Real.log δ ≤ a * ℓ := by
    have := mul_le_mul_of_nonneg_left hℓ1 (by linarith : (0 : ℝ) ≤ Real.log C - Real.log δ)
    rw [ha]
    linarith
  have h5 : B ≤ B * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
  have hlogw : -(A * B) * ℓ < Real.log ‖w‖ := by
    have e : A * B * ℓ = 2 * (a' * (B * ℓ)) + k2 * (a * (B * ℓ)) + a * (B * ℓ) + 11 * (B * ℓ) := by
      rw [hA]; ring
    have e2 : 2 * B * (X / Real.log (6 / 5 : ℝ) + 1) = 2 * (B * (X / Real.log (6 / 5 : ℝ))) + 2 * B := by ring
    nlinarith
  rw [Real.rpow_def_of_pos hT0, ← Real.exp_log hwpos, mul_comm]
  exact Real.exp_lt_exp.mpr hlogw

/-- Paper: Theorem B.6.1.7, p. 641. Each sufficiently high open unit interval
contains a height at which the Euler product outside `S` has a polynomial
lower bound on the whole horizontal segment from real part `-1` to `2`.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. -/
theorem finiteHeckeL_outside_exists_horizontal_lower_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∃ t ∈ Ioo T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A) < ‖Loutside ⟨σ, t⟩‖ := by
  obtain ⟨A, hA, hev⟩ :=
    finiteHeckeL_outside_horizontal_lower_bound_off_small_set χ L S hL hSeries
  refine ⟨A * 2, by positivity, ?_⟩
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with T hT hT1
  obtain ⟨E, -, -, hEvol, hE⟩ := hT 2 one_lt_two
  have hne : (Ioo T (T + 1) \ E).Nonempty := by
    by_contra h
    have hsub : Ioo T (T + 1) ⊆ E := fun x hx ↦ by
      by_contra hxE
      exact h ⟨x, hx, hxE⟩
    have h1 := measure_mono (μ := volume) hsub
    rw [Real.volume_Ioo, hEvol] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h1
    norm_num at h2
  obtain ⟨t, ht, htE⟩ := hne
  refine ⟨t, ht, fun σ hσ ↦ lt_of_le_of_lt ?_ (hE t ⟨Ioo_subset_Icc_self ht, htE⟩ σ hσ)⟩
  rw [abs_of_pos (by linarith [ht.1])]
  exact Real.rpow_le_rpow_of_nonpos (by linarith) ht.1.le (by nlinarith)

-- TODO(paper-gap): The exponent in (B.6.1.38) must account for the left edge
-- of the strip. The basepoint for the integration in (B.6.1.43) is log Loutside(2 + it).

-- TODO(paper-gap): Footnote 29 asks for details in the proof of Corollary B.6.1.8
-- that pass from horizontal lower bounds to bounds for reciprocal derivatives.
-- At the selected heights use Cauchy's estimates on a wider fixed strip for
-- derivatives of Loutside, then differentiate Loutside * (1 / Loutside) = 1.

omit hL hSeries in
/-- A meromorphic normal form that is polynomially bounded on a vertical strip at large height
is analytic at every interior point of the strip above the threshold. -/
private theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_analytic (G : ℂ → ℂ)
    (hG : MeromorphicNFOn G univ) (a b T : ℝ) (n : ℕ)
    (hT : ∀ z : ℂ, z.re ∈ Icc a b → T ≤ |z.im| → ‖G z‖ ≤ |z.im| ^ n)
    (w : ℂ) (hw : w.re ∈ Ioo a b) (hwT : T < |w.im|) : AnalyticAt ℂ G w := by
  apply (hG (mem_univ w)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hre := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hw
  have him := (isOpen_Ioo.preimage Complex.continuous_im.abs).mem_nhds
    (show w ∈ (fun z : ℂ ↦ |z.im|) ⁻¹' Ioo T (|w.im| + 1) from ⟨hwT, by linarith⟩)
  have hb : ∀ᶠ z in 𝓝 w, ‖G z‖ ≤ (|w.im| + 1) ^ n := by
    filter_upwards [hre, him] with z hz h'z
    exact (hT z (Ioo_subset_Icc_self hz) h'z.1.le).trans
      (pow_le_pow_left₀ (abs_nonneg _) h'z.2.le _)
  have hp' := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop ((|w.im| + 1) ^ n)
  obtain ⟨_, h, h'⟩ := ((hb.filter_mono nhdsWithin_le_nhds).and hp').exists
  exact h'.not_ge h

omit hL hSeries in
/-- The reciprocal Euler factors at the finitely many places of `S` form an entire function
bounded on the half-plane `Re s ≥ -c` by a constant depending on `S` and `c`. -/
private theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_euler (c : ℝ) :
    Differentiable ℂ (fun s : ℂ ↦ ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℂ, -c ≤ s.re →
        ‖∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹‖ ≤ C := by
  classical
  have hfac : ∀ v : HeightOneSpectrum (𝓞 F), ∀ s : ℂ, (finiteHeckeEulerFactor χ v s)⁻¹ =
      if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
        1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) else 1 := by
    intro v s
    unfold finiteHeckeEulerFactor
    split_ifs <;> simp
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < v.asIdeal.absNorm := fun v ↦
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  have hdiff : ∀ v : HeightOneSpectrum (𝓞 F),
      Differentiable ℂ (fun s ↦ (finiteHeckeEulerFactor χ v s)⁻¹) := by
    intro v
    simp_rw [hfac]
    split_ifs
    · have hN : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast (hNpos v).ne'
      exact (differentiable_const _).sub
        ((differentiable_const _).mul (differentiable_neg.const_cpow (Or.inl hN)))
    · exact differentiable_const _
  have hbound : ∀ v : HeightOneSpectrum (𝓞 F), ∀ s : ℂ, -c ≤ s.re →
      ‖(finiteHeckeEulerFactor χ v s)⁻¹‖ ≤ 1 + (v.asIdeal.absNorm : ℝ) ^ c := by
    intro v s hs
    rw [hfac]
    have hN1 : (1 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast hNpos v
    have hpow : 0 ≤ (v.asIdeal.absNorm : ℝ) ^ c := Real.rpow_nonneg (by positivity) _
    split_ifs
    · calc ‖1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖
          ≤ ‖(1 : ℂ)‖ + ‖(ideleClassNormTwist χ 0).localValue v *
              (v.asIdeal.absNorm : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ = 1 + (v.asIdeal.absNorm : ℝ) ^ (-s).re := by
          rw [norm_one, norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
            Complex.norm_natCast_cpow_of_pos (hNpos v)]
        _ ≤ 1 + (v.asIdeal.absNorm : ℝ) ^ c := by
          have hsc : (-s).re ≤ c := by
            rw [Complex.neg_re]
            linarith
          exact add_le_add_right (Real.rpow_le_rpow_of_exponent_le hN1 hsc) 1
    · rw [norm_one]
      linarith
  have hprod : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      Differentiable ℂ (fun s : ℂ ↦ ∏ v ∈ T, (finiteHeckeEulerFactor χ v s)⁻¹) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp_rw [Finset.prod_insert ha]
      exact (hdiff a).mul ih
  refine ⟨hprod S, ∏ v ∈ S, (1 + (v.asIdeal.absNorm : ℝ) ^ c), ?_, fun s hs ↦ ?_⟩
  · calc (1 : ℝ) = ∏ v ∈ S, (1 : ℝ) := by simp
      _ ≤ ∏ v ∈ S, (1 + (v.asIdeal.absNorm : ℝ) ^ c) :=
        Finset.prod_le_prod₀ (fun v _ ↦ zero_le_one) fun v _ ↦ by
          linarith [Real.rpow_nonneg (Nat.cast_nonneg v.asIdeal.absNorm) c]
  · rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) fun v _ ↦ hbound v s hs

omit hL hSeries in
/-- Cauchy estimates for the reciprocal: if `f` is analytic and bounded by `M` on the closed disc
of radius two around `z` and `‖f z‖ ≥ ε`, then `1 / f` is analytic at `z` and its `m`-th
derivative there is at most `m! (2 / ε) (2 M / ε) ^ m`. -/
private theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_cauchy (m : ℕ)
    (f : ℂ → ℂ) (z : ℂ) (M ε : ℝ) (hε : 0 < ε)
    (hf : ∀ w ∈ Metric.closedBall z 2, AnalyticAt ℂ f w)
    (hM : ∀ w ∈ Metric.closedBall z 2, ‖f w‖ ≤ M) (hz : ε ≤ ‖f z‖) :
    AnalyticAt ℂ (fun s ↦ (f s)⁻¹) z ∧
      ‖iteratedDeriv m (fun s ↦ (f s)⁻¹) z‖ ≤ m.factorial * (2 / ε) * (2 * M / ε) ^ m := by
  have hz2 : z ∈ Metric.closedBall z 2 := Metric.mem_closedBall_self (by norm_num)
  have hεM : ε ≤ M := hz.trans (hM z hz2)
  have hM0 : 0 < M := hε.trans_le hεM
  have h12 : Metric.closedBall z 1 ⊆ Metric.closedBall z 2 :=
    Metric.closedBall_subset_closedBall (by norm_num)
  have hderiv : ∀ w ∈ Metric.closedBall z 1, ‖deriv f w‖ ≤ M := by
    intro w hw
    have hsub : Metric.closedBall w 1 ⊆ Metric.closedBall z 2 :=
      Metric.closedBall_subset_closedBall' (by linarith [Metric.mem_closedBall.mp hw])
    have hdiff : DiffContOnCl ℂ f (Metric.ball w 1) :=
      (show DifferentiableOn ℂ f (Metric.closedBall w 1) from fun u hu ↦
        (hf u (hsub hu)).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hdiff
      fun u hu ↦ hM u (hsub (Metric.sphere_subset_closedBall hu))
    simpa using this
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ε / (2 * M) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, div_le_iff₀ (by positivity)]
    linarith
  have hball : Metric.closedBall z ρ ⊆ Metric.closedBall z 1 :=
    Metric.closedBall_subset_closedBall hρ1
  have hlow : ∀ w ∈ Metric.closedBall z ρ, ε / 2 ≤ ‖f w‖ := by
    intro w hw
    have hmv := (convex_closedBall z ρ).norm_image_sub_le_of_norm_deriv_le
      (fun u hu ↦ (hf u (h12 (hball hu))).differentiableAt)
      (fun u hu ↦ hderiv u (hball hu)) (Metric.mem_closedBall_self hρ0.le) hw
    have hwz : ‖w - z‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hw
    have h1 : M * ‖w - z‖ ≤ ε / 2 := by
      calc M * ‖w - z‖ ≤ M * ρ := by gcongr
        _ = ε / 2 := by rw [hρ]; field_simp
    have h2 := norm_sub_norm_le (f z) (f w)
    rw [norm_sub_rev] at h2
    linarith
  have hne : ∀ w ∈ Metric.closedBall z ρ, f w ≠ 0 := fun w hw ↦
    norm_pos_iff.mp (by linarith [hlow w hw])
  have hinv_an : ∀ w ∈ Metric.closedBall z ρ, AnalyticAt ℂ (fun s ↦ (f s)⁻¹) w := fun w hw ↦
    (hf w (h12 (hball hw))).inv (hne w hw)
  refine ⟨hinv_an z (Metric.mem_closedBall_self hρ0.le), ?_⟩
  have hdiff : DiffContOnCl ℂ (fun s ↦ (f s)⁻¹) (Metric.ball z ρ) :=
    (show DifferentiableOn ℂ (fun s ↦ (f s)⁻¹) (Metric.closedBall z ρ) from fun u hu ↦
      (hinv_an u hu).differentiableAt.differentiableWithinAt).diffContOnCl_ball subset_rfl
  have hC : ∀ w ∈ Metric.sphere z ρ, ‖(f w)⁻¹‖ ≤ 2 / ε := fun w hw ↦ by
    rw [norm_inv]
    have := hlow w (Metric.sphere_subset_closedBall hw)
    rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
    linarith
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hρ0 hdiff hC
  refine h.trans (le_of_eq ?_)
  rw [hρ, div_pow, div_div_eq_mul_div, div_pow]
  ring

/-- At a height where the Euler product outside `S` has the polynomial lower bound
`|t| ^ (-A₀)` on the segment `-1 ≤ Re s ≤ 2`, the reciprocal is analytic on the segment and its
`m`-th derivative is bounded by a fixed power of the height, with constants independent of the
height. -/
private theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_good (m : ℕ) (A₀ : ℝ)
    (hA₀ : 0 < A₀) :
    ∃ A β T₀ : ℝ, 0 < A ∧ 0 < β ∧ ∀ t : ℝ, T₀ ≤ |t| →
      (∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A₀) < ‖Loutside ⟨σ, t⟩‖) →
      ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (fun s ↦ (Loutside s)⁻¹) ⟨σ, t⟩ ∧
          ‖iteratedDeriv m (fun s ↦ (Loutside s)⁻¹) ⟨σ, t⟩‖ ≤ A * |t| ^ β := by
  obtain ⟨M₁, -, hM₁⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries (-4) 5 (by norm_num)
  obtain ⟨n, T₁, hup⟩ := finiteHeckeL_inv_isBigO_oneLine_strip_bound_nat L (-4) 5 M₁ hM₁
  obtain ⟨hPd, C, hC1, hCb⟩ :=
    finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_euler χ S 4
  refine ⟨m.factorial * 2 * (2 ^ (n + 1) * C) ^ m, A₀ + (n + A₀) * m, max (T₁ + 3) 2,
    by positivity, by positivity, fun t ht hgood σ hσ ↦ ?_⟩
  have ht2 : 2 ≤ |t| := (le_max_right _ _).trans ht
  have htT : T₁ + 3 ≤ |t| := (le_max_left _ _).trans ht
  have hpos : 0 < |t| := by linarith
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun s ↦ (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s :=
    ⟨_, rfl⟩
  have hfval : ∀ s, f s = (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s := fun s ↦ by
    rw [hf]
  simp only [← hfval] at hgood ⊢
  have hdisc : ∀ w ∈ Metric.closedBall (⟨σ, t⟩ : ℂ) 2,
      AnalyticAt ℂ f w ∧ ‖f w‖ ≤ C * (2 * |t|) ^ n := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre := Complex.abs_re_le_norm (w - ⟨σ, t⟩)
    have him := Complex.abs_im_le_norm (w - ⟨σ, t⟩)
    simp only [Complex.sub_re, Complex.sub_im] at hre him
    obtain ⟨hre₁, hre₂⟩ := abs_le.mp (hre.trans hw)
    obtain ⟨him₁, him₂⟩ := abs_le.mp (him.trans hw)
    have hwim : |t| - 2 ≤ |w.im| ∧ |w.im| ≤ |t| + 2 := by
      constructor <;> cases abs_cases t <;> cases abs_cases w.im <;> linarith
    have hLw : AnalyticAt ℂ L w :=
      finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_analytic L hL (-4) 5 T₁ n hup w
        ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ (by linarith)
    refine ⟨?_, ?_⟩
    · rw [hf]
      exact (hPd.analyticAt w).mul hLw
    · rw [hfval, norm_mul]
      calc ‖∏ v ∈ S, (finiteHeckeEulerFactor χ v w)⁻¹‖ * ‖L w‖ ≤ C * |w.im| ^ n := by
            gcongr
            · exact hCb w (by linarith [hσ.1])
            · exact hup w ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ (by linarith)
        _ ≤ C * (2 * |t|) ^ n := by
            gcongr
            linarith
  have hz : |t| ^ (-A₀) ≤ ‖f ⟨σ, t⟩‖ := (hgood σ hσ).le
  obtain ⟨han, hbd⟩ := finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_cauchy m f
    ⟨σ, t⟩ (C * (2 * |t|) ^ n) (|t| ^ (-A₀)) (Real.rpow_pos_of_pos hpos _)
    (fun w hw ↦ (hdisc w hw).1) (fun w hw ↦ (hdisc w hw).2) hz
  refine ⟨han, hbd.trans (le_of_eq ?_)⟩
  have h1 : 2 / |t| ^ (-A₀) = 2 * |t| ^ A₀ := by
    rw [Real.rpow_neg hpos.le, div_eq_mul_inv, inv_inv]
  have h2 : 2 * (C * (2 * |t|) ^ n) / |t| ^ (-A₀) = 2 ^ (n + 1) * C * |t| ^ ((n : ℝ) + A₀) := by
    rw [Real.rpow_neg hpos.le, div_eq_mul_inv, inv_inv, mul_pow, Real.rpow_add hpos,
      Real.rpow_natCast]
    ring
  rw [h1, h2, mul_pow, ← Real.rpow_mul_natCast hpos.le, Real.rpow_add hpos]
  ring

omit hL hSeries in
open scoped ComplexConjugate in
/-- Each finite Euler factor of the inverse character is the conjugate of the original
factor evaluated at the conjugate point. -/
private theorem finiteHeckeEulerFactor_invCharacter
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    finiteHeckeEulerFactor χ⁻¹ v s = conj (finiteHeckeEulerFactor χ v (conj s)) := by
  have hres (x : v.adicCompletion F) :
      (ideleClassNormTwist χ⁻¹ 0).restrict v x = conj ((ideleClassNormTwist χ 0).restrict v x) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    let u := Units.mk0 x hx
    change (ideleClassNormTwist χ⁻¹ 0).restrict v (u : v.adicCompletion F) =
      conj ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F))
    simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (((χ _)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ) = conj ((χ _ : ℂ) * _ ^ (0 : ℂ))
    simp only [Complex.cpow_zero, mul_one, Circle.coe_inv_eq_conj]
  have hu : (ideleClassNormTwist χ⁻¹ 0).IsUnramifiedAt v ↔
      (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, hres, map_eq_one_iff _ (starRingEnd ℂ).injective]
  have hv : (ideleClassNormTwist χ⁻¹ 0).localValue v =
      conj ((ideleClassNormTwist χ 0).localValue v) := hres _
  have hpow : conj ((v.asIdeal.absNorm : ℂ) ^ (-conj s)) = (v.asIdeal.absNorm : ℂ) ^ (-s) := by
    rw [← map_neg, ← Complex.conj_cpow _ _ (by rw [Complex.natCast_arg]; positivity),
      Complex.conj_natCast]
  unfold finiteHeckeEulerFactor
  rw [hu]
  split_ifs <;> simp only [map_inv₀, map_sub, map_mul, map_one, hpow, hv]

open scoped ComplexConjugate in
/-- Paper: Theorem B.6.1.7, p. 641, on the negative tail. Each sufficiently high open unit
interval `(T, T + 1)` contains a height `t` such that the Euler product outside `S` has the
polynomial lower bound `|t| ^ (-A)` on the whole horizontal segment from real part `-1` to `2`
at height `-t`. The paper obtains it from the positive-tail statement for the conjugate
character `χ⁻¹`, using `L_f(s̄, χ̄) = conj L_f(s, χ)` and the same identity for the finitely many
Euler factors. -/
theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_neg :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop, ∃ t ∈ Ioo T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A) < ‖Loutside ⟨σ, -t⟩‖ := by
  let R : ℂ → ℂ := conj ∘ L ∘ conj
  -- Reflect the local normal form, keeping the order of its zero or pole.
  have hR : MeromorphicNFOn R univ := by
    intro z _
    have hc := Complex.continuous_conj.tendsto z
    rcases hL (mem_univ (conj z)) with hzero | ⟨n, g, hg, hne, heq⟩
    · left
      filter_upwards [hc.eventually hzero] with w hw
      exact (congrArg conj hw).trans (map_zero _)
    · refine Or.inr ⟨n, conj ∘ g ∘ conj, ?_, ?_, ?_⟩
      · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
        filter_upwards [hc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)]
          with w hw
        simpa only [Complex.conj_conj] using hw.comp_ringHom conj conj
      · exact (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hne
      · filter_upwards [hc.eventually heq] with w hw
        simpa only [R, comp_apply, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, map_mul,
          map_zpow₀, map_sub, Complex.conj_conj] using congrArg conj hw
  have hSeriesR (s : halfPlane) : R s = finiteHeckeL χ⁻¹ s := by
    let w : halfPlane := ⟨conj (s : ℂ), s.property⟩
    change conj (L w) = _
    rw [hSeries w]
    have hp := (finiteHeckeL_hasProd χ w).map conj Complex.continuous_conj
    exact (hp.congr_fun (fun v ↦ finiteHeckeEulerFactor_invCharacter χ v s)).unique
      (finiteHeckeL_hasProd χ⁻¹ s)
  obtain ⟨A, hA, hT⟩ := finiteHeckeL_outside_exists_horizontal_lower_bound χ⁻¹ R S hR hSeriesR
  refine ⟨A, hA, ?_⟩
  filter_upwards [hT] with T h
  obtain ⟨t, ht, hgood⟩ := h
  refine ⟨t, ht, fun σ hσ ↦ ?_⟩
  have hreflect (z : ℂ) : (∏ v ∈ S, (finiteHeckeEulerFactor χ⁻¹ v z)⁻¹) * R z =
      conj (Loutside (conj z)) := by
    simp only [R, comp_apply, map_mul, map_prod, map_inv₀, finiteHeckeEulerFactor_invCharacter]
  have hconj : conj (⟨σ, t⟩ : ℂ) = ⟨σ, -t⟩ := rfl
  simpa only [hreflect, Complex.norm_conj, hconj] using hgood σ hσ

/-- Paper: Corollary B.6.1.8, p. 643. For each derivative order there is a
nondecreasing sequence of heights tending to infinity in absolute value and
growing at most linearly in the index. The derivative of the reciprocal Euler
product is bounded by a fixed power of the height on every selected segment.
Deviation: The finite set records only finite places. All archimedean factors
have already been removed from `L`. The supremum is expressed pointwise, and
analyticity ensures the iterated derivatives are defined on the segments. The
unit intervals of Theorem B.6.1.7, reflected for the conjugate character on the
negative tail, give heights within one of the index for the application of §B.3. -/
theorem finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound (m : ℕ) :
    let l := comap (abs : ℤ → ℤ) atTop
    ∃ (A β : ℝ) (T : ℤ → ℝ), 0 < A ∧ 0 < β ∧ Monotone T ∧
      Tendsto (abs ∘ T) l atTop ∧ (T =O[l] fun k ↦ |(k : ℝ)|) ∧
      (∀ᶠ k : ℤ in l, |T k - (k : ℝ)| ≤ 1) ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩ ∧
          ‖iteratedDeriv m (fun s ↦ (Loutside s)⁻¹) ⟨σ, T k⟩‖ ≤ A * |T k| ^ β := by
  intro l
  obtain ⟨A₁, hA₁, hpos⟩ := finiteHeckeL_outside_exists_horizontal_lower_bound χ L S hL hSeries
  obtain ⟨A₂, hA₂, hneg⟩ := finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_neg χ L S hL hSeries
  obtain ⟨A, β, T₀, hA, hβ, hgood⟩ := finiteHeckeL_outside_inv_iteratedDeriv_horizontal_bound_good
    χ L S hL hSeries m (max A₁ A₂) (lt_max_of_lt_left hA₁)
  rw [eventually_atTop] at hpos hneg
  obtain ⟨Tp, hTp⟩ := hpos
  obtain ⟨Tn, hTn⟩ := hneg
  obtain ⟨k₀, hk₀⟩ := exists_nat_ge (max (max Tp Tn) (max T₀ 2))
  have hk₀p : Tp ≤ k₀ := (le_max_left _ _).trans ((le_max_left _ _).trans hk₀)
  have hk₀n : Tn ≤ k₀ := (le_max_right _ _).trans ((le_max_left _ _).trans hk₀)
  have hk₀T : T₀ ≤ k₀ := (le_max_left _ _).trans ((le_max_right _ _).trans hk₀)
  have hk₀2 : 2 ≤ (k₀ : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hk₀)
  have hp' : ∀ j : ℕ, k₀ ≤ j → ∃ t : ℝ, t ∈ Ioo (j : ℝ) (j + 1) ∧
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A₁) <
        ‖Loutside ⟨σ, t⟩‖ := fun j hj ↦ by
    obtain ⟨t, ht, h⟩ := hTp j (hk₀p.trans (by exact_mod_cast hj))
    exact ⟨t, ht, h⟩
  have hn' : ∀ j : ℕ, k₀ ≤ j → ∃ t : ℝ, t ∈ Ioo (j : ℝ) (j + 1) ∧
      ∀ σ ∈ Icc (-1 : ℝ) 2, |t| ^ (-A₂) <
        ‖Loutside ⟨σ, -t⟩‖ := fun j hj ↦ by
    obtain ⟨t, ht, h⟩ := hTn j (hk₀n.trans (by exact_mod_cast hj))
    exact ⟨t, ht, h⟩
  choose! tp htp using hp'
  choose! tn htn using hn'
  have hmono : ∀ (f : ℕ → ℝ), (∀ j, k₀ ≤ j → f j ∈ Ioo (j : ℝ) (j + 1)) →
      ∀ i j, k₀ ≤ i → i ≤ j → f i ≤ f j := by
    intro f hf i j hi hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have h1 := (hf i hi).2
      have h2 := (hf j (hi.trans hij)).1
      have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      linarith
  have hexp : ∀ t : ℝ, 1 ≤ |t| → ∀ a : ℝ, a ≤ max A₁ A₂ →
      |t| ^ (-(max A₁ A₂)) ≤ |t| ^ (-a) := fun t ht a ha ↦
    Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg ha)
  obtain ⟨T, hT⟩ : ∃ T : ℤ → ℝ, ∀ k : ℤ,
      T k = if 0 ≤ k then tp (max k.toNat k₀) else -(tn (max (-k).toNat k₀)) := ⟨_, fun _ ↦ rfl⟩
  have hTpos : ∀ k : ℤ, 0 ≤ k → T k = tp (max k.toNat k₀) := fun k hk ↦ by
    rw [hT, ite_eq_left hk]
  have hTneg : ∀ k : ℤ, k < 0 → T k = -(tn (max (-k).toNat k₀)) := fun k hk ↦ by
    rw [hT, ite_eq_right (not_le.mpr hk)]
  have htp0 : ∀ j, k₀ ≤ j → 0 < tp j := fun j hj ↦ by
    have := (htp j hj).1.1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  have htn0 : ∀ j, k₀ ≤ j → 0 < tn j := fun j hj ↦ by
    have := (htn j hj).1.1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  have hcast : ∀ k : ℤ, 0 ≤ k → ((k.toNat : ℕ) : ℝ) = (k : ℝ) := fun k hk ↦ by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hk]
  -- the two tails
  have hkey : ∀ k : ℤ, (k₀ : ℤ) ≤ |k| → |T k - (k : ℝ)| ≤ 1 ∧ |(k : ℝ)| ≤ |T k| := by
    intro k hk
    rcases le_or_gt 0 k with hk0 | hk0
    · rw [abs_of_nonneg hk0] at hk
      have hj : k₀ ≤ k.toNat := (Int.le_toNat hk0).mpr hk
      rw [hTpos k hk0, max_eq_left hj]
      obtain ⟨⟨h1, h2⟩, -⟩ := htp k.toNat hj
      rw [hcast k hk0] at h1 h2
      have hk0r : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      rw [abs_of_nonneg hk0r, abs_of_pos (by linarith : 0 < tp k.toNat)]
      constructor
      · rw [abs_le]; constructor <;> linarith
      · linarith
    · rw [abs_of_neg hk0] at hk
      have hk0' : 0 ≤ -k := by linarith
      have hj : k₀ ≤ (-k).toNat := (Int.le_toNat hk0').mpr hk
      rw [hTneg k hk0, max_eq_left hj]
      obtain ⟨⟨h1, h2⟩, -⟩ := htn (-k).toNat hj
      rw [hcast (-k) hk0', Int.cast_neg] at h1 h2
      have hkr : (k : ℝ) < 0 := by exact_mod_cast hk0
      rw [abs_of_neg hkr, abs_neg, abs_of_pos (by linarith : 0 < tn (-k).toNat)]
      constructor
      · rw [abs_le]; constructor <;> linarith
      · linarith
  have hev : ∀ᶠ k : ℤ in l, (k₀ : ℤ) ≤ |k| :=
    (tendsto_comap (f := (abs : ℤ → ℤ))).eventually_ge_atTop (k₀ : ℤ)
  refine ⟨A, β, T, hA, hβ, ?_, ?_, ?_, hev.mono fun k hk ↦ (hkey k hk).1, fun k σ hσ ↦ ?_⟩
  · -- monotone
    intro k k' hkk'
    rcases le_or_gt 0 k with hk | hk
    · have hk' : 0 ≤ k' := hk.trans hkk'
      rw [hTpos k hk, hTpos k' hk']
      exact hmono tp (fun j hj ↦ (htp j hj).1) _ _ (le_max_right _ _)
        (max_le_max (Int.toNat_le_toNat hkk') le_rfl)
    · rcases le_or_gt 0 k' with hk' | hk'
      · rw [hTneg k hk, hTpos k' hk']
        have := htn0 _ (le_max_right (-k).toNat k₀)
        have := htp0 _ (le_max_right k'.toNat k₀)
        linarith
      · rw [hTneg k hk, hTneg k' hk']
        apply neg_le_neg
        exact hmono tn (fun j hj ↦ (htn j hj).1) _ _ (le_max_right _ _)
          (max_le_max (Int.toNat_le_toNat (by linarith)) le_rfl)
  · -- tendsto
    rw [tendsto_atTop]
    intro b
    filter_upwards [(tendsto_comap (f := (abs : ℤ → ℤ))).eventually_ge_atTop (max ⌈b⌉ k₀)]
      with k hk
    have hk₀k : (k₀ : ℤ) ≤ |k| := (le_max_right _ _).trans hk
    have hbk : (⌈b⌉ : ℤ) ≤ |k| := (le_max_left _ _).trans hk
    have h1 : b ≤ |(k : ℝ)| := by
      have : ((⌈b⌉ : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast hbk
      rw [Int.cast_abs] at this
      linarith [Int.le_ceil b]
    exact h1.trans (hkey k hk₀k).2
  · -- big O
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hev] with k hk
    obtain ⟨h1, h2⟩ := hkey k hk
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : ((1 : ℕ) : ℤ) ≤ |k| := le_trans (by exact_mod_cast (by linarith : 1 ≤ (k₀ : ℝ))) hk
      have : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast this
      rwa [Int.cast_abs, Int.cast_one] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    have := abs_sub_abs_le_abs_sub (T k) (k : ℝ)
    linarith
  · -- the bound at each index
    rcases le_or_gt 0 k with hk | hk
    · rw [hTpos k hk]
      have hj : k₀ ≤ max k.toNat k₀ := le_max_right _ _
      obtain ⟨⟨h1, -⟩, hgd⟩ := htp _ hj
      have hjk : (k₀ : ℝ) ≤ (max k.toNat k₀ : ℕ) := by exact_mod_cast hj
      have hpos : T₀ ≤ |tp (max k.toNat k₀)| := by
        rw [abs_of_pos (htp0 _ hj)]
        linarith
      exact hgood _ hpos (fun σ hσ ↦ (hexp _ (by rw [abs_of_pos (htp0 _ hj)]; linarith) A₁
        (le_max_left _ _)).trans_lt (hgd σ hσ)) σ hσ
    · rw [hTneg k hk]
      have hj : k₀ ≤ max (-k).toNat k₀ := le_max_right _ _
      obtain ⟨⟨h1, -⟩, hgd⟩ := htn _ hj
      have hjk : (k₀ : ℝ) ≤ (max (-k).toNat k₀ : ℕ) := by exact_mod_cast hj
      have habs : |-(tn (max (-k).toNat k₀))| = tn (max (-k).toNat k₀) := by
        rw [abs_neg, abs_of_pos (htn0 _ hj)]
      have hpos : T₀ ≤ |-(tn (max (-k).toNat k₀))| := by
        rw [habs]
        linarith
      refine hgood _ hpos (fun σ hσ ↦ ?_) σ hσ
      rw [habs]
      have := hgd σ hσ
      rw [abs_of_pos (htn0 _ hj)] at this
      exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (le_max_right A₁ A₂))).trans_lt
        this

end OutsideEulerProduct

end RiemannMasullo
