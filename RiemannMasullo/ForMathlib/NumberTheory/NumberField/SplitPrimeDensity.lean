module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The Dirichlet density of completely split rational primes

For a finite Galois extension, count prime ideals first upstairs and then in fibers.
The ramified primes and the unramified primes of residue degree at least two contribute
a bounded error. The simple pole of Dedekind zeta supplies the leading logarithm.
For an arbitrary number field, complete splitting is equivalent to complete splitting
in its normal closure.
-/

public noncomputable section

open Filter IntermediateField IsDedekindDomain NumberField NumberField.Set Set
open scoped Topology Asymptotics Pointwise

namespace RiemannMasullo

local notation "Primes(" K ")" => HeightOneSpectrum (𝓞 K)

section PrimeSum

variable (K : Type*) [Field K] [NumberField K]

private theorem summable_prime_norm_rpow {s : ℝ} (hs : 1 < s) :
    Summable fun v : Primes(K) ↦ (v.asIdeal.absNorm : ℝ) ^ (-s) :=
  (RiemannMasullo.summable_absNorm_rpow K hs).comp_injective (fun _ _ h ↦ HeightOneSpectrum.ext h)

/-- The sum of the terms of degree at least two in the logarithmic Euler product
is bounded uniformly as the real exponent decreases to one. -/
private theorem log_dedekindZeta_sub_prime_sum {s : ℝ} (hs : 1 < s) :
    let P := primeIdealZetaSum (univ : Set (Primes(K))) s
    0 ≤ Real.log ‖dedekindZeta K s‖ - P ∧ Real.log ‖dedekindZeta K s‖ - P ≤
      2 * ∑' v : Primes(K), (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) := by
  let x (v : Primes(K)) := (v.asIdeal.absNorm : ℝ) ^ (-s)
  let y (v : Primes(K)) := (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ))
  let L v := Real.log (1 - x v)⁻¹
  have hx (v) : 0 ≤ x v := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hhalf (v) : x v ≤ 1 / 2 := by
    have hq : (2 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast (Nat.succ_le_of_lt (HeightOneSpectrum.one_lt_absNorm v))
    calc
      x v ≤ (v.asIdeal.absNorm : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 1 / 2 := by rw [Real.rpow_neg_one, inv_eq_one_div]; gcongr
  have hpos (v) : 0 < 1 - x v := by linarith [hhalf v]
  have hsq (v) : x v ^ 2 ≤ y v := by
    dsimp [x, y]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le)
      (by push_cast; linarith)
  have hlog (v) : x v ≤ L v ∧ L v ≤ x v + 2 * y v := by
    have hl := Real.one_sub_inv_le_log_of_pos (inv_pos.mpr (hpos v))
    have hu := Real.log_le_sub_one_of_pos (inv_pos.mpr (hpos v))
    rw [inv_inv] at hl
    refine ⟨by simpa [L] using hl, hu.trans ?_⟩
    have h := hhalf v
    have hh : 1 ≤ (1 + x v + 2 * x v ^ 2) * (1 - x v) := by
      nlinarith [mul_nonneg (sq_nonneg (x v)) (sub_nonneg.mpr h)]
    have hinv := (inv_le_iff_one_le_mul₀ (hpos v)).mpr (by simpa [mul_comm] using hh)
    linarith [hsq v]
  have hxS : Summable x := summable_prime_norm_rpow K hs
  have hyS : Summable y := summable_prime_norm_rpow K (by norm_num)
  have hLS : Summable L :=
    Summable.of_nonneg_of_le (fun v ↦ (hx v).trans (hlog v).1) (fun v ↦ (hlog v).2)
      (hxS.add (hyS.mul_left 2))
  have hp := (Real.hasProd_of_hasSum_log (fun v ↦ inv_pos.mpr (hpos v)) hLS.hasSum)
  have he : ‖dedekindZeta K s‖ = Real.exp (∑' v, L v) := by
    have h := (RiemannMasullo.dedekindZeta_hasProd K (s := (s : ℂ)) hs).norm
    apply HasProd.unique (f := fun v ↦ (1 - x v)⁻¹) _ hp
    refine h.congr_fun (fun v ↦ ?_)
    have hc : (v.asIdeal.absNorm : ℂ) ^ (-(s : ℂ)) = (x v : ℂ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    rw [hc, norm_inv, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hpos v)]
  dsimp only
  rw [he, Real.log_exp, primeIdealZetaSum_def, tsum_univ x]
  change 0 ≤ (∑' v, L v) - (∑' v, x v) ∧ _ ≤ _
  refine ⟨sub_nonneg.mpr (hxS.tsum_le_tsum (fun v ↦ (hlog v).1) hLS), ?_⟩
  have hu := hLS.tsum_le_tsum (fun v ↦ (hlog v).2) (hxS.add (hyS.mul_left 2))
  rw [hxS.tsum_add (hyS.mul_left 2), tsum_mul_left] at hu
  linarith

private theorem tendsto_neg_log_sub_one :
    Tendsto (fun s : ℝ ↦ -Real.log (s - 1)) (𝓝[>] 1) atTop := by
  have hshift : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · rw [← sub_self (1 : ℝ)]
      exact ((show Continuous (fun t : ℝ ↦ t - 1) by fun_prop).tendsto 1).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using sub_pos.mpr hs
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hshift)

/-- The sum over all prime ideals has leading term `-log (s - 1)` at one. -/
private theorem primeIdealZetaSum_univ_isEquivalent :
    primeIdealZetaSum (univ : Set (Primes(K))) ~[𝓝[>] 1]
      (fun s : ℝ ↦ -Real.log (s - 1)) := by
  let T := 𝓝[>] (1 : ℝ)
  let main (s : ℝ) := -Real.log (s - 1)
  let Z (s : ℝ) := ‖dedekindZeta K s‖
  have hmain : Tendsto main T atTop := tendsto_neg_log_sub_one
  have hres := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have hres' : Tendsto (fun s : ℝ ↦ (s - 1) * Z s) T (𝓝 (dedekindZeta_residue K)) := by
    rw [← Real.norm_of_nonneg (dedekindZeta_residue_pos K).le, ← Complex.norm_real]
    refine hres.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    change ‖(↑s - 1 : ℂ) * _‖ = _
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (le_of_lt hs))]
  have hlog := (Real.continuousAt_log (dedekindZeta_residue_ne_zero K)).tendsto.comp hres'
  have hbounded := hlog.isBigO_one ℝ
  let A := 2 * ∑' v : Primes(K), (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ))
  obtain ⟨B, hB⟩ := Asymptotics.isBigO_iff.mp hbounded
  have herror : (primeIdealZetaSum (univ : Set (Primes(K))) - main)
      =O[T] (fun _ ↦ (1 : ℝ)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨B + A, ?_⟩
    filter_upwards [hB, self_mem_nhdsWithin, hres'.eventually_ne (dedekindZeta_residue_ne_zero K)]
      with s hB hs hz
    have hs' : 1 < s := hs
    have h := log_dedekindZeta_sub_prime_sum K hs'
    dsimp only at h
    simp only [Function.comp_apply, Real.norm_eq_abs, Pi.sub_apply, main, abs_one,
      mul_one] at hB ⊢
    rw [Real.log_mul (sub_ne_zero.mpr hs'.ne') (right_ne_zero_of_mul hz)] at hB
    have hb := abs_le.mp hB
    dsimp only [Z] at hb
    exact abs_le.mpr ⟨by dsimp only [A]; linarith [h.2], by
      have ha : 0 ≤ A := by dsimp [A]; positivity
      linarith [h.1]⟩
  exact herror.trans_isLittleO ((Asymptotics.isLittleO_one_left_iff ℝ).mpr
    (tendsto_norm_atTop_atTop.comp hmain))

end PrimeSum

private abbrev AllSplit (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Primes(K)) :=
  ∀ Q : p.asIdeal.primesOver (𝓞 L),
    Q.val.ramificationIdx (𝓞 K) = 1 ∧ Q.val.inertiaDeg (𝓞 K) = 1

private theorem decomp_card (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (Q : Primes(L)) :
    Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) =
      Q.asIdeal.ramificationIdx (𝓞 K) * Q.asIdeal.inertiaDeg (𝓞 K) := by
  let p := Q.under (𝓞 K)
  let : Q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  rw [Ideal.card_stabilizer_eq (G := Gal(L/K)) p.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg p.asIdeal Q.asIdeal Gal(L/K)]

/-- If a prime splits in the intermediate field, every element of its
decomposition group fixes that field pointwise. -/
private theorem fixes_of_split (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [IsGalois ℚ L] (Q : Primes(L))
    (h : AllSplit ℚ F (Q.under (𝓞 ℚ))) (σ : MulAction.stabilizer Gal(L/ℚ) Q.asIdeal)
    (x : F) : σ.val (algebraMap F L x) = algebraMap F L x := by
  let : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  let q := Q.under (𝓞 F)
  let : Q.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  have hq : q.asIdeal.LiesOver (Q.under (𝓞 ℚ)).asIdeal :=
    ⟨(Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 F) Q.asIdeal).symm⟩
  obtain ⟨he, hf⟩ := h ⟨q.asIdeal, q.isPrime, hq⟩
  let D := MulAction.stabilizer Gal(L/F) Q.asIdeal
  let D' := MulAction.stabilizer Gal(L/ℚ) Q.asIdeal
  let i (τ : D) : D' := ⟨τ.val.restrictScalars ℚ, τ.property⟩
  have hi : Function.Injective i := fun a b hab ↦
    Subtype.ext (AlgEquiv.restrictScalars_injective ℚ (congrArg Subtype.val hab))
  have hcard : Nat.card D' = Nat.card D := by
    rw [decomp_card ℚ L Q, decomp_card F L Q,
      Ideal.ramificationIdx_tower (R := 𝓞 ℚ) q.asIdeal Q.asIdeal,
      Ideal.inertiaDeg_tower (R := 𝓞 ℚ) q.asIdeal Q.asIdeal]
    simp only [he, hf, one_mul]
  obtain ⟨τ, hτ⟩ := ((Nat.bijective_iff_injective_and_card i).mpr ⟨hi, hcard.symm⟩).2 σ
  rw [← hτ]
  exact τ.val.commutes x

private theorem split_iff_in_normal_closure (F L : Type*) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L] [IsGalois ℚ L] [IsNormalClosure ℚ F L]
    (p : Primes(ℚ)) : AllSplit ℚ F p ↔ AllSplit ℚ L p := by
  constructor
  · intro h q
    let Q : Primes(L) := ⟨q.val, q.property.1, Ideal.ne_bot_of_mem_primesOver
      p.ne_bot q.property⟩
    have hp : Q.under (𝓞 ℚ) = p := HeightOneSpectrum.ext q.property.2.over.symm
    have hfix (σ : MulAction.stabilizer Gal(L/ℚ) Q.asIdeal) (f : F →ₐ[ℚ] L) (x : F) :
        σ.val (f x) = f x := by
      let : Algebra F L := f.toRingHom.toAlgebra
      exact fixes_of_split F L Q (hp.symm ▸ h) σ x
    have hD : Subsingleton (MulAction.stabilizer Gal(L/ℚ) Q.asIdeal) :=
      ⟨fun a b ↦ by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro x
        have ht := (Algebra.IsAlgebraic.isNormalClosure_iff.mp
          (inferInstance : IsNormalClosure ℚ F L)).2
        have heq : normalClosure ℚ F L ≤
            Algebra.IsAlgebraic.toIntermediateField (a.val.toAlgHom.equalizer b.val.toAlgHom) := by
          apply normalClosure_le_iff.mpr
          rintro f y ⟨x, rfl⟩
          exact (hfix a f x).trans (hfix b f x).symm
        exact heq (ht ▸ IntermediateField.mem_top)⟩
    have h1 := decomp_card ℚ L Q
    rw [Nat.card_unique] at h1
    exact mul_eq_one.mp h1.symm
  · intro h q
    obtain ⟨r⟩ := (inferInstance : Nonempty (q.val.primesOver (𝓞 L)))
    have hr : r.val.LiesOver p.asIdeal := Ideal.LiesOver.trans r.val q.val p.asIdeal
    obtain ⟨he, hf⟩ := h ⟨r.val, r.property.1, hr⟩
    rw [Ideal.ramificationIdx_tower (R := 𝓞 ℚ) q.val r.val] at he
    rw [Ideal.inertiaDeg_tower (R := 𝓞 ℚ) q.val r.val] at hf
    exact ⟨(mul_eq_one.mp he).1, (mul_eq_one.mp hf).1⟩

section PrimeFibers

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def primeTowerEquiv : ((p : Primes(K)) × p.asIdeal.primesOver (𝓞 L)) ≃ Primes(L) where
  toFun q := ⟨q.2.val, q.2.property.1, Ideal.ne_bot_of_mem_primesOver q.1.ne_bot q.2.property⟩
  invFun Q := ⟨Q.under (𝓞 K), ⟨Q.asIdeal, Q.isPrime, ⟨rfl⟩⟩⟩
  right_inv _ := rfl
  left_inv := by
    rintro ⟨p, Q, hQ, hp⟩
    let v : Primes(L) := ⟨Q, hQ, Ideal.ne_bot_of_mem_primesOver p.ne_bot ⟨hQ, hp⟩⟩
    have he : v.under (𝓞 K) = p := HeightOneSpectrum.ext hp.over.symm
    apply Sigma.ext he
    have aux {a b : Primes(K)} (hab : a = b) (J : Ideal (𝓞 L))
        (ha : J ∈ a.asIdeal.primesOver (𝓞 L)) (hb : J ∈ b.asIdeal.primesOver (𝓞 L)) :
        HEq (⟨J, ha⟩ : a.asIdeal.primesOver (𝓞 L)) (⟨J, hb⟩ : b.asIdeal.primesOver (𝓞 L)) := by
      subst b
      rfl
    exact aux he Q _ _

private theorem finite_ramified_under :
    ∃ R : Finset (Primes(K)), ∀ p ∉ R, ∀ Q : p.asIdeal.primesOver (𝓞 L),
      Q.val.ramificationIdx (𝓞 K) = 1 := by
  classical
  let d := differentIdeal (𝓞 K) (𝓞 L)
  have hd : d ≠ 0 := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hd).toFinset
  refine ⟨T.image (HeightOneSpectrum.under (𝓞 K)), fun p hp Q ↦ ?_⟩
  let v : Primes(L) := ⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.property⟩
  have hn : ¬ Q.val ∣ d := fun h ↦ hp (Finset.mem_image.mpr
    ⟨v, (Ideal.finite_factors hd).mem_toFinset.mpr h, HeightOneSpectrum.ext Q.property.2.over.symm⟩)
  let : Algebra.IsUnramifiedAt (𝓞 K) Q.val := not_dvd_differentIdeal_iff.mp hn
  exact Q.val.ramificationIdx_eq_one (𝓞 K)

/-- In a Galois extension, a completely split prime accounts for exactly `[L : K]`
terms. Every other unramified prime has residue degree at least two throughout its fiber. -/
private theorem galois_prime_sum_error [IsGalois K L] :
    let split := {p : Primes(K) | AllSplit K L p}
    let d := (Module.finrank K L : ℝ)
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      |d * Set.primeIdealZetaSum split s - Set.primeIdealZetaSum (Set.univ : Set (Primes(L))) s| ≤ C := by
  classical
  intro split d
  obtain ⟨R, hR⟩ := finite_ramified_under K L
  let u (s : ℝ) (p : Primes(K)) := (p.asIdeal.absNorm : ℝ) ^ (-s)
  let bad (p : Primes(K)) := if p ∈ R then (1 : ℝ) else 0
  have hbad : Summable bad := summable_of_hasFiniteSupport (R.finite_toSet.subset (by
    intro p hp; by_contra h; exact hp (ite_eq_right h)))
  let err (p : Primes(K)) := d * (bad p + u 2 p)
  have herr : Summable err := (hbad.add (summable_prime_norm_rpow K (by norm_num))).mul_left d
  refine ⟨∑' p, err p, fun s hs ↦ ?_⟩
  let w (Q : Primes(L)) := (Q.asIdeal.absNorm : ℝ) ^ (-s)
  let a (p : Primes(K)) := ∑ Q : p.asIdeal.primesOver (𝓞 L), (Q.val.absNorm : ℝ) ^ (-s)
  let b (p : Primes(K)) := d * split.indicator (u s) p
  have hbS : Summable b := ((summable_prime_norm_rpow K hs).indicator split).mul_left d
  have hw : Summable w := summable_prime_norm_rpow L hs
  let e := primeTowerEquiv K L
  have hσ := e.summable_iff.mpr hw
  have haS : Summable a := by
    have h := hσ.sigma' (fun _ ↦ Summable.of_finite)
    simp only [tsum_fintype] at h
    exact h.congr (fun _ ↦ rfl)
  have htot : Set.primeIdealZetaSum (Set.univ : Set (Primes(L))) s = ∑' p, a p := by
    rw [Set.primeIdealZetaSum_def, tsum_univ w, ← e.tsum_eq w]
    change (∑' c, (w ∘ e) c) = _
    rw [hσ.tsum_sigma]
    simp only [tsum_fintype]
    rfl
  have hpart : d * Set.primeIdealZetaSum split s = ∑' p, b p := by
    rw [Set.primeIdealZetaSum_def, tsum_subtype split (u s), tsum_mul_left]
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hcomp (p) : b p ≤ a p ∧ a p ≤ b p + err p := by
    have hsum := Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 L)
    rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hsum
    have hcard : Fintype.card (p.asIdeal.primesOver (𝓞 L)) ≤ Module.finrank K L := by
      rw [← hsum, Fintype.card_eq_sum_ones]
      exact Finset.sum_le_sum fun Q _ ↦ Nat.mul_pos
        (Ideal.ramificationIdx_pos (𝓞 K) Q.val) (Ideal.inertiaDeg_pos Q.val (𝓞 K))
    have hnerr : 0 ≤ err p := mul_nonneg hd (add_nonneg (by dsimp [bad]; split <;> norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    by_cases hp : p ∈ split
    · have h := (show AllSplit K L p from hp)
      have hcard' : Fintype.card (p.asIdeal.primesOver (𝓞 L)) = Module.finrank K L := by
        rw [← hsum, Fintype.card_eq_sum_ones]
        exact Finset.sum_congr rfl fun Q _ ↦ by rw [(h Q).1, (h Q).2, one_mul]
      have hq (Q : p.asIdeal.primesOver (𝓞 L)) : Q.val.absNorm = p.asIdeal.absNorm := by
        rw [← Ideal.absNorm_pow_inertiaDeg p.asIdeal, (h Q).2, pow_one]
      have hab : a p = b p := by
        simp only [a, hq, Finset.sum_const, Finset.card_univ, hcard', nsmul_eq_mul, b,
          indicator_of_mem hp, d, u]
      rw [hab]
      exact ⟨le_rfl, le_add_of_nonneg_right hnerr⟩
    · rw [show b p = 0 by simp only [b, indicator_of_notMem hp, mul_zero], zero_add]
      refine ⟨Finset.sum_nonneg fun _ _ ↦ by positivity, ?_⟩
      have hbnd (Q : p.asIdeal.primesOver (𝓞 L)) :
          (Q.val.absNorm : ℝ) ^ (-s) ≤ bad p + u 2 p := by
        by_cases hram : p ∈ R
        · have hQ : 1 ≤ (Q.val.absNorm : ℝ) := by
            exact_mod_cast (HeightOneSpectrum.one_lt_absNorm (e ⟨p, Q⟩)).le
          exact (Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith)).trans
            (by
              dsimp only [bad]
              rw [ite_eq_left hram]
              exact le_add_of_nonneg_right (by dsimp [u]; positivity))
        · have hdeg : 2 ≤ Q.val.inertiaDeg (𝓞 K) := by
            have hpos := Ideal.inertiaDeg_pos Q.val (𝓞 K)
            by_contra! h
            apply hp
            intro P
            refine ⟨hR p hram P, ?_⟩
            rw [Ideal.inertiaDeg_eq_of_isGaloisGroup p.asIdeal P.val Q.val Gal(L/K)]
            omega
          dsimp only [bad, u]
          rw [ite_eq_right hram, zero_add, ← Ideal.absNorm_pow_inertiaDeg p.asIdeal Q.val, Nat.cast_pow,
            ← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm p).le)
          have : (2 : ℝ) ≤ Q.val.inertiaDeg (𝓞 K) := by exact_mod_cast hdeg
          nlinarith
      calc
        a p ≤ ∑ _Q : p.asIdeal.primesOver (𝓞 L), (bad p + u 2 p) := Finset.sum_le_sum fun Q _ ↦ hbnd Q
        _ ≤ err p := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by dsimp only [d]; exact_mod_cast hcard)
            (add_nonneg (by dsimp [bad]; split <;> norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [hpart, htot, abs_of_nonpos (sub_nonpos.mpr (hbS.tsum_le_tsum (fun p ↦ (hcomp p).1) haS))]
  have h := haS.tsum_le_tsum (fun p ↦ (hcomp p).2) (hbS.add herr)
  rw [hbS.tsum_add herr] at h
  linarith

private theorem galois_split_density [IsGalois K L] :
    Tendsto (fun s ↦ Set.primeIdealZetaSum {p : Primes(K) | AllSplit K L p} s /
      Set.primeIdealZetaSum (univ : Set (Primes(K))) s) (𝓝[>] 1)
      (𝓝 (1 / (Module.finrank K L : ℝ))) := by
  let T := 𝓝[>] (1 : ℝ)
  let d := (Module.finrank K L : ℝ)
  let B := Set.primeIdealZetaSum {p : Primes(K) | AllSplit K L p}
  let P := Set.primeIdealZetaSum (univ : Set (Primes(K)))
  let Q := Set.primeIdealZetaSum (univ : Set (Primes(L)))
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hQ := primeIdealZetaSum_univ_isEquivalent L
  have hP := primeIdealZetaSum_univ_isEquivalent K
  have htQ : Tendsto Q T atTop := hQ.tendsto_atTop_iff.mpr tendsto_neg_log_sub_one
  have htP : Tendsto P T atTop := hP.tendsto_atTop_iff.mpr tendsto_neg_log_sub_one
  obtain ⟨C, hC⟩ := galois_prime_sum_error K L
  have he : ((fun s ↦ d * B s) - Q) =O[T] (fun _ ↦ (1 : ℝ)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_one, mul_one] using hC s hs
  have hE : (fun s ↦ d * B s) ~[T] Q := he.trans_isLittleO
    ((Asymptotics.isLittleO_one_left_iff ℝ).mpr (tendsto_norm_atTop_atTop.comp htQ))
  have h := (Asymptotics.isEquivalent_iff_tendsto_one ((htP.eventually_gt_atTop 0).mono
    (fun s hs ↦ hs.ne'))).mp (hE.trans (hQ.trans hP.symm))
  change Tendsto (fun s ↦ B s / P s) T (𝓝 (1 / d))
  apply (h.div_const d).congr
  intro s
  change d * B s / P s / d = B s / P s
  rw [mul_div_assoc, mul_div_cancel_left₀ _ hd]

/-- The rational primes splitting completely in a number field have positive Dirichlet
density. Their density is the reciprocal of the degree of its normal closure. -/
theorem tendsto_split_primeIdealZetaSum_div (F : Type*) [Field F] [NumberField F] :
    Tendsto (fun s ↦ Set.primeIdealZetaSum {p : Primes(ℚ) |
      ∀ v : Primes(F), v.under (𝓞 ℚ) = p →
        v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1} s /
      Set.primeIdealZetaSum (univ : Set (Primes(ℚ))) s) (𝓝[>] 1)
        (𝓝 (1 / (Module.finrank ℚ (normalClosure ℚ F (AlgebraicClosure F)) : ℝ))) := by
  let L := normalClosure ℚ F (AlgebraicClosure F)
  let : NumberField L := NumberField.of_module_finite ℚ L
  let : Nonempty (F →ₐ[ℚ] AlgebraicClosure F) := ⟨IsScalarTower.toAlgHom _ _ _⟩
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
  let : Normal ℚ (AlgebraicClosure F) := ⟨fun _ ↦ IsAlgClosed.splits _⟩
  let : Normal ℚ L := normalClosure.normal _ _ _
  let : IsNormalClosure ℚ F L := isNormalClosure_normalClosure _ _ _
  let : IsGalois ℚ L := ⟨⟩
  have hsplit (p : Primes(ℚ)) :
      (∀ v : Primes(F), v.under (𝓞 ℚ) = p →
        v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1) ↔ AllSplit ℚ F p := by
    constructor
    · intro h Q
      let v : Primes(F) := ⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot Q.property⟩
      exact h v (HeightOneSpectrum.ext Q.property.2.over.symm)
    · intro h v hv
      exact h ⟨v.asIdeal, v.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hv).symm⟩⟩
  simpa only [hsplit, split_iff_in_normal_closure F L] using galois_split_density ℚ L

/-- Infinitely many rational primes split completely in a given number field. -/
theorem infinite_rational_primes_splitting_completely (F : Type*) [Field F] [NumberField F] :
    {p : Primes(ℚ) | ∀ v : Primes(F), v.under (𝓞 ℚ) = p →
      v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1}.Infinite := by
  let S := {p : Primes(ℚ) | ∀ v : Primes(F), v.under (𝓞 ℚ) = p →
    v.asIdeal.ramificationIdx (𝓞 ℚ) = 1 ∧ v.asIdeal.inertiaDeg (𝓞 ℚ) = 1}
  let P := Set.primeIdealZetaSum (univ : Set (Primes(ℚ)))
  have ht : Tendsto P (𝓝[>] 1) atTop :=
    (primeIdealZetaSum_univ_isEquivalent ℚ).tendsto_atTop_iff.mpr tendsto_neg_log_sub_one
  intro hfin
  have hzero : Tendsto (fun s ↦ S.primeIdealZetaSum s / P s) (𝓝[>] 1) (𝓝 0) := by
    apply squeeze_zero' _ _ (ht.const_div_atTop S.ncard)
    · exact .of_forall fun s ↦ div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact div_le_div_of_nonneg_right (Set.primeIdealZetaSum_le_card_of_finite hfin
        ((zero_le_one : (0 : ℝ) ≤ 1).trans (le_of_lt hs))) (univ.primeIdealZetaSum_nonneg s)
  have h := tendsto_nhds_unique (tendsto_split_primeIdealZetaSum_div F) hzero
  exact (one_div_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)).ne' h

end PrimeFibers

end RiemannMasullo
