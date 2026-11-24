module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Topology.ContinuousMap.Weierstrass
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Norm-ordered Euler products on the 1-line

Masullo, §B.7.2, pp. 648–653. The logarithmic series is grouped by prime-power
norm. The Euler products and the prime sum use a strict cutoff on prime norm.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Equation (B.7.2.2), p. 649. The function `g_n` uses the
oscillatory pole term with its constant term subtracted.
Deviation: At the removable singularity we use the limiting value `log n`
for positive `n`. -/
def heckePrimePowerTailOscillation (t₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if s = ⟨1, t₀⟩ then (Real.log n : ℂ)
  else ((n : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - s) - 1) / ((⟨1, t₀⟩ : ℂ) - s)

/-- Paper: Equations (B.7.2.2) and (B.7.2.12), pp. 649–650.
For positive `n`, the oscillatory term tends to `log n` at the pole ordinate.
Deviation: The printed proof gives the opposite sign for `g_n / log n`. -/
theorem heckePrimePowerTailOscillation_tendsto_at_pole
    (t₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (heckePrimePowerTailOscillation t₀ n)
      (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝 (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ z) (Real.log n : ℂ) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (n : ℂ)) (Or.inl hn')
    simpa [Complex.natCast_log] using h
  have hmap : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝 (⟨1, t₀⟩ : ℂ)) (𝓝 0) := by
        have h' :=
          (tendsto_const_nhds (x := (⟨1, t₀⟩ : ℂ)) (f := 𝓝 (⟨1, t₀⟩ : ℂ))).sub tendsto_id
        rw [sub_self] at h'
        exact h'
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
  refine ((hasDerivAt_iff_tendsto_slope.mp hd).comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ ⟨1, t₀⟩ := hs
  simp [heckePrimePowerTailOscillation, hs', slope_def_field]

/-- Paper: Remark B.7.2.2, p. 649. Index `k` represents the positive
exponent `k + 1`. The ideal character is zero on ramified prime powers. -/
def heckePrimePowerLogTerm (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) : ℂ :=
  heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
    ((k + 1 : ℕ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)

/-- Paper: Equation (B.7.2.15), p. 651. The exponent-one logarithmic term is
the ordinary prime term of the Hecke Dirichlet series. -/
theorem heckePrimePowerLogTerm_zero (χ : U[F]) (v : V[F]) (s : ℂ) :
    heckePrimePowerLogTerm χ v 0 s =
      heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal / (v.asIdeal.absNorm : ℂ) ^ s := by
  simp [heckePrimePowerLogTerm]

/-- Paper: Remark B.7.2.2 and Equation (B.7.2.4), p. 649. Dividing the
norm-grouped von Mangoldt coefficient by the logarithm of the norm gives
the coefficient of the logarithmic Euler series. The norms zero and one
have coefficient zero. -/
def heckePrimePowerLogCoefficient (χ : U[F]) (n : ℕ) : ℂ :=
  heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (Real.log n : ℂ)

/-- Paper: Remark B.7.2.2, p. 649. The coefficient at `n` sums
`χ(𝔭^m) / m` over the positive prime powers of norm exactly `n`. -/
theorem heckePrimePowerLogCoefficient_eq_sum (χ : U[F]) (n : ℕ) :
    heckePrimePowerLogCoefficient χ n =
      ∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
          ((a.val.2 + 1 : ℕ) : ℂ) := by
  classical
  let P (a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, by
      rw [map_pow]; exact a.property⟩
  have hP : Function.Injective P := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, j⟩, hj⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ hI.2)).to_subtype
  have : Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Finite.of_injective P hP
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  have : Fintype {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Fintype.ofFinite _
  delta heckePrimePowerLogCoefficient heckeLogDerivCoefficient
  rw [finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  symm
  refine Fintype.sum_of_injective P hP _ _ (fun I hI ↦ ?_) (fun a ↦ ?_)
  · have h : ¬ ∃ v : V[F], ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · refine hI ⟨⟨(v, k), ?_⟩, Subtype.ext he.symm⟩
        have h2 := I.property.2
        rw [he, map_pow] at h2
        exact h2
    simp [heckeIdealVonMangoldt, idealVonMangoldt, h]
  · obtain ⟨⟨v, k⟩, hk⟩ := a
    have hN : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hlog : Complex.log (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos hN).ne'
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [P, heckeIdealVonMangoldt, idealVonMangoldt_prime_pow v k.succ_pos]
    rw [← hk, Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp

/-- Paper: Remark B.7.2.2, p. 649. This is the Dirichlet term for each
integer norm, with the terms below the cutoff replaced by zero. -/
def heckePrimePowerLogTailTerm (χ : U[F]) (x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then LSeries.term (heckePrimePowerLogCoefficient χ) s n else 0

/-- Paper: Remark B.7.2.2, p. 649. At a positive integer norm equal to the
cutoff, the tail includes the full Dirichlet term for that norm. -/
theorem heckePrimePowerLogTailTerm_at_cutoff (χ : U[F]) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    heckePrimePowerLogTailTerm χ n s n =
      heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ s := by
  simp only [heckePrimePowerLogTailTerm, le_refl, ↓reduceIte]
  rw [LSeries.term_of_ne_zero hn.ne']

/-- Paper: Remark B.7.2.2, p. 649. The logarithmic tail sums the norm-grouped
terms in increasing order of integer norm, starting at the first norm at least `x`. -/
def heckePrimePowerLogTail (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)

/-- The norm of a prime-power logarithmic term is at most the inverse real power of the
ideal norm, since the character value has norm at most one and the exponent is positive. -/
private theorem heckePrimePowerLogTerm_norm_le (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) :
    ‖heckePrimePowerLogTerm χ v k s‖ ≤
      ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ (-s.re) := by
  have hN : (0 : ℝ) < ((v.asIdeal ^ (k + 1)).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ v.ne_bot))
  have hχ : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    split_ifs with h
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hpow : (0 : ℝ) < ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos hN _
  calc ‖heckePrimePowerLogTerm χ v k s‖
      = ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ /
          (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re) := by
        delta heckePrimePowerLogTerm
        rw [norm_div, norm_mul, Complex.norm_natCast,
          ← Complex.ofReal_natCast ((v.asIdeal ^ (k + 1)).absNorm),
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
    _ ≤ 1 / (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re) :=
        div_le_div_of_nonneg_right hχ (by positivity)
    _ ≤ 1 / ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re :=
        one_div_le_one_div_of_le hpow (le_mul_of_one_le_left hpow.le hk)
    _ = ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ (-s.re) := by
        rw [Real.rpow_neg hN.le, one_div]

/-- To the right of one, the prime-power logarithmic terms are summable over all prime
powers, by comparison with the convergent sum of inverse ideal-norm powers. -/
private theorem summable_heckePrimePowerLogTerm_of_one_lt_re (χ : U[F]) (s : halfPlane) :
    Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s) := by
  classical
  let P (a : V[F] × ℕ) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨a.1.asIdeal ^ (a.2 + 1), pow_ne_zero _ a.1.ne_bot⟩
  have hP : Function.Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  have hr : 1 < (s : ℂ).re := s.property
  have hs := ((summable_absNorm_rpow F hr).subtype (fun I ↦ I ≠ ⊥)).comp_injective hP
  exact hs.of_norm_bounded (fun a ↦ heckePrimePowerLogTerm_norm_le χ a.1 a.2 s)

/-- The prime powers of a fixed integer norm form a finite set, since their ideals are
nonzero ideals of that norm. -/
private theorem heckePrimePowerLogTail_fiber_finite (n : ℕ) :
    Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := by
  classical
  let P (a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, by
      rw [map_pow]; exact a.property⟩
  have hP : Function.Injective P := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, j⟩, hj⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ hI.2)).to_subtype
  exact Finite.of_injective P hP

/-- Paper: Remark B.7.2.2, p. 649, and the absolute convergence on p. 653.
To the right of one the same tail is the absolute sum over prime powers
whose norms are at least the cutoff. -/
theorem heckePrimePowerLogTail_hasSum_of_one_lt_re (χ : U[F]) (x : ℝ) (s : halfPlane) :
    HasSum (fun a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} ↦
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (heckePrimePowerLogTail χ x s) := by
  classical
  let S := {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}
  let f (a : S) : ℂ := heckePrimePowerLogTerm χ a.val.1 a.val.2 s
  let Nfn (a : S) : ℕ := a.val.1.asIdeal.absNorm ^ (a.val.2 + 1)
  have hsum : Summable f :=
    (summable_heckePrimePowerLogTerm_of_one_lt_re χ s).subtype
      (fun a ↦ x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ))
  have hfib := hsum.hasSum.tsum_fiberwise Nfn
  have hterm : (fun n : ℕ ↦ ∑' a : Nfn ⁻¹' {n}, f a) = heckePrimePowerLogTailTerm χ x s := by
    funext n
    by_cases hxn : x ≤ (n : ℝ)
    · by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty (↥(Nfn ⁻¹' {0})) := ⟨fun a ↦ by
          have ha : Nfn a.val = 0 := a.property
          have hpos : 0 < Nfn a.val :=
            pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr a.val.val.1.ne_bot)) _
          exact (Nat.pos_iff_ne_zero.mp hpos) ha⟩
        rw [tsum_empty]
        simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte, LSeries.term_zero]
      · simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte]
        let T := {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
        haveI : Finite T := heckePrimePowerLogTail_fiber_finite n
        haveI : Fintype T := Fintype.ofFinite _
        let e : ↥(Nfn ⁻¹' {n}) ≃ T :=
          { toFun := fun a ↦ ⟨a.val.val, a.property⟩
            invFun := fun b ↦ ⟨⟨b.val, by
              have hb : ((b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) : ℕ) : ℝ) = (n : ℝ) := by
                exact_mod_cast b.property
              exact hb.symm ▸ hxn⟩, b.property⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        haveI : Fintype ↥(Nfn ⁻¹' {n}) := Fintype.ofEquiv T e.symm
        rw [tsum_fintype,
          Fintype.sum_equiv e (fun a ↦ f a)
            (fun b ↦ heckePrimePowerLogTerm χ b.val.1 b.val.2 s) (fun _ ↦ rfl)]
        have hpoint (b : T) : heckePrimePowerLogTerm χ b.val.1 b.val.2 s =
            (heckeIdealValue (ideleClassNormTwist χ 0) (b.val.1.asIdeal ^ (b.val.2 + 1)) /
              ((b.val.2 + 1 : ℕ) : ℂ)) / (n : ℂ) ^ (s : ℂ) := by
          delta heckePrimePowerLogTerm
          have hNc : ((b.val.1.asIdeal ^ (b.val.2 + 1)).absNorm : ℂ) = (n : ℂ) := by
            have hp : (b.val.1.asIdeal ^ (b.val.2 + 1)).absNorm =
                b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) := by rw [map_pow]
            rw [hp]
            exact_mod_cast b.property
          rw [hNc, div_div]
        simp_rw [hpoint]
        rw [← Finset.sum_div, ← finsum_eq_sum_of_fintype,
          ← heckePrimePowerLogCoefficient_eq_sum, LSeries.term_of_ne_zero hn]
    · haveI : IsEmpty (↥(Nfn ⁻¹' {n})) := ⟨fun a ↦ by
        have ha : Nfn a.val = n := a.property
        have hx : x ≤ (Nfn a.val : ℝ) := a.val.property
        exact hxn (by rw [ha] at hx; exact hx)⟩
      rw [tsum_empty]
      simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte]
  have hfib' : HasSum (heckePrimePowerLogTailTerm χ x s) (∑' a : S, f a) := by
    rw [← hterm]
    exact hfib
  have htail : Summable (heckePrimePowerLogTailTerm χ x s) := ⟨_, hfib'⟩
  have hL : heckePrimePowerLogTail χ x s = ∑' a : S, f a := by
    delta heckePrimePowerLogTail
    rw [tsum_eq_of_summable_unconditional htail, hfib'.tsum_eq]
  rw [hL]
  exact hsum.hasSum

local notation "invLog(" n ")" => ((Real.log ((n : ℕ) : ℝ) : ℂ)⁻¹)

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. These
are the oscillatory summands weighted by the difference of reciprocal
logarithms at successive norms at or above the cutoff. -/
def heckePrimePowerTailOscillationTerm (t₀ x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then
    heckePrimePowerTailOscillation t₀ (n - 1) s * (invLog(n) - invLog(n - 1))
  else 0

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. The weighted
oscillatory terms are summable on the 1-line away from the pole.
Deviation: The cutoff is greater than two so the reciprocal logarithms
in the tail have nonzero denominators. -/
theorem summable_heckePrimePowerTailOscillationTerm (t₀ x t : ℝ) (hx : 2 < x) (ht : t ≠ t₀) :
    Summable (heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩) := by
  have hz0 : 0 < |t₀ - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm ht))
  have hnz : ‖(⟨1, t₀⟩ : ℂ) - ⟨1, t⟩‖ = |t₀ - t| := by
    have hz : (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ = ((t₀ - t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hg (k : ℕ) (hk : 0 < k) :
      ‖heckePrimePowerTailOscillation t₀ k ⟨1, t⟩‖ ≤ 2 / |t₀ - t| := by
    have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ ht (congrArg Complex.im h)
    have hre : ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩).re = 0 := by simp
    delta heckePrimePowerTailOscillation
    simp only [hne, ↓reduceIte]
    rw [norm_div, hnz]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_natCast_cpow_of_pos hk, hre, Real.rpow_zero, norm_one]
    norm_num
  let e : ℕ → ℝ := fun m ↦ (Real.log ((m + 2 : ℕ) : ℝ))⁻¹
  have he (m : ℕ) : e m = (Real.log ((m + 2 : ℕ) : ℝ))⁻¹ := rfl
  have he1 (m : ℕ) : e (m + 1) = (Real.log ((m + 3 : ℕ) : ℝ))⁻¹ := rfl
  have he0 (m : ℕ) : 0 ≤ e m :=
    inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega))
  have hanti' (m : ℕ) :
      (Real.log ((m + 3 : ℕ) : ℝ))⁻¹ ≤ (Real.log ((m + 2 : ℕ) : ℝ))⁻¹ := by
    apply inv_anti₀ (Real.log_pos (by norm_cast; omega))
    exact Real.log_le_log (by positivity) (by norm_cast; omega)
  have hanti (m : ℕ) : e (m + 1) ≤ e m := by
    rw [he1, he]
    exact hanti' m
  have hd : Summable fun m ↦ e m - e (m + 1) := by
    refine summable_of_sum_range_le (c := e 0) (fun m ↦ sub_nonneg.mpr (hanti m))
      fun n ↦ ?_
    rw [Finset.sum_range_sub']
    linarith [he0 n]
  rw [← summable_nat_add_iff 3]
  refine Summable.of_norm_bounded (hd.mul_left (2 / |t₀ - t|)) fun m ↦ ?_
  have hc : ‖((Real.log ((m + 3 : ℕ) : ℝ) : ℂ))⁻¹ - ((Real.log ((m + 3 - 1 : ℕ) : ℝ) : ℂ))⁻¹‖ =
      e m - e (m + 1) := by
    rw [show m + 3 - 1 = m + 2 by omega, he, he1, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (hanti' m))]
  delta heckePrimePowerTailOscillationTerm
  split_ifs
  · rw [norm_mul, hc]
    exact mul_le_mul_of_nonneg_right (hg _ (by omega)) (sub_nonneg.mpr (hanti m))
  · rw [norm_zero]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (hanti m))

/-- On the 1-line off the pole ordinate, every oscillatory term has norm at most
`2 / |t₀ - t|`. -/
private theorem heckePrimePowerLogTail_normTwist_osc_norm_le (t₀ t : ℝ) (ht : t ≠ t₀)
    (m : ℕ) : ‖heckePrimePowerTailOscillation t₀ m ⟨1, t⟩‖ ≤ 2 / |t₀ - t| := by
  have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ ht (congrArg Complex.im h)
  have hws : (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hre : ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩).re = 0 := by simp
  have hnz : ‖(⟨1, t₀⟩ : ℂ) - ⟨1, t⟩‖ = |t₀ - t| := by
    have hz : (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ = ((t₀ - t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpow : ‖(m : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩)‖ ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, Complex.zero_cpow hws, norm_zero]
      exact zero_le_one
    · rw [Complex.norm_natCast_cpow_of_pos hm, hre, Real.rpow_zero]
  delta heckePrimePowerTailOscillation
  simp only [hne, ↓reduceIte]
  rw [norm_div, hnz]
  gcongr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith

/-- Summation by parts against reciprocal logarithms: if the values of `A` beyond the
cutoff differ from the one at `⌈x⌉₊ - 1` by at most `δ`, the cutoff partial sums of
`(A n - A (n - 1)) / log n` are at most `δ / log (⌈x⌉₊ - 1)`. -/
private theorem heckePrimePowerLogTail_normTwist_abel (A : ℕ → ℂ) (x δ : ℝ)
    (hx : 2 < x) (hA : ∀ n : ℕ, ⌈x⌉₊ - 1 ≤ n → ‖A n - A (⌈x⌉₊ - 1)‖ ≤ δ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (A n - A (n - 1)) / (Real.log ((n : ℕ) : ℝ) : ℂ) else 0)‖ ≤
      δ * (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
  have hM : 3 ≤ ⌈x⌉₊ := by
    have h2 : (2 : ℝ) < ⌈x⌉₊ := hx.trans_le (Nat.le_ceil x)
    have : 2 < ⌈x⌉₊ := by exact_mod_cast h2
    omega
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hA _ le_rfl)
  have hLM : 0 ≤ (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.log_natCast_nonneg _)
  rcases lt_or_ge N ⌈x⌉₊ with hN | hN
  · rw [Finset.sum_eq_zero, norm_zero]
    · exact mul_nonneg hδ hLM
    · intro n hn
      exact ite_eq_right
        (fun h ↦ absurd (Nat.ceil_le.mpr h) (not_le.mpr ((Finset.mem_range.mp hn).trans hN)))
  · have halg : ∀ S u v w a b : ℂ, S + (u - v) / b - (u - w) * b⁻¹ =
        (S - (v - w) * a) + (v - w) * (a - b⁻¹) := by
      intro S u v w a b
      ring
    have key : ‖∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (A n - A (n - 1)) / (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) -
          (A (N - 1) - A (⌈x⌉₊ - 1)) * ((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹‖ ≤
        δ * ((Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((N - 1 : ℕ) : ℝ))⁻¹) := by
      induction N, hN using Nat.le_induction with
      | base =>
        rw [Finset.sum_eq_zero, sub_self, zero_mul, sub_zero, norm_zero, sub_self, mul_zero]
        intro n hn
        exact ite_eq_right
          (fun h ↦ absurd (Nat.ceil_le.mpr h) (not_le.mpr (Finset.mem_range.mp hn)))
      | succ N hN ih =>
        rw [Finset.sum_range_succ, ite_eq_left (Nat.ceil_le.mp hN), Nat.add_sub_cancel,
          halg _ _ _ _ ((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹ _]
        have h2 : (2 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ N - 1)
        have h3 : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
        have hanti : (Real.log (N : ℝ))⁻¹ ≤ (Real.log ((N - 1 : ℕ) : ℝ))⁻¹ :=
          inv_anti₀ (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) h3)
        have hdiff : ‖((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹ - ((Real.log (N : ℝ) : ℂ))⁻¹‖ =
            (Real.log ((N - 1 : ℕ) : ℝ))⁻¹ - (Real.log (N : ℝ))⁻¹ := by
          rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
            Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hanti)]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hdiff]
        have hB := mul_le_mul_of_nonneg_right (hA (N - 1) (Nat.sub_le_sub_right hN 1))
          (sub_nonneg.mpr hanti)
        linarith
    have hLN : 0 ≤ (Real.log ((N - 1 : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.log_natCast_nonneg _)
    have hnorm : ‖(A (N - 1) - A (⌈x⌉₊ - 1)) * ((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹‖ ≤
        δ * (Real.log ((N - 1 : ℕ) : ℝ))⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hA (N - 1) (Nat.sub_le_sub_right hN 1)) hLN
    have htri := norm_add_le
      (∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (A n - A (n - 1)) / (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) -
          (A (N - 1) - A (⌈x⌉₊ - 1)) * ((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹)
      ((A (N - 1) - A (⌈x⌉₊ - 1)) * ((Real.log ((N - 1 : ℕ) : ℝ) : ℂ))⁻¹)
    rw [sub_add_cancel] at htri
    linarith

/-- Beyond a positive cutoff, a tail term is the difference of consecutive integer cutoff
polynomials divided by the logarithm of the norm. -/
private theorem heckePrimePowerLogTail_normTwist_term_eq (χ : U[F]) (x : ℝ)
    (hx : 0 < x) (s : ℂ) (n : ℕ) :
    heckePrimePowerLogTailTerm χ x s n =
      if x ≤ (n : ℝ) then
        (heckeLogDerivPolynomial χ (n : ℝ) s -
          heckeLogDerivPolynomial χ ((n - 1 : ℕ) : ℝ) s) / (Real.log ((n : ℕ) : ℝ) : ℂ)
      else 0 := by
  delta heckePrimePowerLogTailTerm
  split_ifs with hxn
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
      refine ⟨n - 1, ?_⟩
      have h0 : (0 : ℝ) < n := hx.trans_le hxn
      have : 0 < n := by exact_mod_cast h0
      omega
    rw [Nat.add_sub_cancel]
    delta heckeLogDerivPolynomial
    rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Icc_succ_top (Nat.le_add_left 1 m),
      add_sub_cancel_left, LSeries.term_of_ne_zero (Nat.add_one_ne_zero m),
      LSeries.term_of_ne_zero (Nat.add_one_ne_zero m)]
    delta heckePrimePowerLogCoefficient
    rw [div_right_comm]
  · rfl

/-- If the integer cutoff polynomials beyond the cutoff differ from the one at `⌈x⌉₊ - 1`
by at most `δ`, every partial sum of the tail is at most `δ / log (⌈x⌉₊ - 1)`. -/
private theorem heckePrimePowerLogTail_normTwist_partial_le (χ : U[F]) (s : ℂ)
    (x δ : ℝ) (hx : 2 < x)
    (hA : ∀ n : ℕ, ⌈x⌉₊ - 1 ≤ n → ‖heckeLogDerivPolynomial χ (n : ℝ) s -
      heckeLogDerivPolynomial χ ((⌈x⌉₊ - 1 : ℕ) : ℝ) s‖ ≤ δ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x s n‖ ≤
      δ * (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
  have h := heckePrimePowerLogTail_normTwist_abel
    (fun n : ℕ ↦ heckeLogDerivPolynomial χ (n : ℝ) s) x δ hx hA N
  simpa only [heckePrimePowerLogTail_normTwist_term_eq χ x (by linarith) s]
    using h

/-- A difference of partial sums of the tail is a partial sum of the tail that starts
at the lower index. -/
private theorem heckePrimePowerLogTail_normTwist_sub_eq (χ : U[F]) (s : ℂ)
    (x : ℝ) (N₀ m : ℕ) (hx : x ≤ (N₀ : ℝ)) (hm : N₀ ≤ m) :
    ∑ n ∈ Finset.range m, heckePrimePowerLogTailTerm χ x s n -
        ∑ n ∈ Finset.range N₀, heckePrimePowerLogTailTerm χ x s n =
      ∑ n ∈ Finset.range m, heckePrimePowerLogTailTerm χ (N₀ : ℝ) s n := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [sub_self]
    symm
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    delta heckePrimePowerLogTailTerm
    exact ite_eq_right (by exact_mod_cast not_le.mpr (Finset.mem_range.mp hn))
  | succ m hm ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    have h1 : heckePrimePowerLogTailTerm χ x s m =
        heckePrimePowerLogTailTerm χ (N₀ : ℝ) s m := by
      delta heckePrimePowerLogTailTerm
      rw [ite_eq_left (hx.trans (by exact_mod_cast hm)), ite_eq_left (by exact_mod_cast hm)]
    rw [h1]
    ring

/-- Ordered partial sums whose differences beyond `N₀` are `O(1 / log (N₀ - 1))`,
uniformly on a set, converge uniformly there to the ordered sum. -/
private theorem heckePrimePowerLogTail_normTwist_tendstoUniformlyOn
    (u : ℕ → ℝ → ℂ) (K : Set ℝ) (C : ℝ) (N₁ : ℕ)
    (h : ∀ N₀ : ℕ, N₁ ≤ N₀ → ∀ m : ℕ, N₀ ≤ m → ∀ t ∈ K,
      ‖∑ n ∈ Finset.range m, u n t - ∑ n ∈ Finset.range N₀, u n t‖ ≤
        C * (Real.log ((N₀ - 1 : ℕ) : ℝ))⁻¹) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun t : ℝ ↦ ∑ n ∈ Finset.range N, u n t)
      (fun t : ℝ ↦ tsum (fun n ↦ u n t) (SummationFilter.conditional ℕ)) atTop K := by
  have hL0 : Tendsto (fun N : ℕ ↦ C * (Real.log ((N - 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ ((N - 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
    have h2 := (Real.tendsto_log_atTop.comp h1).inv_tendsto_atTop
    simpa using h2.const_mul C
  have hcauchy : UniformCauchySeqOn
      (fun N : ℕ ↦ fun t : ℝ ↦ ∑ n ∈ Finset.range N, u n t) atTop K := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ρ hρ
    obtain ⟨N₀, hN₀, hN₁⟩ := ((hL0.eventually (gt_mem_nhds (half_pos hρ))).and
      (eventually_ge_atTop N₁)).exists
    refine ⟨N₀, fun m hm n hn t ht ↦ ?_⟩
    have hm' := h N₀ hN₁ m hm t ht
    have hn' := h N₀ hN₁ n hn t ht
    change dist (∑ k ∈ Finset.range m, u k t) (∑ k ∈ Finset.range n, u k t) < ρ
    rw [dist_eq_norm, ← sub_sub_sub_cancel_right _ _ (∑ k ∈ Finset.range N₀, u k t)]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  refine hcauchy.tendstoUniformlyOn_of_tendsto fun t ht ↦ ?_
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete (hcauchy.cauchySeq ht)
  have hsum : HasSum (fun n ↦ u n t) a (SummationFilter.conditional ℕ) := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    exact ha
  rw [hsum.tsum_eq]
  exact ha

/-- For a cutoff at least three, `1 / log (⌈x⌉₊ - 1)` is at most `2 / log x`. -/
private theorem heckePrimePowerLogTail_normTwist_inv_log_le (x : ℝ)
    (hx : 3 ≤ x) : (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ ≤ 2 / Real.log x := by
  have hM1 : x - 1 ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌈x⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
    rw [Nat.cast_sub h1, Nat.cast_one]
    linarith [Nat.le_ceil x]
  have hlogM : 0 < Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsq : x ≤ ((⌈x⌉₊ - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hlog : Real.log x ≤ 2 * Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h
  rw [inv_eq_one_div, div_le_div_iff₀ hlogM hlogx]
  linarith

/-- Splitting a sequence `g` off the differences of `A`: beyond the cutoff, the partial
sums of `((A n - g n) - (A (n - 1) - g (n - 1))) / log n` are those of
`(A n - A (n - 1)) / log n`, plus the endpoint term at `⌈x⌉₊ - 1`, plus the weighted
sums of `g`, minus the endpoint term at `N - 1`. -/
private theorem heckePrimePowerLogTail_normTwist_combine (A g : ℕ → ℂ) (x : ℝ) (N : ℕ)
    (hN : ⌈x⌉₊ ≤ N) :
    ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        ((A n - g n) - (A (n - 1) - g (n - 1))) / (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) =
      ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (A n - A (n - 1)) / (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) +
      g (⌈x⌉₊ - 1) * invLog(⌈x⌉₊ - 1) +
      ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        g (n - 1) * (invLog(n) - invLog(n - 1)) else 0) -
      g (N - 1) * invLog(N - 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h0 : ∀ u : ℕ → ℂ,
        ∑ n ∈ Finset.range ⌈x⌉₊, (if x ≤ (n : ℝ) then u n else 0) = 0 := by
      intro u
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      exact ite_eq_right
        (fun h ↦ absurd (Nat.ceil_le.mpr h) (not_le.mpr (Finset.mem_range.mp hn)))
    rw [h0, h0, h0]
    ring
  | succ N hN ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      ite_eq_left (Nat.ceil_le.mp hN), ite_eq_left (Nat.ceil_le.mp hN),
      ite_eq_left (Nat.ceil_le.mp hN), Nat.add_sub_cancel]
    ring

/-- A difference of cutoff partial sums is a partial sum whose cutoff is the lower
index. -/
private theorem heckePrimePowerLogTail_normTwist_cutoff_sub (u : ℕ → ℂ) (x : ℝ) (N₀ m : ℕ)
    (hx : x ≤ (N₀ : ℝ)) (hm : N₀ ≤ m) :
    ∑ n ∈ Finset.range m, (if x ≤ (n : ℝ) then u n else 0) -
        ∑ n ∈ Finset.range N₀, (if x ≤ (n : ℝ) then u n else 0) =
      ∑ n ∈ Finset.range m, (if (N₀ : ℝ) ≤ (n : ℝ) then u n else 0) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [sub_self]
    symm
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    exact ite_eq_right (by exact_mod_cast not_le.mpr (Finset.mem_range.mp hn))
  | succ m hm ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih,
      ite_eq_left (hx.trans (by exact_mod_cast hm)), ite_eq_left (by exact_mod_cast hm)]
    ring

/-- Paper: Theorem B.7.2.1(1), pp. 649–651. For a pure norm character,
the grouped logarithmic tail converges uniformly on compact sets away from
the pole. The oscillatory terms give the displayed main term and the continuous
error is bounded uniformly by `2 ε / log x`.
Deviation: The formula holds for all sufficiently large real cutoffs. Partial summation
uses only integer endpoints, including `M - 1`. The threshold exceeds two. -/
theorem heckePrimePowerLogTail_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        heckePrimePowerLogTail χ x ⟨1, t⟩ =
          -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
            error t - ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨3, by norm_num, fun x _ ↦ ⟨tendstoUniformlyOn_empty, fun _ ↦ 0,
      continuousOn_empty _, fun t ht ↦ absurd ht (Set.notMem_empty t)⟩⟩
  obtain ⟨D, hD0, hg⟩ : ∃ D : ℝ, 0 ≤ D ∧ ∀ (m : ℕ), ∀ t ∈ K,
      ‖heckePrimePowerTailOscillation t₀ m ⟨1, t⟩‖ ≤ D := by
    obtain ⟨t₁, ht₁K, hmin⟩ := hK.exists_isMinOn hKne
      ((continuous_const.sub continuous_id).abs.continuousOn (s := K)
        (f := fun t : ℝ ↦ |t₀ - t|))
    have hd : 0 < |t₀ - t₁| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hpole (h ▸ ht₁K))
    refine ⟨2 / |t₀ - t₁|, by positivity, fun m t ht ↦ ?_⟩
    exact (heckePrimePowerLogTail_normTwist_osc_norm_le t₀ t
      (fun h ↦ hpole (h ▸ ht)) m).trans
        (div_le_div_of_nonneg_left (by norm_num) hd (isMinOn_iff.mp hmin t ht))
  obtain ⟨Z, hZ, hZS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s := fun s ↦ by
    have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
    rw [← heckeGammaFactor_one] at h
    change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
    rw [hZS s]
    exact mul_left_cancel₀
      (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (zero_lt_one.trans s.property)) h
  have hline : Continuous (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) := by
    have hfun : (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ 1 + (t : ℂ) * Complex.I := by
      funext t
      apply Complex.ext <;> simp
    rw [hfun]
    fun_prop
  have hI : (1 + Complex.I * (t₀ : ℂ) : ℂ) = ⟨1, t₀⟩ := by
    apply Complex.ext <;> simp
  obtain ⟨error₁, herr, hunif⟩ := heckeLogDerivPolynomial_normTwist χ t₀ hχ Z hZ hZSeries
    ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' K) (hK.image hline) (by rintro _ ⟨t, -, rfl⟩; rfl)
    (by
      rintro ⟨t, ht, he⟩
      rw [hI] at he
      have htt : t = t₀ := congrArg Complex.im he
      exact hpole (htt ▸ ht))
    (b := 1) one_pos
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n → ∀ t ∈ K,
      ‖error₁ (n : ℝ) ⟨1, t⟩‖ < ε / 4 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / 4) (by positivity)
    rw [eventually_inf_principal, eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨⌈a⌉₊, fun n hn t ht ↦ ?_⟩
    have h1 := ha n (Nat.ceil_le.mp hn) (Or.inl ⟨(n : ℤ), Int.cast_natCast n⟩) ⟨1, t⟩
      ⟨t, ht, rfl⟩
    simpa using h1
  have hmain : ∀ n : ℕ, 2 ≤ n → ∀ t ∈ K,
      heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
          heckePrimePowerTailOscillation t₀ n ⟨1, t⟩ =
        -logDeriv Z (⟨1, t⟩ - Complex.I * t₀) + 1 / ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩) +
          error₁ (n : ℝ) ⟨1, t⟩ := by
    intro n hn t ht
    have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ by
      have htt : t = t₀ := congrArg Complex.im h
      exact hpole (htt ▸ ht)
    rw [(herr n h1).2 ⟨1, t⟩ rfl (by rw [hI]; exact hne), hI, Complex.ofReal_natCast]
    delta heckePrimePowerTailOscillation
    simp only [hne, ↓reduceIte]
    ring
  have hediff : ∀ n k : ℕ, m₀ ≤ n → m₀ ≤ k → ∀ t ∈ K,
      ‖error₁ (n : ℝ) ⟨1, t⟩ - error₁ (k : ℝ) ⟨1, t⟩‖ ≤ ε / 2 := by
    intro n k hn hk t ht
    refine (norm_sub_le _ _).trans ?_
    linarith [hm₀ n hn t ht, hm₀ k hk t ht]
  have hPdiff : ∀ n k : ℕ, m₀ + 2 ≤ n → m₀ + 2 ≤ k → ∀ t ∈ K,
      ‖heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
        heckeLogDerivPolynomial χ (k : ℝ) ⟨1, t⟩‖ ≤ 2 * D + ε / 2 := by
    intro n k hn hk t ht
    have hn' := hmain n (by omega) t ht
    have hk' := hmain k (by omega) t ht
    have hsplit : heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
        heckeLogDerivPolynomial χ (k : ℝ) ⟨1, t⟩ =
        (heckePrimePowerTailOscillation t₀ n ⟨1, t⟩ -
          heckePrimePowerTailOscillation t₀ k ⟨1, t⟩) +
          (error₁ (n : ℝ) ⟨1, t⟩ - error₁ (k : ℝ) ⟨1, t⟩) := by
      linear_combination hn' - hk'
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_)
      (hediff n k (by omega) (by omega) t ht))
    linarith [hg n t ht, hg k t ht]
  have hm₀0 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
  refine ⟨(m₀ : ℝ) + 3, by linarith, fun x hx ↦ ?_⟩
  have hx3 : (m₀ : ℝ) + 3 ≤ x := hx
  have hx2 : 2 < x := by linarith
  have hM : m₀ + 3 ≤ ⌈x⌉₊ := by
    have h : ((m₀ + 3 : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) := by
      push_cast
      exact hx3.trans (Nat.le_ceil x)
    exact_mod_cast h
  have hpart : ∀ y : ℝ, x ≤ y → ∀ N : ℕ, ∀ t ∈ K,
      ‖∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ y ⟨1, t⟩ n‖ ≤
        (2 * D + ε / 2) * (Real.log ((⌈y⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
    intro y hy N t ht
    have hMy : m₀ + 3 ≤ ⌈y⌉₊ := hM.trans (Nat.ceil_le_ceil hy)
    exact heckePrimePowerLogTail_normTwist_partial_le χ ⟨1, t⟩ y _
      (by linarith) (fun n hn ↦ hPdiff n _ (by omega) (by omega) t ht) N
  have hunifx : TendstoUniformlyOn
      (fun N : ℕ ↦ fun t : ℝ ↦
        ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
      (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K := by
    refine heckePrimePowerLogTail_normTwist_tendstoUniformlyOn
      (fun n t ↦ heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n) K (2 * D + ε / 2) ⌈x⌉₊
      fun N₀ hN₀ m hm t ht ↦ ?_
    have hxN₀ : x ≤ (N₀ : ℝ) := Nat.ceil_le.mp hN₀
    rw [heckePrimePowerLogTail_normTwist_sub_eq χ ⟨1, t⟩ x N₀ m hxN₀ hm]
    have hp := hpart (N₀ : ℝ) hxN₀ m t ht
    rwa [Nat.ceil_natCast] at hp
  have hEpart : ∀ y : ℝ, x ≤ y → ∀ N : ℕ, ∀ t ∈ K,
      ‖∑ n ∈ Finset.range N, (if y ≤ (n : ℝ) then
        (error₁ (n : ℝ) ⟨1, t⟩ - error₁ ((n - 1 : ℕ) : ℝ) ⟨1, t⟩) /
          (Real.log ((n : ℕ) : ℝ) : ℂ) else 0)‖ ≤
        ε / 2 * (Real.log ((⌈y⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
    intro y hy N t ht
    have hMy : m₀ + 3 ≤ ⌈y⌉₊ := hM.trans (Nat.ceil_le_ceil hy)
    exact heckePrimePowerLogTail_normTwist_abel
      (fun n : ℕ ↦ error₁ (n : ℝ) ⟨1, t⟩) y (ε / 2) (by linarith)
      (fun n hn ↦ hediff n _ (by omega) (by omega) t ht) N
  let u : ℕ → ℝ → ℂ := fun n t ↦ if x ≤ (n : ℝ) then
    (error₁ (n : ℝ) ⟨1, t⟩ - error₁ ((n - 1 : ℕ) : ℝ) ⟨1, t⟩) /
      (Real.log ((n : ℕ) : ℝ) : ℂ) else 0
  have hEunif : TendstoUniformlyOn
      (fun N : ℕ ↦ fun t : ℝ ↦ ∑ n ∈ Finset.range N, u n t)
      (fun t : ℝ ↦ tsum (fun n ↦ u n t) (SummationFilter.conditional ℕ)) atTop K := by
    refine heckePrimePowerLogTail_normTwist_tendstoUniformlyOn u K (ε / 2)
      ⌈x⌉₊ fun N₀ hN₀ m hm t ht ↦ ?_
    have hxN₀ : x ≤ (N₀ : ℝ) := Nat.ceil_le.mp hN₀
    simp only [u]
    rw [heckePrimePowerLogTail_normTwist_cutoff_sub _ x N₀ m hxN₀ hm]
    have hp := hEpart (N₀ : ℝ) hxN₀ m t ht
    rwa [Nat.ceil_natCast] at hp
  have hEid : ∀ N : ℕ, ⌈x⌉₊ ≤ N → ∀ t ∈ K, ∑ n ∈ Finset.range N, u n t =
      ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n +
      heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
      ∑ n ∈ Finset.range N, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n -
      heckePrimePowerTailOscillation t₀ (N - 1) ⟨1, t⟩ * invLog(N - 1) := by
    intro N hN t ht
    have hcomb := heckePrimePowerLogTail_normTwist_combine
      (fun n : ℕ ↦ heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩)
      (fun n : ℕ ↦ heckePrimePowerTailOscillation t₀ n ⟨1, t⟩) x N hN
    beta_reduce at hcomb
    have h1 : ∑ n ∈ Finset.range N, u n t = ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        ((heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
            heckePrimePowerTailOscillation t₀ n ⟨1, t⟩) -
          (heckeLogDerivPolynomial χ ((n - 1 : ℕ) : ℝ) ⟨1, t⟩ -
            heckePrimePowerTailOscillation t₀ (n - 1) ⟨1, t⟩)) /
          (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      simp only [u]
      split_ifs with hxn
      · have hn3 : 3 ≤ n := by
          have h2 : (2 : ℝ) < n := hx2.trans_le hxn
          have : 2 < n := by exact_mod_cast h2
          omega
        rw [hmain n (by omega) t ht, hmain (n - 1) (by omega) t ht]
        congr 1
        ring
      · rfl
    have h2 : ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
          heckeLogDerivPolynomial χ ((n - 1 : ℕ) : ℝ) ⟨1, t⟩) /
            (Real.log ((n : ℕ) : ℝ) : ℂ) else 0) =
        ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n :=
      Finset.sum_congr rfl fun n _ ↦
        (heckePrimePowerLogTail_normTwist_term_eq χ x (by linarith)
          ⟨1, t⟩ n).symm
    rw [h1, hcomb, h2]
    rfl
  have hElim : ∀ t ∈ K, Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, u n t) atTop
      (𝓝 (heckePrimePowerLogTail χ x ⟨1, t⟩ +
        heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
        ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n)) := by
    intro t ht
    have htne : t ≠ t₀ := fun h ↦ hpole (h ▸ ht)
    have h1 := hunifx.tendsto_at ht
    have h2 :=
      (summable_heckePrimePowerTailOscillationTerm t₀ x t hx2 htne).hasSum.tendsto_sum_nat
    have h3 : Tendsto (fun N : ℕ ↦
        heckePrimePowerTailOscillation t₀ (N - 1) ⟨1, t⟩ * invLog(N - 1)) atTop (𝓝 0) := by
      have hL : Tendsto (fun N : ℕ ↦ D * (Real.log ((N - 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
        have h1 : Tendsto (fun N : ℕ ↦ ((N - 1 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
        have h2 := (Real.tendsto_log_atTop.comp h1).inv_tendsto_atTop
        simpa using h2.const_mul D
      refine squeeze_zero_norm (fun N ↦ ?_) hL
      rw [norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hg _ t ht)
        (inv_nonneg.mpr (Real.log_natCast_nonneg _))
    have h4 := ((h1.add (tendsto_const_nhds
      (x := heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1)))).add
        h2).sub h3
    rw [sub_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with N hN
    exact (hEid N hN t ht).symm
  refine ⟨hunifx, fun t ↦ heckePrimePowerLogTail χ x ⟨1, t⟩ +
    heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
    ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n, ?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · have hEq : Set.EqOn
        (fun t : ℝ ↦ tsum (fun n ↦ u n t) (SummationFilter.conditional ℕ))
        (fun t ↦ heckePrimePowerLogTail χ x ⟨1, t⟩ +
          heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
          ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n) K :=
      fun t ht ↦ tendsto_nhds_unique (hEunif.tendsto_at ht) (hElim t ht)
    refine (hEunif.continuousOn (Eventually.of_forall fun N ↦ ?_).frequently).congr hEq.symm
    refine (continuous_finsetSum _ fun n _ ↦ ?_).continuousOn
    simp only [u]
    split_ifs with hxn
    · have hn3 : 3 ≤ n := by
        have h2 : (2 : ℝ) < n := hx2.trans_le hxn
        have : 2 < n := by exact_mod_cast h2
        omega
      have hc : ∀ k : ℕ, 2 ≤ k → Continuous (fun t : ℝ ↦ error₁ (k : ℝ) ⟨1, t⟩) :=
        fun k hk ↦ ((herr k (by exact_mod_cast (by omega : 1 < k))).1.continuousOn
          ).comp_continuous hline (fun t ↦ rfl)
      exact ((hc n (by omega)).sub (hc (n - 1) (by omega))).div_const _
    · exact continuous_const
  · have hle := le_of_tendsto' (hElim t ht).norm fun N ↦ hEpart x le_rfl N t ht
    have hinv := heckePrimePowerLogTail_normTwist_inv_log_le x (by linarith)
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    calc _ ≤ ε / 2 * (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ := hle
      _ ≤ ε / 2 * (2 / Real.log x) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ε / Real.log x := by ring
      _ ≤ 2 * ε / Real.log x := by
          rw [div_le_div_iff_of_pos_right hlogx]
          linarith
  · ring

/-- Paper: Theorem B.7.2.1(2), pp. 649–651. For a character nontrivial on
the norm-one subgroup the grouped tail converges uniformly on each compact set
on the 1-line. Its limit is continuous and uniformly smaller than `2 ε / log x`.
Deviation: The compact set of ordinates refers to `1 + iK`, as in the
equation and the convergence clause. -/
theorem heckePrimePowerLogTail_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ContinuousOn (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) K ∧
      ∀ t ∈ K, ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ < 2 * ε / Real.log x := by
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation χ
  have hline : Continuous (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) := by
    have hfun : (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ 1 + (t : ℂ) * Complex.I := by
      funext t
      apply Complex.ext <;> simp
    rw [hfun]
    fun_prop
  obtain ⟨error, herr, hunif⟩ := heckeLogDerivPolynomial_of_nontrivial_on_normOne χ hχ L hL
    hSeries ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' K) (hK.image hline)
    (by rintro _ ⟨t, -, rfl⟩; rfl) (b := 1) one_pos
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, ∀ n : ℕ, m₀ ≤ n → ∀ t ∈ K,
      ‖error (n : ℝ) ⟨1, t⟩‖ < ε / 4 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / 4) (by positivity)
    rw [eventually_inf_principal, eventually_atTop] at h
    obtain ⟨a, ha⟩ := h
    refine ⟨⌈a⌉₊, fun n hn t ht ↦ ?_⟩
    have h1 := ha n (Nat.ceil_le.mp hn) (Or.inl ⟨(n : ℤ), Int.cast_natCast n⟩) ⟨1, t⟩
      ⟨t, ht, rfl⟩
    simpa using h1
  have hdiff : ∀ n k : ℕ, m₀ + 2 ≤ n → m₀ + 2 ≤ k → ∀ t ∈ K,
      ‖heckeLogDerivPolynomial χ (n : ℝ) ⟨1, t⟩ -
        heckeLogDerivPolynomial χ (k : ℝ) ⟨1, t⟩‖ ≤ ε / 2 := by
    intro n k hn hk t ht
    have h1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have h2 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
    rw [(herr n h1).2 ⟨1, t⟩ rfl, (herr k h2).2 ⟨1, t⟩ rfl, add_sub_add_left_eq_sub]
    refine (norm_sub_le _ _).trans ?_
    linarith [hm₀ n (by omega) t ht, hm₀ k (by omega) t ht]
  have hm₀0 : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
  refine ⟨(m₀ : ℝ) + 3, by linarith, fun x hx ↦ ?_⟩
  have hx3 : (m₀ : ℝ) + 3 ≤ x := hx
  have hM : m₀ + 3 ≤ ⌈x⌉₊ := by
    have h : ((m₀ + 3 : ℕ) : ℝ) ≤ (⌈x⌉₊ : ℝ) := by
      push_cast
      exact hx3.trans (Nat.le_ceil x)
    exact_mod_cast h
  have hpart : ∀ y : ℝ, x ≤ y → ∀ N : ℕ, ∀ t ∈ K,
      ‖∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ y ⟨1, t⟩ n‖ ≤
        ε / 2 * (Real.log ((⌈y⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
    intro y hy N t ht
    have hMy : m₀ + 3 ≤ ⌈y⌉₊ := hM.trans (Nat.ceil_le_ceil hy)
    exact heckePrimePowerLogTail_normTwist_partial_le χ ⟨1, t⟩ y (ε / 2)
      (by linarith) (fun n hn ↦ hdiff n _ (by omega) (by omega) t ht) N
  have hunifx : TendstoUniformlyOn
      (fun N : ℕ ↦ fun t : ℝ ↦
        ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
      (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K := by
    refine heckePrimePowerLogTail_normTwist_tendstoUniformlyOn
      (fun n t ↦ heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n) K (ε / 2) ⌈x⌉₊
      fun N₀ hN₀ m hm t ht ↦ ?_
    have hxN₀ : x ≤ (N₀ : ℝ) := Nat.ceil_le.mp hN₀
    rw [heckePrimePowerLogTail_normTwist_sub_eq χ ⟨1, t⟩ x N₀ m hxN₀ hm]
    have hp := hpart (N₀ : ℝ) hxN₀ m t ht
    rwa [Nat.ceil_natCast] at hp
  refine ⟨hunifx, ?_, fun t ht ↦ ?_⟩
  · refine hunifx.continuousOn (Eventually.of_forall fun N ↦ ?_).frequently
    refine (continuous_finsetSum _ fun n _ ↦ ?_).continuousOn
    delta heckePrimePowerLogTailTerm
    split_ifs
    · rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]
        exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        exact continuous_const.div (hline.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn)))
          (fun t h ↦ Nat.cast_ne_zero.mpr hn ((Complex.cpow_eq_zero_iff _ _).mp h).1)
    · exact continuous_const
  · have hlim := hunifx.tendsto_at ht
    have hle : ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ ≤
        ε / 2 * (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ :=
      le_of_tendsto' hlim.norm fun N ↦ hpart x le_rfl N t ht
    have hinv := heckePrimePowerLogTail_normTwist_inv_log_le x (by linarith)
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    calc ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖
        ≤ ε / 2 * (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ := hle
      _ ≤ ε / 2 * (2 / Real.log x) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ε / Real.log x := by ring
      _ < 2 * ε / Real.log x := by
          rw [div_lt_div_iff_of_pos_right hlogx]
          linarith

-- TODO(paper-gap): The proof on p. 651 uses a uniform bound for the Perron error
-- on the entire 1-line. The compact-set estimates of §B.7.1 suffice here.

/-- Paper: Equation (B.7.2.15), p. 651. This finite set contains the
finite places whose prime ideals have norm strictly below `x`. -/
def heckePrimesBelow (F : Type*) [Field F] [NumberField F] (x : ℝ) : Finset (V[F]) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F)
    (⌈x⌉₊ - 1)).toFinset

/-- Paper: Equation (B.7.2.15), p. 651. The strict cutoff excludes primes of
norm exactly `x`, including when `x` is an integer. -/
theorem heckePrimesBelow_mem_iff (v : V[F]) (x : ℝ) :
    v ∈ heckePrimesBelow F x ↔ (v.asIdeal.absNorm : ℝ) < x := by
  have hN : v.asIdeal.absNorm ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  simp only [heckePrimesBelow, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [← Nat.lt_ceil]
  omega

/-- Beyond the first integer at or above the cutoff, the full partial sums of the
logarithmic series are a fixed initial sum plus the partial sums of the tail. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_sum_term
    (χ : U[F]) (x : ℝ) (s : ℂ) (m : ℕ) (hm : ⌈x⌉₊ ≤ m) :
    ∑ n ∈ Finset.range m, LSeries.term (heckePrimePowerLogCoefficient χ) s n =
      ∑ n ∈ Finset.range ⌈x⌉₊, LSeries.term (heckePrimePowerLogCoefficient χ) s n +
        ∑ n ∈ Finset.range m, heckePrimePowerLogTailTerm χ x s n := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h0 : ∑ n ∈ Finset.range ⌈x⌉₊, heckePrimePowerLogTailTerm χ x s n = 0 := by
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      delta heckePrimePowerLogTailTerm
      exact ite_eq_right
        (fun h ↦ absurd (Nat.ceil_le.mpr h) (not_le.mpr (Finset.mem_range.mp hn)))
    rw [h0, add_zero]
  | succ m hm ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, add_assoc]
    congr 2
    delta heckePrimePowerLogTailTerm
    exact (ite_eq_left (Nat.ceil_le.mp hm)).symm

/-- The partial sums of the logarithmic series split into the prime sum below the
cutoff and a finite sum over higher prime powers. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_regroup
    (χ : U[F]) (s : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, LSeries.term (heckePrimePowerLogCoefficient χ) s n =
      ∑ v ∈ heckePrimesBelow F (N : ℝ), heckePrimePowerLogTerm χ v 0 s +
        ∑ a ∈ ((heckePrimesBelow F (N : ℝ)) ×ˢ (Finset.range N)).filter
          (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 2) < N),
          heckePrimePowerLogTerm χ a.1 (a.2 + 1) s := by
  classical
  have hPB : ∀ v : V[F], v ∈ heckePrimesBelow F (N : ℝ) ↔ v.asIdeal.absNorm < N := by
    intro v
    rw [heckePrimesBelow_mem_iff, Nat.cast_lt]
  let g : V[F] × ℕ → ℕ := fun a ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)
  let A : Finset (V[F] × ℕ) := (heckePrimesBelow F (N : ℝ)).image (fun v ↦ (v, 0)) ∪
    (((heckePrimesBelow F (N : ℝ)) ×ˢ (Finset.range N)).filter
      (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 2) < N)).image (fun a ↦ (a.1, a.2 + 1))
  have hmemA : ∀ a : V[F] × ℕ, a ∈ A ↔ g a < N := by
    rintro ⟨v, k⟩
    have h2 : 2 ≤ v.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v
    change (v, k) ∈ (_ ∪ _ : Finset (V[F] × ℕ)) ↔ v.asIdeal.absNorm ^ (k + 1) < N
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨w, hw, he⟩ | ⟨⟨w, j⟩, hb, he⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        rw [zero_add, pow_one]
        exact (hPB w).mp hw
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact (Finset.mem_filter.mp hb).2
    · intro h
      rcases k with _ | k
      · rw [zero_add, pow_one] at h
        exact Or.inl ⟨v, (hPB v).mpr h, rfl⟩
      · refine Or.inr ⟨(v, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨(hPB v).mpr ?_, Finset.mem_range.mpr ?_⟩, h⟩, rfl⟩
        · exact lt_of_le_of_lt (Nat.le_self_pow (by omega) _) h
        · calc k < 2 ^ k := Nat.lt_two_pow_self
            _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ v.asIdeal.absNorm ^ (k + 1 + 1) := Nat.pow_le_pow_left h2 _
            _ < N := h
  have hfib : ∀ n ∈ Finset.range N,
      LSeries.term (heckePrimePowerLogCoefficient χ) s n =
        ∑ a ∈ A with g a = n, heckePrimePowerLogTerm χ a.1 a.2 s := by
    intro n hn
    have hterm : LSeries.term (heckePrimePowerLogCoefficient χ) s n =
        heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ s := by
      rcases eq_or_ne n 0 with rfl | hn0
      · delta heckePrimePowerLogCoefficient
        simp
      · exact LSeries.term_of_ne_zero hn0 _ _
    have hset : {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n} =
        ↑(A.filter fun a ↦ g a = n) := by
      ext a
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, hmemA]
      constructor
      · intro h
        exact ⟨by rw [show g a = n from h]; exact Finset.mem_range.mp hn, h⟩
      · exact fun h ↦ h.2
    let φ : V[F] × ℕ → ℂ := fun a ↦
      heckeIdealValue (ideleClassNormTwist χ 0) (a.1.asIdeal ^ (a.2 + 1)) /
        ((a.2 + 1 : ℕ) : ℂ)
    rw [hterm, heckePrimePowerLogCoefficient_eq_sum]
    change (∑ᶠ a : ↥{a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n}, φ a) /
      (n : ℂ) ^ s = _
    rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have hga : a.1.asIdeal.absNorm ^ (a.2 + 1) = n := (Finset.mem_filter.mp ha).2
    change heckeIdealValue (ideleClassNormTwist χ 0) (a.1.asIdeal ^ (a.2 + 1)) /
      ((a.2 + 1 : ℕ) : ℂ) / (n : ℂ) ^ s = heckePrimePowerLogTerm χ a.1 a.2 s
    delta heckePrimePowerLogTerm
    rw [map_pow, hga, div_div]
  rw [Finset.sum_congr rfl hfib,
    Finset.sum_fiberwise_of_maps_to (fun a ha ↦ Finset.mem_range.mpr ((hmemA a).mp ha))]
  change ∑ a ∈ (_ ∪ _ : Finset (V[F] × ℕ)), _ = _
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · rintro ⟨v, k⟩ - ⟨w, j⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.succ.inj h.2)
  · intro v _ w _ h
    exact (Prod.mk.inj h).1
  · refine Finset.disjoint_left.mpr fun a h1 h2 ↦ ?_
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp h2
    exact Nat.succ_ne_zero _ (Prod.mk.inj hb).2

/-- Each logarithmic term is bounded by the positive majorant, because the character
values have norm at most one. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_term_le
    (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) :
    ‖heckePrimePowerLogTerm χ v k s‖ ≤
      (1 : ℝ) / ((k + 1 : ℕ) * (((v.asIdeal.absNorm ^ (k + 1) : ℕ) : ℝ) ^ s.re)) := by
  classical
  have h1 := HeightOneSpectrum.one_lt_absNorm v
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos _)]
    split_ifs
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  show ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
      (((k + 1 : ℕ) : ℂ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)‖ ≤ _
  rw [map_pow, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (by positivity)]
  gcongr

/-- The positive majorant over prime powers of exponent at least two is summable for an
abscissa greater than one half. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_summable_higher
    (F : Type*) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun a : V[F] × ℕ ↦
      (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ σ))) := by
  have hσ0 : 0 < σ := by linarith
  have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) :=
    (summable_absNorm_rpow F (by linarith)).comp_injective
      (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-σ)) ^ k := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
    (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun k ↦ pow_nonneg hr0 k))
  obtain ⟨v, k⟩ := a
  dsimp only
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hpow : ((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ σ =
      (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (_ ^ σ),
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ (2 * σ) := Real.rpow_pos_of_pos hN0 _
  have hB : 0 < ((2 : ℝ) ^ σ) ^ k := pow_pos (Real.rpow_pos_of_pos (by norm_num) _) k
  have hle : ((2 : ℝ) ^ σ) ^ k ≤ ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hN hσ0.le) k
  have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  calc 1 / (((k + 2 : ℕ) : ℝ) *
        ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k))
      ≤ 1 / ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k) := by
        apply one_div_le_one_div_of_le (mul_pos hA hB)
        calc (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k
            ≤ (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
              mul_le_mul_of_nonneg_left hle hA.le
          _ ≤ _ := le_mul_of_one_le_left (by positivity) h1
    _ = (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
        rw [Real.rpow_neg hN0.le, Real.rpow_neg (by norm_num), inv_pow, one_div, mul_inv]

/-- The finite sums over higher prime powers converge uniformly on the whole 1-line. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_higher
    (χ : U[F]) :
    TendstoUniformly
      (fun N : ℕ ↦ fun t : ℝ ↦
        ∑ a ∈ ((heckePrimesBelow F (N : ℝ)) ×ˢ (Finset.range N)).filter
          (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 2) < N),
          heckePrimePowerLogTerm χ a.1 (a.2 + 1) ⟨1, t⟩)
      (fun t : ℝ ↦ ∑' a : V[F] × ℕ, heckePrimePowerLogTerm χ a.1 (a.2 + 1) ⟨1, t⟩)
      atTop := by
  have hu :=
    heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_summable_higher F
      (σ := 1) (by norm_num)
  have hT := tendstoUniformlyOn_tsum
    (f := fun (a : V[F] × ℕ) (t : ℝ) ↦ heckePrimePowerLogTerm χ a.1 (a.2 + 1) ⟨1, t⟩) hu
    (s := Set.univ)
    (fun a t _ ↦ heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_term_le
      χ a.1 (a.2 + 1) ⟨1, t⟩)
  have hB : Tendsto (fun N : ℕ ↦ ((heckePrimesBelow F (N : ℝ)) ×ˢ (Finset.range N)).filter
      (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 2) < N)) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone
      (fun N N' hNN' a ha ↦ ?_) (fun a ↦ ?_)
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        heckePrimesBelow_mem_iff, Nat.cast_lt] at ha ⊢
      exact ⟨⟨lt_of_lt_of_le ha.1.1 hNN', lt_of_lt_of_le ha.1.2 hNN'⟩,
        lt_of_lt_of_le ha.2 hNN'⟩
    · refine ⟨a.1.asIdeal.absNorm ^ (a.2 + 2) + a.2 + 1, ?_⟩
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        heckePrimesBelow_mem_iff, Nat.cast_lt]
      have h2 : 2 ≤ a.1.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm a.1
      have h3 : a.1.asIdeal.absNorm ≤ a.1.asIdeal.absNorm ^ (a.2 + 2) :=
        Nat.le_self_pow (by omega) _
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · omega
      · omega
      · omega
  rw [← tendstoUniformlyOn_univ]
  exact fun u hu' ↦ hB.eventually (hT u hu')

/-- If on every compact subset of an open set of ordinates the ordered partial sums of
some logarithmic tail converge uniformly, the prime sums converge locally uniformly there. -/
private theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_of_tail
    (χ : U[F]) (U : Set ℝ) (hU : IsOpen U)
    (h : ∀ K : Set ℝ, IsCompact K → K ⊆ U → ∃ x : ℝ,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop U := by
  have hK : ∀ K : Set ℝ, IsCompact K → K ⊆ U → ∃ fK : ℝ → ℂ, TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩) fK atTop K := by
    intro K hKc hKU
    obtain ⟨x, hx⟩ := h K hKc hKU
    let fK : ℝ → ℂ := fun t ↦
      ∑ n ∈ Finset.range ⌈x⌉₊, LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n +
        heckePrimePowerLogTail χ x ⟨1, t⟩ -
          ∑' a : V[F] × ℕ, heckePrimePowerLogTerm χ a.1 (a.2 + 1) ⟨1, t⟩
    have hnat : TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ v ∈ heckePrimesBelow F (N : ℝ), heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
        fK atTop K := by
      have h1 : TendstoUniformlyOn
          (fun (_ : ℕ) (t : ℝ) ↦ ∑ n ∈ Finset.range ⌈x⌉₊,
            LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n)
          (fun t : ℝ ↦ ∑ n ∈ Finset.range ⌈x⌉₊,
            LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n) atTop K :=
        fun v hv ↦ Filter.Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hv
      have h2 := (h1.add hx).sub
        ((heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_higher
          χ).tendstoUniformlyOn (s := K))
      refine h2.congr ?_
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with N hN t _
      change ∑ n ∈ Finset.range ⌈x⌉₊,
          LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n +
        ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n - _ = _
      rw [← heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_sum_term χ x
          ⟨1, t⟩ N hN,
        heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_regroup χ ⟨1, t⟩ N,
        add_sub_cancel_right]
    refine ⟨fK, ?_⟩
    have hreal : TendstoUniformlyOn
        (fun y : ℝ ↦ fun t : ℝ ↦
          ∑ v ∈ heckePrimesBelow F ((⌈y⌉₊ : ℕ) : ℝ), heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
        fK atTop K :=
      fun u hu ↦ tendsto_nat_ceil_atTop.eventually (hnat u hu)
    refine hreal.congr (Eventually.of_forall fun y t _ ↦ ?_)
    have hPB : heckePrimesBelow F ((⌈y⌉₊ : ℕ) : ℝ) = heckePrimesBelow F y := by
      ext v
      rw [heckePrimesBelow_mem_iff, heckePrimesBelow_mem_iff, Nat.cast_lt, Nat.lt_ceil]
    exact congrArg (fun P ↦ ∑ v ∈ P, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩) hPB
  refine ⟨fun t ↦ limUnder atTop (fun x : ℝ ↦
    ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩), ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hKc
  obtain ⟨fK, hfK⟩ := hK K hKc hKU
  exact hfK.congr_right fun t ht ↦ ((hfK.tendsto_at ht).limUnder_eq).symm

/-- Paper: Corollary B.7.2.3, p. 651. For a character nontrivial on the
norm-one subgroup, the prime sum converges locally uniformly on the 1-line. -/
theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop := by
  obtain ⟨limit, hlim⟩ :=
    heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_of_tail χ Set.univ
      isOpen_univ fun K hK _ ↦ by
        obtain ⟨x₀, -, hx₀⟩ :=
          heckePrimePowerLogTail_of_nontrivial_on_normOne χ hχ K hK one_pos
        exact ⟨x₀, (hx₀ x₀ le_rfl).1⟩
  exact ⟨limit, tendstoLocallyUniformlyOn_univ.mp hlim⟩

/-- Paper: Corollary B.7.2.3, p. 651. For a pure norm character, the
prime sum converges locally uniformly on the 1-line away from the pole. -/
theorem heckePrimeSum_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop ({t₀}ᶜ : Set ℝ) := by
  refine heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne_of_tail χ _
    isOpen_compl_singleton fun K hK hKU ↦ ?_
  obtain ⟨x₀, -, hx₀⟩ :=
    heckePrimePowerLogTail_normTwist χ t₀ hχ K hK (fun h ↦ hKU h rfl) one_pos
  exact ⟨x₀, (hx₀ x₀ le_rfl).1⟩

/-- Paper: Equation (B.7.2.17), p. 652. The reciprocal partial Euler product
uses the finite Euler factors with prime norm strictly below the cutoff.
Deviation: The strict cutoff extends the definition to real `x`. -/
def reciprocalHeckeEulerProductBelow (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  reciprocalPartialHeckeEulerProduct χ (heckePrimesBelow F x) s

/-- Paper: Equation (B.7.2.17), p. 652. Each prime below the strict cutoff
contributes its linear Euler polynomial, with coefficient zero at ramified primes. -/
theorem reciprocalHeckeEulerProductBelow_eq_prod (χ : U[F]) (x : ℝ) (s : ℂ) :
    reciprocalHeckeEulerProductBelow χ x s =
      ∏ v ∈ heckePrimesBelow F x,
        (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) := by
  classical
  unfold reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
  rw [pow_one] at h
  rw [h, finiteHeckeEulerFactor]
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [hv]

/-- Paper: Equation (B.7.2.19), p. 652. This is the oscillatory part of
the logarithmic tail for a pure norm character, evaluated at ordinate `t`.
Deviation: The first term uses `t₀ - t` in its denominator, as required by
Equation (B.7.2.1). Its use is on the complement of the pole ordinate. -/
def heckeEulerProductOscillation (t₀ x t : ℝ) : ℂ :=
  -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
    ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n

/-- The unweighted oscillation is bounded independently of the integer cutoff on a
compact set of ordinates away from the pole. -/
private theorem heckeEulerProductOscillation_tendstoUniformlyOn_ordinate_bound
    (t₀ : ℝ) (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ K, ∀ m : ℕ, 0 < m →
      ‖heckePrimePowerTailOscillation t₀ m ⟨1, t⟩‖ ≤ B := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, le_rfl, fun t ht ↦ ht.elim⟩
  obtain ⟨t₁, ht₁, hmin⟩ := hK.exists_isMinOn hne
    ((continuous_const.sub continuous_id).abs.continuousOn (s := K) (f := fun t : ℝ ↦ |t₀ - t|))
  have hδ : 0 < |t₀ - t₁| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hpole (h ▸ ht₁))
  refine ⟨2 / |t₀ - t₁|, by positivity, fun t ht m hm ↦ ?_⟩
  have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ hpole ((show t = t₀ from congrArg Complex.im h) ▸ ht)
  have hw : (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ = ((t₀ - t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [heckePrimePowerTailOscillation, hne, ↓reduceIte, norm_div]
  have hn : ‖(m : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hm]
    simp
  have hd : ‖(⟨1, t₀⟩ : ℂ) - ⟨1, t⟩‖ = |t₀ - t| := by
    rw [hw, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hd]
  refine (div_le_div_of_nonneg_right ((norm_sub_le _ _).trans ?_) (abs_nonneg _)).trans
    (div_le_div_of_nonneg_left (by norm_num) hδ (isMinOn_iff.mp hmin t ht))
  rw [hn, norm_one]
  norm_num

/-- The reciprocal-logarithm differences telescope from the actual first included
integer. Thus the same majorant controls uniform convergence and its dependence on
the real cutoff. -/
private theorem heckeEulerProductOscillation_tendstoUniformlyOn_majorant
    (t₀ x : ℝ) (hx : 2 < x) (K : Set ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ t ∈ K, ∀ m : ℕ, 0 < m → ‖heckePrimePowerTailOscillation t₀ m ⟨1, t⟩‖ ≤ B) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧
      (∑' n, u n) ≤ (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ ∧
      ∀ n, ∀ t ∈ K, ‖heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n‖ ≤ B * u n := by
  let M := ⌈x⌉₊
  let m (n : ℕ) := max (M - 1) (n - 1)
  let a (n : ℕ) := (Real.log ((m n : ℕ) : ℝ))⁻¹
  have hM : 2 < M := (Nat.lt_ceil).mpr (by simpa using hx)
  have hm (n : ℕ) : 1 < m n := lt_of_lt_of_le (by omega : 1 < M - 1) (le_max_left _ _)
  have ha (n : ℕ) : 0 < Real.log ((m n : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have hanti (n : ℕ) : a (n + 1) ≤ a n := by
    apply inv_anti₀ (ha n)
    apply Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt (hm n)))
    exact_mod_cast max_le_max_left (M - 1) (by omega : n - 1 ≤ n + 1 - 1)
  let u (n : ℕ) := a n - a (n + 1)
  have hu (n : ℕ) : 0 ≤ u n := sub_nonneg.mpr (hanti n)
  have hsum (n : ℕ) : ∑ k ∈ Finset.range n, u k ≤ (Real.log ((M - 1 : ℕ) : ℝ))⁻¹ := by
    simp only [u, Finset.sum_range_sub']
    have hz : a 0 = (Real.log ((M - 1 : ℕ) : ℝ))⁻¹ := by simp [a, m]
    rw [hz]
    exact sub_le_self _ (inv_nonneg.mpr (ha n).le)
  refine ⟨u, summable_of_sum_range_le hu hsum, hu, Real.tsum_le_of_sum_range_le hu hsum, ?_⟩
  intro n t ht
  dsimp only [heckePrimePowerTailOscillationTerm]
  split_ifs with hxn
  · have hMn : M ≤ n := Nat.ceil_le.mpr hxn
    have hn : M - 1 ≤ n - 1 := by omega
    have hn' : M - 1 ≤ n := by omega
    have he : ‖invLog(n) - invLog(n - 1)‖ = u n := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]
      have e : u n = (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log (n : ℝ))⁻¹ := by
        simp only [u, a, m, Nat.add_sub_cancel, max_eq_right hn, max_eq_right hn']
      rw [← e, abs_of_nonneg (hu n)]
    rw [norm_mul, he]
    exact mul_le_mul_of_nonneg_right (hg t ht _ (by omega)) (hu n)
  · rw [norm_zero]
    exact mul_nonneg hB (hu n)

/-- Paper: Equation (B.7.2.19), p. 652. On compact sets away from the pole,
the endpoint term minus the finite correction sums converges uniformly to `G_x`.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_tendstoUniformlyOn (t₀ x : ℝ) (hx : 2 < x)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun t : ℝ ↦
      -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
        ∑ n ∈ Finset.range N, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n)
      (heckeEulerProductOscillation t₀ x) atTop K := by
  obtain ⟨B, hB, hg⟩ := heckeEulerProductOscillation_tendstoUniformlyOn_ordinate_bound t₀ K hK hpole
  obtain ⟨u, hu, _, _, hb⟩ :=
    heckeEulerProductOscillation_tendstoUniformlyOn_majorant t₀ x hx K hB hg
  have hT := tendstoUniformlyOn_tsum_nat
    (f := fun n t ↦ heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n) (hu.mul_left B) hb
  have hA : TendstoUniformlyOn
      (fun (_ : ℕ) (t : ℝ) ↦
        -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1))
      (fun t : ℝ ↦ -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1))
      atTop K := fun _ hv ↦ Filter.Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hv
  exact hA.sub hT

/-- The telescoping weights `1 / log (n - 1) - 1 / log n` at or above a cutoff greater
than two are nonnegative. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_weight_nonneg (x : ℝ)
    (hx : 2 < x) (n : ℕ) :
    0 ≤ (if x ≤ (n : ℝ) then
      (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) := by
  split_ifs with hxn
  · have hn : 3 ≤ n := by
      have h2 : (2 : ℝ) < n := hx.trans_le hxn
      have : 2 < n := by exact_mod_cast h2
      omega
    have h1 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 1)
    have h2 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    exact sub_nonneg.mpr (inv_anti₀ (Real.log_pos (by linarith))
      (Real.log_le_log (by linarith) h2))
  · exact le_rfl

/-- Partial sums of the telescoping weights are at most `1 / log (⌈x⌉₊ - 1)`. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_sum_weight_le (x : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) ≤
      (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ := by
  have key : ∑ n ∈ Finset.range N, (if x ≤ (n : ℝ) then
        (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) =
      if ⌈x⌉₊ ≤ N then (Real.log ((⌈x⌉₊ - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((N - 1 : ℕ) : ℝ))⁻¹
        else 0 := by
    induction N with
    | zero =>
      rw [Finset.sum_range_zero]
      split_ifs with hM
      · rw [Nat.le_zero.mp hM, sub_self]
      · rfl
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hceil : x ≤ (N : ℝ) ↔ ⌈x⌉₊ ≤ N := Nat.ceil_le.symm
      by_cases hM : ⌈x⌉₊ ≤ N
      · rw [ite_eq_left hM, ite_eq_left (hceil.mpr hM), ite_eq_left (hM.trans N.le_succ),
          Nat.add_sub_cancel]
        ring
      · rw [ite_eq_right hM, ite_eq_right (fun h ↦ hM (hceil.mp h)), add_zero]
        split_ifs with hM'
        · have hMN : ⌈x⌉₊ = N + 1 := by omega
          rw [hMN, sub_self]
        · rfl
  rw [key]
  split_ifs
  · exact sub_le_self _ (inv_nonneg.mpr (Real.log_natCast_nonneg _))
  · exact inv_nonneg.mpr (Real.log_natCast_nonneg _)

/-- The Dirichlet series of `1 / log n` over `n ≥ M` continues analytically to the open
disc around any point `w₁` that reaches to `1`. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_continuation (M : ℕ) (hM : 2 ≤ M)
    (w₁ : ℂ) :
    ∃ C : ℂ → ℂ, DifferentiableOn ℂ C (Metric.ball w₁ ‖w₁ - 1‖) ∧
      ∀ w ∈ Metric.ball w₁ ‖w₁ - 1‖, 1 < w.re →
        C w = LSeries (fun n : ℕ ↦ if M ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) w := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℂ,
      f = fun n : ℕ ↦ if M ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0 := ⟨_, rfl⟩
  rw [← hf]
  have hfb : ∃ B : ℝ, ∀ n ≠ 0, ‖f n‖ ≤ B := by
    refine ⟨(Real.log 2)⁻¹, fun n _ ↦ ?_⟩
    rw [hf]
    dsimp only
    split_ifs with hn
    · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      exact inv_anti₀ (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM.trans hn))
    · rw [norm_zero]
      exact inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  have habs : LSeries.abscissaOfAbsConv f ≤ 1 := LSeries.abscissaOfAbsConv_le_of_le_const hfb
  have hlog : ∀ n : ℕ, LSeries.logMul f n = if M ≤ n then (1 : ℂ) else 0 := by
    intro n
    rw [LSeries.logMul, hf]
    dsimp only
    split_ifs with hn
    · have h0 : (Real.log (n : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
      rw [← Complex.natCast_log, mul_inv_cancel₀ h0]
    · rw [mul_zero]
  have hQ : ∀ w : ℂ, 1 < w.re → LSeries (LSeries.logMul f) w =
      riemannZeta w - ∑ n ∈ Finset.range M, LSeries.term 1 w n := by
    intro w hw
    have hsum : Summable (LSeries.term 1 w) := LSeriesSummable_one_iff.mpr hw
    have h1 := (hasSum_nat_add_iff' M).mpr hsum.hasSum
    have h2 : HasSum (LSeries.term (LSeries.logMul f) w)
        (∑' n, LSeries.term 1 w n - ∑ n ∈ Finset.range M, LSeries.term 1 w n) := by
      refine (hasSum_nat_add_iff' M).mp ?_
      have h0 : ∑ n ∈ Finset.range M, LSeries.term (LSeries.logMul f) w n = 0 := by
        refine Finset.sum_eq_zero fun n hn ↦ ?_
        rcases eq_or_ne n 0 with rfl | hn0
        · exact LSeries.term_zero _ _
        · rw [LSeries.term_of_ne_zero hn0, hlog,
            ite_eq_right (not_le.mpr (Finset.mem_range.mp hn)), zero_div]
      rw [h0, sub_zero]
      convert h1 using 1
      funext i
      have hi : i + M ≠ 0 := by omega
      rw [LSeries.term_of_ne_zero hi, LSeries.term_of_ne_zero hi, hlog,
        ite_eq_left (Nat.le_add_left M i)]
      rfl
    rw [← LSeries_one_eq_riemannZeta hw]
    exact h2.tsum_eq
  have hQdiff : DifferentiableOn ℂ
      (fun w ↦ -(riemannZeta w - ∑ n ∈ Finset.range M, LSeries.term 1 w n))
      (Metric.ball w₁ ‖w₁ - 1‖) := by
    intro w hw
    have hw1 : w ≠ 1 := by
      rintro rfl
      rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hw
      exact lt_irrefl _ hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine ((differentiableAt_riemannZeta hw1).fun_sub
      (DifferentiableAt.fun_sum fun n _ ↦ ?_)).fun_neg
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact differentiableAt_const _
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      simp only [LSeries.term_of_ne_zero hn]
      exact (differentiableAt_const _).div (differentiableAt_id.const_cpow (Or.inl hn0))
        (fun h0 ↦ hn0 ((Complex.cpow_eq_zero_iff _ _).mp h0).1)
  obtain ⟨P, hP⟩ := hQdiff.isExactOn_ball
  have hΩo : IsOpen (Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re}) :=
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hΩc : Convex ℝ (Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re}) :=
    (convex_ball _ _).inter (convex_halfSpace_re_gt 1)
  have hd : ∀ w ∈ Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re},
      HasDerivAt (LSeries f - P) 0 w := by
    intro w hw
    have hre : 1 < w.re := hw.2
    have h1 := LSeries_hasDerivAt (f := f) (s := w)
      (lt_of_le_of_lt habs (by exact_mod_cast hre))
    have h3 := h1.sub (hP w hw.1)
    rw [hQ w hre, sub_self] at h3
    exact h3
  rcases (Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re}).eq_empty_or_nonempty with hΩ | ⟨w₀, hw₀⟩
  · refine ⟨P, fun w hw ↦ (hP w hw).differentiableAt.differentiableWithinAt,
      fun w hw hre ↦ ?_⟩
    have hmem : w ∈ Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re} := ⟨hw, hre⟩
    rw [hΩ] at hmem
    exact absurd hmem (Set.notMem_empty w)
  · refine ⟨fun w ↦ P w + (LSeries f w₀ - P w₀),
      fun w hw ↦ ((hP w hw).differentiableAt.add_const _).differentiableWithinAt,
      fun w hw hre ↦ ?_⟩
    have hc := hΩo.is_const_of_deriv_eq_zero hΩc.isPreconnected
      (fun w hw ↦ (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hd w hw).deriv)
      (show w ∈ Metric.ball w₁ ‖w₁ - 1‖ ∩ {w : ℂ | 1 < w.re} from ⟨hw, hre⟩) hw₀
    rw [Pi.sub_apply, Pi.sub_apply] at hc
    linear_combination -hc

/-- Summation by parts for the finite sums that define the oscillatory part. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_parts (x : ℝ) (hx : 0 < x) (z : ℂ)
    (N : ℕ) (hN : ⌈x⌉₊ - 1 ≤ N) :
    (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
      ∑ n ∈ Finset.range (N + 1), (if x ≤ (n : ℝ) then
        ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) =
    ∑ n ∈ Finset.range (N + 1), (if x ≤ (n : ℝ) then
        ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z) * invLog(n)) else 0) +
      (((N : ℕ) : ℂ) ^ z - 1) * invLog(N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h0 : ∀ u : ℕ → ℂ,
        ∑ n ∈ Finset.range (⌈x⌉₊ - 1 + 1), (if x ≤ (n : ℝ) then u n else 0) = 0 := by
      intro u
      rw [Nat.sub_add_cancel (Nat.ceil_pos.mpr hx)]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      exact ite_eq_right
        (fun h ↦ absurd (Nat.ceil_le.mpr h) (not_le.mpr (Finset.mem_range.mp hn)))
    rw [h0, h0, add_zero, zero_add]
  | succ N hN ih =>
    have hxN : x ≤ ((N + 1 : ℕ) : ℝ) := Nat.ceil_le.mp (by omega)
    rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1), ite_eq_left hxN,
      ite_eq_left hxN, Nat.add_sub_cancel]
    linear_combination ih

/-- On the closed left half-plane, a term of the series for the oscillatory part is at
most twice the telescoping weight. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_term_le (x : ℝ) (hx : 2 < x)
    (z : ℂ) (hz : z.re ≤ 0) (n : ℕ) :
    ‖(if x ≤ (n : ℝ) then
        ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0 : ℂ)‖ ≤
      2 * (if x ≤ (n : ℝ) then
        (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) := by
  split_ifs with hxn
  · have hn : 3 ≤ n := by
      have h2 : (2 : ℝ) < n := hx.trans_le hxn
      have : 2 < n := by exact_mod_cast h2
      omega
    have h1 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 1)
    have h2 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hanti : (Real.log ((n : ℕ) : ℝ))⁻¹ ≤ (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ :=
      inv_anti₀ (Real.log_pos (by linarith)) (Real.log_le_log (by linarith) h2)
    have hc : ‖((Real.log ((n : ℕ) : ℝ) : ℂ))⁻¹ - ((Real.log ((n - 1 : ℕ) : ℝ) : ℂ))⁻¹‖ =
        (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti)]
    have hp : ‖((n - 1 : ℕ) : ℂ) ^ z - 1‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_natCast_cpow_of_pos (by omega), norm_one]
      have h3 := Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ)) hz
      linarith
    rw [norm_mul, hc]
    exact mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hanti)
  · rw [norm_zero, mul_zero]

/-- Second-order bound for the remainder that is left when `(n - 1) ^ z - n ^ z` is
compared with `-z * n ^ (z - 1)`. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_remainder_le (n : ℕ) (hn : 3 ≤ n)
    (z : ℂ) (Z : ℝ) (hZ : ‖z‖ ≤ Z) (hre : z.re ≤ 1 / 2) :
    ‖(((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) * invLog(n)‖ ≤
      (4 * Z ^ 2 * Real.exp Z + 2 * Z) * (Real.log 2)⁻¹ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / (n : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]
    positivity
  have hu3 : u ≤ 1 / 3 := by
    rw [hu]
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hn)
  have habs : |u| < 1 := by
    rw [abs_of_pos hu0]
    linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.log (1 - u) := ⟨_, rfl⟩
  have hq1 : |q| ≤ 2 * u := by
    have h := Real.abs_log_sub_add_sum_range_le habs 0
    simp only [Finset.sum_range_zero, zero_add, pow_one] at h
    rw [abs_of_pos hu0, ← hq] at h
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq2 : |q + u| ≤ 2 * u ^ 2 := by
    have h := Real.abs_log_sub_add_sum_range_le habs 1
    simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one] at h
    rw [abs_of_pos hu0, ← hq] at h
    have h' : |q + u| ≤ u ^ 2 / (1 - u) := by
      rw [add_comm]
      exact h
    refine h'.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg u) (by linarith : (0 : ℝ) ≤ 1 - 2 * u)]
  have hqlog : q = Real.log ((n - 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    rw [hq, hu, ← Real.log_div hn1.ne' hn0.ne']
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
  have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1C : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e1 : ((n - 1 : ℕ) : ℂ) ^ z = ((n : ℕ) : ℂ) ^ z * Complex.exp ((q : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hn1C, Complex.cpow_def_of_ne_zero hnC, ← Complex.exp_add,
      ← Complex.natCast_log, ← Complex.natCast_log, hqlog]
    congr 1
    push_cast
    ring
  have e2 : ((n : ℕ) : ℂ) ^ (z - 1) = ((n : ℕ) : ℂ) ^ z / (n : ℂ) := by
    rw [Complex.cpow_sub _ _ hnC, Complex.cpow_one]
  have e3 : ((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1) =
      ((n : ℕ) : ℂ) ^ z *
        ((Complex.exp ((q : ℂ) * z) - 1 - (q : ℂ) * z) + z * ((q + u : ℝ) : ℂ)) := by
    rw [e1, e2, hu]
    push_cast
    field_simp
    ring
  have hqz : ‖(q : ℂ) * z‖ ≤ 2 * u * Z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hq1 hZ (norm_nonneg z) (by linarith)
  have hqz1 : ‖(q : ℂ) * z‖ ≤ Z := hqz.trans (by nlinarith)
  have hexp : ‖Complex.exp ((q : ℂ) * z) - 1 - (q : ℂ) * z‖ ≤
      4 * Z ^ 2 * Real.exp Z * u ^ 2 := by
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((q : ℂ) * z) 2
    have h' : ‖Complex.exp ((q : ℂ) * z) - 1 - (q : ℂ) * z‖ ≤
        ‖(q : ℂ) * z‖ ^ 2 * Real.exp ‖(q : ℂ) * z‖ := by
      rw [sub_sub]
      simpa [Finset.sum_range_succ] using h
    refine h'.trans (le_of_le_of_eq (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hqz 2)
      (Real.exp_le_exp.mpr hqz1) (Real.exp_nonneg _) (sq_nonneg _)) (by ring))
  have hlin : ‖z * ((q + u : ℝ) : ℂ)‖ ≤ 2 * Z * u ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_le_of_eq (mul_le_mul hZ hq2 (abs_nonneg _) hZ0) (by ring)
  have hpow : ‖((n : ℕ) : ℂ) ^ z‖ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) hre
  have hlog : ‖invLog(n)‖ ≤ (Real.log 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
    exact inv_anti₀ (Real.log_pos (by norm_num))
      (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ n)))
  have hK : 0 ≤ 4 * Z ^ 2 * Real.exp Z + 2 * Z :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Z)) (Real.exp_pos Z).le)
      (mul_nonneg (by norm_num) hZ0)
  have hbr : ‖(Complex.exp ((q : ℂ) * z) - 1 - (q : ℂ) * z) + z * ((q + u : ℝ) : ℂ)‖ ≤
      (4 * Z ^ 2 * Real.exp Z + 2 * Z) * u ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    exact add_le_add hexp hlin
  have hrp : (n : ℝ) ^ (1 / 2 : ℝ) * u ^ 2 = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h2 : (1 / (n : ℝ)) ^ 2 = (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hn0.le, Real.rpow_two, one_div, inv_pow]
    rw [hu, h2, ← Real.rpow_add hn0]
    congr 1
    norm_num
  rw [e3, norm_mul, norm_mul]
  refine le_of_le_of_eq (mul_le_mul (mul_le_mul hpow hbr (norm_nonneg _)
    (Real.rpow_nonneg hn0.le _)) hlog (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg hn0.le _) (mul_nonneg hK (sq_nonneg u)))) ?_
  rw [← hrp]
  ring

/-- Beyond the cutoff the remainder terms are bounded by a summable sequence, uniformly
for bounded `z` with real part at most one half. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_remainder_term_le (x : ℝ)
    (hx : 2 < x) (z : ℂ) (Z : ℝ) (hZ : ‖z‖ ≤ Z) (hre : z.re ≤ 1 / 2) (n : ℕ) :
    ‖((if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0) : ℂ)‖ ≤
      (4 * Z ^ 2 * Real.exp Z + 2 * Z) * (Real.log 2)⁻¹ * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  split_ifs with hxn
  · have hn : 3 ≤ n := by
      have h2 : (2 : ℝ) < n := hx.trans_le hxn
      have : 2 < n := by exact_mod_cast h2
      omega
    exact heckeEulerProductOscillation_analyticOnNhd_remainder_le n hn z Z hZ hre
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (sq_nonneg Z)) (Real.exp_pos Z).le) (mul_nonneg (by norm_num) hZ0))
      (inv_nonneg.mpr (Real.log_nonneg (by norm_num)))) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- To the left of the imaginary axis, the series for the oscillatory part is `-z` times
the Dirichlet series of `1 / log n` at `1 - z`, plus the series of the remainders. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_left (x : ℝ) (hx : 2 < x) (z : ℂ)
    (hz : z.re < 0) :
    (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
        ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) =
      -z * LSeries (fun n : ℕ ↦ if ⌈x⌉₊ ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) (1 - z) +
        ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0) := by
  have hx0 : 0 < x := by linarith
  have hw : Summable (fun n : ℕ ↦ if x ≤ (n : ℝ) then
      (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) :=
    summable_of_sum_range_le (heckeEulerProductOscillation_analyticOnNhd_weight_nonneg x hx)
      (heckeEulerProductOscillation_analyticOnNhd_sum_weight_le x)
  have hB : Summable (fun n : ℕ ↦ ((if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) : ℂ)) :=
    Summable.of_norm_bounded (hw.mul_left 2)
      (heckeEulerProductOscillation_analyticOnNhd_term_le x hx z hz.le)
  have hR : Summable (fun n : ℕ ↦ ((if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0) : ℂ)) :=
    Summable.of_norm_bounded
      ((Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2 : ℝ)) < -1)).mul_left
        ((4 * ‖z‖ ^ 2 * Real.exp ‖z‖ + 2 * ‖z‖) * (Real.log 2)⁻¹))
      (heckeEulerProductOscillation_analyticOnNhd_remainder_term_le x hx z ‖z‖ le_rfl
        (by linarith))
  have hfb : ∀ n : ℕ, n ≠ 0 →
      ‖(fun n : ℕ ↦ if ⌈x⌉₊ ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) n‖ ≤
        (Real.log 2)⁻¹ := by
    intro n _
    dsimp only
    split_ifs with hn
    · rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg n)]
      have h2n : (2 : ℝ) ≤ n :=
        (hx.le.trans (Nat.le_ceil x)).trans (by exact_mod_cast hn)
      exact inv_anti₀ (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h2n)
    · rw [norm_zero]
      exact inv_nonneg.mpr (Real.log_nonneg (by norm_num))
  have hLs : LSeriesSummable
      (fun n : ℕ ↦ if ⌈x⌉₊ ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) (1 - z) :=
    LSeriesSummable_of_bounded_of_one_lt_re hfb
      (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hterm : ∀ n : ℕ, LSeries.term
      (fun n : ℕ ↦ if ⌈x⌉₊ ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) (1 - z) n =
      if x ≤ (n : ℝ) then ((n : ℕ) : ℂ) ^ (z - 1) * invLog(n) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, ite_eq_right (by simpa using hx0)]
    · rw [LSeries.term_of_ne_zero hn]
      by_cases hxn : x ≤ (n : ℝ)
      · rw [ite_eq_left hxn, ite_eq_left (Nat.ceil_le.mpr hxn), show z - 1 = -(1 - z) by ring,
          Complex.cpow_neg]
        ring
      · rw [ite_eq_right hxn, ite_eq_right (fun h ↦ hxn (Nat.ceil_le.mp h)), zero_div]
  have hid : ∀ N : ℕ, ⌈x⌉₊ - 1 ≤ N →
      (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
        ∑ n ∈ Finset.range (N + 1), (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) =
      -z * ∑ n ∈ Finset.range (N + 1), LSeries.term
          (fun n : ℕ ↦ if ⌈x⌉₊ ≤ n then ((Real.log (n : ℝ) : ℂ))⁻¹ else 0) (1 - z) n +
        ∑ n ∈ Finset.range (N + 1), (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0) +
        (((N : ℕ) : ℂ) ^ z - 1) * invLog(N) := by
    intro N hN
    rw [heckeEulerProductOscillation_analyticOnNhd_parts x hx0 z N hN, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    rw [hterm]
    split_ifs
    · ring
    · ring
  have hlimB := (hB.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_add
    ((((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1))
  have hlimF := (hLs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul (-z)
  have hlimR := hR.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim0 : Tendsto (fun N : ℕ ↦ (((N : ℕ) : ℂ) ^ z - 1) * invLog(N)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ ↦ 2 * (Real.log ((N : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      simpa using h2.const_mul 2
    refine squeeze_zero_norm' ?_ hinv
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.log_natCast_nonneg N)]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Real.log_natCast_nonneg N))
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_natCast_cpow_of_pos (by omega), norm_one]
    have h3 := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)) hz.le
    linarith
  have hrhs := (hlimF.add hlimR).add hlim0
  rw [add_zero] at hrhs
  refine tendsto_nhds_unique hlimB (hrhs.congr' ?_)
  filter_upwards [eventually_ge_atTop (⌈x⌉₊ - 1)] with N hN
  exact (hid N hN).symm

/-- Near a nonzero point of the imaginary axis, the series for the oscillatory part agrees
on the axis with a function that is analytic at the point. -/
private theorem heckeEulerProductOscillation_analyticOnNhd_core (x : ℝ) (hx : 2 < x) (z₁ : ℂ)
    (hz₁ : z₁ ≠ 0) (hre : z₁.re = 0) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E z₁ ∧ ∀ᶠ z in 𝓝 z₁, z.re = 0 →
      (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
        ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) = E z := by
  have hM2 : 2 ≤ ⌈x⌉₊ := by
    have h : (2 : ℝ) < ⌈x⌉₊ := hx.trans_le (Nat.le_ceil x)
    have : 2 < ⌈x⌉₊ := by exact_mod_cast h
    omega
  have hr : 0 < min ‖z₁‖ (1 / 2) := lt_min (norm_pos_iff.mpr hz₁) (by norm_num)
  obtain ⟨C, hCd, hC⟩ :=
    heckeEulerProductOscillation_analyticOnNhd_continuation ⌈x⌉₊ hM2 (1 - z₁)
  have hball : ∀ z ∈ Metric.ball z₁ (min ‖z₁‖ (1 / 2)),
      1 - z ∈ Metric.ball (1 - z₁) ‖1 - z₁ - 1‖ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    have e : 1 - z - (1 - z₁) = -(z - z₁) := by ring
    have e' : 1 - z₁ - 1 = -z₁ := by ring
    rw [e, norm_neg, e', norm_neg]
    exact hz.trans_le (min_le_left _ _)
  have hw : Summable (fun n : ℕ ↦ if x ≤ (n : ℝ) then
      (Real.log ((n - 1 : ℕ) : ℝ))⁻¹ - (Real.log ((n : ℕ) : ℝ))⁻¹ else 0) :=
    summable_of_sum_range_le (heckeEulerProductOscillation_analyticOnNhd_weight_nonneg x hx)
      (heckeEulerProductOscillation_analyticOnNhd_sum_weight_le x)
  have hRd : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0))
      (Metric.ball z₁ (min ‖z₁‖ (1 / 2))) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2 : ℝ)) < -1)).mul_left
        ((4 * (‖z₁‖ + 1 / 2) ^ 2 * Real.exp (‖z₁‖ + 1 / 2) + 2 * (‖z₁‖ + 1 / 2)) *
          (Real.log 2)⁻¹))
      (fun n ↦ ?_) Metric.isOpen_ball (fun n z hz ↦ ?_)
    · by_cases hxn : x ≤ (n : ℝ)
      · have hn : 3 ≤ n := by
          have h2 : (2 : ℝ) < n := hx.trans_le hxn
          have : 2 < n := by exact_mod_cast h2
          omega
        have hnC : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hn1C : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have d1 : Differentiable ℂ (fun z : ℂ ↦ ((n - 1 : ℕ) : ℂ) ^ z) :=
          differentiable_id.const_cpow (Or.inl hn1C)
        have d2 : Differentiable ℂ (fun z : ℂ ↦ ((n : ℕ) : ℂ) ^ z) :=
          differentiable_id.const_cpow (Or.inl hnC)
        have d3 : Differentiable ℂ (fun z : ℂ ↦ ((n : ℕ) : ℂ) ^ (z - 1)) :=
          (differentiable_id.sub_const 1).const_cpow (Or.inl hnC)
        simp only [hxn, ↓reduceIte]
        exact (((d1.fun_sub d2).fun_add (differentiable_id.fun_mul d3)).fun_mul
          (differentiable_const _)).differentiableOn
      · simp only [hxn, ↓reduceIte]
        exact differentiableOn_const _
    · rw [Metric.mem_ball, dist_eq_norm] at hz
      have hZ : ‖z‖ ≤ ‖z₁‖ + 1 / 2 := by
        have h1 := norm_sub_norm_le z z₁
        linarith [min_le_right ‖z₁‖ (1 / 2 : ℝ)]
      have hre' : z.re ≤ 1 / 2 := by
        have h1 : (z - z₁).re ≤ ‖z - z₁‖ := Complex.re_le_norm _
        rw [Complex.sub_re, hre, sub_zero] at h1
        linarith [min_le_right ‖z₁‖ (1 / 2 : ℝ)]
      exact heckeEulerProductOscillation_analyticOnNhd_remainder_term_le x hx z _ hZ hre' n
  have hEd : DifferentiableOn ℂ (fun z : ℂ ↦ -z * C (1 - z) + ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0))
      (Metric.ball z₁ (min ‖z₁‖ (1 / 2))) := by
    refine DifferentiableOn.fun_add (DifferentiableOn.fun_mul differentiableOn_id.fun_neg ?_) hRd
    exact hCd.comp ((differentiableOn_const (1 : ℂ)).fun_sub differentiableOn_id) hball
  have hBc : ContinuousOn (fun z : ℂ ↦ (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
      ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0))
      {z : ℂ | z.re ≤ 0} := by
    have ha0 : ((⌈x⌉₊ - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    refine ContinuousOn.add (Continuous.continuousOn ?_) ?_
    · exact ((continuous_id.const_cpow (Or.inl ha0)).sub continuous_const).mul continuous_const
    · refine continuousOn_tsum (fun n ↦ Continuous.continuousOn ?_) (hw.mul_left 2)
        (fun n z hz ↦ heckeEulerProductOscillation_analyticOnNhd_term_le x hx z hz n)
      by_cases hxn : x ≤ (n : ℝ)
      · have hn : 3 ≤ n := by
          have h2 : (2 : ℝ) < n := hx.trans_le hxn
          have : 2 < n := by exact_mod_cast h2
          omega
        have hn1C : ((n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        simp only [hxn, ↓reduceIte]
        exact ((continuous_id.const_cpow (Or.inl hn1C)).sub continuous_const).mul
          continuous_const
      · simp only [hxn, ↓reduceIte]
        exact continuous_const
  have hleft : ∀ z ∈ Metric.ball z₁ (min ‖z₁‖ (1 / 2)), z.re < 0 →
      (((⌈x⌉₊ - 1 : ℕ) : ℂ) ^ z - 1) * invLog(⌈x⌉₊ - 1) +
        ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - 1) * (invLog(n) - invLog(n - 1))) else 0) =
      -z * C (1 - z) + ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0) := by
    intro z hz hzre
    rw [heckeEulerProductOscillation_analyticOnNhd_left x hx z hzre,
      hC (1 - z) (hball z hz) (by rw [Complex.sub_re, Complex.one_re]; linarith)]
  refine ⟨fun z : ℂ ↦ -z * C (1 - z) + ∑' n : ℕ, (if x ≤ (n : ℝ) then
          ((((n - 1 : ℕ) : ℂ) ^ z - ((n : ℕ) : ℂ) ^ z + z * ((n : ℕ) : ℂ) ^ (z - 1)) *
            invLog(n)) else 0),
    hEd.analyticAt (Metric.ball_mem_nhds z₁ hr), ?_⟩
  filter_upwards [Metric.ball_mem_nhds z₁ hr] with z hz hzre
  have hpath : Tendsto (fun δ : ℝ ↦ z - (δ : ℂ)) (𝓝[>] 0) (𝓝 z) := by
    have h0 : Tendsto (fun δ : ℝ ↦ z - (δ : ℂ)) (𝓝 0) (𝓝 (z - ((0 : ℝ) : ℂ))) :=
      (continuous_const.sub Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, sub_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hpathre : ∀ δ : ℝ, 0 < δ → (z - (δ : ℂ)).re < 0 := fun δ hδ ↦ by
    rw [Complex.sub_re, Complex.ofReal_re, hzre]
    linarith
  have hin : ∀ᶠ δ : ℝ in 𝓝[>] 0, z - (δ : ℂ) ∈ Metric.ball z₁ (min ‖z₁‖ (1 / 2)) :=
    hpath.eventually (Metric.isOpen_ball.mem_nhds hz)
  have hlimB := by
    have hwi : Tendsto (fun δ : ℝ ↦ z - (δ : ℂ)) (𝓝[>] 0) (𝓝[{z : ℂ | z.re ≤ 0}] z) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpath ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (hpathre δ hδ).le
    exact (hBc z (show z.re ≤ 0 from hzre.le)).tendsto.comp hwi
  have hlimE := ((hEd.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds hz)).tendsto).comp
    hpath
  refine tendsto_nhds_unique hlimB (hlimE.congr' ?_)
  filter_upwards [hin, self_mem_nhdsWithin] with δ hδ1 hδ2
  exact (hleft _ hδ1 (hpathre δ hδ2)).symm

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.19), p. 652. The oscillatory
part is real analytic away from the pole ordinate.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_analyticOnNhd (t₀ x : ℝ) (hx : 2 < x) :
    AnalyticOnNhd ℝ (heckeEulerProductOscillation t₀ x) ({t₀}ᶜ : Set ℝ) := by
  intro t₁ ht₁
  have ht₁' : t₁ ≠ t₀ := ht₁
  have hzfun : ∀ t : ℝ, (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ = ((t₀ : ℂ) - (t : ℂ)) * Complex.I := fun t ↦ by
    apply Complex.ext <;> simp
  have hz₁ : ((t₀ : ℂ) - (t₁ : ℂ)) * Complex.I ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ht₁'))
  obtain ⟨E, hEa, hE⟩ := heckeEulerProductOscillation_analyticOnNhd_core x hx
    (((t₀ : ℂ) - (t₁ : ℂ)) * Complex.I) hz₁ (by simp)
  have h1 : AnalyticAt ℝ (fun t : ℝ ↦ (t : ℂ)) t₁ := Complex.ofRealCLM.analyticAt t₁
  have hza : AnalyticAt ℝ (fun t : ℝ ↦ ((t₀ : ℂ) - (t : ℂ)) * Complex.I) t₁ :=
    (analyticAt_const.sub h1).mul analyticAt_const
  have hEa' : AnalyticAt ℝ (fun t : ℝ ↦ E (((t₀ : ℂ) - (t : ℂ)) * Complex.I)) t₁ :=
    (hEa.restrictScalars (𝕜 := ℝ)).comp_of_eq hza rfl
  have hG : AnalyticAt ℝ (fun t : ℝ ↦ -((((t₀ : ℂ) - (t : ℂ)) * Complex.I)⁻¹ *
      E (((t₀ : ℂ) - (t : ℂ)) * Complex.I))) t₁ := ((hza.inv hz₁).mul hEa').neg
  refine hG.congr ?_
  filter_upwards [hza.continuousAt.tendsto.eventually hE, isOpen_ne.mem_nhds ht₁']
    with t hEt htne
  have hB := hEt (by simp)
  have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ htne (congrArg Complex.im h)
  have hterm : ∀ n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n =
      (if x ≤ (n : ℝ) then
        ((((n - 1 : ℕ) : ℂ) ^ (((t₀ : ℂ) - (t : ℂ)) * Complex.I) - 1) *
          (invLog(n) - invLog(n - 1))) else 0) / (((t₀ : ℂ) - (t : ℂ)) * Complex.I) := by
    intro n
    delta heckePrimePowerTailOscillationTerm heckePrimePowerTailOscillation
    simp only [hne, ↓reduceIte, hzfun]
    split_ifs
    · ring
    · rw [zero_div]
  delta heckeEulerProductOscillation heckePrimePowerTailOscillation
  simp only [hne, ↓reduceIte, hzfun]
  rw [tsum_congr hterm, tsum_div_const, ← hB]
  ring

/-- Paper: Equation (B.7.2.19), p. 652. The oscillatory part is uniformly
`O(1 / log x)` on any compact set of ordinates away from the pole. -/
theorem heckeEulerProductOscillation_bound (t₀ : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ K,
      ‖heckeEulerProductOscillation t₀ x t‖ ≤ C / Real.log x := by
  obtain ⟨B, hB, hg⟩ := heckeEulerProductOscillation_tendstoUniformlyOn_ordinate_bound t₀ K hK hpole
  refine ⟨4 * B, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx t ht
  let M := ⌈x⌉₊
  let m := M - 1
  have hM : 2 < M := Nat.lt_ceil.mpr (by simpa using hx)
  have hm : 1 < m := by dsimp [m]; omega
  have hmr : (1 : ℝ) < m := by exact_mod_cast hm
  have hl : 0 < Real.log (m : ℝ) := Real.log_pos hmr
  have hxlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hcmp : Real.log x ≤ 2 * Real.log (m : ℝ) := by
    change Real.log x ≤ ((2 : ℕ) : ℝ) * Real.log (m : ℝ)
    rw [← Real.log_pow]
    apply Real.log_le_log (by linarith)
    refine (Nat.le_ceil x).trans ?_
    have h1 : M = m + 1 := by dsimp [m]; omega
    have h2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    change (M : ℝ) ≤ (m : ℝ) ^ 2
    rw [h1, Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg ((m : ℝ) - 2)]
  obtain ⟨u, hu, _, hs, hb⟩ :=
    heckeEulerProductOscillation_tendstoUniformlyOn_majorant t₀ x hx K hB hg
  have hseries : ‖∑' n, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n‖ ≤
      B * (Real.log (m : ℝ))⁻¹ := by
    refine (tsum_of_norm_bounded (hu.mul_left B).hasSum fun n ↦ hb n t ht).trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hs hB
  have hend : ‖-heckePrimePowerTailOscillation t₀ m ⟨1, t⟩ * invLog(m)‖ ≤ B * (Real.log (m : ℝ))⁻¹ := by
    rw [norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hl.le]
    exact mul_le_mul_of_nonneg_right (hg t ht m (by omega)) (inv_nonneg.mpr hl.le)
  refine (norm_sub_le _ _).trans ((add_le_add hend hseries).trans ?_)
  rw [le_div_iff₀ hxlog]
  calc
    _ = 2 * B * (Real.log (m : ℝ))⁻¹ * Real.log x := by ring
    _ ≤ 2 * B * (Real.log (m : ℝ))⁻¹ * (2 * Real.log (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hcmp (by positivity)
    _ = _ := by field_simp; ring

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction `H_x` is minus
the logarithmic terms whose primes lie below the cutoff but whose powers
have reached or exceeded it. Such powers have exponent at least two. -/
def heckeEulerProductLogCorrection (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
      heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)

/-- Paper: Theorem B.7.2.4(1), p. 652. The positive majorant over prime powers
of exponent at least two is summable for an abscissa greater than one half. -/
theorem summable_heckeHigherPrimePowerWeights (F : Type*) [Field F] [NumberField F]
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun a : V[F] × ℕ ↦
      (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ σ))) := by
  have hσ0 : 0 < σ := by linarith
  have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) :=
    (summable_absNorm_rpow F (by linarith)).comp_injective
      (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-σ)) ^ k := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
    (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun k ↦ pow_nonneg hr0 k))
  obtain ⟨v, k⟩ := a
  dsimp only
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hpow : ((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ σ =
      (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (_ ^ σ),
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ (2 * σ) := Real.rpow_pos_of_pos hN0 _
  have hB : 0 < ((2 : ℝ) ^ σ) ^ k := pow_pos (Real.rpow_pos_of_pos (by norm_num) _) k
  have hle : ((2 : ℝ) ^ σ) ^ k ≤ ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hN hσ0.le) k
  have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  calc 1 / (((k + 2 : ℕ) : ℝ) *
        ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k))
      ≤ 1 / ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k) := by
        apply one_div_le_one_div_of_le (mul_pos hA hB)
        calc (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k
            ≤ (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
              mul_le_mul_of_nonneg_left hle hA.le
          _ ≤ _ := le_mul_of_one_le_left (by positivity) h1
    _ = (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
        rw [Real.rpow_neg hN0.le, Real.rpow_neg (by norm_num), inv_pow, one_div, mul_inv]

/-- Each term of the correction is bounded by the positive majorant, because the
character values have norm at most one. -/
private theorem heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le (χ : U[F]) (v : V[F])
    (k : ℕ) (s : ℂ) :
    ‖heckePrimePowerLogTerm χ v (k + 1) s‖ ≤
      (1 : ℝ) / ((k + 2 : ℕ) * (((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ s.re)) := by
  classical
  have h1 := HeightOneSpectrum.one_lt_absNorm v
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 2))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos _)]
    split_ifs
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  show ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 2)) /
      (((k + 2 : ℕ) : ℂ) * ((v.asIdeal ^ (k + 2)).absNorm : ℂ) ^ s)‖ ≤ _
  rw [map_pow, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (by positivity)]
  gcongr

/-- Paper: Theorem B.7.2.4(1), p. 652. The series defining the correction
converges absolutely and uniformly on half-planes strictly to the right of one half.
Its sum is the negative of `H_x`. -/
theorem heckeEulerProductLogCorrection_hasSumUniformlyOn (χ : U[F]) (x : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSumUniformlyOn
      (fun (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) s ↦
        heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)
      (fun s ↦ -heckeEulerProductLogCorrection χ x s) {s : ℂ | σ ≤ s.re} := by
  have hu := (summable_heckeHigherPrimePowerWeights F hσ).comp_injective
    (Subtype.val_injective (p := fun a : V[F] × ℕ ↦ (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)))
  have hb : ∀ (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) (s : ℂ), s ∈ {s : ℂ | σ ≤ s.re} →
      ‖heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s‖ ≤
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ σ)) := by
    intro a s hs
    have h1 : (1 : ℝ) ≤ ((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) := by
      have := HeightOneSpectrum.one_lt_absNorm a.val.1
      exact_mod_cast Nat.one_le_pow _ _ (by omega)
    refine (heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le χ a.val.1 a.val.2 s).trans ?_
    have hp : (0 : ℝ) < ((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ σ :=
      Real.rpow_pos_of_pos (by linarith) _
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hs) (by positivity)
  convert HasSumUniformlyOn.of_norm_le_summable hu hb using 1
  funext s
  delta heckeEulerProductLogCorrection
  rw [neg_neg]

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction has norm at most
the tail of the positive majorant with prime-power norm at least `x`.
Deviation: The absolute majorant is evaluated at the real part of `s`. -/
theorem heckeEulerProductLogCorrection_norm_le (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ‖heckeEulerProductLogCorrection χ x s‖ ≤
      ∑' a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ s.re)) := by
  let w : V[F] × ℕ → ℝ := fun a ↦
    (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ s.re))
  have hW : Summable w := summable_heckeHigherPrimePowerWeights F hs
  have hw0 : ∀ a, 0 ≤ w a := fun a ↦ by simp only [w]; positivity
  let S1 : Set (V[F] × ℕ) := {a | (a.1.asIdeal.absNorm : ℝ) < x ∧
    x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  let S2 : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  have hsub : S1 ⊆ S2 := fun a ha ↦ ha.2
  have hs1 : Summable (fun a : S1 ↦ w a) := hW.comp_injective Subtype.val_injective
  delta heckeEulerProductLogCorrection
  rw [norm_neg]
  calc ‖∑' a : S1, heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s‖
      ≤ ∑' a : S1, w a :=
        tsum_of_norm_bounded hs1.hasSum fun a ↦
          heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le χ a.val.1 a.val.2 s
    _ = ∑' a, S1.indicator w a := tsum_subtype S1 w
    _ ≤ ∑' a, S2.indicator w a :=
        Summable.tsum_le_tsum (fun a ↦ Set.indicator_le_indicator_of_subset hsub hw0 a)
          (hW.indicator _) (hW.indicator _)
    _ = ∑' a : S2, w a := (tsum_subtype S2 w).symm

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction tends to zero
uniformly on the whole 1-line. -/
theorem heckeEulerProductLogCorrection_tendstoUniformly (χ : U[F]) :
    TendstoUniformly (fun x : ℝ ↦ fun t : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1, t⟩)
      (fun _ ↦ 0) atTop := by
  let w : V[F] × ℕ → ℝ := fun a ↦
    (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ (1 : ℝ)))
  have hW : Summable w := summable_heckeHigherPrimePowerWeights F (by norm_num)
  have hw0 : ∀ a, 0 ≤ w a := fun a ↦ by simp only [w]; positivity
  let S (x : ℝ) : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  have hT : Tendsto (fun x ↦ ∑' a, (S x).indicator w a) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun x a ↦ (S x).indicator w a) (g := fun _ ↦ (0 : ℝ)) hW (fun a ↦ ?_)
      (Eventually.of_forall fun x a ↦ ?_)
    · simpa using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop
        ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)] with x hx
      exact (Set.indicator_of_notMem (fun h : x ≤ _ ↦ absurd h (not_le.mpr hx)) w).symm
    · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun a _ ↦ hw0 a) a)]
      exact Set.indicator_le_self' (fun a _ ↦ hw0 a) a
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with x hx t
  rw [dist_zero_left]
  refine lt_of_le_of_lt ?_ hx
  exact (heckeEulerProductLogCorrection_norm_le χ x ⟨1, t⟩ (by norm_num)).trans_eq
    (tsum_subtype (S x) w)

/-- For an abscissa greater than zero, the logarithmic terms of one prime sum to a
logarithm of its Euler factor. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_factor (χ : U[F]) (v : V[F])
    (s : ℂ) (hs : 0 < s.re) :
    ∃ ℓ : ℂ, HasSum (fun k : ℕ ↦ heckePrimePowerLogTerm χ v k s) ℓ ∧
      Complex.exp ℓ = finiteHeckeEulerFactor χ v s := by
  classical
  have hN1 : 1 < v.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal := ⟨_, rfl⟩
  have ha' : a = if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v else 0 := by
    have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
    rw [pow_one, pow_one] at h
    rw [ha, h]
  have hapow (k : ℕ) :
      heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) = a ^ (k + 1) := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k), ha']
    split_ifs
    · rfl
    · rw [zero_pow (Nat.succ_ne_zero k)]
  have hanorm : ‖a‖ ≤ 1 := by
    rw [ha']
    split_ifs
    · rw [norm_ideleClassNormTwist_zero_localValue]
    · rw [norm_zero]
      exact zero_le_one
  have hz : ‖a * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have h1 : (v.asIdeal.absNorm : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (by simpa using hs)
    have h0 : 0 ≤ (v.asIdeal.absNorm : ℝ) ^ (-s).re := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖a‖ * (v.asIdeal.absNorm : ℝ) ^ (-s).re
        ≤ 1 * (v.asIdeal.absNorm : ℝ) ^ (-s).re := mul_le_mul_of_nonneg_right hanorm h0
      _ < 1 := by rw [one_mul]; exact h1
  have hterm (k : ℕ) : heckePrimePowerLogTerm χ v k s =
      (a * (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
    delta heckePrimePowerLogTerm
    rw [hapow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
      Complex.cpow_neg]
    ring
  have hshift := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hz)
  have h1z : 1 - a * (v.asIdeal.absNorm : ℂ) ^ (-s) ≠ 0 := by
    intro h
    rw [← (sub_eq_zero.mp h), norm_one] at hz
    exact lt_irrefl _ hz
  refine ⟨-Complex.log (1 - a * (v.asIdeal.absNorm : ℂ) ^ (-s)), ?_, ?_⟩
  · convert hshift using 1
    · funext k
      rw [hterm]
    · simp
  · rw [Complex.exp_neg, Complex.exp_log h1z]
    delta finiteHeckeEulerFactor
    rw [ha']
    split_ifs <;> simp

/-- Abel's inequality for a sequence whose partial sums stay within `η` of `T` beyond
`N₁`, against nonnegative weights that decrease beyond `N₁` and are at most one there. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_abel_bound (u : ℕ → ℂ)
    (T : ℂ) (b : ℕ → ℝ) (η : ℝ) (N₁ : ℕ)
    (hr : ∀ n : ℕ, N₁ ≤ n → ‖∑ k ∈ Finset.range n, u k - T‖ ≤ η)
    (hb0 : ∀ n : ℕ, N₁ ≤ n → 0 ≤ b n) (hb1 : b N₁ ≤ 1)
    (hanti : ∀ n : ℕ, N₁ ≤ n → b (n + 1) ≤ b n) (m : ℕ) (hm : N₁ ≤ m) :
    ‖∑ n ∈ Finset.range (m + 1), u n * ((b n : ℝ) : ℂ) -
      ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)‖ ≤ 2 * η := by
  have hη : 0 ≤ η := (norm_nonneg _).trans (hr N₁ le_rfl)
  have key : ‖(∑ n ∈ Finset.range (m + 1), u n * ((b n : ℝ) : ℂ) -
        ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)) -
      (∑ k ∈ Finset.range (m + 1), u k - T) * ((b m : ℝ) : ℂ)‖ ≤ η * (2 * b N₁ - b m) := by
    induction m, hm using Nat.le_induction with
    | base =>
      have e : (∑ n ∈ Finset.range (N₁ + 1), u n * ((b n : ℝ) : ℂ) -
          ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)) -
          (∑ k ∈ Finset.range (N₁ + 1), u k - T) * ((b N₁ : ℝ) : ℂ) =
          -((∑ k ∈ Finset.range N₁, u k - T) * ((b N₁ : ℝ) : ℂ)) := by
        rw [Finset.sum_range_succ (fun n ↦ u n * ((b n : ℝ) : ℂ)) N₁, Finset.sum_range_succ u N₁]
        ring
      rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 N₁ le_rfl)]
      have h1 := mul_le_mul_of_nonneg_right (hr N₁ le_rfl) (hb0 N₁ le_rfl)
      linarith
    | succ m hm ih =>
      have e : (∑ n ∈ Finset.range (m + 1 + 1), u n * ((b n : ℝ) : ℂ) -
          ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)) -
          (∑ k ∈ Finset.range (m + 1 + 1), u k - T) * ((b (m + 1) : ℝ) : ℂ) =
          ((∑ n ∈ Finset.range (m + 1), u n * ((b n : ℝ) : ℂ) -
            ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)) -
            (∑ k ∈ Finset.range (m + 1), u k - T) * ((b m : ℝ) : ℂ)) +
          (∑ k ∈ Finset.range (m + 1), u k - T) * (((b m - b (m + 1) : ℝ)) : ℂ) := by
        rw [Finset.sum_range_succ (fun n ↦ u n * ((b n : ℝ) : ℂ)) (m + 1),
          Finset.sum_range_succ u (m + 1), Complex.ofReal_sub]
        ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hanti m hm))]
      have h1 := mul_le_mul_of_nonneg_right (hr (m + 1) (by omega)) (sub_nonneg.mpr (hanti m hm))
      linarith [ih]
  have h2 : ‖(∑ k ∈ Finset.range (m + 1), u k - T) * ((b m : ℝ) : ℂ)‖ ≤ η * b m := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 m hm)]
    exact mul_le_mul_of_nonneg_right (hr (m + 1) (by omega)) (hb0 m hm)
  have h3 := norm_add_le
    ((∑ n ∈ Finset.range (m + 1), u n * ((b n : ℝ) : ℂ) -
        ∑ n ∈ Finset.range N₁, u n * ((b n : ℝ) : ℂ)) -
      (∑ k ∈ Finset.range (m + 1), u k - T) * ((b m : ℝ) : ℂ))
    ((∑ k ∈ Finset.range (m + 1), u k - T) * ((b m : ℝ) : ℂ))
  rw [sub_add_cancel] at h3
  nlinarith [mul_le_mul_of_nonneg_left hb1 hη]

/-- A meromorphic function in normal form whose values along the horizontal ray into a
point of the 1-line converge takes the limit as its value there. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_boundary (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (t : ℝ) (c : ℂ)
    (h : Tendsto (fun δ : ℝ ↦ L ⟨1 + δ, t⟩) (𝓝[>] 0) (𝓝 c)) : L ⟨1, t⟩ = c := by
  have hray : (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) = fun δ : ℝ ↦ (⟨1, t⟩ : ℂ) + (δ : ℂ) := by
    funext δ
    apply Complex.ext <;> simp
  have hcont : Tendsto (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) (𝓝[>] 0) (𝓝 (⟨1, t⟩ : ℂ)) := by
    rw [hray]
    have h0 : Tendsto (fun δ : ℝ ↦ (⟨1, t⟩ : ℂ) + (δ : ℂ)) (𝓝 0)
        (𝓝 ((⟨1, t⟩ : ℂ) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  by_cases ho : meromorphicOrderAt L (⟨1, t⟩ : ℂ) < 0
  · exfalso
    have hne : Tendsto (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) (𝓝[>] 0) (𝓝[≠] (⟨1, t⟩ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      intro he
      have h1 : 1 + δ = 1 := congrArg Complex.re he
      have hδ' : (0 : ℝ) < δ := hδ
      linarith
    have hcob := (tendsto_cobounded_of_meromorphicOrderAt_neg ho).comp hne
    exact h.not_tendsto (Metric.disjoint_nhds_cobounded c) hcob
  · have han : AnalyticAt ℂ L (⟨1, t⟩ : ℂ) :=
      (hL (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (not_lt.mp ho)
    exact tendsto_nhds_unique (han.continuousAt.tendsto.comp hcont) h

/-- Moving the abscissa of a tail term from one to `1 + δ` multiplies it by `n ^ (-δ)`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_term_shift (χ : U[F])
    (x t δ : ℝ) (n : ℕ) :
    heckePrimePowerLogTailTerm χ x ⟨1 + δ, t⟩ n =
      heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ) := by
  delta heckePrimePowerLogTailTerm
  split_ifs with hxn
  · rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, LSeries.term_zero, zero_mul]
    · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hs : (⟨1 + δ, t⟩ : ℂ) = (⟨1, t⟩ : ℂ) + (δ : ℂ) := by
        apply Complex.ext <;> simp
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hs, Complex.cpow_add _ _ hn0,
        Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
      ring
  · rw [zero_mul]

/-- Abel's limit theorem along the horizontal ray: if the ordered sum of `u` converges
to `T`, the ordered sums of `u n * n ^ (-δ)` tend to `T` as `δ` decreases to zero. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_abel (u : ℕ → ℂ) (T : ℂ)
    (A : ℝ → ℂ) (hu0 : u 0 = 0)
    (hu : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, u n) atTop (𝓝 T))
    (hA : ∀ δ : ℝ, 0 < δ → Tendsto (fun N : ℕ ↦
      ∑ n ∈ Finset.range N, u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ)) atTop (𝓝 (A δ))) :
    Tendsto A (𝓝[>] 0) (𝓝 T) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hu) (ε / 8) (by positivity)
  have hr : ∀ n : ℕ, N₀ + 1 ≤ n → ‖∑ k ∈ Finset.range n, u k - T‖ ≤ ε / 8 := fun n hn ↦ by
    rw [← dist_eq_norm]
    exact (hN₀ n (by omega)).le
  have hfin : Tendsto
      (fun δ : ℝ ↦ ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (∑ n ∈ Finset.range (N₀ + 1), u n)) := by
    refine tendsto_finsetSum _ fun n _ ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hu0]
      simp only [zero_mul]
      exact tendsto_const_nhds
    · have hc : Tendsto (fun δ : ℝ ↦ (n : ℝ) ^ (-δ)) (𝓝 0) (𝓝 ((n : ℝ) ^ (-(0 : ℝ)))) :=
        ((Real.continuous_const_rpow (Nat.cast_ne_zero.mpr hn)).comp continuous_neg).tendsto 0
      rw [neg_zero, Real.rpow_zero] at hc
      have h1 := ((Complex.continuous_ofReal.tendsto 1).comp hc).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have h2 := h1.const_mul (u n)
      rw [Complex.ofReal_one, mul_one] at h2
      exact h2
  filter_upwards [(Metric.tendsto_nhds.mp hfin) (ε / 8) (by positivity), self_mem_nhdsWithin]
    with δ hδ1 hδ0
  have hδ : (0 : ℝ) < δ := hδ0
  have hbound : ∀ m : ℕ, N₀ + 1 ≤ m →
      ‖∑ n ∈ Finset.range (m + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ) -
        ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ)‖ ≤ 2 * (ε / 8) :=
    fun m hm ↦ reciprocalHeckeEulerProductBelow_mul_normTwist_abel_bound u T
      (fun n ↦ (n : ℝ) ^ (-δ)) (ε / 8) (N₀ + 1) hr
      (fun n _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.le_add_left 1 N₀)
        (by linarith))
      (fun n hn ↦ Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (by omega : 0 < n))
        (by exact_mod_cast n.le_succ) (by linarith))
      m hm
  have hlim : Tendsto
      (fun m : ℕ ↦ ‖∑ n ∈ Finset.range (m + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ) -
        ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ)‖) atTop
      (𝓝 ‖A δ - ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ)‖) :=
    (((hA δ hδ).comp (tendsto_add_atTop_nat 1)).sub_const _).norm
  have h1 : ‖A δ - ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ)‖ ≤
      2 * (ε / 8) :=
    le_of_tendsto hlim (eventually_atTop.mpr ⟨N₀ + 1, hbound⟩)
  have h2 := hr (N₀ + 1) le_rfl
  rw [dist_eq_norm] at hδ1 ⊢
  have h3 := norm_add₃_le
    (a := A δ - ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ))
    (b := ∑ n ∈ Finset.range (N₀ + 1), u n * (((n : ℝ) ^ (-δ) : ℝ) : ℂ) -
      ∑ n ∈ Finset.range (N₀ + 1), u n)
    (c := ∑ n ∈ Finset.range (N₀ + 1), u n - T)
  rw [sub_add_sub_cancel, sub_add_sub_cancel] at h3
  linarith

/-- The reciprocal product below a cutoff does not vanish to the right of zero. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_ne_zero (χ : U[F]) (x : ℝ)
    (s : ℂ) (hs : 0 < s.re) : reciprocalHeckeEulerProductBelow χ x s ≠ 0 := by
  delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  refine Finset.prod_ne_zero_iff.mpr fun v _ ↦ inv_ne_zero ?_
  obtain ⟨ℓ, -, hℓ⟩ := reciprocalHeckeEulerProductBelow_mul_normTwist_factor χ v s hs
  rw [← hℓ]
  exact Complex.exp_ne_zero _

/-- To the right of one, the logarithmic terms of all powers of the primes of norm at
least the cutoff sum to the tail plus the correction. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_hasSum_above (χ : U[F])
    (x : ℝ) (s : halfPlane) :
    HasSum (fun a : V[F] × ℕ ↦ if x ≤ (a.1.asIdeal.absNorm : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  classical
  have hs : 1 < (s : ℂ).re := s.property
  have h1 := (hasSum_subtype_iff_indicator
    (s := {a : V[F] × ℕ | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)})
    (f := fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s)).mp
    (heckePrimePowerLogTail_hasSum_of_one_lt_re χ x s)
  have h2 := (hasSum_subtype_iff_indicator
    (s := {a : V[F] × ℕ | (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)})
    (f := fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 (a.2 + 1) s)).mp
    ((heckeEulerProductLogCorrection_hasSumUniformlyOn χ x (σ := 1) (by norm_num)).hasSum
      (show (1 : ℝ) ≤ (s : ℂ).re from hs.le))
  have hinj : Function.Injective (fun b : V[F] × ℕ ↦ (b.1, b.2 + 1)) := by
    rintro ⟨v, j⟩ ⟨w, i⟩ h
    exact Prod.ext (Prod.mk.inj h).1 (Nat.succ.inj (Prod.mk.inj h).2)
  have h3 : HasSum (fun a : V[F] × ℕ ↦
      if (a.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)
        then heckePrimePowerLogTerm χ a.1 a.2 s else 0)
      (-heckeEulerProductLogCorrection χ x s) := by
    refine (hinj.hasSum_iff fun a ha ↦ ?_).mp ?_
    · obtain ⟨v, k⟩ := a
      rcases k with _ | k
      · refine ite_eq_right fun h ↦ ?_
        rw [zero_add, pow_one] at h
        exact absurd h.2 (not_le.mpr h.1)
      · exact absurd ⟨(v, k), rfl⟩ ha
    · convert h2 using 1
      funext b
      by_cases hb : (b.1.asIdeal.absNorm : ℝ) < x ∧
          x ≤ ((b.1.asIdeal.absNorm ^ (b.2 + 2) : ℕ) : ℝ)
      · rw [Set.indicator_of_mem (by exact hb)]
        exact ite_eq_left hb
      · rw [Set.indicator_of_notMem (by exact hb)]
        exact ite_eq_right hb
  convert h1.sub h3 using 1
  · funext a
    have hpow : (a.1.asIdeal.absNorm : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero a.2) _
    by_cases hx : x ≤ (a.1.asIdeal.absNorm : ℝ)
    · rw [ite_eq_left hx, Set.indicator_of_mem (by exact hx.trans hpow),
        ite_eq_right (fun h ↦ absurd hx (not_le.mpr h.1)), sub_zero]
    · by_cases hx2 : x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)
      · rw [ite_eq_right hx, Set.indicator_of_mem (by exact hx2), ite_eq_left ⟨not_le.mp hx, hx2⟩,
          sub_self]
      · rw [ite_eq_right hx, Set.indicator_of_notMem (by exact hx2), ite_eq_right (fun h ↦ hx2 h.2),
          sub_zero]
  · rw [sub_neg_eq_add]

/-- To the right of one, the reciprocal product below the cutoff times the finite
L-function is the exponential of the tail plus the correction. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_of_one_lt_re (χ : U[F])
    (x : ℝ) (s : halfPlane) :
    reciprocalHeckeEulerProductBelow χ x s * finiteHeckeL χ s =
      Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  classical
  have hs0 : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  choose ℓ hℓsum hℓexp using fun v : V[F] ↦
    reciprocalHeckeEulerProductBelow_mul_normTwist_factor χ v s hs0
  have hfib : HasSum (fun v : V[F] ↦ if x ≤ (v.asIdeal.absNorm : ℝ) then ℓ v else 0)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
    refine (reciprocalHeckeEulerProductBelow_mul_normTwist_hasSum_above χ x s).prod_fiberwise
      fun v ↦ ?_
    by_cases hv : x ≤ (v.asIdeal.absNorm : ℝ)
    · simp only [ite_eq_left hv]
      exact hℓsum v
    · simp only [ite_eq_right hv]
      exact hasSum_zero
  have hP : HasProd (fun v : V[F] ↦
      if v ∈ heckePrimesBelow F x then (finiteHeckeEulerFactor χ v s)⁻¹ else 1)
      (reciprocalHeckeEulerProductBelow χ x s) := by
    have h := hasProd_prod_of_ne_finset_one (L := SummationFilter.unconditional _)
      (s := heckePrimesBelow F x)
      (f := fun v : V[F] ↦
        if v ∈ heckePrimesBelow F x then (finiteHeckeEulerFactor χ v s)⁻¹ else 1)
      (fun v hv ↦ ite_eq_right hv)
    convert h using 1
    delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
    exact Finset.prod_congr rfl fun v hv ↦ (ite_eq_left hv).symm
  refine (hP.mul (finiteHeckeL_hasProd χ s)).unique ?_
  convert hfib.cexp using 1
  funext v
  have hne : finiteHeckeEulerFactor χ v s ≠ 0 := by
    rw [← hℓexp v]
    exact Complex.exp_ne_zero _
  by_cases hv : x ≤ (v.asIdeal.absNorm : ℝ)
  · have hmem : v ∉ heckePrimesBelow F x := fun h ↦
      absurd ((heckePrimesBelow_mem_iff v x).mp h) (not_lt.mpr hv)
    rw [Function.comp_apply, ite_eq_right hmem, ite_eq_left hv, one_mul, hℓexp]
  · have hmem : v ∈ heckePrimesBelow F x := (heckePrimesBelow_mem_iff v x).mpr (not_le.mp hv)
    rw [Function.comp_apply, ite_eq_left hmem, ite_eq_right hv, Complex.exp_zero]
    exact inv_mul_cancel₀ hne

/-- To the right of one, the tail terms are absolutely summable over the integer norms.
Their sum is the sum of the logarithmic terms over the prime powers whose norms are at
least the cutoff. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_tail_hasSum (χ : U[F])
    (x : ℝ) (s : halfPlane) :
    HasSum (heckePrimePowerLogTailTerm χ x s)
      (∑' a : V[F] × ℕ,
        ({a : V[F] × ℕ | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}.indicator
          (fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s)) a) := by
  classical
  have hsum : Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s) :=
    summable_heckePrimePowerLogTerm_of_one_lt_re χ s
  let S : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}
  let f : V[F] × ℕ → ℂ := S.indicator (fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s)
  have hf : Summable f := hsum.indicator S
  have hfib := hf.hasSum.tsum_fiberwise (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 1))
  have hfib_eq (n : ℕ) :
      ∑' b : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}, f b =
        heckePrimePowerLogTailTerm χ x s n := by
    have hfin : Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} :=
      heckePrimePowerLogTail_fiber_finite n
    have hval (b : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
        f b = if x ≤ (n : ℝ) then
          (heckeIdealValue (ideleClassNormTwist χ 0) (b.val.1.asIdeal ^ (b.val.2 + 1)) /
            ((b.val.2 + 1 : ℕ) : ℂ)) / (n : ℂ) ^ (s : ℂ) else 0 := by
      obtain ⟨⟨v, k⟩, hb⟩ := b
      have hb' : v.asIdeal.absNorm ^ (k + 1) = n := hb
      have hmem : (v, k) ∈ S ↔ x ≤ (n : ℝ) := by
        simp only [S, Set.mem_ofPred_eq]
        rw [hb']
      by_cases hxn : x ≤ (n : ℝ)
      · rw [ite_eq_left hxn]
        simp only [f]
        rw [Set.indicator_of_mem (hmem.mpr hxn)]
        delta heckePrimePowerLogTerm
        rw [map_pow, hb', div_div]
      · rw [ite_eq_right hxn]
        simp only [f]
        rw [Set.indicator_of_notMem (fun h ↦ hxn (hmem.mp h))]
    have hterm : LSeries.term (heckePrimePowerLogCoefficient χ) s n =
        heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ (s : ℂ) := by
      rcases eq_or_ne n 0 with rfl | hn
      · delta heckePrimePowerLogCoefficient
        simp
      · exact LSeries.term_of_ne_zero hn _ _
    rw [tsum_congr hval]
    delta heckePrimePowerLogTailTerm
    split_ifs with hxn
    · rw [tsum_div_const, hterm, heckePrimePowerLogCoefficient_eq_sum,
        tsum_eq_finsum (Set.toFinite _)]
    · exact tsum_zero
  have hN : HasSum (heckePrimePowerLogTailTerm χ x s) (∑' a, f a) := by
    convert hfib using 1
    funext n
    exact (hfib_eq n).symm
  exact hN

/-- To the right of one, the ordered partial sums of the tail terms converge to the
tail. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_tail_tendsto (χ : U[F])
    (x : ℝ) (s : halfPlane) :
    Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x s n) atTop
      (𝓝 (heckePrimePowerLogTail χ x s)) := by
  have hN := reciprocalHeckeEulerProductBelow_mul_normTwist_tail_hasSum χ x s
  have htail : heckePrimePowerLogTail χ x s = ∑' n, heckePrimePowerLogTailTerm χ x s n := by
    delta heckePrimePowerLogTail
    rw [tsum_eq_of_summable_unconditional hN.summable]
  rw [htail]
  exact hN.summable.hasSum.tendsto_sum_nat

/-- The correction is continuous on the closed half-plane to the right of one. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_correction_continuousOn
    (χ : U[F]) (x : ℝ) :
    ContinuousOn (heckeEulerProductLogCorrection χ x) {s : ℂ | 1 ≤ s.re} := by
  have h := (heckeEulerProductLogCorrection_hasSumUniformlyOn χ x (σ := 1)
    (by norm_num)).tendstoUniformlyOn
  have hc : ContinuousOn (fun s ↦ -heckeEulerProductLogCorrection χ x s)
      {s : ℂ | 1 ≤ s.re} := by
    refine h.continuousOn (Frequently.of_forall fun I ↦ ?_)
    refine continuousOn_finsetSum _ fun a _ ↦ Continuous.continuousOn ?_
    have hN : ((a.val.1.asIdeal ^ (a.val.2 + 1 + 1)).absNorm : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
      exact pow_ne_zero _ a.val.1.ne_bot
    delta heckePrimePowerLogTerm
    exact continuous_const.div (continuous_const.mul (continuous_id.const_cpow (Or.inl hN)))
      (fun s ↦ mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
        (fun h0 ↦ hN ((Complex.cpow_eq_zero_iff _ _).mp h0).1))
  simpa using hc.neg

/-- Paper: Theorem B.7.2.4(1), p. 652. Off the pole, multiplying the
reciprocal partial product by the continued finite L-function gives the
exponential of the oscillation, the cutoff correction and a small continuous error.
Deviation: Uses the sign-corrected oscillation from Equation (B.7.2.19).
The cutoff threshold is greater than two. Real cutoffs have the same strict
norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductOscillation t₀ x t +
            heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  obtain ⟨x₀, hx₀, h⟩ := heckePrimePowerLogTail_normTwist χ t₀ hχ K hK hpole hε
  refine ⟨x₀, hx₀, fun x hx ↦ ?_⟩
  obtain ⟨hunif, error, herrc, herr⟩ := h x hx
  refine ⟨error, herrc, fun t ht ↦ ⟨(herr t ht).1, ?_⟩⟩
  have hray : Tendsto (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) (𝓝[>] 0) (𝓝 (⟨1, t⟩ : ℂ)) := by
    have hfun : (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) = fun δ : ℝ ↦ (⟨1, t⟩ : ℂ) + (δ : ℂ) := by
      funext δ
      apply Complex.ext <;> simp
    rw [hfun]
    have h0 : Tendsto (fun δ : ℝ ↦ (⟨1, t⟩ : ℂ) + (δ : ℂ)) (𝓝 0)
        (𝓝 ((⟨1, t⟩ : ℂ) + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hmem : ∀ δ : ℝ, 0 < δ → (⟨1 + δ, t⟩ : ℂ) ∈ halfPlane := fun δ hδ ↦ by
    show (1 : ℝ) < 1 + δ
    linarith
  have hAbel : Tendsto (fun δ : ℝ ↦ heckePrimePowerLogTail χ x ⟨1 + δ, t⟩) (𝓝[>] 0)
      (𝓝 (heckePrimePowerLogTail χ x ⟨1, t⟩)) := by
    refine reciprocalHeckeEulerProductBelow_mul_normTwist_abel
      (heckePrimePowerLogTailTerm χ x ⟨1, t⟩) _ _ ?_ (hunif.tendsto_at ht) fun δ hδ ↦ ?_
    · delta heckePrimePowerLogTailTerm
      rw [LSeries.term_zero, ite_self]
    · have h1 : Tendsto (fun N : ℕ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1 + δ, t⟩ n) atTop
          (𝓝 (heckePrimePowerLogTail χ x ⟨1 + δ, t⟩)) :=
        reciprocalHeckeEulerProductBelow_mul_normTwist_tail_tendsto χ x ⟨_, hmem δ hδ⟩
      simp only [reciprocalHeckeEulerProductBelow_mul_normTwist_term_shift] at h1
      exact h1
  have hH : Tendsto (fun δ : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1 + δ, t⟩) (𝓝[>] 0)
      (𝓝 (heckeEulerProductLogCorrection χ x ⟨1, t⟩)) := by
    have hw : Tendsto (fun δ : ℝ ↦ (⟨1 + δ, t⟩ : ℂ)) (𝓝[>] 0)
        (𝓝[{s : ℂ | 1 ≤ s.re}] (⟨1, t⟩ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hray ?_
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      show (1 : ℝ) ≤ 1 + δ
      exact le_add_of_nonneg_right (le_of_lt hδ)
    exact ((reciprocalHeckeEulerProductBelow_mul_normTwist_correction_continuousOn χ x)
      (⟨1, t⟩ : ℂ) (show (1 : ℝ) ≤ 1 from le_rfl)).tendsto.comp hw
  have hPc : Continuous (reciprocalHeckeEulerProductBelow χ x) := by
    have hfun : reciprocalHeckeEulerProductBelow χ x = fun s ↦
        ∏ v ∈ heckePrimesBelow F x,
          (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
            (v.asIdeal.absNorm : ℂ) ^ (-s)) :=
      funext fun s ↦ reciprocalHeckeEulerProductBelow_eq_prod χ x s
    rw [hfun]
    refine continuous_finsetProd _ fun v _ ↦ continuous_const.sub (continuous_const.mul ?_)
    refine continuous_neg.const_cpow (Or.inl ?_)
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hP := (hPc.tendsto (⟨1, t⟩ : ℂ)).comp hray
  have hP1 : reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ ≠ 0 :=
    reciprocalHeckeEulerProductBelow_mul_normTwist_ne_zero χ x _ (show (0 : ℝ) < 1 from one_pos)
  have hexp := (Complex.continuous_exp.tendsto _).comp (hAbel.add hH)
  have hLlim : Tendsto (fun δ : ℝ ↦ L ⟨1 + δ, t⟩) (𝓝[>] 0)
      (𝓝 (Complex.exp (heckePrimePowerLogTail χ x ⟨1, t⟩ +
        heckeEulerProductLogCorrection χ x ⟨1, t⟩) /
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)) := by
    refine (hexp.div hP hP1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have h3 : reciprocalHeckeEulerProductBelow χ x ⟨1 + δ, t⟩ *
        finiteHeckeL χ ⟨⟨1 + δ, t⟩, hmem δ hδ'⟩ =
        Complex.exp (heckePrimePowerLogTail χ x ⟨1 + δ, t⟩ +
          heckeEulerProductLogCorrection χ x ⟨1 + δ, t⟩) :=
      reciprocalHeckeEulerProductBelow_mul_normTwist_of_one_lt_re χ x ⟨_, hmem δ hδ'⟩
    have hS : L ⟨1 + δ, t⟩ = finiteHeckeL χ ⟨⟨1 + δ, t⟩, hmem δ hδ'⟩ :=
      hSeries ⟨_, hmem δ hδ'⟩
    have hPδ : reciprocalHeckeEulerProductBelow χ x ⟨1 + δ, t⟩ ≠ 0 :=
      reciprocalHeckeEulerProductBelow_mul_normTwist_ne_zero χ x _
        (show (0 : ℝ) < 1 + δ by linarith)
    show Complex.exp (heckePrimePowerLogTail χ x ⟨1 + δ, t⟩ +
      heckeEulerProductLogCorrection χ x ⟨1 + δ, t⟩) /
      reciprocalHeckeEulerProductBelow χ x ⟨1 + δ, t⟩ = L ⟨1 + δ, t⟩
    rw [← h3, ← hS, mul_div_cancel_left₀ _ hPδ]
  have hbd := reciprocalHeckeEulerProductBelow_mul_normTwist_boundary L hL t _ hLlim
  have hcancel : reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ *
      (Complex.exp (heckePrimePowerLogTail χ x ⟨1, t⟩ +
        heckeEulerProductLogCorrection χ x ⟨1, t⟩) /
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) =
      Complex.exp (heckePrimePowerLogTail χ x ⟨1, t⟩ +
        heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
    field_simp
  rw [hbd, hcancel, (herr t ht).2]
  delta heckeEulerProductOscillation
  congr 1
  ring

/-- A family that is eventually the exponential of uniformly small exponents on a set tends
uniformly to one there. -/
private theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist_of_exp
    (f : ℝ → ℝ → ℂ) (K : Set ℝ)
    (h : ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℝ in atTop, ∀ t ∈ K, ∃ z : ℂ, ‖z‖ < δ ∧ f x t = Complex.exp z) :
    TendstoUniformlyOn f (fun _ ↦ 1) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hexp : Tendsto Complex.exp (𝓝 0) (𝓝 1) := by
    simpa using Complex.continuous_exp.tendsto 0
  obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhds_nhds.mp hexp ε hε
  filter_upwards [h δ hδ] with x hx t ht
  obtain ⟨z, hz, hfz⟩ := hx t ht
  rw [hfz, dist_comm]
  exact hδε (by simpa using hz)

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.20), p. 652. The product
with the finite L-function tends uniformly to one on compact sets away from the pole. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  obtain ⟨x₀, -, hx₀⟩ := reciprocalHeckeEulerProductBelow_mul_normTwist χ t₀ hχ L hL hSeries K hK
    hpole (ε := 1) one_pos
  obtain ⟨C, -, hC⟩ := heckeEulerProductOscillation_bound t₀ K hK hpole
  have hH := heckeEulerProductLogCorrection_tendstoUniformly χ
  refine reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist_of_exp _ K fun δ hδ ↦ ?_
  have h1 : Tendsto (fun x : ℝ ↦ 2 * 1 / Real.log x) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  have h2 : Tendsto (fun x : ℝ ↦ C / Real.log x) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  have hδ3 : (0 : ℝ) < δ / 3 := by positivity
  filter_upwards [eventually_ge_atTop x₀, hC, h1.eventually (gt_mem_nhds hδ3),
    h2.eventually (gt_mem_nhds hδ3),
    Metric.tendstoUniformly_iff.mp hH (δ / 3) hδ3] with x hx hCx h1x h2x hHx t ht
  obtain ⟨error, -, herr⟩ := hx₀ x hx
  obtain ⟨he, heq⟩ := herr t ht
  refine ⟨_, ?_, heq⟩
  have hH' : ‖heckeEulerProductLogCorrection χ x ⟨1, t⟩‖ < δ / 3 := by
    simpa [dist_zero_left] using hHx t
  have hG := hCx t ht
  calc ‖error t + heckeEulerProductOscillation t₀ x t +
        heckeEulerProductLogCorrection χ x ⟨1, t⟩‖
      ≤ ‖error t‖ + ‖heckeEulerProductOscillation t₀ x t‖ +
        ‖heckeEulerProductLogCorrection χ x ⟨1, t⟩‖ := norm_add₃_le
    _ < δ / 3 + δ / 3 + δ / 3 := by linarith
    _ = δ := by ring

/-- Only finitely many prime powers have a given norm. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_finite (n : ℕ) :
    {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n}.Finite := by
  have hfin : {I : Ideal (𝓞 F) | I.absNorm = n}.Finite :=
    Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n
  refine Set.Finite.of_finite_image (f := fun a : V[F] × ℕ ↦ a.1.asIdeal ^ (a.2 + 1))
    (hfin.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    show (a.1.asIdeal ^ (a.2 + 1)).absNorm = n
    rw [map_pow]
    exact ha
  · rintro ⟨v, k⟩ - ⟨w, m⟩ - heq
    have heq' : v.asIdeal ^ (k + 1) = w.asIdeal ^ (m + 1) := heq
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq'.dvd)
    exact Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq'))

/-- The grouped Dirichlet term at `n` is the sum of the logarithmic terms of the prime powers
of norm `n`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_term (χ : U[F])
    (s : ℂ) (n : ℕ) :
    LSeries.term (heckePrimePowerLogCoefficient χ) s n =
      ∑ᶠ a ∈ {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.1 a.2 s := by
  have hfin := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_finite (F := F) n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    refine (finsum_mem_eq_zero_of_forall_eq_zero fun a ha ↦ ?_).symm
    have h1 := HeightOneSpectrum.one_lt_absNorm a.1
    exact absurd ha (pow_ne_zero _ (by omega))
  · have hc : heckePrimePowerLogCoefficient χ n =
        ∑ᶠ a ∈ {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
          heckeIdealValue (ideleClassNormTwist χ 0) (a.1.asIdeal ^ (a.2 + 1)) /
            ((a.2 + 1 : ℕ) : ℂ) :=
      (heckePrimePowerLogCoefficient_eq_sum χ n).trans
        (finsum_set_coe_eq_finsum_mem (f := fun a : V[F] × ℕ ↦
          heckeIdealValue (ideleClassNormTwist χ 0) (a.1.asIdeal ^ (a.2 + 1)) /
            ((a.2 + 1 : ℕ) : ℂ)) {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n})
    rw [LSeries.term_of_ne_zero hn, hc, finsum_mem_eq_finite_toFinset_sum _ hfin,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    have han : a.1.asIdeal.absNorm ^ (a.2 + 1) = n := hfin.mem_toFinset.mp ha
    delta heckePrimePowerLogTerm
    rw [map_pow, han, div_div]

/-- The terms of the correction, indexed by all prime powers, sum to minus the correction. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_hasSum (χ : U[F])
    (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    HasSum (fun a : V[F] × ℕ ↦
      if (a.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0)
      (-heckeEulerProductLogCorrection χ x s) := by
  have hg := (heckeEulerProductLogCorrection_hasSumUniformlyOn χ x hs).hasSum
    (show s.re ≤ s.re from le_refl _)
  have hj : Function.Injective
      (fun b : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)} ↦
          ((b.val.1, b.val.2 + 1) : V[F] × ℕ)) := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, m⟩, hm⟩ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  refine (hj.hasSum_iff fun a ha ↦ ?_).mp ?_
  · obtain ⟨v, k⟩ := a
    refine ite_eq_right ?_
    rintro ⟨h1, h2⟩
    cases k with
    | zero =>
      rw [zero_add, pow_one] at h2
      exact absurd h1 (not_lt.mpr h2)
    | succ k => exact ha ⟨⟨(v, k), h1, h2⟩, rfl⟩
  · convert hg using 1
    funext b
    exact ite_eq_left b.property

/-- At one prime the logarithmic terms have a sum whose exponential is the Euler factor. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_local (χ : U[F])
    (v : V[F]) {s : ℂ} (hs : 0 < s.re) :
    ∃ w : ℂ, HasSum (fun k : ℕ ↦ heckePrimePowerLogTerm χ v k s) w ∧
      Complex.exp w = finiteHeckeEulerFactor χ v s := by
  classical
  have hN1 := HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  by_cases hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have hzn : ‖(ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul,
        Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (by linarith)
    refine ⟨-Complex.log (1 - (ideleClassNormTwist χ 0).localValue v *
      (v.asIdeal.absNorm : ℂ) ^ (-s)), ?_, ?_⟩
    · convert Complex.hasSum_taylorSeries_neg_log' hzn using 1
      funext k
      have hpow : ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (k + 1) =
          (((v.asIdeal.absNorm : ℂ) ^ (k + 1)) ^ s)⁻¹ := by
        rw [← Complex.cpow_nat_mul, mul_neg, Complex.cpow_neg, Complex.natCast_cpow_natCast_mul]
      have hne : ((v.asIdeal.absNorm : ℂ) ^ (k + 1)) ^ s ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl (pow_ne_zero _ hN0))
      delta heckePrimePowerLogTerm
      rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k), ite_eq_left hu, map_pow, Nat.cast_pow,
        mul_pow, hpow]
      push_cast
      field_simp
    · rw [Complex.exp_neg, Complex.exp_log, finiteHeckeEulerFactor, ite_eq_left hu]
      intro h0
      have h1 : ‖(ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ = 1 := by
        rw [← sub_eq_zero.mp h0, norm_one]
      linarith
  · refine ⟨0, ?_, ?_⟩
    · convert hasSum_zero using 1
      funext k
      delta heckePrimePowerLogTerm
      rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k), ite_eq_right hu, zero_div]
    · rw [Complex.exp_zero, finiteHeckeEulerFactor, ite_eq_right hu]

/-- To the right of one the logarithmic terms over all prime powers are absolutely summable. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_summable (χ : U[F])
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s) := by
  classical
  have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-s.re) :=
    (summable_absNorm_rpow F hs).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-s.re) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-s.re)) ^ k := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_norm_bounded
    (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun k ↦ pow_nonneg hr0 k)) fun a ↦ ?_
  obtain ⟨v, k⟩ := a
  have hN1 := HeightOneSpectrum.one_lt_absNorm v
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hσ0 : 0 < s.re := by linarith
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos _)]
    split_ifs
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ s.re := Real.rpow_pos_of_pos hN0 _
  have hB : 0 < (2 : ℝ) ^ s.re := Real.rpow_pos_of_pos (by norm_num) _
  have hBA : (2 : ℝ) ^ s.re ≤ (v.asIdeal.absNorm : ℝ) ^ s.re :=
    Real.rpow_le_rpow (by norm_num) hN hσ0.le
  have hpow : ((v.asIdeal.absNorm ^ (k + 1) : ℕ) : ℝ) ^ s.re =
      ((v.asIdeal.absNorm : ℝ) ^ s.re) ^ (k + 1) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, mul_comm,
      Real.rpow_mul hN0.le, Real.rpow_natCast]
  show ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
      (((k + 1 : ℕ) : ℂ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)‖ ≤
    (v.asIdeal.absNorm : ℝ) ^ (-s.re) * ((2 : ℝ) ^ (-s.re)) ^ k
  rw [map_pow, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (pow_pos (by omega) _), hpow, Real.rpow_neg hN0.le,
    Real.rpow_neg (by norm_num), inv_pow]
  have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  calc ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ /
        (((k + 1 : ℕ) : ℝ) * ((v.asIdeal.absNorm : ℝ) ^ s.re) ^ (k + 1))
      ≤ 1 / (1 * ((v.asIdeal.absNorm : ℝ) ^ s.re) ^ (k + 1)) := by gcongr
    _ = ((v.asIdeal.absNorm : ℝ) ^ s.re)⁻¹ * (((v.asIdeal.absNorm : ℝ) ^ s.re) ^ k)⁻¹ := by
        rw [one_mul, pow_succ, one_div, mul_inv, mul_comm]
    _ ≤ ((v.asIdeal.absNorm : ℝ) ^ s.re)⁻¹ * (((2 : ℝ) ^ s.re) ^ k)⁻¹ := by
        gcongr

/-- To the right of one, the reciprocal product times the L-value is the exponential of the
sum of the logarithmic terms over the primes of norm at least `x`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_primes (χ : U[F])
    (x : ℝ) (s : halfPlane) :
    ∃ w : ℂ, HasSum (fun a : V[F] × ℕ ↦
        if x ≤ (a.1.asIdeal.absNorm : ℝ) then heckePrimePowerLogTerm χ a.1 a.2 s else 0) w ∧
      reciprocalHeckeEulerProductBelow χ x s * finiteHeckeL χ s = Complex.exp w := by
  classical
  have hs1 : 1 < (s : ℂ).re := s.property
  have hs0 : 0 < (s : ℂ).re := by linarith
  choose w hw hexp using fun v : V[F] ↦
      reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_local χ v hs0
  have hsum := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_summable χ hs1
  have hg : Summable (fun a : V[F] × ℕ ↦
      if x ≤ (a.1.asIdeal.absNorm : ℝ) then heckePrimePowerLogTerm χ a.1 a.2 s else 0) := by
    refine Summable.of_norm_bounded hsum.norm fun a ↦ ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  refine ⟨_, hg.hasSum, ?_⟩
  have hfib : HasSum (fun v : V[F] ↦ if x ≤ (v.asIdeal.absNorm : ℝ) then w v else 0)
      (∑' a : V[F] × ℕ, if x ≤ (a.1.asIdeal.absNorm : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0) := by
    refine hg.hasSum.prod_fiberwise fun v ↦ ?_
    by_cases hxv : x ≤ (v.asIdeal.absNorm : ℝ)
    · simp only [hxv, ↓reduceIte]
      exact hw v
    · simp only [hxv, ↓reduceIte]
      exact hasSum_zero
  have hprod := hfib.cexp
  have hL := finiteHeckeL_hasProd χ s
  have hP : HasProd (fun v : V[F] ↦ if v ∈ heckePrimesBelow F x then
      (finiteHeckeEulerFactor χ v s)⁻¹ else 1) (reciprocalHeckeEulerProductBelow χ x s) := by
    have h := hasProd_prod_of_ne_finset_one (f := fun v : V[F] ↦
      if v ∈ heckePrimesBelow F x then (finiteHeckeEulerFactor χ v s)⁻¹ else 1)
      (s := heckePrimesBelow F x) (L := SummationFilter.unconditional V[F])
      (fun v hv ↦ ite_eq_right hv)
    convert h using 1
    delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
    exact Finset.prod_congr rfl fun v hv ↦ (ite_eq_left hv).symm
  refine (hP.mul hL).unique ?_
  convert hprod using 1
  funext v
  have hne : finiteHeckeEulerFactor χ v s ≠ 0 := by
    rw [← hexp v]
    exact Complex.exp_ne_zero _
  show _ = Complex.exp (if x ≤ (v.asIdeal.absNorm : ℝ) then w v else 0)
  by_cases hxv : x ≤ (v.asIdeal.absNorm : ℝ)
  · rw [ite_eq_left hxv, ite_eq_right
      (fun h ↦ absurd ((heckePrimesBelow_mem_iff v x).mp h) (not_lt.mpr hxv)), one_mul, hexp v]
  · rw [ite_eq_right hxv, ite_eq_left ((heckePrimesBelow_mem_iff v x).mpr (not_le.mp hxv)),
      inv_mul_cancel₀ hne, Complex.exp_zero]

/-- To the right of one the ordered tail is summable and the product comparison holds. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_of_one_lt_re
    (χ : U[F]) (x : ℝ) (s : halfPlane) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * finiteHeckeL χ s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  classical
  have hs1 : 1 < (s : ℂ).re := s.property
  obtain ⟨w, hw, hexp⟩ := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_primes χ x s
  have hsum := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_summable χ hs1
  have hg2 : Summable (fun a : V[F] × ℕ ↦
      if x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0) := by
    refine Summable.of_norm_bounded hsum.norm fun a ↦ ?_
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  have hfib := hg2.hasSum.tsum_fiberwise (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 1))
  have hterm : ∀ n : ℕ,
      (∑' b : (fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)) ⁻¹' {n},
        if x ≤ ((b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) : ℕ) : ℝ) then
          heckePrimePowerLogTerm χ b.val.1 b.val.2 s else 0) =
      heckePrimePowerLogTailTerm χ x s n := by
    intro n
    have hfin := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_finite (F := F) n
    have hfinite : Finite ((fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)) ⁻¹' {n}) :=
      hfin.to_subtype
    rw [tsum_eq_finsum (Set.toFinite _)]
    delta heckePrimePowerLogTailTerm
    rw [reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_term χ s n]
    refine (finsum_set_coe_eq_finsum_mem (f := fun a : V[F] × ℕ ↦
      if x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0)
      ((fun a : V[F] × ℕ ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)) ⁻¹' {n})).trans ?_
    by_cases hxn : x ≤ (n : ℝ)
    · rw [ite_eq_left hxn]
      refine finsum_mem_congr rfl fun a ha ↦ ?_
      have han : a.1.asIdeal.absNorm ^ (a.2 + 1) = n := ha
      rw [ite_eq_left (by rw [han]; exact hxn)]
    · rw [ite_eq_right hxn]
      refine finsum_mem_eq_zero_of_forall_eq_zero fun a ha ↦ ?_
      have han : a.1.asIdeal.absNorm ^ (a.2 + 1) = n := ha
      rw [ite_eq_right (by rw [han]; exact hxn)]
  have hT : HasSum (fun n : ℕ ↦ heckePrimePowerLogTailTerm χ x s n)
      (∑' a : V[F] × ℕ, if x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0) (SummationFilter.conditional ℕ) := by
    rw [← funext hterm]
    exact Tendsto.mono_left hfib (SummationFilter.conditional ℕ).le_atTop
  have htail : heckePrimePowerLogTail χ x s =
      ∑' a : V[F] × ℕ, if x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) then
        heckePrimePowerLogTerm χ a.1 a.2 s else 0 := hT.tsum_eq
  refine ⟨hT.summable, ?_⟩
  have hH := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_hasSum χ x s
    (by linarith : 1 / 2 < (s : ℂ).re)
  have hdiff := hg2.hasSum.sub hH
  have hw' : HasSum (fun a : V[F] × ℕ ↦
      if x ≤ (a.1.asIdeal.absNorm : ℝ) then heckePrimePowerLogTerm χ a.1 a.2 s else 0)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
    rw [htail, ← sub_neg_eq_add]
    convert hdiff using 1
    funext a
    have hle : (a.1.asIdeal.absNorm : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero _) _
    by_cases hxa : x ≤ (a.1.asIdeal.absNorm : ℝ)
    · rw [ite_eq_left hxa, ite_eq_left (hxa.trans hle),
        ite_eq_right (fun h ↦ absurd h.1 (not_lt.mpr hxa)), sub_zero]
    · rw [ite_eq_right hxa]
      by_cases hxp : x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)
      · rw [ite_eq_left hxp, ite_eq_left ⟨not_le.mp hxa, hxp⟩, sub_self]
      · rw [ite_eq_right hxp, ite_eq_right (fun h ↦ hxp h.2), sub_zero]
  rw [hexp, hw.unique hw']

/-- Summation by parts against the remainders `S (i + 1) - T`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_abel_parts
    (φ ψ c S : ℕ → ℂ) (T : ℂ) (hc0 : c 0 = 0) (hψ0 : ψ 0 = 1)
    (hψ : ∀ n, ψ (n + 1) = φ (n + 1)) (hS0 : S 0 = 0) (hS : ∀ n, S (n + 1) = S n + c n) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), φ n * c n) - T =
      ψ N * (S (N + 1) - T) + ∑ i ∈ Finset.range N, (ψ i - ψ (i + 1)) * (S (i + 1) - T) := by
  induction N with
  | zero => simp [hc0, hψ0, hS, hS0]
  | succ N ih =>
    rw [Finset.sum_range_succ (fun n ↦ φ n * c n) (N + 1),
      Finset.sum_range_succ (fun i ↦ (ψ i - ψ (i + 1)) * (S (i + 1) - T)) N, hS (N + 1), hψ N]
    linear_combination ih

/-- Abel's limit theorem for Dirichlet weights: if the partial sums of `c` tend to `T` and
`c 0 = 0`, then the limits of the sums weighted by `n ^ (-δ)` tend to `T` as `δ → 0⁺`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_abel (c : ℕ → ℂ)
    (T : ℂ) (hc0 : c 0 = 0)
    (hc : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, c n) atTop (𝓝 T))
    (A : ℝ → ℂ)
    (hA : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N, (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * c n) atTop (𝓝 (A δ))) :
    Tendsto A (𝓝[>] 0) (𝓝 T) := by
  have hR : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, c n) - T) atTop (𝓝 0) := by
    simpa using hc.sub_const T
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ N : ℕ, ‖(∑ n ∈ Finset.range N, c n) - T‖ ≤ B := by
    obtain ⟨B, hB⟩ := hR.norm.bddAbove_range
    exact ⟨B, fun N ↦ hB (Set.mem_range_self N)⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hR (ε / 2) (by positivity)
  have hm1 : (1 : ℝ) ≤ ((max M 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right M 1
  have hlog : 0 ≤ Real.log ((max M 1 : ℕ) : ℝ) := Real.log_nonneg hm1
  refine ⟨ε / (4 * (B * Real.log ((max M 1 : ℕ) : ℝ) + 1)), by positivity, fun {δ} hδ hδlt ↦ ?_⟩
  have hδ0 : 0 < δ := hδ
  rw [Real.dist_eq, sub_zero, abs_of_pos hδ0] at hδlt
  have hupos : ∀ i : ℕ, (0 : ℝ) < ((max i 1 : ℕ) : ℝ) := fun i ↦ by
    exact_mod_cast lt_of_lt_of_le one_pos (le_max_right i 1)
  have hu1 : ∀ i : ℕ, ((max i 1 : ℕ) : ℝ) ^ (-δ) ≤ 1 := fun i ↦
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast le_max_right i 1) (by linarith)
  have hu0 : ∀ i : ℕ, 0 ≤ ((max i 1 : ℕ) : ℝ) ^ (-δ) := fun i ↦
    (Real.rpow_pos_of_pos (hupos i) _).le
  have hanti : ∀ i : ℕ, ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ) ≤ ((max i 1 : ℕ) : ℝ) ^ (-δ) := fun i ↦
    Real.rpow_le_rpow_of_nonpos (hupos i)
      (by exact_mod_cast max_le_max (Nat.le_succ i) le_rfl) (by linarith)
  have hid := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_abel_parts
      (fun n ↦ (((n : ℝ) ^ (-δ) : ℝ) : ℂ))
    (fun i ↦ ((((max i 1 : ℕ) : ℝ) ^ (-δ) : ℝ) : ℂ)) c (fun N ↦ ∑ n ∈ Finset.range N, c n) T hc0
    (by simp) (fun n ↦ by simp) (by simp) (fun n ↦ Finset.sum_range_succ c n)
  -- the bound for large N
  have hbound : ∀ N ≥ M, ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * c n) - T‖ ≤
      ‖(∑ n ∈ Finset.range (N + 1), c n) - T‖ +
        (B * (1 - ((max M 1 : ℕ) : ℝ) ^ (-δ)) + ε / 2) := by
    intro N hN
    rw [hid N]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hu0 N)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hu1 N)
    · refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ i : ℕ, ‖((((max i 1 : ℕ) : ℝ) ^ (-δ) : ℝ) : ℂ) -
          ((((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ) : ℝ) : ℂ)‖ =
          ((max i 1 : ℕ) : ℝ) ^ (-δ) - ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ) := fun i ↦ by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hanti i))]
      simp only [norm_mul, hterm]
      rw [← Finset.sum_range_add_sum_Ico _ hN]
      have h1 : ∑ i ∈ Finset.range M, (((max i 1 : ℕ) : ℝ) ^ (-δ) -
          ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ)) * ‖(∑ n ∈ Finset.range (i + 1), c n) - T‖ ≤
          B * (1 - ((max M 1 : ℕ) : ℝ) ^ (-δ)) := by
        calc _ ≤ ∑ i ∈ Finset.range M, (((max i 1 : ℕ) : ℝ) ^ (-δ) -
              ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ)) * B :=
              Finset.sum_le_sum fun i _ ↦
                mul_le_mul_of_nonneg_left (hB _) (sub_nonneg.mpr (hanti i))
          _ = B * (1 - ((max M 1 : ℕ) : ℝ) ^ (-δ)) := by
              rw [← Finset.sum_mul, Finset.sum_range_sub' (fun i ↦ ((max i 1 : ℕ) : ℝ) ^ (-δ))]
              simp [mul_comm]
      have h2 : ∑ i ∈ Finset.Ico M N, (((max i 1 : ℕ) : ℝ) ^ (-δ) -
          ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ)) * ‖(∑ n ∈ Finset.range (i + 1), c n) - T‖ ≤
          ε / 2 := by
        calc _ ≤ ∑ i ∈ Finset.Ico M N, (((max i 1 : ℕ) : ℝ) ^ (-δ) -
              ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ)) * (ε / 2) :=
              Finset.sum_le_sum fun i hi ↦ by
                refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.mpr (hanti i))
                have h := hM (i + 1) ((Finset.mem_Ico.mp hi).1.trans (Nat.le_succ i))
                rw [dist_zero_right] at h
                exact h.le
          _ ≤ ∑ i ∈ Finset.range N, (((max i 1 : ℕ) : ℝ) ^ (-δ) -
              ((max (i + 1) 1 : ℕ) : ℝ) ^ (-δ)) * (ε / 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
                (fun i _ _ ↦ mul_nonneg (sub_nonneg.mpr (hanti i)) (by positivity))
          _ ≤ ε / 2 := by
              rw [← Finset.sum_mul, Finset.sum_range_sub' (fun i ↦ ((max i 1 : ℕ) : ℝ) ^ (-δ))]
              have h3 : ((max 0 1 : ℕ) : ℝ) ^ (-δ) = 1 := by simp
              rw [h3]
              have h4 := hu0 N
              nlinarith
      linarith
  -- pass to the limit
  have hlim1 : Tendsto (fun N : ℕ ↦
      ‖(∑ n ∈ Finset.range (N + 1), (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * c n) - T‖) atTop
      (𝓝 ‖A δ - T‖) :=
    (((hA δ hδ0).comp (tendsto_add_atTop_nat 1)).sub_const T).norm
  have hlim2 : Tendsto (fun N : ℕ ↦ ‖(∑ n ∈ Finset.range (N + 1), c n) - T‖ +
      (B * (1 - ((max M 1 : ℕ) : ℝ) ^ (-δ)) + ε / 2)) atTop
      (𝓝 (0 + (B * (1 - ((max M 1 : ℕ) : ℝ) ^ (-δ)) + ε / 2))) := by
    have h := (hR.comp (tendsto_add_atTop_nat 1)).norm
    rw [norm_zero] at h
    exact h.add_const _
  have hle := le_of_tendsto_of_tendsto hlim1 hlim2
    (eventually_atTop.mpr ⟨M, fun N hN ↦ hbound N hN⟩)
  rw [zero_add] at hle
  -- small δ
  have hexp : 1 - ((max M 1 : ℕ) : ℝ) ^ (-δ) ≤ δ * Real.log ((max M 1 : ℕ) : ℝ) := by
    rw [Real.rpow_def_of_pos (hupos M)]
    have h := Real.add_one_le_exp (Real.log ((max M 1 : ℕ) : ℝ) * -δ)
    linarith
  have hden : 0 < 4 * (B * Real.log ((max M 1 : ℕ) : ℝ) + 1) := by positivity
  have hδ4 : δ * (4 * (B * Real.log ((max M 1 : ℕ) : ℝ) + 1)) < ε := (lt_div_iff₀ hden).mp hδlt
  rw [dist_eq_norm]
  have hBL : 0 ≤ B * Real.log ((max M 1 : ℕ) : ℝ) := mul_nonneg hB0 hlog
  nlinarith [mul_le_mul_of_nonneg_left hexp hB0]

/-- The reciprocal partial product is continuous in the complex argument. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuous_prod
    (χ : U[F]) (x : ℝ) :
    Continuous (fun z : ℂ ↦ reciprocalHeckeEulerProductBelow χ x z) := by
  have hfun : (fun z : ℂ ↦ reciprocalHeckeEulerProductBelow χ x z) = fun z : ℂ ↦
      ∏ v ∈ heckePrimesBelow F x, (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
        (v.asIdeal.absNorm : ℂ) ^ (-z)) :=
    funext fun z ↦ reciprocalHeckeEulerProductBelow_eq_prod χ x z
  rw [hfun]
  refine continuous_finsetProd _ fun v _ ↦ continuous_const.sub (continuous_const.mul ?_)
  refine continuous_neg.const_cpow (Or.inl ?_)
  have h1 := HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)

/-- Each logarithmic term is continuous in the complex argument. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuous_term
    (χ : U[F]) (v : V[F]) (k : ℕ) :
    Continuous (fun z : ℂ ↦ heckePrimePowerLogTerm χ v k z) := by
  have hN0 : ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact pow_ne_zero _ v.ne_bot
  delta heckePrimePowerLogTerm
  exact continuous_const.div (continuous_const.mul (continuous_id.const_cpow (Or.inl hN0)))
    fun z ↦ mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl hN0))

/-- The correction is continuous at every point to the right of one half. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuousAt
    (χ : U[F]) (x : ℝ) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    ContinuousAt (fun z : ℂ ↦ heckeEulerProductLogCorrection χ x z) s := by
  obtain ⟨σ, hσ1, hσ2⟩ := exists_between hs
  have hu := (heckeEulerProductLogCorrection_hasSumUniformlyOn χ x hσ1).tendstoUniformlyOn
  have hc : ContinuousOn (fun z ↦ -heckeEulerProductLogCorrection χ x z)
      {z : ℂ | σ ≤ z.re} := by
    exact hu.continuousOn (Eventually.of_forall fun I ↦
      (continuous_finsetSum I fun a _ ↦
        reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuous_term χ a.val.1
            (a.val.2 + 1)).continuousOn).frequently
  have hmem : {z : ℂ | σ ≤ z.re} ∈ 𝓝 s :=
    Filter.mem_of_superset
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσ2) fun z hz ↦ le_of_lt hz
  have h := (hc.continuousAt hmem).neg
  simpa using h

/-- A continuation of the completed L-function with the same orders as `L` on `Re s > 0`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_completed (χ : U[F])
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ Λ : ℂ → ℂ, MeromorphicNFOn Λ univ ∧ (∀ s : halfPlane, Λ s = completedHeckeL χ s) ∧
      ∀ s : ℂ, 0 < s.re → meromorphicOrderAt Λ s = meromorphicOrderAt L s := by
  have hΓ (w : ℂ) (hw : 0 < w.re) : AnalyticAt ℂ (heckeGammaFactor χ) w :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos χ hz).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hw)
  have hM : MeromorphicOn (fun w ↦ heckeGammaFactor χ w * L w) univ := fun w _ ↦
    (meromorphic_heckeGammaFactor χ w).mul (hL (mem_univ w)).meromorphicAt
  refine ⟨toMeromorphicNFOn (fun w ↦ heckeGammaFactor χ w * L w) univ,
    meromorphicNFOn_toMeromorphicNFOn _ _, fun z ↦ ?_, fun s hs ↦ ?_⟩
  · have hz : 0 < (z : ℂ).re := zero_lt_one.trans z.property
    have hMan : AnalyticAt ℂ (fun w ↦ heckeGammaFactor χ w * L w) z :=
      (hΓ z hz).mul (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries z).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    show heckeGammaFactor χ z * L z = completedHeckeL χ z
    rw [hSeries z]
    rfl
  · rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hΓ s hs) (heckeGammaFactor_ne_zero_of_re_pos χ hs)

/-- On and to the right of the 1-line, the continuation for a character that is nontrivial
on norm-one classes has neither a zero nor a pole. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_order (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) : meromorphicOrderAt L s = 0 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
    obtain ⟨B, hB, hB'⟩ := h F χ
    refine hB' L hL hSeries s ?_
    have hlog : 0 < Real.log (B * (|s.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg s.im])
    have h0 : 0 ≤ A / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|s.im| + 3))) :=
      div_nonneg hA.le (mul_nonneg (by positivity) hlog.le)
    linarith
  · obtain ⟨Λ, hΛ, hΛs, hord⟩ :=
      reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_completed χ L hL hSeries
    have hd := completedHeckeL_continuation_entire χ Λ hΛ hΛs hχ
    rw [← hord s (by linarith)]
    exact (hd.analyticAt s).meromorphicOrderAt_nonneg

/-- For a pure norm character the continuation has a pole at the pole ordinate. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_pole (χ : U[F])
    (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    meromorphicOrderAt L ⟨1, t₀⟩ ≠ 0 := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ :=
      reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_completed χ L hL hSeries
  obtain ⟨t₁, ⟨ht₁, -, hp, -⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Λ hΛ hΛs htriv
  have ht : t₁ = t₀ :=
    (heckeIdealSummatory_tendsto_of_trivial_on_normOne χ htriv).1.unique ht₁ hχ
  have hpt : (⟨1, t₀⟩ : ℂ) = 1 + Complex.I * (t₁ : ℂ) := by
    rw [ht]
    apply Complex.ext <;> simp
  rw [hpt, ← hord _ (by simp), hp]
  decide

/-- At a regular nonzero point of the 1-line the ordered tail is summable. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_boundary (χ : U[F])
    (x : ℝ)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (t : ℝ) (hregular : meromorphicOrderAt L ⟨1, t⟩ = 0) :
    Summable (heckePrimePowerLogTailTerm χ x ⟨1, t⟩) (SummationFilter.conditional ℕ) := by
  have h1 : ∃ x' : ℝ, x ≤ x' ∧ ∃ T' : ℂ, Tendsto (fun N : ℕ ↦
      ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x' ⟨1, t⟩ n) atTop (𝓝 T') := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t₀, ht₀, -⟩ := (heckeIdealSummatory_tendsto_of_trivial_on_normOne χ hχ).1
      have hne : t ≠ t₀ := fun h ↦
          reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_pole χ t₀ ht₀ hχ L hL
          hSeries (by
        rw [← h]
        exact hregular)
      obtain ⟨x₀, -, hx₀⟩ := heckePrimePowerLogTail_normTwist χ t₀ ht₀ {t} isCompact_singleton
        (fun h ↦ hne (mem_singleton_iff.mp h).symm) (ε := 1) one_pos
      exact ⟨max x₀ x, le_max_right _ _, _,
        (hx₀ _ (le_max_left _ _)).1.tendsto_at (mem_singleton t)⟩
    · obtain ⟨x₀, -, hx₀⟩ := heckePrimePowerLogTail_of_nontrivial_on_normOne χ hχ {t}
        isCompact_singleton (ε := 1) one_pos
      exact ⟨max x₀ x, le_max_right _ _, _,
        (hx₀ _ (le_max_left _ _)).1.tendsto_at (mem_singleton t)⟩
  obtain ⟨x', hxx', T', hT'⟩ := h1
  have hd : ∀ n ≥ ⌈x'⌉₊, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n -
      heckePrimePowerLogTailTerm χ x' ⟨1, t⟩ n = 0 := by
    intro n hn
    have hx'n : x' ≤ (n : ℝ) := Nat.ceil_le.mp hn
    delta heckePrimePowerLogTailTerm
    rw [ite_eq_left hx'n, ite_eq_left (hxx'.trans hx'n), sub_self]
  have hconst : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
      (heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n - heckePrimePowerLogTailTerm χ x' ⟨1, t⟩ n)) atTop
      (𝓝 (∑ n ∈ Finset.range ⌈x'⌉₊,
        (heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n - heckePrimePowerLogTailTerm χ x' ⟨1, t⟩ n))) :=
    tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨⌈x'⌉₊, fun N hN ↦
      (Finset.eventually_constant_sum hd hN).symm⟩)
  have hhas : HasSum (heckePrimePowerLogTailTerm χ x ⟨1, t⟩)
      (T' + ∑ n ∈ Finset.range ⌈x'⌉₊, (heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n -
        heckePrimePowerLogTailTerm χ x' ⟨1, t⟩ n)) (SummationFilter.conditional ℕ) := by
    show Tendsto _ (SummationFilter.conditional ℕ).filter _
    rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    refine (hT'.add hconst).congr fun N ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ ↦ by ring
  exact hhas.summable

/-- At a regular nonzero point on or to the right of the 1-line the ordered tail is summable
and the product comparison holds. -/
private theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_exp_logTail (χ : U[F])
    {x : ℝ} (hx : 1 < x)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) (hregular : meromorphicOrderAt L s = 0) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * L s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  rcases hs.lt_or_eq with h1 | h1
  · have h := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_of_one_lt_re χ x ⟨s, h1⟩
    rw [← hSeries ⟨s, h1⟩] at h
    exact h
  · have hst : s = ⟨1, s.im⟩ := Complex.ext h1.symm rfl
    have hsumm : Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) := by
      rw [hst]
      exact reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_boundary χ x L hL hSeries
          s.im (hst ▸ hregular)
    refine ⟨hsumm, ?_⟩
    have hc : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x s n)
        atTop (𝓝 (heckePrimePowerLogTail χ x s)) := by
      have h : Tendsto (fun I : Finset ℕ ↦ ∑ n ∈ I, heckePrimePowerLogTailTerm χ x s n)
          (SummationFilter.conditional ℕ).filter (𝓝 (heckePrimePowerLogTail χ x s)) :=
        hsumm.hasSum
      rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at h
      exact h
    have hc0 : heckePrimePowerLogTailTerm χ x s 0 = 0 := by
      delta heckePrimePowerLogTailTerm
      exact ite_eq_right (by
        push_cast
        linarith)
    have hpt : ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, heckePrimePowerLogTailTerm χ x (s + δ) n =
        (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * heckePrimePowerLogTailTerm χ x s n := by
      intro δ hδ n
      delta heckePrimePowerLogTailTerm
      split_ifs
      · rcases eq_or_ne n 0 with rfl | hn
        · simp
        · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
            Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn),
            Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg, Complex.cpow_neg,
            Complex.ofReal_natCast]
          field_simp
      · rw [mul_zero]
    have hA : ∀ δ : ℝ, 0 < δ → Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N,
        (((n : ℝ) ^ (-δ) : ℝ) : ℂ) * heckePrimePowerLogTailTerm χ x s n) atTop
        (𝓝 (heckePrimePowerLogTail χ x (s + δ))) := by
      intro δ hδ
      have hre : 1 < (s + (δ : ℂ)).re := by
        rw [Complex.add_re, Complex.ofReal_re]
        linarith
      have h : Tendsto (fun I : Finset ℕ ↦ ∑ n ∈ I, heckePrimePowerLogTailTerm χ x (s + δ) n)
          (SummationFilter.conditional ℕ).filter (𝓝 (heckePrimePowerLogTail χ x (s + δ))) :=
        (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_of_one_lt_re χ x
            ⟨s + δ, hre⟩).1.hasSum
      rw [SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at h
      exact h.congr fun N ↦ Finset.sum_congr rfl fun n _ ↦ hpt δ hδ n
    have habel := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_abel _ _ hc0 hc
        (fun δ : ℝ ↦ heckePrimePowerLogTail χ x (s + δ)) hA
    have hshift : Tendsto (fun δ : ℝ ↦ s + (δ : ℂ)) (𝓝[>] 0) (𝓝 s) := by
      have h : Tendsto (fun δ : ℝ ↦ s + (δ : ℂ)) (𝓝 0) (𝓝 (s + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      rw [Complex.ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hH := (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuousAt χ x
        (s := s) (by linarith)).tendsto.comp hshift
    have hLan : AnalyticAt ℂ L s :=
      (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hregular.ge
    have hlhs := (((reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_continuous_prod χ
        x).continuousAt (x := s)).mul
      hLan.continuousAt).tendsto.comp hshift
    have hrhs := (habel.add hH).cexp
    refine tendsto_nhds_unique (hlhs.congr' ?_) hrhs
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ0 : (0 : ℝ) < δ := hδ
    have hre : 1 < (s + (δ : ℂ)).re := by
      rw [Complex.add_re, Complex.ofReal_re]
      linarith
    have h := (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_of_one_lt_re χ x
        ⟨s + δ, hre⟩).2
    rw [← hSeries ⟨s + δ, hre⟩] at h
    exact h

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.21), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function has an exponential comparison on every compact set of ordinates.
Deviation: Uses `+ H_x` from the definition of the correction, in agreement
with (B.7.2.18). Real cutoffs have the same strict norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  obtain ⟨x₀, hx₀, h⟩ := heckePrimePowerLogTail_of_nontrivial_on_normOne χ hχ K hK hε
  refine ⟨x₀, hx₀, fun x hx ↦ ?_⟩
  obtain ⟨-, hcont, hbound⟩ := h x hx
  refine ⟨fun t ↦ heckePrimePowerLogTail χ x ⟨1, t⟩, hcont, fun t ht ↦ ⟨(hbound t ht).le, ?_⟩⟩
  exact (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_exp_logTail χ
    (hx₀.trans_le hx) L hL hSeries ⟨1, t⟩ le_rfl
    (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_order χ hχ L hL hSeries
      ⟨1, t⟩ le_rfl)).2

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.22), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function tends uniformly to one on every compact set of ordinates. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  obtain ⟨x₀, -, hx₀⟩ := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne χ hχ L hL
    hSeries K hK (ε := 1) one_pos
  have hH := heckeEulerProductLogCorrection_tendstoUniformly χ
  refine reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist_of_exp _ K fun δ hδ ↦ ?_
  have h1 : Tendsto (fun x : ℝ ↦ 2 * 1 / Real.log x) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  have hδ2 : (0 : ℝ) < δ / 2 := by positivity
  filter_upwards [eventually_ge_atTop x₀, h1.eventually (gt_mem_nhds hδ2),
    Metric.tendstoUniformly_iff.mp hH (δ / 2) hδ2] with x hx h1x hHx t ht
  obtain ⟨error, -, herr⟩ := hx₀ x hx
  obtain ⟨he, heq⟩ := herr t ht
  refine ⟨_, ?_, heq⟩
  have hH' : ‖heckeEulerProductLogCorrection χ x ⟨1, t⟩‖ < δ / 2 := by
    simpa [dist_zero_left] using hHx t
  calc ‖error t + heckeEulerProductLogCorrection χ x ⟨1, t⟩‖
      ≤ ‖error t‖ + ‖heckeEulerProductLogCorrection χ x ⟨1, t⟩‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

/-- Paper: Equation (B.7.2.23), p. 653. At a regular nonzero point of the
continued L-function on or to the right of the 1-line, the norm-ordered
logarithmic tail and its correction give the reciprocal product comparison.
Deviation: Uses `+ H_x` and exponentiates to avoid selecting a logarithm branch.
The convergence of the ordered sum is explicit. -/
theorem reciprocalHeckeEulerProductBelow_mul_eq_exp_logTail (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) (hregular : meromorphicOrderAt L s = 0) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * L s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  exact reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_exp_logTail χ hx L hL
    hSeries s hs hregular

/-- At fixed norm the logarithmic Dirichlet coefficient is a finite sum, so its
prime-power expansion works without any convergence assumption on the abscissa. -/
private theorem heckePrimePowerLogTail_add_correction_at_norm (χ : U[F]) (s : ℂ) (n : ℕ) :
    LSeries.term (heckePrimePowerLogCoefficient χ) s n =
      ∑' a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 s := by
  classical
  let A := {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
  change _ = ∑' a : A, _
  by_cases hn : n = 0
  · have : IsEmpty A := ⟨fun a ↦ by
        have h := pow_ne_zero (a.val.2 + 1) (Ideal.absNorm_eq_zero_iff.not.mpr a.val.1.ne_bot)
        exact h (a.property.trans hn)⟩
    rw [tsum_empty, hn, LSeries.term_zero]
  have : Finite A := heckePrimePowerLogTail_fiber_finite n
  have : Fintype A := Fintype.ofFinite _
  have hterm (a : A) : heckePrimePowerLogTerm χ a.val.1 a.val.2 s =
      (heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
        ((a.val.2 + 1 : ℕ) : ℂ)) / (n : ℂ) ^ s := by
    unfold heckePrimePowerLogTerm
    rw [map_pow, a.property, div_div]
  rw [tsum_fintype, LSeries.term_of_ne_zero hn, heckePrimePowerLogCoefficient_eq_sum,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  exact Finset.sum_congr rfl (fun a _ ↦ (hterm a).symm)

/-- Split the prime powers of fixed norm into surviving primes and the higher
powers of primes below the cutoff. Each fiber is finite, even on the one-line. -/
private theorem heckePrimePowerLogTail_add_correction_split (χ : U[F]) (x : ℝ) (s : ℂ) (n : ℕ) :
    let S := {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
    let N (a : S) := a.val.1.asIdeal.absNorm ^ (a.val.2 + 2)
    (∑ᶠ a : {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) +
      (∑' a : N ⁻¹' {n}, heckePrimePowerLogTerm χ a.val.val.1 (a.val.val.2 + 1) s) =
      heckePrimePowerLogTailTerm χ x s n := by
  classical
  intro S N
  let A := {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
  let H := {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
  let L := ↥(N ⁻¹' {n})
  let f (a : A) := heckePrimePowerLogTerm χ a.val.1 a.val.2 s
  let p (a : A) := x ≤ (a.val.1.asIdeal.absNorm : ℝ)
  change (∑ᶠ a : H, _) + (∑' a : L, _) = _
  by_cases hx : x ≤ (n : ℝ)
  · let e : H ≃ {a : A // p a} :=
      { toFun := fun a ↦ ⟨⟨a.val, a.property.2⟩, a.property.1⟩
        invFun := fun a ↦ ⟨a.val.val, a.property, a.val.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    let l : L ≃ {a : A // ¬ p a} :=
      { toFun := fun a ↦ ⟨⟨(a.val.val.1, a.val.val.2 + 1), a.property⟩, not_le.mpr a.val.property.1⟩
        invFun := fun b ↦ by
          obtain ⟨⟨⟨v, k⟩, hn⟩, hb⟩ := b
          cases k with
          | zero =>
            have e : v.asIdeal.absNorm = n := by simpa using hn
            exact (hb (by simpa [p, e] using hx)).elim
          | succ j =>
            have hnx : x ≤ ((v.asIdeal.absNorm ^ (j + 2) : ℕ) : ℝ) := by
              change x ≤ ((v.asIdeal.absNorm ^ (j + 1 + 1) : ℕ) : ℝ)
              rw [hn]
              exact hx
            exact ⟨⟨(v, j), lt_of_not_ge hb, hnx⟩, hn⟩
        left_inv := fun a ↦ by rfl
        right_inv := fun b ↦ by
          obtain ⟨⟨⟨v, _|k⟩, hn⟩, hb⟩ := b
          · have e : v.asIdeal.absNorm = n := by simpa using hn
            exact (hb (by simpa [p, e] using hx)).elim
          · rfl }
    have : Finite A := heckePrimePowerLogTail_fiber_finite n
    have : Fintype A := Fintype.ofFinite _
    have : Fintype H := Fintype.ofEquiv _ e.symm
    have : Fintype L := Fintype.ofEquiv _ l.symm
    simp only [heckePrimePowerLogTailTerm, hx, ↓reduceIte, heckePrimePowerLogTail_add_correction_at_norm,
      finsum_eq_sum_of_fintype, tsum_fintype]
    exact (congrArg₂ (· + ·)
      (Fintype.sum_equiv e (fun a ↦ heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (fun a ↦ f a.val)
        (fun _ ↦ rfl))
      (Fintype.sum_equiv l (fun a ↦ heckePrimePowerLogTerm χ a.val.val.1 (a.val.val.2 + 1) s)
        (fun a ↦ f a.val) (fun _ ↦ rfl))).trans (Fintype.sum_subtype_add_sum_subtype p f)
  · have : IsEmpty H := ⟨fun a ↦ by
        have hp : a.val.1.asIdeal.absNorm ≤ a.val.1.asIdeal.absNorm ^ (a.val.2 + 1) :=
          Nat.le_self_pow (by omega) _
        rw [a.property.2] at hp
        exact hx (a.property.1.trans (by exact_mod_cast hp))⟩
    have : IsEmpty L := ⟨fun a ↦ by
        have e : N a.val = n := a.property
        have h : x ≤ (N a.val : ℝ) := a.val.property.2
        exact hx (e ▸ h)⟩
    simp [heckePrimePowerLogTailTerm, hx, finsum_of_isEmpty]

/-- Paper: Equation (B.7.2.23), p. 653. The logarithmic tail restricted to
primes of norm at least `x`, grouped by prime-power norm, is the full
prime-power tail plus the cutoff correction.
Deviation: Adds `H_x`, which already carries the minus sign. -/
theorem heckePrimePowerLogTail_add_correction (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hsum : Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)) :
    HasSum (fun n : ℕ ↦
      ∑ᶠ a : {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧
        a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 s)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s)
      (SummationFilter.conditional ℕ) := by
  let S := {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
    x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  let N (a : S) := a.val.1.asIdeal.absNorm ^ (a.val.2 + 2)
  let g (a : S) := heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s
  have h := (heckeEulerProductLogCorrection_hasSumUniformlyOn χ x hs).hasSum (show s.re ≤ s.re from le_rfl)
  have ht : HasSum g (-heckeEulerProductLogCorrection χ x s) := h
  have hgroup := ht.tsum_fiberwise N
  have hgroup' := hgroup.mono_left (SummationFilter.conditional ℕ).le_atTop
  have hsub := hsum.hasSum.sub hgroup'
  rw [sub_neg_eq_add] at hsub
  apply hsub.congr_fun
  intro n
  exact eq_sub_iff_add_eq.mpr (heckePrimePowerLogTail_add_correction_split χ x s n)

/-- If continuous functions `P x` satisfy `P x * L → 1` uniformly on a compact set, then
their reciprocals tend uniformly to `L` there. -/
private theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_inv
    (P : ℝ → ℝ → ℂ) (L : ℝ → ℂ) (K : Set ℝ) (hK : IsCompact K)
    (hP : ∀ x : ℝ, ContinuousOn (P x) K)
    (h : TendstoUniformlyOn (fun x : ℝ ↦ fun t : ℝ ↦ P x t * L t) (fun _ ↦ 1) atTop K) :
    TendstoUniformlyOn (fun x : ℝ ↦ fun t : ℝ ↦ (P x t)⁻¹) L atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  obtain ⟨x₁, hx₁⟩ := (h (1 / 2) (by norm_num)).exists
  have hP1 : ∀ t ∈ K, P x₁ t ≠ 0 := by
    intro t ht h0
    have h1 := hx₁ t ht
    rw [h0, zero_mul, dist_zero_right, norm_one] at h1
    norm_num at h1
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((hP x₁).inv₀ hP1)
  have hL : ∀ t ∈ K, ‖L t‖ ≤ 3 / 2 * max C 0 := by
    intro t ht
    have h1 := hx₁ t ht
    rw [dist_comm, dist_eq_norm] at h1
    have h2 : ‖P x₁ t * L t‖ < 3 / 2 := by
      have h3 := norm_sub_norm_le (P x₁ t * L t) 1
      rw [norm_one] at h3
      linarith
    have h3 : ‖L t‖ = ‖(P x₁ t)⁻¹‖ * ‖P x₁ t * L t‖ := by
      rw [← norm_mul, ← mul_assoc, inv_mul_cancel₀ (hP1 t ht), one_mul]
    rw [h3]
    have hM : ‖(P x₁ t)⁻¹‖ ≤ max C 0 := (hC t ht).trans (le_max_left _ _)
    nlinarith [norm_nonneg ((P x₁ t)⁻¹), norm_nonneg (P x₁ t * L t), le_max_right C 0]
  intro ε hε
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hδ : 0 < min (1 / 2) (ε / (3 * max C 0 + 1)) := by positivity
  filter_upwards [h _ hδ] with x hx t ht
  have h1 := hx t ht
  rw [dist_comm, dist_eq_norm] at h1
  have h2 : ‖P x t * L t - 1‖ < 1 / 2 := h1.trans_le (min_le_left _ _)
  have h3 : ‖P x t * L t - 1‖ < ε / (3 * max C 0 + 1) := h1.trans_le (min_le_right _ _)
  have h4 : 1 / 2 < ‖P x t‖ * ‖L t‖ := by
    have h5 := norm_sub_norm_le 1 (P x t * L t)
    rw [norm_one, norm_sub_rev, norm_mul] at h5
    linarith
  have hPx : P x t ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at h4
    norm_num at h4
  have hPpos : 0 < ‖P x t‖ := norm_pos_iff.mpr hPx
  have h6 : ‖(P x t)⁻¹‖ ≤ 3 * max C 0 := by
    rw [norm_inv, inv_le_iff_one_le_mul₀ hPpos]
    nlinarith [hL t ht, norm_nonneg (L t)]
  have h7 : L t - (P x t)⁻¹ = (P x t)⁻¹ * (P x t * L t - 1) := by
    field_simp
  rw [dist_eq_norm, h7, norm_mul]
  have h8 : 3 * max C 0 * (ε / (3 * max C 0 + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  calc ‖(P x t)⁻¹‖ * ‖P x t * L t - 1‖
      ≤ 3 * max C 0 * ‖P x t * L t - 1‖ := mul_le_mul_of_nonneg_right h6 (norm_nonneg _)
    _ ≤ 3 * max C 0 * (ε / (3 * max C 0 + 1)) :=
        mul_le_mul_of_nonneg_left h3.le (by positivity)
    _ < ε := h8

/-- The reciprocal partial product is continuous along the 1-line. -/
private theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_continuous
    (χ : U[F]) (x : ℝ) :
    Continuous (fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) := by
  have hmk : Continuous (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) := by
    have h : (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ 1 + (t : ℂ) * Complex.I := by
      funext t
      apply Complex.ext <;> simp
    rw [h]
    fun_prop
  have hfun : (fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) = fun t : ℝ ↦
      ∏ v ∈ heckePrimesBelow F x, (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
        (v.asIdeal.absNorm : ℂ) ^ (-(⟨1, t⟩ : ℂ))) :=
    funext fun t ↦ reciprocalHeckeEulerProductBelow_eq_prod χ x ⟨1, t⟩
  rw [hfun]
  refine continuous_finsetProd _ fun v _ ↦ ?_
  refine continuous_const.sub (continuous_const.mul ?_)
  refine hmk.neg.const_cpow (Or.inl ?_)
  have h1 := HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a character
nontrivial on the norm-one subgroup, the prime-norm-ordered Euler product
converges locally uniformly to the continued finite L-function on the 1-line. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  refine (heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_inv
    (fun x t ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) (fun t ↦ L ⟨1, t⟩) K hK
    (fun x ↦
      (heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_continuous
        χ x).continuousOn)
    (reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne χ hχ L hL
      hSeries K hK)).congr (Eventually.of_forall fun x t _ ↦ ?_)
  delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  beta_reduce
  rw [Finset.prod_inv_distrib, inv_inv]

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a pure
norm character, the prime-norm-ordered Euler product converges locally uniformly
to the continued finite L-function off the pole ordinate. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop ({t₀}ᶜ : Set ℝ) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_compl_singleton]
  intro K hKsub hK
  refine (heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_inv
    (fun x t ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) (fun t ↦ L ⟨1, t⟩) K hK
    (fun x ↦
      (heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_continuous
        χ x).continuousOn)
    (reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist χ t₀ hχ L hL
      hSeries K hK fun h ↦ hKsub h rfl)).congr (Eventually.of_forall fun x t _ ↦ ?_)
  delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  beta_reduce
  rw [Finset.prod_inv_distrib, inv_inv]

/-- The finite Euler factor of a norm twist of the trivial character at `s` is the
reciprocal of `1 - N(v)^(-(s + a))`. -/
private theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor (χ : U[F]) (a : ℂ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) a) (v : V[F]) (s : ℂ) :
    finiteHeckeEulerFactor χ v s = (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s + a)))⁻¹ := by
  classical
  have hval (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) a).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) :
      ℝ) : ℂ) ^ a = _
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : (ideleClassNormTwist (1 : U[F]) a).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) a).restrict v u = 1
    rw [hval u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  have hN : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [finiteHeckeEulerFactor, hχ, ite_eq_left hu, hu.localValue_eq u hπ, hval, hnorm,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
    ← Complex.cpow_neg, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hN, neg_add, add_comm (-a)]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. At the pole
ordinate the reciprocal product for a pure norm character equals the untwisted
Mertens product. -/
theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod (χ : U[F]) (t₀ x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩ =
      ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) := by
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h1 : -((⟨1, t₀⟩ : ℂ) + -Complex.I * t₀) = -1 := by
    apply Complex.ext <;> simp
  rw [reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor χ _ hχ, inv_inv, h1,
    Complex.cpow_neg_one]

/-- A bounded continuous test preserves summability of positive weights. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_test_summable
    {ι : Type*} (w z : ι → ℝ) (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    (hz : ∀ i, z i ∈ Icc 0 1) (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    Summable (fun i ↦ w i * g (z i)) := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  refine (hw.mul_right D).of_norm_bounded fun i ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw₀ i)]
  exact mul_le_mul_of_nonneg_left (hD _ (hz i)) (hw₀ i)

/-- Uniform error in a test is bounded by the total mass times the uniform error. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_test_error
    {f : ℝ → ℝ} {p : Polynomial ℝ} {δ : ℝ} (hf : ContinuousOn f (Icc 0 1))
  (hp' : ∀ x ∈ Icc 0 1, |p.eval x - f x| < δ) {ι : Type*} (w z : ι → ℝ) (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i)
    (hz : ∀ i, z i ∈ Icc 0 1) :
    |(∑' i, w i * f (z i)) - ∑' i, w i * p.eval (z i)| ≤ (∑' i, w i) * δ := by
  have h₁ := reciprocalHeckeEulerProductBelow_mertens_test_summable w z hw hw₀ hz _ hf
  have h₂ := reciprocalHeckeEulerProductBelow_mertens_test_summable w z hw hw₀ hz _ p.continuous.continuousOn
  rw [← h₁.tsum_sub h₂]
  calc |∑' i, (w i * f (z i) - w i * p.eval (z i))| ≤
      ∑' i, |w i * f (z i) - w i * p.eval (z i)| := by
        simpa only [Real.norm_eq_abs]
          using norm_tsum_le_tsum_norm (f := fun i ↦ w i * f (z i) - w i * p.eval (z i))
            (by simpa only [Real.norm_eq_abs] using (h₁.sub h₂).abs)
    _ ≤ ∑' i, w i * δ := by
      apply Summable.tsum_le_tsum _ (h₁.sub h₂).abs (hw.mul_right δ)
      intro i
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw₀ i), abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (hp' _ (hz i)).le (hw₀ i)
    _ = _ := tsum_mul_right

/-- Uniform polynomial approximation transfers convergence of nonnegative weighted rows
on monomials to every continuous test on the interval. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_continuous_tests {T ι κ : Type*} (l : Filter T)
    (a : T → ι → ℝ) (b : T → κ → ℝ) (x : T → ι → ℝ) (y : T → κ → ℝ)
    (ha : ∀ t i, 0 ≤ a t i) (hb : ∀ t j, 0 ≤ b t j)
    (hs : ∀ t, Summable (a t)) (hr : ∀ t, Summable (b t))
    (hx : ∀ t i, x t i ∈ Icc 0 1) (hy : ∀ t j, y t j ∈ Icc 0 1)
    {C : ℝ} (hC : ∀ᶠ t in l, (∑' i, a t i) + (∑' j, b t j) ≤ C)
    (hm : ∀ n : ℕ, Tendsto (fun t ↦ (∑' i, a t i * x t i ^ n) -
      (∑' j, b t j * y t j ^ n)) l (𝓝 0))
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun t ↦ (∑' i, a t i * f (x t i)) - (∑' j, b t j * f (y t j))) l (𝓝 0) := by
  classical
  have hp (p : Polynomial ℝ) : Tendsto (fun t ↦
      (∑' i, a t i * p.eval (x t i)) - (∑' j, b t j * p.eval (y t j))) l (𝓝 0) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      convert hp.add hq using 1
      · funext t
        simp only [Polynomial.eval_add, mul_add]
        have hA := reciprocalHeckeEulerProductBelow_mertens_test_summable
          (a t) (x t) (hs t) (ha t) (hx t)
        have hB := reciprocalHeckeEulerProductBelow_mertens_test_summable
          (b t) (y t) (hr t) (hb t) (hy t)
        rw [(hA _ p.continuous.continuousOn).tsum_add (hA _ q.continuous.continuousOn),
          (hB _ p.continuous.continuousOn).tsum_add (hB _ q.continuous.continuousOn)]
        ring
      · simp
    | monomial n c =>
      convert (hm n).const_mul c using 1
      · funext t
        simp only [Polynomial.eval_monomial, mul_sub, ← tsum_mul_left]
        congr 1 <;> apply tsum_congr <;> intro i <;> ring
      · simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (2 * (max 0 C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp'⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδ
  have hε₂ : 0 < ε / 2 := half_pos hε
  filter_upwards [hC, (Metric.tendsto_nhds.mp (hp p)) (ε / 2) hε₂] with t ht h
  rw [Real.dist_eq, sub_zero] at h ⊢
  have h₁ := reciprocalHeckeEulerProductBelow_mertens_test_error hf hp' _ _ (hs t) (ha t) (hx t)
  have h₂ := reciprocalHeckeEulerProductBelow_mertens_test_error hf hp' _ _ (hr t) (hb t) (hy t)
  have hbound : C * δ < ε / 2 := by
    have hz : 0 < max 0 C + 1 := by positivity
    dsimp [δ]
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right 0 C) hε.le]
  rw [abs_le] at h₁ h₂
  rw [abs_lt] at h ⊢
  have reciprocalHeckeEulerProductBelow_mertens_power_summable := (mul_le_mul_of_nonneg_right ht hδ.le).trans_lt hbound
  rw [add_mul] at reciprocalHeckeEulerProductBelow_mertens_power_summable
  constructor <;> linarith
/-- Every positive integral power of a Laplace weight is dominated by its first power. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_power_summable
    {I : Type*} (w q : I → ℝ) (h : Summable (fun i ↦ w i * q i))
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Ioo 0 1) (n : ℕ) :
    Summable (fun i ↦ w i * q i ^ (n + 1)) := by
  apply Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (hw _) (pow_nonneg (hq i).1.le _)) _ h
  intro i
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hq i).1.le (pow_le_one₀ (hq i).1.le (hq i).2.le)) (hw i)

/-- A monomial moment of the weighted row is the difference of two successive Laplace sums. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_moment_eq
    {I : Type*} (w q : I → ℝ) (h : Summable (fun i ↦ w i * q i))
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Ioo 0 1) (n : ℕ) :
    (∑' i, (w i * q i * (1 - q i)) * q i ^ n) =
      (∑' i, w i * q i ^ (n + 1)) - (∑' i, w i * q i ^ (n + 2)) := by
  rw [← (reciprocalHeckeEulerProductBelow_mertens_power_summable w q h hw hq n).tsum_sub
      (reciprocalHeckeEulerProductBelow_mertens_power_summable w q h hw hq (n + 1))]
  apply tsum_congr
  intro i
  ring

/-- The damping factor q(1−q) gives each weighted row finite mass. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_damped_summable
    {I : Type*} (w q : I → ℝ) (h : Summable (fun i ↦ w i * q i))
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Ioo 0 1) :
    Summable (fun i ↦ w i * q i * (1 - q i)) :=
  Summable.of_nonneg_of_le (fun i ↦ by have := hw i; have := (hq i).1; have := (hq i).2; positivity)
    (fun i ↦ mul_le_of_le_one_right (mul_nonneg (hw i) (hq i).1.le) (by linarith [(hq i).1])) h

/-- A ramp test places its weighted sum between two neighboring sharp cutoffs. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_ramp_bounds
    {I : Type*} (w q : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Ioo 0 1)
    (h : Summable (fun i ↦ w i * q i)) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (f : ℝ → ℝ) (hf : Continuous f) (htest : ∀ z ∈ Ioo (0 : ℝ) 1,
      (if r' < z then 1 else 0) - z ≤ z * (1 - z) * f z ∧
      z * (1 - z) * f z ≤ (if r < z then 1 else 0) - z) :
    (∑' i, if r' < q i then w i else 0) - (∑' i, w i * q i) ≤
      (∑' i, (w i * q i * (1 - q i)) * f (q i)) ∧
    (∑' i, (w i * q i * (1 - q i)) * f (q i)) ≤
      (∑' i, if r < q i then w i else 0) - (∑' i, w i * q i) := by
  have hcut (u : ℝ) (hu : 0 < u) : Summable (fun i ↦ if u < q i then w i else 0) := by
    apply Summable.of_nonneg_of_le (fun i ↦ by split_ifs <;> simp [hw i]) _ (h.mul_right u⁻¹)
    intro i
    split_ifs with e
    · simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left ((one_le_div hu).mpr e.le) (hw i)
    · exact mul_nonneg (mul_nonneg (hw i) (hq i).1.le) (inv_nonneg.mpr hu.le)
  have hrow := reciprocalHeckeEulerProductBelow_mertens_test_summable (fun i ↦ w i * q i * (1 - q i)) q
      (reciprocalHeckeEulerProductBelow_mertens_damped_summable w q h hw hq)
    (fun i ↦ mul_nonneg (mul_nonneg (hw i) (hq i).1.le) (sub_nonneg.mpr (hq i).2.le))
    (fun i ↦ Ioo_subset_Icc_self (hq i)) f hf.continuousOn
  rw [← (hcut r' hr').tsum_sub h, ← (hcut r hr).tsum_sub h]
  constructor
  · apply Summable.tsum_le_tsum _ ((hcut r' hr').sub h) hrow
    intro i
    have hh := mul_le_mul_of_nonneg_left (htest _ (hq i)).1 (hw i)
    split_ifs at hh ⊢ <;> nlinarith only [hh]
  · apply Summable.tsum_le_tsum _ hrow ((hcut r hr).sub h)
    intro i
    have hh := mul_le_mul_of_nonneg_left (htest _ (hq i)).2 (hw i)
    split_ifs at hh ⊢ <;> nlinarith only [hh]

/-- Continuous majorants and minorants of the sharp cutoff after subtracting its Laplace weight. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_ramp {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ q ∈ Ioo (0 : ℝ) 1,
      (if b < q then 1 else 0) - q ≤ q * (1 - q) * f q ∧
      q * (1 - q) * f q ≤ (if a < q then 1 else 0) - q := by
  let z (q : ℝ) := min 1 (max 0 ((q - a) / (b - a)))
  let A (q : ℝ) := -(max (1 - q) (1 - b))⁻¹
  let B (q : ℝ) := (max q a)⁻¹
  let f (q : ℝ) := (1 - z q) * A q + z q * B q
  refine ⟨f, ?_, ?_⟩
  · have hA : Continuous A :=
      (((continuous_const.sub continuous_id).max continuous_const).inv₀
        (fun q ↦ ne_of_gt ((sub_pos.mpr hb).trans_le (le_max_right _ _)))).neg
    have hB : Continuous B :=
      ((continuous_id.max continuous_const).inv₀ (fun q ↦ ne_of_gt (ha.trans_le (le_max_right _ _))))
    have hz : Continuous z := by dsimp [z]; fun_prop
    exact ((continuous_const.sub hz).mul hA).add (hz.mul hB)
  intro q hq
  have hq₁ := sub_pos.mpr hq.2
  by_cases hqa : q ≤ a
  · have hza : z q = 0 := by simp [z, max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hqa) (sub_pos.mpr hab).le)]
    have haq : 1 - b ≤ 1 - q := by linarith
    simp [f, hza, A, max_eq_left haq, not_lt.mpr hqa, not_lt.mpr (hqa.trans hab.le), hq₁.ne']
  · have hqa' := lt_of_not_ge hqa
    by_cases hqb : b ≤ q
    · have hzb : z q = 1 := by
        have h : 1 ≤ (q - a) / (b - a) := (one_le_div (sub_pos.mpr hab)).mpr (by linarith)
        exact min_eq_left (h.trans (le_max_right _ _))
      have hval : q * (1 - q) * f q = 1 - q := by
        simp [f, hzb, B, max_eq_left hqa'.le, hq.1.ne', mul_comm]
      rw [hval, ite_eq_left hqa']
      split_ifs <;> constructor <;> linarith
    · have hqb' := lt_of_not_ge hqb
      have ha' : 1 - b ≤ 1 - q := by linarith
      have hz₀ : 0 ≤ z q := le_min zero_le_one (le_max_left _ _)
      have hz₁ : z q ≤ 1 := min_le_left _ _
      have hval : q * (1 - q) * f q = z q - q := by
        dsimp only [f, A, B]
        rw [max_eq_left ha', max_eq_left hqa'.le]
        field_simp [hq₁.ne', hq.1.ne']
        ring
      rw [hval, ite_eq_right (not_lt.mpr hqb'.le), ite_eq_left hqa']
      constructor <;> linarith

/-- Subtraction of the Laplace weight makes a sharply truncated sum testable by continuous
functions up to an arbitrarily small change in its cutoff. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_transfer {T ι κ : Type*} (l : Filter T)
    (a : ι → ℝ) (b : κ → ℝ) (x : T → ι → ℝ) (y : T → κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hx : ∀ t i, x t i ∈ Ioo 0 1) (hy : ∀ t j, y t j ∈ Ioo 0 1)
    (hs : ∀ t, Summable (fun i ↦ a i * x t i))
    (hr : ∀ t, Summable (fun j ↦ b j * y t j))
    {D E C : ℝ}
    (hm : ∀ n : ℕ, Tendsto (fun t ↦ (∑' i, a i * x t i ^ (n + 1)) -
      (∑' j, b j * y t j ^ (n + 1))) l (𝓝 D))
    (hbounded : ∀ᶠ t in l, (∑' j, b j * y t j) - (∑' j, b j * y t j ^ 2) ≤ E)
    (hc : ∀ u : ℝ, 0 < u → Tendsto (fun t ↦
      (∑' j, if Real.exp (-u) < y t j then b j else 0) - (∑' j, b j * y t j))
      l (𝓝 (C + Real.log u))) :
    Tendsto (fun t ↦ (∑' i, if Real.exp (-1) < x t i then a i else 0) -
      (∑' i, a i * x t i)) l (𝓝 C) := by
  classical
  let A t i := a i * x t i * (1 - x t i)
  let B t j := b j * y t j * (1 - y t j)

  have hA (t i) : 0 ≤ A t i := mul_nonneg (mul_nonneg (ha i) (hx t i).1.le) (sub_nonneg.mpr (hx t i).2.le)
  have hB (t j) : 0 ≤ B t j := mul_nonneg (mul_nonneg (hb j) (hy t j).1.le) (sub_nonneg.mpr (hy t j).2.le)
  have hnm (n : ℕ) : Tendsto (fun t ↦ (∑' i, A t i * x t i ^ n) -
      (∑' j, B t j * y t j ^ n)) l (𝓝 0) := by
    convert (hm n).sub (hm (n + 1)) using 1
    · funext t
      rw [show (∑' i, A t i * x t i ^ n) = _ from
          reciprocalHeckeEulerProductBelow_mertens_moment_eq a (x t) (hs t) ha (hx t) n,
        show (∑' j, B t j * y t j ^ n) = _ from
          reciprocalHeckeEulerProductBelow_mertens_moment_eq b (y t) (hr t) hb (hy t) n]
      ring
    · simp
  have hf (f : ℝ → ℝ) (hf : Continuous f) : Tendsto
      (fun t ↦ (∑' i, A t i * f (x t i)) - (∑' j, B t j * f (y t j))) l (𝓝 0) := by
    apply reciprocalHeckeEulerProductBelow_mertens_continuous_tests l A B x y hA hB
      (fun t ↦ reciprocalHeckeEulerProductBelow_mertens_damped_summable a _ (hs t) ha (hx t))
      (fun t ↦ reciprocalHeckeEulerProductBelow_mertens_damped_summable b _ (hr t) hb (hy t))
      (fun t i ↦ Ioo_subset_Icc_self (hx t i))
      (fun t j ↦ Ioo_subset_Icc_self (hy t j)) (C := 2 * E + 1) _ hnm hf.continuousOn
    have h₀ : Tendsto (fun t ↦ (∑' i, A t i) - ∑' j, B t j) l (𝓝 0) := by simpa using hnm 0
    filter_upwards [hbounded, h₀.eventually_lt_const zero_lt_one] with t ht ht'
    have he : (∑' j, B t j) = (∑' j, b j * y t j) - ∑' j, b j * y t j ^ 2 := by
      simpa using reciprocalHeckeEulerProductBelow_mertens_moment_eq b (y t) (hr t) hb (hy t) 0
    linarith
  -- A weighted cutoff test is squeezed between the two neighboring sharp cutoffs.

  rw [Metric.tendsto_nhds]
  intro ε hε
  let u := Real.exp (-(ε / 2))
  let v := Real.exp (ε / 2)
  have hExp (t : ℝ) := Real.exp_pos (-t)
  have h₁ : u < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h₂ : 1 < v := Real.one_lt_exp_iff.mpr (by linarith)
  obtain ⟨f, hfc, hfb⟩ := reciprocalHeckeEulerProductBelow_mertens_ramp (hExp 1) (Real.exp_lt_exp.mpr (neg_lt_neg h₁))
    (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (Real.exp_pos _)))
  obtain ⟨g, hgc, hgb⟩ := reciprocalHeckeEulerProductBelow_mertens_ramp (hExp v) (Real.exp_lt_exp.mpr (neg_lt_neg h₂))
    (Real.exp_lt_one_iff.mpr (by norm_num))
  have hlo := (hc u (Real.exp_pos _)).add (hf f hfc)
  have hhi := (hc v (Real.exp_pos _)).add (hf g hgc)
  have hlow : C - ε < C + Real.log u + 0 := by
    simp [u]
    linarith
  have hhigh : C + Real.log v + 0 < C + ε := by
    simp [v]
    linarith
  filter_upwards [hlo.eventually_const_lt hlow, hhi.eventually_lt_const hhigh] with t ht₁ ht₂
  have A₁ := (reciprocalHeckeEulerProductBelow_mertens_ramp_bounds a _ ha (hx t) (hs t) (hExp 1) (hExp u) f hfc hfb).2
  have A₂ := (reciprocalHeckeEulerProductBelow_mertens_ramp_bounds a _ ha (hx t) (hs t) (hExp v) (hExp 1) g hgc hgb).1
  have B₁ := (reciprocalHeckeEulerProductBelow_mertens_ramp_bounds b _ hb (hy t) (hr t) (hExp 1) (hExp u) f hfc hfb).1
  have B₂ := (reciprocalHeckeEulerProductBelow_mertens_ramp_bounds b _ hb (hy t) (hr t) (hExp v) (hExp 1) g hgc hgb).2
  rw [Real.dist_eq, abs_lt]
  simp only [A, B] at ht₁ ht₂
  constructor <;> linarith

/-- The Laplace transform of the harmonic model is −log(1−exp(−s)). -/
private theorem reciprocalHeckeEulerProductBelow_mertens_model_laplace {s : ℝ} (hs : 0 < s) :
    HasSum (fun j : ℕ ↦ (j + 1 : ℝ)⁻¹ * Real.exp (-s * (j + 1))) (-Real.log (1 - Real.exp (-s))) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one
    (by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs))
  apply h.congr_fun
  intro j
  rw [mul_comm (-s), add_comm (j:ℝ) 1, add_comm (1 : ℝ) j, show (j : ℝ) + 1 = (j + 1 : ℕ) from by norm_cast, Real.exp_nat_mul]
  ring

/-- The harmonic transform has the same leading singularity as −log s. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_scale_laplace :
    Tendsto (fun s : ℝ ↦ (1 - Real.exp (-s)) / s) (𝓝[>] 0) (𝓝 1) := by
  have h : HasDerivAt (fun s : ℝ ↦ 1 - Real.exp (-s)) 1 0 := by
    simpa using ((hasDerivAt_neg (0 : ℝ)).exp.const_sub 1)
  refine (h.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)).congr fun x ↦ ?_
  simp [slope_def_field]

/-- The class number formula fixes the limiting difference of the two Laplace transforms. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_log_compare (F : Type*) [Field F] [NumberField F] :
    Tendsto (fun s : ℝ ↦ Real.log ‖dedekindZeta F ((1 + s : ℝ) : ℂ)‖ +
      Real.log (1 - Real.exp (-s))) (𝓝[>] 0) (𝓝 (Real.log (dedekindZeta_residue F))) := by
  have hshift : Tendsto (fun s : ℝ ↦ 1 + s) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
        (show Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with s hs using show 1 < 1 + s by simpa using hs
  have hz : Tendsto (fun s : ℝ ↦ s * ‖dedekindZeta F ((1 + s : ℝ) : ℂ)‖)
      (𝓝[>] 0) (𝓝 (dedekindZeta_residue F)) := by
    rw [← Real.norm_of_nonneg (dedekindZeta_residue_pos F).le, ← Complex.norm_real]
    apply ((tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm.comp hshift).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp [abs_of_pos (show 0 < s from hs), Complex.norm_real]
  have hpos := dedekindZeta_residue_pos F
  have hm := (hz.mul reciprocalHeckeEulerProductBelow_mertens_scale_laplace)
  rw [mul_one] at hm
  apply ((Real.continuousAt_log hpos.ne').tendsto.comp hm).congr'
  filter_upwards [self_mem_nhdsWithin, hz.eventually_const_lt hpos] with s hs hn
  have hs' : 0 < s := hs
  have he : 0 < 1 - Real.exp (-s) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs'))
  have hn' : 0 < ‖dedekindZeta F ((1 + s : ℝ) : ℂ)‖ := pos_of_mul_pos_right hn hs'.le
  dsimp only [Function.comp_apply]
  rw [← Real.log_mul hn'.ne' he.ne']
  congr 1
  field_simp

/-- A strict cutoff in the harmonic model gives harmonic(⌈ut⌉−1), including at integer endpoints. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_model_cut (u : ℝ) (hu : 0 < u) :
    Tendsto (fun t : ℝ ↦ (∑' j : ℕ, if Real.exp (-u) < Real.exp (-(max 1 t)⁻¹ * (j + 1))
      then (j + 1 : ℝ)⁻¹ else 0) - Real.log (max 1 t)) atTop (𝓝 (Real.eulerMascheroniConstant + Real.log u)) := by
  classical
  let N (t : ℝ) := ⌈u * t⌉₊ - 1
  have hN : Tendsto N atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp (tendsto_nat_ceil_atTop.comp (tendsto_id.const_mul_atTop hu))
  have hratio : Tendsto (fun t : ℝ ↦ (N t : ℝ) / t) atTop (𝓝 u) := by
    have hc := (tendsto_nat_ceil_div_atTop (R := ℝ)).comp (tendsto_id.const_mul_atTop hu)
    have he := (hc.const_mul u).sub (tendsto_inv_atTop_zero (𝕜 := ℝ))
    rw [mul_one, sub_zero] at he
    refine he.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [N, Function.comp_apply, id_eq]
    rw [Nat.cast_sub (show 1 ≤ ⌈u * t⌉₊ from Nat.ceil_pos.mpr (mul_pos hu ht)), Nat.cast_one]
    field_simp
  have hh := (Real.tendsto_harmonic_sub_log.comp hN).add ((Real.continuousAt_log hu.ne').tendsto.comp hratio)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hN.eventually (eventually_ge_atTop 1)] with t ht hn
  have ht' : 0 < t := zero_lt_one.trans ht
  have hn' : (0 : ℝ) < N t := by exact_mod_cast (show 0 < N t from hn)
  have he (j : ℕ) : Real.exp (-u) < Real.exp (-t⁻¹ * (j + 1)) ↔ j < N t := by
    rw [Real.exp_lt_exp, neg_mul, neg_lt_neg_iff, inv_mul_eq_div, div_lt_iff₀ ht']
    change (j:ℝ) + 1 < u * t ↔ j < ⌈u * t⌉₊-1
    rw [show (j:ℝ) + 1 = (j + 1 : ℕ) from by norm_cast, ← Nat.lt_ceil]
    omega
  dsimp only [Function.comp_apply]
  rw [max_eq_right ht.le,
    show (∑' j : ℕ, if Real.exp (-u) < Real.exp (-t⁻¹ * (j + 1))
      then (j + 1 : ℝ)⁻¹ else 0) = (harmonic (N t) : ℝ) from ?_,
    Real.log_div hn'.ne' ht'.ne']
  · ring
  · simp_rw [he]
    rw [tsum_eq_sum (s := Finset.range (N t)) fun j hj ↦ ite_eq_right (fun e ↦ hj (Finset.mem_range.mpr e))]
    simp [harmonic, Finset.sum_congr rfl (fun i hi ↦ ite_eq_left (Finset.mem_range.mp hi))]

/-- For the trivial character the Euler logarithm has positive Laplace weights indexed by prime powers. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_exp_term (a : V[F] × ℕ) (s : ℝ) :
    let height := Real.log (((a.1.asIdeal ^ (a.2 + 1)).absNorm : ℕ) : ℝ)
    heckePrimePowerLogTerm (1 : U[F]) a.1 a.2 ((1 + s : ℝ) : ℂ) =
      ((Real.exp (-height) / (a.2 + 1 : ℝ) * Real.exp (-s * height) : ℝ) : ℂ) := by
  dsimp only
  classical
  have hnon (g) : ideleClassNormTwist (1 : U[F]) 0 g = 1 := by
    change 1 * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres (v : V[F]) (z : v.adicCompletion F) (hz : z ≠ 0) :
      (ideleClassNormTwist (1 : U[F]) 0).restrict v z = 1 := by
    have hu := isUnit_iff_ne_zero.mpr hz
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hnon, hz]
  have hu := HeckeCharacter.isUnramifiedAt_iff.mpr
    (fun x ↦ hres a.1 _ (by simp))
  have hloc : (ideleClassNormTwist (1 : U[F]) 0).localValue a.1 = 1 := by
    rw [HeckeCharacter.localValue]
    exact hres _ _ (by simpa using (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero))
  have hn : 0 < (((a.1.asIdeal ^ (a.2 + 1)).absNorm : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ a.1.ne_bot))
  rw [heckePrimePowerLogTerm, heckeIdealValue_prime_pow _ _ (Nat.succ_pos _), ite_eq_left hu, hloc, one_pow]
  rw [← Complex.ofReal_natCast ((a.1.asIdeal ^ (a.2 + 1)).absNorm), ← Complex.ofReal_cpow hn.le]
  push_cast
  rw [Real.rpow_def_of_pos hn]
  norm_cast
  rw [div_mul_eq_mul_div, ← Real.exp_add, one_div, mul_inv_rev]
  rw [← Real.exp_neg]
  congr 1
  ring_nf
/-- The Laplace transform of the prime-power weights is the logarithm of the zeta value on the positive real axis. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_laplace (s : ℝ) (hs : 0 < s) :
    let height (p : V[F] × ℕ) := Real.log (((p.1.asIdeal ^ (p.2 + 1)).absNorm : ℕ) : ℝ)
    let weight (p : V[F] × ℕ) := Real.exp (-height p) / (p.2 + 1 : ℝ)
    HasSum (fun a : V[F] × ℕ ↦ weight a * Real.exp (-s * height a))
      (Real.log ‖dedekindZeta F ((1 + s : ℝ) : ℂ)‖) := by
  intro height weight
  let z : Complex.re ⁻¹' Ioi (1 : ℝ) := ⟨((1 + s : ℝ) : ℂ), by simpa using hs⟩
  obtain ⟨w, hw, he⟩ := reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_primes (1 : U[F]) 0 z
  have hn : heckePrimesBelow F 0 = ∅ := by
    ext v
    simp [heckePrimesBelow, v.ne_bot]
  have hp : reciprocalHeckeEulerProductBelow (1 : U[F]) 0 z = 1 := by
    simp [reciprocalHeckeEulerProductBelow, reciprocalPartialHeckeEulerProduct, hn]
  have hz : finiteHeckeL (1 : U[F]) z = dedekindZeta F z := by
    have h := completedHeckeL_one_eq_dedekindZeta (F := F) z
    rw [← heckeGammaFactor_one] at h
    change heckeGammaFactor (1 : U[F]) z * finiteHeckeL (1 : U[F]) z = _ at h
    exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) (zero_lt_one.trans z.property)) h
  rw [hp, one_mul, hz] at he
  rw [show ((1 + s : ℝ) : ℂ) = z from rfl, he, Complex.norm_exp, Real.log_exp]
  apply (Complex.hasSum_re hw).congr_fun
  intro a
  rw [ite_eq_left (Nat.cast_nonneg _), show (z : ℂ) = ((1 + s : ℝ) : ℂ) from rfl,
    reciprocalHeckeEulerProductBelow_mertens_exp_term a s]
  rfl

/-- Compare the zeta transform with the harmonic model to obtain the constant for the sharp prime-power cutoff. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_cutoff_height :
    let height (p : V[F] × ℕ) := Real.log (((p.1.asIdeal ^ (p.2 + 1)).absNorm : ℕ) : ℝ)
    let weight (p : V[F] × ℕ) := Real.exp (-height p) / (p.2 + 1 : ℝ)
    Tendsto (fun t : ℝ ↦ (∑' a : V[F] × ℕ, if height a < max 1 t then weight a else 0) -
      Real.log (max 1 t)) atTop (𝓝 (Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue F))) := by
  intro height weight
  let X (t : ℝ) := max 1 t
  let s (t : ℝ) := (X t)⁻¹
  let Z (v : ℝ) := Real.log ‖dedekindZeta F ((1 + v : ℝ) : ℂ)‖
  let G (v : ℝ) := -Real.log (1 - Real.exp (-v))
  let x (t : ℝ) (a : V[F] × ℕ) := Real.exp (-s t * height a)
  let y (t : ℝ) (j : ℕ) := Real.exp (-s t * (j + 1))
  let a (p : V[F] × ℕ) := weight p
  let b (j : ℕ) := (j + 1 : ℝ)⁻¹
  have hX (t) : 0 < X t := zero_lt_one.trans_le (le_max_left _ _)
  have hs (t) : 0 < s t := inv_pos.mpr (hX t)
  have hXtop : Tendsto X atTop atTop := tendsto_atTop_mono (fun t ↦ le_max_right 1 t) tendsto_id
  have hs0 : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_inv_atTop_zero.comp hXtop, Eventually.of_forall hs⟩
  have hp (v : V[F] × ℕ) : 0 < height v := by
    apply Real.log_pos
    rw [map_pow]
    exact_mod_cast Nat.one_lt_pow (by omega : v.2 + 1 ≠ 0) (HeightOneSpectrum.one_lt_absNorm v.1)
  have hg0 : Tendsto (fun v : ℝ ↦ G v + Real.log v) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp reciprocalHeckeEulerProductBelow_mertens_scale_laplace).neg
    rw [Real.log_one, neg_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have hv' : 0 < v := hv
    dsimp [G]
    rw [Real.log_div (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hv'))).ne' hv'.ne']
    ring
  have hGX : Tendsto (fun t ↦ G (s t) - Real.log (X t)) atTop (𝓝 0) := by
    simpa [Function.comp_def, s, Real.log_inv, sub_eq_add_neg] using hg0.comp hs0
  have hAs (t) (n : ℕ) : HasSum (fun i ↦ a i * x t i ^ (n + 1)) (Z ((n + 1) * s t)) := by
    have hn : 0 < ((n:ℝ) + 1) * s t := mul_pos (by positivity) (hs t)
    apply (reciprocalHeckeEulerProductBelow_mertens_laplace (F := F) _ hn).congr_fun
    intro i
    dsimp [a, x]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hBs (t) (n : ℕ) : HasSum (fun j ↦ b j * y t j ^ (n + 1)) (G ((n + 1) * s t)) := by
    have hn : 0 < ((n:ℝ) + 1) * s t := mul_pos (by positivity) (hs t)
    apply (reciprocalHeckeEulerProductBelow_mertens_model_laplace hn).congr_fun
    intro j
    dsimp [b, y]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 2
    ring
  have hm (n : ℕ) : Tendsto (fun t ↦ (∑' i, a i * x t i ^ (n + 1)) -
      (∑' j, b j * y t j ^ (n + 1))) atTop (𝓝 (Real.log (dedekindZeta_residue F))) := by
    simp_rw [(hAs _ _).tsum_eq, (hBs _ _).tsum_eq]
    have hh : Tendsto (fun t ↦ ((n:ℝ) + 1) * s t) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun t ↦ mul_pos (by positivity) (hs t)⟩
      simpa using ((tendsto_nhds_of_tendsto_nhdsWithin hs0).const_mul ((n:ℝ) + 1))
    simpa [Function.comp_def, Z, G, sub_neg_eq_add] using (reciprocalHeckeEulerProductBelow_mertens_log_compare F).comp hh
  have hbdd : ∀ᶠ t in atTop, (∑' j, b j * y t j) - (∑' j, b j * y t j ^ 2) ≤ Real.log 2 := by
    apply Eventually.of_forall
    intro t
    have h₁ := (hBs t 0).tsum_eq
    have h₂ := (hBs t 1).tsum_eq
    simp [G] at h₁ h₂
    rw [h₁, h₂, neg_sub_neg, ← Real.log_div]
    · apply Real.log_le_log (div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hs t])))
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hs t]))))
      rw [div_le_iff₀ (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hs t])))]
      rw [show -((1 + 1) * s t) = -s t + -s t by ring, Real.exp_add]
      nlinarith [sq_nonneg (1 - Real.exp (-s t))]
    · exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hs t]))).ne'
    · exact (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [hs t]))).ne'
  have hmodel (u) (hu : 0 < u) : Tendsto (fun t ↦
      (∑' j, if Real.exp (-u) < y t j then b j else 0) - (∑' j, b j * y t j))
      atTop (𝓝 (Real.eulerMascheroniConstant + Real.log u)) := by
    have he (t : ℝ) : (∑' j, b j * y t j) = G (s t) := by simpa using (hBs t 0).tsum_eq
    simp_rw [he]
    have h := (reciprocalHeckeEulerProductBelow_mertens_model_cut u hu).sub hGX
    rw [sub_zero] at h
    refine h.congr fun t ↦ ?_
    dsimp [b, y, s, X]
    ring
  have ht := reciprocalHeckeEulerProductBelow_mertens_transfer atTop a b x y
    (fun i ↦ by dsimp [a]; positivity) (fun j ↦ by dsimp [b]; positivity)
    (fun t i ↦ ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (hs t)) (hp i))⟩)
    (fun t j ↦ ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr (hs t)) (by positivity))⟩)
    (fun t ↦ by simpa using (hAs t 0).summable) (fun t ↦ by simpa using (hBs t 0).summable)
    hm hbdd hmodel
  have he (t : ℝ) : (∑' i, a i * x t i) = Z (s t) := by simpa using (hAs t 0).tsum_eq
  simp_rw [he] at ht
  have hz := ((reciprocalHeckeEulerProductBelow_mertens_log_compare F).comp hs0).add hGX
  rw [add_zero] at hz
  refine (ht.add hz).congr fun t ↦ ?_
  have heq (i : V[F] × ℕ) : Real.exp (-1) < x t i ↔ height i < X t := by
    have he : x t i = Real.exp (-(height i / X t)) := by
      dsimp [x, s]
      congr 1
      ring
    rw [he, Real.exp_lt_exp, neg_lt_neg_iff,
      div_lt_iff₀ (hX t), one_mul]
  simp only [Function.comp_apply, heq, Z, G, X, a]
  ring

/-- Removing the cutoff on the powers of each retained prime adds exactly minus the
logarithmic correction from (B.7.2.18). -/
private theorem reciprocalHeckeEulerProductBelow_mertens_product_log (x : ℝ) (hx : 0 < x) :
    let height (p : V[F] × ℕ) := Real.log (((p.1.asIdeal ^ (p.2 + 1)).absNorm : ℕ) : ℝ)
    let weight (p : V[F] × ℕ) := Real.exp (-height p) / (p.2 + 1 : ℝ)
    (∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℝ)⁻¹)) =
      Real.exp (- (∑' a : V[F] × ℕ, if height a < Real.log x then weight a else 0) +
        (heckeEulerProductLogCorrection (1 : U[F]) x 1).re) := by
  intro height weight
  classical
  let P := heckePrimesBelow F x
  let f (p : V[F] × ℕ) := if p.1 ∈ P then weight p else 0
  let d (v : V[F]) := -Real.log (1 - (v.asIdeal.absNorm : ℝ)⁻¹)
  have hn (v : V[F]) : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hpos (v : V[F]) : 0 < 1 - (v.asIdeal.absNorm : ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (hn v))
  have hLocalSum (v : V[F]) : HasSum (fun j : ℕ ↦ f (v, j)) (if v ∈ P then d v else 0) := by
    by_cases hv : v ∈ P
    · simp only [f, hv, ↓reduceIte]
      have hlog := Real.hasSum_pow_div_log_of_abs_lt_one
        (show |(v.asIdeal.absNorm : ℝ)⁻¹| < 1 by
          rw [abs_of_nonneg (by positivity)]; exact inv_lt_one_of_one_lt₀ (hn v))
      apply hlog.congr_fun
      intro j
      have hp : 0 < (((v.asIdeal ^ (j + 1)).absNorm : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ v.ne_bot))
      dsimp only [weight, height]
      rw [Real.exp_neg, Real.exp_log hp, map_pow, Nat.cast_pow, inv_pow]
    · simp [f, hv]
  have hfin : HasSum (fun v : V[F] ↦ if v ∈ P then d v else 0) (∑ v ∈ P, d v) := by
    simpa using hasSum_sum_of_ne_finset_zero (f := fun v : V[F] ↦ if v ∈ P then d v else 0)
      (s := P) (fun v hv ↦ ite_eq_right hv)
  have hfs : Summable f := by
    apply (summable_prod_of_nonneg ?_).mpr
    · refine ⟨fun v ↦ (hLocalSum v).summable, ?_⟩
      simpa only [(hLocalSum _).tsum_eq] using hfin.summable
    · intro i
      dsimp only [f]
      split_ifs <;> positivity
  have he : (∑' i, f i) = ∑ v ∈ P, d v := (hfs.hasSum.prod_fiberwise hLocalSum).unique hfin
  have hc := Complex.hasSum_re (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_hasSum
    (1 : U[F]) x (1 : ℂ) (by norm_num))
  let g (i : V[F] × ℕ) :=
    if (i.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℝ)
      then weight i else 0
  have hg : HasSum g (-(heckeEulerProductLogCorrection (1 : U[F]) x 1).re) := by
    apply hc.congr_fun
    intro i
    have hm : heckePrimePowerLogTerm (1 : U[F]) i.1 i.2 1 = ((weight i : ℝ) : ℂ) := by
      simpa [weight, height] using reciprocalHeckeEulerProductBelow_mertens_exp_term i 0
    dsimp only [g]
    simp only [← map_pow, hm]
    split_ifs <;> rfl
  have hsharp : HasSum (fun i : V[F] × ℕ ↦ if height i < Real.log x then weight i else 0)
      ((∑ v ∈ P, d v) + (heckeEulerProductLogCorrection (1 : U[F]) x 1).re) := by
    rw [←he, ←sub_neg_eq_add]
    apply (hfs.hasSum.sub hg).congr_fun
    intro i
    have hpower : 0 < (((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ i.1.ne_bot))
    have hle : (i.1.asIdeal.absNorm : ℝ) ≤ ((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℝ) := by
      rw [map_pow]
      exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero _) _
    simp only [f, g, P, height, heckePrimesBelow_mem_iff, Real.log_lt_log_iff hpower hx]
    by_cases h : ((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℝ) < x
    · have hn : ¬ ((i.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℝ)) := fun e ↦ (not_le.mpr h) e.2
      simp only [ite_eq_left h, ite_eq_left (hle.trans_lt h), ite_eq_right hn, sub_zero]
    · by_cases e : (i.1.asIdeal.absNorm : ℝ) < x
      · simp only [ite_eq_right h, ite_eq_left e, ite_eq_left (And.intro e (le_of_not_gt h)), sub_self]
      · have hn : ¬ ((i.1.asIdeal.absNorm : ℝ) < x ∧ x ≤ ((i.1.asIdeal ^ (i.2 + 1)).absNorm : ℝ)) := fun h ↦ e h.1
        simp only [ite_eq_right h, ite_eq_right e, ite_eq_right hn, sub_zero]
  rw [hsharp.tsum_eq,
    show -((∑ v ∈ P, d v) + (heckeEulerProductLogCorrection (1 : U[F]) x 1).re) + _ = -(∑ v ∈ P, d v) by ring,
    ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  simp [d, Real.exp_log (hpos v)]

/-- The stated norm-one class volume equals the Dedekind residue in the class number formula. -/
private theorem reciprocalHeckeEulerProductBelow_mertens_volume (F : Type*) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F univ).toReal = dedekindZeta_residue F := by
  rw [normOneIdeleClassTamagawaMeasure_volume]
  suffices hform : (2 : ℝ) ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
      (NumberField.classNumber F : ℝ) * Units.regulator F /
      (Real.sqrt ((NumberField.discr F).natAbs : ℝ) * (Units.torsionOrder F : ℝ)) = dedekindZeta_residue F by
    rw [hform, ENNReal.toReal_ofReal (dedekindZeta_residue_pos F).le]
  rw [dedekindZeta_residue_def, Nat.cast_natAbs, Int.cast_abs]
  ring

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. Multiplying
the Mertens product at the pole ordinate by the logarithm of the cutoff gives
a limit of `exp (-γ)` divided by the norm-one class volume. -/
theorem reciprocalHeckeEulerProductBelow_mertens (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    Tendsto (fun x : ℝ ↦ (Real.log x : ℂ) * reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩)
      atTop (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) /
        (normOneIdeleClassTamagawaMeasure F univ).toReal : ℝ) : ℂ)) := by
  have h := (reciprocalHeckeEulerProductBelow_mertens_cutoff_height (F := F)).comp Real.tendsto_log_atTop
  have hcorr : Tendsto (fun x : ℝ ↦ (heckeEulerProductLogCorrection (1 : U[F]) x 1).re) atTop (𝓝 0) :=
    (Complex.continuous_re.tendsto (0 : ℂ)).comp
      ((heckeEulerProductLogCorrection_tendstoUniformly (1 : U[F])).tendsto_at (0 : ℝ))
  have he := Real.continuous_exp.continuousAt.tendsto.comp (h.neg.add hcorr)
  rw [add_zero, neg_add, Real.exp_add, Real.exp_neg (Real.log _),
    Real.exp_log (dedekindZeta_residue_pos F), ←div_eq_mul_inv] at he
  have hreal : Tendsto (fun x : ℝ ↦ Real.log x * ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℝ)⁻¹)) atTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / dedekindZeta_residue F)) := by
    refine he.congr' ?_
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 1), eventually_gt_atTop (0 : ℝ)] with x hx hx'
    dsimp only [Function.comp_apply]
    rw [max_eq_right hx.le, reciprocalHeckeEulerProductBelow_mertens_product_log x hx',
      neg_sub, sub_eq_add_neg, add_assoc, Real.exp_add, Real.exp_log (zero_lt_one.trans hx)]
  rw [reciprocalHeckeEulerProductBelow_mertens_volume F]
  apply ((Complex.continuous_ofReal.tendsto _).comp hreal).congr
  intro x
  rw [reciprocalHeckeEulerProductBelow_at_pole_eq_prod χ t₀ x hχ]
  simp


/-- One Euler polynomial compared with the same polynomial at a point further to the right:
the loss is at most a sixth power of a quotient of real Euler polynomials. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_factor
    (y a : ℝ) (hy0 : 0 < y) (hy : y ≤ 1 / 2) (ha0 : 0 < a) (ha1 : a < 1) (z : ℂ) (hz : ‖z‖ = y) :
    (1 / 2 ≤ a → ‖1 - z‖ ≤
      ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ * ((1 - y * a ^ 2) / (1 - y * a)) ^ 6) ∧
    (a ≤ 3 / 4 → 1 ≤
      ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ * ((1 - y * a ^ 2) / (1 - y * a)) ^ 6) := by
  have hd0 : 0 ≤ y * a * (1 - a) := mul_nonneg (mul_nonneg hy0.le ha0.le) (by linarith)
  have hya : y * a < 1 := by nlinarith
  have hden : 0 < 1 - y * a := by linarith
  have hq : 1 + y * a * (1 - a) ≤ (1 - y * a ^ 2) / (1 - y * a) := by
    rw [le_div_iff₀ hden]
    nlinarith [mul_nonneg hd0 (mul_nonneg hy0.le ha0.le)]
  have hpow : 1 + 6 * (y * a * (1 - a)) ≤ ((1 - y * a ^ 2) / (1 - y * a)) ^ 6 := by
    have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ y * a * (1 - a)) 6
    push_cast at h
    exact h.trans (pow_le_pow_left₀ (by linarith) hq 6)
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hnz : ‖z * ((a ^ 2 : ℝ) : ℂ)‖ = y * a ^ 2 := by
    rw [norm_mul, hz, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hlow : 1 - y * a ^ 2 ≤ ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (z * ((a ^ 2 : ℝ) : ℂ))
    rw [norm_one, hnz] at h
    exact h
  have hhalf : 1 / 2 ≤ 1 - y * a ^ 2 := by nlinarith [mul_le_of_le_one_right hy0.le ha2]
  have hW : 1 / 2 ≤ ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ := hhalf.trans hlow
  refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
  · have hdiff : ‖1 - z‖ ≤ ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ + y * (1 - a ^ 2) := by
      have h := norm_add_le (1 - z * ((a ^ 2 : ℝ) : ℂ)) (z * (((a ^ 2 : ℝ) : ℂ) - 1))
      have hn : ‖z * (((a ^ 2 : ℝ) : ℂ) - 1)‖ = y * (1 - a ^ 2) := by
        rw [norm_mul, hz, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [hn] at h
      refine le_trans (le_of_eq ?_) h
      congr 1
      ring
    have h3 : y * (1 - a ^ 2) ≤ 3 * (y * a * (1 - a)) := by
      nlinarith [mul_nonneg (mul_nonneg hy0.le (by linarith : (0 : ℝ) ≤ 1 - a))
        (by linarith : (0 : ℝ) ≤ 2 * a - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤
      ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖), mul_le_mul_of_nonneg_right hW hd0]
  · have h3 : y * a ^ 2 ≤ 3 * (y * a * (1 - a)) := by
      nlinarith [mul_nonneg (mul_nonneg hy0.le ha0.le) (by linarith : (0 : ℝ) ≤ 3 - 4 * a)]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤
      ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖), mul_le_mul_of_nonneg_right hW hd0,
      mul_le_mul_of_nonneg_right hlow hd0]

/-- The reciprocal Euler factor of a pure norm character is an Euler polynomial in the norm. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_inv_factor
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (v : V[F]) (s : ℂ) :
    (finiteHeckeEulerFactor χ v s)⁻¹ =
      1 - (v.asIdeal.absNorm : ℂ) ^ (-(s + -Complex.I * t₀)) := by
  rw [reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor χ _ hχ, inv_inv]

/-- With `δ log x = 1`, each reciprocal Euler factor on the 1-line below the cutoff, and the
constant one above it, is bounded by the factor at distance `δ` to the right times a sixth
power of a quotient of factors at the pole ordinate. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_local
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδx : δ * Real.log x = 1) (t : ℝ) (v : V[F]) :
    ((v.asIdeal.absNorm : ℝ) < x → ‖(finiteHeckeEulerFactor χ v ⟨1, t⟩)⁻¹‖ ≤
      ‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t⟩)⁻¹‖ *
        (‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t₀⟩)⁻¹‖ /
          ‖(finiteHeckeEulerFactor χ v ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6) ∧
    (x ≤ (v.asIdeal.absNorm : ℝ) → 1 ≤
      ‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t⟩)⁻¹‖ *
        (‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t₀⟩)⁻¹‖ /
          ‖(finiteHeckeEulerFactor χ v ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6) := by
  have hN1 := HeightOneSpectrum.one_lt_absNorm v
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hNC : (v.asIdeal.absNorm : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (v.asIdeal.absNorm : ℝ) ^ (-(δ / 2)) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (v.asIdeal.absNorm : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ,
      z = (v.asIdeal.absNorm : ℂ) ^ (-((⟨1, t⟩ : ℂ) + -Complex.I * t₀)) := ⟨_, rfl⟩
  have ha0 : 0 < a := ha ▸ Real.rpow_pos_of_pos hN0 _
  have ha1 : a < 1 := ha ▸ Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hy0 : 0 < y := hy ▸ inv_pos.mpr hN0
  have hyh : y ≤ 1 / 2 := by
    rw [hy, one_div]
    exact inv_anti₀ (by norm_num) hN
  have ha2 : a ^ 2 = (v.asIdeal.absNorm : ℝ) ^ (-δ) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hreal : ∀ σ : ℝ, (v.asIdeal.absNorm : ℂ) ^ (-((⟨σ, t₀⟩ : ℂ) + -Complex.I * t₀)) =
      (((v.asIdeal.absNorm : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro σ
    rw [Complex.ofReal_cpow hN0.le, Complex.ofReal_natCast]
    congr 1
    apply Complex.ext <;> simp
  have hz : ‖z‖ = y := by
    rw [hzdef, Complex.norm_natCast_cpow_of_pos (by omega), hy, ← Real.rpow_neg_one]
    congr 1
    simp
  have hshift : (v.asIdeal.absNorm : ℂ) ^ (-((⟨1 + δ, t⟩ : ℂ) + -Complex.I * t₀)) =
      z * ((a ^ 2 : ℝ) : ℂ) := by
    rw [hzdef, ha2, Complex.ofReal_cpow hN0.le, Complex.ofReal_natCast,
      ← Complex.cpow_add _ _ hNC]
    congr 1
    apply Complex.ext <;> simp
    ring
  have h1 : (v.asIdeal.absNorm : ℝ) ^ (-(1 + δ)) = y * a ^ 2 := by
    rw [ha2, hy, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1
    ring
  have h2 : (v.asIdeal.absNorm : ℝ) ^ (-(1 + δ / 2)) = y * a := by
    rw [ha, hy, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
    congr 1
    ring
  have hya : y * a < 1 := by nlinarith
  have hya2 : y * a ^ 2 < 1 := by nlinarith
  have e0 : ‖(finiteHeckeEulerFactor χ v ⟨1, t⟩)⁻¹‖ = ‖1 - z‖ := by
    rw [reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_inv_factor χ t₀ hχ,
      hzdef]
  have e1 : ‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t⟩)⁻¹‖ = ‖1 - z * ((a ^ 2 : ℝ) : ℂ)‖ := by
    rw [reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_inv_factor χ t₀ hχ,
      hshift]
  have e2 : ‖(finiteHeckeEulerFactor χ v ⟨1 + δ, t₀⟩)⁻¹‖ = 1 - y * a ^ 2 := by
    rw [reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_inv_factor χ t₀ hχ,
      hreal, h1, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have e3 : ‖(finiteHeckeEulerFactor χ v ⟨1 + δ / 2, t₀⟩)⁻¹‖ = 1 - y * a := by
    rw [reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_inv_factor χ t₀ hχ,
      hreal, h2, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  rw [e0, e1, e2, e3]
  obtain ⟨hA, hB⟩ :=
    reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_factor y a hy0 hyh ha0 ha1
      z hz
  have hlogx : 0 < Real.log x := Real.log_pos hx
  refine ⟨fun hNx ↦ hA ?_, fun hNx ↦ hB ?_⟩
  · have hlog : Real.log (v.asIdeal.absNorm : ℝ) < Real.log x := Real.log_lt_log hN0 hNx
    have hmul := mul_lt_mul_of_pos_left hlog hδ
    rw [ha, Real.rpow_def_of_pos hN0]
    have h := Real.add_one_le_exp (Real.log (v.asIdeal.absNorm : ℝ) * -(δ / 2))
    nlinarith
  · have hlog : Real.log x ≤ Real.log (v.asIdeal.absNorm : ℝ) :=
      Real.log_le_log (by linarith) hNx
    have hmul := mul_le_mul_of_nonneg_left hlog hδ.le
    rw [ha, Real.rpow_def_of_pos hN0]
    have h3 : Real.log (v.asIdeal.absNorm : ℝ) * -(δ / 2) ≤ -(1 / 2) := by nlinarith
    have h4 : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
      have h5 := Real.add_one_le_exp (1 / 2 : ℝ)
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      norm_num at h5 ⊢
      linarith
    linarith [Real.exp_le_exp.mpr h3]

/-- With `δ log x = 1`, the reciprocal partial product on the 1-line is bounded by the
reciprocal of the L-value at distance `δ` to the right times a sixth power of a quotient of
L-values at the pole ordinate. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_bound
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδx : δ * Real.log x = 1) (t : ℝ) :
    ‖reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩‖ ≤
      ‖(L ⟨1 + δ, t⟩)⁻¹‖ * (‖(L ⟨1 + δ, t₀⟩)⁻¹‖ / ‖(L ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6 := by
  classical
  have hprod : ∀ s : ℂ, 1 < s.re → L s ≠ 0 ∧
      Tendsto (fun T : Finset V[F] ↦ ∏ v ∈ T, finiteHeckeEulerFactor χ v s) atTop (𝓝 (L s)) := by
    intro s hs
    rw [show L s = finiteHeckeL χ ⟨s, hs⟩ from hSeries ⟨s, hs⟩]
    exact ⟨finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s, hs⟩, finiteHeckeL_hasProd χ ⟨s, hs⟩⟩
  obtain ⟨hne1, hl1⟩ := hprod ⟨1 + δ, t⟩ (show (1 : ℝ) < 1 + δ by linarith)
  obtain ⟨hne2, hl2⟩ := hprod ⟨1 + δ, t₀⟩ (show (1 : ℝ) < 1 + δ by linarith)
  obtain ⟨hne3, hl3⟩ := hprod ⟨1 + δ / 2, t₀⟩ (show (1 : ℝ) < 1 + δ / 2 by linarith)
  have hlim := ((hl1.inv₀ hne1).norm).mul
    ((((hl2.inv₀ hne2).norm).div ((hl3.inv₀ hne3).norm)
      (norm_ne_zero_iff.mpr (inv_ne_zero hne3))).pow 6)
  refine ge_of_tendsto hlim (eventually_atTop.mpr ⟨heckePrimesBelow F x, fun T hT ↦ ?_⟩)
  have hloc := fun v : V[F] ↦
    reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_local χ t₀ hχ hx hδ hδx t v
  have hP : ‖reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩‖ =
      ∏ v ∈ T, if v ∈ heckePrimesBelow F x then
        ‖(finiteHeckeEulerFactor χ v ⟨1, t⟩)⁻¹‖ else 1 := by
    rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hT]
    delta reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
    exact norm_prod _ _
  show ‖reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩‖ ≤
    ‖(∏ v ∈ T, finiteHeckeEulerFactor χ v ⟨1 + δ, t⟩)⁻¹‖ *
      (‖(∏ v ∈ T, finiteHeckeEulerFactor χ v ⟨1 + δ, t₀⟩)⁻¹‖ /
        ‖(∏ v ∈ T, finiteHeckeEulerFactor χ v ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6
  rw [hP, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    norm_prod, norm_prod, norm_prod, ← Finset.prod_div_distrib, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun v _ ↦ ?_) fun v _ ↦ ?_
  · by_cases hv : v ∈ heckePrimesBelow F x
    · rw [ite_eq_left hv]
      exact norm_nonneg _
    · rw [ite_eq_right hv]
      exact zero_le_one
  · by_cases hv : v ∈ heckePrimesBelow F x
    · rw [ite_eq_left hv]
      exact (hloc v).1 ((heckePrimesBelow_mem_iff v x).mp hv)
    · rw [ite_eq_right hv]
      exact (hloc v).2 (not_lt.mp fun h ↦ hv ((heckePrimesBelow_mem_iff v x).mpr h))

/-- Near a point where a meromorphic function is not locally zero, halving the real distance
to the point changes its size by at most a bounded factor. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_ratio
    (L : ℂ → ℂ) (s₀ : ℂ) (hL : MeromorphicAt L s₀) (hord : meromorphicOrderAt L s₀ ≠ ⊤) :
    ∃ C : ℝ, ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ‖L (s₀ + ((δ / 2 : ℝ) : ℂ))‖ ≤ C * ‖L (s₀ + (δ : ℂ))‖ := by
  have hΘ := hL.isTheta_pow_sub hord
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = (meromorphicOrderAt L s₀).untop hord := ⟨_, rfl⟩
  rw [← hn] at hΘ
  obtain ⟨c₁, hc₁, h₁⟩ := hΘ.1.exists_pos
  obtain ⟨c₂, hc₂, h₂⟩ := hΘ.2.exists_pos
  have hm : ∀ φ : ℝ → ℝ, Continuous φ → φ 0 = 0 → (∀ δ : ℝ, 0 < δ → 0 < φ δ) →
      Tendsto (fun δ : ℝ ↦ s₀ + ((φ δ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] s₀) := by
    intro φ hφ hφ0 hφpos
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun δ : ℝ ↦ s₀ + ((φ δ : ℝ) : ℂ)) (𝓝 0) (𝓝 (s₀ + ((φ 0 : ℝ) : ℂ))) :=
        (continuous_const.add (Complex.continuous_ofReal.comp hφ)).tendsto 0
      rw [hφ0, Complex.ofReal_zero, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      intro h
      have h0 : ((φ δ : ℝ) : ℂ) = 0 := add_eq_left.mp h
      exact (hφpos δ hδ).ne' (Complex.ofReal_eq_zero.mp h0)
  refine ⟨c₁ * ((1 / 2 : ℝ) ^ n * c₂), ?_⟩
  filter_upwards [(hm (fun δ ↦ δ / 2) (continuous_id.div_const 2) (by norm_num)
      (fun δ hδ ↦ by positivity)).eventually h₁.bound,
    (hm (fun δ ↦ δ) continuous_id rfl (fun δ hδ ↦ hδ)).eventually h₂.bound,
    self_mem_nhdsWithin] with δ hδ1 hδ2 hδ
  have hδ0 : (0 : ℝ) < δ := hδ
  rw [add_sub_cancel_left, norm_zpow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    at hδ1 hδ2
  have hhalf : (δ / 2 : ℝ) ^ n = (1 / 2 : ℝ) ^ n * δ ^ n := by
    rw [← mul_zpow]
    congr 1
    ring
  calc ‖L (s₀ + ((δ / 2 : ℝ) : ℂ))‖ ≤ c₁ * ((1 / 2 : ℝ) ^ n * δ ^ n) := by
        rw [← hhalf]
        exact hδ1
    _ ≤ c₁ * ((1 / 2 : ℝ) ^ n * (c₂ * ‖L (s₀ + (δ : ℂ))‖)) := by gcongr
    _ = c₁ * ((1 / 2 : ℝ) ^ n * c₂) * ‖L (s₀ + (δ : ℂ))‖ := by ring

/-- If continuous functions `P x` satisfy `P x * L → 1` uniformly on a compact set, then they
tend uniformly to the reciprocal of `L` there. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_of_mul
    (P : ℝ → ℝ → ℂ) (L : ℝ → ℂ) (K : Set ℝ) (hK : IsCompact K)
    (hP : ∀ x : ℝ, ContinuousOn (P x) K)
    (h : TendstoUniformlyOn (fun x : ℝ ↦ fun t : ℝ ↦ P x t * L t) (fun _ ↦ 1) atTop K) :
    TendstoUniformlyOn P (fun t : ℝ ↦ (L t)⁻¹) atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  obtain ⟨x₁, hx₁⟩ := (h (1 / 2) (by norm_num)).exists
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hP x₁)
  have hM0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hL : ∀ t ∈ K, L t ≠ 0 ∧ ‖(L t)⁻¹‖ ≤ 2 * max C 0 := by
    intro t ht
    have h1 := hx₁ t ht
    rw [dist_comm, dist_eq_norm] at h1
    have h2 : 1 / 2 < ‖P x₁ t * L t‖ := by
      have h3 := norm_sub_norm_le 1 (P x₁ t * L t)
      rw [norm_one, norm_sub_rev] at h3
      linarith
    have hne : L t ≠ 0 := by
      intro h0
      rw [h0, mul_zero, norm_zero] at h2
      norm_num at h2
    refine ⟨hne, ?_⟩
    rw [norm_mul] at h2
    have hLpos : 0 < ‖L t‖ := norm_pos_iff.mpr hne
    have hPC : ‖P x₁ t‖ ≤ max C 0 := (hC t ht).trans (le_max_left _ _)
    rw [norm_inv, inv_le_iff_one_le_mul₀ hLpos]
    nlinarith [mul_le_mul_of_nonneg_right hPC hLpos.le]
  intro ε hε
  have hδ : 0 < ε / (2 * max C 0 + 1) := by positivity
  filter_upwards [h _ hδ] with x hx t ht
  obtain ⟨hne, hb⟩ := hL t ht
  have h1 := hx t ht
  rw [dist_comm, dist_eq_norm] at h1
  have h7 : (L t)⁻¹ - P x t = -((L t)⁻¹ * (P x t * L t - 1)) := by
    field_simp
    ring
  rw [dist_eq_norm, h7, norm_neg, norm_mul]
  calc ‖(L t)⁻¹‖ * ‖P x t * L t - 1‖
      ≤ 2 * max C 0 * (ε / (2 * max C 0 + 1)) :=
        mul_le_mul hb h1.le (norm_nonneg _) (by positivity)
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith

/-- Near the pole ordinate the reciprocal partial products and the reciprocal of the
continuation are both uniformly small for large cutoffs. -/
private theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_pole
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 t₀, ∀ᶠ x : ℝ in atTop, ∀ t ∈ U,
      dist ((L ⟨1, t⟩)⁻¹) (reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) < ε := by
  have hgen : ∀ s : ℂ, 1 ≤ s.re → meromorphicOrderAt L s ≤ 0 := by
    intro s hs
    obtain ⟨A, hA, h⟩ := finiteHeckeL_zeroFreeRegion
    obtain ⟨B, hB, hB'⟩ := h F χ
    refine hB' L hL hSeries s ?_
    have hlog : 0 < Real.log (B * (|s.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg s.im])
    have h0 : 0 ≤ A / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B * (|s.im| + 3))) :=
      div_nonneg hA.le (mul_nonneg (by positivity) hlog.le)
    linarith
  have hord : meromorphicOrderAt L ⟨1, t₀⟩ < 0 :=
    lt_of_le_of_ne (hgen ⟨1, t₀⟩ le_rfl)
      (reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne_pole χ t₀ hχ htriv L hL
        hSeries)
  have hLs₀ : L ⟨1, t₀⟩ = 0 := by
    by_contra h
    exact hord.ne ((hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr h)
  have hinv : Tendsto (fun z : ℂ ↦ (L z)⁻¹) (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_cobounded_of_meromorphicOrderAt_neg hord)
  obtain ⟨C, hC⟩ :=
    reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_ratio L ⟨1, t₀⟩
      (hL (mem_univ _)).meromorphicAt hord.ne_top
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hε' : 0 < ε / (2 * ((max C 0) ^ 6 + 1)) := by positivity
  obtain ⟨ρ, hρ, hρb⟩ := Metric.tendsto_nhdsWithin_nhds.mp hinv _ hε'
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC
  have hδ₁0 : (0 : ℝ) < δ₁ := hδ₁
  refine ⟨Metric.ball t₀ (ρ / 2), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  filter_upwards [eventually_gt_atTop 1,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop δ₁⁻¹),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (ρ / 2)⁻¹)] with x hx1 hx2 hx3 t ht
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  obtain ⟨δ, hdelta⟩ : ∃ δ : ℝ, δ = (Real.log x)⁻¹ := ⟨_, rfl⟩
  have hδ : 0 < δ := hdelta ▸ inv_pos.mpr hlogx
  have hδx : δ * Real.log x = 1 := by
    rw [hdelta]
    exact inv_mul_cancel₀ hlogx.ne'
  have hδ1 : δ < δ₁ := by
    rw [hdelta]
    exact inv_lt_of_inv_lt₀ hδ₁0 hx2
  have hδρ : δ < ρ / 2 := by
    rw [hdelta]
    exact inv_lt_of_inv_lt₀ (by positivity) hx3
  have htd : |t - t₀| < ρ / 2 := by
    have h := Metric.mem_ball.mp ht
    rwa [Real.dist_eq] at h
  have hb := reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_bound χ t₀ hχ L
    hSeries hx1 hδ hδx t
  have hsmall : ∀ z : ℂ, z ≠ ⟨1, t₀⟩ → ‖z - ⟨1, t₀⟩‖ < ρ →
      ‖(L z)⁻¹‖ < ε / (2 * ((max C 0) ^ 6 + 1)) := by
    intro z hz hzd
    have h := hρb (x := z) hz (by rwa [dist_eq_norm])
    rwa [dist_zero_right] at h
  have h1 : ‖(L ⟨1 + δ, t⟩)⁻¹‖ < ε / (2 * ((max C 0) ^ 6 + 1)) := by
    refine hsmall _ (fun h ↦ ?_) ?_
    · have h' : 1 + δ = 1 := congrArg Complex.re h
      linarith
    · refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      show |1 + δ - 1| + |t - t₀| < ρ
      rw [add_sub_cancel_left, abs_of_pos hδ]
      linarith
  have h2 : ‖(L ⟨1 + δ, t₀⟩)⁻¹‖ / ‖(L ⟨1 + δ / 2, t₀⟩)⁻¹‖ ≤ max C 0 := by
    have hCδ : ‖L ((⟨1, t₀⟩ : ℂ) + ((δ / 2 : ℝ) : ℂ))‖ ≤ C * ‖L ((⟨1, t₀⟩ : ℂ) + (δ : ℂ))‖ :=
      hδ₁b ⟨hδ, hδ1⟩
    have e1 : (⟨1, t₀⟩ : ℂ) + ((δ / 2 : ℝ) : ℂ) = ⟨1 + δ / 2, t₀⟩ := by
      apply Complex.ext <;> simp
    have e2 : (⟨1, t₀⟩ : ℂ) + (δ : ℂ) = ⟨1 + δ, t₀⟩ := by
      apply Complex.ext <;> simp
    rw [e1, e2] at hCδ
    have hmem : (⟨1 + δ, t₀⟩ : ℂ) ∈ Complex.re ⁻¹' Ioi (1 : ℝ) := by
      show (1 : ℝ) < 1 + δ
      linarith
    have hne : L ⟨1 + δ, t₀⟩ ≠ 0 := by
      rw [show L ⟨1 + δ, t₀⟩ = finiteHeckeL χ ⟨⟨1 + δ, t₀⟩, hmem⟩ from hSeries ⟨_, hmem⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ _
    rw [norm_inv, norm_inv, inv_div_inv, div_le_iff₀ (norm_pos_iff.mpr hne)]
    exact hCδ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have h3 : ‖(L ⟨1, t⟩)⁻¹‖ < ε / 2 := by
    by_cases hne : t = t₀
    · rw [hne, hLs₀, inv_zero, norm_zero]
      positivity
    · have h := hsmall ⟨1, t⟩ (fun h ↦ hne (congrArg Complex.im h)) (by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
        show |(1 : ℝ) - 1| + |t - t₀| < ρ
        rw [sub_self, abs_zero, zero_add]
        linarith)
      refine h.trans_le (div_le_div_of_nonneg_left hε.le (by norm_num) ?_)
      nlinarith [pow_nonneg hC0 6]
  have h4 : ‖reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩‖ < ε / 2 := by
    refine lt_of_le_of_lt hb ?_
    have hpow : (‖(L ⟨1 + δ, t₀⟩)⁻¹‖ / ‖(L ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6 ≤ (max C 0) ^ 6 :=
      pow_le_pow_left₀ (by positivity) h2 6
    calc ‖(L ⟨1 + δ, t⟩)⁻¹‖ * (‖(L ⟨1 + δ, t₀⟩)⁻¹‖ / ‖(L ⟨1 + δ / 2, t₀⟩)⁻¹‖) ^ 6
        ≤ ε / (2 * ((max C 0) ^ 6 + 1)) * (max C 0) ^ 6 :=
          mul_le_mul h1.le hpow (by positivity) hε'.le
      _ < ε / 2 := by
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [pow_nonneg hC0 6]
  calc dist ((L ⟨1, t⟩)⁻¹) (reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
      ≤ ‖(L ⟨1, t⟩)⁻¹‖ + ‖reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩‖ := by
        rw [dist_eq_norm]
        exact norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h3 h4
    _ = ε := by ring

/-- Paper: Remark B.7.2.7, p. 653. For a pure norm character the reciprocal
partial products tend locally uniformly on the 1-line to the reciprocal of the
continued finite L-function. Its reciprocal takes the removable value zero at the pole.
Deviation: Local uniform convergence holds across the pole ordinate as well (R27). -/
theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
      (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε t₁
  have haway : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun x : ℝ ↦ fun t : ℝ ↦
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩) (fun _ ↦ 1) atTop K →
      ∀ᶠ x : ℝ in atTop, ∀ t ∈ K,
        dist ((L ⟨1, t⟩)⁻¹) (reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) < ε := by
    intro K hK h
    exact Metric.tendstoUniformlyOn_iff.mp
      (reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_of_mul
        (fun x t ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩) (fun t ↦ L ⟨1, t⟩) K hK
        (fun x ↦
          (heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne_continuous
            χ x).continuousOn) h) ε hε
  by_cases htriv : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · by_cases heq : t₁ = t₀
    · rw [heq]
      exact reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist_pole χ t₀ hχ htriv
        L hL hSeries hε
    · have hr : 0 < |t₁ - t₀| / 2 := by
        have h := abs_pos.mpr (sub_ne_zero.mpr heq)
        positivity
      refine ⟨Metric.closedBall t₁ (|t₁ - t₀| / 2), Metric.closedBall_mem_nhds _ hr,
        haway _ (isCompact_closedBall _ _)
          (reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist χ t₀ hχ L hL hSeries
            _ (isCompact_closedBall _ _) fun h ↦ ?_)⟩
      rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] at h
      linarith
  · exact ⟨Metric.closedBall t₁ 1, Metric.closedBall_mem_nhds _ one_pos,
      haway _ (isCompact_closedBall _ _)
        (reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne χ htriv
          L hL hSeries _ (isCompact_closedBall _ _))⟩

end RiemannMasullo
