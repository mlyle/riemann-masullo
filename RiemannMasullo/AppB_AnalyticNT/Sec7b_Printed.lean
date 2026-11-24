module

public import RiemannMasullo.AppB_AnalyticNT.Sec7b
import Mathlib.Algebra.Field.ULift

/-!
# Appendix B.7.2: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Paragraph after Equation (B.7.2.12), p. 650. At the pole ordinate
the printed value of the normalized oscillatory term is minus one. -/
def Printed.heckePrimePowerTailOscillation_at_pole : Prop :=
  ∀ (t₀ : ℝ) (n : ℕ), 2 ≤ n →
    Tendsto (fun t : ℝ ↦ heckePrimePowerTailOscillation t₀ n ⟨1, t⟩ / (Real.log n : ℂ))
      (𝓝[≠] t₀) (𝓝 (-1))

/-- Paper: Paragraph after Equation (B.7.2.12), p. 650. With `t₀ = 0` and
`n = 2`, the quotient off the pole has limit `log 2` at `s = 1`, giving
normalized value one. -/
theorem Printed.heckePrimePowerTailOscillation_at_pole_false :
    ¬ Printed.heckePrimePowerTailOscillation_at_pole := by
  intro h
  have h1 := h 0 2 le_rfl
  have hmap : Tendsto (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (⟨1, 0⟩ : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) := by
        have he : (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ (1 : ℂ) + t * Complex.I := by
          funext t
          apply Complex.ext <;> simp
        rw [he]
        fun_prop
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      intro heq
      exact ht (congrArg Complex.im heq)
  have hlog : (Real.log (2 : ℕ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact (Real.log_pos (by norm_num)).ne'
  have h2 := ((heckePrimePowerTailOscillation_tendsto_at_pole 0 (n := 2) two_pos).comp
    hmap).div_const (Real.log (2 : ℕ) : ℂ)
  rw [div_self hlog] at h2
  have h3 := tendsto_nhds_unique h1 h2
  norm_num at h3

/-- Paper: Theorem B.7.2.4(1), Equations (B.7.2.18)–(B.7.2.19), p. 652.
In the printed product comparison the first term of `G_x` has the sign
corresponding to denominator `i log(M - 1) (t - t₀)`. -/
def Printed.reciprocalHeckeEulerProductBelow_mul_normTwist : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
    ∀ (K : Set ℝ), IsCompact K → t₀ ∉ K → ∀ ε > (0 : ℝ),
      ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℕ, x₀ ≤ (x : ℝ) →
        ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
          let G := heckePrimePowerTailOscillation t₀ (x - 1) ⟨1, t⟩ /
              (Real.log ((x - 1 : ℕ) : ℝ) : ℂ) -
            ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n
          ‖error t‖ ≤ 2 * ε / Real.log x ∧
          reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
            Complex.exp (error t + G + heckeEulerProductLogCorrection χ x ⟨1, t⟩)

/-- With pole ordinate zero, the oscillatory term at `1 + i` is `(m ^ (-i) - 1) / (-i)`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_false_osc (m : ℕ) :
    heckePrimePowerTailOscillation 0 m ⟨1, 1⟩ =
      ((m : ℂ) ^ (-Complex.I) - 1) / (-Complex.I) := by
  have hne : (⟨1, 1⟩ : ℂ) ≠ ⟨1, (0 : ℝ)⟩ := fun h ↦ one_ne_zero (congrArg Complex.im h)
  have hsub : (⟨1, (0 : ℝ)⟩ : ℂ) - ⟨1, 1⟩ = -Complex.I := by
    apply Complex.ext <;> simp
  delta heckePrimePowerTailOscillation
  simp only [hne, ↓reduceIte]
  rw [hsub]

/-- With pole ordinate zero, the oscillatory term at `1 + i` has norm at most two. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_false_osc_le (m : ℕ)
    (hm : 0 < m) : ‖heckePrimePowerTailOscillation 0 m ⟨1, 1⟩‖ ≤ 2 := by
  rw [reciprocalHeckeEulerProductBelow_mul_normTwist_false_osc, norm_div, norm_neg,
    Complex.norm_I, div_one]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_natCast_cpow_of_pos hm, Complex.neg_re, Complex.I_re, neg_zero,
    Real.rpow_zero, norm_one]
  norm_num

/-- With pole ordinate zero, the oscillatory term at `1 + i` has norm at least one when
the cosine of `log m` is not positive. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_false_one_le_osc (m : ℕ)
    (hm : 0 < m) (hcos : Real.cos (Real.log m) ≤ 0) :
    1 ≤ ‖heckePrimePowerTailOscillation 0 m ⟨1, 1⟩‖ := by
  rw [reciprocalHeckeEulerProductBelow_mul_normTwist_false_osc, norm_div, norm_neg,
    Complex.norm_I, div_one]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hre : ((m : ℂ) ^ (-Complex.I) - 1).re = Real.cos (Real.log m) - 1 := by
    rw [Complex.sub_re, Complex.one_re, Complex.cpow_def_of_ne_zero hm', ← Complex.natCast_log,
      Complex.exp_re, mul_neg, Complex.neg_re, Complex.neg_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.I_re, Complex.I_im, mul_zero, mul_one, neg_zero,
      Real.exp_zero, one_mul, Real.cos_neg]
  have h1 := Complex.abs_re_le_norm ((m : ℂ) ^ (-Complex.I) - 1)
  rw [hre, abs_of_nonpos (by linarith)] at h1
  linarith

/-- Beyond every bound there is a natural number `m ≥ 3` with `cos (log m) ≤ 0`: take the
integer part of `exp ((2 k + 1) π)`. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_false_exists_nat (B : ℝ) :
    ∃ m : ℕ, B ≤ m ∧ 3 ≤ m ∧ Real.cos (Real.log m) ≤ 0 := by
  have hπ := Real.pi_gt_three
  obtain ⟨k, hk⟩ : ∃ k : ℕ, max B 3 ≤ (k : ℝ) := ⟨⌈max B 3⌉₊, Nat.le_ceil _⟩
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hy0 : 0 < Real.exp ((2 * k + 1) * Real.pi) := Real.exp_pos _
  have hyk : (k : ℝ) + 1 ≤ Real.exp ((2 * k + 1) * Real.pi) := by
    have h1 := Real.add_one_le_exp ((2 * k + 1) * Real.pi)
    nlinarith
  have hmk : k ≤ ⌊Real.exp ((2 * k + 1) * Real.pi)⌋₊ := Nat.le_floor (by linarith)
  have hmy := Nat.floor_le hy0.le
  have hym := Nat.lt_floor_add_one (Real.exp ((2 * k + 1) * Real.pi))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌊Real.exp ((2 * k + 1) * Real.pi)⌋₊ := ⟨_, rfl⟩
  rw [← hm] at hmk hmy hym
  have hmk' : (k : ℝ) ≤ m := by exact_mod_cast hmk
  have hm3 : (3 : ℝ) ≤ m := (le_max_right B 3).trans (hk.trans hmk')
  have hm0 : (0 : ℝ) < m := by linarith
  refine ⟨m, (le_max_left B 3).trans (hk.trans hmk'), by exact_mod_cast hm3, ?_⟩
  have hlogy : Real.log (Real.exp ((2 * k + 1) * Real.pi)) = (2 * k + 1) * Real.pi :=
    Real.log_exp _
  have hδ0 : 0 ≤ (2 * k + 1) * Real.pi - Real.log m := by
    have h1 := Real.log_le_log hm0 hmy
    rw [hlogy] at h1
    linarith
  have hδ1 : (2 * k + 1) * Real.pi - Real.log m ≤ 1 := by
    have h1 : Real.log (Real.exp ((2 * k + 1) * Real.pi) / m) =
        Real.log (Real.exp ((2 * k + 1) * Real.pi)) - Real.log m :=
      Real.log_div hy0.ne' hm0.ne'
    have h2 := Real.log_le_sub_one_of_pos (div_pos hy0 hm0)
    have h3 : Real.exp ((2 * k + 1) * Real.pi) / m - 1 ≤ 1 := by
      rw [sub_le_iff_le_add, div_le_iff₀ hm0]
      linarith
    rw [h1, hlogy] at h2
    linarith
  have he : Real.log m =
      Real.pi - ((2 * k + 1) * Real.pi - Real.log m) + (k : ℕ) * (2 * Real.pi) := by
    ring
  rw [he, Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub]
  have h4 := Real.cos_nonneg_of_mem_Icc
    (x := (2 * k + 1) * Real.pi - Real.log m) ⟨by linarith, by linarith⟩
  linarith

/-- Two exponential forms of one number are incompatible when their exponents differ by
`2 g / ℓ` with `1 ≤ ‖g‖ ≤ 2` and `1 ≤ ℓ`, up to two errors of size `(1 / 2) / ℓ'` with
`ℓ ≤ ℓ'`: the difference of the exponents is too small to be a nonzero period, and too
large to vanish. -/
private theorem reciprocalHeckeEulerProductBelow_mul_normTwist_false_core
    (Q e₁ e₂ g S H : ℂ) (ℓ ℓ' : ℝ) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ ℓ') (hg1 : 1 ≤ ‖g‖)
    (hg2 : ‖g‖ ≤ 2) (he₁ : ‖e₁‖ ≤ 2 * (1 / 4) / ℓ') (he₂ : ‖e₂‖ ≤ 2 * (1 / 4) / ℓ')
    (h1 : Q = Complex.exp (e₁ + (g / (ℓ : ℂ) - S) + H))
    (h2 : Q = Complex.exp (e₂ + (-g * (ℓ : ℂ)⁻¹ - S) + H)) : False := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (h1.symm.trans h2)
  have hD : e₁ - e₂ + 2 * g / (ℓ : ℂ) = n * (2 * Real.pi * Complex.I) := by
    linear_combination hn
  have hnormD : ‖2 * g / (ℓ : ℂ)‖ = 2 * ‖g‖ / ℓ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ0.le, Complex.norm_ofNat]
  have hE : ‖e₁‖ + ‖e₂‖ ≤ 1 / ℓ := by
    have h3 : 2 * (1 / 4) / ℓ' ≤ 2 * (1 / 4) / ℓ := by gcongr
    have h4 : 2 * (1 / 4) / ℓ + 2 * (1 / 4) / ℓ = 1 / ℓ := by ring
    linarith
  have hinv : 1 / ℓ ≤ 1 := by
    rw [div_le_one hℓ0]
    exact hℓ
  have hsmall : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 * Real.pi := by
    rw [← hD]
    have h5 : ‖e₁ - e₂ + 2 * g / (ℓ : ℂ)‖ ≤ ‖e₁‖ + ‖e₂‖ + 2 * ‖g‖ / ℓ := by
      rw [← hnormD]
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact norm_sub_le _ _
    have h6 : 2 * ‖g‖ / ℓ ≤ 4 * (1 / ℓ) := by
      rw [mul_one_div]
      gcongr
      linarith
    linarith [Real.pi_gt_three]
  have hn0 : n = 0 := by
    by_contra hne
    have h7 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
    have he : (n : ℂ) * (2 * Real.pi * Complex.I) =
        (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hsmall
    nlinarith [Real.pi_pos]
  rw [hn0, Int.cast_zero, zero_mul] at hD
  have h8 : 2 * g / (ℓ : ℂ) = e₂ - e₁ := by linear_combination hD
  have h9 : 2 * ‖g‖ / ℓ ≤ ‖e₁‖ + ‖e₂‖ := by
    rw [← hnormD, h8]
    exact (norm_sub_le _ _).trans (by linarith)
  have h10 : 2 * 1 / ℓ ≤ 2 * ‖g‖ / ℓ := by gcongr
  have h11 : 2 * 1 / ℓ ≤ 1 / ℓ := by linarith
  rw [div_le_div_iff_of_pos_right hℓ0] at h11
  norm_num at h11

/-- Paper: Theorem B.7.2.4(1), pp. 652–653. Take `F = ℚ`, `χ = 1`, `t₀ = 0`,
`K = {1}`, and `x = 1 + floor(exp((2k + 1)π))`. The printed and corrected
oscillations differ by `2 g_{x-1}(1+i) / log(x-1)`. Its norm times
`log x` tends to four, whereas both error bounds with `ε = 1/4` give a
combined bound of one. The difference of the exponents tends to zero,
so equality of the exponentials would force the difference to vanish. -/
theorem Printed.reciprocalHeckeEulerProductBelow_mul_normTwist_false :
    ¬ Printed.reciprocalHeckeEulerProductBelow_mul_normTwist := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation (1 : U[ULift ℚ])
  have hχ : ideleClassNormTwist (1 : U[ULift ℚ]) 0 =
      ideleClassNormTwist (1 : U[ULift ℚ]) (-Complex.I * ((0 : ℝ) : ℂ)) := by simp
  have hpole : (0 : ℝ) ∉ ({1} : Set ℝ) := by simp
  obtain ⟨x₁, -, h1⟩ := h (ULift ℚ) 1 0 hχ L hL hSeries {1} isCompact_singleton hpole (1 / 4)
    (by norm_num)
  obtain ⟨x₂, -, h2⟩ := _root_.RiemannMasullo.reciprocalHeckeEulerProductBelow_mul_normTwist
    (1 : U[ULift ℚ]) 0 hχ L hL hSeries {1} isCompact_singleton hpole
    (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨m, hmB, hm3, hcos⟩ :=
    reciprocalHeckeEulerProductBelow_mul_normTwist_false_exists_nat (max x₁ x₂)
  have hm3' : (3 : ℝ) ≤ m := by exact_mod_cast hm3
  have hm0 : (0 : ℝ) < m := by linarith
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    push_cast
    ring
  obtain ⟨e₁, -, he₁⟩ := h1 (m + 1) (by rw [hcast]; linarith [le_max_left x₁ x₂])
  obtain ⟨e₂, -, he₂⟩ := h2 ((m + 1 : ℕ) : ℝ) (by rw [hcast]; linarith [le_max_right x₁ x₂])
  obtain ⟨hb1, hE1⟩ := he₁ 1 (Set.mem_singleton 1)
  obtain ⟨hb2, hE2⟩ := he₂ 1 (Set.mem_singleton 1)
  delta heckeEulerProductOscillation at hE2
  rw [Nat.ceil_natCast, Nat.add_sub_cancel] at hE2
  rw [Nat.add_sub_cancel] at hE1
  refine reciprocalHeckeEulerProductBelow_mul_normTwist_false_core _ _ _ _ _ _ (Real.log m)
    (Real.log ((m + 1 : ℕ) : ℝ)) ?_ ?_
    (reciprocalHeckeEulerProductBelow_mul_normTwist_false_one_le_osc m (by omega) hcos)
    (reciprocalHeckeEulerProductBelow_mul_normTwist_false_osc_le m (by omega)) hb1 hb2 hE1 hE2
  · exact (Real.le_log_iff_exp_le hm0).mpr (by linarith [Real.exp_one_lt_d9])
  · exact Real.log_le_log hm0 (by rw [hcast]; linarith)

open Classical in
/-- Paper: Equation (B.7.2.23), p. 653. On and to the right of the 1-line,
excluding the pole of a pure norm character, the printed second equality
subtracts `H_x` from the ordered prime-power tail. Its left side sums over
primes in norm order, taking all positive powers at each prime. -/
def Printed.heckePrimePowerLogTail_sub_correction : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (x : ℕ), 1 < x → ∀ s : ℂ, 1 ≤ s.re →
    (∀ t₀ : ℝ, ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
      s ≠ ⟨1, t₀⟩) →
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      Tendsto (fun y : ℝ ↦
        ∑ v ∈ heckePrimesBelow F y \ heckePrimesBelow F x,
          ∑' k : ℕ, heckePrimePowerLogTerm χ v k s) atTop
        (𝓝 (heckePrimePowerLogTail χ x s - heckeEulerProductLogCorrection χ x s))

/-- The trivial character has ideal value one on every positive prime power. -/
private theorem heckePrimePowerLogTail_sub_correction_false_value (F : Type*) [Field F]
    [NumberField F] (v : V[F]) (k : ℕ) :
    heckeIdealValue (ideleClassNormTwist (1 : U[F]) 0) (v.asIdeal ^ (k + 1)) = 1 := by
  classical
  have hχ : ideleClassNormTwist (1 : U[F]) 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion F)ˣ) :
      (1 : HeckeCharacter (𝓞 F) F).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hu : (1 : HeckeCharacter (𝓞 F) F).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hunit (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let u := Units.mk0
    (val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose : v.adicCompletion F)
    val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hval : (1 : HeckeCharacter (𝓞 F) F).localValue v = 1 := hunit u
  rw [hχ, heckeIdealValue_prime_pow _ v (Nat.succ_pos k), ite_eq_left hu, hval, one_pow]

/-- At `s = 2` the logarithmic term of the trivial character is an explicit positive real. -/
private theorem heckePrimePowerLogTail_sub_correction_false_term (F : Type*) [Field F]
    [NumberField F] (v : V[F]) (k : ℕ) :
    heckePrimePowerLogTerm (1 : U[F]) v k 2 =
      (((((k + 1 : ℕ) : ℝ) * ((v.asIdeal.absNorm : ℝ) ^ (k + 1)) ^ 2)⁻¹ : ℝ) : ℂ) := by
  show heckeIdealValue (ideleClassNormTwist (1 : U[F]) 0) (v.asIdeal ^ (k + 1)) /
      (((k + 1 : ℕ) : ℂ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ (2 : ℂ)) = _
  rw [heckePrimePowerLogTail_sub_correction_false_value, map_pow]
  push_cast
  rw [one_div]
  norm_num

/-- The explicit real terms at `s = 2` are summable over all prime powers. -/
private theorem heckePrimePowerLogTail_sub_correction_false_summable (F : Type*) [Field F]
    [NumberField F] :
    Summable (fun a : V[F] × ℕ ↦
      (((a.2 + 1 : ℕ) : ℝ) * ((a.1.asIdeal.absNorm : ℝ) ^ (a.2 + 1)) ^ 2)⁻¹) := by
  have h := (summable_heckeHigherPrimePowerWeights F (σ := 1) (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_) h
  obtain ⟨v, k⟩ := a
  have hN : (1 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  have h1 : (v.asIdeal.absNorm : ℝ) ^ (k + 2) ≤ ((v.asIdeal.absNorm : ℝ) ^ (k + 1)) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hN (by omega)
  have h2 : ((k + 2 : ℕ) : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h3 := mul_le_mul h2 h1 (by positivity) (by positivity)
  dsimp only
  rw [Real.rpow_one, Nat.cast_pow, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- When the logarithmic terms are summable over all prime powers, the norm-ordered tail is
their sum over the prime powers of norm at least the cutoff. -/
private theorem heckePrimePowerLogTail_sub_correction_false_tail (F : Type*) [Field F]
    [NumberField F] (χ : U[F]) (x : ℝ) (hx : 0 < x) (s : ℂ)
    (hsum : Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s)) :
    heckePrimePowerLogTail χ x s =
      ∑' a : V[F] × ℕ,
        {a : V[F] × ℕ | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}.indicator
          (fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s) a := by
  classical
  set t : V[F] × ℕ → ℂ := fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s with ht
  set S : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} with hS
  let g : V[F] × ℕ → ℕ := fun a ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)
  have hfin : ∀ n : ℕ, Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := by
    intro n
    refine Set.Finite.to_subtype (s := {a : V[F] × ℕ | a.1.asIdeal.absNorm ^ (a.2 + 1) = n})
      (Set.Finite.subset
        ((Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F) n).prod
          (Set.finite_Iio n)) fun a ha ↦ ?_)
    have h1 := HeightOneSpectrum.one_lt_absNorm a.1
    have hga : a.1.asIdeal.absNorm ^ (a.2 + 1) = n := ha
    refine ⟨?_, ?_⟩
    · show a.1.asIdeal.absNorm ≤ n
      rw [← hga]
      exact Nat.le_self_pow (Nat.succ_ne_zero _) _
    · show a.2 < n
      rw [← hga]
      exact ((Nat.lt_succ_self _).trans Nat.lt_two_pow_self).trans_le
        (Nat.pow_le_pow_left h1 _)
  have hterm : ∀ n : ℕ,
      ∑' b : g ⁻¹' {n}, S.indicator t b = heckePrimePowerLogTailTerm χ x s n := by
    intro n
    have := hfin n
    change ∑' b : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}, S.indicator t b = _
    by_cases hn : x ≤ (n : ℝ)
    · have hn0 : n ≠ 0 := by
        rintro rfl
        rw [Nat.cast_zero] at hn
        exact absurd hx (not_lt.mpr hn)
      have hfs : (∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
          heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
            ((a.val.2 + 1 : ℕ) : ℂ)) =
          ∑' a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
            heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
              ((a.val.2 + 1 : ℕ) : ℂ) :=
        (tsum_eq_finsum (Set.toFinite _)).symm
      rw [heckePrimePowerLogTailTerm, ite_eq_left hn, LSeries.term_of_ne_zero hn0,
        heckePrimePowerLogCoefficient_eq_sum, hfs, ← tsum_div_const]
      refine tsum_congr fun b ↦ ?_
      have hb : b.1.1.asIdeal.absNorm ^ (b.1.2 + 1) = n := b.2
      have hbS : (b : V[F] × ℕ) ∈ S := by
        show x ≤ ((b.1.1.asIdeal.absNorm ^ (b.1.2 + 1) : ℕ) : ℝ)
        rw [hb]
        exact hn
      rw [Set.indicator_of_mem hbS]
      show heckeIdealValue _ (b.1.1.asIdeal ^ (b.1.2 + 1)) /
        (((b.1.2 + 1 : ℕ) : ℂ) * ((b.1.1.asIdeal ^ (b.1.2 + 1)).absNorm : ℂ) ^ s) = _
      rw [map_pow, hb, div_mul_eq_div_div]
    · rw [heckePrimePowerLogTailTerm, ite_eq_right hn]
      refine (tsum_congr fun b ↦ ?_).trans tsum_zero
      have hb : b.1.1.asIdeal.absNorm ^ (b.1.2 + 1) = n := b.2
      refine Set.indicator_of_notMem
        (fun hbS : x ≤ ((b.1.1.asIdeal.absNorm ^ (b.1.2 + 1) : ℕ) : ℝ) ↦ hn ?_) t
      rwa [hb] at hbS
  have hfib : HasSum (heckePrimePowerLogTailTerm χ x s) (∑' a, S.indicator t a) := by
    convert (hsum.indicator S).hasSum.tsum_fiberwise g using 1
    funext n
    exact (hterm n).symm
  show tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) = _
  rw [tsum_eq_of_summable_unconditional hfib.summable]
  exact hfib.tsum_eq

open Classical in
/-- When the logarithmic terms are summable over all prime powers, the sums over the primes
with norm in `[x, y)`, each with all of its powers, tend to the sum over all powers of the
primes of norm at least `x`. -/
private theorem heckePrimePowerLogTail_sub_correction_false_primeSum (F : Type*) [Field F]
    [NumberField F] (χ : U[F]) (x : ℝ) (s : ℂ)
    (hsum : Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s)) :
    Tendsto (fun y : ℝ ↦
      ∑ v ∈ heckePrimesBelow F y \ heckePrimesBelow F x,
        ∑' k : ℕ, heckePrimePowerLogTerm χ v k s) atTop
      (𝓝 (∑' a : V[F] × ℕ,
        {a : V[F] × ℕ | x ≤ (a.1.asIdeal.absNorm : ℝ)}.indicator
          (fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s) a)) := by
  set t : V[F] × ℕ → ℂ := fun a ↦ heckePrimePowerLogTerm χ a.1 a.2 s with ht
  set S : Set (V[F] × ℕ) := {a | x ≤ (a.1.asIdeal.absNorm : ℝ)} with hS
  have hfib : HasSum (fun v : V[F] ↦
      if x ≤ (v.asIdeal.absNorm : ℝ) then ∑' k : ℕ, t (v, k) else 0)
      (∑' a, S.indicator t a) := by
    refine (hsum.indicator S).hasSum.prod_fiberwise fun v ↦ ?_
    by_cases hv : x ≤ (v.asIdeal.absNorm : ℝ)
    · rw [ite_eq_left hv]
      have he : (fun k : ℕ ↦ S.indicator t (v, k)) = fun k ↦ t (v, k) := by
        funext k
        exact Set.indicator_of_mem (show (v, k) ∈ S from hv) t
      rw [he]
      exact (hsum.prod_factor v).hasSum
    · rw [ite_eq_right hv]
      have he : (fun k : ℕ ↦ S.indicator t (v, k)) = fun _ ↦ 0 := by
        funext k
        exact Set.indicator_of_notMem (show (v, k) ∉ S from hv) t
      rw [he]
      exact hasSum_zero
  have hmono : Tendsto (fun y : ℝ ↦ heckePrimesBelow F y) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun y y' hy v hv ↦ ?_)
      (fun v ↦ ⟨(v.asIdeal.absNorm : ℝ) + 1, ?_⟩)
    · rw [heckePrimesBelow_mem_iff] at hv ⊢
      exact hv.trans_le hy
    · rw [heckePrimesBelow_mem_iff]
      linarith
  refine (hfib.comp hmono).congr fun y ↦ ?_
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have hiff : v ∉ heckePrimesBelow F x ↔ x ≤ (v.asIdeal.absNorm : ℝ) := by
    rw [heckePrimesBelow_mem_iff, not_lt]
  beta_reduce
  by_cases hv : x ≤ (v.asIdeal.absNorm : ℝ)
  · rw [ite_eq_left hv, ite_eq_left (hiff.mpr hv)]
  · rw [ite_eq_right hv, ite_eq_right fun hn ↦ hv (hiff.mp hn)]

open Classical in
/-- For the trivial character at `s = 2` and the cutoff just above the norm of a prime, the
prime-ordered sums cannot have the printed limit, because the cutoff correction is a
strictly negative real number. -/
private theorem heckePrimePowerLogTail_sub_correction_false_aux (F : Type*) [Field F]
    [NumberField F] (v₀ : V[F]) (x : ℕ) (hx : x = v₀.asIdeal.absNorm + 1)
    (h : Tendsto (fun y : ℝ ↦
        ∑ v ∈ heckePrimesBelow F y \ heckePrimesBelow F x,
          ∑' k : ℕ, heckePrimePowerLogTerm (1 : U[F]) v k 2) atTop
        (𝓝 (heckePrimePowerLogTail (1 : U[F]) x 2 -
          heckeEulerProductLogCorrection (1 : U[F]) x 2))) :
    False := by
  have hN0 : (2 : ℝ) ≤ v₀.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have hXv : (x : ℝ) = (v₀.asIdeal.absNorm : ℝ) + 1 := by
    rw [hx]
    push_cast
    ring
  let r : V[F] × ℕ → ℝ := fun a ↦
    (((a.2 + 1 : ℕ) : ℝ) * ((a.1.asIdeal.absNorm : ℝ) ^ (a.2 + 1)) ^ 2)⁻¹
  have hr0 : ∀ a, 0 ≤ r a := fun a ↦ by
    show 0 ≤ (((a.2 + 1 : ℕ) : ℝ) * ((a.1.asIdeal.absNorm : ℝ) ^ (a.2 + 1)) ^ 2)⁻¹
    positivity
  have hrs : Summable r := heckePrimePowerLogTail_sub_correction_false_summable F
  have ht : (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm (1 : U[F]) a.1 a.2 2) =
      fun a ↦ ((r a : ℝ) : ℂ) :=
    funext fun a ↦ heckePrimePowerLogTail_sub_correction_false_term F a.1 a.2
  have hts : Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm (1 : U[F]) a.1 a.2 2) := by
    rw [ht]
    exact Complex.summable_ofReal.mpr hrs
  have hT := heckePrimePowerLogTail_sub_correction_false_tail F 1 x
    (by rw [hXv]; linarith) 2 hts
  have hA := heckePrimePowerLogTail_sub_correction_false_primeSum F 1 x 2 hts
  have hEq := tendsto_nhds_unique h hA
  have hind : ∀ S : Set (V[F] × ℕ),
      (∑' a, S.indicator (fun a ↦ ((r a : ℝ) : ℂ)) a) = ((∑' a, S.indicator r a : ℝ) : ℂ) := by
    intro S
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun a ↦ ?_
    by_cases ha : a ∈ S <;> simp [ha]
  have hH : heckeEulerProductLogCorrection (1 : U[F]) x 2 =
      -((∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        (x : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        r (a.val.1, a.val.2 + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    show -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        (x : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        heckePrimePowerLogTerm (1 : U[F]) a.val.1 (a.val.2 + 1) 2) = _
    congr 1
    exact tsum_congr fun a ↦
      heckePrimePowerLogTail_sub_correction_false_term F a.val.1 (a.val.2 + 1)
  rw [hT, ht, hind, hind, hH] at hEq
  have hinj : Function.Injective (fun a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      (x : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)} ↦
      ((a.val.1, a.val.2 + 1) : V[F] × ℕ)) := by
    intro a b hab
    have hab' : ((a.val.1, a.val.2 + 1) : V[F] × ℕ) = (b.val.1, b.val.2 + 1) := hab
    obtain ⟨h1, h2⟩ := Prod.mk.inj hab'
    exact Subtype.ext (Prod.ext h1 (Nat.succ_injective h2))
  have hmem : (v₀.asIdeal.absNorm : ℝ) < x ∧
      (x : ℝ) ≤ ((v₀.asIdeal.absNorm ^ (0 + 2) : ℕ) : ℝ) := by
    refine ⟨by rw [hXv]; linarith, ?_⟩
    rw [hXv]
    push_cast
    nlinarith
  have hpos : 0 < ∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      (x : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}, r (a.val.1, a.val.2 + 1) := by
    refine lt_of_lt_of_le ?_
      ((hrs.comp_injective hinj).le_tsum ⟨(v₀, 0), hmem⟩ fun j _ ↦ hr0 _)
    show 0 < (((0 + 1 + 1 : ℕ) : ℝ) * ((v₀.asIdeal.absNorm : ℝ) ^ (0 + 1 + 1)) ^ 2)⁻¹
    positivity
  have hle : ∑' a, {a : V[F] × ℕ | (x : ℝ) ≤ (a.1.asIdeal.absNorm : ℝ)}.indicator r a ≤
      ∑' a, {a : V[F] × ℕ | (x : ℝ) ≤
        ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}.indicator r a := by
    refine Summable.tsum_le_tsum (fun a ↦ Set.indicator_le_indicator_of_subset
      (fun a ha ↦ ?_) hr0 a) (hrs.indicator _) (hrs.indicator _)
    have h1 : (x : ℝ) ≤ (a.1.asIdeal.absNorm : ℝ) := ha
    have h2 : (a.1.asIdeal.absNorm : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_self_pow (Nat.succ_ne_zero a.2) a.1.asIdeal.absNorm
    exact h1.trans h2
  have hEq' : (∑' a, {a : V[F] × ℕ | (x : ℝ) ≤
        ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}.indicator r a) -
      -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        (x : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}, r (a.val.1, a.val.2 + 1)) =
      ∑' a, {a : V[F] × ℕ | (x : ℝ) ≤ (a.1.asIdeal.absNorm : ℝ)}.indicator r a := by
    exact_mod_cast hEq
  linarith

/-- Paper: Equation (B.7.2.23), p. 653. Over `ℚ` take the trivial character,
`x = 3`, and ordinate `2π / log 2` on the 1-line. The grouped tail includes
all powers of two with exponent at least two, whose sum is `log 2 - 1/2 > 0`.
The prime tail omits them and the printed subtraction counts them twice. -/
theorem Printed.heckePrimePowerLogTail_sub_correction_false :
    ¬ Printed.heckePrimePowerLogTail_sub_correction := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 (ULift ℚ))
  let v₀ : V[ULift ℚ] := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hN := HeightOneSpectrum.one_lt_absNorm v₀
  refine heckePrimePowerLogTail_sub_correction_false_aux (ULift ℚ) v₀
    (v₀.asIdeal.absNorm + 1) rfl
    (h (ULift ℚ) 1 (v₀.asIdeal.absNorm + 1) (by omega) 2 (by norm_num) fun t₀ _ hEq ↦ ?_).2
  have hre := congrArg Complex.re hEq
  norm_num at hre

/-- Paper: Remark B.7.2.7, p. 653. For every pure norm character and every
interval with the pole ordinate in its interior, convergence of the
reciprocal products is claimed to fail to be uniform on that interval. -/
def Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (L : ℂ → ℂ), MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
    ∀ (J : Set ℝ), OrdConnected J → t₀ ∈ interior J →
      ¬ TendstoUniformlyOn
        (fun x : ℕ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
        (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop J

/-- Paper: Remark B.7.2.7, p. 653. Take `F = ℚ`, `χ = 1`, `t₀ = 0`, and
`J = [-1, 1]`. A comparison of log moduli at abscissa `1 + 1 / log x`
bounds the reciprocal product near zero by a constant times
`|t| + 1 / log x`. This gives uniform convergence near the pole together
with the compact-uniform convergence away from it (R27). -/
theorem Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole_false :
    ¬ Printed.reciprocalHeckeEulerProductBelow_not_uniform_at_pole := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation (1 : U[ULift ℚ])
  have hχ : ideleClassNormTwist (1 : U[ULift ℚ]) 0 =
      ideleClassNormTwist (1 : U[ULift ℚ]) (-Complex.I * ((0 : ℝ) : ℂ)) := by simp
  refine h (ULift ℚ) 1 0 hχ L hL hSeries (Icc (-1) 1) ordConnected_Icc ?_ ?_
  · rw [interior_Icc]
    constructor <;> norm_num
  · have hloc := reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist
      (1 : U[ULift ℚ]) 0 hχ L hL hSeries
    have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc) (Icc (-1) 1) isCompact_Icc
    intro u hu
    exact tendsto_natCast_atTop_atTop.eventually (hunif u hu)

end RiemannMasullo
