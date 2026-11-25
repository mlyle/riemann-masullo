module
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.SmoothedPNT
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Fixed-frequency prime sums and the two-cosine prime-power correction

The prime number theorem gives the leading term of the logarithm-weighted sum of
`p ^ r` over primes for every fixed purely imaginary exponent `r`. For the rational
two-cosine probe in Theorem 12.5.1.1, pp. 519–520, this determines the complete
contribution of composite prime powers at the square-root scale. The prime squares
give an explicit oscillating main term. Chebyshev's bound controls the higher powers.
-/

open Filter MeasureTheory Set
open scoped Topology

public noncomputable section

namespace RiemannMasullo

private def twistPrimeSum (r : ℂ) (X a b : ℝ) :=
  (∑ p ∈ (Finset.Ioc ⌊X * a⌋₊ ⌊X * b⌋₊).filter Nat.Prime,
    (((p : ℝ) / X : ℝ) : ℂ) ^ r * (Real.log p : ℂ)) / (X : ℂ)

private theorem twistPrimeSum_short {r : ℂ} (hr : r.re = 0) {X a : ℝ} (hX : 0 < X) (ha : 0 ≤ a) :
    ‖twistPrimeSum r X 0 a‖ ≤ Real.log 4 * a := by
  let S := (Finset.Ioc 0 ⌊X * a⌋₊).filter Nat.Prime
  have hs : (∑ p ∈ S, Real.log (p : ℝ)) = Chebyshev.theta (X * a) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    dsimp only [S]
    congr 1
  change ‖_ / (X : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX, div_le_iff₀ hX]
  simp only [mul_zero, Nat.floor_zero]
  calc
    _ ≤ ∑ p ∈ S, ‖(((p : ℝ) / X : ℝ) : ℂ) ^ r * (Real.log p : ℂ)‖ := norm_sum_le _ _
    _ = ∑ p ∈ S, Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hP := (Finset.mem_filter.mp hp).2
      have hpos : (0 : ℝ) < p := by exact_mod_cast hP.pos
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hpos hX), hr, Real.rpow_zero,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hP.one_le))]
    _ ≤ _ := by
      rw [hs]
      convert Chebyshev.theta_le_log4_mul_x (mul_nonneg hX.le ha) using 1; ring

private theorem twistPrimeSum_split (r : ℂ) {X a : ℝ} (hX : 0 ≤ X) (ha : a ≤ 1) :
    twistPrimeSum r X 0 a + twistPrimeSum r X a 1 = twistPrimeSum r X 0 1 := by
  dsimp only [twistPrimeSum]
  rw [← add_div]
  simp only [Finset.sum_filter, mul_zero, Nat.floor_zero]
  apply congrArg (· / (X : ℂ))
  apply Finset.sum_Ioc_consecutive _ (Nat.zero_le _)
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left ha hX

private theorem twistPrimeSum_shell {r : ℂ} (hr : r.re = 0) {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    Tendsto (fun X ↦ twistPrimeSum r X a 1) atTop
      (𝓝 ((1 - (a : ℂ) ^ (r + 1)) / (r + 1))) := by
  let K (t : ℝ) := (t : ℂ) ^ r
  let K' (t : ℝ) := r * (t : ℂ) ^ (r - 1)
  have hd (t : ℝ) (ht : t ∈ Icc a 1) : HasDerivAt K (K' t) t := by
    by_cases h : r = 0
    · simp [K, K', h, hasDerivAt_const]
    exact hasDerivAt_ofReal_cpow_const (ha.trans_le ht.1).ne' h
  have hc : ContinuousOn K' (Icc a 1) := fun t ht ↦ continuousWithinAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const _ _ (.inr (ha.trans_le ht.1).ne')).continuousWithinAt
  have hh := tendsto_scaled_sum_prime_log ha ha' hd hc
  have hi : (∫ t in a..1, K t) = (1 - (a : ℂ) ^ (r + 1)) / (r + 1) := by
    simpa [K] using (integral_cpow (a := a) (b := 1) (r := r) (.inl (by linarith : -1 < r.re)))
  rw [hi] at hh
  exact hh

/-- The fixed-height twist of the prime number theorem, demodulated at the cutoff.
The logarithmic prime measure has Mellin moment `1 / (1 + r)` for purely imaginary `r`. -/
private theorem tendsto_demodulated_prime_log_cpow (r : ℂ) (hr : r.re = 0) :
    Tendsto (fun X : ℝ ↦ (∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      (((p : ℝ) / X : ℝ) : ℂ) ^ r * (Real.log p : ℂ)) / (X : ℂ)) atTop (𝓝 (1 / (r + 1))) := by
  suffices h : Tendsto (fun X ↦ twistPrimeSum r X 0 1) atTop (𝓝 (1 / (r + 1))) by
    simpa only [twistPrimeSum, mul_zero, mul_one, Nat.floor_zero] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC : 0 < Real.log 4 + 1 := by positivity
  obtain ⟨a, ha, haq⟩ := exists_between (lt_min zero_lt_one (div_pos (half_pos hε) hC))
  have ha1 := (lt_min_iff.mp haq).1
  have hsmall := (lt_div_iff₀ hC).mp (lt_min_iff.mp haq).2
  have hr1 : 1 ≤ ‖r + 1‖ := by simpa [hr] using Complex.re_le_norm (r + 1)
  have hcorr : ‖(a : ℂ) ^ (r + 1) / (r + 1)‖ ≤ a := by
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.add_re, hr]
    simp only [Complex.one_re, zero_add, Real.rpow_one]
    exact div_le_self ha.le hr1
  have hclose := Metric.tendsto_nhds.mp (twistPrimeSum_shell hr ha ha1.le) (ε/2) (half_pos hε)
  filter_upwards [hclose, eventually_gt_atTop (0 : ℝ)] with X hx hX
  rw [dist_eq_norm] at hx ⊢
  rw [← twistPrimeSum_split r hX.le ha1.le]
  have H : twistPrimeSum r X 0 a + twistPrimeSum r X a 1 - 1 / (r + 1) =
      twistPrimeSum r X 0 a + (twistPrimeSum r X a 1 - (1 - (a : ℂ) ^ (r + 1)) / (r + 1)) -
        (a : ℂ) ^ (r + 1) / (r + 1) := by ring
  rw [H]
  exact (norm_sub_le ..).trans_lt (by
    have hbound := norm_add_le (twistPrimeSum r X 0 a) (twistPrimeSum r X a 1 - (1 - (a : ℂ) ^ (r + 1)) / (r + 1))
    have hshort := twistPrimeSum_short hr hX ha.le
    nlinarith)

/-- The log-weighted prime sum with a fixed purely imaginary exponent has main term
`X ^ (r + 1) / (r + 1)`, with error o(X). -/
theorem tendsto_prime_log_cpow_sub_main (r : ℂ) (hr : r.re = 0) :
    Tendsto (fun X : ℝ ↦ (∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      (p : ℂ) ^ r * (Real.log p : ℂ)) / (X : ℂ) - (X : ℂ) ^ r / (r + 1)) atTop (𝓝 0) := by
  let T (X : ℝ) := twistPrimeSum r X 0 1
  have hT : Tendsto T atTop (𝓝 (1 / (r + 1))) := by
    simpa only [T, twistPrimeSum, mul_zero, mul_one, Nat.floor_zero] using
      tendsto_demodulated_prime_log_cpow r hr
  have he (X : ℝ) (hX : 0 < X) :
      (∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
        (p : ℂ) ^ r * (Real.log p : ℂ)) / (X : ℂ) - (X : ℂ) ^ r / (r + 1) =
        (X : ℂ) ^ r * (T X - 1 / (r + 1)) := by
    have hn : (X : ℂ) ^ r ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl (by exact_mod_cast hX.ne'))
    dsimp only [T, twistPrimeSum]
    simp only [mul_zero, mul_one, Nat.floor_zero, Complex.ofReal_div, Complex.ofReal_natCast]
    rw [mul_sub, ← mul_div_assoc, Finset.mul_sum]
    congr 2
    · apply Finset.sum_congr rfl
      intro p _
      have heq := Complex.div_cpow_ofReal_nonneg (a := p) p.cast_nonneg hX.le r
      simp only [Complex.ofReal_natCast] at heq
      rw [heq]
      field_simp
    · ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hl : Tendsto (fun X ↦ ‖T X - 1 / (r + 1)‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hT.sub_const (1 / (r + 1))).norm
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [he X hX, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX, hr, Real.rpow_zero, one_mul]

private theorem rationalPrime_cosine_cpow_re (t x : ℝ) (hx : 0 < x) :
    ((x : ℂ) ^ ((t : ℂ) * Complex.I)).re = Real.cos (t * Real.log x) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Complex.exp_re]
  simp [Complex.mul_re, Complex.mul_im, mul_comm]

private theorem tendsto_prime_log_cos_sub_main (t : ℝ) :
    Tendsto (fun X : ℝ ↦ (∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      Real.cos (t * Real.log p) * Real.log p) / X -
      ((X : ℂ) ^ ((t : ℂ) * Complex.I) / ((t : ℂ) * Complex.I + 1)).re) atTop (𝓝 0) := by
  let r : ℂ := (t : ℂ) * Complex.I
  have h := (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_prime_log_cpow_sub_main r (by simp [r])))
  apply (show Tendsto _ _ (𝓝 (0 : ℝ)) from h).congr'
  apply Eventually.of_forall
  intro X
  simp only [Function.comp_apply, Complex.sub_re, Complex.div_ofReal_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  have hpos : 0 < (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  rw [← Complex.ofReal_natCast, rationalPrime_cosine_cpow_re t p hpos]

/-- For the two-cosine first-prime test, the prime-square contribution divided by
the square root of the cutoff has this explicitly oscillating main term. -/
private theorem tendsto_twoCosine_primeSquares_sub_main :
    let A (t X : ℝ) := ((X : ℂ) ^ ((t : ℂ) * Complex.I) / ((t : ℂ) * Complex.I + 1)).re
    Tendsto (fun X : ℝ ↦ (∑ p ∈ (Finset.Ioc 0 ⌊Real.sqrt X⌋₊).filter Nat.Prime,
      (2 - Real.cos (2 * Real.log p) - Real.cos (Real.sqrt 2 * (2 * Real.log p))) *
        Real.log p) / Real.sqrt X -
      (2 - A 2 (Real.sqrt X) - A (2 * Real.sqrt 2) (Real.sqrt X))) atTop (𝓝 0) := by
  intro A
  have h0 : Tendsto (fun Y : ℝ ↦ (∑ p ∈ (Finset.Ioc 0 ⌊Y⌋₊).filter Nat.Prime, Real.log (p : ℝ)) / Y - 1)
      atTop (𝓝 0) := by simpa using tendsto_prime_log_cos_sub_main 0
  have h1 := tendsto_prime_log_cos_sub_main 2
  have h2 := tendsto_prime_log_cos_sub_main (2 * Real.sqrt 2)
  have H := (((h0.const_mul 2).sub h1).sub h2).comp Real.tendsto_sqrt_atTop
  apply (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa only [mul_zero, sub_zero] using H).congr'
  apply Eventually.of_forall
  intro X
  dsimp only [Function.comp_apply, A]
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, ← mul_assoc (Real.sqrt 2) 2,
    mul_comm (Real.sqrt 2) 2]
  ring

private def twoCosinePowerSum (X : ℝ) (k : ℕ) :=
  ∑ p ∈ (Finset.Ioc 0 ⌊X ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
    (2 - Real.cos (k * Real.log p) - Real.cos (Real.sqrt 2 * (k * Real.log p))) * Real.log p

private theorem twoCosinePowerSum_le (X : ℝ) (hX : 1 ≤ X) (k : ℕ) (hk : 3 ≤ k) :
    0 ≤ twoCosinePowerSum X k ∧ twoCosinePowerSum X k ≤ 4 * Real.log 4 * X ^ (1 / (3 : ℝ)) := by
  let S := (Finset.Ioc 0 ⌊X ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime
  have hb (u : ℝ) : 0 ≤ 2 - Real.cos u - Real.cos (Real.sqrt 2 * u) ∧
      2 - Real.cos u - Real.cos (Real.sqrt 2 * u) ≤ 4 := by
    constructor <;> linarith [Real.cos_le_one u, Real.cos_le_one (Real.sqrt 2 * u),
      Real.neg_one_le_cos u, Real.neg_one_le_cos (Real.sqrt 2 * u)]
  have hlog (p : ℕ) (hp : p ∈ S) : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)
  constructor
  · exact Finset.sum_nonneg (fun p hp ↦ mul_nonneg (hb _).1 (hlog p hp))
  calc
    twoCosinePowerSum X k ≤ ∑ p ∈ S, 4 * Real.log (p : ℝ) :=
      Finset.sum_le_sum (fun p hp ↦ mul_le_mul_of_nonneg_right (hb _).2 (hlog p hp))
    _ = 4 * Chebyshev.theta (X ^ (1 / (k : ℝ))) := by
      rw [← Finset.mul_sum, Chebyshev.theta_eq_sum_Icc]
      rfl
    _ ≤ 4 * (Real.log 4 * X ^ (1 / (k : ℝ))) := by
      gcongr
      apply Chebyshev.theta_le_log4_mul_x
      positivity
    _ ≤ _ := by
      rw [← mul_assoc]
      gcongr
      exact_mod_cast hk

private def twoCosineHigherPrimePowers (X : ℝ) :=
  ∑ k ∈ Finset.Icc 3 ⌊Real.log X / Real.log 2⌋₊, twoCosinePowerSum X k

private theorem tendsto_twoCosineHigherPrimePowers :
    Tendsto (fun X ↦ twoCosineHigherPrimePowers X / Real.sqrt X) atTop (𝓝 0) := by
  let C := 4 * Real.log 4 / Real.log 2
  have hlim : Tendsto (fun X : ℝ ↦ C * (Real.log X / X ^ (1 / (6 : ℝ)))) atTop (𝓝 0) := by
    simpa using ((isLittleO_log_rpow_atTop (show 0 < 1 / (6 : ℝ) by norm_num)).tendsto_div_nhds_zero.const_mul C)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    apply div_nonneg _ (Real.sqrt_nonneg _)
    exact Finset.sum_nonneg (fun k hk ↦ (twoCosinePowerSum_le X hX k (Finset.mem_Icc.mp hk).1).1)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    let N := ⌊Real.log X / Real.log 2⌋₊
    have hX0 : 0 < X := zero_lt_one.trans_le hX
    have hN : ((Finset.Icc 3 N).card : ℝ) ≤ Real.log X / Real.log 2 := by
      apply le_trans _ (Nat.floor_le (div_nonneg (Real.log_nonneg hX) (by positivity)))
      exact_mod_cast (show (Finset.Icc 3 N).card ≤ N by simp only [Nat.card_Icc]; omega)
    have hbd : twoCosineHigherPrimePowers X ≤ (Real.log X / Real.log 2) * (4 * Real.log 4 * X ^ (1 / (3 : ℝ))) := by
      calc
        _ ≤ ∑ k ∈ Finset.Icc 3 N, 4 * Real.log 4 * X ^ (1 / (3 : ℝ)) :=
          Finset.sum_le_sum (fun k hk ↦ (twoCosinePowerSum_le X hX k (Finset.mem_Icc.mp hk).1).2)
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
    refine (div_le_div_of_nonneg_right hbd (Real.sqrt_nonneg _)).trans_eq ?_
    have hpow : Real.sqrt X = X ^ (1 / (3 : ℝ)) * X ^ (1 / (6 : ℝ)) := by
      rw [← Real.rpow_add hX0, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [hpow]
    dsimp [C]
    field_simp

/-- The entire composite prime-power contribution for the two-cosine physical count:
the prime-square main term is explicit and all higher exponents are o(√X). -/
theorem tendsto_twoCosine_compositePrimePowers_sub_main :
    let A (t X : ℝ) := ((X : ℂ) ^ ((t : ℂ) * Complex.I) / ((t : ℂ) * Complex.I + 1)).re
    Tendsto (fun X : ℝ ↦ (∑ k ∈ Finset.Icc 2 ⌊Real.log X / Real.log 2⌋₊,
      ∑ p ∈ (Finset.Ioc 0 ⌊X ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime,
        (2 - Real.cos (k * Real.log p) - Real.cos (Real.sqrt 2 * (k * Real.log p))) *
          Real.log p) / Real.sqrt X -
      (2 - A 2 (Real.sqrt X) - A (2 * Real.sqrt 2) (Real.sqrt X))) atTop (𝓝 0) := by
  intro A
  have h := tendsto_twoCosine_primeSquares_sub_main.add tendsto_twoCosineHigherPrimePowers
  have hN : Tendsto (fun X : ℝ ↦ ⌊Real.log X / Real.log 2⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by positivity))
  apply (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa only [add_zero] using h).congr'
  filter_upwards [hN.eventually_ge_atTop 2] with X hX
  let N := ⌊Real.log X / Real.log 2⌋₊
  have hsplit : (∑ k ∈ Finset.Icc 2 N, twoCosinePowerSum X k) =
      twoCosinePowerSum X 2 + twoCosineHigherPrimePowers X := by
    rw [← Finset.insert_Icc_succ_left_eq_Icc (show 2 ≤ N from hX), Finset.sum_insert (by simp)]
    rfl
  change _ = (∑ k ∈ Finset.Icc 2 N, twoCosinePowerSum X k) / Real.sqrt X - _
  rw [hsplit, add_div]
  simp only [twoCosinePowerSum, Nat.cast_ofNat, ← Real.sqrt_eq_rpow, A]
  ring

end RiemannMasullo
