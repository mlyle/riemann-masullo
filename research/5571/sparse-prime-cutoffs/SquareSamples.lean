module

public import RiemannMasullo.Ch13_ZerosHecke.RationalCompensatedPrimeZeros
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt

public noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing
namespace RiemannMasullo.SquareSamples

local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "Λ₀" => continuedCompletedHeckeL (F := ℚ) χ₀

open Set MeasureTheory Finset

private abbrev w (t : ℝ) := 2 - Real.cos t - Real.cos (Real.sqrt 2 * t)

private theorem w_bounds (t : ℝ) : 0 ≤ w t ∧ w t ≤ 4 := by
  constructor <;> unfold w <;> linarith [Real.cos_le_one t, Real.cos_le_one (Real.sqrt 2 * t),
    Real.neg_one_le_cos t, Real.neg_one_le_cos (Real.sqrt 2 * t)]

private theorem discrete_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (a k - 1) * w (Real.log k)) - 4 ≤
      ∑ k ∈ Icc 1 (n+1), (a k - 1) * w (Real.log k) := by
  rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hw := w_bounds (Real.log (n + 1 : ℕ))
  nlinarith [mul_nonneg (ha (n+1)) hw.1]

private theorem integral_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Icc 1 n, a k * w (Real.log k)) - (∫ t in (1:ℝ)..n, w (Real.log t)) - 4 ≤
      (∑ k ∈ Icc 1 (n+1), a k * w (Real.log k)) -
      ∫ t in (1:ℝ)..(n+1 : ℕ), w (Real.log t) := by
  have hint {b c : ℝ} (hb : 0 < b) (hbc : b ≤ c) :
      IntervalIntegrable (fun t ↦ w (Real.log t)) volume b c := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hbc]
    have hlog : ContinuousOn Real.log (Set.Icc b c) :=
      Real.continuousOn_log.mono fun x hx ↦ (hb.trans_le hx.1).ne'
    exact (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn hlog)).sub
      (Real.continuous_cos.comp_continuousOn (continuousOn_const.mul hlog))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (n : ℝ))
    (b := n+1) (C := 4) (f := fun t ↦ w (Real.log t)) (fun t _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (w_bounds _).1]; exact (w_bounds _).2)
  rw [show (n:ℝ)+1-n=1 by ring] at hb
  simp only [abs_one, mul_one, Real.norm_eq_abs] at hb
  have hupper := (le_abs_self _).trans hb
  rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1), Nat.cast_add_one,
    ← intervalIntegral.integral_add_adjacent_intervals (hint zero_lt_one hn') (hint hn0 (by linarith : (n:ℝ) ≤ n+1))]
  have hmass := mul_nonneg (ha (n+1)) (w_bounds (Real.log (n+1 : ℕ))).1
  push_cast at hmass
  linarith

theorem interpolation (E : ℕ → ℝ)
    (hstep : ∀ n ≥ 1, E n - 4 ≤ E (n+1)) {r C : ℝ} (hr : 1/2 ≤ r) (hr' : r ≤ 1)
    (hC : 0 ≤ C) (hsq : ∀ k : ℕ, 1 ≤ k → |E (k^2)| ≤ C * ((k^2 : ℕ) : ℝ)^r) (n : ℕ) (hpos : 1 ≤ n) :
    |E n| ≤ (4*C+12) * (n:ℝ)^r := by
  have hr0 : 0 ≤ r := by linarith
  have hprop (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) : E i - 4*((j:ℝ)-i) ≤ E j := by
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      push_cast
      linarith [hstep j (by omega)]
  let k := n.sqrt
  have hlo : k^2 ≤ n := Nat.sqrt_le' n
  have hup : n ≤ (k+1)^2 := (Nat.lt_succ_sqrt' n).le
  have hk : 1 ≤ k := Nat.le_sqrt'.mpr (by simpa using (show 1 ≤ n by omega))
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hlor : (k:ℝ)^2 ≤ n := by exact_mod_cast hlo
  have hupr : (n:ℝ) ≤ ((k:ℝ)+1)^2 := by exact_mod_cast hup
  have hkN : (k:ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by positivity) (by positivity)).2 hlor
  have hsqr : Real.sqrt n ≤ (n:ℝ)^r := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le hn hr
  have hnr : 1 ≤ (n:ℝ)^r := Real.one_le_rpow hn hr0
  have hU : (↑((k+1)^2 : ℕ) : ℝ) ≤ 4 * n := by
    push_cast
    nlinarith [sq_nonneg ((k:ℝ)-1)]
  have hU' : (↑((k+1)^2 : ℕ) : ℝ)^r ≤ 4*(n:ℝ)^r := by
    calc
      _ ≤ (4 * (n:ℝ))^r := Real.rpow_le_rpow (by positivity) hU hr0
      _ = (4:ℝ)^r * (n:ℝ)^r := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        calc (4:ℝ)^r ≤ (4:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr'
             _ = _ := Real.rpow_one _) (by positivity)
  have hL' : (↑(k^2 : ℕ) : ℝ)^r ≤ (n:ℝ)^r :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlo) hr0
  have hlow := hprop (k^2) n (by nlinarith) hlo
  have hhigh := hprop n ((k+1)^2) hpos hup
  have hlow' := (abs_le.mp (hsq k hk)).1
  have hhigh' := (abs_le.mp (hsq (k+1) (by omega))).2
  have hlow'' := mul_le_mul_of_nonneg_left hL' hC
  have hhigh'' := mul_le_mul_of_nonneg_left hU' hC
  have hspan : (↑((k+1)^2 : ℕ):ℝ) - (↑(k^2 : ℕ):ℝ) ≤ 3*(n:ℝ)^r := by
    push_cast; nlinarith
  have hlo' : (↑(k^2 : ℕ):ℝ) ≤ n := by exact_mod_cast hlo
  have hup' : (n:ℝ) ≤ (↑((k+1)^2 : ℕ):ℝ) := by exact_mod_cast hup
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hC (show 0 ≤ (n:ℝ)^r by positivity)]

theorem first_prime_integral {r C : ℝ} (hr : 1/2 ≤ r) (hr' : r ≤ 1) (hC : 0 ≤ C) :
    let E := fun n : ℕ ↦ (∑ k ∈ Icc 1 n, (if k.Prime then Real.log k else 0) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))) -
      ∫ t in (1:ℝ)..n, 2 - Real.cos (Real.log t) - Real.cos (Real.sqrt 2 * Real.log t)
    (∀ k : ℕ, 1 ≤ k → |E (k^2)| ≤ C * ((k^2 : ℕ) : ℝ)^r) →
    ∀ n : ℕ, 1 ≤ n → |E n| ≤ (4*C+12) * (n:ℝ)^r := by
  intro E h n hn
  let a (k : ℕ) := if k.Prime then Real.log k else 0
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  exact interpolation E (integral_step a ha) hr hr' hC h n hn

theorem first_prime_discrete {r C : ℝ} (hr : 1/2 ≤ r) (hr' : r ≤ 1) (hC : 0 ≤ C) :
    let E := fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((if k.Prime then Real.log k else 0) - 1) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))
    (∀ k : ℕ, 1 ≤ k → |E (k^2)| ≤ C * ((k^2 : ℕ) : ℝ)^r) →
    ∀ n : ℕ, 1 ≤ n → |E n| ≤ (4*C+12) * (n:ℝ)^r := by
  intro E h n hn
  let a (k : ℕ) := if k.Prime then Real.log k else 0
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  exact interpolation E (fun j _ ↦ discrete_step a ha j) hr hr' hC h n hn

private theorem of_square_growth (E : ℕ → ℝ) {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ < 1)
    (hstep : ∀ n ≥ 1, E n - 4 ≤ E (n+1))
    (hsq : ∀ r : ℝ, σ < r → r < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |E (k^2)| ≤ C * ((k^2 : ℕ):ℝ)^r) (r : ℝ) (hr : σ < r) :
    ∃ D : ℝ, ∀ n : ℕ, 1 ≤ n → |E n| ≤ D * (n:ℝ)^r := by
  let q := min r ((σ+1)/2)
  have hq : σ < q := lt_min hr (by linarith)
  have hq' : q < 1 := lt_of_le_of_lt (min_le_right ..) (by linarith)
  obtain ⟨C,hC,hk⟩ := hsq q hq hq'
  refine ⟨4*C+12, fun n hn ↦ (interpolation E hstep (hσ.trans hq.le) hq'.le hC hk n hn).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (min_le_left ..)

theorem zero_free_of_square_discrete {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ < 1)
    (hsq : ∀ r : ℝ, σ < r → r < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |rationalCompensatedPrimeError (k^2)| ≤ C * ((k^2 : ℕ):ℝ)^r)
    {z : ℂ} (hz : σ < z.re) : MeromorphicOn.divisor Λ₀ univ z ≤ 0 ∧ riemannZeta z ≠ 0 := by
  let a (k : ℕ) := if k.Prime then Real.log k else 0
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  apply rationalPrincipal_zero_free_of_compensatedPrimeError hσ hσ₁ _ hz
  intro r hr
  obtain ⟨D,hD⟩ := of_square_growth rationalCompensatedPrimeError hσ hσ₁
    (fun n _ ↦ by simpa only [rationalCompensatedPrimeError_apply,
      rationalPrimeCosineWeight_apply] using discrete_step a ha n) hsq r hr
  refine ⟨D, fun n ↦ ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [rationalCompensatedPrimeError_apply, Real.zero_rpow (by linarith : r ≠ 0)]
  · exact hD n hn

theorem zero_free_of_square_integral {σ : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ < 1)
    (hsq : ∀ r : ℝ, σ < r → r < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k →
      |(∑ p ∈ Icc 1 (k^2) with p.Prime, Real.log p * rationalPrimeCosineWeight (Real.log p)) -
       ∫ x in (1:ℝ)..(k^2 : ℕ), rationalPrimeCosineWeight (Real.log x)| ≤ C * ((k^2 : ℕ):ℝ)^r)
    {z : ℂ} (hz : σ < z.re) : MeromorphicOn.divisor Λ₀ univ z ≤ 0 ∧ riemannZeta z ≠ 0 := by
  let a (k : ℕ) := if k.Prime then Real.log k else 0
  let E (n : ℕ) := (∑ p ∈ Icc 1 n with p.Prime, Real.log p * rationalPrimeCosineWeight (Real.log p)) -
      ∫ x in (1:ℝ)..n, rationalPrimeCosineWeight (Real.log x)
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  have hE (n : ℕ) : E n = (∑ k ∈ Icc 1 n, a k * w (Real.log k)) -
      ∫ t in (1:ℝ)..n, w (Real.log t) := by
    simp only [E, Finset.sum_filter, rationalPrimeCosineWeight_apply, w]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.Prime <;> simp [a,h]
  apply rationalPrincipal_zero_free_of_compensatedPrimeIntegralError hσ hσ₁ _ hz
  exact of_square_growth E hσ hσ₁ (fun n hn ↦ by
    rw [hE,hE]; exact integral_step a ha n hn) hsq

#print axioms zero_free_of_square_integral
#print axioms zero_free_of_square_discrete

#print axioms interpolation
#print axioms first_prime_integral
#print axioms first_prime_discrete

end RiemannMasullo.SquareSamples
