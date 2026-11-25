module
public import RiemannMasullo.Ch13_ZerosHecke.RationalCompensatedPrimeError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

public noncomputable section

open Set MeasureTheory ArithmeticFunction Finset

namespace TwoCosineCrossings

private abbrev w (t : ℝ) := 2 - Real.cos t - Real.cos (Real.sqrt 2 * t)

private theorem w_bounds (t : ℝ) : 0 ≤ w t ∧ w t ≤ 4 := by
  constructor <;> unfold w <;> linarith [Real.cos_le_one t, Real.cos_le_one (Real.sqrt 2 * t),
    Real.neg_one_le_cos t, Real.neg_one_le_cos (Real.sqrt 2 * t)]

private theorem downward_passage {u : ℕ → ℝ} {M : ℕ}
    (hpos : ∃ n ≥ M, 0 < u n) (hneg : ∀ n, ∃ j ≥ n, u j ≤ 0) :
    ∃ n ≥ M, 0 < u n ∧ u (n + 1) ≤ 0 := by
  by_contra! h
  obtain ⟨n, hn, hu⟩ := hpos
  have hforever (k : ℕ) : 0 < u (n + k) := by
    induction k with
    | zero => simpa using hu
    | succ k ih => exact h (n + k) (by omega) ih
  obtain ⟨j, hj, hj'⟩ := hneg n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact (not_lt_of_ge hj') (hforever k)

private theorem downward_crossing {u : ℕ → ℝ} {M : ℕ}
    (hstep : ∀ n ≥ M, u n - 4 ≤ u (n + 1))
    (hpos : ∃ n ≥ M, 0 < u n) (hneg : ∀ n, ∃ j ≥ n, u j ≤ 0) :
    ∃ n ≥ M, -4 < u n ∧ u n ≤ 0 := by
  obtain ⟨n, hn, hu, hv⟩ := downward_passage hpos hneg
  exact ⟨n+1, by omega, by linarith [hstep n hn], hv⟩

private theorem discrete_step (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n : ℕ) :
    (∑ k ∈ Icc 1 n, (a k - 1) * w (Real.log k)) - 4 ≤
      ∑ k ∈ Icc 1 (n+1), (a k - 1) * w (Real.log k) := by
  rw [sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hw := w_bounds (Real.log (n + 1 : ℕ))
  nlinarith [mul_nonneg (ha (n+1)) hw.1]

private theorem centered_crossing {E : ℕ → ℝ} (hstep : ∀ n ≥ 1, E n - 4 ≤ E (n+1))
    {c : ℝ} (hc : c ≤ 0) (hpos : ∀ M : ℕ, ∃ n ≥ M, c * Real.sqrt n < E n)
    (hneg : ∀ M : ℕ, ∃ n ≥ M, E n ≤ c * Real.sqrt n) (M : ℕ) :
    ∃ n ≥ M, c * Real.sqrt n - 4 < E n ∧ E n ≤ c * Real.sqrt n := by
  let u (n : ℕ) := E n - c * Real.sqrt n
  have hs (n : ℕ) (hn : max M 1 ≤ n) : u n - 4 ≤ u (n+1) := by
    have h1 := hstep n (by omega)
    have h2 := mul_le_mul_of_nonpos_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ (n+1 : ℕ))) hc
    dsimp [u]; linarith
  obtain ⟨n, hn, hun⟩ := hpos (max M 1)
  obtain ⟨j, hj, hjl, hju⟩ := downward_crossing hs ⟨n, hn, sub_pos.mpr hun⟩ (fun k ↦ by
    obtain ⟨l, hl, hel⟩ := hneg k
    exact ⟨l, hl, sub_nonpos.mpr hel⟩)
  exact ⟨j, by omega, by dsimp [u] at hjl; linarith, sub_nonpos.mp hju⟩

theorem discrete_crossing (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : c ≤ 0) :
    let E := fun n : ℕ ↦ ∑ k ∈ Icc 1 n, (a k - 1) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))
    (∀ M : ℕ, ∃ n ≥ M, c * Real.sqrt n < E n) →
    (∀ M : ℕ, ∃ n ≥ M, E n ≤ c * Real.sqrt n) →
    ∀ M : ℕ, ∃ n ≥ M, c * Real.sqrt n - 4 < E n ∧ E n ≤ c * Real.sqrt n := by
  dsimp only
  exact centered_crossing (fun n _ ↦ discrete_step a ha n) hc

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

theorem integral_crossing (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) {c : ℝ} (hc : c ≤ 0) :
    let E := fun n : ℕ ↦ (∑ k ∈ Icc 1 n, a k *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))) -
      ∫ t in (1:ℝ)..n, 2 - Real.cos (Real.log t) - Real.cos (Real.sqrt 2 * Real.log t)
    (∀ M : ℕ, ∃ n ≥ M, c * Real.sqrt n < E n) →
    (∀ M : ℕ, ∃ n ≥ M, E n ≤ c * Real.sqrt n) →
    ∀ M : ℕ, ∃ n ≥ M, c * Real.sqrt n - 4 < E n ∧ E n ≤ c * Real.sqrt n := by
  dsimp only
  exact centered_crossing (integral_step a ha) hc

theorem first_prime_integral_crossing :
    let E := fun n : ℕ ↦ (∑ k ∈ Icc 1 n, (if k.Prime then Real.log k else 0) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))) -
      ∫ t in (1:ℝ)..n, 2 - Real.cos (Real.log t) - Real.cos (Real.sqrt 2 * Real.log t)
    (∀ M : ℕ, ∃ n ≥ M, 0 < E n) → (∀ M : ℕ, ∃ n ≥ M, E n ≤ 0) →
    ∀ M : ℕ, ∃ n ≥ M, -4 < E n ∧ E n ≤ 0 := by
  dsimp only
  simpa only [zero_mul, zero_sub] using
    integral_crossing (fun k : ℕ ↦ if k.Prime then Real.log k else 0) (fun k ↦ by
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
      · exact le_rfl) (c := 0) le_rfl

theorem first_prime_discrete_crossing :
    let E := fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((if k.Prime then Real.log k else 0) - 1) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))
    (∀ M : ℕ, ∃ n ≥ M, 0 < E n) → (∀ M : ℕ, ∃ n ≥ M, E n ≤ 0) →
    ∀ M : ℕ, ∃ n ≥ M, -4 < E n ∧ E n ≤ 0 := by
  dsimp only
  simpa only [zero_mul, zero_sub] using
    discrete_crossing (fun k : ℕ ↦ if k.Prime then Real.log k else 0) (fun k ↦ by
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
      · exact le_rfl) (c := 0) le_rfl

theorem first_prime_composite_crossing :
    let E := fun n : ℕ ↦ ∑ k ∈ Icc 1 n, ((if k.Prime then Real.log k else 0) - 1) *
      (2 - Real.cos (Real.log k) - Real.cos (Real.sqrt 2 * Real.log k))
    (∀ M : ℕ, ∃ n ≥ M, 0 < E n) → (∀ M : ℕ, ∃ n ≥ M, E n ≤ 0) →
    ∀ M : ℕ, ∃ n ≥ M, 2 ≤ n ∧ ¬ n.Prime ∧ -4 < E n ∧ E n ≤ 0 := by
  let a (k : ℕ) := if k.Prime then Real.log k else 0
  let E (n : ℕ) := ∑ k ∈ Icc 1 n, (a k - 1) * w (Real.log k)
  intro _ hp hn M
  obtain ⟨k, hk, he, he'⟩ := downward_passage (u := E) (hp (max M 2)) hn
  have ha (l : ℕ) : 0 ≤ a l := by
    dsimp only [a]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_rfl
  have hstep : E (k+1) = E k + (a (k+1) - 1) * w (Real.log (k+1 : ℕ)) :=
    sum_Icc_succ_top (by omega : 1 ≤ k + 1) _
  refine ⟨k+1, by omega, by omega, ?_, by linarith [discrete_step a ha k], he'⟩
  intro hprime
  have h3 : (3:ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 3 ≤ k+1 by omega)
  have hlog : 1 ≤ Real.log (k+1 : ℕ) := (Real.le_log_iff_exp_le (by positivity)).2
    (Real.exp_one_lt_three.le.trans h3)
  rw [show a (k+1) = Real.log (k+1 : ℕ) by simp [a, hprime]] at hstep
  linarith [mul_nonneg (sub_nonneg.mpr hlog) (w_bounds (Real.log (k+1 : ℕ))).1]

#print axioms first_prime_composite_crossing
#print axioms first_prime_discrete_crossing
#print axioms discrete_crossing
#print axioms integral_crossing
#print axioms first_prime_integral_crossing

end TwoCosineCrossings
