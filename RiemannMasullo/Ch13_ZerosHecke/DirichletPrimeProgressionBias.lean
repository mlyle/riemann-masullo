module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletOneSidedPrimeError
public import RiemannMasullo.Ch13_ZerosHecke.ProgressionPrimePowerTails

/-!
# Square-root fluctuations in the identity progression

Combine the density of prime squares with negative excursions of the centered
von Mangoldt count. This gives an explicit modulus-dependent coefficient for
ordinary primes in the rational test for Theorem 12.5.1.1, pp. 519–520.
-/

open Nat Finset Filter ArithmeticFunction
open scoped Topology

public noncomputable section

namespace RiemannMasullo

private theorem progressionBias_prime_error_eq_layer (q : ℕ) (x : ℝ) :
    dirichletSplitPrimeError q x = progressionPrimePowerLayer (1 : ZMod q) 1 x - x / q.totient := by
  unfold dirichletSplitPrimeError progressionPrimePowerLayer
  simp only [pow_one, ← Finset.sum_filter, Nat.primesLE_eq_filter_Icc_one, Finset.filter_filter]

/-- At arbitrarily large integers the prime error in the identity class lies below
−c√n for every c strictly smaller than the density of unit square roots of one. -/
theorem dirichletSplitPrimeError_frequently_lt_neg_root_density (q : ℕ) [NeZero q] {c : ℝ}
    (hc : c < ((residueClassUnitPowerRoots (1 : ZMod q) 2).card : ℝ) / q.totient) :
    ∃ᶠ n : ℕ in atTop, dirichletSplitPrimeError q n < -(c * Real.sqrt n) := by
  have hlim := (vonMangoldt_residueClass_sub_prime_sum_sqrt_limit (1 : ZMod q)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hchar := hlim.eventually (lt_mem_nhds hc)
  have hneg := dirichletResidueClassPsiError_frequently_lt_neg_rpow q (b := 0) (by norm_num) 0
  refine ((hneg.and_eventually hchar).and_eventually (eventually_ge_atTop (1 : ℕ))).mono ?_
  rintro n ⟨⟨hN, hD⟩, hn⟩
  simp only [Function.comp_apply] at hD
  simp only [dirichletResidueClassPsiError, zero_mul, neg_zero] at hN
  have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have h := (lt_div_iff₀ hp).mp hD
  rw [progressionBias_prime_error_eq_layer]
  linarith

/-- Modulo eight, the prime error in the identity class falls below −c√n
arbitrarily far out for every c < 1. -/
theorem dirichletSplitPrimeError_eight_frequently_lt_neg_sqrt {c : ℝ} (hc : c < 1) :
    ∃ᶠ n : ℕ in atTop, dirichletSplitPrimeError 8 n < -(c * Real.sqrt n) := by
  apply dirichletSplitPrimeError_frequently_lt_neg_root_density
  rw [residueClassUnitPowerRoots_one_mod_eight_sq_card, show Nat.totient 8 = 4 by decide]
  norm_num
  exact hc

end RiemannMasullo
