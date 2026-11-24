module

public import Mathlib.NumberTheory.LSeries.WeakPNT
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Weighted prime powers in a residue class

For a residue class a modulo q, consider the von Mangoldt sum with all prime powers of
exponent less than k removed. The first remaining exponent j for which a has a unit
j-th root gives its exact leading term: the number of such roots times x^(1/j) / φ(q).
Primes dividing the modulus contribute only a bounded weight at each fixed exponent.
The same first exponent determines convergence of the weighted square integral.

These results compute the contribution of higher powers to the rational prime
measurements for Theorem 12.5.1.1, pp. 519–520.
-/

open Nat Finset Filter ArithmeticFunction MeasureTheory Asymptotics
open scoped Topology

public noncomputable section
namespace RiemannMasullo

/-- The log-weighted sum over prime powers pʲ ≤ x with j ≥ k and pʲ congruent to a.
The prime-power interpretation uses k ≥ 1. -/
@[expose] def progressionPrimePowerTail {q : ℕ} (a : ZMod q) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ primesLE ⌊x⌋₊, ∑ j ∈ Finset.Icc k (p.log ⌊x⌋₊),
    if (p : ZMod q) ^ j = a then Real.log p else 0

/-- The sum of log p over primes p ≤ y whose k-th power is congruent to a.
The argument y bounds the prime base. -/
@[expose] def progressionPrimePowerLayer {q : ℕ} (a : ZMod q) (k : ℕ) (y : ℝ) : ℝ :=
  ∑ p ∈ primesLE ⌊y⌋₊, if (p : ZMod q) ^ k = a then Real.log p else 0

/-- The units modulo q whose k-th power equals the specified class. -/
@[expose] def residueClassUnitPowerRoots {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ) : Finset (ZMod q) :=
  Finset.univ.filter fun b ↦ b ^ k = a ∧ IsUnit b

/-- At exponent one the tail is exactly the von Mangoldt sum in the progression. -/
theorem progressionPrimePowerTail_one {q : ℕ} (a : ZMod q) (x : ℝ) :
    progressionPrimePowerTail a 1 x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n := by
  let N := ⌊x⌋₊
  let v := vonMangoldt.residueClass a
  let U := ((Finset.Icc 1 N).filter Nat.Prime).biUnion fun p ↦ image (p ^ ·) (Finset.Icc 1 (p.log N))
  have hu : U ⊆ Finset.Icc 1 N := by
    intro n hn
    simp only [U, mem_biUnion, mem_filter, mem_Icc, mem_image] at hn
    obtain ⟨p, ⟨_, hp⟩, j, ⟨hj, hj'⟩, rfl⟩ := hn
    exact mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, pow_le_of_le_log (by omega) hj'⟩
  have hv (n : ℕ) (hn : n ∈ Finset.Icc 1 N) (hu' : n ∉ U) : v n = 0 := by
    have hpp : ¬ IsPrimePow n := by
      intro h
      obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp h
      have hn' := mem_Icc.mp hn
      have hpn := (Nat.le_of_dvd (by omega : 0 < p ^ j) (dvd_pow_self p hj.ne')).trans hn'.2
      apply hu'
      apply mem_biUnion.mpr
      refine ⟨p, mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.one_le, hpn⟩, hp⟩, mem_image.mpr ?_⟩
      exact ⟨j, mem_Icc.mpr ⟨hj, Nat.le_log_of_pow_le hp.one_lt hn'.2⟩, rfl⟩
    simp [v, vonMangoldt.residueClass, Set.indicator_apply, vonMangoldt_eq_zero_iff.mpr hpp]
  rw [← Finset.sum_subset hu hv]
  dsimp only [U]
  rw [Finset.sum_biUnion (by rw [pairwiseDisjoint_iff]; grind [Nat.Prime.pow_inj'])]
  unfold progressionPrimePowerTail
  apply Finset.sum_congr (primesLE_eq_filter_Icc_one N)
  intro p hp
  rw [Finset.sum_image (by exact fun i _ j _ h ↦ Nat.pow_right_injective (Finset.mem_filter.mp hp).2.two_le h)]
  apply Finset.sum_congr rfl
  intro j hj
  simp [v, vonMangoldt.residueClass, Set.indicator_apply, vonMangoldt_apply_pow
    (by have := (Finset.mem_Icc.mp hj).1; omega : j ≠ 0), vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]

private theorem progressionPower_prime_cutoff {x : ℝ} (hx : 1 ≤ x) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    k ≤ p.log ⌊x⌋₊ ↔ p ≤ ⌊x ^ ((k : ℝ)⁻¹)⌋₊ := by
  have hx₀ := zero_le_one.trans hx
  rw [Nat.le_log_iff_pow_le hp.one_lt (by have := (Nat.one_le_floor_iff _).mpr hx; omega),
    Nat.le_floor_iff hx₀, Nat.le_floor_iff (Real.rpow_nonneg hx₀ _),
    Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) hx₀ (by exact_mod_cast hk),
    Real.rpow_natCast, Nat.cast_pow]

/-- Peeling off the first exponent leaves the next tail and the primes up to the corresponding root of x. -/
theorem progressionPrimePowerTail_eq_layer_add {q : ℕ} (a : ZMod q) {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 1 ≤ x) :
    progressionPrimePowerTail a k x = progressionPrimePowerLayer a k (x ^ ((k : ℝ)⁻¹)) + progressionPrimePowerTail a (k + 1) x := by
  let N := ⌊x⌋₊
  let M := ⌊x ^ ((k : ℝ)⁻¹)⌋₊
  let w (p j : ℕ) := if (p : ZMod q) ^ j = a then Real.log p else 0
  have hex : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  have hMN : M ≤ N := Nat.floor_mono (by simpa using Real.rpow_le_rpow_of_exponent_le hx hex)
  have hsingle : progressionPrimePowerLayer a k (x ^ ((k : ℝ)⁻¹)) = ∑ p ∈ primesLE N, if k ≤ p.log N then w p k else 0 := by
    unfold progressionPrimePowerLayer
    have hset : primesLE M = (primesLE N).filter (fun p ↦ k ≤ p.log N) := by
      ext p
      simp only [mem_primesLE, mem_filter]
      constructor
      · rintro ⟨h, hp⟩
        exact ⟨⟨h.trans hMN, hp⟩, (progressionPower_prime_cutoff hx hp hk).mpr h⟩
      · rintro ⟨⟨_, hp⟩, h⟩
        exact ⟨(progressionPower_prime_cutoff hx hp hk).mp h, hp⟩
    change (∑ p ∈ primesLE M, w p k) = _
    rw [hset, sum_filter]
  rw [hsingle, progressionPrimePowerTail, progressionPrimePowerTail, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  change (∑ j ∈ Finset.Icc k (p.log N), w p j) =
    (if k ≤ p.log N then w p k else 0) + ∑ j ∈ Finset.Icc (k + 1) (p.log N), w p j
  by_cases h : k ≤ p.log N
  · rw [ite_eq_left h, Finset.Icc_add_one_left_eq_Ioc]
    exact (Finset.add_sum_Ioc_eq_sum_Icc h).symm
  · have h' : p.log N < k := lt_of_not_ge h
    simp [Finset.Icc_eq_empty_of_lt h', Finset.Icc_eq_empty_of_lt (by omega : p.log N < k + 1), h]

private theorem progressionPower_tail_nonneg {q : ℕ} (a : ZMod q) (k : ℕ) (x : ℝ) : 0 ≤ progressionPrimePowerTail a k x := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE hp).one_le)
  · exact le_rfl

/-- A uniform bound for the remaining powers, independent of the modulus and the residue class. -/
theorem progressionPrimePowerTail_le {q : ℕ} (a : ZMod q) {k : ℕ} (hk : 0 < k) {x : ℝ} (hx : 1 ≤ x) :
    progressionPrimePowerTail a k x ≤ x ^ ((k : ℝ)⁻¹) * Real.log x := by
  let N := ⌊x⌋₊
  let M := ⌊x ^ ((k : ℝ)⁻¹)⌋₊
  have hx₀ := zero_le_one.trans hx
  have hN : N ≠ 0 := Nat.ne_of_gt ((Nat.one_le_floor_iff _).mpr hx)
  let S := (primesLE N).filter (fun p ↦ p ≤ M)
  have hrow (p : ℕ) (hp : p ∈ primesLE N) :
      (∑ j ∈ Finset.Icc k (p.log N), if (p : ZMod q) ^ j = a then Real.log p else 0) ≤
        if p ≤ M then Real.log x else 0 := by
    have hp' := prime_of_mem_primesLE hp
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_le)
    by_cases h : p ≤ M
    · rw [ite_eq_left h]
      have hcnt : (Finset.Icc k (p.log N)).card ≤ p.log N := by rw [Nat.card_Icc]; omega
      have hpow : (p : ℝ) ^ (p.log N) ≤ x := by
        exact le_trans (by exact_mod_cast Nat.pow_log_le_self p hN) (Nat.floor_le hx₀)
      calc _ ≤ ∑ j ∈ Finset.Icc k (p.log N), Real.log p := Finset.sum_le_sum
                  fun j _ ↦ by split_ifs <;> first | exact hlog | exact le_rfl
           _ = ((Finset.Icc k (p.log N)).card : ℝ) * Real.log p := by simp
           _ ≤ (p.log N : ℝ) * Real.log p := mul_le_mul_of_nonneg_right (by exact_mod_cast hcnt) hlog
           _ ≤ Real.log x := by
             rw [← Real.log_pow]
             exact Real.log_le_log (pow_pos (by exact_mod_cast hp'.pos) _) hpow
    · have hlt : p.log N < k := lt_of_not_ge fun h' ↦ h ((progressionPower_prime_cutoff hx hp' hk).mp h')
      simp [Finset.Icc_eq_empty_of_lt hlt, h]
  have hsub : S ⊆ Finset.Icc 1 M := by
    intro p hp
    obtain ⟨hp, hm⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨(prime_of_mem_primesLE hp).one_le, hm⟩
  have hc : S.card ≤ M := by simpa using Finset.card_le_card hsub
  apply (Finset.sum_le_sum hrow).trans
  rw [← Finset.sum_filter]
  change (∑ p ∈ S, Real.log x) ≤ _
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right ((by exact_mod_cast hc : (S.card : ℝ) ≤ M).trans
    (Nat.floor_le (Real.rpow_nonneg hx₀ _))) (Real.log_nonneg hx)

private theorem progressionPower_class_prime_limit {q : ℕ} [NeZero q] (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ progressionPrimePowerLayer a 1 x / x) atTop (𝓝 (if IsUnit a then (q.totient : ℝ)⁻¹ else 0)) := by
  by_cases ha : IsUnit a
  · rw [ite_eq_left ha]
    have hc := (ZMod.isUnit_iff_coprime a.val q).mp (by simpa only [ZMod.natCast_zmod_val] using ha)
    apply (Chebyshev.tendsto_sum_log_prime_modEq_div_atTop hc).congr
    intro x
    unfold progressionPrimePowerLayer
    rw [Nat.primesLE_eq_filter_Icc_one, ← Finset.Icc_add_one_left_eq_Ioc]
    simp only [Finset.sum_filter, pow_one, zero_add, ite_and]
    apply congrArg (·/x)
    apply Finset.sum_congr rfl
    intro n _
    have he : n ≡ a.val [MOD q] ↔ (n : ZMod q) = a := by
      simpa only [ZMod.natCast_zmod_val] using (ZMod.natCast_eq_natCast_iff n a.val q).symm
    by_cases h : n.Prime <;> simp [h, he]
  · rw [ite_eq_right ha]
    let C := ∑ p ∈ q.primeFactors, Real.log p
    have hpos (x : ℝ) : 0 ≤ progressionPrimePowerLayer a 1 x := Finset.sum_nonneg fun p hp ↦ by
      split_ifs <;> first | exact Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE hp).one_le) | exact le_rfl
    have hbound (x : ℝ) : progressionPrimePowerLayer a 1 x ≤ C := by
      unfold progressionPrimePowerLayer
      simp only [pow_one, ← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, e⟩ := Finset.mem_filter.mp hp
        have hpr := Nat.prime_of_mem_primesLE hp
        apply Nat.mem_primeFactors.mpr
        refine ⟨hpr, ?_, NeZero.ne q⟩
        by_contra h
        exact ha (e ▸ (ZMod.isUnit_iff_coprime p q).mpr (hpr.coprime_iff_not_dvd.mpr h))
      · intro p hp _
        exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
    apply squeeze_zero' (g := fun x : ℝ ↦ C / x)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact div_nonneg (hpos x) (zero_le_one.trans hx)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact div_le_div_of_nonneg_right (hbound x) (zero_le_one.trans hx)
    · exact tendsto_const_nhds.div_atTop tendsto_id

/-- The prime density of a fixed exponent is the number of unit roots divided by the totient. -/
theorem progressionPrimePowerLayer_density {q : ℕ} [NeZero q] (a : ZMod q) (k : ℕ) :
    Tendsto (fun x : ℝ ↦ progressionPrimePowerLayer a k x / x) atTop (𝓝 (((residueClassUnitPowerRoots a k).card : ℝ) / q.totient)) := by
  let U := Finset.univ.filter fun b : ZMod q ↦ b ^ k = a
  have H := tendsto_finsetSum U (fun b _ ↦ progressionPower_class_prime_limit b)
  have hsum : (∑ b ∈ U, if IsUnit b then (q.totient : ℝ)⁻¹ else 0) =
      ((residueClassUnitPowerRoots a k).card : ℝ) / q.totient := by
    simp only [U, ← Finset.sum_filter, Finset.filter_filter, residueClassUnitPowerRoots, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hsum] at H
  apply H.congr
  intro x
  rw [← Finset.sum_div]
  apply congrArg (·/x)
  simp only [progressionPrimePowerLayer, Finset.sum_comm (s := U), pow_one]
  apply Finset.sum_congr rfl
  intro p _
  simp [U, eq_comm]

/-- The progression sum is the sum of its first k prime-power layers and the exact tail. -/
theorem vonMangoldt_residueClass_eq_layers_add_tail {q : ℕ} (a : ZMod q) (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n) =
      (∑ j ∈ Finset.Icc 1 k, progressionPrimePowerLayer a j (x ^ ((j : ℝ)⁻¹))) + progressionPrimePowerTail a (k + 1) x := by
  induction k with
  | zero => simpa using (progressionPrimePowerTail_one a x).symm
  | succ k ih =>
    rw [ih, progressionPrimePowerTail_eq_layer_add a (Nat.succ_pos k) hx, Finset.sum_Icc_succ_top (Nat.succ_pos k), add_assoc]

/-- At scale x^(1/k), the progression tail has leading coefficient equal to the unit root density. -/
theorem progressionPrimePowerTail_density {q : ℕ} [NeZero q] (a : ZMod q) {k : ℕ} (hk : 0 < k) :
    Tendsto (fun x : ℝ ↦ progressionPrimePowerTail a k x / x ^ ((k : ℝ)⁻¹)) atTop (𝓝 (((residueClassUnitPowerRoots a k).card : ℝ) / q.totient)) := by
  let r := (k : ℝ)⁻¹
  let u := ((k + 1 : ℕ) : ℝ)⁻¹
  have hr : 0 < r := inv_pos.mpr (by exact_mod_cast hk)
  have hu : u < r := inv_lt_inv₀ (by positivity) (by exact_mod_cast hk) |>.mpr (by exact_mod_cast Nat.lt_succ_self k)
  have hs : Tendsto (fun x : ℝ ↦ progressionPrimePowerTail a (k + 1) x / x ^ r) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℝ ↦ Real.log x / x ^ (r - u))
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      exact div_nonneg (progressionPower_tail_nonneg ..) (Real.rpow_nonneg (zero_le_one.trans hx) _)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx₀ := zero_lt_one.trans_le hx
      apply (div_le_div_of_nonneg_right (progressionPrimePowerTail_le a (Nat.succ_pos k) hx) (Real.rpow_nonneg hx₀.le _)).trans_eq
      change x ^ u * Real.log x / x ^ r = _
      rw [Real.rpow_sub hx₀, div_div_eq_mul_div]
      ring
    · exact (isLittleO_log_rpow_atTop (sub_pos.mpr hu)).tendsto_div_nhds_zero
  have hh := ((progressionPrimePowerLayer_density a k).comp (tendsto_rpow_atTop hr)).add hs
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [progressionPrimePowerTail_eq_layer_add a hk hx, add_div]
  rfl

private theorem progressionPower_layer_bound_of_no_roots {q : ℕ} [NeZero q] {a : ZMod q} {k : ℕ} (he : residueClassUnitPowerRoots a k = ∅) (x : ℝ) :
    progressionPrimePowerLayer a k x ≤ ∑ p ∈ q.primeFactors, Real.log p := by
  unfold progressionPrimePowerLayer
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpow⟩ := Finset.mem_filter.mp hp
    have hpr := prime_of_mem_primesLE hp
    apply Nat.mem_primeFactors.mpr
    refine ⟨hpr, ?_, NeZero.ne q⟩
    by_contra h
    have hunit := (ZMod.isUnit_iff_coprime p q).mpr (hpr.coprime_iff_not_dvd.mpr h)
    have hx : (p : ZMod q) ∈ residueClassUnitPowerRoots a k := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpow, hunit⟩
    simp [he] at hx
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)

/-- Skipped exponents with no unit roots do not affect the leading term at the first occupied exponent. -/
theorem progressionPrimePowerTail_first_nonempty_density {q : ℕ} [NeZero q] (a : ZMod q) {k j : ℕ} (hk : 0 < k) (hkj : k ≤ j)
    (habs : ∀ i, k ≤ i → i < j → residueClassUnitPowerRoots a i = ∅) :
    Tendsto (fun x : ℝ ↦ progressionPrimePowerTail a k x / x ^ ((j : ℝ)⁻¹)) atTop (𝓝 (((residueClassUnitPowerRoots a j).card : ℝ) / q.totient)) := by
  induction hkj using Nat.decreasingInduction with
  | self => exact progressionPrimePowerTail_density a hk
  | of_succ i hij ih =>
    have hI := ih (by omega) (fun n hn h ↦ habs n (by omega) h)
    have hs : Tendsto (fun x : ℝ ↦ progressionPrimePowerLayer a i (x ^ ((i : ℝ)⁻¹)) / x ^ ((j : ℝ)⁻¹)) atTop (𝓝 0) := by
      let C := ∑ p ∈ q.primeFactors, Real.log p
      apply squeeze_zero' (g := fun x : ℝ ↦ C / x ^ ((j : ℝ)⁻¹))
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        apply div_nonneg _ (Real.rpow_nonneg (zero_le_one.trans hx) _)
        apply Finset.sum_nonneg
        intro p hp
        split_ifs <;> first | exact le_rfl | exact Real.log_nonneg (by exact_mod_cast (prime_of_mem_primesLE hp).one_le)
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
        exact div_le_div_of_nonneg_right (progressionPower_layer_bound_of_no_roots (habs i le_rfl (by omega)) _) (Real.rpow_nonneg (zero_le_one.trans hx) _)
      · exact tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (inv_pos.mpr (by exact_mod_cast (show 0 < j by omega))))
    have hh := hs.add hI
    rw [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [progressionPrimePowerTail_eq_layer_add a hk hx, add_div]

private theorem progressionPower_tail_measurable {q : ℕ} (a : ZMod q) (k : ℕ) : Measurable (progressionPrimePowerTail a k) :=
  (measurable_of_countable (fun N : ℕ ↦ ∑ p ∈ primesLE N, ∑ j ∈ Finset.Icc k (p.log N),
    if (p : ZMod q) ^ j = a then Real.log p else 0)).comp measurable_id.nat_floor

/-- When j is the first exponent at least k with a unit root, the weighted square integral
converges exactly for b > 1/j and diverges at equality. -/
theorem progressionPrimePowerTail_square_integrable_iff {q : ℕ} [NeZero q] (a : ZMod q) {k j : ℕ} (hk : 0 < k) (hkj : k ≤ j)
    (habs : ∀ i, k ≤ i → i < j → residueClassUnitPowerRoots a i = ∅) (hp : (residueClassUnitPowerRoots a j).Nonempty) (b : ℝ) :
    IntegrableOn (fun x : ℝ ↦ (progressionPrimePowerTail a k x) ^ 2 * x ^ (-2 * b - 1)) (Set.Ioi 1) ↔ (j : ℝ)⁻¹ < b := by
  let r := (j : ℝ)⁻¹
  let e := -2 * b - 1
  let F (x : ℝ) := (progressionPrimePowerTail a k x) ^ 2 * x ^ e
  let G (x : ℝ) := x ^ (2 * r + e)
  let c := ((residueClassUnitPowerRoots a j).card : ℝ) / q.totient
  have hc : 0 < c := div_pos (by exact_mod_cast Finset.card_pos.mpr hp)
    (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q))
  have hlim : Tendsto (fun x : ℝ ↦ F x / G x) atTop (𝓝 (c ^ 2)) := by
    apply ((progressionPrimePowerTail_first_nonempty_density a hk hkj habs).pow 2).congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx₀ := zero_lt_one.trans_le hx
    change (progressionPrimePowerTail a k x / x ^ r) ^ 2 = (progressionPrimePowerTail a k x) ^ 2 * x ^ e / x ^ (2 * r + e)
    rw [Real.rpow_add hx₀, div_pow, show 2 * r = r * (2 : ℕ) by push_cast; ring,
      Real.rpow_mul_natCast hx₀.le]
    field_simp [(Real.rpow_pos_of_pos hx₀ e).ne']
  have hθ : G =Θ[atTop] F := isTheta_of_div_tendsto_nhds_ne_zero hlim (pow_ne_zero _ hc.ne')
  have hF : Measurable F := by
    have := progressionPower_tail_measurable a k
    dsimp [F]; fun_prop
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hIF : IntegrableAtFilter F atTop ↔ IntegrableAtFilter G atTop :=
    ⟨hθ.1.integrableAtFilter hG.aestronglyMeasurable.stronglyMeasurableAtFilter,
     hθ.2.integrableAtFilter hF.aestronglyMeasurable.stronglyMeasurableAtFilter⟩
  have hEx : IntegrableAtFilter G atTop ↔ r < b := by
    change IntegrableAtFilter (fun x : ℝ ↦ x ^ (2 * r + e)) atTop volume ↔ _
    rw [integrableAtFilter_rpow_atTop_iff]
    change (2 * r + (-2 * b - 1) < -1) ↔ r < b
    constructor <;> intro h <;> linarith
  change IntegrableOn F (Set.Ioi 1) ↔ r < b
  rw [← hEx, ← hIF]
  refine ⟨fun h ↦ ⟨Set.Ioi 1, Ioi_mem_atTop _, h⟩, ?_⟩
  intro h
  obtain ⟨B, hB⟩ := integrableAtFilter_atTop_iff.mp h
  let R := max 1 B
  have hR : 1 ≤ R := le_max_left ..
  let K (x : ℝ) := (x ^ ((k : ℝ)⁻¹) * Real.log x) ^ 2 * x ^ e
  have hK : ContinuousOn K (Set.Icc 1 R) := by
    intro x hx
    have hx' : 0 < x := zero_lt_one.trans_le hx.1
    have hk' : ContinuousAt (fun t : ℝ ↦ t ^ ((k : ℝ)⁻¹)) x := continuousAt_id.rpow_const (.inl hx'.ne')
    have he' : ContinuousAt (fun t : ℝ ↦ t ^ e) x := continuousAt_id.rpow_const (.inl hx'.ne')
    exact ((hk'.mul (Real.continuousAt_log hx'.ne')).pow 2 |>.mul he').continuousWithinAt
  have hKI : IntegrableOn K (Set.Ioc 1 R) := (hK.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hFI : IntegrableOn F (Set.Ioc 1 R) := by
    apply hKI.mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (measurableSet_Ioc (a := 1) (b := R))] with x hx
    have hx' : 1 < x := hx.1
    have hn := Real.rpow_nonneg (zero_lt_one.trans hx').le e
    change ‖(progressionPrimePowerTail a k x) ^ 2 * x ^ e‖ ≤ (x ^ ((k : ℝ)⁻¹) * Real.log x) ^ 2 * x ^ e
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hn)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (progressionPower_tail_nonneg a k x) (progressionPrimePowerTail_le a hk hx'.le) 2) hn
  rw [← Set.Ioc_union_Ioi_eq_Ioi hR]
  exact hFI.union (hB.mono_set (fun _ hx ↦ (le_max_right (1 : ℝ) B).trans (Set.mem_Ioi.mp hx).le))

private theorem progressionPower_higher_eq {q : ℕ} (a : ZMod q) {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n) - progressionPrimePowerLayer a 1 x = progressionPrimePowerTail a 2 x := by
  have h := vonMangoldt_residueClass_eq_layers_add_tail a 1 hx
  simpa using sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n) = progressionPrimePowerTail a 2 x + progressionPrimePowerLayer a 1 x)

/-- The difference between the von Mangoldt and ordinary prime counts, divided by √x, tends
to the number of unit square roots of the class divided by the totient. -/
theorem vonMangoldt_residueClass_sub_prime_sum_sqrt_limit {q : ℕ} [NeZero q] (a : ZMod q) :
    Tendsto (fun x : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n) - progressionPrimePowerLayer a 1 x) / Real.sqrt x)
      atTop (𝓝 (((residueClassUnitPowerRoots a 2).card : ℝ) / q.totient)) := by
  apply (progressionPrimePowerTail_density a (k := 2) (by decide)).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simp only [progressionPower_higher_eq a hx, Real.sqrt_eq_rpow, one_div, Nat.cast_ofNat]

/-- All four units modulo eight are square roots of one. -/
theorem residueClassUnitPowerRoots_one_mod_eight_sq_card : (residueClassUnitPowerRoots (1 : ZMod 8) 2).card = 4 := by decide

private theorem progressionPower_two_mod_three_roots : residueClassUnitPowerRoots (2 : ZMod 3) 2 = ∅ ∧ (residueClassUnitPowerRoots (2 : ZMod 3) 3).card = 1 := by decide

/-- For the class two modulo three, the excess of the prime-power count over the ordinary
prime count is asymptotic to one half of the cube root of x. -/
theorem vonMangoldt_residueClass_two_mod_three_sub_prime_sum_cubic_limit :
    Tendsto (fun x : ℝ ↦ ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass (2 : ZMod 3) n) -
      progressionPrimePowerLayer (2 : ZMod 3) 1 x) / x ^ ((3 : ℝ)⁻¹)) atTop (𝓝 (1 / 2)) := by
  have h := progressionPrimePowerTail_first_nonempty_density (2 : ZMod 3) (k := 2) (j := 3) (by decide) (by decide)
    (fun i hi hj ↦ by
      have hh : i = 2 := by omega
      exact hh ▸ progressionPower_two_mod_three_roots.1)
  rw [progressionPower_two_mod_three_roots.2] at h
  have ht : Nat.totient 3 = 2 := by decide
  rw [ht] at h
  apply (by simpa only [Nat.cast_one, Nat.cast_ofNat] using h :
    Tendsto (fun x : ℝ ↦ progressionPrimePowerTail (2 : ZMod 3) 2 x / x ^ ((3 : ℝ)⁻¹)) atTop (𝓝 (1 / 2))).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [progressionPower_higher_eq _ hx]

end RiemannMasullo
