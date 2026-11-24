module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletResidueClassZeros
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.AbelPartialSums
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Landau
import RiemannMasullo.External.HardyCriticalLine.CriticalLineZeroInfinitude
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.Chebyshev

/-!
# One-sided estimates for primes in the identity progression

An eventual lower bound −C nᵇ for the centered sum of log p over primes p ≡ 1 modulo q
excludes every zero of every Dirichlet L-function of modulus q strictly to the right of b,
away from the principal pole. A single sequence of such bounds on factorial moduli
would put every Dirichlet zero in the open critical strip on the critical line.
Conversely, prime squares in the same progression and a critical zero of zeta force the
centered prime count below −√n/φ(q) − C nᵇ infinitely often for every b < 1/2.

The lower bound makes a shifted series of centered partial sums nonnegative.
The identity-progression residues have one sign, so Landau's theorem forces convergence
throughout the required half-plane. This gives an arithmetic criterion for the rational
case of Theorem 12.5.1.1, pp. 519–520.
-/

open Set Function Complex Filter LSeries ArithmeticFunction DirichletCharacter MeasureTheory
open scoped Topology ComplexOrder

public noncomputable section
namespace RiemannMasullo

private theorem oneSidedPrime_term_shift (a : ℕ → ℂ) (d s : ℂ) (n : ℕ) :
    term (fun n ↦ a n * (n : ℂ) ^ d) s n = term a (s - d) n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [term_of_ne_zero hn, term_of_ne_zero hn]
  have hz : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_sub _ _ hz]
  have hd : (n : ℂ) ^ d ≠ 0 := (Complex.cpow_ne_zero_iff.mpr (.inl hz))
  field_simp

private theorem oneSidedPrime_LSeries_shift (a : ℕ → ℂ) (d s : ℂ) :
    LSeries (fun n ↦ a n * (n : ℂ) ^ d) s = LSeries a (s - d) := tsum_congr (oneSidedPrime_term_shift a d s)

private theorem oneSidedPrime_summable_shift (a : ℕ → ℂ) (d s : ℂ) :
    LSeriesSummable (fun n ↦ a n * (n : ℂ) ^ d) s ↔ LSeriesSummable a (s - d) := by
  exact summable_congr (oneSidedPrime_term_shift a d s)

private theorem oneSidedPrime_landau_extension {A : ℕ → ℝ} {C b : ℝ} (hb : 0 < b)
    (hl : ∀ n : ℕ, 0 ≤ A n + C * (n : ℝ) ^ b)
    (hS : ∀ s : ℂ, 2 < s.re → LSeriesSummable (fun n ↦ (A n : ℂ)) s)
    {Q : ℂ → ℂ} (hQ : MeromorphicOn Q {s | b < s.re})
    (hE : ∀ s : ℂ, 2 < s.re → s * LSeries (fun n ↦ (A n : ℂ)) (s + 1) = Q s)
    (hR : ∀ x : ℝ, b < x → ∃ c : ℂ, c.re ≤ 0 ∧
      Tendsto (fun t : ℝ ↦ ((t : ℂ) - x) * Q t) (𝓝[>] x) (𝓝 c)) (hb₁ : b < 1) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s | b < s.re} ∧ ∀ s : ℂ, 2 < s.re → H s = Q s := by
  let a (n : ℕ) : ℂ := A n
  let p (n : ℕ) := (1 : ℂ) * (n : ℂ) ^ (b : ℂ)
  let d := a + (C:ℂ) • p
  let f (n : ℕ) := d n * (n : ℂ) ^ (-1 : ℂ)
  let Z (s : ℂ) := (C:ℂ) * riemannZeta (s + 1 - b)
  have hZ : AnalyticOnNhd ℂ Z {s | b < s.re} := by
    intro s hs
    change b < s.re at hs
    have hn : s + 1 - b ≠ 1 := by
      intro e; have h := congrArg Complex.re e; simp at h; linarith
    exact analyticAt_const.mul ((analyticOn_riemannZeta (s + 1 - b) hn).comp (f := fun z : ℂ ↦ z + 1 - b)
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const))
  have hf : 0 ≤ f := by
    intro n
    apply mul_nonneg
    · change 0 ≤ (A n : ℂ) + (C:ℂ) * (1 * (n : ℂ) ^ (b : ℂ))
      rw [one_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
        ← Complex.ofReal_mul, ← Complex.ofReal_add]
      exact_mod_cast hl n
    · rw [Complex.cpow_neg, Complex.cpow_one]
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have sums (s : ℂ) (hs : 1 < s.re) : LSeriesSummable a (s + 1) ∧ LSeriesSummable p (s + 1) := by
    refine ⟨hS _ (by simp; linarith), ?_⟩
    apply (oneSidedPrime_summable_shift (1:ℕ → ℂ) _ _).mpr
    apply LSeriesSummable_one_iff.mpr
    simp; linarith
  have hd (s : ℂ) (hs : 1 < s.re) : LSeriesSummable d (s + 1) := (sums s hs).1.add ((sums s hs).2.smul C)
  have he (s : ℂ) (hs : 1 < s.re) : LSeries f s = LSeries a (s + 1) + Z s := by
    rw [show LSeries f s = LSeries d (s + 1) by simpa only [sub_neg_eq_add] using oneSidedPrime_LSeries_shift d (-1) s,
      show LSeries d (s + 1) = _ from LSeries_add (sums s hs).1 ((sums s hs).2.smul C),
      LSeries_smul, show LSeries p (s + 1) = _ from oneSidedPrime_LSeries_shift (1:ℕ → ℂ) b (s + 1),
      LSeries_one_eq_riemannZeta (by simp; linarith)]
  have hbound : abscissaOfAbsConv f ≤ (2 : ℝ) := by
    have ht : LSeriesSummable f 2 := (oneSidedPrime_summable_shift d (-1) 2).mpr (by convert hd 2 (by norm_num) using 1; norm_num)
    exact_mod_cast ht.abscissaOfAbsConv_le
  let F (s : ℂ) := Q s / s + Z s
  have hFM : MeromorphicOn F {s | b < s.re} := fun s hs ↦
    ((hQ s hs).div analyticAt_id.meromorphicAt).add (hZ s hs).meromorphicAt
  have hFE (s : ℂ) (hs : 2 < s.re) : F s = LSeries f s := by
    rw [he s (by linarith)]
    dsimp [F]; rw [← hE s hs]
    have hn : s ≠ 0 := fun e ↦ by norm_num [e] at hs
    rw [mul_div_cancel_left₀ _ hn]
  have hFR (x : ℝ) (hx : b < x) (_ : x ≤ 2) : ∃ c : ℂ, c.re ≤ 0 ∧
      Tendsto (fun t : ℝ ↦ ((t : ℂ) - x) * F t) (𝓝[>] x) (𝓝 c) := by
    obtain ⟨c, hc, hl⟩ := hR x hx
    have ht : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝 (x : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hx₀ := hb.trans hx
    refine ⟨c / (x : ℂ), ?_, ?_⟩
    · rw [Complex.div_ofReal_re]
      exact div_nonpos_of_nonpos_of_nonneg hc hx₀.le
    · have hv := (hl.div ht (Complex.ofReal_ne_zero.mpr hx₀.ne')).add
        ((ht.sub_const (x : ℂ)).mul ((hZ x hx).continuousAt.tendsto.comp ht))
      simp only [sub_self, zero_mul, add_zero] at hv
      apply hv.congr
      intro t
      dsimp [F]
      ring
  have hab := LSeries_abscissa_le_of_nonpositive_limits hf hbound hFM hFE hFR
  let H (s : ℂ) := s * (LSeries f s - Z s)
  have hH : AnalyticOnNhd ℂ H {s | b < s.re} := by
    intro s hs
    change b < s.re at hs
    exact analyticAt_id.mul ((LSeries_analyticOnNhd f _ (hab.trans_lt (by exact_mod_cast hs))).sub (hZ _ hs))
  refine ⟨H, hH, fun s hs ↦ ?_⟩
  dsimp only [H]
  rw [he s (by linarith), add_sub_cancel_right]
  exact hE s hs

private theorem oneSidedPrime_psi_difference {q : ℕ} (a : ZMod q) (n : ℕ) :
    dirichletResidueClassPsiError a (n + 1:ℕ) - dirichletResidueClassPsiError a n =
      vonMangoldt.residueClass a (n + 1) - (q.totient : ℝ)⁻¹ := by
  simp only [dirichletResidueClassPsiError, Nat.floor_natCast, Finset.sum_Icc_succ_top (Nat.succ_pos n)]
  push_cast
  ring

private theorem oneSidedPrime_psi_bound {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |dirichletResidueClassPsiError a n| ≤ C * n := by
  let k := Real.log 4 + 4
  let d := (q.totient : ℝ)⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨k + d, add_nonneg hk hd, fun n ↦ ?_⟩
  let S := ∑ j ∈ Finset.Icc 1 n, vonMangoldt.residueClass a j
  have hpos : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ vonMangoldt.residueClass_nonneg _ j
  have hle : S ≤ k * n := by
    apply (Finset.sum_le_sum fun j (_ : j ∈ Finset.Icc 1 n) ↦ vonMangoldt.residueClass_le a j).trans
    simpa only [k, Chebyshev.psi, Nat.floor_natCast,← Finset.Icc_succ_left_eq_Ioc,
      Nat.succ_eq_add_one, zero_add, Order.succ_eq_add_one] using Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  have hrewrite : dirichletResidueClassPsiError a n = S - d * n := by
    simp only [dirichletResidueClassPsiError, Nat.floor_natCast, S, d, div_eq_mul_inv, mul_comm]
  rw [hrewrite, abs_le, add_mul]
  constructor <;> linarith [mul_nonneg hk (Nat.cast_nonneg (α:=ℝ) n), mul_nonneg hd (Nat.cast_nonneg (α:=ℝ) n)]

private theorem oneSidedPrime_prime_le_psi {q : ℕ} (n : ℕ) :
    dirichletSplitPrimeError q n ≤ dirichletResidueClassPsiError (1:ZMod q) n := by
  simp only [dirichletSplitPrimeError, dirichletResidueClassPsiError, Nat.floor_natCast, sub_le_sub_iff_right]
  let S := Finset.Icc 1 n
  let p (j:ℕ) := j.Prime ∧ (j:ZMod q) = 1
  let f := vonMangoldt.residueClass (1:ZMod q)
  change (∑ j ∈ S.filter p, Real.log j) ≤ ∑ j ∈ S, f j
  calc _ = ∑ j ∈ S.filter p, f j := by
           apply Finset.sum_congr rfl
           intro j hj
           obtain ⟨hp, hj'⟩ := (Finset.mem_filter.mp hj).2
           simp [f, vonMangoldt.residueClass, hj', vonMangoldt_apply_prime hp]
       _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ ↦
         vonMangoldt.residueClass_nonneg _ j)

private theorem oneSidedPrime_aux_meromorphic {q : ℕ} [NeZero q] (a : ZMod q) (z : ℂ) :
    MeromorphicAt (vonMangoldt.LFunctionResidueClassAux a) z := by
  classical
  have hn := ((differentiable_LFunctionTrivChar₁ q).analyticAt z).meromorphicAt
  apply MeromorphicAt.fun_mul (.const _ _)
  apply MeromorphicAt.fun_sub
  · exact hn.deriv.neg.div hn
  · apply MeromorphicAt.fun_sum
    intro χ hχ
    have hne : χ ≠ 1 := by simpa only [Finset.mem_compl, Finset.mem_singleton] using hχ
    have h := ((differentiable_LFunction hne).analyticAt z).meromorphicAt
    exact ((MeromorphicAt.const _ _).mul h.deriv).div h

private theorem oneSidedPrime_real_residue {q : ℕ} [NeZero q] (x : ℝ) : ∃ c : ℂ, c.re ≤ 0 ∧
    Tendsto (fun t : ℝ ↦ ((t : ℂ) - x) * vonMangoldt.LFunctionResidueClassAux (1:ZMod q) t)
      (𝓝[>] x) (𝓝 c) := by
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝 (x : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  by_cases hx : (x : ℂ) = 1
  · have h1 : x = 1 := by exact_mod_cast hx
    subst x
    have hD : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] 1) (𝓝[{s : ℂ | 1 ≤ s.re}] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using ht, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
      exact ht.le
    have hcont := (vonMangoldt.continuousOn_LFunctionResidueClassAux (1:ZMod q) 1 (show (1 : ℂ) ∈ {s : ℂ | 1 ≤ s.re} by simp)).tendsto.comp hD
    refine ⟨0, le_refl _,?_⟩
    simpa only [Complex.ofReal_one, Function.comp_apply, sub_self, zero_mul] using (ht.sub_const (1 : ℂ)).mul hcont
  · have hp : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝[≠] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨ht, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t (h : x < t)
      exact fun e ↦ h.ne' (Complex.ofReal_injective e)
    have hr := (dirichletResidueClass_residue (1:ZMod q) isUnit_one hx).comp hp
    simp only [ZMod.inv_one, map_one, one_mul,← Nat.cast_sum] at hr
    exact ⟨_, by simp [Complex.mul_re]; positivity, hr⟩

private theorem oneSidedPrime_aux_extension {q : ℕ} [NeZero q] {b C : ℝ} (hb : 0 < b) (hb₁ : b < 1)
    (hL : ∀ n : ℕ, -(C * (n : ℝ) ^ b) ≤ dirichletResidueClassPsiError (1:ZMod q) n) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s | b < s.re} ∧
      ∀ s : ℂ, 2 < s.re → H s = vonMangoldt.LFunctionResidueClassAux (1:ZMod q) s := by
  let A (n : ℕ) := dirichletResidueClassPsiError (1:ZMod q) n
  let d : ℂ := (q.totient : ℂ)⁻¹
  let v (n : ℕ) : ℂ := vonMangoldt.residueClass (1:ZMod q) n
  let u := v - d • (1:ℕ → ℂ)
  have hzero : (A 0 : ℂ) = 0 := by simp [A, dirichletResidueClassPsiError]
  have hincr (n : ℕ) : (A (n + 1) : ℂ) - A n = u (n + 1) := by
    simpa only [A, u, v, d, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_natCast] using
      congrArg Complex.ofReal (oneSidedPrime_psi_difference (1:ZMod q) n)
  obtain ⟨k, hk, hn⟩ := oneSidedPrime_psi_bound (1:ZMod q)
  have hbnd (n : ℕ) : ‖(A n : ℂ)‖ ≤ k * n := by simpa only [A, Complex.norm_real, Real.norm_eq_abs] using hn n
  obtain ⟨E, hE, hrel⟩ := LSeries_partialSums_analytic_correction hzero hincr ⟨k, hk, hbnd⟩
  let aux := vonMangoldt.LFunctionResidueClassAux (1:ZMod q)
  let G (s : ℂ) := E s - d * riemannZeta₀ s
  have hG : AnalyticOnNhd ℂ G {s | b < s.re} := fun s hs ↦ (hE _ (hb.trans hs)).sub
    (analyticAt_const.mul (differentiable_riemannZeta₀.analyticAt s))
  have hQ : MeromorphicOn (aux + G) {s | b < s.re} := fun s hs ↦
    (oneSidedPrime_aux_meromorphic (1:ZMod q) s).add (hG s hs).meromorphicAt
  have hr (s : ℂ) (hs : 2 < s.re) : s * LSeries (fun n ↦ (A n : ℂ)) (s + 1) = (aux + G) s := by
    have hs₁ : 1 < s.re := by linarith
    have hn₁ : s ≠ 1 := fun e ↦ by norm_num [e] at hs
    have hv : LSeriesSummable v s := LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1:ZMod q)).trans_lt (by exact_mod_cast hs₁))
    rw [hrel s hs, show LSeries u s = _ from LSeries_sub hv ((LSeriesSummable_one_iff.mpr hs₁).smul d),
      LSeries_smul, LSeries_one_eq_riemannZeta hs₁, riemannZeta_eq_inv_sub_add hn₁]
    change _ = vonMangoldt.LFunctionResidueClassAux (1:ZMod q) s + (E s - d * riemannZeta₀ s)
    rw [vonMangoldt.eqOn_LFunctionResidueClassAux isUnit_one hs₁]
    change LSeries v s - d * _ + _ = LSeries v s - d / _ + _
    ring
  have hR (x : ℝ) (hx : b < x) : ∃ c : ℂ, c.re ≤ 0 ∧
      Tendsto (fun t : ℝ ↦ ((t : ℂ) - x) * (aux + G) t) (𝓝[>] x) (𝓝 c) := by
    obtain ⟨c, hc, hr⟩ := oneSidedPrime_real_residue (q:=q) x
    have ht : Tendsto (fun t : ℝ ↦ (t : ℂ)) (𝓝[>] x) (𝓝 (x : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hh := hr.add ((ht.sub_const (x : ℂ)).mul ((hG x hx).continuousAt.tendsto.comp ht))
    refine ⟨c, hc,?_⟩
    simp only [sub_self, zero_mul, add_zero] at hh
    apply hh.congr
    intro t
    simp only [Pi.add_apply, mul_add, aux, Function.comp_apply]
  have hs (s : ℂ) (hs : 2 < s.re) : LSeriesSummable (fun n ↦ (A n : ℂ)) s := by
    apply LSeriesSummable_of_le_const_mul_rpow hs
    exact ⟨k, fun n _ ↦ by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hbnd n⟩
  have hpos (n : ℕ) : 0 ≤ A n + C * (n : ℝ) ^ b := by
    have he := hL n
    change -(C * (n : ℝ) ^ b) ≤ A n at he
    linarith
  obtain ⟨H, hH, hEq⟩ := oneSidedPrime_landau_extension hb hpos hs hQ hr hR hb₁
  refine ⟨H - G, fun s hs ↦ (hH _ hs).sub (hG _ hs), fun s hs ↦ ?_⟩
  simp only [Pi.sub_apply, hEq s hs, Pi.add_apply, add_sub_cancel_right, aux]

private theorem oneSidedPrime_lower_all {f : ℕ → ℝ} (h₀ : f 0 = 0) {b : ℝ} (hb : 0 < b)
    (h : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, -(C * (n : ℝ) ^ b) ≤ f n) :
    ∃ D : ℝ, ∀ n : ℕ, -(D * (n : ℝ) ^ b) ≤ f n := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  let S := ∑ k ∈ Finset.range N, |f k|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨|C|+S, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · apply le_trans _ (hN n hn)
    exact neg_le_neg (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · rcases n.eq_zero_or_pos with hzero | hp
    · simp [hzero, h₀, Real.zero_rpow hb.ne']
    · have hfn : |f n| ≤ S := Finset.single_le_sum (f := fun k ↦ |f k|) (fun k _ ↦ abs_nonneg (f k)) (Finset.mem_range.mpr (lt_of_not_ge hn))
      have hpow : 1 ≤ (n : ℝ) ^ b := Real.one_le_rpow (by exact_mod_cast hp) hb.le
      have hh := le_mul_of_one_le_right (add_nonneg (abs_nonneg C) hS) hpow
      linarith [neg_abs_le (f n), abs_nonneg C]

private theorem oneSidedPrime_psi_nonzero {q : ℕ} [NeZero q] {b : ℝ} (hb : 0 < b) (hb₁ : b < 1)
    (hL : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, -(C * (n : ℝ) ^ b) ≤ dirichletResidueClassPsiError (1:ZMod q) n)
    {ρ : ℂ} (hr : b < ρ.re) (hn : ρ ≠ 1) (χ : DirichletCharacter ℂ q) : χ.LFunction ρ ≠ 0 := by
  obtain ⟨C, hC⟩ := oneSidedPrime_lower_all (f := fun n : ℕ ↦ dirichletResidueClassPsiError (1:ZMod q) n)
    (by simp [dirichletResidueClassPsiError]) hb hL
  obtain ⟨H, hH, hEq⟩ := oneSidedPrime_aux_extension hb hb₁ hC
  apply dirichletLFunction_ne_zero_of_residueClass_extension hb₁ hH _ hr hn χ
  let U := {s : ℂ | 1 < s.re}
  let v (n : ℕ) : ℂ := vonMangoldt.residueClass (1:ZMod q) n
  let D (s : ℂ) := LSeries v s - (q.totient : ℂ)⁻¹ / (s - 1)
  have hD : AnalyticOnNhd ℂ D U := by
    intro s hs
    change 1 < s.re at hs
    have ha : AnalyticAt ℂ (LSeries v) s := LSeries_analyticOnNhd _ _
      ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one (1:ZMod q)).trans_lt (by exact_mod_cast hs))
    exact ha.sub (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr fun e ↦ by simp [e] at hs))
  have h₃ : (3 : ℂ) ∈ U := by change 1 < (3 : ℂ).re; norm_num
  have he : H =ᶠ[𝓝 (3 : ℂ)] D := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with z hz
    exact (hEq z hz).trans (vonMangoldt.eqOn_LFunctionResidueClassAux isUnit_one (by change (1 : ℝ) < z.re; linarith))
  have hh : AnalyticOnNhd ℂ H U := fun s hs ↦ hH s (hb₁.trans hs)
  intro s hs
  exact (hh.eqOn_of_preconnected_of_eventuallyEq hD (convex_halfSpace_re_gt 1).isPreconnected h₃ he hs).trans
    (vonMangoldt.eqOn_LFunctionResidueClassAux isUnit_one hs).symm

/-- An eventual one-sided lower estimate for primes congruent to one modulo q excludes
zeros of every Dirichlet character modulo q strictly to the right of b, away from one. -/
theorem dirichletLFunction_ne_zero_of_split_prime_lower_bound {q : ℕ} [NeZero q] {b : ℝ} (hb : 0 < b) (hb₁ : b < 1)
    (hL : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, -(C * (n : ℝ) ^ b) ≤ dirichletSplitPrimeError q n)
    {ρ : ℂ} (hr : b < ρ.re) (hn : ρ ≠ 1) (χ : DirichletCharacter ℂ q) : χ.LFunction ρ ≠ 0 := by
  obtain ⟨C, hC⟩ := hL
  apply oneSidedPrime_psi_nonzero hb hb₁ ⟨C,?_⟩ hr hn χ
  filter_upwards [hC] with n hn
  exact hn.trans (oneSidedPrime_prime_le_psi n)

/-- In every identity progression the centered von Mangoldt sum falls below −C nᵇ
at arbitrarily large integers, for every b < 1/2 and every real constant C. -/
theorem dirichletResidueClassPsiError_frequently_lt_neg_rpow (q : ℕ) [NeZero q] {b : ℝ} (hb : b < 1 / 2) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, dirichletResidueClassPsiError (1:ZMod q) n < -(C * (n : ℝ) ^ b) := by
  obtain ⟨t, ht⟩ := HardyCriticalLine.positiveHardyZeroHeights_infinite.nonempty
  let ρ := HardyCriticalLine.criticalLinePoint t
  have hr : ρ.re = 1 / 2 := by norm_num [ρ, HardyCriticalLine.criticalLinePoint]
  have hn : ρ ≠ 1 := fun e ↦ by norm_num [e] at hr
  have hz : riemannZeta ρ = 0 := (HardyCriticalLine.hardyFunctionReal_eq_zero_iff t).1 ht.2
  have hz' : (1:DirichletCharacter ℂ q).LFunction ρ = 0 := by
    change LFunctionTrivChar q ρ = 0
    rw [LFunctionTrivChar_eq_mul_riemannZeta hn, hz, mul_zero]
  let d : ℝ := max b (1 / 4)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (le_max_right ..)
  have hd' : d < 1 / 2 := max_lt hb (by norm_num)
  by_contra hf
  have hl : ∀ᶠ n : ℕ in atTop, -(C * (n : ℝ) ^ b) ≤ dirichletResidueClassPsiError (1:ZMod q) n := by
    simpa only [Filter.not_frequently, not_lt] using hf
  have hlow : ∀ᶠ n : ℕ in atTop, -(|C| *(n : ℝ) ^ d) ≤ dirichletResidueClassPsiError (1:ZMod q) n := by
    filter_upwards [hl, eventually_ge_atTop 1] with n h hn
    apply le_trans _ h
    exact neg_le_neg (mul_le_mul (le_abs_self C)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (le_max_left ..))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (abs_nonneg _))
  exact oneSidedPrime_psi_nonzero hd (by linarith) ⟨|C|, hlow⟩ (hr ▸ hd') hn 1 hz'

private theorem oneSidedPrime_squares_le_psi (q n m : ℕ) (hm : m ^ 2 ≤ n) :
    dirichletSplitPrimeError q n + (dirichletSplitPrimeError q m + (m : ℝ) / q.totient) ≤
      dirichletResidueClassPsiError (1:ZMod q) n := by
  classical
  let S (j:ℕ) := Finset.Icc 1 j
  let P (j:ℕ) := (S j).filter fun p : ℕ ↦ p.Prime ∧ (p:ZMod q) = 1
  let B := (P m).image (fun p : ℕ ↦ p ^ 2)
  let f := vonMangoldt.residueClass (1:ZMod q)
  have hu : P n ∪ B ⊆ S n := by
    intro k hk
    rcases Finset.mem_union.mp hk with hp | hb
    · exact (Finset.mem_filter.mp hp).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      exact Finset.mem_Icc.mpr ⟨by nlinarith, (Nat.pow_le_pow_left h₂ 2).trans hm⟩
  have hd : Disjoint (P n) B := by
    apply Finset.disjoint_left.mpr
    intro k hk hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp hk).2.1.prime.not_isSquare ⟨p, sq p⟩
  have hp (j : ℕ) (h : j ∈ P n) : f j = Real.log j := by
    obtain ⟨hp, hj⟩ := (Finset.mem_filter.mp h).2
    simp [f, vonMangoldt.residueClass, hj, vonMangoldt_apply_prime hp]
  have hsq : (∑ k ∈ B, f k) = ∑ p ∈ P m, Real.log p := by
    rw [Finset.sum_image (f := f) (by exact fun i _ j _ e ↦ Nat.pow_left_injective (by decide : 2 ≠ 0) e)]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hp', he⟩ := (Finset.mem_filter.mp hp).2
    simp [f, vonMangoldt.residueClass, he, vonMangoldt_apply_pow (by decide : 2 ≠ 0), vonMangoldt_apply_prime hp']
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hu
    (fun i _ _ ↦ vonMangoldt.residueClass_nonneg _ i)
  rw [Finset.sum_union hd, hsq, Finset.sum_congr rfl hp] at hh
  simp only [dirichletSplitPrimeError, dirichletResidueClassPsiError, Nat.floor_natCast, sub_add_cancel]
  change (∑ j ∈ P n, Real.log j) - _ + (∑ j ∈ P m, Real.log j) ≤ (∑ j ∈ S n, f j) - _
  linarith

/-- In every identity progression the centered prime count is below −√n/φ(q) − C nᵇ
at arbitrarily large integers, for every b < 1/2 and every real constant C. -/
theorem dirichletSplitPrimeError_frequently_lt_neg_sqrt_sub_rpow (q : ℕ) [NeZero q] {b : ℝ} (hb : b < 1 / 2) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, dirichletSplitPrimeError q n < -Real.sqrt n / q.totient - C * (n : ℝ) ^ b := by
  let c := (q.totient : ℝ)⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let d : ℝ := max b (1 / 4)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) (le_max_right ..)
  have hd' : d < 1 / 2 := max_lt hb (by norm_num)
  let T (n:ℕ) := dirichletSplitPrimeError q n
  by_contra hf
  have hh : ∀ᶠ n : ℕ in atTop, -Real.sqrt n / q.totient - C * (n : ℝ) ^ b ≤ T n := by
    simpa only [Filter.not_frequently, not_lt, T] using hf
  have hl : ∀ᶠ n : ℕ in atTop, -(|C| * (n : ℝ) ^ d) ≤ T n + c * Real.sqrt n := by
    filter_upwards [hh, eventually_ge_atTop 1] with n hn h1
    have h := mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1) (le_max_left b (1 / 4)))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_nonneg C)
    dsimp [c, d]
    rw [div_eq_mul_inv] at hn
    linarith
  obtain ⟨D, hD⟩ := oneSidedPrime_lower_all (f := fun n : ℕ ↦ T n + c * Real.sqrt n)
    (by simp [T, dirichletSplitPrimeError]) hd ⟨|C|, hl⟩
  have hB (n : ℕ) : -(|D| * (n : ℝ) ^ d) ≤ T n + c * Real.sqrt n :=
    (neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self D) (Real.rpow_nonneg (Nat.cast_nonneg n) _))).trans (hD n)
  have bad := dirichletResidueClassPsiError_frequently_lt_neg_rpow q hd' (2 * c + 2*|D|)
  apply bad
  filter_upwards [eventually_ge_atTop 1] with n hn
  let m := ⌊Real.sqrt n⌋₊
  have hn₀ := Nat.cast_nonneg (α:=ℝ) n
  have h1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hm : (m : ℝ) ≤ Real.sqrt n := Nat.floor_le (Real.sqrt_nonneg _)
  have hmf : Real.sqrt n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmn : (m : ℝ) ≤ n := hm.trans (Real.sqrt_le_self_iff.mpr (.inr h1))
  have hms : m ^ 2 ≤ n := by
    exact_mod_cast (pow_le_pow_left₀ (Nat.cast_nonneg m : 0 ≤ (m : ℝ)) hm 2).trans_eq (Real.sq_sqrt hn₀)
  have hcount := oneSidedPrime_squares_le_psi q n m hms
  change T n + (T m + (m : ℝ) / q.totient) ≤ _ at hcount
  rw [div_eq_mul_inv, mul_comm (m : ℝ)] at hcount
  have hquad : Real.sqrt (m : ℝ) ≤ (n : ℝ) ^ d := by
    calc Real.sqrt (m : ℝ) ≤ Real.sqrt (Real.sqrt (n : ℝ)) := Real.sqrt_le_sqrt hm
         _ = (n : ℝ) ^ (1 / 4 : ℝ) := by simp only [Real.sqrt_eq_rpow,← Real.rpow_mul hn₀]; norm_num
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h1 (le_max_right ..)
  have he₁ := mul_le_mul_of_nonneg_left hquad hc
  have he₂ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg m) hmn hd.le) (abs_nonneg D)
  have he₃ := mul_le_mul_of_nonneg_left (le_of_lt hmf) hc
  have he₄ := mul_le_mul_of_nonneg_left (Real.one_le_rpow h1 hd.le) hc
  change T n + (T m + c * (m : ℝ)) ≤ _ at hcount
  apply not_lt_of_ge
  linarith [hB n, hB m]

/-- One eventual lower bound at each of an unbounded sequence of factorial moduli excludes
zeros strictly right of the critical line for every Dirichlet character, away from one. -/
theorem dirichletLFunction_ne_zero_of_factorial_prime_lower_bound (hE : ∀ N : ℕ, ∃ n ≥ N, ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      -(C * (k : ℝ) ^ (1 / 2 + 1 / ((n : ℝ) + 3))) ≤ dirichletSplitPrimeError n.factorial k)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hr : 1 / 2 < ρ.re) (hn : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hr)
  obtain ⟨n, hN, he⟩ := hE (max q k)
  have hq : q ∣ n.factorial := Nat.dvd_factorial (NeZero.pos q) ((le_max_left q k).trans hN)
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast (le_max_right q k).trans hN
  let b : ℝ := 1 / 2 + 1 / ((n : ℝ) + 3)
  have hb : 1 / 2 ≤ b := by exact le_add_of_nonneg_right (by positivity)
  have h1 : b < 1 := by
    dsimp [b]
    have hh : 1 / ((n : ℝ) + 3) < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hρ : b < ρ.re := by
    have hh : 1 / ((n : ℝ) + 3) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    dsimp [b]; linarith
  have : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  intro hz
  apply dirichletLFunction_ne_zero_of_split_prime_lower_bound (lt_of_lt_of_le (by norm_num) hb) h1 he hρ hn (changeLevel hq χ)
  rw [LFunction_changeLevel hq χ (.inr hn), hz, zero_mul]

private theorem oneSidedPrime_primitive_critical_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hfree : ∀ (η : DirichletCharacter ℂ q) (s : ℂ), 1 / 2 < s.re → s ≠ 1 → η.LFunction s ≠ 0)
    {ρ : ℂ} (hp : 0 < ρ.re) (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) : ρ.re = 1 / 2 := by
  have hn : ρ ≠ 1 := fun e ↦ by simp [e] at hr
  have hright : ρ.re ≤ 1 / 2 := le_of_not_gt fun h ↦ hfree χ ρ h hn hz
  apply le_antisymm hright
  by_contra! hleft
  have hρ : ρ ≠ 0 := fun e ↦ by simp [e] at hp
  have hg : χ.gammaFactor ρ ≠ 0 := by
    intro h
    rcases χ.even_or_odd with he | ho
    · obtain ⟨n, e⟩ := (gammaFactor_eq_zero_iff_of_even he).mp h
      have heq := congrArg Complex.re e
      norm_num [Complex.mul_re] at heq
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · obtain ⟨n, e⟩ := (gammaFactor_eq_zero_iff_of_odd ho).mp h
      have heq := congrArg Complex.re e
      norm_num [Complex.mul_re] at heq
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcomp : χ.completedLFunction ρ = 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor ρ (.inl hρ)] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hg
  have he := hχ.completedLFunction_one_sub (1 - ρ)
  rw [sub_sub_cancel, hcomp] at he
  have hpow : (q : ℂ) ^ ((1 - ρ) - 1 / 2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, NeZero.ne q]
  have hi : χ⁻¹.completedLFunction (1 - ρ) = 0 := (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hpow (rootNumber_ne_zero hχ))
  have hk : χ⁻¹.LFunction (1 - ρ) = 0 := by
    rw [χ⁻¹.LFunction_eq_completed_div_gammaFactor (1 - ρ) (.inl (sub_ne_zero.mpr hn.symm)), hi, zero_div]
  have hd : 1 / 2 < (1 - ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  exact hfree χ⁻¹ (1 - ρ) hd (fun e ↦ hρ (by linear_combination -e)) hk

/-- If the identity progression has these eventual lower bounds at arbitrarily large factorial
moduli, every Dirichlet zero in the open critical strip has real part one half. -/
theorem dirichletLFunction_critical_line_of_factorial_prime_lower_bound (hE : ∀ N : ℕ, ∃ n ≥ N, ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      -(C * (k : ℝ) ^ (1 / 2 + 1 / ((n : ℝ) + 3))) ≤ dirichletSplitPrimeError n.factorial k)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hp : 0 < ρ.re) (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) : ρ.re = 1 / 2 := by
  have hn : ρ ≠ 1 := fun e ↦ by simp [e] at hr
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  apply oneSidedPrime_primitive_critical_line χ.primitiveCharacter χ.primitiveCharacter_isPrimitive (fun η _ ↦ dirichletLFunction_ne_zero_of_factorial_prime_lower_bound hE η) hp hr
  have he := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inr hn)
  rw [χ.changeLevel_primitiveCharacter, hz] at he
  apply (mul_eq_zero.mp he.symm).resolve_right
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp'
  have hprime := Nat.prime_of_mem_primeFactors hp'
  have hc : ‖(p : ℂ) ^ (-ρ)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_lt_zero.mpr hp)
  have he' : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-ρ)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.primitiveCharacter.norm_le_one _)).trans_lt hc
  exact sub_ne_zero.mpr fun e ↦ (ne_of_lt he') (by rw [← e, norm_one])

end RiemannMasullo
