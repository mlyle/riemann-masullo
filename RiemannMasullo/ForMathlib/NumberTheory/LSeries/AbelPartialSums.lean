module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Dirichlet series of partial sums

If A(n) is the partial sum of a(n) and grows at most linearly, the difference between
s L(A, s + 1) and L(a, s) extends holomorphically to Re(s) > 0. The correction comes from
replacing n⁻ˢ − (n + 1)⁻ˢ by its first derivative approximation s n⁻ˢ⁻¹.
-/

open Set Complex Filter LSeries Metric
open scoped Topology

public noncomputable section
namespace RiemannMasullo

private theorem partialSums_abelStep_real_bound {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖s * (a : ℂ) ^ (-s - 1) - (a : ℂ) ^ (-s) + ((a + 1 : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖s‖ * ‖ - s - 1‖ * a ^ (-s.re - 2) := by
  have h1 : -s - 1 ≠ 0 := by
    intro e
    have h := congrArg Complex.re e
    simp at h
    linarith
  have h0 : -s ≠ 0 := by exact neg_ne_zero.mpr (fun e ↦ by simp [e] at hs)
  let f (x : ℝ) := (x : ℂ) ^ (-s - 1)
  let M := ‖ - s - 1‖ * a ^ (-s.re - 2)
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg ha.le _)
  have hfd (x : ℝ) (hx : x ∈ Icc a (a + 1)) :
      HasDerivAt f ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x :=
    hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' h1
  have hbd (x : ℝ) (hx : x ∈ Ico a (a + 1)) :
      ‖(-s - 1) * (x : ℂ) ^ (-s - 1 - 1)‖ ≤ M := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hx.1)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    have h : -s.re - 1 - 1 = -s.re - 2 := by ring
    rw [h]
    exact Real.rpow_le_rpow_of_nonpos ha hx.1 (by linarith)
  have hdiff (x : ℝ) (hx : x ∈ Icc a (a + 1)) : ‖f x - f a‖ ≤ M :=
    (norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht ↦ (hfd t ht).hasDerivWithinAt) hbd x hx).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (show x - a ≤ 1 by linarith [hx.2]) hM)
  let F (x : ℝ) := (x : ℂ) ^ (-s) + ((x : ℂ) - a) * (s * f a)
  have hF (x : ℝ) (hx : x ∈ Icc a (a + 1)) : HasDerivAt F ((-s) * (f x - f a)) x := by
    have ho : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 x := by simpa using! (hasDerivAt_id x).ofReal_comp
    convert (hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' h0).add
      ((ho.sub_const (a : ℂ)).mul_const (s * f a)) using 1
    dsimp [f]
    ring
  have hFd (x : ℝ) (hx : x ∈ Ico a (a + 1)) : ‖(-s) * (f x - f a)‖ ≤ ‖s‖ * M := by
    rw [norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left (hdiff x ⟨hx.1, hx.2.le⟩) (norm_nonneg _)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht ↦ (hF t ht).hasDerivWithinAt) hFd
    (a + 1) (right_mem_Icc.mpr (by linarith))
  simp only [F, f, Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_left,
    sub_self, zero_mul, add_zero, one_mul, mul_one] at hh
  dsimp [M] at hh
  push_cast
  convert hh using 1 <;> ring_nf

private def partialSums_abelStep (n : ℕ) (s : ℂ) : ℂ :=
  s * ((n + 1:ℕ) : ℂ) ^ (-s - 1) - ((n + 1:ℕ) : ℂ) ^ (-s) + ((n + 2:ℕ) : ℂ) ^ (-s)

private def partialSums_abelCorrection (A : ℕ → ℂ) (s : ℂ) := ∑' n : ℕ, A n * partialSums_abelStep n s

private theorem partialSums_abelStep_bound (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖partialSums_abelStep n s‖ ≤ ‖s‖ * ‖ - s - 1‖ * ((n + 1:ℕ) : ℝ) ^ (-s.re - 2) := by
  convert partialSums_abelStep_real_bound hs (show (0 : ℝ) < (n + 1:ℕ) by positivity) using 1
  simp only [partialSums_abelStep, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  rw [show (n : ℂ) + 2 = (n : ℂ) + 1 + 1 by ring]

private theorem partialSums_abelCorrection_analytic {A : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C * (n + 1:ℕ)) :
    AnalyticOnNhd ℂ (partialSums_abelCorrection A) {s | 0 < s.re} := by
  intro s hs
  change 0 < s.re at hs
  let b := s.re / 2
  let M := ‖s‖ + 1
  let U := {z : ℂ | b < z.re} ∩ {z : ℂ | ‖z‖ < M}
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hopen : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by constructor <;> dsimp [b, M] <;> linarith
  let u (n : ℕ) := (C * M * (M + 1)) * ((n + 1:ℕ) : ℝ) ^ (-b - 1)
  have hu : Summable u := by
    apply Summable.mul_left
    exact (summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (-b - 1)) 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hterm (n : ℕ) : DifferentiableOn ℂ (fun z ↦ A n * partialSums_abelStep n z) U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    unfold partialSums_abelStep
    fun_prop (disch := norm_num)
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ U) : ‖A n * partialSums_abelStep n z‖ ≤ u n := by
    change b < z.re ∧ ‖z‖ < M at hz
    have hn : (1 : ℝ) ≤ (n + 1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn' := lt_of_lt_of_le zero_lt_one hn
    have hz' : ‖ - z - 1‖ ≤ M + 1 := by
      calc ‖ - z - 1‖ ≤ ‖ - z‖ + ‖(1 : ℂ)‖ := norm_sub_le ..
           _ ≤ _ := by simpa using add_le_add_right hz.2.le 1
    have hz'' : ((n + 1:ℕ) : ℝ) ^ (-z.re - 2) ≤ ((n + 1:ℕ) : ℝ) ^ (-b - 2) :=
      Real.rpow_le_rpow_of_exponent_le hn (by linarith [hz.1])
    rw [norm_mul]
    calc
      _ ≤ (C * (n + 1:ℕ)) * (‖z‖ * ‖ - z - 1‖ * ((n + 1:ℕ) : ℝ) ^ (-z.re - 2)) :=
        mul_le_mul (hA n) (partialSums_abelStep_bound n (hb.trans hz.1)) (norm_nonneg _) (by positivity)
      _ ≤ (C * (n + 1:ℕ)) * (M * (M + 1) * ((n + 1:ℕ) : ℝ) ^ (-b - 2)) := by gcongr; exact hz.2.le
      _ = u n := by
        have he : -b - 1 = (-b - 2) + 1 := by ring
        dsimp [u]
        rw [he, Real.rpow_add hn', Real.rpow_one]
        ring
  exact (Complex.differentiableOn_tsum_of_summable_norm hu hterm hopen hbound).analyticAt
    (hopen.mem_nhds hsU)

private theorem partialSums_summable_weight {A : ℕ → ℂ} {C : ℝ} (hA : ∀ n, ‖A n‖ ≤ C * (n + 1:ℕ))
    {s : ℂ} (hs : 2 < s.re) : Summable (fun n ↦ A n * ((n + 1:ℕ) : ℂ) ^ (-s)) := by
  have hS : Summable (fun n : ℕ ↦ C * ((n + 1:ℕ) : ℝ) ^ (1 - s.re)) :=
    ((summable_nat_add_iff (f := fun n : ℕ ↦ (n : ℝ) ^ (1 - s.re)) 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith))).mul_left C
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hS
  intro n
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), Complex.neg_re]
  have hpos : 0 < ((n + 1:ℕ) : ℝ) := by positivity
  rw [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hA n) (Real.rpow_nonneg hpos.le (-s.re))

private theorem partialSums_abel_tsum {A : ℕ → ℂ} (h0 : A 0 = 0) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ n : ℕ, ‖A n‖ ≤ C * n) {s : ℂ} (hs : 2 < s.re) :
    s * (∑' n : ℕ, A (n + 1) * ((n + 1:ℕ) : ℂ) ^ (-s - 1)) =
      (∑' n : ℕ, (A (n + 1) - A n) * ((n + 1:ℕ) : ℂ) ^ (-s)) + partialSums_abelCorrection (fun n ↦ A (n + 1)) s := by
  let P (n : ℕ) := ((n + 1:ℕ) : ℂ) ^ (-s)
  let V (n : ℕ) := ((n + 1:ℕ) : ℂ) ^ (-s - 1)
  have h₁ : Summable (fun n : ℕ ↦ A (n + 1) * P n) := partialSums_summable_weight (fun n ↦ hA (n + 1)) hs
  have h₂ : Summable (fun n : ℕ ↦ A n * P n) := partialSums_summable_weight (fun n ↦
    (hA n).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hC)) hs
  have h₃ : Summable (fun n : ℕ ↦ A (n + 1) * P (n + 1)) :=
    (summable_nat_add_iff (f := fun n : ℕ ↦ A n * P n) 1).mpr h₂
  have h₄ : Summable (fun n : ℕ ↦ A (n + 1) * V n) := by
    have h := partialSums_summable_weight (A := fun n ↦ A (n + 1)) (fun n ↦ hA (n + 1)) (s := s + 1)
      (by simp only [Complex.add_re, Complex.one_re]; linarith)
    simpa only [V, neg_add_rev, sub_eq_add_neg, add_comm (-s)] using h
  have hShift : (∑' n : ℕ, A n * P n) = ∑' n : ℕ, A (n + 1) * P (n + 1) := by
    rw [h₂.tsum_eq_zero_add]; simp [h0]
  have hu : (∑' n : ℕ, (A (n + 1) - A n) * P n) = (∑' n : ℕ, A (n + 1) * P n) - ∑' n : ℕ, A n * P n := by
    simp_rw [sub_mul]
    exact h₁.tsum_sub h₂
  have hk : partialSums_abelCorrection (fun n ↦ A (n + 1)) s =
      s * (∑' n : ℕ, A (n + 1) * V n) - (∑' n : ℕ, A (n + 1) * P n) + ∑' n : ℕ, A (n + 1) * P (n + 1) := by
    unfold partialSums_abelCorrection
    rw [← tsum_mul_left,← (h₄.mul_left s).tsum_sub h₁,← ((h₄.mul_left s).sub h₁).tsum_add h₃]
    apply tsum_congr
    intro n
    dsimp [partialSums_abelStep, P, V]
    ring
  change s * (∑' n : ℕ, A (n + 1) * V n) = (∑' n : ℕ, (A (n + 1) - A n) * P n) + _
  rw [hk, hu, hShift]
  ring

private theorem partialSums_LSeries_succ {a : ℕ → ℂ} {s : ℂ} (h : Summable (fun n : ℕ ↦ a (n + 1) * ((n + 1:ℕ) : ℂ) ^ (-s))) :
    LSeries a s = ∑' n : ℕ, a (n + 1) * ((n + 1:ℕ) : ℂ) ^ (-s) := by
  have he (n : ℕ) : term a s (n + 1) = a (n + 1) * ((n + 1:ℕ) : ℂ) ^ (-s) := by
    rw [term_of_ne_zero (Nat.succ_ne_zero _), Complex.cpow_neg, div_eq_mul_inv]
  have h' : Summable (term a s) := (summable_nat_add_iff 1).mp (h.congr fun n ↦ (he n).symm)
  rw [LSeries, h'.tsum_eq_zero_add, term_zero, zero_add]
  exact tsum_congr he

private theorem partialSums_abel_identity {A a : ℕ → ℂ} (h₀ : A 0 = 0) (ha : ∀ n, A (n + 1) - A n = a (n + 1))
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ n : ℕ, ‖A n‖ ≤ C * n) {s : ℂ} (hs : 2 < s.re) :
    s * LSeries A (s + 1) = LSeries a s + partialSums_abelCorrection (fun n ↦ A (n + 1)) s := by
  have h₁ := partialSums_summable_weight (A := fun n ↦ A (n + 1)) (fun n ↦ hA (n + 1)) hs
  have h₂ := partialSums_summable_weight (A := A) (fun n ↦ (hA n).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ n) hC)) hs
  have hu : Summable (fun n : ℕ ↦ a (n + 1) * ((n + 1:ℕ) : ℂ) ^ (-s)) := by
    simp_rw [← ha, sub_mul]
    exact h₁.sub h₂
  have h₃ := partialSums_summable_weight (A := fun n ↦ A (n + 1)) (fun n ↦ hA (n + 1)) (s := s + 1)
    (by simp only [Complex.add_re, Complex.one_re]; linarith)
  rw [partialSums_LSeries_succ h₃, partialSums_LSeries_succ hu]
  have hh := partialSums_abel_tsum h₀ hC hA hs
  simpa only [ha, neg_add_rev, sub_eq_add_neg, add_comm (-s)] using hh

/-- For partial sums A of at most linear growth, the difference s L(A, s + 1) − L(a, s)
has an analytic continuation to the open right half-plane. -/
theorem LSeries_partialSums_analytic_correction {A a : ℕ → ℂ} (h₀ : A 0 = 0) (ha : ∀ n, A (n + 1) - A n = a (n + 1))
    (hA : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖A n‖ ≤ C * n) :
    ∃ E : ℂ → ℂ, AnalyticOnNhd ℂ E {s | 0 < s.re} ∧
      ∀ s : ℂ, 2 < s.re → s * LSeries A (s + 1) = LSeries a s + E s := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact ⟨partialSums_abelCorrection (fun n ↦ A (n + 1)), partialSums_abelCorrection_analytic hC (fun n ↦ hAC (n + 1)),
    fun _ hs ↦ partialSums_abel_identity h₀ ha hC hAC hs⟩

end RiemannMasullo
