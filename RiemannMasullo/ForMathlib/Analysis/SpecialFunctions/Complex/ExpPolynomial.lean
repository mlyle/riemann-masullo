module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Linear independence of exponential polynomials

Functions `t ↦ exp (z t) P(t)` on the real line with pairwise distinct complex exponents `z` and
polynomial factors `P` are linearly independent. The proof uses translation by a small step: each
such function is a generalized eigenvector of the translation operator, and generalized
eigenspaces for distinct eigenvalues are independent.
-/

@[expose] public section

namespace RiemannMasullo

open Polynomial

/-- Exponential polynomials with distinct exponents are linearly independent: if a finite sum of
functions `t ↦ exp (s c * t) * P c (t)` with pairwise distinct exponents vanishes on the real line,
then every polynomial `P c` is zero. -/
theorem exp_mul_polynomial_eq_zero {ι : Type*} (C : Finset ι) (s : ι → ℂ) (hs : Set.InjOn s C)
    (P : ι → ℂ[X])
    (h : ∀ t : ℝ, ∑ c ∈ C, Complex.exp (s c * t) * (P c).eval (t : ℂ) = 0) :
    ∀ c ∈ C, P c = 0 := by
  classical
  -- A translation step small enough to separate the exponentials.
  let B : ℝ := ∑ c ∈ C, ‖s c‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  let h₀ : ℝ := Real.pi / (2 * B + 1)
  have hh₀ : 0 < h₀ := div_pos Real.pi_pos (by positivity)
  let T : Module.End ℂ (ℝ → ℂ) :=
    { toFun := fun f t ↦ f (t + h₀), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let v (z : ℂ) (Q : ℂ[X]) : ℝ → ℂ := fun t ↦ Complex.exp (z * t) * Q.eval (t : ℂ)
  let μ (z : ℂ) : ℂ := Complex.exp (z * h₀)
  have hstep (z : ℂ) (Q : ℂ[X]) : (T - μ z • (1 : Module.End ℂ (ℝ → ℂ))) (v z Q) =
      v z (μ z • (taylor (h₀ : ℂ) Q - Q)) := by
    funext t
    change Complex.exp (z * ((t + h₀ : ℝ) : ℂ)) * Q.eval (((t + h₀ : ℝ) : ℂ)) -
        μ z * (Complex.exp (z * t) * Q.eval (t : ℂ)) =
      Complex.exp (z * t) * (μ z • (taylor (h₀ : ℂ) Q - Q)).eval (t : ℂ)
    rw [eval_smul, eval_sub, taylor_eval, smul_eq_mul]
    push_cast
    rw [mul_add, Complex.exp_add]
    ring
  have hmem (z : ℂ) : ∀ (n : ℕ) (Q : ℂ[X]), Q.degree < n →
      ((T - μ z • (1 : Module.End ℂ (ℝ → ℂ))) ^ n) (v z Q) = 0 := by
    intro n
    induction n with
    | zero =>
      intro Q hQ
      have hQ0 : Q = 0 := by
        by_contra hne
        exact absurd hQ (not_lt.mpr (by simpa using zero_le_degree_iff.mpr hne))
      funext t
      simp [v, hQ0]
    | succ n ih =>
      intro Q hQ
      rw [pow_succ]
      change ((T - μ z • (1 : Module.End ℂ (ℝ → ℂ))) ^ n)
        ((T - μ z • (1 : Module.End ℂ (ℝ → ℂ))) (v z Q)) = 0
      rw [hstep]
      apply ih
      by_cases hQ0 : Q = 0
      · simp [hQ0]
      · have hlt : (taylor (h₀ : ℂ) Q - Q).degree < Q.degree :=
          (degree_sub_lt_left (degree_taylor Q _) ((taylor_eq_zero _ _).not.mpr hQ0)
            (leadingCoeff_taylor _ _)).trans_eq (degree_taylor Q _)
        refine lt_of_le_of_lt (degree_smul_le _ _) ?_
        have h1 : Q.degree ≤ n :=
          degree_le_of_natDegree_le (Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hQ0).mpr hQ))
        exact lt_of_lt_of_le hlt h1
  have hgen (c : ι) : v (s c) (P c) ∈ T.maxGenEigenspace (μ (s c)) :=
    (Module.End.mem_maxGenEigenspace _ _ _).mpr
      ⟨(P c).natDegree + 1, hmem (s c) _ _ (by
        exact_mod_cast (P c).degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_self _))⟩
  have hμ : Set.InjOn (fun c ↦ μ (s c)) C := by
    intro c hc c' hc' he
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    apply hs hc hc'
    have hle : ‖s c - s c'‖ ≤ 2 * B := by
      have h1 : ‖s c‖ ≤ B := Finset.single_le_sum (f := fun c ↦ ‖s c‖) (fun _ _ ↦ norm_nonneg _) hc
      have h2 : ‖s c'‖ ≤ B := Finset.single_le_sum (f := fun c ↦ ‖s c‖) (fun _ _ ↦ norm_nonneg _) hc'
      exact (norm_sub_le _ _).trans (by linarith)
    have hnorm : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ < 2 * Real.pi := by
      have e : (n : ℂ) * (2 * Real.pi * Complex.I) = (s c - s c') * h₀ := by
        linear_combination -hn
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh₀.le]
      have h3 : ‖s c - s c'‖ * h₀ ≤ 2 * B * h₀ := mul_le_mul_of_nonneg_right hle hh₀.le
      have h4 : 2 * B * h₀ < Real.pi := by
        rw [show 2 * B * h₀ = Real.pi * (2 * B / (2 * B + 1)) by simp only [h₀]; ring]
        have : 2 * B / (2 * B + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
        nlinarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      have h2 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Complex.norm_intCast]
        simp [abs_of_pos Real.pi_pos]
      rw [h2] at hnorm
      nlinarith [Real.pi_pos]
    rw [hn0, Int.cast_zero, zero_mul, add_zero] at hn
    have hc0 : ((h₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh₀.ne'
    exact mul_right_cancel₀ hc0 hn
  have hsum : ∑ c ∈ C, v (s c) (P c) = 0 := by
    funext t
    rw [Finset.sum_apply]
    exact h t
  have hind := Module.End.independent_maxGenEigenspace T
  intro c₀ hc₀
  have hv : v (s c₀) (P c₀) = 0 := by
    have hrest : v (s c₀) (P c₀) = -∑ c ∈ C.erase c₀, v (s c) (P c) := by
      rw [eq_neg_iff_add_eq_zero, Finset.add_sum_erase C (fun c ↦ v (s c) (P c)) hc₀, hsum]
    refine Submodule.disjoint_def.mp (hind (μ (s c₀))) _ (hgen c₀) ?_
    rw [hrest]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun c hc ↦ ?_)
    have hne : μ (s c) ≠ μ (s c₀) := fun he ↦
      (Finset.ne_of_mem_erase hc) (hμ (Finset.mem_of_mem_erase hc) hc₀ he)
    exact Submodule.mem_iSup_of_mem (μ (s c)) (Submodule.mem_iSup_of_mem hne (hgen c))
  apply eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem Complex.ofReal_injective fun t : ℝ ↦ ?_
  have ht := congrFun hv t
  exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)

/-- Triangular unwinding of exponential polynomials. At each centre `c` the coefficients
`L c m` vanish above the order `n c` and the leading one does not. If the exponential polynomials
given by the translation formula for Laurent coefficients cancel on the real line, every weight
vanishes. -/
theorem expPolynomial_translate_coeff_eq_zero {ι κ : Type*} (J : Finset ι) (cen : ι → κ)
    (ord : ι → ℕ) (s : κ → ℂ) (n : κ → ℕ) (L : κ → ℕ → ℂ) (a : ι → ℂ)
    (hinj : ∀ j ∈ J, ∀ j' ∈ J, cen j = cen j' → ord j = ord j' → j = j')
    (hs : ∀ j ∈ J, ∀ j' ∈ J, s (cen j) = s (cen j') → cen j = cen j')
    (hJ : ∀ j ∈ J, ord j ≤ n (cen j))
    (hL : ∀ j ∈ J, L (cen j) (n (cen j)) ≠ 0) (hL0 : ∀ (c : κ) (m : ℕ), n c < m → L c m = 0)
    (h : ∀ t : ℝ, ∑ j ∈ J, a j * (Complex.exp (s (cen j) * t) *
      ∑ i ∈ Finset.range (n (cen j) - ord j + 1),
        L (cen j) (ord j + i) * (t : ℂ) ^ i / (i.factorial : ℂ)) = 0) :
    ∀ j ∈ J, a j = 0 := by
  classical
  let Q (j : ι) : ℂ[X] := ∑ i ∈ Finset.range (n (cen j) - ord j + 1),
    C (L (cen j) (ord j + i) / (i.factorial : ℂ)) * X ^ i
  have hQc (j : ι) (d : ℕ) : (Q j).coeff d =
      if d < n (cen j) - ord j + 1 then L (cen j) (ord j + d) / (d.factorial : ℂ) else 0 := by
    simp only [Q, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range]
  have hQe (j : ι) (t : ℂ) : (Q j).eval t = ∑ i ∈ Finset.range (n (cen j) - ord j + 1),
      L (cen j) (ord j + i) * t ^ i / (i.factorial : ℂ) := by
    simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  let P (c : κ) : ℂ[X] := ∑ j ∈ J with cen j = c, C (a j) * Q j
  have hP : ∀ c ∈ J.image cen, P c = 0 := by
    refine exp_mul_polynomial_eq_zero (J.image cen) s ?_ P fun t ↦ ?_
    · intro c hc c' hc' he
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hc'
      exact hs j hj j' hj' he
    · rw [← h t, ← Finset.sum_fiberwise_of_maps_to (g := cen)
        (fun j hj ↦ Finset.mem_image_of_mem _ hj)]
      refine Finset.sum_congr rfl fun c _ ↦ ?_
      simp only [P, eval_finsetSum, eval_mul, eval_C]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [hQe, (Finset.mem_filter.mp hj).2]
      ring
  intro j₀ hj₀
  induction hk : ord j₀ using Nat.strong_induction_on generalizing j₀ with
  | _ k ih =>
    have hP0 := hP (cen j₀) (Finset.mem_image_of_mem _ hj₀)
    have hcoeff := congrArg (fun p : ℂ[X] ↦ p.coeff (n (cen j₀) - ord j₀)) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_zero] at hcoeff
    rw [Finset.sum_eq_single j₀] at hcoeff
    · rw [hQc, ite_eq_left (Nat.lt_succ_self _), Nat.add_sub_cancel' (hJ j₀ hj₀)] at hcoeff
      have hne : L (cen j₀) (n (cen j₀)) / ((n (cen j₀) - ord j₀).factorial : ℂ) ≠ 0 :=
        div_ne_zero (hL j₀ hj₀) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      exact (mul_eq_zero.mp hcoeff).resolve_right hne
    · intro j hj hne
      obtain ⟨hjJ, hjc⟩ := Finset.mem_filter.mp hj
      rcases lt_trichotomy (ord j) (ord j₀) with hlt | heq | hgt
      · rw [ih (ord j) (hk ▸ hlt) j hjJ rfl, zero_mul]
      · exact absurd (hinj j hjJ j₀ hj₀ hjc heq) hne
      · rw [hQc]
        split_ifs
        · rw [hjc, hL0 (cen j₀) _ (by have := hJ j₀ hj₀; omega), zero_div, mul_zero]
        · rw [mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_filter.mpr ⟨hj₀, rfl⟩)).elim

end RiemannMasullo
