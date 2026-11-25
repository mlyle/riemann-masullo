module

public import RiemannMasullo.Ch13_ZerosHecke.RieszZeroGaussianMeanSquare
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Mean square on the fourth-power prime sample grid

The gap between two logarithmic frequencies in the fourth-power prime
measurements bounds their Gaussian correlation. The estimate allows
arbitrary coefficients, including the indicators that select negative samples.
-/

public noncomputable section

open Finset Real MeasureTheory

namespace RiemannMasullo

private theorem fourthGrid_log_gap {x y n : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyn : y ≤ n) :
    (y-x)/n ≤ Real.log y - Real.log x := by
  have hy := hx.trans_le hxy
  have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at h
  calc
    _ ≤ (y-x)/y := div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hy hyn
    _ = 1-x/y := by field_simp
    _ ≤ _ := by linarith

private theorem fourthGrid_kernel {x y n T : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hyn : y ≤ n) (hT : 0 < T) :
    Real.exp (-((2*T*Real.log y - 2*T*Real.log x)^2)) ≤
      Real.exp 1 * Real.exp (-(4*T/n)*(y-x)) := by
  have h := mul_le_mul_of_nonneg_left (fourthGrid_log_gap hx hxy hyn) (by positivity : 0 ≤ 4*T)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [show -(4*T/n)*(y-x) = -(4*T*((y-x)/n)) by ring]
  nlinarith [sq_nonneg (2*T*Real.log y - 2*T*Real.log x - 1)]

private theorem fourthGrid_geometric (S : Finset ℕ) (g : ℕ → ℕ)
    (hinj : Set.InjOn g (S : Set ℕ)) {u : ℝ} (hu : 0 < u) :
    ∑ k ∈ S, Real.exp (-u*((g k : ℝ)+1)) ≤ 1 / u := by
  let r := Real.exp (-u)
  have hr : 0 < r := Real.exp_pos _
  have hr' : |r| < 1 := by
    rw [abs_of_pos hr]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hfun (k : ℕ) : Real.exp (-u*((g k : ℝ)+1)) = r*r^(g k) := by
    dsimp [r]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hsum := Summable.sum_le_tsum (S.image g) (fun i _ ↦ pow_nonneg hr.le i)
    (summable_geometric_of_abs_lt_one hr')
  rw [tsum_geometric_of_abs_lt_one hr'] at hsum
  rw [Finset.sum_image hinj] at hsum
  simp_rw [hfun]
  rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hsum hr.le).trans ?_
  have hone : r*(u+1) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp u) hr.le
    simpa [r, Real.exp_neg, (Real.exp_pos u).ne'] using h
  rw [← div_eq_mul_inv, le_div_iff₀ hu, div_mul_eq_mul_div, div_le_iff₀]
  · linarith
  · rw [abs_of_pos hr] at hr'
    linarith

/-- Every row of the Gaussian kernel on the fourth-power logarithmic frequencies
has bounded mass, uniformly in the chosen sample. -/
theorem fourthPowerPrimeGrid_gaussianRow {J j : ℕ} (hj : j ∈ Finset.Icc 1 J)
    {T : ℝ} (hT : 0 < T) :
    ∑ k ∈ Finset.Icc 1 J, Real.exp (-((2*T*Real.log j - 2*T*Real.log k)^2)) ≤
      1 + Real.exp 1 * (J:ℝ) / (2*T) := by
  let S := Finset.Icc 1 J
  let u := 4*T/(J:ℝ)
  let K (x y : ℕ) := Real.exp (-((2*T*Real.log x - 2*T*Real.log y)^2))
  have hj' := Finset.mem_Icc.mp hj
  have hJ : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hu : 0 < u := by dsimp [u]; positivity
  have hsym (x y : ℕ) : K x y = K y x := by
    dsimp [K]
    congr 2
    ring
  have hpoint (x y : ℕ) (hx : 1 ≤ x) (hxy : x < y) (hy : y ≤ J) :
      K x y ≤ Real.exp 1 * Real.exp (-u*(((y-x-1 : ℕ):ℝ)+1)) := by
    have hn : (((y-x-1 : ℕ):ℝ)+1) = (y:ℝ)-x := by
      rw [Nat.cast_sub (by omega : 1 ≤ y-x), Nat.cast_sub hxy.le, Nat.cast_one]
      ring
    rw [hn, hsym]
    exact fourthGrid_kernel (by exact_mod_cast (show 0 < x by omega))
      (by exact_mod_cast hxy.le) (by exact_mod_cast hy) hT
  have hside (U : Finset ℕ) (g : ℕ → ℕ) (hinj : Set.InjOn g (U : Set ℕ))
      (hK : ∀ k ∈ U, K j k ≤ Real.exp 1 * Real.exp (-u*((g k : ℝ)+1))) :
      ∑ k ∈ U, K j k ≤ Real.exp 1 * (1/u) := by
    calc
      _ ≤ ∑ k ∈ U, Real.exp 1 * Real.exp (-u*((g k : ℝ)+1)) := Finset.sum_le_sum hK
      _ = _ := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (fourthGrid_geometric U g hinj hu) (Real.exp_pos _).le
  let U := S.erase j
  have hleft : ∑ k ∈ U with k < j, K j k ≤ Real.exp 1 * (1/u) := by
    apply hside _ (fun k ↦ j-k-1)
    · intro a ha b hb e
      obtain ⟨_, h₁⟩ := Finset.mem_filter.mp ha
      obtain ⟨_, h₂⟩ := Finset.mem_filter.mp hb
      dsimp at e
      omega
    · intro k hk
      obtain ⟨hU,hk'⟩ := Finset.mem_filter.mp hk
      have hmem := Finset.mem_Icc.mp (Finset.mem_erase.mp hU).2
      rw [hsym]
      exact hpoint k j hmem.1 hk' hj'.2
  have hright : ∑ k ∈ U with ¬ k < j, K j k ≤ Real.exp 1 * (1/u) := by
    apply hside _ (fun k ↦ k-j-1)
    · intro a ha b hb e
      obtain ⟨ha,h₁⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb,h₂⟩ := Finset.mem_filter.mp hb
      have ea := (Finset.mem_erase.mp ha).1
      have eb := (Finset.mem_erase.mp hb).1
      dsimp at e
      omega
    · intro k hk
      obtain ⟨hU,hk'⟩ := Finset.mem_filter.mp hk
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hU
      exact hpoint j k hj'.1 (by omega) (Finset.mem_Icc.mp hm).2
  have h := add_le_add hleft hright
  rw [Finset.sum_filter_add_sum_filter_not] at h
  change ∑ k ∈ S, K j k ≤ _
  rw [← Finset.sum_erase_add S (K j) hj, show K j j = 1 by simp [K]]
  have hden : Real.exp 1 * (1/u) + Real.exp 1 * (1/u) = Real.exp 1 * (J:ℝ)/(2*T) := by
    dsimp [u]
    field_simp
    ring
  linarith

/-- The Gaussian mean square of an arbitrary fourth-power sample polynomial
is bounded by its coefficient energy. The center, scale, and complex sample
coefficients are free, so the estimate includes signed clipping masks. -/
theorem fourthPowerPrimeGrid_gaussianMeanSquare (J : ℕ) (c : ℕ → ℂ) (u : ℝ)
    {T : ℝ} (hT : 0 < T) :
    (∫ v : ℝ, Real.exp (-(v^2)) *
      ‖∑ j ∈ Finset.Icc 1 J, c j * Complex.exp
        (((4*(u+T*v)*Real.log ((j:ℝ)/J) : ℝ) : ℂ)*Complex.I)‖^2) ≤
      Real.sqrt Real.pi * Real.exp 1 * (1+Real.exp 1*(J:ℝ)/(2*T)) *
        ∑ j ∈ Finset.Icc 1 J, ‖c j‖^2 := by
  let L (j : ℕ) := Real.log ((j:ℝ)/J)
  let z (j : ℕ) : ℂ := ((2*T*L j : ℝ):ℂ)*Complex.I
  let d (j : ℕ) := c j * Complex.exp (((4*u*L j : ℝ):ℂ)*Complex.I)
  have hr (j : ℕ) (hj : j ∈ Finset.Icc 1 J) :
      ∑ k ∈ Finset.Icc 1 J, Real.exp (-(((z j).im-(z k).im)^2)) ≤
        1+Real.exp 1*(J:ℝ)/(2*T) := by
    refine le_trans (le_of_eq ?_) (fourthPowerPrimeGrid_gaussianRow hj hT)
    apply Finset.sum_congr rfl
    intro k hk
    have hj' := Finset.mem_Icc.mp hj
    have hk' := Finset.mem_Icc.mp hk
    have hn : (J:ℝ) ≠ 0 := by exact_mod_cast (show J ≠ 0 by omega)
    have hreg (i : ℕ) (hi : i ≠ 0) : Real.log ((i:ℝ)/J) = Real.log i-Real.log J :=
      Real.log_div (by exact_mod_cast hi) hn
    simp only [z, L, Complex.mul_I_im, Complex.ofReal_re, hreg j (by omega), hreg k (by omega)]
    rw [show 2*T*(Real.log j-Real.log J)-2*T*(Real.log k-Real.log J) =
      2*T*Real.log j-2*T*Real.log k by ring]
  have h := rieszZero_gaussian_meanSquare_le (Finset.Icc 1 J) d z
    (1+Real.exp 1*(J:ℝ)/(2*T)) (fun j _ ↦ by simp [z]) hr
  have he (v : ℝ) : (∑ j ∈ Finset.Icc 1 J, d j * Complex.exp (2*z j*v)) =
      ∑ j ∈ Finset.Icc 1 J, c j * Complex.exp
        (((4*(u+T*v)*Real.log ((j:ℝ)/J) : ℝ) : ℂ)*Complex.I) := by
    apply Finset.sum_congr rfl
    intro j _
    dsimp [d, z, L]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [he] at h
  have hd (j : ℕ) : ‖d j‖ = ‖c j‖ := by
    dsimp only [d]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simpa only [hd] using h

end RiemannMasullo
