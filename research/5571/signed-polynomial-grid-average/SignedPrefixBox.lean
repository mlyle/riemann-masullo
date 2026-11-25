module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

public noncomputable section

open Finset Function
namespace RiemannMasullo.PrimeGrid

def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range n, f (j+1)
private def delta (L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := f (n+L)-f n
private def box (L : ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ range L, f (n+j+1)

private theorem delta_prefix (L : ℕ) (f : ℕ → ℝ) : delta L (partialSum f) = box L f := by
  funext n
  unfold delta partialSum box
  rw [sum_range_add]
  simp

private theorem delta_box (L : ℕ) : Function.Commute (delta L) (box L) := by
  intro f
  funext n
  change (∑ j ∈ range L, f (n+L+j+1)) - (∑ j ∈ range L, f (n+j+1)) =
      ∑ j ∈ range L, (f (n+j+1+L) - f (n+j+1))
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [show n+L+j+1=n+j+1+L by omega]

private theorem delta_prefix_iter (m L : ℕ) (f : ℕ → ℝ) :
    (delta L)^[m] (partialSum^[m] f) = (box L)^[m] f := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply (delta L) m, iterate_succ_apply' partialSum m f, delta_prefix,
      (delta_box L).iterate_left m _, ih, iterate_succ_apply' (box L) m]

private theorem box_lower (m L n : ℕ) (f : ℕ → ℝ) (V : ℝ)
    (h : ∀ j ≤ m*L, V ≤ f (n+j)) : (L:ℝ)^m * V ≤ ((box L)^[m] f) n := by
  induction m generalizing n with
  | zero => simpa using h 0 (by simp)
  | succ m ih =>
    rw [iterate_succ_apply']
    change _ ≤ ∑ j ∈ range L, ((box L)^[m] f) (n+j+1)
    have H (j : ℕ) (hj : j ∈ range L) := ih (n+j+1) (fun i hi ↦ by
      have hm := h (j+1+i) (by rw [Nat.succ_mul]; have := mem_range.mp hj; omega)
      simpa [Nat.add_assoc] using hm)
    calc
      _ = ∑ _j ∈ range L, (L:ℝ)^m * V := by simp [pow_succ]; ring
      _ ≤ _ := sum_le_sum H

private theorem delta_upper (m L n : ℕ) (F : ℕ → ℝ) (C : ℝ)
    (h : ∀ j ≤ m, |F (n+j*L)| ≤ C) : |((delta L)^[m] F) n| ≤ (2:ℝ)^m*C := by
  induction m generalizing n with
  | zero => simpa using h 0 (by simp)
  | succ m ih =>
    rw [iterate_succ_apply']
    change |((delta L)^[m] F) (n+L) - ((delta L)^[m] F) n| ≤ _
    have Hleft := ih n (fun j hj ↦ h j (by omega))
    have Hright := ih (n+L) (fun j hj ↦ by
      have h' := h (j+1) (by omega)
      simpa only [Nat.add_mul, one_mul, Nat.add_assoc, Nat.add_comm L] using h')
    calc
      _ ≤ |((delta L)^[m] F) (n+L)| + |((delta L)^[m] F) n| := abs_sub _ _
      _ ≤ _ := by rw [pow_succ]; linarith

theorem signed_prefix_bound (m L n : ℕ) (f : ℕ → ℝ) (V C : ℝ)
    (h : ∀ j ≤ m*L, V ≤ f (n+j))
    (hp : ∀ j ≤ m, |(partialSum^[m] f) (n+j*L)| ≤ C) :
    (L:ℝ)^m * V ≤ (2:ℝ)^m*C := by
  have B := box_lower m L n f V h
  rw [← delta_prefix_iter] at B
  exact B.trans ((le_abs_self _).trans (delta_upper m L n (partialSum^[m] f) C hp))

#print axioms signed_prefix_bound
end RiemannMasullo.PrimeGrid
