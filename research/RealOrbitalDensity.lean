import Mathlib

open Real Filter Set
open scoped Topology

noncomputable section

namespace RationalArchimedean

def decay (x : ℝ) := Real.exp (-x / 2)
def ratio (x : ℝ) := Real.exp (-2 * x)
def density (x : ℝ) := decay x / (1 - ratio x)
def slope (x : ℝ) := -(decay x * (1 + 3 * ratio x)) / (2 * (1 - ratio x) ^ 2)

private theorem decay_deriv (x : ℝ) : HasDerivAt decay (-decay x / 2) x := by
  unfold decay
  convert (((hasDerivAt_id x).neg.div_const 2).exp) using 1 <;> simp
  ring

private theorem ratio_deriv (x : ℝ) : HasDerivAt ratio (-2 * ratio x) x := by
  unfold ratio
  convert (((hasDerivAt_id x).const_mul (-2)).exp) using 1 <;> simp
  ring

private theorem denominator_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - ratio x := by
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

private theorem density_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt density (slope x) x := by
  have hD := (denominator_pos hx).ne'
  unfold density slope
  convert (decay_deriv x).div ((hasDerivAt_const x (1 : ℝ)).sub (ratio_deriv x)) hD using 1
  simp only [Pi.sub_apply]
  field_simp [hD]
  ring

/-- On a positive rational log shell this is the exact density after both polar
evaluation functionals have been removed by two integrations by parts. -/
theorem polarRemoved_density {x : ℝ} (hx : 0 < x) :
    deriv (deriv density) x - density x / 4 =
      2 * decay x * ratio x * (3 + ratio x) / (1 - ratio x) ^ 3 := by
  have hD := (denominator_pos hx).ne'
  have hnear : deriv density =ᶠ[𝓝 x] slope := by
    filter_upwards [lt_mem_nhds hx] with y hy using (density_deriv hy).deriv
  have hN := ((decay_deriv x).mul ((hasDerivAt_const x (1 : ℝ)).add
    ((ratio_deriv x).const_mul 3))).neg
  have hQ := ((((hasDerivAt_const x (1 : ℝ)).sub (ratio_deriv x)).pow 2).const_mul 2)
  have hs := hN.div hQ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hD))
  rw [hnear.deriv_eq, show deriv slope x = _ from hs.deriv]
  dsimp [density]
  field_simp [hD]
  ring

theorem polarRemoved_density_ge {x : ℝ} (hx : 0 < x) :
    6 * decay x * ratio x ≤ deriv (deriv density) x - density x / 4 := by
  rw [polarRemoved_density hx, le_div_iff₀ (pow_pos (denominator_pos hx) 3)]
  have hq : 0 < ratio x := Real.exp_pos _
  have hr : 0 < decay x := Real.exp_pos _
  have hD : (1 - ratio x) ^ 3 ≤ 1 :=
    pow_le_one₀ (denominator_pos hx).le (by linarith)
  calc
    6 * decay x * ratio x * (1 - ratio x) ^ 3 ≤ 6 * decay x * ratio x * 1 := by gcongr
    _ ≤ 2 * decay x * ratio x * (3 + ratio x) := by nlinarith [mul_pos hr (sq_pos_of_pos hq)]

#print axioms polarRemoved_density
#print axioms polarRemoved_density_ge

end RationalArchimedean
