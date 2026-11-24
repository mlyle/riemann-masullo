module

public import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Set.Infinite

/-! # Periodic factors on vertical strips -/

public section

open Set Filter Metric Complex
open scoped Topology

namespace RiemannMasullo

/-- A nonzero entire function stays away from zero on some enclosing circle of prescribed minimum radius. -/
private theorem exists_sphere_norm_pos {D : ℂ → ℂ} (hD : Differentiable ℂ D) (hne : ∃ z, D z ≠ 0)
    (r : ℝ) (hr : 0 < r) : ∃ R > r, ∃ d > 0, ∀ z ∈ sphere (0 : ℂ) R, d ≤ ‖D z‖ := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  have ha : AnalyticOnNhd ℂ D univ := fun z _ ↦ hD.analyticAt z
  have hdisc := (ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
    (fun h ↦ hz₀ (h (mem_univ z₀)))
  let K := closedBall (0 : ℂ) (r+1)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin
    (s := {z | D z ≠ 0}) ((Filter.codiscreteWithin_mono (subset_univ K)) hdisc)
  have hrad := hfin.image (fun z : ℂ ↦ ‖z‖)
  obtain ⟨R, hR, hout⟩ := (Ioo_infinite (show r < r+1 by linarith)).exists_notMem_finset hrad.toFinset
  have hRpos := hr.trans hR.1
  have hz (z : ℂ) (hs : z ∈ sphere 0 R) : D z ≠ 0 := by
    intro he
    have hn : ‖z‖ = R := mem_sphere_zero_iff_norm.mp hs
    apply hout
    exact hrad.mem_toFinset.mpr ⟨z, ⟨mem_closedBall_zero_iff.mpr (hn ▸ hR.2.le), fun h ↦ h he⟩, hn⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ℂ) R).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hRpos.le) hD.continuous.norm.continuousOn
  exact ⟨R, hR.1, ‖D w‖, norm_pos_iff.mpr (hz w hw), fun z hs ↦ hmin hs⟩

/-- Division by a nonzero entire function with a purely imaginary period preserves
boundedness on every closed vertical strip provided the quotient is entire. -/
theorem bddAbove_strip_of_periodic_mul {D G : ℂ → ℂ} (hD : Differentiable ℂ D)
    (hne : ∃ z, D z ≠ 0) {T : ℝ} (hT : 0 < T) (hper : Function.Periodic D ((T : ℂ) * I))
    (hG : Differentiable ℂ G)
    (h : ∀ a b : ℝ, a ≤ b → BddAbove ((fun z : ℂ ↦ ‖D z * G z‖) '' (re ⁻¹' Icc a b)))
    (a b : ℝ) : BddAbove ((fun z : ℂ ↦ ‖G z‖) '' (re ⁻¹' Icc a b)) := by
  let r := |a| + |b| + T + 1
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨R, hR, d, hd, hDlow⟩ := exists_sphere_norm_pos hD hne r hr
  have hRp := hr.trans hR
  obtain ⟨B, hB⟩ := h (-R) R (by linarith)
  refine ⟨B/d, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change a ≤ z.re ∧ z.re ≤ b at hz
  let n : ℤ := ⌊z.im / T⌋
  let c : ℂ := (n : ℂ) * ((T : ℂ) * I)
  have hc : c.re = 0 ∧ c.im = (n : ℝ) * T := by simp [c]
  have h0 : (n : ℝ) * T ≤ z.im := (le_div_iff₀ hT).mp (Int.floor_le _)
  have h1 : z.im < ((n : ℝ)+1) * T := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one _)
  have hin : z - c ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    apply (norm_le_abs_re_add_abs_im _).trans_lt
    rw [sub_re, sub_im, hc.1, hc.2, sub_zero, abs_of_nonneg (sub_nonneg.mpr h0)]
    have hre : |z.re| ≤ |a|+|b| := abs_le.mpr ⟨by linarith [neg_abs_le a, abs_nonneg b, hz.1],
      by linarith [le_abs_self b, abs_nonneg a, hz.2]⟩
    dsimp [r] at hR
    linarith
  let g (w : ℂ) := G (w + c)
  have hg : Differentiable ℂ g := hG.comp (differentiable_id.add_const c)
  have hgB : ‖g (z - c)‖ ≤ B / d := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) R))
      hg.diffContOnCl _ (subset_closure hin)
    intro w hw
    rw [frontier_ball _ hRp.ne'] at hw
    have hwn := mem_sphere_zero_iff_norm.mp hw
    have hwre := abs_le.mp ((abs_re_le_norm w).trans_eq hwn)
    have hstrip : (w + c).re ∈ Icc (-R) R := by rwa [add_re, hc.1, add_zero]
    have hprod := hB (mem_image_of_mem (fun v : ℂ ↦ ‖D v * G v‖) hstrip)
    rw [norm_mul, hper.int_mul n w] at hprod
    exact (le_div_iff₀' hd).mpr ((mul_le_mul_of_nonneg_right (hDlow w hw) (norm_nonneg _)).trans hprod)
  simpa [g] using hgB

/-- A continuous function with a positive imaginary period is bounded on any closed vertical strip. -/
theorem norm_bounded_on_strip_of_imaginary_period {D : ℂ → ℂ} (hd : Continuous D)
    {T : ℝ} (hT : 0 < T) (hp : Function.Periodic D ((T : ℂ)*I)) (a b : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, z.re ∈ Icc a b → ‖D z‖ ≤ C := by
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.bddAbove_image hd.norm.continuousOn
  refine ⟨C, fun z hz ↦ ?_⟩
  let n : ℤ := ⌊z.im / T⌋
  let c : ℂ := (n : ℂ) * ((T : ℂ) * I)
  have hc : c.re = 0 ∧ c.im = (n : ℝ) * T := by simp [c]
  have h0 : (n : ℝ) * T ≤ z.im := (le_div_iff₀ hT).mp (Int.floor_le _)
  have h1 : z.im < ((n : ℝ)+1) * T := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one _)
  have hw : z-c ∈ K := by
    refine ⟨?_, ?_⟩
    · change (z-c).re ∈ Icc a b
      rwa [sub_re, hc.1, sub_zero]
    · change (z-c).im ∈ Icc 0 T
      rw [sub_im, hc.2]
      exact ⟨by linarith, by linarith⟩
  have he : D (z-c) = D z := hp.sub_int_mul_eq n
  exact (congrArg norm he.symm).trans_le (hC (mem_image_of_mem _ hw))

end RiemannMasullo
