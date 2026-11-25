module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Smooth compact profiles with positive real Laplace transform on a strip

A Gaussian times the autocorrelation of an even bump has strictly positive cosine transform
at every real frequency. Dividing by a hyperbolic cosine gives one real even compact test
whose bilateral Laplace transform has positive real part throughout the closed strip.
A second difference of the numerator cancels the two real boundary moments while preserving
strict positivity throughout the open strip.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function Complex
open scoped ContDiff Convolution Real

namespace RiemannMasullo
namespace EdgeProfile

private def phase (t x : ℝ) : ℂ := Complex.exp ((t * x : ℝ) * Complex.I)

private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by simp [phase, Complex.norm_exp]

private theorem phase_add (t x y : ℝ) : phase t (x + y) = phase t x * phase t y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def transform (f : ℝ → ℝ) (t : ℝ) : ℂ := ∫ x : ℝ, (f x : ℂ) * phase t x

private theorem transform_int {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (t : ℝ) :
    Integrable (fun x : ℝ ↦ (f x : ℂ) * phase t x) := by
  exact ((Complex.continuous_ofReal.comp hf).mul (by unfold phase; fun_prop)).integrable_of_hasCompactSupport
    ((hc.comp_left Complex.ofReal_zero).mul_right)

private theorem transform_continuous {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Continuous (transform f) := by
  apply continuous_of_dominated
    (bound := fun x : ℝ ↦ ‖f x‖) (fun t ↦ (transform_int hf hc t).aestronglyMeasurable)
  · exact fun t ↦ .of_forall fun x ↦ by simp [phase_norm]
  · exact (hf.integrable_of_hasCompactSupport hc).norm
  · exact .of_forall fun x ↦ by unfold phase; fun_prop

private theorem transform_re {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (t : ℝ) :
    (transform f t).re = ∫ x : ℝ, f x * Real.cos (t * x) := by
  rw [transform, ← RCLike.re_eq_complex_re, ← integral_re (transform_int hf hc t), RCLike.re_eq_complex_re]
  simp [phase, Complex.exp_re]

private theorem transform_even_real {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (he : ∀ x, f (-x) = f x) (t : ℝ) : (transform f t).im = 0 := by
  rw [transform, ← RCLike.im_eq_complex_im, ← integral_im (transform_int hf hc t), RCLike.im_eq_complex_im]
  have hz := integral_neg_eq_self (μ := volume) (fun x : ℝ ↦ f x * Real.sin (t * x))
  simp only [he, mul_neg, Real.sin_neg, integral_neg] at hz
  simpa [phase, Complex.exp_im] using (show (∫ x : ℝ, f x * Real.sin (t * x)) = 0 by linarith)

private theorem transform_convolution {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) (t : ℝ) :
    transform (f ⋆[ContinuousLinearMap.mul ℝ ℝ] g) t = transform f t * transform g t := by
  let F := fun x : ℝ ↦ (f x : ℂ) * phase t x
  let G := fun x : ℝ ↦ (g x : ℂ) * phase t x
  change _ = (ContinuousLinearMap.mul ℝ ℂ) (∫ x : ℝ, F x) (∫ x : ℝ, G x)
  rw [← integral_convolution _ (transform_int hf hfc t) (transform_int hg hgc t)]
  unfold transform
  apply integral_congr_ae
  filter_upwards with x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  have hp : phase t x = phase t u * phase t (x - u) := by
    rw [← phase_add]; congr 1; ring
  simp only [Complex.ofReal_mul, hp]
  ring

private theorem gaussian_phase (x : ℝ) :
    (∫ u : ℝ, (Real.exp (-(u ^ 2)) : ℂ) * phase u x) =
      ((Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4) : ℝ) : ℂ) := by
  have h := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (x : ℂ)
  have hp : ((Real.pi : ℂ) ^ (1 / 2 : ℂ)) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    convert (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm using 2
    norm_num
  convert h using 1
  · congr 1
    funext u
    unfold phase
    push_cast
    rw [mul_comm, show (u : ℂ) * x * Complex.I = Complex.I * x * u by ring, neg_one_mul]
  · rw [div_one, hp]
    push_cast
    rw [mul_one]

private theorem gaussian_average {k : ℝ → ℝ} (hk : Continuous k) (hc : HasCompactSupport k) (t : ℝ) :
    transform (fun x ↦ k x * (Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4))) t =
      ∫ u : ℝ, (Real.exp (-(u ^ 2)) : ℂ) * transform k (t + u) := by
  have hG : Integrable (fun u : ℝ ↦ Real.exp (-(u ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  let P := fun (x u : ℝ) ↦ (Real.exp (-(u ^ 2)) : ℂ) * ((k x : ℂ) * phase (t + u) x)
  have hP : Integrable (uncurry P) (volume.prod volume) := by
    apply ((hk.integrable_of_hasCompactSupport hc).norm.mul_prod hG).mono'
    · have hm : Continuous (uncurry P) := by dsimp [P, uncurry, phase]; fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards with p
      simp only [P, uncurry, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
      exact le_rfl
  calc transform (fun x ↦ k x * (Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4))) t
      = ∫ x : ℝ, ∫ u : ℝ, P x u := by
          unfold transform
          apply integral_congr_ae
          filter_upwards with x
          rw [Complex.ofReal_mul, ← gaussian_phase, mul_assoc, ← integral_mul_const, ← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u
          have he : phase (t + u) x = phase t x * phase u x := by
            unfold phase; rw [← Complex.exp_add]; congr 1; push_cast; ring
          simp only [P, he]
          ring
    _ = ∫ u : ℝ, ∫ x : ℝ, P x u := integral_integral_swap hP
    _ = _ := by simp only [P, transform, integral_const_mul]

private theorem convolution_kernel :
    ∃ k : ℝ → ℝ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ (∀ x, k (-x) = k x) ∧
      0 < k 0 ∧ (∀ t, 0 ≤ (transform k t).re) ∧ 0 < (transform k 0).re := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  let k := (f : ℝ → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ] (f : ℝ → ℝ)
  have hk : ContDiff ℝ ∞ k := f.hasCompactSupport.contDiff_convolution_right _
    f.continuous.locallyIntegrable f.contDiff
  have hc : HasCompactSupport k := f.hasCompactSupport.convolution _ f.hasCompactSupport
  have he (x : ℝ) : k (-x) = k x := by
    change (∫ u : ℝ, f u * f (-x - u)) = ∫ u : ℝ, f u * f (x - u)
    rw [← integral_neg_eq_self (fun u : ℝ ↦ f u * f (-x - u))]
    simp only [f.neg, show ∀ u : ℝ, -x - -u = -(x - u) by intro u; ring]
  have h₀ : 0 < k 0 := by
    change 0 < ∫ u : ℝ, f u * f (0 - u)
    simp only [zero_sub, f.neg]
    exact integral_pos_of_integrable_nonneg_ne_zero (x := 0) (f.continuous.mul f.continuous)
      ((f.continuous.mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right)
      (fun x ↦ mul_self_nonneg _) (by rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)]; norm_num)
  have hsq (t : ℝ) : (transform k t).re = (transform f t).re ^ 2 := by
    rw [show transform k t = transform f t * transform f t from
      transform_convolution f.continuous f.continuous f.hasCompactSupport f.hasCompactSupport t,
      Complex.mul_re, transform_even_real f.continuous f.hasCompactSupport f.neg, zero_mul, sub_zero, sq]
  refine ⟨k, hk, hc, he, h₀, fun t ↦ (hsq t).symm ▸ sq_nonneg _, ?_⟩
  rw [hsq, transform_re f.continuous f.hasCompactSupport]
  simpa using sq_pos_of_pos f.integral_pos

end EdgeProfile

open EdgeProfile in
/-- A real even smooth compact kernel strictly positive at the origin and with strictly
positive cosine transform at every real frequency. -/
theorem exists_compact_pos_cosineTransform :
    ∃ K : ℝ → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧ (∀ x, K (-x) = K x) ∧
      0 < K 0 ∧ ∀ t : ℝ, 0 < ∫ x : ℝ, K x * Real.cos (t * x) := by
  obtain ⟨k, hs, hc, he, hp, hspec, hzero⟩ := convolution_kernel
  let g := fun x : ℝ ↦ Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4)
  let K := fun x ↦ k x * g x
  have hK : ContDiff ℝ ∞ K := hs.mul (by dsimp [g]; fun_prop)
  have hKc : HasCompactSupport K := hc.mul_right
  refine ⟨K, hK, hKc, fun x ↦ by simp [K, g, he], mul_pos hp (by dsimp [g]; positivity), ?_⟩
  intro t
  rw [← transform_re hK.continuous hKc]
  change 0 < (transform (fun x ↦ k x * (Real.sqrt Real.pi * Real.exp (-(x ^ 2) / 4))) t).re
  rw [gaussian_average hs.continuous hc]
  have cont : Continuous (fun u : ℝ ↦ transform k (t + u)) :=
    (transform_continuous hs.continuous hc).comp (continuous_const.add continuous_id)
  have hi : Integrable (fun u : ℝ ↦ (Real.exp (-(u ^ 2)) : ℂ) * transform k (t + u)) := by
    have hg : Integrable (fun u : ℝ ↦ Real.exp (-(u ^ 2))) := by
      simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
    apply (hg.mul_const (∫ x : ℝ, ‖k x‖)).mono'
    · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul cont).aestronglyMeasurable
    · filter_upwards with u
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply (norm_integral_le_integral_norm _).trans_eq
      simp [phase_norm]
  rw [← RCLike.re_eq_complex_re, ← integral_re hi, RCLike.re_eq_complex_re]
  simp only [Complex.re_ofReal_mul]
  apply integral_pos_of_integrable_nonneg_ne_zero (x := -t)
  · exact (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (-(u ^ 2)))).mul (Complex.continuous_re.comp cont)
  · simpa only [RCLike.re_eq_complex_re, Complex.re_ofReal_mul] using hi.re
  · exact fun u ↦ mul_nonneg (Real.exp_pos _).le (hspec _)
  · simp [hzero.ne']

private theorem laplace_re_even {K : ℝ → ℝ} (hs : Continuous K) (hc : HasCompactSupport K)
    (he : ∀ x, K (-x) = K x) (a t : ℝ) :
    (bilateralLaplace (fun x ↦ (K x : ℂ)) ((a : ℂ) + (t : ℂ) * Complex.I)).re =
      ∫ x : ℝ, K x * Real.cosh (a*x) * Real.cos (t*x) := by
  let P := fun x : ℝ ↦ K x * Real.exp (a*x) * Real.cos (t*x)
  let Q := fun x : ℝ ↦ K x * Real.exp (-(a*x)) * Real.cos (t*x)
  have hp : Integrable P := (hs.mul (by fun_prop) |>.mul (by fun_prop)).integrable_of_hasCompactSupport
    hc.mul_right.mul_right
  have hq : Integrable Q := (hs.mul (by fun_prop) |>.mul (by fun_prop)).integrable_of_hasCompactSupport
    hc.mul_right.mul_right
  have hsub : (∫ x, Q x) = ∫ x, P x := by
    rw [← integral_neg_eq_self P]
    simp [P, Q, he, mul_neg]
  have hint : Integrable (fun x : ℝ ↦ (K x : ℂ) *
      Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * x)) :=
    ((Complex.continuous_ofReal.comp hs).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hc.comp_left Complex.ofReal_zero).mul_right)
  have hz : (bilateralLaplace (fun x ↦ (K x : ℂ)) ((a : ℂ) + (t : ℂ) * Complex.I)).re =
      ∫ x : ℝ, P x := by
    rw [bilateralLaplace, ← RCLike.re_eq_complex_re, ← integral_re hint, RCLike.re_eq_complex_re]
    simp [P, Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_assoc]
  rw [hz]
  calc ∫ x : ℝ, P x = ((∫ x : ℝ, P x) + ∫ x : ℝ, Q x) / 2 := by rw [hsub]; ring
    _ = ∫ x : ℝ, (P x + Q x) / 2 := by rw [← integral_add hp hq, integral_div]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [P, Q, Real.cosh_eq]
      ring

/-- For every half-width, there is a real even smooth compact test with positive real
bilateral Laplace transform along both vertical boundary lines at every ordinate.
The same compact numerator works for all widths. -/
theorem exists_compact_positive_laplace_edges :
    ∃ K : ℝ → ℝ, ContDiff ℝ ∞ K ∧ HasCompactSupport K ∧ (∀ x, K (-x) = K x) ∧
      0 < K 0 ∧ ∀ b : ℝ,
        let H := fun x : ℝ ↦ K x / Real.cosh (b*x)
        ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ (∀ x, H (-x) = H x) ∧
          ∀ a : ℝ, |a| = |b| → ∀ t : ℝ,
            0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) ((a : ℂ) + (t : ℂ) * Complex.I)).re := by
  obtain ⟨K, hs, hc, he, h₀, hpos⟩ := exists_compact_pos_cosineTransform
  refine ⟨K, hs, hc, he, h₀, fun b ↦ ?_⟩
  let H := fun x : ℝ ↦ K x / Real.cosh (b*x)
  have hHs : ContDiff ℝ ∞ H := hs.div (by simp only [Real.cosh_eq]; fun_prop) (fun _ ↦ (Real.cosh_pos _).ne')
  have hHc : HasCompactSupport H := by
    simp only [H, div_eq_mul_inv]; exact hc.mul_right
  have hHe (x : ℝ) : H (-x) = H x := by simp [H, he]
  refine ⟨hHs, hHc, hHe, fun a hab t ↦ ?_⟩
  rw [laplace_re_even hHs.continuous hHc hHe]
  have hcosh (x : ℝ) : Real.cosh (a*x) = Real.cosh (b*x) := by
    rcases abs_eq_abs.mp hab with h | h
    · rw [h]
    · rw [h, neg_mul, Real.cosh_neg]
  simpa only [H, hcosh, div_mul_cancel₀ _ (Real.cosh_pos _).ne'] using hpos t

private theorem bilateralLaplace_strip_bound {H : ℝ → ℂ} (hs : Continuous H)
    (hc : HasCompactSupport H) (B : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, |w.re| ≤ B → ‖bilateralLaplace H w‖ ≤ C := by
  let u := fun x : ℝ ↦ ‖H x‖ * Real.exp (B * |x|)
  have hu : Integrable u := (hs.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hc.norm.mul_right
  refine ⟨∫ x : ℝ, u x, fun w hw ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  have hi : Integrable (fun x : ℝ ↦ H x * Complex.exp (w*x)) :=
    (hs.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  apply integral_mono hi.norm hu
  intro x
  change ‖H x * Complex.exp (w * x)‖ ≤ ‖H x‖ * Real.exp (B * |x|)
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [show (w * x).re = w.re * x by simp]
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hw (abs_nonneg x)))

/-- Nonnegative boundary values and one strictly positive boundary value give strict
positivity everywhere inside the strip. -/
theorem bilateralLaplace_re_pos_of_nonneg_edges {H : ℝ → ℂ} (hs : Continuous H)
    (hc : HasCompactSupport H) {B : ℝ} (hB : 0 < B)
    (hedge : ∀ w : ℂ, |w.re| = B → 0 ≤ (bilateralLaplace H w).re)
    (hpos : ∃ z : ℂ, 0 < (bilateralLaplace H z).re)
    (w : ℂ) (hw : |w.re| < B) : 0 < (bilateralLaplace H w).re := by
  let L := bilateralLaplace H
  let f := fun z : ℂ ↦ Complex.exp (-L z)
  have dL : Differentiable ℂ L := by
    intro z
    let a := |z.re| + 1
    have hcont : Continuous (fun x : ℝ ↦ Real.exp (a * |x|) • H x) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).smul hs
    have hcomp : HasCompactSupport (fun x : ℝ ↦ Real.exp (a * |x|) • H x) :=
      HasCompactSupport.smul_left (f := fun x : ℝ ↦ Real.exp (a * |x|)) hc
    exact (hasDerivAt_bilateralLaplace (hcont.memLp_of_hasCompactSupport hcomp)
      (show |z.re| < a by dsimp [a]; linarith)).differentiableAt
  have df : Differentiable ℂ f := Complex.differentiable_exp.comp dL.neg
  have hn (z : ℂ) : ‖f z‖ = Real.exp (-(L z).re) := by simp [f, Complex.norm_exp]
  have he (z : ℂ) (heq : |z.re| = B) : ‖f z‖ ≤ 1 := by
    rw [hn, Real.exp_le_one_iff]; exact neg_nonpos.mpr (hedge z heq)
  obtain ⟨C, hC⟩ := bilateralLaplace_strip_bound hs hc B
  have hbound : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip (-B) B) := by
    refine ⟨Real.exp C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖f z‖ ≤ _
    rw [hn, Real.exp_le_exp]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hC z (abs_le.mpr hz)))
  have hnle (z : ℂ) (hz : |z.re| ≤ B) : ‖f z‖ ≤ 1 := by
    have hx := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := f) (a := 1) (b := 1) (neg_lt_self hB) (abs_le.mp hz) df.diffContOnCl hbound
      (fun u hu ↦ he u (by change u.re = -B at hu; rw [hu, abs_neg, abs_of_pos hB]))
      (fun u hu ↦ he u (by change u.re = B at hu; rw [hu, abs_of_pos hB]))
    simpa using hx
  by_contra! hne
  have h₁ : ‖f w‖ = 1 := le_antisymm (hnle w hw.le) (by rw [hn, Real.one_le_exp_iff]; exact neg_nonneg.mpr hne)
  have hmax : IsLocalMax (norm ∘ f) w := by
    have hopen : IsOpen {z : ℂ | |z.re| < B} := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
    filter_upwards [hopen.mem_nhds hw] with z hz
    change ‖f z‖ ≤ ‖f w‖
    rw [h₁]; exact hnle z hz.le
  have hloc := Complex.eventually_eq_of_isLocalMax_norm (Filter.Eventually.of_forall df) hmax
  have ha : AnalyticOnNhd ℂ f univ := fun z _ ↦ df.analyticAt z
  have hconst : f = fun _ ↦ f w := ha.eq_of_eventuallyEq analyticOnNhd_const hloc
  obtain ⟨z, hz⟩ := hpos
  have hb : ‖f z‖ < 1 := by rw [hn, Real.exp_lt_one_iff]; exact neg_lt_zero.mpr hz
  rw [congrFun hconst z, h₁] at hb
  exact (lt_irrefl _ hb)

/-- Strict positivity on both edges propagates throughout the closed strip. -/
theorem bilateralLaplace_re_pos_of_pos_on_edges {H : ℝ → ℂ} (hs : Continuous H)
    (hc : HasCompactSupport H) {B : ℝ} (hB : 0 < B)
    (hedge : ∀ w : ℂ, |w.re| = B → 0 < (bilateralLaplace H w).re)
    (w : ℂ) (hw : |w.re| ≤ B) : 0 < (bilateralLaplace H w).re := by
  rcases hw.lt_or_eq with h | h
  · exact bilateralLaplace_re_pos_of_nonneg_edges hs hc hB (fun z hz ↦ (hedge z hz).le)
      ⟨B, hedge B (by simp [abs_of_pos hB])⟩ w h
  · exact hedge w h

/-- One real even compact smooth test has strictly positive real Laplace transform at
every point of a prescribed closed vertical strip, simultaneously at all widths and heights. -/
theorem exists_compact_positive_laplace_strip {B : ℝ} (hB : 0 < B) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ (∀ x, H (-x) = H x) ∧
      0 < H 0 ∧ ∀ w : ℂ, |w.re| ≤ B →
        0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) w).re := by
  obtain ⟨K, -, -, -, h₀, hK⟩ := exists_compact_positive_laplace_edges
  obtain ⟨hs, hc, he, hp⟩ := hK B
  refine ⟨_, hs, hc, he, by simpa using h₀, ?_⟩
  apply bilateralLaplace_re_pos_of_pos_on_edges (Complex.continuous_ofReal.comp hs.continuous)
    (hc.comp_left Complex.ofReal_zero) hB
  intro w hw
  have h := hp w.re (hw.trans (abs_of_pos hB).symm) w.im
  rwa [Complex.re_add_im] at h

private theorem cosine_second_difference (K : ℝ → ℝ) (hs : Continuous K) (hc : HasCompactSupport K)
    (t : ℝ) :
    (∫ x : ℝ, (2 * K x - K (x-1) - K (x+1)) * Real.cos (t*x)) =
      (2 * (1 - Real.cos t)) * ∫ x : ℝ, K x * Real.cos (t*x) := by
  have hi (d : ℝ) : Integrable (fun x : ℝ ↦ K (x+d) * Real.cos (t*x)) :=
    ((hs.comp (continuous_id.add continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hc.comp_homeomorph (Homeomorph.addRight d)).mul_right)
  have hj (d : ℝ) : Integrable (fun x : ℝ ↦ K x * Real.cos (t*(x+d))) :=
    (hs.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have hshift (d : ℝ) : (∫ x : ℝ, K (x+d) * Real.cos (t*x)) =
      ∫ x : ℝ, K x * Real.cos (t*(x-d)) := by
    have h := integral_add_right_eq_self (μ := volume) (fun x : ℝ ↦ K x * Real.cos (t*(x-d))) d
    simpa using h
  have hi₀ : Integrable (fun x : ℝ ↦ K x * Real.cos (t*x)) := by simpa using hi 0
  have hm : Integrable (fun x : ℝ ↦ K (x-1) * Real.cos (t*x)) := by simpa [sub_eq_add_neg] using hi (-1)
  have hdiff : Integrable (fun x : ℝ ↦ 2*(K x*Real.cos (t*x)) - K (x-1)*Real.cos (t*x)) :=
    (hi₀.const_mul 2).sub hm
  simp_rw [sub_mul, mul_assoc]
  rw [integral_sub hdiff (hi 1), integral_sub (hi₀.const_mul 2) hm, integral_const_mul]
  rw [show (fun x : ℝ ↦ K (x-1) * Real.cos (t*x)) = (fun x ↦ K (x+(-1)) * Real.cos (t*x)) by
    simp only [sub_eq_add_neg], hshift (-1), hshift 1]
  simp_rw [sub_neg_eq_add]
  have hsum : (∫ x : ℝ, K x * Real.cos (t*(x+1))) + (∫ x : ℝ, K x * Real.cos (t*(x-1))) =
      (2 * Real.cos t) * ∫ x : ℝ, K x * Real.cos (t*x) := by
    rw [← integral_add (hj 1) (by simpa [sub_eq_add_neg] using hj (-1)), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [mul_add, mul_sub, mul_one, Real.cos_add, Real.cos_sub]
    ring
  linear_combination -hsum

/-- A single real even smooth compact test cancels the two real polar moments and
has strictly positive real Laplace transform at every point of the open strip between them. -/
theorem exists_compact_polar_free_positive_laplace_strip {B : ℝ} (hB : 0 < B) :
    ∃ H : ℝ → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ (∀ x, H (-x) = H x) ∧
      bilateralLaplace (fun x ↦ (H x : ℂ)) B = 0 ∧ bilateralLaplace (fun x ↦ (H x : ℂ)) (-B) = 0 ∧
      ∀ w : ℂ, |w.re| < B → 0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) w).re := by
  obtain ⟨K, hs, hc, he, -, hpos⟩ := exists_compact_pos_cosineTransform
  let P := fun x : ℝ ↦ 2 * K x - K (x-1) - K (x+1)
  let H := fun x : ℝ ↦ P x / Real.cosh (B*x)
  have hPs : ContDiff ℝ ∞ P := ((contDiff_const.mul hs).sub
    (hs.comp (contDiff_id.sub contDiff_const))).sub (hs.comp (contDiff_id.add contDiff_const))
  have hPc : HasCompactSupport P := ((hc.mul_left).sub (hc.comp_homeomorph (Homeomorph.subRight 1))).sub
    (hc.comp_homeomorph (Homeomorph.addRight 1))
  have hHs : ContDiff ℝ ∞ H := hPs.div (by simp only [Real.cosh_eq]; fun_prop) (fun _ ↦ (Real.cosh_pos _).ne')
  have hHc : HasCompactSupport H := by simp only [H, div_eq_mul_inv]; exact hPc.mul_right
  have hHe (x : ℝ) : H (-x) = H x := by
    simp only [H, P, he, mul_neg, Real.cosh_neg, show -x - 1 = -(x+1) by ring,
      show -x + 1 = -(x-1) by ring]
    ring
  let L := bilateralLaplace (fun x ↦ (H x : ℂ))
  have edge (a t : ℝ) (hab : |a| = B) :
      (L ((a : ℂ) + t * Complex.I)).re = 2*(1-Real.cos t) * ∫ x : ℝ, K x * Real.cos (t*x) := by
    have hcosh (x : ℝ) : Real.cosh (a*x) = Real.cosh (B*x) := by
      rcases abs_eq_abs.mp (hab.trans (abs_of_pos hB).symm) with h | h
      · rw [h]
      · rw [h, neg_mul, Real.cosh_neg]
    rw [show (L ((a : ℂ) + t * Complex.I)).re = _ from laplace_re_even hHs.continuous hHc hHe a t]
    simpa only [H, hcosh, div_mul_cancel₀ _ (Real.cosh_pos _).ne'] using cosine_second_difference K hs.continuous hc t
  have polar (a : ℝ) (ha : |a| = B) : L a = 0 := by
    apply Complex.ext
    · simpa using edge a 0 ha
    · change (∫ x : ℝ, (H x : ℂ) * Complex.exp ((a : ℂ) * x)).im = _
      have h : (fun x : ℝ ↦ (H x : ℂ) * Complex.exp ((a : ℂ) * x)) =
          (fun x : ℝ ↦ ((H x * Real.exp (a*x) : ℝ) : ℂ)) := by
        funext x; push_cast; rfl
      rw [h, integral_complex_ofReal]; simp
  refine ⟨H, hHs, hHc, hHe, polar B (abs_of_pos hB), by simpa using polar (-B) (by simp [abs_of_pos hB]), ?_⟩
  apply bilateralLaplace_re_pos_of_nonneg_edges (Complex.continuous_ofReal.comp hHs.continuous)
    (hHc.comp_left Complex.ofReal_zero) hB
  · intro w hw
    have h := edge w.re w.im hw
    rw [Complex.re_add_im] at h
    change 0 ≤ (L w).re
    rw [h]
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one _))) (hpos _).le
  · refine ⟨(B : ℂ) + Real.pi * Complex.I, ?_⟩
    change 0 < (L _).re
    rw [edge B Real.pi (abs_of_pos hB), Real.cos_pi]
    exact mul_pos (by norm_num) (hpos _)

end RiemannMasullo
