module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! # Smooth compact profiles positive on two vertical lines

A Gaussian times the autocorrelation of an even bump has strictly positive cosine transform
at every real frequency. Dividing by a hyperbolic cosine gives one real even compact test
whose bilateral Laplace transform has positive real part on both specified edges.
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

end RiemannMasullo
