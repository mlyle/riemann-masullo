module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Function.Floor

/-! # A compensated rational prime statistic

For the exterior-zero problem in Theorem 12.5.1.1, pp. 519–520, a bound on one
signed prime sum continues a combination of five translates of the genuine
pole-corrected Riemann zeta logarithmic derivative from its Euler half-plane.
-/

public noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction

namespace RiemannMasullo

/-- The two-frequency nonnegative weight in logarithmic norm coordinates. -/
def rationalPrimeCosineWeight (x : ℝ) : ℝ :=
  2 - Real.cos x - Real.cos (Real.sqrt 2 * x)

/-- The prime sum for the two-frequency weight, with a unit mass subtracted
at each positive integer up to the same cutoff. -/
def rationalCompensatedPrimeError (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ((if n.Prime then Real.log n else 0) - 1) *
    rationalPrimeCosineWeight (Real.log n)

private def fourShift (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  2 * f z - (f (z + Complex.I) + f (z - Complex.I) +
    f (z + (Real.sqrt 2 : ℂ) * Complex.I) + f (z - (Real.sqrt 2 : ℂ) * Complex.I)) / 2

/-- The four shifts of the negative logarithmic derivative of zeta after
removing its pole at one, in the normalization of the cosine weight. -/
def rationalCompensatedZetaLogDeriv (z : ℂ) : ℂ :=
  fourShift (fun w ↦ -logDeriv riemannZeta w - 1 / (w - 1)) z

private def mangoldtError (n : ℕ) : ℂ :=
  ((vonMangoldt n - 1) * rationalPrimeCosineWeight (Real.log n) : ℝ)

private theorem rationalPrimeCosineWeight_bounds (x : ℝ) :
    0 ≤ rationalPrimeCosineWeight x ∧ rationalPrimeCosineWeight x ≤ 4 := by
  unfold rationalPrimeCosineWeight
  constructor <;> linarith [Real.cos_le_one x, Real.cos_le_one (Real.sqrt 2*x),
    Real.neg_one_le_cos x, Real.neg_one_le_cos (Real.sqrt 2*x)]


private theorem mangoldt_partial_error (N : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 N, mangoldtError n) - (rationalCompensatedPrimeError N : ℂ)‖
      ≤ 4 * (Chebyshev.psi N - Chebyshev.theta N) := by
  let p (n : ℕ) := if n.Prime then Real.log n else 0
  have hi (n : ℕ) : 0 ≤ vonMangoldt n - p n := by
    by_cases h : n.Prime
    · simp [p, h, vonMangoldt_apply_prime h]
    · simp [p, h, vonMangoldt_nonneg]
  have hsum : (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n - p n)) =
      Chebyshev.psi N - Chebyshev.theta N := by
    rw [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Finset.sum_filter]
    simp only [Nat.floor_natCast, p]
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N by ext n; simp; omega]
  have hdiff : (∑ n ∈ Finset.Icc 1 N, mangoldtError n) - (rationalCompensatedPrimeError N : ℂ) =
      ((∑ n ∈ Finset.Icc 1 N, (vonMangoldt n - p n) * rationalPrimeCosineWeight (Real.log n) : ℝ) : ℂ) := by
    simp only [mangoldtError, rationalCompensatedPrimeError, Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [p]
    ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (Finset.sum_nonneg fun n _ ↦ mul_nonneg (hi n) (rationalPrimeCosineWeight_bounds _).1)]
  rw [← hsum, Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ ↦ by
    exact (mul_le_mul_of_nonneg_left (rationalPrimeCosineWeight_bounds _).2 (hi n)).trans_eq (mul_comm _ _)


private theorem mangoldt_partial_bound {r : ℝ} (hr : 1 / 2 ≤ r) {C : ℝ}
    (hC : ∀ n : ℕ, |rationalCompensatedPrimeError n| ≤ C * (n : ℝ) ^ r) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, mangoldtError k‖ ≤ D * (n : ℝ) ^ r := by
  obtain ⟨B, hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0 + 4 * max B 0, by positivity, fun n ↦ ?_⟩
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, norm_zero, Nat.cast_zero]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : Real.sqrt n ≤ (n : ℝ) ^ r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hr
  have hp := (mangoldt_partial_error n).trans (mul_le_mul_of_nonneg_left (hB n) (by norm_num))
  calc
    _ ≤ ‖(∑ k ∈ Finset.Icc 1 n, mangoldtError k) - (rationalCompensatedPrimeError n : ℂ)‖ +
        ‖(rationalCompensatedPrimeError n : ℂ)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        ((∑ k ∈ Finset.Icc 1 n, mangoldtError k) - (rationalCompensatedPrimeError n : ℂ))
        (rationalCompensatedPrimeError n : ℂ)
    _ ≤ 4 * (B * Real.sqrt n) + C * (n : ℝ) ^ r :=
      add_le_add hp (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC n)
    _ ≤ 4 * (max B 0 * (n : ℝ) ^ r) + max C 0 * (n : ℝ) ^ r := by
      gcongr <;> simp
    _ = _ := by ring


private theorem cosine_term_pair (a : ℕ → ℂ) (z : ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term a z n * (2 * (Real.cos (t * Real.log n) : ℂ)) =
      LSeries.term a (z + (t : ℂ)*Complex.I) n +
        LSeries.term a (z - (t : ℂ)*Complex.I) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_of_ne_zero hn, div_eq_mul_inv, Complex.cpow_def_of_ne_zero hn',
    ← Complex.natCast_log, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos, Complex.ofReal_mul]
  let l : ℂ := Real.log n
  change a n * Complex.exp (-(l*z)) * (2 * ((Complex.exp ((t:ℂ)*l*Complex.I) +
    Complex.exp (-((t:ℂ)*l)*Complex.I))/2)) =
    a n * Complex.exp (-(l*(z+(t:ℂ)*Complex.I))) +
    a n * Complex.exp (-(l*(z-(t:ℂ)*Complex.I)))
  rw [show -(l*(z+(t:ℂ)*Complex.I)) = -(l*z) + -((t:ℂ)*l)*Complex.I by ring,
    show -(l*(z-(t:ℂ)*Complex.I)) = -(l*z) + (t:ℂ)*l*Complex.I by ring,
    Complex.exp_add, Complex.exp_add]
  ring


private theorem mangoldt_error_series {z : ℂ} (hz : 1 < z.re) :
    LSeriesHasSum mangoldtError z (fourShift (fun w ↦ -logDeriv riemannZeta w - riemannZeta w) z) := by
  let a : ℕ → ℂ := (fun n ↦ (vonMangoldt n : ℂ)) - 1
  let F := fun w ↦ -logDeriv riemannZeta w - riemannZeta w
  have h (w : ℂ) (hw : 1 < w.re) : HasSum (LSeries.term a w) (F w) := by
    have hΛ := (LSeriesSummable_vonMangoldt hw).LSeriesHasSum
    have h1 := (LSeriesSummable_one_iff.mpr hw).LSeriesHasSum
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw] at hΛ
    rw [LSeries_one_eq_riemannZeta hw] at h1
    change LSeriesHasSum ((fun n ↦ (vonMangoldt n : ℂ)) - 1) w _
    simpa only [F, logDeriv_apply, neg_div] using LSeriesHasSum.sub hΛ h1
  have hpair (t : ℝ) :
      HasSum (fun n ↦ LSeries.term a z n * (2 * (Real.cos (t * Real.log n) : ℂ)))
        (F (z+(t:ℂ)*Complex.I) + F (z-(t:ℂ)*Complex.I)) := by
    simp_rw [cosine_term_pair]
    exact (h _ (by simpa using hz)).add (h _ (by simpa using hz))
  have hall := ((h z hz).mul_left 2).sub (((hpair 1).add (hpair (Real.sqrt 2))).mul_right (2:ℂ)⁻¹)
  change HasSum _ _
  convert hall using 1
  · funext n
    by_cases hn : n = 0
    · simp [hn]
    simp only [LSeries.term_of_ne_zero hn, mangoldtError, a, rationalPrimeCosineWeight,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one,
      Pi.sub_apply, Pi.one_apply, one_mul]
    ring
  · dsimp [fourShift, F]
    norm_num
    ring


private theorem pole_removed_zeta :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ ∀ w : ℂ, w ≠ 1 → Z w = riemannZeta w - 1 / (w-1) := by
  classical
  let f := Function.update (fun w : ℂ ↦ (w-1)*riemannZeta w) 1 1
  have hoff {w : ℂ} (hw : w ≠ 1) : DifferentiableAt ℂ f w := by
    apply DifferentiableAt.congr_of_eventuallyEq (((differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hw)))
    filter_upwards [eventually_ne_nhds hw] with z hz using Function.update_of_ne hz ..
  have hf : Differentiable ℂ f := by
    intro w
    obtain h | rfl := ne_or_eq w 1
    · exact hoff h
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz using hoff hz
    · simpa only [f,continuousAt_update_same] using riemannZeta_residue_one
  refine ⟨dslope f 1, fun w ↦ ((hf.analyticAt w).dslope 1).differentiableAt, fun w hw ↦ ?_⟩
  rw [dslope_of_ne f hw]
  simp only [slope, smul_eq_mul, f, Function.update_of_ne hw, Function.update_self]
  simp only [vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hw]


private def abelStep (a : ℕ → ℂ) : ℝ → ℂ :=
  (Ioi 1).indicator fun x : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

private def abelValue (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  z * mellin (abelStep a) (-z)

private theorem abelValue_analyticAt (a : ℕ → ℂ) {r D : ℝ} (hr : 0 ≤ r) (hD : 0 ≤ D)
    (h : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ D * (n : ℝ) ^ r)
    {z : ℂ} (hz : r < z.re) : AnalyticAt ℂ (abelValue a) z := by
  have hm : Measurable (abelStep a) :=
    ((measurable_of_countable (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k)).comp
      measurable_id.nat_floor).indicator measurableSet_Ioi
  have hbd (x : ℝ) (hx₀ : 0 ≤ x) : ‖abelStep a x‖ ≤ D * x ^ r := by
    by_cases hx : x ∈ Ioi (1:ℝ)
    · rw [abelStep, indicator_of_mem hx]
      exact (h _).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith [show 1 < x from hx])) hr) hD)
    · rw [abelStep, indicator_of_notMem hx, norm_zero]
      positivity
  have hloc : LocallyIntegrableOn (abelStep a) (Ioi 0) := by
    have hc : Continuous (fun x : ℝ ↦ D * x ^ r) := continuous_const.mul (Real.continuous_rpow_const hr)
    apply (hc.locallyIntegrable.locallyIntegrableOn (Ioi 0)).mono hm.aestronglyMeasurable
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · exact (hbd x hx).trans (Real.le_norm_self _)
    · have hnot : x ∉ Ioi (1:ℝ) := by simpa using (show ¬ 1 < x by linarith)
      rw [abelStep, indicator_of_notMem hnot, norm_zero]
      exact norm_nonneg _
  have ht : abelStep a =O[atTop] (fun x : ℝ ↦ x ^ (-(-r))) := by
    refine Asymptotics.isBigO_iff.mpr ⟨D, ?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg hx r)] using hbd x hx
  have hb (b : ℝ) : abelStep a =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨0, ?_⟩
    filter_upwards [(eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x hx
    simp [abelStep, not_lt.mpr (le_of_lt hx)]
  have hDiff : DifferentiableOn ℂ (abelValue a) {w : ℂ | r < w.re} := by
    intro w hw
    have hM := mellin_differentiableAt_of_isBigO_rpow hloc ht
      (by simp only [Complex.neg_re]; linarith [show r < w.re from hw] : (-w).re < -r)
      (hb ((-w).re - 1)) (by linarith)
    exact (differentiableAt_id.fun_mul (hM.comp w differentiableAt_id.neg)).differentiableWithinAt
  exact hDiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re) z hz


private theorem abelValue_eq (a : ℕ → ℂ) {r D : ℝ} (hr : 0 ≤ r)
    (h : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ D * (n : ℝ) ^ r)
    {z : ℂ} (hz : r < z.re) (hs : LSeriesSummable a z) : abelValue a z = LSeries a z := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ r := by
    exact Asymptotics.isBigO_iff.mpr ⟨D, Eventually.of_forall fun n ↦ by
      simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)] using h n⟩
  rw [LSeries_eq_mul_integral a hr hz hs hO, abelValue]
  congr 1
  have he (x : ℝ) : (x : ℂ) ^ (-z - 1) • abelStep a x =
      (Ioi 1).indicator (fun y : ℝ ↦ (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, a k) * (y : ℂ) ^ (-(z+1))) x := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [abelStep, indicator_of_mem hx, smul_eq_mul]
      rw [show -z - 1 = -(z+1) by ring, mul_comm]
    · simp [abelStep, hx]
  simp only [mellin, he, integral_indicator measurableSet_Ioi]
  rw [Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]


/-- For the rational trivial chart of Theorem 12.5.1.1, pp. 519–520, if the signed
two-frequency prime counting error grows at most as every power above σ, then the
four-shift pole-corrected zeta logarithmic derivative continues holomorphically from
its Euler half-plane to Re z > σ. Prime powers above the first cost only O(√N). -/
theorem rationalCompensatedZetaLogDeriv_continuation_of_primeError {σ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ < 1)
    (hp : ∀ r : ℝ, σ < r → ∃ C : ℝ, ∀ n : ℕ,
      |rationalCompensatedPrimeError n| ≤ C * (n : ℝ) ^ r) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {z : ℂ | σ < z.re} ∧
      ∀ z : ℂ, 1 < z.re → G z = rationalCompensatedZetaLogDeriv z := by
  obtain ⟨Z, hZ, hZe⟩ := pole_removed_zeta
  refine ⟨fun z ↦ abelValue mangoldtError z + fourShift Z z, ?_, ?_⟩
  · intro z hz
    obtain ⟨r, hσr, hrz⟩ := exists_between (show σ < z.re from hz)
    obtain ⟨C, hC⟩ := hp r hσr
    obtain ⟨D, hD, hbd⟩ := mangoldt_partial_bound (hσ.trans hσr.le) hC
    have hfour : Differentiable ℂ (fourShift Z) := by
      unfold fourShift
      fun_prop
    exact (abelValue_analyticAt mangoldtError (by linarith) hD hbd hrz).add (hfour.analyticAt z)
  · intro z hz
    obtain ⟨r, hσr, hr₁⟩ := exists_between hσ₁
    obtain ⟨C, hC⟩ := hp r hσr
    obtain ⟨D, -, hbd⟩ := mangoldt_partial_bound (hσ.trans hσr.le) hC
    have hs := mangoldt_error_series hz
    change abelValue mangoldtError z + fourShift Z z = _
    rw [abelValue_eq mangoldtError (by linarith) hbd (hr₁.trans hz) hs.LSeriesSummable, hs.LSeries_eq]
    have hne (w : ℂ) (hw : 1 < w.re) : w ≠ 1 := fun he ↦ by simp [he] at hw
    simp only [rationalCompensatedZetaLogDeriv, fourShift]
    rw [hZe _ (hne _ hz), hZe _ (hne _ (by simpa using hz)), hZe _ (hne _ (by simpa using hz)),
      hZe _ (hne _ (by simpa using hz)), hZe _ (hne _ (by simpa using hz))]
    ring



private theorem primeCosineWeight_lipschitz (x y : ℝ) :
    |rationalPrimeCosineWeight x - rationalPrimeCosineWeight y| ≤ (1+Real.sqrt 2) * |x-y| := by
  have h := Real.abs_cos_sub_cos_le (Real.sqrt 2*x) (Real.sqrt 2*y)
  rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)] at h
  rw [rationalPrimeCosineWeight, rationalPrimeCosineWeight,
    show 2 - Real.cos x - Real.cos (Real.sqrt 2*x) - (2 - Real.cos y - Real.cos (Real.sqrt 2*y)) =
      -((Real.cos x - Real.cos y) + (Real.cos (Real.sqrt 2*x)-Real.cos (Real.sqrt 2*y))) by ring,
    abs_neg, add_mul, one_mul]
  exact (abs_add_le ..).trans (add_le_add (Real.abs_cos_sub_cos_le x y) h)


/-- The discrete mean differs from the continuous mean on [1,N] by at most
(1+√2) log N, so the two choices give the same exponent threshold. -/
theorem rationalPrimeCosineWeight_discrete_mean_error (N : ℕ) (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Icc 1 N, rationalPrimeCosineWeight (Real.log n)) -
      ∫ x in (1 : ℝ)..N, rationalPrimeCosineWeight (Real.log x)| ≤
        (1+Real.sqrt 2) * Real.log N := by
  let f (x : ℝ) := rationalPrimeCosineWeight (Real.log x)
  have hInt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    unfold f rationalPrimeCosineWeight
    have hl : ContinuousOn Real.log (Icc a b) := Real.continuousOn_log.mono fun x hx ↦ (ha.trans_le hx.1).ne'
    exact (continuousOn_const.sub (Real.continuous_cos.comp_continuousOn hl)).sub
      (Real.continuous_cos.comp_continuousOn (continuousOn_const.mul hl))
  induction N, hN using Nat.le_induction with
  | base => norm_num [rationalPrimeCosineWeight]
  | succ n hn ih =>
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h0 : (0 : ℝ) < n := by linarith
    have hup : (n : ℝ) ≤ (n+1 : ℝ) := by linarith
    have hb : |f (n+1) - ∫ x in (n:ℝ)..(n+1), f x| ≤
        (1+Real.sqrt 2)*(Real.log (n+1) - Real.log n) := by
      let C := (1+Real.sqrt 2)*(Real.log (n+1) - Real.log n)
      have he : (∫ x in (n:ℝ)..(n+1), f (n+1) - f x) = f (n+1) - ∫ x in (n:ℝ)..(n+1), f x := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (hInt h0 hup), intervalIntegral.integral_const]
        simp
      rw [← he, ← Real.norm_eq_abs]
      apply (intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x : ℝ ↦ f (n+1) - f x) (C := C) ?_).trans_eq
      · simp [C]
      · intro x hx
        rw [uIoc_of_le hup] at hx
        have hlog := Real.log_le_log (h0.trans hx.1) hx.2
        apply (primeCosineWeight_lipschitz _ _).trans
        rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
        dsimp [C]
        gcongr
        exact hx.1.le
    change |(∑ k ∈ Finset.Icc 1 (n+1), f k) - ∫ x in (1:ℝ)..(↑(n+1 : ℕ):ℝ), f x| ≤ _
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1), Nat.cast_add_one,
      ← intervalIntegral.integral_add_adjacent_intervals (hInt zero_lt_one h1) (hInt h0 hup)]
    have hcalc := (abs_add_le
      ((∑ k ∈ Finset.Icc 1 n, f k) - ∫ x in (1:ℝ)..n, f x)
      (f (n+1) - ∫ x in (n:ℝ)..(n+1), f x)).trans (add_le_add ih hb)
    convert hcalc using 1 <;> congr 1 <;> ring



/-- The continuous mean version uses only first primes and the ordinary integral of
the log-norm weight. Bounds on integer cutoffs suffice for the same continuation. -/
theorem rationalCompensatedZetaLogDeriv_continuation_of_primeIntegralError {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ₁ : σ < 1)
    (hp : ∀ r : ℝ, σ < r → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with p.Prime, Real.log p * rationalPrimeCosineWeight (Real.log p)) -
        ∫ x in (1 : ℝ)..N, rationalPrimeCosineWeight (Real.log x)| ≤ C * (N : ℝ) ^ r) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {z : ℂ | σ < z.re} ∧
      ∀ z : ℂ, 1 < z.re → G z = rationalCompensatedZetaLogDeriv z := by
  apply rationalCompensatedZetaLogDeriv_continuation_of_primeError hσ hσ₁
  intro r hr
  obtain ⟨C, hC⟩ := hp r hr
  have hr₀ : 0 < r := by linarith
  refine ⟨C + (1+Real.sqrt 2)/r, fun N ↦ ?_⟩
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [rationalCompensatedPrimeError, Real.zero_rpow hr₀.ne']
  let q := ∑ p ∈ Finset.Icc 1 N with p.Prime, Real.log p * rationalPrimeCosineWeight (Real.log p)
  let m := ∑ n ∈ Finset.Icc 1 N, rationalPrimeCosineWeight (Real.log n)
  let M := ∫ x in (1 : ℝ)..N, rationalPrimeCosineWeight (Real.log x)
  have he : rationalCompensatedPrimeError N = q-m := by
    simp only [rationalCompensatedPrimeError, q, m, sub_mul, one_mul, Finset.sum_sub_distrib,
      Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  have hm : |m-M| ≤ (1+Real.sqrt 2) * ((N:ℝ)^r/r) :=
    (rationalPrimeCosineWeight_discrete_mean_error N hN).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div (Nat.cast_nonneg N) hr₀) (by positivity))
  rw [he, show q-m = (q-M) - (m-M) by ring]
  calc
    _ ≤ |q-M| + |m-M| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (q-M) (-(m-M))
    _ ≤ C*(N:ℝ)^r + (1+Real.sqrt 2)*((N:ℝ)^r/r) := add_le_add (hC N hN) hm
    _ = _ := by ring

end RiemannMasullo
