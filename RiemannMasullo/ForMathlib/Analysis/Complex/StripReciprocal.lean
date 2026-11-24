module

public import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
public import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Regularization of a zero-free reciprocal on a strip

On a strict substrip the disk Harnack inequality bounds the logarithm of the reciprocal by
a single exponential in the height. If the cutoff frequency exceeds that growth rate, the
entire multiplier `exp (−ε cos (c (z − a)))` makes the reciprocal decay at every exponential
rate while converging to one on compact sets. The two independent strip margins allow the
center of the cutoff to differ from the center of the original strip.
-/

@[expose] public noncomputable section
open Filter Function InnerProductSpace MeasureTheory Metric Real Set
open scoped Topology

namespace RiemannMasullo

/-- A positive harmonic function on the unit disk grows at most like the
reciprocal Euclidean distance to the disk boundary. -/
private theorem stripReciprocal_disk_harnack (H : ℂ → ℝ) (hH : HarmonicOnNhd H (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ H z) {z : ℂ} (hz : z ∈ ball 0 1) :
    H z ≤ (4 / (1 - ‖z‖)) * H 0 := by
  let R := (1 + ‖z‖) / 2
  have hz' : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hR : ‖z‖ < R := by dsimp [R]; linarith
  have hR' : R < 1 := by dsimp [R]; linarith
  have hR₀ : 0 < R := (norm_nonneg _).trans_lt hR
  have hzR : z ∈ ball (0 : ℂ) R := by simpa [mem_ball] using hR
  have hrH : HarmonicOnNhd H (closedBall 0 R) := hH.mono (closedBall_subset_ball hR')
  have hC : ContinuousOn H (sphere 0 |R|) := by
    rw [abs_of_pos hR₀]
    exact hrH.continuousOn.mono sphere_subset_closedBall
  let K := Complex.re ∘ herglotzRieszKernel 0 z
  let c := (R + ‖z‖) / (R - ‖z‖)
  have hK : ContinuousOn K (sphere 0 |R|) := by
    apply Complex.continuous_re.comp_continuousOn
    apply continuousOn_herglotzRieszKernel_sphere
    simpa [mem_sphere, abs_of_pos hR₀] using hR.ne
  have hav : circleAverage (K • H) 0 R ≤ circleAverage (c • H) 0 R := by
    apply circleAverage_mono (hK.smul hC).circleIntegrable' (continuousOn_const.smul hC).circleIntegrable'
    intro x hx
    have hx' : x ∈ sphere 0 R := by simpa [abs_of_pos hR₀] using hx
    have hk : K x ≤ c := by simpa [K, c, herglotzRieszKernel_def] using re_herglotzRieszKernel_le hx' hzR
    exact mul_le_mul_of_nonneg_right hk (hn x (sphere_subset_ball hR' hx'))
  have hcc : c ≤ 4 / (1 - ‖z‖) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hR) (sub_pos.mpr hz')]
    dsimp [R]
    nlinarith [sq_nonneg (1 - ‖z‖)]
  calc
    H z = _ := (hrH.circleAverage_re_herglotzRieszKernel_smul hzR).symm
    _ ≤ _ := hav
    _ = c * H 0 := by
      rw [circleAverage_smul,
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq (by simpa [abs_of_pos hR₀] using hrH)]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right hcc (hn _ (by simp))

private theorem stripReciprocal_cayley_gap {u : ℂ} (hu : 0 < u.re) :
    (1 - ‖(u - 1) / (u + 1)‖)⁻¹ ≤ (‖u‖ + 1) ^ 2 / (2 * u.re) := by
  have hsq : ‖u + 1‖ ^ 2 - ‖u - 1‖ ^ 2 = 4 * u.re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero, add_zero]
    ring
  have hp : ‖u + 1‖ ≤ ‖u‖ + 1 := by simpa using norm_add_le u 1
  have hm : ‖u - 1‖ ≤ ‖u‖ + 1 := by simpa using norm_sub_le u 1
  have hdiff : 0 < ‖u + 1‖ - ‖u - 1‖ := by
    nlinarith [norm_nonneg (u + 1), norm_nonneg (u - 1)]
  have hden : ‖u + 1‖ ≠ 0 := ((norm_nonneg (u - 1)).trans_lt (sub_pos.mp hdiff)).ne'
  have hquot : (1 - ‖(u - 1) / (u + 1)‖)⁻¹ = ‖u + 1‖ * (‖u + 1‖ + ‖u - 1‖) / (4 * u.re) := by
    rw [norm_div, show 1 - ‖u - 1‖ / ‖u + 1‖ = (‖u + 1‖ - ‖u - 1‖) / ‖u + 1‖ by field_simp [hden], inv_div]
    rw [div_eq_div_iff hdiff.ne' (mul_pos (by norm_num) hu).ne']
    nlinarith [congrArg (‖u + 1‖ * ·) hsq]
  rw [hquot, div_le_div_iff₀ (mul_pos (by norm_num) hu) (mul_pos (by norm_num) hu)]
  have hprod : ‖u + 1‖ * (‖u + 1‖ + ‖u - 1‖) ≤ (‖u‖ + 1) * ((‖u‖ + 1) + (‖u‖ + 1)) :=
    mul_le_mul hp (add_le_add hp hm) (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hprod hu.le]

/-- The conformal disk boundary is approached at exponential rate k along each
fixed narrower vertical strip. The lower angular margin enters only as a constant. -/
private theorem stripReciprocal_chart_gap (A k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d) (hkd : k * d < π / 2)
    (w : ℂ) (hw : |w.re - A| ≤ d) :
    (1 - ‖stripBlaschkeToDisk (A : ℂ) k w‖)⁻¹ ≤
      (2 / Real.cos (k * d)) * Real.exp (k * |w.im|) := by
  let t : ℂ := (k : ℂ) * (Complex.I * (w - (A : ℂ)))
  let u := Complex.exp t
  let x := Real.exp (-k * w.im)
  let E := Real.exp (k * |w.im|)
  let b := Real.cos (k * d)
  have hpos : 0 < b := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hk.le hd, pi_pos], hkd⟩
  have hre : t.re = -k * w.im := by simp [t]
  have him : t.im = k * (w.re - A) := by simp [t]
  have hθ : b ≤ Real.cos t.im := by
    rw [← Real.cos_abs t.im]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
    rw [him, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_left hw hk.le
  have hxn : ‖u‖ = x := by simp [u, Complex.norm_exp, hre, x]
  have hure : u.re = x * Real.cos t.im := by simp only [u, Complex.exp_re, hre, x]
  have hx : 0 < x := exp_pos _
  have hu : 0 < u.re := hure ▸ mul_pos hx (hpos.trans_le hθ)
  have h₁e : 1 ≤ E := Real.one_le_exp_iff.mpr (mul_nonneg hk.le (abs_nonneg _))
  have hxe : x ≤ E := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs w.im) hk.le]
  have hxi : x⁻¹ ≤ E := by
    dsimp [x]
    rw [← Real.exp_neg]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self w.im) hk.le]
  calc
    _ ≤ (‖u‖ + 1) ^ 2 / (2 * u.re) := stripReciprocal_cayley_gap hu
    _ ≤ (x + 1) ^ 2 / (2 * (x * b)) := by
      rw [hxn, hure]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by gcongr)
    _ = (x + 2 + x⁻¹) / (2 * b) := by field_simp; ring
    _ ≤ (4 * E) / (2 * b) := by gcongr; linarith
    _ = (2 / b) * E := by ring

/-- A bounded zero-free holomorphic function on a vertical strip satisfies the
Harnack bound for its log reciprocal on each strictly narrower closed strip. -/
theorem stripReciprocal_log_growth (A k d : ℝ) (hk : 0 < k) (hd : 0 ≤ d)
    (hkd : k * d < π / 2) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g {w : ℂ | |w.re - A| < (π / 2) / k})
    (hn : ∀ w : ℂ, |w.re - A| < (π / 2) / k → g w ≠ 0)
    (M : ℝ) (hb : ∀ w : ℂ, |w.re - A| < (π / 2) / k → ‖g w‖ ≤ M) :
    ∃ C ≥ 0, ∀ w : ℂ, |w.re - A| ≤ d →
      -Real.log ‖g w‖ ≤ C * Real.exp (k * |w.im|) := by
  let D := stripBlaschkeFromDisk (A : ℂ) k
  let B := stripBlaschkeToDisk (A : ℂ) k
  let G := g ∘ D
  let L := Real.log (max 1 M)
  let H (z : ℂ) := L - Real.log ‖G z‖
  have hD (z : ℂ) (hz : z ∈ ball 0 1) : |(D z).re - A| < (π / 2) / k :=
    stripBlaschkeFromDisk_mem_strip hk hz
  have hH : HarmonicOnNhd H (ball 0 1) := by
    intro z hz
    have hG : AnalyticAt ℂ G z := (hg _ (hD z hz)).comp (stripBlaschkeFromDisk_analyticAt_deriv_ne_zero hk hz).1
    exact (harmonicAt_const L).sub (hG.harmonicAt_log_norm (hn _ (hD z hz)))
  have hnn (z : ℂ) (hz : z ∈ ball 0 1) : 0 ≤ H z := by
    apply sub_nonneg.mpr
    exact Real.log_le_log (norm_pos_iff.mpr (hn _ (hD z hz)))
      ((hb _ (hD z hz)).trans (le_max_right _ _))
  have h₀ := hnn 0 (by simp)
  have hcos : 0 < Real.cos (k * d) :=
    cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hk.le hd, pi_pos], hkd⟩
  refine ⟨4 * (2 / Real.cos (k * d)) * H 0, by positivity, ?_⟩
  intro w hw
  have hw' : |w.re - A| < (π / 2) / k := (lt_div_iff₀ hk).mpr (by nlinarith [mul_le_mul_of_nonneg_left hw hk.le])
  have hz : B w ∈ ball 0 1 := stripBlaschkeToDisk_mem hk hw'
  have he : D (B w) = w := stripBlaschkeFromDisk_toDisk hk hw'
  have hL : 0 ≤ L := log_nonneg (le_max_left _ _)
  calc
    -Real.log ‖g w‖ ≤ H (B w) := by simp only [H, G, Function.comp_apply, he]; linarith
    _ ≤ (4 / (1 - ‖B w‖)) * H 0 := stripReciprocal_disk_harnack H hH hnn hz
    _ = (4 * (1 - ‖B w‖)⁻¹) * H 0 := by rw [div_eq_mul_inv]
    _ ≤ (4 * ((2 / Real.cos (k * d)) * Real.exp (k * |w.im|))) * H 0 := by
      gcongr
      exact stripReciprocal_chart_gap A k d hk hd hkd w hw
    _ = _ := by ring

/-- Entire vertical cutoff. Its cosine has a positive real part throughout a
closed strip of half-width strictly less than π/(2c). -/
def stripReciprocalCutoff (a c ε : ℝ) (w : ℂ) : ℂ :=
  Complex.exp (-(ε : ℂ) * Complex.cos ((c : ℂ) * (w - a)))

/-- The exponential cosine cutoff is entire. -/
theorem stripReciprocalCutoff_analytic (a c ε : ℝ) (w : ℂ) :
    AnalyticAt ℂ (stripReciprocalCutoff a c ε) w := by
  unfold stripReciprocalCutoff
  fun_prop

private theorem stripReciprocal_real_cos (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]
  simp [Complex.mul_re, Complex.cos_ofReal_re]

/-- The size of the cutoff separates into a horizontal cosine and a vertical hyperbolic cosine. -/
private theorem stripReciprocalCutoff_norm (a c ε : ℝ) (w : ℂ) :
    ‖stripReciprocalCutoff a c ε w‖ =
      Real.exp (-ε * (Real.cos (c * (w.re - a)) * Real.cosh (c * w.im))) := by
  simp [stripReciprocalCutoff, Complex.norm_exp, stripReciprocal_real_cos]

private theorem stripReciprocal_cosh_lower (c t : ℝ) :
    Real.exp (c * |t|) / 2 ≤ Real.cosh (c * t) := by
  rw [Real.cosh_eq]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]; linarith [exp_pos (-(c * t))]
  · rw [abs_of_neg (lt_of_not_ge ht), mul_neg]; linarith [exp_pos (c * t)]

/-- Uniform double-exponential decay on the entire closed inner strip. In
particular each nonnegative-parameter cutoff is bounded in norm by one there. -/
theorem stripReciprocalCutoff_decay (a c r ε : ℝ) (hc : 0 < c) (hr : 0 ≤ r)
    (hcr : c * r < π / 2) (he : 0 ≤ ε) (w : ℂ) (hw : |w.re - a| ≤ r) :
    ‖stripReciprocalCutoff a c ε w‖ ≤ Real.exp (-(ε * Real.cos (c * r) / 2) * Real.exp (c * |w.im|)) := by
  have hpos : 0 < Real.cos (c * r) := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hc.le hr, pi_pos], hcr⟩
  have hcos : Real.cos (c * r) ≤ Real.cos (c * (w.re - a)) := by
    rw [← Real.cos_abs (c * (w.re - a))]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_pos])
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hw hc.le
  have hprod := mul_le_mul hcos (stripReciprocal_cosh_lower c w.im)
    (by positivity) (hpos.le.trans hcos)
  rw [stripReciprocalCutoff_norm, exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left hprod he]

/-- The cutoff is contractive on the closed target strip for every nonnegative parameter. -/
theorem stripReciprocalCutoff_norm_le_one (a c r ε : ℝ) (hc : 0 < c) (hr : 0 ≤ r)
    (hcr : c * r < π / 2) (he : 0 ≤ ε) (w : ℂ) (hw : |w.re - a| ≤ r) :
    ‖stripReciprocalCutoff a c ε w‖ ≤ 1 := by
  apply (stripReciprocalCutoff_decay a c r ε hc hr hcr he w hw).trans
  have hp : 0 < Real.cos (c * r) := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hc.le hr, pi_pos], hcr⟩
  apply exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos_of_nonneg (by positivity)) (exp_pos _).le

/-- The cutoffs tend uniformly to one on each compact set when ε tends to zero. -/
theorem stripReciprocalCutoff_tendsto_compact (a c : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (stripReciprocalCutoff a c) (fun _ ↦ 1) (𝓝 0) K := by
  let F : C(ℝ × ℂ, ℂ) := ⟨fun p ↦ stripReciprocalCutoff a c p.1 p.2, by
    unfold stripReciprocalCutoff
    fun_prop⟩
  have ht : Tendsto F.curry (𝓝 0) (𝓝 (F.curry 0)) := F.curry.continuous.continuousAt
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht K hK
  change TendstoUniformlyOn (stripReciprocalCutoff a c) (stripReciprocalCutoff a c 0) (𝓝 0) K at hu
  have heq : stripReciprocalCutoff a c 0 = fun _ ↦ 1 := by funext w; simp [stripReciprocalCutoff]
  rwa [heq] at hu

private theorem stripReciprocal_dominate (A b k c q : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hk : 0 < k) (hkc : k < c) (hq : 0 ≤ q) :
    ∃ K ≥ 0, ∀ t ≥ 0, A * Real.exp (k * t) + q * t - b * Real.exp (c * t) ≤ K := by
  let B := A + q / k
  let T := B / (b * (c - k))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbk := mul_pos hb (sub_pos.mpr hkc)
  refine ⟨B * Real.exp (k * T), by positivity, ?_⟩
  intro t ht
  have hkt : k * t ≤ Real.exp (k * t) := by linarith [Real.add_one_le_exp (k * t)]
  have htq : q * t ≤ (q / k) * Real.exp (k * t) := by
    calc
      q * t = (q / k) * (k * t) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hkt (div_nonneg hq hk.le)
  have hall : A * Real.exp (k * t) + q * t ≤ B * Real.exp (k * t) := by dsimp [B]; linarith
  by_cases hT : T ≤ t
  · have hf : B ≤ b * ((c - k) * t) := by
      have hle := (div_le_iff₀ hbk).mp hT
      linarith
    have hlin : (c - k) * t ≤ Real.exp ((c - k) * t) := by linarith [Real.add_one_le_exp ((c - k) * t)]
    have hlim := mul_le_mul_of_nonneg_right (hf.trans (mul_le_mul_of_nonneg_left hlin hb.le))
      (Real.exp_pos (k * t)).le
    have hexp : Real.exp ((c - k) * t) * Real.exp (k * t) = Real.exp (c * t) := by rw [← Real.exp_add]; congr 1; ring
    rw [mul_assoc, hexp] at hlim
    linarith [mul_nonneg hB (Real.exp_pos (k * T)).le]
  · have hlim := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_ge hT) hk.le)) hB
    linarith [mul_nonneg hb.le (Real.exp_pos (c * t)).le]

/-- The regularized reciprocal of a bounded zero-free holomorphic function
on an outer strip decays at every prescribed exponential rate throughout a
strictly interior closed strip. Outer and inner strips may have different centers.
Here k = π/(2R) for the outer half-width R. -/
theorem stripReciprocal_regularized_decay (A a k c r ε : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 ≤ r) (hwider : k * (|a - A| + r) < π / 2)
    (hcr : c * r < π / 2) (he : 0 < ε) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g {w : ℂ | |w.re - A| < (π / 2) / k})
    (hn : ∀ w : ℂ, |w.re - A| < (π / 2) / k → g w ≠ 0)
    (M : ℝ) (hb : ∀ w : ℂ, |w.re - A| < (π / 2) / k → ‖g w‖ ≤ M) :
    ∀ q ≥ 0, ∃ C > 0, ∀ w : ℂ, |w.re - a| ≤ r →
      ‖stripReciprocalCutoff a c ε w / g w‖ ≤ C * Real.exp (-q * |w.im|) := by
  obtain ⟨G, hG, hlog⟩ := stripReciprocal_log_growth A k (|a - A| + r) hk
    (add_nonneg (abs_nonneg _) hr) hwider g hg hn M hb
  have hc := hk.trans hkc
  have hcos : 0 < Real.cos (c * r) := cos_pos_of_mem_Ioo ⟨by linarith [mul_nonneg hc.le hr, pi_pos], hcr⟩
  let b := ε * Real.cos (c * r) / 2
  have hb' : 0 < b := by dsimp [b]; positivity
  intro q hq
  obtain ⟨K, _, hK⟩ := stripReciprocal_dominate G b k c q hG hb' hk hkc hq
  refine ⟨Real.exp K, exp_pos _, ?_⟩
  intro w hw
  let t := |w.im|
  have hdin : |w.re - A| ≤ |a - A| + r := by
    rw [show w.re - A = (w.re - a) + (a - A) by ring]
    exact (abs_add_le ..).trans (by linarith)
  have hs : |w.re - A| < (π / 2) / k :=
    (lt_div_iff₀ hk).mpr (by nlinarith [mul_le_mul_of_nonneg_left hdin hk.le])
  have hgpos := norm_pos_iff.mpr (hn w hs)
  have hcut := stripReciprocalCutoff_decay a c r ε hc hr hcr he.le w hw
  have hglog := hlog w hdin
  have hbound := hK t (abs_nonneg _)
  calc
    ‖stripReciprocalCutoff a c ε w / g w‖ = ‖stripReciprocalCutoff a c ε w‖ / ‖g w‖ := norm_div ..
    _ ≤ Real.exp (-b * Real.exp (c * t)) / ‖g w‖ := div_le_div_of_nonneg_right hcut hgpos.le
    _ = Real.exp (-b * Real.exp (c * t) - Real.log ‖g w‖) := by rw [Real.exp_sub, Real.exp_log hgpos]
    _ ≤ Real.exp (K + (-q * t)) := by
      apply Real.exp_le_exp.mpr
      change -Real.log ‖g w‖ ≤ G * Real.exp (k * t) at hglog
      linarith
    _ = _ := Real.exp_add ..

/-- The regularized reciprocal is holomorphic throughout the outer zero-free strip. -/
theorem stripReciprocal_regularized_analytic (A a k c ε : ℝ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g {w : ℂ | |w.re - A| < (π / 2) / k})
    (hn : ∀ w : ℂ, |w.re - A| < (π / 2) / k → g w ≠ 0) :
    AnalyticOnNhd ℂ (fun w ↦ stripReciprocalCutoff a c ε w / g w)
      {w : ℂ | |w.re - A| < (π / 2) / k} :=
  fun w hw ↦ (stripReciprocalCutoff_analytic a c ε w).div (hg w hw) (hn w hw)

/-- Removing the cutoff recovers the reciprocal pointwise. -/
theorem stripReciprocal_regularized_tendsto (a c : ℝ) (g : ℂ → ℂ) (w : ℂ) :
    Tendsto (fun ε ↦ stripReciprocalCutoff a c ε w / g w) (𝓝 0) (𝓝 (1 / g w)) := by
  have ht := (stripReciprocalCutoff_tendsto_compact a c {w} isCompact_singleton).tendsto_at (mem_singleton w)
  exact ht.div_const _

/-- Exponential bounds on a wider closed strip pass to every analytic
derivative on a narrower closed strip by the circle estimate. -/
private theorem stripReciprocal_iteratedDeriv_estimate {f : ℂ → ℂ} {a r δ q C : ℝ}
    (hδ : 0 < δ) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.re - a| ≤ r + δ})
    (hbound : ∀ z : ℂ, |z.re - a| ≤ r + δ → ‖f z‖ ≤ C * Real.exp (-q * |z.im|))
    (n : ℕ) (w : ℂ) (hw : |w.re - a| ≤ r) :
    ‖iteratedDeriv n f w‖ ≤ ((n.factorial : ℝ) * C * Real.exp (q * δ) / δ ^ n) * Real.exp (-q * |w.im|) := by
  have hstrip : closedBall w δ ⊆ {z : ℂ | |z.re - a| ≤ r + δ} := by
    intro z hz
    have hdist := (Complex.abs_re_le_norm (z - w)).trans (mem_closedBall_iff_norm.mp hz)
    simp only [Complex.sub_re] at hdist
    change |z.re - a| ≤ r + δ
    rw [show z.re - a = (z.re - w.re) + (w.re - a) by ring]
    linarith [abs_add_le (z.re - w.re) (w.re - a)]
  have hcircle (z : ℂ) (hz : z ∈ sphere w δ) : ‖f z‖ ≤ C * Real.exp (q * δ) * Real.exp (-q * |w.im|) := by
    have hdist := (Complex.abs_im_le_norm (z - w)).trans_eq (mem_sphere_iff_norm.mp hz)
    simp only [Complex.sub_im] at hdist
    have him : |w.im| ≤ |z.im| + δ := by
      have hh := abs_sub z.im (z.im - w.im)
      rw [sub_sub_cancel] at hh
      linarith
    apply (hbound z (hstrip (sphere_subset_closedBall hz))).trans
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left him hq])) hC
  apply (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hδ
    (hf.differentiableOn.diffContOnCl_ball hstrip) hcircle).trans_eq
  ring

/-- Every derivative of the regularized reciprocal decays uniformly, at all
exponential rates, throughout the closed target strip. -/
theorem stripReciprocal_regularized_iteratedDeriv_decay (A a k c r ε : ℝ)
    (hk : 0 < k) (hkc : k < c) (hr : 0 ≤ r) (hwider : k * (|a - A| + r) < π / 2)
    (hcr : c * r < π / 2) (he : 0 < ε) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g {w : ℂ | |w.re - A| < (π / 2) / k})
    (hn : ∀ w : ℂ, |w.re - A| < (π / 2) / k → g w ≠ 0)
    (M : ℝ) (hb : ∀ w : ℂ, |w.re - A| < (π / 2) / k → ‖g w‖ ≤ M) :
    ∀ (n : ℕ) (q : ℝ), 0 ≤ q → ∃ C > 0, ∀ w : ℂ, |w.re - a| ≤ r →
      ‖iteratedDeriv n (fun z ↦ stripReciprocalCutoff a c ε z / g z) w‖ ≤
        C * Real.exp (-q * |w.im|) := by
  have hc := hk.trans hkc
  let d₁ := (π / 2) / k - (|a - A| + r)
  let d₂ := (π / 2) / c - r
  have hd₁ : 0 < d₁ := sub_pos.mpr ((lt_div_iff₀ hk).mpr (by linarith))
  have hd₂ : 0 < d₂ := sub_pos.mpr ((lt_div_iff₀ hc).mpr (by linarith))
  let δ := min d₁ d₂ / 2
  have hmin := lt_min hd₁ hd₂
  have hδ : 0 < δ := half_pos hmin
  have hδ₁ : δ < d₁ := (half_lt_self hmin).trans_le (min_le_left ..)
  have hδ₂ : δ < d₂ := (half_lt_self hmin).trans_le (min_le_right ..)
  have hwide : |a - A| + (r + δ) < (π / 2) / k := by dsimp [d₁] at hδ₁; linarith
  have hcut : r + δ < (π / 2) / c := by dsimp [d₂] at hδ₂; linarith
  intro n q hq
  obtain ⟨C, hC, hbound⟩ := stripReciprocal_regularized_decay A a k c (r + δ) ε hk hkc
    (add_nonneg hr hδ.le) (by simpa [mul_comm k _] using (lt_div_iff₀ hk).mp hwide)
    (by simpa [mul_comm c _] using (lt_div_iff₀ hc).mp hcut) he g hg hn M hb q hq
  have hsub : {z : ℂ | |z.re - a| ≤ r + δ} ⊆ {z : ℂ | |z.re - A| < (π / 2) / k} := by
    intro z hz
    change |z.re - a| ≤ r + δ at hz
    apply lt_of_le_of_lt _ hwide
    rw [show z.re - A = (z.re - a) + (a - A) by ring]
    linarith [abs_add_le (z.re - a) (a - A)]
  refine ⟨(n.factorial : ℝ) * C * Real.exp (q * δ) / δ ^ n, by positivity, ?_⟩
  exact stripReciprocal_iteratedDeriv_estimate hδ hq hC.le
    ((stripReciprocal_regularized_analytic A a k c ε g hg hn).mono hsub) hbound n

/-- A frequency c with the required margins exists for every strictly nested
strip, including a zero-width target. -/
theorem stripReciprocal_exists_frequency (k r : ℝ) (hr : 0 ≤ r)
    (hkr : k * r < π / 2) : ∃ c : ℝ, k < c ∧ c * r < π / 2 := by
  rcases hr.eq_or_lt with h | h
  · refine ⟨k + 1, by linarith, ?_⟩
    rw [← h, mul_zero]; positivity
  · obtain ⟨c, hkc, hc⟩ := exists_between ((lt_div_iff₀ h).mpr hkr)
    exact ⟨c, hkc, (lt_div_iff₀ h).mp hc⟩

end RiemannMasullo
