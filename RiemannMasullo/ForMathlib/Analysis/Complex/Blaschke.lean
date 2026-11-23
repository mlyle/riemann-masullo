module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Order

/-!
# Blaschke products on a disk and a vertical strip

Jensen's formula gives the Blaschke condition for the divisor of a bounded analytic function.
The conformal coordinate transports this condition to a vertical strip. For a summable family
of disk zeros with multiplicities, the products omitting a finite subset are bounded by one,
vanish to the specified remaining orders and tend pointwise to one.
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory MeromorphicOn Metric Real Set
open scoped Topology

namespace RiemannMasullo

private theorem finite_sum_le_finsum_of_nonneg {α : Type*} (f : α → ℝ)
    (hf : (support f).Finite) (hn : 0 ≤ f) (S : Finset α) :
    ∑ x ∈ S, f x ≤ ∑ᶠ x, f x := by
  classical
  have hsub : support f ⊆ ↑(S ∪ hf.toFinset) := fun x hx ↦
    Finset.mem_union_right _ (hf.mem_toFinset.mpr hx)
  rw [finsum_eq_sum_of_support_subset _ hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun x _ _ ↦ hn x)

/-- The weighted sum of the logarithmic distances of any finite collection of
zeros from the boundary is bounded by the central deficit in Jensen's formula. -/
private theorem disk_divisor_finite_log_sum_le {g : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hg₀ : g 0 ≠ 0)
    (hb : ∀ z ∈ ball 0 1, ‖g z‖ ≤ M) (S : Finset ℂ) :
    ∑ z ∈ S, (divisor g (ball 0 1) z : ℝ) * log ‖z‖⁻¹ ≤ log M - log ‖g 0‖ := by
  classical
  let d := divisor g (ball 0 1)
  have hc (z : ℂ) : ContinuousAt (fun r : ℝ ↦ log (r * ‖z‖⁻¹)) 1 := by
    by_cases hz : z = 0
    · simp [hz, continuousAt_const]
    · exact (continuousAt_id.mul continuousAt_const).log (by simp [hz])
  have hlim : Tendsto (fun r : ℝ ↦ ∑ z ∈ S, (d z : ℝ) * log (r * ‖z‖⁻¹))
      (𝓝[<] 1) (𝓝 (∑ z ∈ S, (d z : ℝ) * log ‖z‖⁻¹)) := by
    apply tendsto_finsetSum
    intro z hz
    exact tendsto_const_nhds.mul (by simpa only [one_mul] using ((hc z).tendsto.mono_left nhdsWithin_le_nhds))
  apply le_of_tendsto hlim
  have hS : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z ∈ S, z ∈ ball (0 : ℂ) 1 → ‖z‖ ≤ r := by
    apply (eventually_all_finset S).mpr
    intro z hz
    by_cases h : z ∈ ball (0 : ℂ) 1
    · have hn : ‖z‖ < 1 := by simpa [mem_ball] using h
      exact (((eventually_gt_nhds hn).filter_mono nhdsWithin_le_nhds)).mono fun r hr _ ↦ hr.le
    · exact .of_forall fun _ hz ↦ (h hz).elim
  filter_upwards [hS, self_mem_nhdsWithin, (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds]
    with r hrS hr₁ hr₀
  have hr : r < 1 := hr₁
  let D := divisor g (closedBall 0 |r|)
  let J (z : ℂ) := (D z : ℝ) * log (r * ‖z‖⁻¹)
  have hA : AnalyticOnNhd ℂ g (closedBall 0 |r|) := hg.mono
    (closedBall_subset_ball (by rwa [abs_of_pos hr₀]))
  have hJ (z : ℂ) : 0 ≤ J z := by
    by_cases hz : z = 0
    · simp [J, hz]
    by_cases hR : z ∈ closedBall (0 : ℂ) |r|
    · apply mul_nonneg (by exact_mod_cast hA.divisor_nonneg z)
      apply log_nonneg
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.mpr hz)]
      simpa [mem_closedBall, abs_of_pos hr₀] using hR
    · simp [J, D.apply_eq_zero_of_notMem hR]
  have hfin : (support J).Finite :=
    (D.finiteSupport (isCompact_closedBall ..)).subset (fun z h ↦ by
      change D z ≠ 0
      intro hz
      exact h (by simp [J, hz]))
  have hav : circleAverage (fun x ↦ log ‖g x‖) 0 r ≤ log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (hA.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · intro z hz
      obtain h | h := eq_zero_or_norm_pos (g z)
      · simpa [h] using log_nonneg hM
      · exact log_le_log h (hb z (closedBall_subset_ball (by rwa [abs_of_pos hr₀] : |r| < 1) (sphere_subset_closedBall hz)))
  have hj := hA.circleAverage_log_norm hg₀
  calc
    ∑ z ∈ S, (d z : ℝ) * log (r * ‖z‖⁻¹) ≤ ∑ z ∈ S, J z := by
      refine Finset.sum_le_sum fun z hz ↦ ?_
      by_cases h : z ∈ ball (0 : ℂ) 1
      · have hR : z ∈ closedBall (0 : ℂ) |r| := by simpa [mem_closedBall, abs_of_pos hr₀] using hrS z hz h
        exact le_of_eq (congrArg (fun n : ℤ ↦ (n : ℝ) * log (r * ‖z‖⁻¹))
          ((hg.divisor_apply h).trans (hA.divisor_apply hR).symm))
      · simpa [d.apply_eq_zero_of_notMem h] using hJ z
    _ ≤ ∑ᶠ z, J z := finite_sum_le_finsum_of_nonneg J hfin hJ S
    _ ≤ log M - log ‖g 0‖ := by
      have he : circleAverage (fun x ↦ log ‖g x‖) 0 r = (∑ᶠ z, J z) + log ‖g 0‖ := by
        simpa only [J, D, zero_sub, norm_neg] using hj
      linarith

/-- The divisor of a nonzero bounded analytic function on the unit disk
satisfies the Blaschke condition, including the multiplicity of every zero. -/
theorem disk_divisor_summable_one_sub_norm {g : ℂ → ℂ} {M : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball 0 1)) (hg₀ : g 0 ≠ 0)
    (hb : ∀ z ∈ ball 0 1, ‖g z‖ ≤ M) :
    Summable fun z : ℂ ↦ (divisor g (ball 0 1) z : ℝ) * (1 - ‖z‖) := by
  let d := divisor g (ball 0 1)
  have hd (z : ℂ) : 0 ≤ (d z : ℝ) := by exact_mod_cast hg.divisor_nonneg z
  apply summable_of_sum_le (c := log (max 1 M) - log ‖g 0‖)
  · intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · have hn : ‖z‖ < 1 := by simpa [mem_ball] using hz
      exact mul_nonneg (hd z) (sub_nonneg.mpr hn.le)
    · simp [(divisor g (ball 0 1)).apply_eq_zero_of_notMem hz]
  · intro S
    refine le_trans (Finset.sum_le_sum fun z _ ↦ ?_) (disk_divisor_finite_log_sum_le (le_max_left 1 M) hg hg₀
      (fun z hz ↦ (hb z hz).trans (le_max_right _ _)) S)
    by_cases hz : z = 0
    · subst z
      rw [hg.divisor_apply (by simp), (hg 0 (by simp)).analyticOrderAt_eq_zero.mpr hg₀]
      simp
    · apply mul_le_mul_of_nonneg_left _ (hd z)
      simpa using one_sub_inv_le_log_of_pos (inv_pos.mpr (norm_pos_iff.mpr hz))

/-- The strip-to-disk and disk-to-strip maps use the half-width π/(2k).
The center may have arbitrary imaginary part. -/
def stripBlaschkeToDisk (w₀ : ℂ) (k : ℝ) (w : ℂ) : ℂ :=
  let u := Complex.exp ((k : ℂ) * (Complex.I * (w - w₀)))
  (u - 1) / (u + 1)

/-- The inverse coordinate from the unit disk to the open vertical strip. -/
def stripBlaschkeFromDisk (w₀ : ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  w₀ + ((k⁻¹ : ℝ) : ℂ) * (-Complex.I * Complex.log ((1 + z) / (1 - z)))

private theorem diskCayley_re_pos {z : ℂ} (hz : ‖z‖ < 1) :
    0 < ((1 + z) / (1 - z)).re := by
  have hn : 1 - z ≠ 0 := sub_ne_zero.mpr (fun h ↦ by simp [← h] at hz)
  have H := congrFun (poissonKernel_eq_re_herglotzRieszKernel (c := 0) (w := z)) (1 : ℂ)
  have he : ((1 + z) / (1 - z)).re = (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2 := by
    simpa [poissonKernel_def, herglotzRieszKernel_def] using H.symm
  rw [he]
  exact div_pos (by nlinarith [(sq_lt_sq₀ (norm_nonneg z) zero_le_one).mpr hz])
    (pow_pos (norm_pos_iff.mpr hn) _)

private theorem diskInverseCayley_mem {u : ℂ} (hu : 0 < u.re) :
    ‖(u - 1) / (u + 1)‖ < 1 := by
  have hn : u + 1 ≠ 0 := fun h ↦ by
    have he := congrArg Complex.re h
    simp at he
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hn)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero, add_zero]
  linarith

private theorem stripBlaschke_phase {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) :
    |((k : ℂ) * (Complex.I * (w - w₀))).im| < π / 2 := by
  rw [Complex.im_ofReal_mul, Complex.I_mul_im, Complex.sub_re, abs_mul, abs_of_pos hk]
  simpa only [mul_comm k _] using (lt_div_iff₀ hk).mp hw

/-- The strip coordinate takes its values in the open unit disk. -/
theorem stripBlaschkeToDisk_mem {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) : stripBlaschkeToDisk w₀ k w ∈ ball 0 1 := by
  have ht := stripBlaschke_phase hk hw
  have hpos : 0 < (Complex.exp ((k : ℂ) * (Complex.I * (w - w₀)))).re := by
    rw [Complex.exp_re]
    exact mul_pos (exp_pos _) (cos_pos_of_mem_Ioo (abs_lt.mp ht))
  simpa [stripBlaschkeToDisk, mem_ball] using diskInverseCayley_mem hpos

private theorem stripBlaschkeFromDisk_mem {z w₀ : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    |(stripBlaschkeFromDisk w₀ k z).re - w₀.re| < (π / 2) / k := by
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (diskCayley_re_pos (z := z) (by simpa [mem_ball] using hz)))
  have he : (stripBlaschkeFromDisk w₀ k z).re - w₀.re = k⁻¹ * Complex.arg ((1 + z)/(1 - z)) := by
    simp [stripBlaschkeFromDisk, Complex.mul_re, Complex.log_im]
  rw [he, abs_mul, abs_inv, abs_of_pos hk, show (π / 2) / k = k⁻¹ * (π / 2) from div_eq_inv_mul ..]
  exact mul_lt_mul_of_pos_left h (inv_pos.mpr hk)

private theorem stripBlaschke_cancel (k : ℝ) (hk : 0 < k) :
    ((k⁻¹ : ℝ) : ℂ) * (-Complex.I) * ((k : ℂ) * Complex.I) = 1 := by
  rw [Complex.ofReal_inv]
  field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne']
  simp

/-- The inverse coordinate recovers each point of the vertical strip. -/
theorem stripBlaschkeFromDisk_toDisk {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (π / 2) / k) :
    stripBlaschkeFromDisk w₀ k (stripBlaschkeToDisk w₀ k w) = w := by
  let t := (k : ℂ) * (Complex.I * (w - w₀))
  let u := Complex.exp t
  have ht : |t.im| < π / 2 := stripBlaschke_phase hk hw
  have hpos : 0 < u.re := by
    change 0 < (Complex.exp t).re
    rw [Complex.exp_re]
    exact mul_pos (exp_pos _) (cos_pos_of_mem_Ioo (abs_lt.mp ht))
  have hn : u + 1 ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hz := diskInverseCayley_mem hpos
  have hz' : 1 - (u - 1)/(u + 1) ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hz
  have hC : (1 + (u - 1)/(u + 1)) / (1 - (u - 1)/(u + 1)) = u := by field_simp; ring
  have hlog : Complex.log u = t := Complex.log_exp
    (by linarith [(abs_lt.mp ht).1, pi_pos]) (by linarith [(abs_lt.mp ht).2, pi_pos])
  change w₀ + _ * (-Complex.I * Complex.log ((1 + (u - 1)/(u + 1)) / (1 - (u - 1)/(u + 1)))) = w
  rw [hC,hlog]
  change w₀ + ((k⁻¹ : ℝ) : ℂ) * (-Complex.I * ((k : ℂ) * (Complex.I * (w - w₀)))) = w
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, show ((k⁻¹ : ℝ) : ℂ) * -Complex.I * (k : ℂ) * Complex.I = 1 by
    simpa only [mul_assoc] using stripBlaschke_cancel k hk]
  ring

/-- The forward coordinate recovers each point of the unit disk. -/
theorem stripBlaschkeToDisk_fromDisk {w₀ z : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    stripBlaschkeToDisk w₀ k (stripBlaschkeFromDisk w₀ k z) = z := by
  let u := (1 + z)/(1 - z)
  have hzn : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hpos : 0 < u.re := diskCayley_re_pos hzn
  have hn : u ≠ 0 := fun h ↦ by simp [h] at hpos
  have hu : u + 1 ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hzn
  have hC : (u - 1)/(u + 1) = z := by dsimp [u] at *; field_simp; ring
  have hphase : (k : ℂ) * (Complex.I * (stripBlaschkeFromDisk w₀ k z - w₀)) = Complex.log u := by
    change (k : ℂ) * (Complex.I * (w₀ + ((k⁻¹ : ℝ):ℂ) * (-Complex.I * Complex.log u) - w₀)) = Complex.log u
    rw [add_sub_cancel_left]
    calc
      _ = (((k⁻¹ : ℝ):ℂ) * -Complex.I * ((k : ℂ) * Complex.I)) * Complex.log u := by ring
      _ = _ := by rw [stripBlaschke_cancel k hk,one_mul]
  simpa only [stripBlaschkeToDisk, hphase, Complex.exp_log hn] using hC

private theorem stripBlaschkeFromDisk_analytic_deriv {z w₀ : ℂ} {k : ℝ} (hk : 0 < k) (hz : z ∈ ball 0 1) :
    AnalyticAt ℂ (stripBlaschkeFromDisk w₀ k) z ∧ deriv (stripBlaschkeFromDisk w₀ k) z ≠ 0 := by
  have hzn : ‖z‖ < 1 := by simpa [mem_ball] using hz
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr fun h ↦ by simp [← h] at hzn
  have hpos := diskCayley_re_pos hzn
  let u (v : ℂ) := (1 + v)/(1 - v)
  have hu : AnalyticAt ℂ u z := (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id) hden
  have hslit : u z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hpos)
  have hnum : u z ≠ 0 := fun h ↦ by change 0 < (u z).re at hpos; simp [h] at hpos
  refine ⟨analyticAt_const.add (analyticAt_const.mul (analyticAt_const.mul (hu.clog hslit))), ?_⟩
  have hdu : HasDerivAt u (2/(1-z) ^ 2) z := by
    convert (((hasDerivAt_const z 1).add (hasDerivAt_id z)).div ((hasDerivAt_const z 1).sub (hasDerivAt_id z)) hden) using 1
    · rfl
    · simp
      ring
  have h := (((Complex.hasDerivAt_log hslit).comp z hdu).const_mul (-Complex.I)).const_mul ((k⁻¹ : ℝ):ℂ)
  have hd := (h.const_add w₀).deriv
  change deriv (fun v ↦ w₀ + ((k⁻¹ : ℝ):ℂ) * (-Complex.I * Complex.log (u v))) z ≠ 0
  simp only [Function.comp_apply] at hd
  rw [hd]
  exact mul_ne_zero (by exact_mod_cast (inv_ne_zero hk.ne')) (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (mul_ne_zero (inv_ne_zero hnum) (div_ne_zero two_ne_zero (pow_ne_zero _ hden))))

/-- A bounded analytic function on a vertical strip satisfies a Blaschke condition
with the exact local zero orders in the conformal coordinate of the disk. -/
theorem verticalStrip_divisor_blaschke {w₀ : ℂ} {k M : ℝ} (hk : 0 < k)
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G {w | |w.re-w₀.re| < (π / 2) / k})
    (h₀ : G w₀ ≠ 0) (hb : ∀ w, |w.re-w₀.re| < (π / 2) / k → ‖G w‖ ≤ M) :
    Summable (fun w : {w : ℂ // |w.re-w₀.re| < (π / 2) / k} ↦
      ((meromorphicOrderAt G w.val).untop₀ : ℝ) * (1 - ‖stripBlaschkeToDisk w₀ k w‖)) := by
  let D := stripBlaschkeFromDisk w₀ k
  let A := G ∘ D
  have hA : AnalyticOnNhd ℂ A (ball 0 1) := fun z hz ↦
    (hG _ (stripBlaschkeFromDisk_mem (w₀ := w₀) hk hz)).comp (stripBlaschkeFromDisk_analytic_deriv hk hz).1
  have hD₀ : D 0 = w₀ := by simp [D,stripBlaschkeFromDisk]
  have hA₀ : A 0 ≠ 0 := by simpa [A, hD₀] using h₀
  have hB : ∀ z ∈ ball (0 : ℂ) 1, ‖A z‖ ≤ M := fun z hz ↦ hb _ (stripBlaschkeFromDisk_mem hk hz)
  let B (w : {w : ℂ // |w.re-w₀.re| < (π / 2) / k}) := stripBlaschkeToDisk w₀ k w
  have hleft (w) : D (B w) = w.val := stripBlaschkeFromDisk_toDisk hk w.property
  have hinj : Injective B := fun x y h ↦ Subtype.ext ((hleft x).symm.trans ((congrArg D h).trans (hleft y)))
  have hsum := (disk_divisor_summable_one_sub_norm hA hA₀ hB).comp_injective hinj
  refine hsum.congr fun w ↦ ?_
  have hw : B w ∈ ball 0 1 := stripBlaschkeToDisk_mem hk w.property
  have hc := stripBlaschkeFromDisk_analytic_deriv (w₀ := w₀) hk hw
  apply congrArg (fun n : ℤ ↦ (n : ℝ) * (1 - ‖B w‖))
  rw [hA.meromorphicOn.divisor_apply hw]
  change (meromorphicOrderAt (G ∘ D) (B w)).untop₀ = _
  rw [meromorphicOrderAt_comp_of_deriv_ne_zero hc.1 hc.2]
  exact congrArg (fun z ↦ (meromorphicOrderAt G z).untop₀) (hleft w)

/-- The conformal coordinate is analytic throughout the open vertical strip. -/
theorem stripBlaschkeToDisk_analytic {w₀ w : ℂ} {k : ℝ} (hk : 0 < k)
    (hw : |w.re - w₀.re| < (Real.pi / 2) / k) : AnalyticAt ℂ (stripBlaschkeToDisk w₀ k) w := by
  let E (z : ℂ) := Complex.exp ((k : ℂ) * (Complex.I * (z - w₀)))
  have hE : AnalyticAt ℂ E w :=
    (analyticAt_const.mul (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))).cexp
  have hr : 0 < (E w).re := by
    rw [show (E w).re = _ from Complex.exp_re _]
    exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp (stripBlaschke_phase hk hw)))
  exact (hE.sub analyticAt_const).div (hE.add analyticAt_const) (fun h ↦ by
    have he := congrArg Complex.re h
    change (E w + 1).re = 0 at he
    simp only [Complex.add_re, Complex.one_re] at he
    linarith)

/-- Composing with an analytic change of variable preserves a lower bound
on a zero multiplicity, even if the change itself is ramified. -/
theorem natCast_le_analyticOrderAt_comp {f g : ℂ → ℂ} {w : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f (g w)) (hg : AnalyticAt ℂ g w)
    (hm : (m : ℕ∞) ≤ analyticOrderAt f (g w)) :
    (m : ℕ∞) ≤ analyticOrderAt (f ∘ g) w := by
  have hcenter : AnalyticAt ℂ (fun z ↦ g z - g w) w := hg.sub analyticAt_const
  have h1 : (1 : ℕ∞) ≤ analyticOrderAt (fun z ↦ g z - g w) w :=
    Order.one_le_iff_ne_zero.mpr (hcenter.analyticOrderAt_ne_zero.mpr (sub_self _))
  rw [hf.analyticOrderAt_comp hg]
  calc
    _ ≤ analyticOrderAt f (g w) := hm
    _ = analyticOrderAt f (g w) * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 bot_le

end RiemannMasullo

open Complex Filter Function Metric Set
open scoped BigOperators ComplexConjugate Topology

@[expose] public noncomputable section
namespace RiemannMasullo.Blaschke

/-- Rotation carrying a nonzero zero to its positive radius. -/
private def rotation (a : ℂ) := conj a / (‖a‖ : ℂ)

private theorem rotation_norm {a : ℂ} (ha : a ≠ 0) : ‖rotation a‖ = 1 := by
  simp [rotation, norm_ne_zero_iff.mpr ha]

private theorem rotation_mul {a : ℂ} (ha : a ≠ 0) : rotation a * a = ‖a‖ := by
  rw [rotation, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)]

/-- A disk factor normalized to have the positive value ‖a‖ at zero. -/
private def factor (a z : ℂ) : ℂ :=
  ((‖a‖ : ℂ) - rotation a * z) / (1 - (‖a‖ : ℂ) * (rotation a * z))

private theorem den_ne {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - (‖a‖ : ℂ) * (rotation a * z) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hn : ‖(‖a‖ : ℂ) * (rotation a * z)‖ < 1 := by
    simp only [norm_mul, rotation_norm ha, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha'.le) (norm_nonneg z)]
  simp only [← h, norm_one, lt_self_iff_false] at hn

private theorem factor_contracts {a z : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖factor a z‖ ≤ 1 := by
  let r := ‖a‖
  let w := rotation a * z
  have hw : ‖w‖ < 1 := by simpa [w, norm_mul, rotation_norm ha] using hz
  have hr : r ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg a) ha'.le
  have hw' : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw.le
  have hsq : ‖1 - (r : ℂ) * w‖ ^ 2 - ‖(r : ℂ) - w‖ ^ 2 = (1 - r ^ 2) * (1 - ‖w‖ ^ 2) := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  change ‖((r : ℂ) - w) / (1 - (r : ℂ) * w)‖ ≤ 1
  rw [norm_div, div_le_one (norm_pos_iff.mpr (den_ne ha ha' hz))]
  nlinarith [norm_nonneg ((r : ℂ) - w), norm_nonneg (1 - (r : ℂ) * w),
    mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hw')]

private theorem factor_close {a z : ℂ} {R : ℝ} (ha : a ≠ 0) (ha' : ‖a‖ < 1)
    (hz : ‖z‖ ≤ R) (hR : R < 1) :
    ‖factor a z - 1‖ ≤ (1 + R) / (1 - R) * (1 - ‖a‖) := by
  let r := ‖a‖
  let w := rotation a * z
  have hw : ‖w‖ ≤ R := by simpa [w, norm_mul, rotation_norm ha] using hz
  have hr : 0 ≤ r := norm_nonneg a
  have hr1 : r ≤ 1 := ha'.le
  have hd : 1 - (r : ℂ) * w ≠ 0 := den_ne ha ha' (hz.trans_lt hR)
  have hdn : 1 - R ≤ ‖1 - (r : ℂ)*w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ)*w)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (norm_nonneg w)]
  have hnum : ‖1 + w‖ ≤ 1 + R := (norm_add_le _ _).trans (by simpa using hw)
  have hid : factor a z - 1 = ((r : ℂ)-1) * (1+w) / (1 - (r : ℂ)*w) := by
    change ((r : ℂ)-w)/(1-(r : ℂ)*w)-1 = _
    field_simp
    ring
  have hrnorm : ‖(r : ℂ) - 1‖ = 1 - r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  rw [hid, norm_div, norm_mul, hrnorm]
  have hne := sub_pos.mpr hR
  calc
    _ ≤ (1 - r) * (1+R) / (1-R) := by
      gcongr
      exact mul_nonneg (sub_nonneg.mpr hr1) (by linarith [norm_nonneg z])
    _ = _ := by ring

private theorem factor_analytic {a : ℂ} (ha : a ≠ 0) (ha' : ‖a‖ < 1) :
    AnalyticOnNhd ℂ (factor a) (ball 0 1) := by
  intro z hz
  have hw : AnalyticAt ℂ (fun u : ℂ ↦ rotation a * u) z := analyticAt_const.mul analyticAt_id
  exact (analyticAt_const.sub hw).div (analyticAt_const.sub (analyticAt_const.mul hw))
    (den_ne ha ha' (mem_ball_zero_iff.mp hz))

private theorem norm_mul_sub_one (x y : ℂ) (hx : ‖x‖ ≤ 1) :
    ‖x*y-1‖ ≤ ‖x-1‖ + ‖y-1‖ := by
  calc
    _ = ‖(x-1) + x*(y-1)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_mul]; nlinarith [mul_nonneg (sub_nonneg.mpr hx) (norm_nonneg (y-1))])

private theorem norm_pow_sub_one (x : ℂ) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖x ^ m-1‖ ≤ m * ‖x-1‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    exact (norm_mul_sub_one _ _ hx).trans (by push_cast; linarith)

private theorem norm_prod_sub_one {ι : Type*} (f : ι → ℂ) (h : ∀ i, ‖f i‖ ≤ 1) (S : Finset ι) :
    ‖∏ i ∈ S, f i - 1‖ ≤ ∑ i ∈ S, ‖f i - 1‖ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (norm_mul_sub_one _ _ (h i)).trans (add_le_add le_rfl ih)

private theorem product_uniform {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    HasProdLocallyUniformlyOn (fun i z ↦ factor (a i) z ^ m i)
      (fun z ↦ ∏' i, factor (a i) z ^ m i) (ball 0 1) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball
  intro K hK hKc
  obtain h | h := K.eq_empty_or_nonempty
  · subst K
    rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    exact tendstoUniformlyOn_empty
  obtain ⟨x, hx, hmax⟩ := hKc.exists_isMaxOn h (continuous_norm.continuousOn)
  let R := ‖x‖
  have hR : R < 1 := mem_ball_zero_iff.mp (hK hx)
  let C := (1 + R) / (1 - R)
  let f (i : ι) (z : ℂ) := factor (a i) z ^ m i - 1
  have hf (i) (z) (hz : z ∈ K) : ‖f i z‖ ≤ C * ((m i : ℝ) * (1 - ‖a i‖)) := by
    apply (norm_pow_sub_one _ (factor_contracts (ha i) (ha' i) (mem_ball_zero_iff.mp (hK hz))) _).trans
    calc
      _ ≤ (m i : ℝ) * (C * (1 - ‖a i‖)) := mul_le_mul_of_nonneg_left
        (factor_close (ha i) (ha' i) (hmax hz) hR) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hcts (i) : ContinuousOn (f i) K :=
    (((factor_analytic (ha i) (ha' i)).continuousOn.mono hK).pow _).sub continuousOn_const
  simpa only [f, add_sub_cancel, add_sub_cancel_left, add_sub_cancel_right, add_sub_assoc, add_comm (1 : ℂ), sub_add_cancel] using
    (Summable.hasProdUniformlyOn_one_add hKc (hs.mul_left C) (.of_forall hf) hcts)

private theorem product_analytic {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    AnalyticOnNhd ℂ (fun z ↦ ∏' i, factor (a i) z ^ m i) (ball 0 1) := by
  have h := product_uniform a m ha ha' hs
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply TendstoLocallyUniformlyOn.differentiableOn h _ isOpen_ball
  exact .of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun i _ ↦
    ((factor_analytic (ha i) (ha' i)).differentiableOn).pow _

private theorem product_bound {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (z : ℂ) (hz : ‖z‖ < 1) :
    ‖∏' i, factor (a i) z ^ m i‖ ≤ 1 ∧
    ‖(∏' i, factor (a i) z ^ m i) - 1‖ ≤
      ((1 + ‖z‖) / (1 - ‖z‖)) * ∑' i, (m i : ℝ) * (1 - ‖a i‖) := by
  let C := (1 + ‖z‖) / (1 - ‖z‖)
  have hp := (product_uniform a m ha ha' hs).hasProd (mem_ball_zero_iff.mpr hz)
  have h1 (i) : ‖factor (a i) z ^ m i‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (factor_contracts (ha i) (ha' i) hz)
  constructor
  · apply le_of_tendsto' hp.norm
    intro S
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ h1 i
  · apply le_of_tendsto' (hp.sub tendsto_const_nhds).norm
    intro S
    apply (norm_prod_sub_one _ h1 S).trans
    calc
      _ ≤ ∑ i ∈ S, C * ((m i : ℝ) * (1 - ‖a i‖)) := by
        apply Finset.sum_le_sum
        intro i _
        apply (norm_pow_sub_one _ (factor_contracts (ha i) (ha' i) hz) _).trans
        calc
          _ ≤ (m i : ℝ) * (C * (1 - ‖a i‖)) := mul_le_mul_of_nonneg_left
            (factor_close (ha i) (ha' i) le_rfl hz) (Nat.cast_nonneg _)
          _ = _ := by ring
      _ = C * ∑ i ∈ S, (m i : ℝ) * (1 - ‖a i‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hs.sum_le_tsum S (fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' i).le)))
        (div_nonneg (by positivity) (sub_nonneg.mpr hz.le))

private theorem product_divisible {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) (i : ι) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (a i) ∧
      (fun z ↦ ∏' j, factor (a j) z ^ m j) =ᶠ[𝓝 (a i)]
        fun z ↦ (z - a i) ^ m i * G z := by
  classical
  let n (j : ι) := if j = i then 0 else m j
  have hs' : Summable (fun j ↦ (n j : ℝ) * (1 - ‖a j‖)) := by
    apply Summable.of_nonneg_of_le (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' j).le)) _ hs
    intro j
    by_cases h : j = i
    · simp only [n, ite_eq_left h, Nat.cast_zero, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (ha' j).le)
    · simp [n, h]
  let D (z : ℂ) := 1 - (‖a i‖ : ℂ) * (rotation (a i) * z)
  let V (z : ℂ) := -rotation (a i)/D z
  let U (z : ℂ) := ∏' j, factor (a j) z ^ n j
  have hai : a i ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (ha' i)
  have hD : AnalyticAt ℂ D (a i) :=
    analyticAt_const.sub (analyticAt_const.mul (analyticAt_const.mul analyticAt_id))
  have hV : AnalyticAt ℂ V (a i) :=
    analyticAt_const.div hD (den_ne (ha i) (ha' i) (ha' i))
  have hU : AnalyticAt ℂ U (a i) := product_analytic a n ha ha' hs' _ hai
  refine ⟨fun z ↦ V z ^ m i * U z, (hV.pow _).mul hU, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hai] with z hz
  have hu : Function.update (fun j ↦ factor (a j) z ^ m j) i 1 =
      fun j ↦ factor (a j) z ^ n j := by
    funext j
    by_cases h : j = i <;> simp [h, n, Function.update_of_ne]
  have hconv : Multipliable (Function.update (fun j ↦ factor (a j) z ^ m j) i 1) := by
    rw [hu]
    exact ((product_uniform a n ha ha' hs').hasProd hz).multipliable
  rw [Multipliable.tprod_eq_mul_tprod_ite' i hconv]
  have htail : (∏' j, if j = i then 1 else factor (a j) z ^ m j) = U z := by
    apply tprod_congr
    intro j
    by_cases h : j = i <;> simp [n, h]
  have hfac : factor (a i) z = (z - a i) * V z := by
    have hn : ((‖a i‖ : ℂ) - rotation (a i) * z) = (z - a i) * (-rotation (a i)) := by
      rw [← rotation_mul (ha i)]
      ring
    change ((‖a i‖ : ℂ) - rotation (a i) * z)/D z = (z-a i)*(-rotation (a i)/D z)
    rw [hn, mul_div_assoc]
  rw [htail, hfac, mul_pow, mul_assoc]

/-- Any divisor satisfying the Blaschke condition has contractive holomorphic
tail factors on the disk. The tails tend pointwise to one and have all
prescribed zero multiplicities outside a finite set. -/
theorem exists_holomorphic_disk_tails {ι : Type*} (a : ι → ℂ) (m : ι → ℕ)
    (ha : ∀ i, a i ≠ 0) (ha' : ∀ i, ‖a i‖ < 1)
    (hs : Summable (fun i ↦ (m i : ℝ) * (1 - ‖a i‖))) :
    ∃ B : Finset ι → ℂ → ℂ,
      (∀ S, AnalyticOnNhd ℂ (B S) (ball 0 1)) ∧
      (∀ S z, ‖z‖ < 1 → ‖B S z‖ ≤ 1) ∧
      (∀ z, ‖z‖ < 1 → Tendsto (fun S ↦ B S z) atTop (𝓝 1)) ∧
      ∀ (S : Finset ι) (i : ι), i ∉ S →
        ∃ G : ℂ → ℂ, AnalyticAt ℂ G (a i) ∧
          B S =ᶠ[𝓝 (a i)] fun z ↦ (z - a i) ^ m i * G z := by
  classical
  let ar (S : Finset ι) (j : {j // j ∉ S}) := a j.val
  let mult (S : Finset ι) (j : {j // j ∉ S}) := m j.val
  let tail (S : Finset ι) (z : ℂ) := ∏' j : {j // j ∉ S}, factor (ar S j) z ^ mult S j
  have hn (S : Finset ι) (j) : ar S j ≠ 0 := ha j.val
  have hlt (S : Finset ι) (j) : ‖ar S j‖ < 1 := ha' j.val
  have hconv (S : Finset ι) : Summable (fun j ↦ (mult S j : ℝ) * (1 - ‖ar S j‖)) := hs.subtype _
  have hA (S : Finset ι) : AnalyticOnNhd ℂ (tail S) (ball 0 1) :=
    product_analytic (ar S) (mult S) (hn S) (hlt S) (hconv S)
  have hbound (S : Finset ι) (z : ℂ) (hz : ‖z‖ < 1) := product_bound
    (ar S) (mult S) (hn S) (hlt S) (hconv S) z hz
  refine ⟨tail, hA, fun S z hz ↦ (hbound S z hz).1, ?_, ?_⟩
  · intro z hz
    let C := (1 + ‖z‖) / (1 - ‖z‖)
    let u (i : ι) := (m i : ℝ) * (1 - ‖a i‖)
    have hmajor (S : Finset ι) : ‖tail S z - 1‖ ≤ C * ∑' j : {x // x ∉ S}, u j.val :=
      (hbound S z hz).2
    have hlim : Tendsto (fun S : Finset ι ↦ C * ∑' j : {x // x ∉ S}, u j.val) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_tsum_compl_atTop_zero u).const_mul C
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun S ↦ norm_nonneg _) hmajor hlim)
  · intro S i hi
    let j : {x // x ∉ S} := ⟨i, hi⟩
    exact product_divisible (ar S) (mult S) (hn S) (hlt S) (hconv S) j

end RiemannMasullo.Blaschke
