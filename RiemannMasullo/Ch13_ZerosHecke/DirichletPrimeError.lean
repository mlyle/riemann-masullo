module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import RiemannMasullo.External.HardyCriticalLine.CriticalLineZeroInfinitude

/-!
# A Dirichlet L-function zero forces divergence of the prime-counting error

Let `P(x)` be the character-weighted sum of the von Mangoldt function up to `x`,
with the main term `x` subtracted for principal characters. A zero with real
part `β < 1` forces divergence of the integral of `‖P(x)‖² x^(-2β-1)` above one.

Finite energy would give an analytic Mellin integral to the right of `β`
whose growth when approaching from a distance `δ` is at most a constant
times `1 / √δ`. The logarithmic derivative of the L-function has a simple
pole at the zero. The two growth estimates conflict at that same exponent.

This gives an arithmetic condition for the rational case of Theorem 12.5.1.1,
pp. 519–520. At the critical exponent itself, the ordinary Chebyshev prime-power
error has infinite weighted squared integral by Hardy’s critical-line theorem.
-/

open Set Filter Function MeasureTheory Metric ArithmeticFunction Classical
open scoped Topology Asymptotics

public noncomputable section
namespace RiemannMasullo

/-- The character-weighted Chebyshev prime-power sum minus its pole contribution. -/
@[expose] def dirichletChebyshevError {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ (n : ZMod q) * (vonMangoldt n : ℂ)) -
    (if χ = 1 then (x : ℂ) else 0)

private theorem primeError_measurable {q : ℕ} (χ : DirichletCharacter ℂ q) : Measurable (dirichletChebyshevError χ) := by
  let A (m : ℕ) := ∑ n ∈ Finset.Icc 1 m, χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have h : Measurable (fun x : ℝ ↦ A ⌊x⌋₊) := (measurable_of_countable A).comp measurable_id.nat_floor
  change Measurable (fun x : ℝ ↦ A ⌊x⌋₊ - (if χ = 1 then (x : ℂ) else 0))
  by_cases he : χ = 1
  · simp only [ite_eq_left he]
    exact h.sub Complex.measurable_ofReal
  · simp only [ite_eq_right he, sub_zero]
    exact h

private theorem primeError_logDeriv_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 2 < s.re)
    (hi : IntegrableOn (fun x : ℝ ↦ dirichletChebyshevError χ x * (x : ℂ) ^ (-(s+1))) (Ioi 1)) :
    let e : ℂ := if χ = 1 then 1 else 0
    let H := ∫ x in Ioi (1 : ℝ), dirichletChebyshevError χ x * (x : ℂ) ^ (-(s+1))
    deriv χ.LFunction s / χ.LFunction s = -(s*H) - e*s/(s-1) := by
  intro e H
  let a (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have hA : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n ↦ (n : ℝ) ^ (2 : ℝ) := by
    refine Asymptotics.isBigO_iff.mpr ⟨1, Eventually.of_forall fun n ↦ ?_⟩
    simp only [one_mul, Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _)]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 n, (n : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [show ‖a k‖ = _ from norm_mul _ _, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
        calc
          _ ≤ 1 * vonMangoldt k := mul_le_mul_of_nonneg_right (χ.norm_le_one _) vonMangoldt_nonneg
          _ ≤ n := by
            rw [one_mul]
            exact vonMangoldt_le_log.trans ((Real.log_le_self (Nat.cast_nonneg k)).trans
              (Nat.cast_le.mpr (Finset.mem_Icc.mp hk).2))
      _ = _ := by simp [pow_two]
  have h₁ : 1 < s.re := by linarith
  have heq := LSeries_eq_mul_integral a (by norm_num : 0 ≤ (2 : ℝ)) hs
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h₁) hA
  have hL : χ.LFunction =ᶠ[𝓝 s] LSeries (fun n : ℕ ↦ χ (n : ZMod q)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₁] with z hz
    exact χ.LFunction_eq_LSeries hz
  have hrep : LSeries a s = -deriv χ.LFunction s / χ.LFunction s := by
    rw [hL.deriv_eq, hL.self_of_nhds]
    exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ h₁
  have hcorr (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n) * (x : ℂ) ^ (-(s+1)) =
      dirichletChebyshevError χ x * (x : ℂ) ^ (-(s+1)) + e * (x : ℂ) ^ (-s) := by
    have hx₀ := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hx).ne'
    have hpow : (x : ℂ) ^ (-s) = x * (x : ℂ) ^ (-(s+1)) := by
      rw [show -s = 1 + -(s+1) by ring, Complex.cpow_add _ _ hx₀, Complex.cpow_one]
    by_cases he : χ = 1
    all_goals simp only [dirichletChebyshevError, e, he, ite_true, ite_false,
      one_mul, zero_mul, add_zero, sub_zero, a, hpow]
    ring
  have hpowI := integrableOn_Ioi_cpow_of_lt (a := -s) (by simp; linarith) (c := (1 : ℝ)) zero_lt_one
  have hval : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s)) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    rw [show -s+1 = -(s-1) by ring, neg_div_neg_eq]
  rw [setIntegral_congr_fun measurableSet_Ioi hcorr, integral_add hi (hpowI.const_mul e),
    integral_const_mul, hval] at heq
  change LSeries a s = s * (H + e * (1 / (s-1))) at heq
  rw [hrep, neg_div] at heq
  linear_combination -heq

private theorem primeError_horizontal_logDeriv_limit {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hn : ∃ w, f w ≠ 0) (ρ : ℂ) :
    let z (u : ℝ) := ρ + (u : ℂ)
    (∀ᶠ u in 𝓝[>] (0 : ℝ), f (z u) ≠ 0) ∧
      Tendsto (fun u : ℝ ↦ (u : ℂ) * logDeriv f (z u)) (𝓝[>] 0)
        (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
  intro z
  let m := analyticOrderNatAt f ρ
  have htop : analyticOrderAt f ρ ≠ ⊤ := by
    intro h
    have hA : AnalyticOnNhd ℂ f univ := fun w _ ↦ hf.analyticAt w
    have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ρ)
      (analyticOrderAt_eq_top.mp h)
    obtain ⟨w, hw⟩ := hn
    exact hw (hzero (mem_univ w))
  obtain ⟨g,hg,hg₀,hfac⟩ := (hf.analyticAt ρ).analyticOrderAt_ne_top.mp htop
  let p (w : ℂ) := (w-ρ)^m
  change f =ᶠ[𝓝 ρ] fun w ↦ p w*g w at hfac
  have hlim : Tendsto z (𝓝[>] 0) (𝓝 ρ) := by
    have hc : Continuous z := by dsimp [z]; fun_prop
    simpa [z] using (hc.continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have h₀ := hlim.eventually (hg.continuousAt.eventually_ne hg₀)
  have hu0 : Tendsto (fun u : ℝ ↦ (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hG : ContinuousAt (logDeriv g) ρ := hg.deriv.continuousAt.div hg.continuousAt hg₀
  have hlog := hlim.eventually (logDeriv_congr_nhds hfac)
  refine ⟨?_, ?_⟩
  · filter_upwards [hlim.eventually hfac, h₀, self_mem_nhdsWithin] with u he hgu (hu : 0 < u)
    rw [he]; exact mul_ne_zero (pow_ne_zero _ (by simp [z,hu.ne'])) hgu
  · have ht := tendsto_const_nhds (x := (m : ℂ)) |>.add (hu0.mul (hG.tendsto.comp hlim))
    apply (show Tendsto _ _ (𝓝 (m : ℂ)) from by simpa using ht).congr'
    filter_upwards [hlog, h₀, hlim.eventually hg.eventually_analyticAt, self_mem_nhdsWithin] with u
      he hgu hga (hu : 0 < u)
    have hdiff : z u-ρ ≠ 0 := by simp [z,hu.ne']
    rw [he, logDeriv_fun_mul (f := p) (g := g) (z u) (pow_ne_zero _ hdiff) hgu (by dsimp [p]; fun_prop) hga.differentiableAt]
    have hp : logDeriv p (z u) = m / (z u - ρ) := by
      have hd : HasDerivAt (fun w : ℂ ↦ w-ρ) 1 (z u) := (hasDerivAt_id' (z u)).sub_const ρ
      change logDeriv (fun w : ℂ ↦ (w-ρ)^m) (z u) = _
      rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
      ring
    rw [hp]
    dsimp [z]
    field_simp [hu.ne']
    ring

private theorem primeError_pole_removed {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hr : ρ.re < 1) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ f 1 ≠ 0 ∧ analyticOrderNatAt f ρ = analyticOrderNatAt χ.LFunction ρ ∧
      ∀ s : ℂ, 2 < s.re →
      IntegrableOn (fun x : ℝ ↦ dirichletChebyshevError χ x * (x : ℂ) ^ (-(s+1))) (Ioi 1) →
      deriv f s = -(s * (∫ x in Ioi (1 : ℝ), dirichletChebyshevError χ x * (x : ℂ) ^ (-(s+1))) +
        (if χ = 1 then 1 else 0)) * f s := by
  have hne (s : ℂ) (hs : 2 < s.re) : χ.LFunction s ≠ 0 := by
    have h₁ : 1 < s.re := by linarith
    rw [χ.LFunction_eq_LSeries h₁]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ h₁
  by_cases he : χ = 1
  · subst χ
    let f := DirichletCharacter.LFunctionTrivChar₁ q
    have hz₁ : ρ ≠ 1 := fun e ↦ by simp [e] at hr
    refine ⟨f, DirichletCharacter.differentiable_LFunctionTrivChar₁ q,
      DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q, ?_, ?_⟩
    · have hloc : f =ᶠ[𝓝 ρ] fun w ↦ (w-1)*DirichletCharacter.LFunctionTrivChar q w := by
        filter_upwards [eventually_ne_nhds hz₁] with w hw
        exact Function.update_of_ne hw ..
      have hA : AnalyticAt ℂ (DirichletCharacter.LFunctionTrivChar q) ρ := by
        have ho : IsOpen ({1}ᶜ : Set ℂ) := isClosed_singleton.isOpen_compl
        apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) _ (ho.mem_nhds hz₁)
        exact fun z hz ↦ (DirichletCharacter.differentiableAt_LFunction _ z (.inl hz)).differentiableWithinAt
      have hF : AnalyticAt ℂ (fun w : ℂ ↦ w-1) ρ := by fun_prop
      simp only [analyticOrderNatAt, analyticOrderAt_congr hloc, analyticOrderAt_fun_mul hF hA,
        hF.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hz₁), zero_add]
    · intro s hs hi
      have hs₁ : s ≠ 1 := fun e ↦ by norm_num [e] at hs
      have hL := hne s hs
      have h := primeError_logDeriv_integral (1 : DirichletCharacter ℂ q) s hs hi
      simp only [ite_true, one_mul] at h
      simp only [f, ite_true]
      rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hs₁,
        DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs₁]
      change _ * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s +
        (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s = _
      field_simp [hL, sub_ne_zero.mpr hs₁] at h
      linear_combination h
  · refine ⟨χ.LFunction, DirichletCharacter.differentiable_LFunction he,
      DirichletCharacter.LFunction_apply_one_ne_zero he, rfl, ?_⟩
    intro s hs hi
    have h := primeError_logDeriv_integral χ s hs hi
    simp only [ite_eq_right he, zero_mul, zero_div, sub_zero] at h
    simpa [he] using (div_eq_iff (hne s hs)).mp h

private theorem primeError_analytic_mellin_integral {P : ℝ → ℂ} (hm : Measurable P) {b : ℝ}
    (hI : ∀ d > b, IntegrableOn (fun x : ℝ ↦ ‖P x‖ * x ^ (-d-1)) (Ioi 1)) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ x in Ioi (1 : ℝ), P x * (x : ℂ) ^ (-(s+1))) {s | b < s.re} := by
  let U := {s : ℂ | b < s.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  intro s hs
  change b < s.re at hs
  let d := (s.re - b)/3
  have hd : 0 < d := by dsimp [d]; linarith
  let F (z : ℂ) (x : ℝ) := P x * (x : ℂ) ^ (-(z+1))
  let F' (z : ℂ) (x : ℝ) := P x * ((x : ℂ) ^ (-(z+1)) * (-(Real.log x : ℂ)))
  have hF (z : ℂ) : Measurable (F z) := by dsimp [F]; fun_prop
  have hF' (z : ℂ) : Measurable (F' z) := by dsimp [F']; fun_prop
  have hr (z : ℂ) (x : ℝ) (hx : 0 < x) : ‖F z x‖ = ‖P x‖ * x ^ (-z.re-1) := by
    simp only [F, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re,
      Complex.add_re, Complex.one_re, neg_add_rev]
    ring_nf
  have hi : IntegrableOn (F s) (Ioi (1 : ℝ)) := by
    apply (hI s.re hs).mono' (hF _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hr _ _ (lt_trans zero_lt_one hx)).le
  let bound (x : ℝ) := (‖P x‖ * x ^ (-(s.re-2*d)-1))/d
  have hbound : IntegrableOn bound (Ioi 1) := (hI _ (by dsimp [d]; linarith)).div_const d
  have hl : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1),
      ∀ z ∈ ball s d, ‖F' z x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    have hx₁ : 1 ≤ x := le_of_lt hx
    have hx₀ := lt_of_lt_of_le zero_lt_one hx₁
    have hzr := (Complex.re_le_norm (s-z)).trans_lt (mem_ball_iff_norm'.mp hz)
    rw [Complex.sub_re] at hzr
    change ‖P x * ((x : ℂ) ^ (-(z+1)) * (-(Real.log x : ℂ)))‖ ≤ _
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx₁),
      Complex.norm_cpow_eq_rpow_re_of_pos hx₀]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    calc
      _ ≤ ‖P x‖ * (x ^ (-(z.re+1)) * (x^d/d)) := by
        gcongr; exact Real.log_le_rpow_div hx₀.le hd
      _ = ‖P x‖ * x ^ (-(z.re+1) + d) / d := by rw [Real.rpow_add hx₀]; ring
      _ ≤ bound x := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)) (norm_nonneg _)
  have hder : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 1),
      ∀ z ∈ ball s d, HasDerivAt (fun z ↦ F z x) (F' z x) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    have hpos : 0 < x := lt_trans zero_lt_one hx
    have hh := (((hasDerivAt_id' z).add_const 1).neg.const_cpow
      (c := (x : ℂ)) (Or.inl (Complex.ofReal_ne_zero.mpr hpos.ne'))).const_mul (P x)
    convert hh using 1
    simp [F', Complex.ofReal_log hpos.le]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hd)
    (Eventually.of_forall fun z ↦ (hF z).aestronglyMeasurable) hi
    (hF' s).aestronglyMeasurable hl hbound hder).2.differentiableAt.differentiableWithinAt

/-- The horizontal Mellin residue of the centered prime-power count, multiplied by the boundary point,
equals the negative order of the L-function whenever the integral converges absolutely to the right. -/
theorem dirichletChebyshevError_mellin_boundary {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hr : ρ.re < 1)
    (hI : ∀ d > ρ.re, IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevError χ x‖ * x ^ (-d-1)) (Ioi 1)) :
    Tendsto (fun u : ℝ ↦ (u : ℂ) * (ρ+u) *
      ∫ x in Ioi (1 : ℝ), dirichletChebyshevError χ x * (x : ℂ) ^ (-(ρ+u+1)))
      (𝓝[>] 0) (𝓝 (-(analyticOrderNatAt χ.LFunction ρ : ℂ))) := by
  let P := dirichletChebyshevError χ
  let H (s : ℂ) := ∫ x in Ioi (1 : ℝ), P x * (x : ℂ) ^ (-(s+1))
  let e : ℂ := if χ = 1 then 1 else 0
  obtain ⟨f, hf, hn, horder, he⟩ := primeError_pole_removed χ hr
  have hm := primeError_measurable χ
  have hA : AnalyticOnNhd ℂ H {s | ρ.re < s.re} := primeError_analytic_mellin_integral hm hI
  have hleft : AnalyticOnNhd ℂ (deriv f) {s | ρ.re < s.re} := fun s _ ↦ (hf.analyticAt s).deriv
  have hright : AnalyticOnNhd ℂ (fun s ↦ -(s*H s + e) * f s) {s | ρ.re < s.re} :=
    fun s hs ↦ (((analyticAt_id.mul (hA s hs)).add analyticAt_const).neg).mul (hf.analyticAt _)
  have heq := hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (convex_halfSpace_re_gt ρ.re).isPreconnected (z₀ := (3 : ℂ))
    (by change ρ.re < (3 : ℂ).re; norm_num; linarith) (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num : (3 : ℂ) ∈ {w : ℂ | 2 < w.re})] with s hs
      apply he s hs
      apply (hI s.re (lt_trans (by linarith : ρ.re < 2) hs)).mono' (by fun_prop)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re, neg_add_rev]
      ring_nf
      exact le_rfl)
  obtain ⟨hfn, hres⟩ := primeError_horizontal_logDeriv_limit hf ⟨1, hn⟩ ρ
  rw [horder] at hres
  have h0 : Tendsto (fun u : ℝ ↦ (u : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have ht := hres.neg.sub (h0.mul_const e)
  rw [zero_mul, sub_zero] at ht
  apply ht.congr'
  filter_upwards [hfn, self_mem_nhdsWithin] with u hn' (hu : 0 < u)
  have hu' : ρ.re < (ρ+u).re := by simp [hu]
  change -((u : ℂ) * logDeriv f (ρ+u)) - u*e = (u : ℂ)*(ρ+u)*H (ρ+u)
  change f (ρ+u) ≠ 0 at hn'
  rw [logDeriv_apply, heq hu']
  field_simp
  ring

private theorem primeError_mellin_energy_bound {P : ℝ → ℂ} (hm : Measurable P) (b : ℝ)
    (hE : IntegrableOn (fun x : ℝ ↦ ‖P x‖ ^ 2 * x ^ (-2*b-1)) (Ioi 1))
    {u : ℝ} (hu : 0 < u) :
    let E := ∫ x in Ioi (1 : ℝ), ‖P x‖ ^ 2 * x ^ (-2*b-1)
    let W (x : ℝ) := ‖P x‖ * x ^ (-(b+u^2)-1)
    IntegrableOn W (Ioi 1) ∧ (∫ x in Ioi (1 : ℝ), W x) ≤ (E+1) / u := by
  intro E W
  let f (x : ℝ) := ‖P x‖ ^ 2 * x ^ (-2*b-1)
  let g (x : ℝ) := x ^ (-2*u^2-1)
  have hp : -2*u^2-1 < -1 := by nlinarith [sq_pos_of_pos hu]
  have hi : IntegrableOn g (Ioi 1) := integrableOn_Ioi_rpow_of_lt hp zero_lt_one
  have hfg : IntegrableOn (fun x ↦ (f x + u^2 * g x) / (2*u)) (Ioi 1) :=
    (hE.add (hi.const_mul (u^2))).div_const _
  have hle (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : W x ≤ (f x + u^2 * g x)/(2*u) := by
    have hx₀ := lt_trans zero_lt_one hx
    let v := ‖P x‖ * x ^ (-b-1/2)
    let t := x ^ (-u^2-1/2)
    have h₁ : v^2 = f x := by
      simp only [v, f, mul_pow, ← Real.rpow_mul_natCast hx₀.le]
      congr 2
      push_cast
      ring
    have h₂ : t^2 = g x := by
      simp only [t, g, ← Real.rpow_mul_natCast hx₀.le]
      congr 1
      push_cast
      ring
    have h₃ : v*t = W x := by
      dsimp only [v,t,W]
      rw [mul_assoc, ← Real.rpow_add hx₀]
      congr 2
      ring
    rw [le_div_iff₀ (by positivity), ← h₁, ← h₂, ← h₃]
    nlinarith [sq_nonneg (v-u*t)]
  have hW : IntegrableOn W (Ioi 1) := by
    apply hfg.mono' (by dsimp [W]; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ := lt_trans zero_lt_one hx
    rw [Real.norm_of_nonneg (show 0 ≤ W x from mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx₀.le _))]
    exact hle x hx
  have hn : 0 ≤ E := integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)
  refine ⟨hW, (setIntegral_mono_on hW hfg measurableSet_Ioi hle).trans ?_⟩
  rw [integral_div, integral_add hE (hi.const_mul _), integral_const_mul]
  change (E + u^2 * (∫ x in Ioi (1 : ℝ), x ^ (-2*u^2-1))) / (2*u) ≤ _
  rw [integral_Ioi_rpow_of_lt hp zero_lt_one, Real.one_rpow]
  rw [show -2*u^2 - 1 + 1 = -(2*u^2) by ring]
  have he : u^2 * (-1 / -(2*u^2)) = 1/2 := by field_simp
  rw [he]
  field_simp
  linarith

/-- If a correction has a horizontal Mellin residue and leaves a finite weighted square integral,
its residue times the boundary point must equal the negative order of the L-function. -/
theorem dirichletChebyshevError_correction_residue {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) (hr : ρ.re < 1)
    (D : ℝ → ℂ) (hmD : Measurable D) {C : ℝ} (hD : ∀ x : ℝ, 1 ≤ x → ‖D x‖ ≤ C*x^ρ.re)
    {v : ℂ} (hV : Tendsto (fun u : ℝ ↦ (u : ℂ) * ∫ x in Ioi (1 : ℝ), D x * (x : ℂ) ^ (-(ρ+u+1)))
      (𝓝[>] 0) (𝓝 v))
    (hE : IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevError χ x - D x‖^2 * x^(-2*ρ.re-1)) (Ioi 1)) :
    ρ*v = -(analyticOrderNatAt χ.LFunction ρ : ℂ) := by
  let P := dirichletChebyshevError χ
  let Q (x : ℝ) := P x - D x
  have hP := primeError_measurable χ
  have hQ : Measurable Q := hP.sub hmD
  let E := ∫ x in Ioi (1 : ℝ), ‖Q x‖^2 * x^(-2*ρ.re-1)
  have hIQ (d : ℝ) (hd : ρ.re < d) : IntegrableOn (fun x : ℝ ↦ ‖Q x‖ * x^(-d-1)) (Ioi 1) := by
    have he := (primeError_mellin_energy_bound hQ ρ.re hE (Real.sqrt_pos_of_pos (sub_pos.mpr hd))).1
    simpa only [Real.sq_sqrt (sub_nonneg.mpr hd.le), add_sub_cancel] using he
  have hID (d : ℝ) (hd : ρ.re < d) : IntegrableOn (fun x : ℝ ↦ ‖D x‖ * x^(-d-1)) (Ioi 1) := by
    have hi := integrableOn_Ioi_rpow_of_lt (by linarith : ρ.re+(-d-1) < -1) zero_lt_one
    apply (hi.const_mul C).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ := lt_trans zero_lt_one hx
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx₀.le _)),
      Real.rpow_add hx₀, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hD x hx.le) (Real.rpow_nonneg hx₀.le _)
  have hIP (d : ℝ) (hd : ρ.re < d) : IntegrableOn (fun x : ℝ ↦ ‖P x‖ * x^(-d-1)) (Ioi 1) := by
    apply ((hIQ d hd).add (hID d hd)).mono' (by dsimp only [P]; apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hw := Real.rpow_nonneg (lt_trans zero_lt_one hx).le (-d-1)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    change _ ≤ ‖Q x‖ * _ + ‖D x‖ * _
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ hw
    simpa [Q] using norm_add_le (Q x) (D x)
  let z (t : ℝ) := ρ + ((t^2 : ℝ) : ℂ)
  let H (g : ℝ → ℂ) (t : ℝ) := ∫ x in Ioi (1 : ℝ), g x * (x : ℂ) ^ (-(z t+1))
  have ht₂ : Tendsto (fun t : ℝ ↦ t^2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ ↦ t^2) := by fun_prop
      simpa using (hc.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact sq_pos_of_pos ht
  have hz : Tendsto z (𝓝[>] 0) (𝓝 ρ) := by
    have h : Continuous z := by dsimp [z]; fun_prop
    simpa [z] using (h.continuousAt (x := (0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hn (g : ℝ → ℂ) (t x : ℝ) (hx : x ∈ Ioi (1:ℝ)) :
      ‖g x * (x : ℂ)^(-(z t+1))‖ = ‖g x‖ * x^(-(ρ.re+t^2)-1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
    simp only [z, Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    congr 2
    ring
  have hHQ : Tendsto (fun t : ℝ ↦ ((t^2 : ℝ) : ℂ) * H Q t) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun t : ℝ ↦ t*(E+1))
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hb := (primeError_mellin_energy_bound hQ ρ.re hE ht).2
      have hu : ‖H Q t‖ ≤ (E+1)/t := by
        apply (norm_integral_le_integral_norm _).trans
        convert hb using 1
        exact setIntegral_congr_fun measurableSet_Ioi (hn Q t)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      calc
        _ ≤ t^2*((E+1)/t) := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
        _ = _ := by field_simp
    · simpa using (show Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).mul_const (E+1)
  have hd : Tendsto (fun t : ℝ ↦ ((t^2 : ℝ) : ℂ) * H D t) (𝓝[>] 0) (𝓝 v) := hV.comp ht₂
  have hp : Tendsto (fun t : ℝ ↦ ((t^2 : ℝ) : ℂ) * (z t) * H P t) (𝓝[>] 0)
      (𝓝 (-(analyticOrderNatAt χ.LFunction ρ : ℂ))) := (dirichletChebyshevError_mellin_boundary χ ρ hr hIP).comp ht₂
  apply tendsto_nhds_unique _ hp
  have hsum := hz.mul (hHQ.add hd)
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hi (g : ℝ → ℂ) (hm : Measurable g)
      (hg : IntegrableOn (fun x : ℝ ↦ ‖g x‖ * x ^ (-(ρ.re+t^2)-1)) (Ioi 1)) :
      IntegrableOn (fun x : ℝ ↦ g x * (x : ℂ)^(-(z t+1))) (Ioi 1) := by
    apply hg.mono' (by dsimp [z]; apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hn g t x hx).le
  have hg : H Q t + H D t = H P t := by
    dsimp only [H]
    have hlt := lt_add_of_pos_right ρ.re (sq_pos_of_pos ht)
    rw [← integral_add (hi Q hQ (hIQ _ hlt)) (hi D hmD (hID _ hlt))]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change Q x * _ + D x * _ = P x * _
    rw [← add_mul, show Q x + D x = P x from sub_add_cancel ..]
  change z t * (((t^2 : ℝ) : ℂ) * H Q t + ((t^2 : ℝ) : ℂ) * H D t) = _
  rw [← mul_add, hg]
  ring

/-- Every Dirichlet L-function zero to the left of one has nonzero finite natural order. -/
theorem dirichletLFunction_zero_order_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hr : ρ.re < 1)
    (hz : χ.LFunction ρ = 0) : analyticOrderNatAt χ.LFunction ρ ≠ 0 := by
  have hn : ρ ∈ ({1}ᶜ : Set ℂ) := fun e ↦ by change ρ = 1 at e; simp [e] at hr
  have hA : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isClosed_singleton.isOpen_compl
    exact fun z h ↦ (DirichletCharacter.differentiableAt_LFunction χ z (.inl h)).differentiableWithinAt
  have ht : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    intro h
    have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected hn (analyticOrderAt_eq_top.mp h)
    have h₂ : 2 < (3 : ℂ).re := by norm_num
    have he := χ.LFunction_eq_LSeries (by linarith : 1 < (3 : ℂ).re)
    exact (DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ (by linarith : 1 < (3 : ℂ).re))
      (he ▸ hzero (show (3 : ℂ) ∈ {1}ᶜ by norm_num))
  intro h
  exact (analyticOrderAt_ne_zero.mpr ⟨hA _ hn, hz⟩) (by rw [← Nat.cast_analyticOrderNatAt ht, h]; rfl)

/-- At every Dirichlet L-function zero to the left of real part one, the weighted
mean-square error of its prime-power count diverges at the real part of that zero. -/
theorem dirichletLFunction_zero_primePower_energy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {ρ : ℂ} (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) :
    ¬ IntegrableOn (fun x : ℝ ↦ ‖dirichletChebyshevError χ x‖ ^ 2 * x ^ (-2*ρ.re-1)) (Ioi 1) := by
  intro hE
  have h := dirichletChebyshevError_correction_residue χ ρ hr (fun _ ↦ 0) measurable_const (C := 0) (by simp)
    (v := 0) (by simp) (by simpa using hE)
  have hm : analyticOrderNatAt χ.LFunction ρ = 0 := by simpa using h.symm
  exact dirichletLFunction_zero_order_ne_zero χ hr hz hm

/-- Each zeta zero to the left of real part one forces divergence of this weighted
mean square of the ordinary Chebyshev error. -/
theorem riemannZeta_zero_primePower_energy {ρ : ℂ} (hr : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ¬ IntegrableOn (fun x : ℝ ↦ (Chebyshev.psi x - x) ^ 2 * x ^ (-2*ρ.re-1)) (Ioi 1) := by
  have h := dirichletLFunction_zero_primePower_energy (1 : DirichletCharacter ℂ 1) hr (by simpa using hz)
  have heq (x : ℝ) : dirichletChebyshevError (1 : DirichletCharacter ℂ 1) x =
      ((Chebyshev.psi x - x : ℝ) : ℂ) := by
    simp only [dirichletChebyshevError, ite_true, Chebyshev.psi, Complex.ofReal_sub, Complex.ofReal_sum]
    congr 1
    rw [show Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ from (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) ⌊x⌋₊).symm]
    apply Finset.sum_congr rfl
    intro n _
    have hn : (n : ZMod 1) = 1 := Subsingleton.elim ..
    simp [hn]
  simpa only [heq, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- Hardy’s theorem supplies a critical-line zero unconditionally. Consequently the
relative error of the ordinary Chebyshev prime-power sum is not square-integrable above one. -/
theorem chebyshevPsi_relative_error_not_square_integrable : ¬ IntegrableOn (fun x : ℝ ↦ ((Chebyshev.psi x - x) / x) ^ 2) (Ioi 1) := by
  obtain ⟨t, ht⟩ := HardyCriticalLine.positiveHardyZeroHeights_infinite.nonempty
  have hz := (HardyCriticalLine.hardyFunctionReal_eq_zero_iff t).1 ht.2
  have hr : (HardyCriticalLine.criticalLinePoint t).re = 1/2 := by
    norm_num [HardyCriticalLine.criticalLinePoint]
  have h := riemannZeta_zero_primePower_energy (by rw [hr]; norm_num) hz
  rw [hr, show -2*(1/2 : ℝ)-1 = -(2 : ℝ) by norm_num] at h
  intro hi
  apply h
  refine hi.congr ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_)
  change ((Chebyshev.psi x - x) / x)^2 = (Chebyshev.psi x - x)^2 * x^(-(2 : ℝ))
  rw [Real.rpow_neg (lt_trans zero_lt_one hx).le, Real.rpow_two, div_pow, div_eq_mul_inv]

private theorem primeError_nonprime_bound {q : ℕ} (χ : DirichletCharacter ℂ q) :
    let T (x : ℝ) := (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      χ (n : ZMod q) * (Real.log n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖dirichletChebyshevError χ x - T x‖ ≤ C * Real.sqrt x := by
  intro T
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  let S := Finset.Icc 1 ⌊x⌋₊
  let a (n : ℕ) := χ (n : ZMod q) * (vonMangoldt n : ℂ)
  have hp : ∑ n ∈ S.filter Nat.Prime, a n =
      ∑ n ∈ S.filter Nat.Prime, χ (n : ZMod q) * (Real.log n : ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [a, vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hpart := Finset.sum_filter_add_sum_filter_not S Nat.Prime a
  have he : dirichletChebyshevError χ x - T x = ∑ n ∈ S.filter (fun n ↦ ¬ Nat.Prime n), a n := by
    dsimp only [T, dirichletChebyshevError]
    rw [← hp, sub_sub_sub_cancel_right]
    change (∑ n ∈ S, a n) - _ = _
    rw [← hpart]
    abel
  have hψ : Chebyshev.psi x - Chebyshev.theta x = ∑ n ∈ S.filter (fun n ↦ ¬ Nat.Prime n), vonMangoldt n := by
    have heq : Finset.Ioc 0 ⌊x⌋₊ = S := (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) ⌊x⌋₊).symm
    simp only [Chebyshev.psi, Chebyshev.theta, heq]
    rw [← Finset.sum_filter_add_sum_filter_not S Nat.Prime (fun n ↦ vonMangoldt n)]
    have hp : ∑ n ∈ S.filter Nat.Prime, vonMangoldt n = ∑ n ∈ S.filter Nat.Prime, Real.log n :=
      Finset.sum_congr rfl fun k hk ↦ vonMangoldt_apply_prime (Finset.mem_filter.mp hk).2
    rw [hp]
    abel
  rw [he]
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S.filter (fun n ↦ ¬ Nat.Prime n), vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _
      rw [show ‖a n‖ = _ from norm_mul _ _, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_left vonMangoldt_nonneg (χ.norm_le_one _)
    _ = _ := hψ.symm
    _ ≤ _ := (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))

/-- For a zero to the right of the critical line and left of one, the same divergence
holds after restricting the sum to genuine primes. -/
theorem dirichletLFunction_zero_prime_energy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {ρ : ℂ} (hβ : 1 / 2 < ρ.re) (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) :
    let T (x : ℝ) := (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      χ (n : ZMod q) * (Real.log n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)
    ¬ IntegrableOn (fun x : ℝ ↦ ‖T x‖ ^ 2 * x ^ (-2*ρ.re-1)) (Ioi 1) := by
  intro T hT
  obtain ⟨C, hC, herr⟩ := primeError_nonprime_bound χ
  change ∀ x : ℝ, ‖dirichletChebyshevError χ x - T x‖ ≤ C * Real.sqrt x at herr
  apply dirichletLFunction_zero_primePower_energy χ hr hz
  have hpow := integrableOn_Ioi_rpow_of_lt (by linarith : -2*ρ.re < -1) (c := 1) zero_lt_one
  have h := (hT.const_mul 2).add (hpow.const_mul (2*C^2))
  have hm := primeError_measurable χ
  apply h.mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ := lt_trans zero_lt_one hx
  have hw := Real.rpow_nonneg hx₀.le (-2*ρ.re-1)
  have hb : ‖dirichletChebyshevError χ x‖ ≤ ‖T x‖ + C*Real.sqrt x := by
    calc
      _ = ‖(dirichletChebyshevError χ x - T x) + T x‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith [herr x]
  have hb₂ : ‖dirichletChebyshevError χ x‖ ^ 2 ≤ 2*‖T x‖^2 + 2*C^2*x := by
    have hs := mul_self_le_mul_self (norm_nonneg _) hb
    nlinarith [sq_nonneg (‖T x‖-C*Real.sqrt x), congrArg (fun v : ℝ ↦ C^2*v) (Real.sq_sqrt hx₀.le)]
  have he : x * x ^ (-2*ρ.re-1) = x ^ (-2*ρ.re) := by
    conv_lhs => lhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx₀]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hb₂ hw
    _ = _ := by simp only [Pi.add_apply, add_mul]; linear_combination 2*C^2*he

/-- Finite centered prime-counting energy at one exponent above the critical line
excludes zeros on the entire closed half-plane to its right, away from the principal pole. -/
theorem dirichletLFunction_ne_zero_of_prime_energy {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {b : ℝ} (hb : 1 / 2 < b)
    (h : IntegrableOn (fun x : ℝ ↦ ‖(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      χ (n : ZMod q) * (Real.log n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)‖ ^ 2 * x ^ (-2*b-1)) (Ioi 1))
    (s : ℂ) (hs : b ≤ s.re) (hp : χ ≠ 1 ∨ s ≠ 1) : χ.LFunction s ≠ 0 := by
  by_cases hr : 1 ≤ s.re
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hp hr
  intro hz
  let A (m : ℕ) := ∑ n ∈ (Finset.Icc 1 m).filter Nat.Prime, χ (n : ZMod q) * (Real.log n : ℂ)
  let T (x : ℝ) := A ⌊x⌋₊ - (if χ = 1 then (x : ℂ) else 0)
  have hm : Measurable T := by
    have ha : Measurable (fun x : ℝ ↦ A ⌊x⌋₊) := (measurable_of_countable A).comp measurable_id.nat_floor
    by_cases he : χ = 1
    · simp only [T, ite_eq_left he]
      exact ha.sub Complex.measurable_ofReal
    · simpa only [T, ite_eq_right he, sub_zero] using ha
  apply dirichletLFunction_zero_prime_energy χ (hb.trans_le hs) (lt_of_not_ge hr) hz
  change IntegrableOn (fun x : ℝ ↦ ‖T x‖ ^ 2 * x ^ (-2*s.re-1)) (Ioi 1)
  apply h.mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change ‖‖T x‖^2 * x^(-2*s.re-1)‖ ≤ ‖T x‖^2 * x^(-2*b-1)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) (sq_nonneg _)

/-- A zeta zero strictly to the right of the critical line forces divergence of the
weighted squared error for the ordinary prime sum θ. -/
theorem riemannZeta_zero_prime_energy {ρ : ℂ} (hβ : 1 / 2 < ρ.re) (hr : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ¬ IntegrableOn (fun x : ℝ ↦ (Chebyshev.theta x - x) ^ 2 * x ^ (-2*ρ.re-1)) (Ioi 1) := by
  have h := dirichletLFunction_zero_prime_energy (1 : DirichletCharacter ℂ 1) hβ hr (by simpa using hz)
  have heq (x : ℝ) : (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
      (1 : DirichletCharacter ℂ 1) (n : ZMod 1) * (Real.log n : ℂ)) - (x : ℂ) =
      ((Chebyshev.theta x - x : ℝ) : ℂ) := by
    simp only [Chebyshev.theta, Complex.ofReal_sum, Complex.ofReal_sub,
      ← Finset.Icc_succ_left_eq_Ioc]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have hn : (n : ZMod 1) = 1 := Subsingleton.elim ..
    simp [hn]
  simpa only [ite_true, heq, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end RiemannMasullo
