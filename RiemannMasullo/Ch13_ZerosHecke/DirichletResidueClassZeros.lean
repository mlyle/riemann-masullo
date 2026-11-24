module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Chebyshev
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic

/-!
# Detecting Dirichlet zeros with primes in one residue class

The residue of the logarithmic-derivative sum for a unit class a modulo q is a finite
character sum of zero multiplicities. In the identity class the multiplicities add with
the same sign. Thus control of the single prime count in the class 1 modulo q can detect
zeros of every Dirichlet character of that modulus. Varying factorial moduli makes a
single sequence of estimates sufficient for all conductors.

This gives an arithmetic sufficient condition for the rational case of Theorem 12.5.1.1,
pp. 519–520. The prime estimates are hypotheses.
-/

open Set Filter Function ArithmeticFunction DirichletCharacter MeasureTheory
open scoped Topology Asymptotics

public noncomputable section
namespace RiemannMasullo

private theorem residueClass_logDeriv_limit {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    Tendsto (fun s : ℂ ↦ (s-ρ)*logDeriv f s) (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt f ρ : ℂ)) := by
  by_cases ht : analyticOrderAt f ρ = ⊤
  · have h := logDeriv_congr_nhds (analyticOrderAt_eq_top.mp ht)
    have hz : (fun s : ℂ ↦ (s-ρ)*logDeriv f s) =ᶠ[𝓝[≠] ρ] fun _ ↦ 0 := by
      filter_upwards [h.filter_mono nhdsWithin_le_nhds] with s hs
      rw [hs]
      simp [logDeriv]
    simpa [analyticOrderNatAt,ht] using (tendsto_const_nhds (x := (0:ℂ))).congr' hz.symm
  obtain ⟨g, hg, hn, he⟩ := hf.analyticOrderAt_ne_top.mp ht
  let m := analyticOrderNatAt f ρ
  change f =ᶠ[𝓝 ρ] fun s ↦ (s-ρ)^m * g s at he
  have hz : Tendsto (fun s : ℂ ↦ s-ρ) (𝓝[≠] ρ) (𝓝 0) := by
    have hc : Continuous (fun s : ℂ ↦ s-ρ) := by fun_prop
    simpa using (hc.continuousAt (x := ρ)).tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have hG := (hg.deriv.continuousAt.div hg.continuousAt hn).tendsto.mono_left
    (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have h := (tendsto_const_nhds (x := (m : ℂ))).add (hz.mul hG)
  apply (show Tendsto _ _ (𝓝 (m : ℂ)) from by simpa using h).congr'
  filter_upwards [(logDeriv_congr_nhds he).filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hn).filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hn' ha (hsρ : s ≠ ρ)
  have hd := sub_ne_zero.mpr hsρ
  have hpow : logDeriv (fun w : ℂ ↦ (w-ρ)^m) s = m/(s-ρ) := by
    have hsub : HasDerivAt (fun w : ℂ ↦ w-ρ) 1 s := (hasDerivAt_id' s).sub_const ρ
    rw [logDeriv_fun_pow hsub.differentiableAt, logDeriv_apply, hsub.deriv]
    ring
  rw [hs, logDeriv_fun_mul (f := fun w : ℂ ↦ (w-ρ)^m) (g := g) s (pow_ne_zero _ hd) hn' (by fun_prop) ha.differentiableAt, hpow]
  change (m : ℂ) + (s-ρ) * (deriv g s / g s) = (s-ρ)*(m/(s-ρ) + logDeriv g s)
  rw [logDeriv_apply]
  field_simp

/-- At every point away from one, the residue for a unit class is the character-weighted sum of
the Dirichlet zero multiplicities, with factor −1/φ(q). -/
theorem dirichletResidueClass_residue {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) {ρ : ℂ} (hρ : ρ ≠ 1) :
    Tendsto (fun s : ℂ ↦ (s-ρ) * vonMangoldt.LFunctionResidueClassAux a s) (𝓝[≠] ρ)
      (𝓝 (-(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (analyticOrderNatAt χ.LFunction ρ : ℂ))) := by
  classical
  have HA (χ : DirichletCharacter ℂ q) : AnalyticAt ℂ χ.LFunction ρ := by
    apply DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ)) _ (isOpen_compl_singleton.mem_nhds hρ)
    exact fun z h ↦ (differentiableAt_LFunction χ z (.inl h)).differentiableWithinAt
  have hl : LFunctionTrivChar₁ q =ᶠ[𝓝 ρ] fun w ↦ (w-1)*LFunctionTrivChar q w := by
    filter_upwards [eventually_ne_nhds hρ] with w hw
    exact Function.update_of_ne hw ..
  have hF : AnalyticAt ℂ (fun w : ℂ ↦ w-1) ρ := by fun_prop
  have ho : analyticOrderNatAt (LFunctionTrivChar₁ q) ρ =
      analyticOrderNatAt (LFunction (1 : DirichletCharacter ℂ q)) ρ := by
    simp only [analyticOrderNatAt, analyticOrderAt_congr hl, analyticOrderAt_fun_mul hF (HA 1),
      hF.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ), zero_add]
  have htr := residueClass_logDeriv_limit ((differentiable_LFunctionTrivChar₁ q).analyticAt ρ)
  rw [ho] at htr
  let S := ({1}ᶜ : Finset (DirichletCharacter ℂ q))
  have H := tendsto_finsetSum S (fun χ _ ↦ (residueClass_logDeriv_limit (HA χ)).const_mul (χ a⁻¹))
  have hh := (htr.add H).const_mul (-(q.totient : ℂ)⁻¹)
  have hunit := isUnit_of_dvd_one (show a⁻¹ ∣ 1 from ⟨a,(ZMod.inv_mul_of_unit a ha).symm⟩)
  rw [Fintype.sum_eq_add_sum_compl (1 : DirichletCharacter ℂ q),
    MulChar.one_apply hunit, one_mul]
  apply hh.congr
  intro s
  have hs : (∑ χ ∈ S, χ a⁻¹ * ((s-ρ) * logDeriv χ.LFunction s)) =
      (s-ρ) * ∑ χ ∈ S, χ a⁻¹ * deriv χ.LFunction s / χ.LFunction s := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [logDeriv_apply]
    ring
  rw [hs]
  simp only [vonMangoldt.LFunctionResidueClassAux, logDeriv_apply, S]
  ring

private theorem residueClass_order_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hn : ρ ≠ 1) :
    analyticOrderNatAt χ.LFunction ρ = 0 ↔ χ.LFunction ρ ≠ 0 := by
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isClosed_singleton.isOpen_compl
    exact fun z h ↦ (DirichletCharacter.differentiableAt_LFunction χ z (.inl h)).differentiableWithinAt
  have ht : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    intro h
    have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected hn (analyticOrderAt_eq_top.mp h)
    exact (LFunction_ne_zero_of_one_le_re χ (s := 2) (.inr (by norm_num)) (by norm_num))
      (hz (show (2 : ℂ) ∈ {1}ᶜ by norm_num))
  rw [← (ha _ hn).analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt ht]
  simp

/-- In the identity class the residue vanishes exactly when every character is nonzero at the point. -/
theorem dirichletResidueClass_one_residue_zero_iff {q : ℕ} [NeZero q] {ρ : ℂ} (hρ : ρ ≠ 1) :
    Tendsto (fun s : ℂ ↦ (s-ρ) * vonMangoldt.LFunctionResidueClassAux (1 : ZMod q) s)
      (𝓝[≠] ρ) (𝓝 0) ↔ ∀ χ : DirichletCharacter ℂ q, χ.LFunction ρ ≠ 0 := by
  have H := dirichletResidueClass_residue (1 : ZMod q) isUnit_one hρ
  simp only [ZMod.inv_one, map_one, one_mul, ← Nat.cast_sum] at H
  have hq : (q.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  constructor
  · intro h
    have hm := tendsto_nhds_unique H h
    have hsum : (∑ χ : DirichletCharacter ℂ q, analyticOrderNatAt χ.LFunction ρ) = 0 := by
      have hm' := (mul_eq_zero.mp hm).resolve_left (neg_ne_zero.mpr (inv_ne_zero hq))
      exact_mod_cast hm'
    intro χ
    apply (residueClass_order_eq_zero_iff χ hρ).mp
    have := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (DirichletCharacter ℂ q))) ↦
      Nat.zero_le (analyticOrderNatAt i.LFunction ρ)) (Finset.mem_univ χ)
    omega
  · intro h
    simpa only [fun χ ↦ (residueClass_order_eq_zero_iff χ hρ).mpr (h χ), Finset.sum_const_zero, Nat.cast_zero, mul_zero] using H

private theorem residueClass_meromorphic {q : ℕ} [NeZero q] (a : ZMod q) (z : ℂ) :
    MeromorphicAt (vonMangoldt.LFunctionResidueClassAux a) z := by
  classical
  have hn := ((differentiable_LFunctionTrivChar₁ q).analyticAt z).meromorphicAt
  apply MeromorphicAt.fun_mul (.const _ _)
  apply MeromorphicAt.fun_sub
  · exact hn.deriv.neg.div hn
  · apply MeromorphicAt.fun_sum
    intro χ hχ
    have hne : χ ≠ 1 := by simpa only [Finset.mem_compl, Finset.mem_singleton] using hχ
    have h := ((differentiable_LFunction hne).analyticAt z).meromorphicAt
    exact ((MeromorphicAt.const _ _).mul h.deriv).div h

/-- An analytic continuation of the one residue-class auxiliary function to a right half-plane
excludes zeros of all characters modulo q there, away from one. -/
theorem dirichletLFunction_ne_zero_of_residueClass_extension {q : ℕ} [NeZero q] {b : ℝ} (hb : b < 1) {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {s | b < s.re})
    (hR : ∀ s : ℂ, 1 < s.re → H s = vonMangoldt.LFunctionResidueClassAux (1 : ZMod q) s)
    {ρ : ℂ} (hr : b < ρ.re) (hn : ρ ≠ 1) (χ : DirichletCharacter ℂ q) : χ.LFunction ρ ≠ 0 := by
  let A := vonMangoldt.LFunctionResidueClassAux (1 : ZMod q)
  have hM : MeromorphicOn (H-A) {s | b < s.re} := fun s hs ↦ (hH _ hs).meromorphicAt.sub (residueClass_meromorphic _ _)
  have h₂ : (2 : ℂ) ∈ {s : ℂ | b < s.re} := by change b < (2 : ℂ).re; norm_num; linarith
  have ho : meromorphicOrderAt (H-A) 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have he : ∀ᶠ s : ℂ in 𝓝 (2:ℂ), 1 < s.re := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : 1 < (2:ℂ).re)
    filter_upwards [he.filter_mono (nhdsWithin_le_nhds (s := {(2:ℂ)}ᶜ))] with s hs
    exact sub_eq_zero.mpr (hR s hs)
  have he := meromorphicOrderAt_eq_top_iff.mp
    (hM.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected h₂ hr ho)
  apply (dirichletResidueClass_one_residue_zero_iff hn).mp _ χ
  have hc : ContinuousAt (fun s : ℂ ↦ (s-ρ)*H s) ρ := (continuousAt_id.sub continuousAt_const).mul (hH _ hr).continuousAt
  have hl : Tendsto (fun s : ℂ ↦ (s-ρ)*H s) (𝓝[≠] ρ) (𝓝 0) := by
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  apply hl.congr'
  filter_upwards [he] with z hz
  exact congrArg ((z-ρ)*·) (sub_eq_zero.mp hz)

/-- The sum of the von Mangoldt weights in one residue class with the principal main term subtracted. -/
@[expose] def dirichletResidueClassPsiError {q : ℕ} (a : ZMod q) (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt.residueClass a n) - x / q.totient

private theorem residueClass_error_measurable {q : ℕ} (a : ZMod q) : Measurable (dirichletResidueClassPsiError a) := by
  exact ((measurable_of_countable (fun m : ℕ ↦ ∑ n ∈ Finset.Icc 1 m, vonMangoldt.residueClass a n)).comp
    measurable_id.nat_floor).sub (measurable_id.div_const _)

private theorem residueClass_analytic_mellin (P : ℝ → ℝ) (hm : Measurable P) {b : ℝ}
    (hI : ∀ d > b, IntegrableOn (fun x : ℝ ↦ |P x| * x ^ (-d-1)) (Ioi 1)) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ ∫ x in Ioi (1 : ℝ), (P x : ℂ) * (x : ℂ)^(-(s+1))) {s | b < s.re} := by
  let n := fun x : ℝ ↦ max x 1
  have hn : Measurable n := measurable_id.max measurable_const
  have hp (x : ℝ) : 0 < n x := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let F (z : ℂ) := ∫ x in Ioi (1:ℝ), (P x : ℂ) * (n x : ℂ)^z
  have hi (z : ℂ) (hz : z.re ∈ Iio (-b-1)) : IntegrableOn (fun x : ℝ ↦ (P x : ℂ)*(n x : ℂ)^z) (Ioi 1) := by
    have hd : b < -z.re-1 := by change z.re < -b-1 at hz; linarith
    apply (hI _ hd).mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos (hp x),
      show n x = x from max_eq_left hx.le, show -(-z.re-1)-1=z.re by ring]
  have hA := analyticOnNhd_integral_mul_cpow_of_integrable (volume.restrict (Ioi (1:ℝ)))
    (fun x : ℝ ↦ (P x : ℂ)) n hn hp isOpen_Iio hi
  intro s hs
  have hg : AnalyticAt ℂ (fun w : ℂ ↦ -(w+1)) s := by fun_prop
  have hz : (-(s+1)).re ∈ Iio (-b-1) := by change _ < _; simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; change b < s.re at hs; linarith
  have he (w : ℂ) : F (-(w+1)) = ∫ x in Ioi (1:ℝ), (P x : ℂ) * (x : ℂ) ^ (-(w+1)) := by
    exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by simp only [n, max_eq_left hx.le]
  have ht := (hA (-(s+1)) hz).comp (f := fun w : ℂ ↦ -(w+1)) hg
  exact ht.congr (Eventually.of_forall he)

private theorem residueClass_aux_integral {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (s : ℂ) (hs : 1 < s.re)
    (hi : IntegrableOn (fun x : ℝ ↦ (dirichletResidueClassPsiError a x : ℂ) * (x : ℂ)^(-(s+1))) (Ioi 1)) :
    vonMangoldt.LFunctionResidueClassAux a s =
      s * (∫ x in Ioi (1:ℝ), (dirichletResidueClassPsiError a x : ℂ) * (x : ℂ)^(-(s+1))) + (q.totient : ℂ)⁻¹ := by
  let f := vonMangoldt.residueClass a
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n ↦ (n:ℝ)^(1:ℝ) := by
    refine Asymptotics.isBigO_iff.mpr ⟨Real.log 4+4, Eventually.of_forall fun n ↦ ?_⟩
    have h₀ : 0 ≤ ∑ k ∈ Finset.Icc 1 n, f k := Finset.sum_nonneg fun k _ ↦ vonMangoldt.residueClass_nonneg a k
    rw [Real.norm_of_nonneg h₀, Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg _)]
    apply (Finset.sum_le_sum fun k (_ : k ∈ Finset.Icc 1 n) ↦ vonMangoldt.residueClass_le a k).trans
    simpa only [Chebyshev.psi, Nat.floor_natCast, ← Finset.Icc_succ_left_eq_Ioc, Nat.succ_eq_add_one, zero_add, Order.succ_eq_add_one] using
      (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))
  have h := LSeries_eq_mul_integral_of_nonneg f zero_le_one hs hO (vonMangoldt.residueClass_nonneg a)
  have hc (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (∑ k ∈ Finset.Icc 1 ⌊x⌋₊, (f k : ℂ)) * (x : ℂ)^(-(s+1)) =
        (dirichletResidueClassPsiError a x : ℂ)*(x : ℂ)^(-(s+1)) + (q.totient : ℂ)⁻¹ * (x : ℂ)^(-s) := by
    have hx₀ := Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hx).ne'
    rw [show (x : ℂ)^(-s) = x * (x : ℂ)^(-(s+1)) by
      rw [show -s = 1 + -(s+1) by ring, Complex.cpow_add _ _ hx₀, Complex.cpow_one]]
    simp only [dirichletResidueClassPsiError, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast, f]
    ring
  have hI := integrableOn_Ioi_cpow_of_lt (a := -s) (by simp; linarith) (c := (1:ℝ)) zero_lt_one
  have hv : (∫ x in Ioi (1:ℝ), (x:ℂ)^(-s)) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one, Complex.ofReal_one, Complex.one_cpow,
      show -s+1 = -(s-1) by ring, neg_div_neg_eq]
  rw [vonMangoldt.eqOn_LFunctionResidueClassAux ha hs]
  change LSeries (fun n ↦ (f n : ℂ)) s - _ = _
  rw [h, setIntegral_congr_fun measurableSet_Ioi hc,
    integral_add hi (hI.const_mul _), integral_const_mul, hv]
  have hn : s-1 ≠ 0 := sub_ne_zero.mpr fun e ↦ by simp [e] at hs
  field_simp
  ring

/-- Absolute Mellin integrability of the centered count of prime powers congruent to one
in a right half-plane excludes all Dirichlet zeros of that modulus there, away from one. -/
theorem dirichletLFunction_ne_zero_of_residueClass_error {q : ℕ} [NeZero q] {b : ℝ} (hb : b < 1)
    (hI : ∀ d > b, IntegrableOn (fun x : ℝ ↦ |dirichletResidueClassPsiError (1 : ZMod q) x| * x^(-d-1)) (Ioi 1))
    {ρ : ℂ} (hr : b < ρ.re) (hn : ρ ≠ 1) (χ : DirichletCharacter ℂ q) : χ.LFunction ρ ≠ 0 := by
  have ha := residueClass_analytic_mellin _ (residueClass_error_measurable (1:ZMod q)) hI
  apply dirichletLFunction_ne_zero_of_residueClass_extension hb (H := fun s ↦ s *
    (∫ x in Ioi (1:ℝ), (dirichletResidueClassPsiError (1:ZMod q) x : ℂ) * (x : ℂ)^(-(s+1))) + (q.totient : ℂ)⁻¹) _ _ hr hn χ
  · exact fun z hz ↦ (analyticAt_id.mul (ha z hz)).add analyticAt_const
  · intro s hs
    apply (residueClass_aux_integral 1 isUnit_one s hs _).symm
    apply (hI s.re (hb.trans hs)).mono' (by
      have := residueClass_error_measurable (1:ZMod q)
      apply Measurable.aestronglyMeasurable
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx),
      show (-(s+1)).re = -s.re-1 by simp; ring]

/-- The sum of log p over primes p ≤ x congruent to one modulo q, with x/φ(q) subtracted. -/
@[expose] def dirichletSplitPrimeError (q : ℕ) (x : ℝ) : ℝ :=
  (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = 1), Real.log n) - x / q.totient

private theorem residueClass_higher_powers (q : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |dirichletResidueClassPsiError (1:ZMod q) x - dirichletSplitPrimeError q x| ≤ C * Real.sqrt x := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C, fun x ↦ ?_⟩
  let S := Finset.Icc 1 ⌊x⌋₊
  let f := vonMangoldt.residueClass (1:ZMod q)
  have hpr : ∑ n ∈ S.filter Nat.Prime, f n =
      ∑ n ∈ S.filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = 1), Real.log n := by
    rw [← Finset.filter_filter]
    conv_rhs => rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [f, vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
      vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  have hpart := Finset.sum_filter_add_sum_filter_not S Nat.Prime f
  have he : dirichletResidueClassPsiError (1:ZMod q) x - dirichletSplitPrimeError q x = ∑ n ∈ S.filter (fun n ↦ ¬ n.Prime), f n := by
    dsimp only [dirichletResidueClassPsiError,dirichletSplitPrimeError]
    rw [← hpr, sub_sub_sub_cancel_right]
    change (∑ n ∈ S, f n) - _ = _
    rw [← hpart]; abel
  have hψ : Chebyshev.psi x - Chebyshev.theta x = ∑ n ∈ S.filter (fun n ↦ ¬ n.Prime), vonMangoldt n := by
    have e : Finset.Ioc 0 ⌊x⌋₊ = S := (Finset.Icc_succ_left_eq_Ioc (0 : ℕ) ⌊x⌋₊).symm
    simp only [Chebyshev.psi, Chebyshev.theta, e]
    rw [← Finset.sum_filter_add_sum_filter_not S Nat.Prime (fun n ↦ vonMangoldt n)]
    have hpr : ∑ n ∈ S.filter Nat.Prime, vonMangoldt n = ∑ n ∈ S.filter Nat.Prime, Real.log n :=
      Finset.sum_congr rfl fun k hk ↦ vonMangoldt_apply_prime (Finset.mem_filter.mp hk).2
    rw [hpr]; abel
  rw [he, abs_of_nonneg (Finset.sum_nonneg fun n _ ↦ vonMangoldt.residueClass_nonneg _ n)]
  exact (Finset.sum_le_sum fun n _ ↦ vonMangoldt.residueClass_le (1:ZMod q) n).trans (hψ ▸ hC x)

/-- Finite weighted square integral for primes congruent to one modulo q at b ≥ 1/2 excludes
zeros of every Dirichlet character modulo q strictly to the right of b, away from one. -/
theorem dirichletLFunction_ne_zero_of_split_prime_energy {q : ℕ} [NeZero q] {b : ℝ} (hb : 1/2 ≤ b) (hb₁ : b < 1)
    (hE : IntegrableOn (fun x : ℝ ↦ (dirichletSplitPrimeError q x)^2 * x^(-2*b-1)) (Ioi 1))
    {ρ : ℂ} (hr : b < ρ.re) (hn : ρ ≠ 1) (χ : DirichletCharacter ℂ q) : χ.LFunction ρ ≠ 0 := by
  apply dirichletLFunction_ne_zero_of_residueClass_error hb₁ _ hr hn χ
  intro d hd
  obtain ⟨C,hC⟩ := residueClass_higher_powers q
  have he := integrableOn_Ioi_rpow_of_lt (by linarith : 2*b-2*d-1 < -1) zero_lt_one
  have hc := integrableOn_Ioi_rpow_of_lt (by linarith : (1/2:ℝ)-d-1 < -1) zero_lt_one
  have hm := residueClass_error_measurable (1:ZMod q)
  apply (((hE.add he).div_const 2).add (hc.const_mul C)).mono' (by
    apply Measurable.aestronglyMeasurable
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₀ := lt_trans zero_lt_one hx
  have hrp (a b' : ℝ) := Real.rpow_add (x := x) hx₀ a b'
  have hsq (a : ℝ) : (x^a)^2 = x^(2*a) := by rw [pow_two, ← hrp]; congr 1; ring
  let T := dirichletSplitPrimeError q x
  have hpoint : |T| * x^(-d-1) ≤ (T^2*x^(-2*b-1) + x^(2*b-2*d-1))/2 := by
    have hh := sq_nonneg (|T| * x^(-b-1/2) - x^(b-d-1/2))
    rw [sub_sq,mul_pow, sq_abs, hsq, hsq] at hh
    rw [show 2*(|T| * x^(-b-1/2))*x^(b-d-1/2) = 2 * |T| * x^(-d-1) by
      rw [← mul_assoc 2, mul_assoc (2 * |T|), ← hrp]; congr 2; ring] at hh
    convert (by linarith : |T| * x^(-d-1) ≤ (T^2*x^(2*(-b-1/2)) + x^(2*(b-d-1/2)))/2) using 2; ring_nf
  have ha : |dirichletResidueClassPsiError (1:ZMod q) x| ≤ |T| + C * Real.sqrt x := by
    have := abs_add_le (dirichletResidueClassPsiError (1:ZMod q) x - T) T
    rw [sub_add_cancel] at this
    linarith [hC x]
  have hw := Real.rpow_nonneg hx₀.le (-d-1)
  rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hw)]
  change _ ≤ (T^2*x^(-2*b-1) + x^(2*b-2*d-1))/2 + C*x^((1/2:ℝ)-d-1)
  apply (mul_le_mul_of_nonneg_right ha hw).trans
  rw [add_mul, mul_assoc, Real.sqrt_eq_rpow, ← hrp, show 1/2+(-d-1)=1/2-d-1 by ring]
  exact add_le_add_left hpoint _

/-- Controlling just the primes congruent to one modulo n! at exponent 1/2 + 1/(n+3),
for arbitrarily large n, excludes right-hand zeros at every conductor. -/
theorem dirichletLFunction_ne_zero_of_factorial_prime_energy (hE : ∀ N : ℕ, ∃ n ≥ N, IntegrableOn (fun x : ℝ ↦
    (dirichletSplitPrimeError n.factorial x)^2 * x^(-2*(1/2+1/((n:ℝ)+3))-1)) (Ioi 1))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ} (hr : 1/2 < ρ.re) (hn : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hr)
  obtain ⟨n, hN, he⟩ := hE (max q k)
  have hq : q ∣ n.factorial := Nat.dvd_factorial (NeZero.pos q) ((le_max_left q k).trans hN)
  have hk' : (k:ℝ) ≤ n := by exact_mod_cast (le_max_right q k).trans hN
  let b : ℝ := 1/2+1/((n:ℝ)+3)
  have hb : 1/2 ≤ b := by exact le_add_of_nonneg_right (by positivity)
  have h1 : b < 1 := by
    dsimp [b]
    have hh : 1/((n:ℝ)+3) < 1/2 := one_div_lt_one_div_of_lt (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  have hρ : b < ρ.re := by
    have hh : 1/((n:ℝ)+3) ≤ 1/((k:ℝ)+1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    dsimp [b]; linarith
  have : NeZero n.factorial := ⟨Nat.factorial_ne_zero n⟩
  intro hz
  apply dirichletLFunction_ne_zero_of_split_prime_energy hb h1 he hρ hn (changeLevel hq χ)
  rw [LFunction_changeLevel hq χ (.inr hn), hz, zero_mul]

private theorem residueClass_primitive_critical_line {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hfree : ∀ (η : DirichletCharacter ℂ q) (s : ℂ), 1/2 < s.re → s ≠ 1 → η.LFunction s ≠ 0)
    {ρ : ℂ} (hp : 0 < ρ.re) (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) : ρ.re = 1/2 := by
  have hn : ρ ≠ 1 := fun e ↦ by simp [e] at hr
  have hright : ρ.re ≤ 1/2 := le_of_not_gt fun h ↦ hfree χ ρ h hn hz
  apply le_antisymm hright
  by_contra! hleft
  have hρ : ρ ≠ 0 := fun e ↦ by simp [e] at hp
  have hg : χ.gammaFactor ρ ≠ 0 := by
    intro h
    rcases χ.even_or_odd with he | ho
    · obtain ⟨n, e⟩ := (gammaFactor_eq_zero_iff_of_even he).mp h
      have heq := congrArg Complex.re e
      norm_num [Complex.mul_re] at heq
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · obtain ⟨n, e⟩ := (gammaFactor_eq_zero_iff_of_odd ho).mp h
      have heq := congrArg Complex.re e
      norm_num [Complex.mul_re] at heq
      linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcomp : χ.completedLFunction ρ = 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor ρ (.inl hρ)] at hz
    exact (div_eq_zero_iff.mp hz).resolve_right hg
  have he := hχ.completedLFunction_one_sub (1-ρ)
  rw [sub_sub_cancel, hcomp] at he
  have hpow : (q : ℂ) ^ ((1-ρ)-1/2) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, NeZero.ne q]
  have hi : χ⁻¹.completedLFunction (1-ρ) = 0 := (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hpow (rootNumber_ne_zero hχ))
  have hk : χ⁻¹.LFunction (1-ρ) = 0 := by
    rw [χ⁻¹.LFunction_eq_completed_div_gammaFactor (1-ρ) (.inl (sub_ne_zero.mpr hn.symm)), hi, zero_div]
  have hd : 1/2 < (1-ρ).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  exact hfree χ⁻¹ (1-ρ) hd (fun e ↦ hρ (by linear_combination -e)) hk

/-- The cofinal sequence of prime estimates on factorial moduli puts every Dirichlet zero
in the open critical strip on the critical line, including imprimitive characters. -/
theorem dirichletLFunction_critical_line_of_factorial_prime_energy (hE : ∀ N : ℕ, ∃ n ≥ N, IntegrableOn (fun x : ℝ ↦
    (dirichletSplitPrimeError n.factorial x)^2 * x^(-2*(1/2+1/((n:ℝ)+3))-1)) (Ioi 1))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hp : 0 < ρ.re) (hr : ρ.re < 1) (hz : χ.LFunction ρ = 0) : ρ.re = 1/2 := by
  have hn : ρ ≠ 1 := fun e ↦ by simp [e] at hr
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  apply residueClass_primitive_critical_line χ.primitiveCharacter χ.primitiveCharacter_isPrimitive (fun η _ ↦ dirichletLFunction_ne_zero_of_factorial_prime_energy hE η) hp hr
  have he := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inr hn)
  rw [χ.changeLevel_primitiveCharacter, hz] at he
  apply (mul_eq_zero.mp he.symm).resolve_right
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp'
  have hprime := Nat.prime_of_mem_primeFactors hp'
  have hc : ‖(p : ℂ)^(-ρ)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hprime.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hprime.one_lt) (neg_lt_zero.mpr hp)
  have he' : ‖χ.primitiveCharacter p * (p : ℂ)^(-ρ)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.primitiveCharacter.norm_le_one _)).trans_lt hc
  exact sub_ne_zero.mpr fun e ↦ (ne_of_lt he') (by rw [← e, norm_one])

end RiemannMasullo
