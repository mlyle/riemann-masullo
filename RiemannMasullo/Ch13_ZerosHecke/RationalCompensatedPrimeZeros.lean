module

public import RiemannMasullo.Ch13_ZerosHecke.RationalCompensatedPrimeError
public import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # Zeta nonvanishing from compensated rational prime counts

For the rational principal character in Theorem 12.5.1.1, pp. 519–520,
a first-prime error estimate with the weight `2 − cos x − cos (√2 x)`
excludes every positive completed divisor order and every Riemann zeta zero
strictly to the right of its growth abscissa.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "Λ₀" => continuedCompletedHeckeL (F := ℚ) χ₀
local notation "Γ₀" => heckeGammaFactor (F := ℚ) χ₀

/-- On the Euler half-plane the principal completed function has the logarithmic
derivative of the actual archimedean factor times the ordinary Riemann zeta. -/
private theorem rationalPrincipal_euler_logDeriv {s : ℂ} (hs : 1 < s.re) :
    logDeriv Λ₀ s = logDeriv Γ₀ s + logDeriv riemannZeta s := by
  have he : Λ₀ =ᶠ[𝓝 s] fun z ↦ Γ₀ z * riemannZeta z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [(continuedCompletedHeckeL_spec χ₀).2 ⟨z, hz⟩]
    change Γ₀ z * finiteHeckeL χ₀ ⟨z, hz⟩ = _
    rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta hz]
  refine (logDeriv_congr_nhds he).eq_of_nhds.trans (logDeriv_fun_mul s
    (heckeGammaFactor_ne_zero_of_re_pos χ₀ (zero_lt_one.trans hs))
    (riemannZeta_ne_zero_of_one_le_re hs.le)
    (differentiableAt_heckeGammaFactor_of_re_pos χ₀ (zero_lt_one.trans hs)) ?_)
  apply differentiableAt_riemannZeta
  rintro rfl
  norm_num at hs

/-- After the translation `s = z + 1/2`, the compensator has the opposite logarithmic
derivative sign and half the scale of the completed two-cosine multiplier. -/
private theorem rationalPrincipal_divisor_of_compensated_continuation {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G {s : ℂ | σ < s.re})
    (he : ∀ s : ℂ, 1 < s.re → G s = rationalCompensatedZetaLogDeriv s)
    {s : ℂ} (hs : σ < s.re) : MeromorphicOn.divisor Λ₀ univ s ≤ 0 := by
  classical
  let q (z : ℂ) := z + 1 / 2
  let F (s : ℂ) := -logDeriv riemannZeta s - 1 / (s - 1)
  let A (s : ℂ) := logDeriv Γ₀ s + 1 / s - logDeriv Γ₀ (5 / 2)
  let R (z : ℂ) := logDeriv Λ₀ (q z) + (1 / (z + 1 / 2) + 1 / (z - 1 / 2)) -
    logDeriv Γ₀ (5 / 2)
  let D (f : ℂ → ℂ) (z : ℂ) := 4 * f z - f (z + Complex.I) - f (z - Complex.I) -
    f (z + (Real.sqrt 2 : ℂ) * Complex.I) - f (z - (Real.sqrt 2 : ℂ) * Complex.I)
  have hA (w : ℂ) (hw : 0 < w.re) : AnalyticAt ℂ A w := by
    have hd : DifferentiableOn ℂ Γ₀ {s : ℂ | 0 < s.re} := fun _ h ↦
      (differentiableAt_heckeGammaFactor_of_re_pos χ₀ h).differentiableWithinAt
    have ha := hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
    have hn : w ≠ 0 := by rintro rfl; norm_num at hw
    exact ((ha.deriv.div ha (heckeGammaFactor_ne_zero_of_re_pos χ₀ hw)).add
      (analyticAt_const.div analyticAt_id hn)).sub analyticAt_const
  have hRF (z : ℂ) (hz : 1 / 2 < z.re) : R z = A (q z) - F (q z) := by
    have hq : 1 < (q z).re := by dsimp [q]; norm_num; linarith
    have hsub : q z - 1 = z - 1 / 2 := by dsimp [q]; ring
    dsimp only [R, A, F]
    rw [rationalPrincipal_euler_logDeriv hq, hsub]
    dsimp only [q]
    ring
  let π : (AdeleRing (𝓞 ℚ) ℚ)ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := π.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  have hdiv := introTrace_zeroOrder_nonpos_of_twoCosine_continuation τ hτ χ₀ (by simp)
    (σ - 1 / 2) (1 / 2)
  have hp : σ - 1 / 2 < (s - 1 / 2).re := by norm_num; linarith
  suffices hx : ∀ p : ℂ, σ - 1 / 2 < p.re → MeromorphicOn.divisor Λ₀ univ (p + 1 / 2) ≤ 0 by
    simpa using hx (s - 1 / 2) hp
  apply hdiv
  refine ⟨fun z ↦ D (fun w ↦ A (q w)) z - 2 * G (q z), ?_, ?_⟩
  · intro z hz
    change σ - 1 / 2 < z.re at hz
    have hg : σ < (q z).re := by dsimp [q]; norm_num; linarith
    have hqa : AnalyticAt ℂ q z := by dsimp [q]; fun_prop
    have hAQ (w : ℂ) (hw : w.re = z.re) : AnalyticAt ℂ (fun v ↦ A (q v)) w := by
      have hpos : 0 < (q w).re := by dsimp [q]; norm_num; linarith
      exact (hA _ hpos).comp (f := q) (by dsimp [q]; fun_prop)
    have hAc (c : ℂ) (hc : c.re = 0) : AnalyticAt ℂ (fun w ↦ A (q (w + c))) z :=
      (hAQ (z + c) (by simp [hc])).comp (f := fun w ↦ w + c) (by fun_prop)
    have hconst (a : ℂ) : AnalyticAt ℂ (fun _ : ℂ ↦ a) z := analyticAt_const
    have hDc := (((((hconst 4).fun_mul (hAQ z rfl)).fun_sub
      (hAc Complex.I (by simp))).fun_sub (hAc (-Complex.I) (by simp))).fun_sub
      (hAc ((Real.sqrt 2 : ℂ) * Complex.I) (by simp))).fun_sub (hAc (-((Real.sqrt 2 : ℂ) * Complex.I)) (by simp))
    simpa only [D, sub_eq_add_neg, Function.comp_apply] using hDc.fun_sub ((hconst 2).fun_mul ((hG _ hg).comp hqa))
  · intro z hz
    have hz' : 1 / 2 < z.re := (le_max_right _ _).trans_lt hz
    have hqz : 1 < (q z).re := by dsimp [q]; norm_num; linarith
    have hcomp : G (q z) = 2 * F (q z) -
        (F (q z + Complex.I) + F (q z - Complex.I) +
          F (q z + (Real.sqrt 2 : ℂ) * Complex.I) + F (q z - (Real.sqrt 2 : ℂ) * Complex.I)) / 2 :=
      (he _ hqz).trans (rationalCompensatedZetaLogDeriv_apply _)
    change D (fun w ↦ A (q w)) z - 2 * G (q z) = _
    simp only
    change D (fun w ↦ A (q w)) z - 2 * G (q z) = D R z
    dsimp only [D]
    rw [hcomp, hRF _ hz', hRF _ (by simpa using hz'), hRF _ (by simpa using hz'),
      hRF _ (by simpa using hz'), hRF _ (by simpa using hz')]
    dsimp only [q]
    ring_nf

/-- In the positive half-plane, a nonpositive order of the rational principal
completed divisor excludes an ordinary zero of Riemann zeta. -/
private theorem riemannZeta_ne_zero_of_principal_divisor_nonpos {s : ℂ} (hs : 0 < s.re)
    (hdiv : MeromorphicOn.divisor Λ₀ univ s ≤ 0) : riemannZeta s ≠ 0 := by
  by_cases h₁ : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h₁
  have hs₁ : s ≠ 1 := by rintro rfl; norm_num at h₁
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hcmp := meromorphicOrderAt_finiteHeckeL_continuation χ₀ hm
    (fun z ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta z.property]) hs
  have ha := analyticOn_riemannZeta s hs₁
  have ha₂ : AnalyticAt ℂ riemannZeta 2 := analyticOn_riemannZeta 2 (by norm_num)
  have h₂ : meromorphicOrderAt riemannZeta 2 = 0 :=
    ha₂.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (riemannZeta_ne_zero_of_one_le_re (by norm_num))
  have hfinite := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ s) (by simp [h₂])
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ₀).1.meromorphicOn (mem_univ _),
    ← hcmp, ← hn, WithTop.untop₀_coe] at hdiv
  apply ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
  apply le_antisymm _ ha.meromorphicOrderAt_nonneg
  rw [← hn]
  exact_mod_cast hdiv

/-- On the rational principal chart, the single pole-corrected zeta continuation
excludes both positive completed divisor orders and ordinary Riemann zeta zeros. -/
private theorem rationalPrincipal_zero_free_of_compensated_continuation {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (h : ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G {z : ℂ | σ < z.re} ∧
      ∀ z : ℂ, 1 < z.re → G z = rationalCompensatedZetaLogDeriv z)
    {s : ℂ} (hs : σ < s.re) : MeromorphicOn.divisor Λ₀ univ s ≤ 0 ∧ riemannZeta s ≠ 0 := by
  obtain ⟨G, hG, he⟩ := h
  have hdiv := rationalPrincipal_divisor_of_compensated_continuation hσ hG he hs
  exact ⟨hdiv, riemannZeta_ne_zero_of_principal_divisor_nonpos (by linarith) hdiv⟩

/-- A bound for the signed first-prime error with its discrete mean rules out
rational principal zeros strictly to the right of its growth abscissa. -/
theorem rationalPrincipal_zero_free_of_compensatedPrimeError {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ₁ : σ < 1)
    (hp : ∀ r : ℝ, σ < r → ∃ C : ℝ, ∀ n : ℕ,
      |rationalCompensatedPrimeError n| ≤ C * (n : ℝ) ^ r)
    {s : ℂ} (hs : σ < s.re) : MeromorphicOn.divisor Λ₀ univ s ≤ 0 ∧ riemannZeta s ≠ 0 :=
  rationalPrincipal_zero_free_of_compensated_continuation hσ
    (rationalCompensatedZetaLogDeriv_continuation_of_primeError hσ hσ₁ hp) hs

/-- A first-prime count against the ordinary integral of the two-cosine weight,
at all integer cutoffs and all exponents above σ, excludes every ordinary zeta
zero and positive rational principal divisor order in the strict half-plane. -/
theorem rationalPrincipal_zero_free_of_compensatedPrimeIntegralError {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ₁ : σ < 1)
    (hp : ∀ r : ℝ, σ < r → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(∑ p ∈ Finset.Icc 1 N with p.Prime, Real.log p * rationalPrimeCosineWeight (Real.log p)) -
        ∫ x in (1 : ℝ)..N, rationalPrimeCosineWeight (Real.log x)| ≤ C * (N : ℝ) ^ r)
    {s : ℂ} (hs : σ < s.re) : MeromorphicOn.divisor Λ₀ univ s ≤ 0 ∧ riemannZeta s ≠ 0 :=
  rationalPrincipal_zero_free_of_compensated_continuation hσ
    (rationalCompensatedZetaLogDeriv_continuation_of_primeIntegralError hσ hσ₁ hp) hs

end RiemannMasullo
