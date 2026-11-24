module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a

/-!
# Appendix B.7.1: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter NumberField Set
open scoped Asymptotics Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "oneLine" => Complex.re ⁻¹' ({1} : Set ℝ)

/-- Paper: Lemma B.7.1.1, Equations (B.7.1.4)–(B.7.1.5), p. 644.
The two printed simplified bounds are uniform in the unrestricted range
`σ > 1 - c`. A common constant majorizes the three big-O constants.
The bound in (B.7.1.3) is supplied as one law of the exponent and the
coefficient bound in (1), fixed for all the sequences under consideration.
The natural floor extends the integer majorant to positive real arguments. -/
def Printed.truncatedPerron_error_of_isBigO : Prop :=
  ∀ (α A : ℝ), 0 < α → 0 < A →
    ∃ C : ℝ, 0 < C ∧ ∀ (absBound : ℝ → ℝ → ℝ),
      (∀ α' A', 0 < α' → 0 < A' → 0 < absBound α' A') →
      ∀ (a : ℕ → ℂ) (ψ : ℕ → ℝ),
      (∀ n, 0 < ψ n) → Monotone ψ →
      (∀ s : ℂ, 1 < s.re → LSeriesSummable a s) →
      (∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ A * ψ n) →
      Asymptotics.IsBigOWith (absBound α A) (𝓝[>] (1 : ℝ))
        (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖)
        (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹) →
      ∀ (c σ T : ℝ), 0 < c → 1 - c < σ → 1 ≤ T →
        let s : ℂ := ⟨σ, T⟩
        (∀ (x : ℝ), 0 < x → x ∉ Set.range (Int.cast : ℤ → ℝ) →
          ∀ N : ℤ, |x - (N : ℝ)| ≤ 1 / 2 →
            ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
              C * (x ^ c / (T * (σ + c - 1) ^ α) +
                |ψ ⌊2 * x⌋₊ * x ^ (1 - σ) * Real.log x / T| +
                ψ N.toNat * x ^ (1 - σ) / (T * |x - (N : ℝ)|))) ∧
        (∀ m : ℕ, 0 < m →
          ‖perronHalfWeightedSum a s m - truncatedPerronIntegral (LSeries a) s m c T‖ ≤
            C * ((m : ℝ) ^ c / (T * (σ + c - 1) ^ α) +
              ψ (2 * m) * (m : ℝ) ^ (1 - σ) * Real.log m / T +
              ψ m * c * (m : ℝ) ^ (-σ) / T))

/-- Paper: Lemma B.7.1.1, pp. 644–645. Take `a₁ = 1`, all other
coefficients zero, `ψ ≡ 1`, and `α = c = T = 1`. At `x = 5/4` and
`x = 2` the cutoff sum is 1, while the integral has norm at most `x / π < 1`.
Each proposed error bound tends to zero as `σ → +∞`. -/
theorem Printed.truncatedPerron_error_of_isBigO_false :
    ¬ Printed.truncatedPerron_error_of_isBigO := by
  intro h
  obtain ⟨C, hC, H⟩ := h 1 1 one_pos one_pos
  have H2 := H (fun _ _ ↦ 1) (fun _ _ _ _ ↦ one_pos) LSeries.delta (fun _ ↦ 1)
  have hdelta_zero : ∀ (s : ℂ) (n : ℕ), n ≠ 1 → LSeries.term LSeries.delta s n = 0 := by
    intro s n hn
    simp [LSeries.term_delta, hn]
  have hsum : ∀ σ : ℝ, ∑' n : ℕ, ‖LSeries.term LSeries.delta (σ : ℂ) n‖ = 1 := by
    intro σ
    rw [tsum_eq_single 1 (fun n hn => by simp [hdelta_zero _ n hn])]
    simp [LSeries.delta]
  have hsumm : ∀ s : ℂ, 1 < s.re → LSeriesSummable LSeries.delta s := by
    intro s _
    apply summable_of_ne_finset_zero (s := {1})
    intro n hn
    exact hdelta_zero s n (by simpa using hn)
  have hev : ∀ᶠ n : ℕ in atTop, ‖LSeries.delta n‖ ≤ 1 * 1 := by
    apply Eventually.of_forall
    intro n
    by_cases hn : n = 1 <;> simp [LSeries.delta, hn]
  have hbig : Asymptotics.IsBigOWith ((fun _ _ ↦ (1:ℝ)) 1 1) (𝓝[>] (1 : ℝ))
      (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term LSeries.delta (σ : ℂ) n‖)
      (fun σ : ℝ ↦ ((σ - 1) ^ (1:ℝ))⁻¹) := by
    apply Asymptotics.IsBigOWith.of_bound
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1:ℝ) < 2)] with σ hσ
    have h0 : (0:ℝ) < σ - 1 := by linarith [hσ.1]
    rw [hsum σ]
    simp only [Real.rpow_one, norm_inv, Real.norm_eq_abs, abs_of_pos h0, one_mul, abs_one]
    exact (one_le_inv₀ h0).2 (by linarith [hσ.2])
  have H3 := H2 (fun _ ↦ one_pos) monotone_const hsumm hev hbig
  have hI : ∀ t : ℝ, ‖((5/4 : ℝ) : ℂ) ^ (⟨1, t⟩ : ℂ) / (⟨1, t⟩ : ℂ)‖ ≤ 5/4 := by
    intro t
    have hre : (⟨1, t⟩ : ℂ).re = 1 := rfl
    have hge : (1:ℝ) ≤ ‖(⟨1, t⟩ : ℂ)‖ := by
      have := Complex.abs_re_le_norm (⟨1, t⟩ : ℂ)
      rw [hre, abs_one] at this
      exact this
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), hre, Real.rpow_one]
    exact div_le_self (by norm_num) hge
  have hIbound : ∀ s : ℂ, ‖truncatedPerronIntegral (LSeries LSeries.delta) s (5/4) 1 1‖ ≤ 5 / 12 := by
    intro s
    show ‖(∫ t in -(1:ℝ)..1, LSeries LSeries.delta (s + ⟨1, t⟩) *
        ((5/4 : ℝ) : ℂ) ^ (⟨1, t⟩ : ℂ) / (⟨1, t⟩ : ℂ)) / (2 * (Real.pi : ℂ))‖ ≤ 5 / 12
    simp only [LSeries_delta, Pi.one_apply, one_mul]
    rw [norm_div]
    have hint' : ‖∫ t in (-1:ℝ)..1, ((5/4 : ℝ) : ℂ) ^ (⟨1, t⟩ : ℂ) / (⟨1, t⟩ : ℂ)‖ ≤ 5/4 * |(1:ℝ) - -1| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      exact hI t
    rw [show |(1:ℝ) - -1| = 2 by norm_num] at hint'
    have hn2 : ‖(2 * (Real.pi:ℂ))‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      simp
    rw [hn2, div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hnot : (5/4:ℝ) ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨k, hk⟩
    have h5 : (4 * k : ℤ) = 5 := by
      have : (4 * (k:ℝ)) = 5 := by rw [hk]; norm_num
      exact_mod_cast this
    omega
  have hfl : ⌊(5/4:ℝ)⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have hperron : ∀ σ : ℝ, perronHalfWeightedSum LSeries.delta ⟨σ, 1⟩ (5/4) = 1 := by
    intro σ
    show (∑ n ∈ Finset.Icc 1 ⌊(5/4:ℝ)⌋₊, if (n : ℝ) = 5/4 then
      LSeries.term LSeries.delta ⟨σ, 1⟩ n / 2 else LSeries.term LSeries.delta ⟨σ, 1⟩ n) = 1
    rw [hfl]
    norm_num [LSeries.term_delta]
  have hlim : Tendsto (fun σ : ℝ => C * ((5/4:ℝ) / σ + |(5/4:ℝ)^(1-σ) * Real.log (5/4)| + (5/4:ℝ)^(1-σ) * 4)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun σ : ℝ => (5/4:ℝ) / σ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1s : Tendsto (fun σ : ℝ => 1 - σ) atTop atBot := by
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_left atTop (1:ℝ) tendsto_neg_atTop_atBot
    have h2 : Tendsto (fun σ : ℝ => (5/4:ℝ)^(1-σ)) atTop (𝓝 0) :=
      (tendsto_rpow_atBot_of_base_gt_one (5/4) (by norm_num)).comp h1s
    have h3 : Tendsto (fun σ : ℝ => |(5/4:ℝ)^(1-σ) * Real.log (5/4)|) atTop (𝓝 0) := by
      have := (h2.mul_const (Real.log (5/4))).abs
      simpa using this
    have h4 : Tendsto (fun σ : ℝ => (5/4:ℝ)^(1-σ) * 4) atTop (𝓝 0) := by
      simpa using h2.mul_const (4:ℝ)
    have := ((h1.add h3).add h4).const_mul C
    simpa using this
  obtain ⟨σ, hRHS, hσ1⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))).and
    (eventually_gt_atTop (1:ℝ))).exists
  have hA := (H3 1 σ 1 one_pos (by linarith) le_rfl).1
  have H4 := hA (5/4) (by norm_num) hnot 1 (by norm_num)
  rw [hperron σ] at H4
  have hlow : (7/12:ℝ) ≤ ‖(1:ℂ) - truncatedPerronIntegral (LSeries LSeries.delta) ⟨σ, 1⟩ (5/4) 1 1‖ := by
    have h := norm_sub_norm_le (1:ℂ) (truncatedPerronIntegral (LSeries LSeries.delta) ⟨σ, 1⟩ (5/4) 1 1)
    have h' := hIbound ⟨σ, 1⟩
    rw [norm_one] at h
    linarith
  simp only [Real.rpow_one, one_mul, div_one, Int.cast_one] at H4
  norm_num at H4 hRHS
  linarith

/-- Paper: Equation (B.7.1.11), p. 646. The printed bound uses a full weight at
integer cutoffs with the error terms for the half-weight Perron formula. -/
def Printed.heckeLogDerivPolynomial_perron_error : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℂ → ℂ), MeromorphicNFOn Z univ →
      (∀ s : halfPlane, Z s = dedekindZeta F s) →
      ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → s ≠ 1 + Complex.I * t₀ → 1 < x → 0 < c → 1 ≤ T →
        ‖heckeLogDerivPolynomial χ x s -
          truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T‖ ≤
          C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
            (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
             else Real.log x / (T * |x - (round x : ℝ)|)))

/-- Paper: Equation (B.7.1.11), p. 646. Over the rationals take the trivial
character, `t₀ = 0`, `s = 1 + i`, `x = 2` and `c = 1`. The integral
tends to the half-weight sum as `T → +∞`. The full sum differs by
`log(2) / (2 · 2^s) ≠ 0`, whereas the printed error tends to zero. -/
theorem Printed.heckeLogDerivPolynomial_perron_error_false :
    ¬ Printed.heckeLogDerivPolynomial_perron_error := by
  sorry

/-- Paper: Contour preceding Equation (B.7.1.12), p. 647. The printed choice
`δ = α η(|T - t₀|)` is claimed to place the entire contour inside the
region specified by the width `η`. -/
def Printed.dedekindZeta_perron_contour_in_zeroFreeRegion : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (t₀ : ℝ),
    ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
    ∀ (Z : ℂ → ℂ), MeromorphicNFOn Z univ → (∀ s : halfPlane, Z s = dedekindZeta F s) →
    ∀ (A B : ℝ), 0 < A → 1 / 3 < B →
    let η := fun v : ℝ ↦ A / Real.log (B * (|v| + 3))
    MapsTo η (Ici 0) (Ioc 0 (1 / 2)) →
    (∀ z : ℂ, 1 - η |z.im| < z.re → meromorphicOrderAt Z z ≤ 0) →
    ∀ (α t T c : ℝ), α ∈ Ioo 0 1 → t ≠ t₀ → 2 + |t₀| + |t| ≤ T → 0 < c →
      let δ := α * η |T - t₀|
      ∀ u ∈ Icc (-δ) c, ∀ y ∈ Icc (-T) T,
        (u = -δ ∨ u = c ∨ y = -T ∨ y = T) →
        1 - η |t + y - t₀| < 1 + u

/-- Paper: Contour preceding Equation (B.7.1.12), p. 647. Take `t₀ = 0`,
`t = 2`, `T = 4`, and `c = 1`. At the top left corner the shifted
height is 6. Take the trivial character over the rationals and any genuine
logarithmic zero-free width from Proposition B.6.1.1, shrinking its numerator
to ensure the range condition. For every such width, `η(6) / η(4) < 1`.
Choose `α` strictly between that ratio and one. -/
theorem Printed.dedekindZeta_perron_contour_in_zeroFreeRegion_false :
    ¬ Printed.dedekindZeta_perron_contour_in_zeroFreeRegion := by
  sorry

end RiemannMasullo
