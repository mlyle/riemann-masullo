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

/-- The truncated Perron kernel of a term beyond the cutoff, with `l = log (n / x) > 0`, decays
like `1 / T`: moving the segment from `c - iT` to `c + iT` to the right inside a rectangle
leaves only the two horizontal edges. -/
private theorem heckeLogDerivPolynomial_perron_error_false_kernel (l c T : ℝ) (hl : 0 < l)
    (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in -T..T, Complex.exp (-(l : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)‖ ≤
      2 * Real.exp (-l * c) / (l * T) := by
  have hlim : Tendsto (fun U : ℝ ↦ 2 * Real.exp (-l * c) / (l * T) + 2 * T / U) atTop
      (𝓝 (2 * Real.exp (-l * c) / (l * T) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop c] with U hU
  have hU0 : 0 < U := hc.trans hU
  obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun w ↦ Complex.exp (-(l : ℂ) * w) / w := ⟨_, rfl⟩
  have hnorm : ∀ x y : ℝ,
      ‖Complex.exp (-(l : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))‖ = Real.exp (-l * x) := by
    intro x y
    rw [Complex.norm_exp]
    congr 1
    simp
  have hdiff : DifferentiableOn ℂ f (uIcc c U ×ℂ uIcc (-T) T) := by
    intro w hw
    have hre : c ≤ w.re := by
      have h1 : w.re ∈ uIcc c U := hw.1
      rw [uIcc_of_le hU.le] at h1
      exact h1.1
    have hw0 : w ≠ 0 := fun h0 ↦ by
      rw [h0, Complex.zero_re] at hre
      linarith
    rw [hf]
    exact (((differentiableAt_id.const_mul (-(l : ℂ))).cexp).div differentiableAt_id
      hw0).differentiableWithinAt
  have hrect : (∫ x : ℝ in c..U, f (x + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in c..U, f (x + (T : ℂ) * Complex.I)) +
      Complex.I • (∫ y : ℝ in -T..T, f ((U : ℂ) + y * Complex.I)) -
      Complex.I • (∫ y : ℝ in -T..T, f ((c : ℂ) + y * Complex.I)) = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨c, -T⟩ ⟨U, T⟩ hdiff
  have hside : ∀ τ : ℝ, |τ| = T →
      ‖∫ x : ℝ in c..U, f (x + (τ : ℂ) * Complex.I)‖ ≤ Real.exp (-l * c) / (l * T) := by
    intro τ hτ
    have hb : ∀ x : ℝ, ‖f (x + (τ : ℂ) * Complex.I)‖ ≤ Real.exp (-l * x) / T := by
      intro x
      rw [hf]
      simp only []
      rw [norm_div, hnorm]
      have h1 : T ≤ ‖(x : ℂ) + (τ : ℂ) * Complex.I‖ := by
        have h2 := Complex.abs_im_le_norm ((x : ℂ) + (τ : ℂ) * Complex.I)
        simpa [hτ] using h2
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT h1
    have hint : IntervalIntegrable (fun x : ℝ ↦ Real.exp (-l * x) / T) MeasureTheory.volume c U :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    refine (intervalIntegral.norm_integral_le_of_norm_le hU.le
      (Eventually.of_forall fun x _ ↦ hb x) hint).trans ?_
    have hderiv : ∀ x ∈ uIcc c U, HasDerivAt (fun x : ℝ ↦ -Real.exp (-l * x) / (l * T))
        (Real.exp (-l * x) / T) x := by
      intro x _
      have h1 : HasDerivAt (fun x : ℝ ↦ -l * x) (-l) x := by
        simpa using (hasDerivAt_id x).const_mul (-l)
      have h2 := (h1.exp.neg).div_const (l * T)
      convert h2 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have h3 : 0 ≤ Real.exp (-l * U) / (l * T) := by positivity
    have e : -Real.exp (-l * U) / (l * T) - -Real.exp (-l * c) / (l * T) =
        Real.exp (-l * c) / (l * T) - Real.exp (-l * U) / (l * T) := by ring
    rw [e]
    linarith
  have hV : ‖∫ y : ℝ in -T..T, f ((U : ℂ) + y * Complex.I)‖ ≤ 2 * T / U := by
    have hb : ∀ y ∈ uIoc (-T) T, ‖f ((U : ℂ) + (y : ℂ) * Complex.I)‖ ≤ 1 / U := by
      intro y _
      rw [hf]
      simp only []
      rw [norm_div, hnorm]
      have h1 : U ≤ ‖(U : ℂ) + (y : ℂ) * Complex.I‖ := by
        have h2 := Complex.abs_re_le_norm ((U : ℂ) + (y : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] at h2
        exact (le_abs_self U).trans h2
      have h2 : Real.exp (-l * U) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      exact div_le_div₀ zero_le_one h2 hU0 h1
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]] at h3
    calc _ ≤ 1 / U * (2 * T) := h3
      _ = 2 * T / U := by ring
  have hK : (∫ t in -T..T, Complex.exp (-(l : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)) =
      ∫ y : ℝ in -T..T, f ((c : ℂ) + y * Complex.I) := by
    rw [hf]
    simp only [Complex.mk_eq_add_mul_I]
  have hA := hside (-T) (by rw [abs_neg, abs_of_pos hT])
  have hB := hside T (abs_of_pos hT)
  simp only [smul_eq_mul] at hrect
  have hIK : Complex.I * (∫ y : ℝ in -T..T, f ((c : ℂ) + y * Complex.I)) =
      (∫ x : ℝ in c..U, f (x + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in c..U, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in -T..T, f ((U : ℂ) + y * Complex.I)) := by
    linear_combination -hrect
  have hn : ‖∫ y : ℝ in -T..T, f ((c : ℂ) + y * Complex.I)‖ =
      ‖Complex.I * (∫ y : ℝ in -T..T, f ((c : ℂ) + y * Complex.I))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hK, hn, hIK]
  have h4 := norm_add_le ((∫ x : ℝ in c..U, f (x + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in c..U, f (x + (T : ℂ) * Complex.I)))
      (Complex.I * (∫ y : ℝ in -T..T, f ((U : ℂ) + y * Complex.I)))
  have h5 := norm_sub_le (∫ x : ℝ in c..U, f (x + ((-T : ℝ) : ℂ) * Complex.I))
      (∫ x : ℝ in c..U, f (x + (T : ℂ) * Complex.I))
  rw [norm_mul, Complex.norm_I, one_mul] at h4
  have e : 2 * Real.exp (-l * c) / (l * T) =
      Real.exp (-l * c) / (l * T) + Real.exp (-l * c) / (l * T) := by ring
  rw [e]
  linarith

/-- For a Dirichlet series whose terms below the integer cutoff `m` vanish, the truncated
Perron integral differs from `arctan (T / c) / π` times the `m`-th term by `O(1 / T)`. -/
private theorem heckeLogDerivPolynomial_perron_error_false_perron (a : ℕ → ℂ) (s : ℂ) (m : ℕ)
    (c T : ℝ) (hm : 0 < m) (hc : 0 < c) (hT : 0 < T)
    (ha : LSeriesSummable a (s + (c : ℂ)))
    (hlow : ∀ n, n < m → LSeries.term a s n = 0) :
    ‖truncatedPerronIntegral (LSeries a) s m c T -
        ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) * LSeries.term a s m‖ ≤
      (m : ℝ) ^ c / (Real.pi * Real.log ((m + 1 : ℝ) / m) * T) *
        ∑' n : ℕ, ‖LSeries.term a (s + (c : ℂ)) n‖ := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  obtain ⟨l, hl⟩ : ∃ l : ℕ → ℝ, ∀ n : ℕ, l n = Real.log n - Real.log m := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ℝ, l₀ = Real.log ((m + 1 : ℝ) / m) := ⟨_, rfl⟩
  have hl₀pos : 0 < l₀ := by
    rw [hl₀]
    exact Real.log_pos (by rw [lt_div_iff₀ hm0]; linarith)
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℂ, ∀ n : ℕ, K n =
      ∫ t in -T..T, Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℂ, J = ∫ t in -T..T,
      LSeries a (s + ⟨c, t⟩) * ((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ) := ⟨_, rfl⟩
  have hwne : ∀ t : ℝ, (⟨c, t⟩ : ℂ) ≠ 0 := fun t h ↦ hc.ne' (congrArg Complex.re h)
  have hwnorm : ∀ t : ℝ, c ≤ ‖(⟨c, t⟩ : ℂ)‖ := fun t ↦
    (le_abs_self c).trans (Complex.abs_re_le_norm (⟨c, t⟩ : ℂ))
  have hwcont : Continuous fun t : ℝ ↦ (⟨c, t⟩ : ℂ) := by
    rw [show Complex.mk c = fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I c t]
    fun_prop
  have hkey : ∀ n : ℕ, ‖LSeries.term a s n‖ * Real.exp (-(l n) * c) =
      ‖LSeries.term a (s + (c : ℂ)) n‖ * (m : ℝ) ^ c := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn.ne',
        ite_eq_right hn.ne', hl n]
      simp only [Complex.add_re, Complex.ofReal_re]
      rw [Real.rpow_add hn0, Real.rpow_def_of_pos hm0 c, Real.rpow_def_of_pos hn0 c,
        show -(Real.log n - Real.log m) * c = Real.log m * c - Real.log n * c by ring,
        Real.exp_sub]
      have h1 : (n : ℝ) ^ s.re ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
      have h2 := Real.exp_ne_zero (Real.log n * c)
      field_simp
  have hpt : ∀ (n : ℕ) (t : ℝ),
      LSeries.term a (s + ⟨c, t⟩) n * ((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ) =
        LSeries.term a s n *
          (Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)) := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      have hm' : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      have e1 : (n : ℂ) ^ (⟨c, t⟩ : ℂ) = Complex.exp ((Real.log n : ℂ) * ⟨c, t⟩) := by
        rw [Complex.cpow_def_of_ne_zero hn', Complex.natCast_log]
      have e2 : ((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) = Complex.exp ((Real.log m : ℂ) * ⟨c, t⟩) := by
        rw [Complex.cpow_def_of_ne_zero hm', Complex.ofReal_log hm0.le]
      have e3 : Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) =
          Complex.exp ((Real.log m : ℂ) * ⟨c, t⟩) /
            Complex.exp ((Real.log n : ℂ) * ⟨c, t⟩) := by
        rw [← Complex.exp_sub, hl n]
        congr 1
        push_cast
        ring
      rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
        Complex.cpow_add _ _ hn', e1, e2, e3]
      have h1 := Complex.exp_ne_zero ((Real.log n : ℂ) * ⟨c, t⟩)
      have h2 : (n : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn']
        exact Complex.exp_ne_zero _
      have h3 := hwne t
      field_simp
  have hbound : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term a s n *
      (Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ))‖ ≤
        ‖LSeries.term a (s + (c : ℂ)) n‖ * ((m : ℝ) ^ c / c) := by
    intro n t
    rw [norm_mul, norm_div, Complex.norm_exp]
    have hre : (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)).re = -(l n) * c := by simp
    rw [hre]
    calc ‖LSeries.term a s n‖ * (Real.exp (-(l n) * c) / ‖(⟨c, t⟩ : ℂ)‖)
        ≤ ‖LSeries.term a s n‖ * (Real.exp (-(l n) * c) / c) := by
          gcongr
          exact hwnorm t
      _ = ‖LSeries.term a (s + (c : ℂ)) n‖ * ((m : ℝ) ^ c / c) := by
          rw [← mul_div_assoc, hkey n, mul_div_assoc]
  have hlim : ∀ t : ℝ, HasSum (fun n : ℕ ↦ LSeries.term a s n *
      (Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)))
      (LSeries a (s + ⟨c, t⟩) * ((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) := by
    intro t
    have hsum : LSeriesSummable a (s + ⟨c, t⟩) := LSeriesSummable.of_re_le_re (by simp) ha
    have h0 : HasSum (fun n : ℕ ↦ LSeries.term a (s + ⟨c, t⟩) n) (LSeries a (s + ⟨c, t⟩)) :=
      hsum.LSeriesHasSum
    exact ((h0.mul_right (((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ))).div_const (⟨c, t⟩ : ℂ)).congr_fun
      fun n ↦ (hpt n t).symm
  have hexch : HasSum (fun n : ℕ ↦ LSeries.term a s n * K n) J := by
    have h := intervalIntegral.hasSum_integral_of_dominated_convergence
      (μ := MeasureTheory.volume) (a := -T) (b := T)
      (F := fun (n : ℕ) (t : ℝ) ↦ LSeries.term a s n *
        (Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)))
      (f := fun t : ℝ ↦
        LSeries a (s + ⟨c, t⟩) * ((m : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ))
      (fun n _ ↦ ‖LSeries.term a (s + (c : ℂ)) n‖ * ((m : ℝ) ^ c / c))
      (fun n ↦ Continuous.aestronglyMeasurable (continuous_const.mul
        (((continuous_const.mul hwcont).cexp).div hwcont hwne)))
      (fun n ↦ Eventually.of_forall fun t _ ↦ hbound n t)
      (Eventually.of_forall fun t _ ↦ ha.norm.mul_right _)
      intervalIntegrable_const
      (Eventually.of_forall fun t _ ↦ hlim t)
    have h' : (fun n : ℕ ↦ LSeries.term a s n * K n) = fun n : ℕ ↦ ∫ t in -T..T,
        LSeries.term a s n *
          (Complex.exp (-((l n : ℝ) : ℂ) * (⟨c, t⟩ : ℂ)) / (⟨c, t⟩ : ℂ)) :=
      funext fun n ↦ by rw [hK n, intervalIntegral.integral_const_mul]
    rw [h', hJ]
    exact h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hKm : K m = 2 * Real.pi * ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) := by
    have h1 := truncatedPerronIntegral_one s (T := T) hc
    have h2 : truncatedPerronIntegral (fun _ ↦ 1) s 1 c T = K m / (2 * (Real.pi : ℂ)) := by
      rw [hK m, hl m]
      show (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) = _
      simp only [sub_self, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
        Complex.ofReal_one, Complex.one_cpow, one_mul]
    rw [h2] at h1
    rw [← h1]
    field_simp
  classical
  have hupd := hexch.update m 0
  have hbd : ∀ n : ℕ, ‖Function.update (fun n : ℕ ↦ LSeries.term a s n * K n) m 0 n‖ ≤
      ‖LSeries.term a (s + (c : ℂ)) n‖ * (2 * (m : ℝ) ^ c / (l₀ * T)) := by
    intro n
    have hnonneg : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ * (2 * (m : ℝ) ^ c / (l₀ * T)) := by
      positivity
    rw [Function.update_apply]
    split_ifs with hnm
    · simpa using hnonneg
    · rcases lt_or_gt_of_ne hnm with hlt | hgt
      · rw [hlow n hlt, zero_mul, norm_zero]
        exact hnonneg
      · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (hm.trans hgt)
        have hln : l₀ ≤ l n := by
          rw [hl₀, hl n, ← Real.log_div hn0.ne' hm0.ne']
          apply Real.log_le_log (by positivity)
          have h1 : (m : ℝ) + 1 ≤ n := by exact_mod_cast hgt
          gcongr
        have hlpos : 0 < l n := hl₀pos.trans_le hln
        have hker := heckeLogDerivPolynomial_perron_error_false_kernel (l n) c T hlpos hc hT
        have hKn : ‖K n‖ ≤ 2 * Real.exp (-(l n) * c) / (l₀ * T) := by
          rw [hK n]
          refine hker.trans ?_
          gcongr
        rw [norm_mul]
        calc ‖LSeries.term a s n‖ * ‖K n‖
            ≤ ‖LSeries.term a s n‖ * (2 * Real.exp (-(l n) * c) / (l₀ * T)) := by gcongr
          _ = (‖LSeries.term a s n‖ * Real.exp (-(l n) * c)) * (2 / (l₀ * T)) := by ring
          _ = ‖LSeries.term a (s + (c : ℂ)) n‖ * (2 * (m : ℝ) ^ c / (l₀ * T)) := by
              rw [hkey n]
              ring
  have hgsum : HasSum
      (fun n : ℕ ↦ ‖LSeries.term a (s + (c : ℂ)) n‖ * (2 * (m : ℝ) ^ c / (l₀ * T)))
      ((∑' n : ℕ, ‖LSeries.term a (s + (c : ℂ)) n‖) * (2 * (m : ℝ) ^ c / (l₀ * T))) :=
    ha.norm.hasSum.mul_right _
  have hfin := hupd.norm_le_of_bounded hgsum hbd
  have hI : truncatedPerronIntegral (LSeries a) s m c T = J / (2 * (Real.pi : ℂ)) := by
    rw [hJ]
    rfl
  have hid : truncatedPerronIntegral (LSeries a) s m c T -
      ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) * LSeries.term a s m =
      (0 - LSeries.term a s m * K m + J) / (2 * (Real.pi : ℂ)) := by
    rw [hI, hKm]
    field_simp
    ring
  have h2π : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    simp
  rw [hid, norm_div, h2π, div_le_iff₀ (by positivity), ← hl₀]
  refine hfin.trans (le_of_eq ?_)
  have h1 := hl₀pos.ne'
  have h2 := hT.ne'
  have h3 := Real.pi_ne_zero
  field_simp

/-- Every type level contains a number field: a lift of the rationals. -/
private theorem heckeLogDerivPolynomial_perron_error_false_numberField.{u} :
    ∃ (F : Type u) (_ : Field F), NumberField F := by
  let : Field (ULift.{u} ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact ⟨ULift.{u} ℚ, inferInstance, inferInstance⟩

/-- On the half-plane of absolute convergence the finite L-function of the trivial character is
the Dedekind zeta function. -/
private theorem heckeLogDerivPolynomial_perron_error_false_zeta
    (F : Type*) [Field F] [NumberField F] (s : halfPlane) :
    finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- Grouping the ideals by norm: to the right of one, the negative logarithmic derivative of
the continued finite L-function of the trivial character is the Dirichlet series of the
logarithmic-derivative coefficients. -/
private theorem heckeLogDerivPolynomial_perron_error_false_hasSum
    (F : Type*) [Field F] [NumberField F] (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hZS : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s) (w : ℂ) (hw : 1 < w.re) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0)) w
      (-logDeriv Z w) := by
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  have hw0 : w ≠ 0 := by
    intro h
    norm_num [h] at hw
  have hsum := (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ hZS ⟨w, hw⟩).2.2.neg
  refine (hsum.tsum_fiberwise normIndex).congr_fun ?_
  intro n
  symm
  rw [LSeries.term_of_ne_zero' hw0]
  let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ I.absNorm = n}
  let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
    { toFun := fun I ↦ ⟨I.val.val, I.val.property, I.property⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hnorm (I : normFiber) : I.val.absNorm = n := I.property.2
  rw [← e.symm.tsum_eq]
  change (∑' I : normFiber,
      -(-heckeIdealVonMangoldt (ideleClassNormTwist (1 : U[F]) 0) I.val /
        (I.val.absNorm : ℂ) ^ w)) =
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n / (n : ℂ) ^ w
  let : Finite normFiber :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
      (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hI.2)).to_subtype
  simp_rw [hnorm, neg_div, neg_neg, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
  rfl

/-- The coefficient at norm one vanishes: the only ideal of norm one is the unit ideal, and it
is not a positive power of a prime. -/
private theorem heckeLogDerivPolynomial_perron_error_false_coeff_one
    (F : Type*) [Field F] [NumberField F] :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) 1 = 0 := by
  rw [heckeLogDerivCoefficient]
  apply finsum_eq_zero_of_forall_eq_zero
  intro I
  have htop : I.val = ⊤ := Ideal.absNorm_eq_one_iff.mp I.property.2
  have h : ¬ ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ k : ℕ,
      0 < k ∧ I.val = v.asIdeal ^ k := by
    rintro ⟨v, k, hk, hvk⟩
    have h1 : v.asIdeal ^ k ≤ v.asIdeal := Ideal.pow_le_self hk.ne'
    rw [← hvk, htop, top_le_iff] at h1
    exact v.isPrime.ne_top h1
  simp [heckeIdealVonMangoldt, idealVonMangoldt, h]

/-- Some coefficient of positive index is nonzero: otherwise the continued Dedekind zeta
function would be constant to the right of one, contradicting its pole there. -/
private theorem heckeLogDerivPolynomial_perron_error_false_coeff_ne
    (F : Type*) [Field F] [NumberField F] (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hZS : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s)
    (hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ n : ℕ, n ≠ 0 ∧ heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n ≠ 0 := by
  by_contra hex
  have hcon : ∀ n : ℕ, n ≠ 0 →
      heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n = 0 :=
    fun n hn ↦ by_contra fun hne ↦ hex ⟨n, hn, hne⟩
  have hzero : ∀ w : ℂ, 1 < w.re → logDeriv Z w = 0 := by
    intro w hw
    have h := heckeLogDerivPolynomial_perron_error_false_hasSum F Z hZ hZS w hw
    have h0 : LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0))
        w 0 := by
      have hfun : LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0))
          w = fun _ ↦ 0 := by
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · rw [LSeries.term_of_ne_zero hn, hcon n hn, zero_div]
      rw [LSeriesHasSum, hfun]
      exact hasSum_zero
    exact neg_eq_zero.mp (h.unique h0)
  have hderiv : ∀ w : ℂ, 1 < w.re → deriv Z w = 0 := by
    intro w hw
    obtain ⟨-, hne, -⟩ := finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ hZS ⟨w, hw⟩
    have h := hzero w hw
    rw [logDeriv_apply, div_eq_zero_iff] at h
    exact h.resolve_right hne
  have hdiff : DifferentiableOn ℂ Z {w : ℂ | 1 < w.re} := fun w hw ↦
    (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ hZS
      ⟨w, hw⟩).1.differentiableAt.differentiableWithinAt
  have hconst : ∀ x : ℝ, 1 < x → Z x = Z 2 := by
    intro x hx
    exact (isOpen_lt continuous_const Complex.continuous_re).is_const_of_deriv_eq_zero
      (convex_halfSpace_re_gt 1).isPreconnected hdiff (fun w hw ↦ hderiv w hw)
      (show 1 < (x : ℂ).re by simpa using hx) (show 1 < (2 : ℂ).re by norm_num)
  have hres := tendsto_sub_one_mul_dedekindZeta_nhdsGT F
  have hlim0 : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * dedekindZeta F x) (𝓝[>] 1) (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * Z 2) (𝓝[>] 1) (𝓝 0) := by
      have h2 : Tendsto (fun x : ℝ ↦ ((x : ℂ) - 1) * Z 2) (𝓝 1)
          (𝓝 ((((1 : ℝ) : ℂ) - 1) * Z 2)) :=
        Continuous.tendsto (by fun_prop) 1
      simp only [Complex.ofReal_one, sub_self, zero_mul] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : 1 < x := hx
    rw [← hconst x hx1]
    congr 1
    exact hZSeries ⟨(x : ℂ), by simpa using hx1⟩
  have hzero' := tendsto_nhds_unique hres hlim0
  exact dedekindZeta_residue_ne_zero F (by exact_mod_cast hzero')

/-- For every number field the printed bound fails at the least integer cutoff `m` carrying a
nonzero coefficient, with the trivial character, `t₀ = 0`, `s = 1 + i` and `c = 1`: the cutoff
polynomial is the full `m`-th term, the truncated integral is within `O(1 / T)` of
`arctan T / π < 1 / 2` times that term, and the printed error is `O(1 / T)`. -/
private theorem heckeLogDerivPolynomial_perron_error_false_contra.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.heckeLogDerivPolynomial_perron_error.{u}) : False := by
  obtain ⟨C, hC, hbound⟩ := h F (1 : U[F]) 0 (by simp)
  obtain ⟨Z, hZ, hZS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s := fun s ↦ by
    rw [hZS s, heckeLogDerivPolynomial_perron_error_false_zeta]
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ,
      a = heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) := ⟨_, rfl⟩
  have hLS : ∀ w : ℂ, 1 < w.re → LSeriesHasSum a w (-logDeriv Z w) := fun w hw ↦ by
    rw [ha]
    exact heckeLogDerivPolynomial_perron_error_false_hasSum F Z hZ hZS w hw
  have hex : ∃ n : ℕ, n ≠ 0 ∧ a n ≠ 0 := by
    rw [ha]
    exact heckeLogDerivPolynomial_perron_error_false_coeff_ne F Z hZ hZS hZSeries
  have ha1 : a 1 = 0 := by
    rw [ha]
    exact heckeLogDerivPolynomial_perron_error_false_coeff_one F
  classical
  obtain ⟨m, ⟨hm0, ham⟩, hmin⟩ : ∃ m : ℕ, (m ≠ 0 ∧ a m ≠ 0) ∧
      ∀ n < m, ¬ (n ≠ 0 ∧ a n ≠ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun n hn ↦ Nat.find_min hex hn⟩
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · have hm1 : m = 1 := by omega
      rw [hm1] at ham
      exact absurd ha1 ham
    · exact hge
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ⟨1, 1⟩ := ⟨_, rfl⟩
  have hsre : s.re = 1 := by rw [hs]
  have hsim : s.im = 1 := by rw [hs]
  have hlow : ∀ n, n < m → LSeries.term a s n = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | h0
    · simp
    · have han : a n = 0 := by
        by_contra hne
        exact hmin n hn ⟨h0, hne⟩
      rw [LSeries.term_of_ne_zero h0, han, zero_div]
  have hsum : LSeriesSummable a (s + ((1 : ℝ) : ℂ)) :=
    (hLS _ (by simp [hsre])).LSeriesSummable
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm2
  have hm0R : (0 : ℝ) < m := by linarith
  have hP : heckeLogDerivPolynomial (1 : U[F]) (m : ℝ) s = LSeries.term a s m := by
    rw [ha]
    show ∑ n ∈ Finset.Icc 1 ⌊(m : ℝ)⌋₊,
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0)) s n = _
    rw [Nat.floor_natCast, ← ha]
    refine Finset.sum_eq_single_of_mem m (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩) ?_
    intro n hn hnm
    exact hlow n (lt_of_le_of_ne (Finset.mem_Icc.mp hn).2 hnm)
  have hI : ∀ T : ℝ,
      truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * ((0 : ℝ) : ℂ))) s m 1 T =
        truncatedPerronIntegral (LSeries a) s m 1 T := by
    intro T
    show (∫ t in -T..T, (fun w ↦ -logDeriv Z (w - Complex.I * ((0 : ℝ) : ℂ))) (s + ⟨1, t⟩) *
        ((m : ℝ) : ℂ) ^ (⟨1, t⟩ : ℂ) / (⟨1, t⟩ : ℂ)) / (2 * (Real.pi : ℂ)) =
      (∫ t in -T..T, LSeries a (s + ⟨1, t⟩) * ((m : ℝ) : ℂ) ^ (⟨1, t⟩ : ℂ) / (⟨1, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ))
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hre : 1 < (s + ⟨1, t⟩ : ℂ).re := by simp [hsre]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    rw [(hLS _ hre).LSeries_eq]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℂ, τ = LSeries.term a s m := ⟨_, rfl⟩
  have hτpos : 0 < ‖τ‖ := by
    rw [norm_pos_iff, hτ, LSeries.term_of_ne_zero hm0]
    refine div_ne_zero ham ?_
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hm0)]
    exact Complex.exp_ne_zero _
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℝ, S₀ = ∑' n : ℕ, ‖LSeries.term a (s + ((1 : ℝ) : ℂ)) n‖ :=
    ⟨_, rfl⟩
  have hS₀nn : 0 ≤ S₀ := hS₀ ▸ tsum_nonneg fun n ↦ norm_nonneg _
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ℝ, l₀ = Real.log ((m + 1 : ℝ) / m) := ⟨_, rfl⟩
  have hl₀pos : 0 < l₀ := by
    rw [hl₀]
    exact Real.log_pos (by rw [lt_div_iff₀ hm0R]; linarith)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (m : ℝ) := ⟨_, rfl⟩
  have hLnn : 0 ≤ L := hL ▸ Real.log_nonneg hmR.le
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * ((m : ℝ) + L ^ 2 + L / m) +
      (m : ℝ) / (Real.pi * l₀) * S₀ := ⟨_, rfl⟩
  have hBnn : 0 ≤ B := by
    rw [hB]
    have := Real.pi_pos
    positivity
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 2 * B / ‖τ‖ + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    have : 0 ≤ 2 * B / ‖τ‖ := by positivity
    linarith
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hsne : s ≠ 1 + Complex.I * ((0 : ℝ) : ℂ) := fun hcon ↦ by
    have h1 := congrArg Complex.im hcon
    rw [hsim] at h1
    simp at h1
  have hpr := hbound Z hZ hZSeries s (m : ℝ) 1 T hsre hsne hmR one_pos hT1
  rw [hP, hI T, Nat.floor_natCast, ite_eq_left rfl, Real.rpow_one, ← hτ, ← hL] at hpr
  have hper := heckeLogDerivPolynomial_perron_error_false_perron a s m 1 T (by omega) one_pos
    hT0 hsum hlow
  rw [Real.rpow_one, ← hτ, ← hS₀, ← hl₀] at hper
  obtain ⟨θ, hθv⟩ : ∃ θ : ℝ, θ = Real.arctan (T / 1) / Real.pi := ⟨_, rfl⟩
  have hθ : θ < 1 / 2 := by
    rw [hθv, div_lt_iff₀ Real.pi_pos]
    have := Real.arctan_lt_pi_div_two (T / 1)
    linarith
  rw [← hθv] at hper
  have htri : ‖τ‖ * (1 - θ) ≤ ‖τ - truncatedPerronIntegral (LSeries a) s m 1 T‖ +
      ‖truncatedPerronIntegral (LSeries a) s m 1 T - (θ : ℂ) * τ‖ := by
    have e : τ - (θ : ℂ) * τ = (τ - truncatedPerronIntegral (LSeries a) s m 1 T) +
        (truncatedPerronIntegral (LSeries a) s m 1 T - (θ : ℂ) * τ) := by ring
    have e2 : ‖τ - (θ : ℂ) * τ‖ = ‖τ‖ * (1 - θ) := by
      rw [show τ - (θ : ℂ) * τ = ((1 - θ : ℝ) : ℂ) * τ by push_cast; ring, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg (by linarith), mul_comm]
    rw [← e2, e]
    exact norm_add_le _ _
  have hsumB : C * ((m : ℝ) / (T * 1) + L ^ 2 / T + 1 * L / (T * m)) +
      (m : ℝ) / (Real.pi * l₀ * T) * S₀ = B / T := by
    rw [hB]
    have h1 := hT0.ne'
    have h2 := Real.pi_ne_zero
    have h3 := hl₀pos.ne'
    have h4 := hm0R.ne'
    field_simp
  have hfinal : ‖τ‖ * (1 - θ) ≤ B / T := by
    rw [← hsumB]
    linarith
  have h1 : ‖τ‖ / 2 ≤ ‖τ‖ * (1 - θ) := by nlinarith
  have h2 : ‖τ‖ / 2 * T ≤ B := (le_div_iff₀ hT0).mp (h1.trans hfinal)
  have h3 : ‖τ‖ / 2 * T = B + ‖τ‖ / 2 := by
    rw [hTdef]
    have h4 := hτpos.ne'
    field_simp
  linarith

/-- Paper: Equation (B.7.1.11), p. 646. Over the rationals take the trivial
character, `t₀ = 0`, `s = 1 + i`, `x = 2` and `c = 1`. The integral
tends to the half-weight sum as `T → +∞`. The full sum differs by
`log(2) / (2 · 2^s) ≠ 0`, whereas the printed error tends to zero. -/
theorem Printed.heckeLogDerivPolynomial_perron_error_false :
    ¬ Printed.heckeLogDerivPolynomial_perron_error := by
  intro h
  obtain ⟨F, _, _⟩ := heckeLogDerivPolynomial_perron_error_false_numberField
  exact heckeLogDerivPolynomial_perron_error_false_contra F h

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

/-- Every type level contains a number field: a lift of the rationals. -/
private theorem dedekindZeta_perron_contour_in_zeroFreeRegion_false_numberField.{u} :
    ∃ (F : Type u) (_ : Field F), NumberField F := by
  let : Field (ULift.{u} ℚ) := { ULift.ring, ULift.groupWithZero, Equiv.ulift.field with }
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) :=
    { to_finiteDimensional := Module.Finite.ulift (R := ℚ) (M := ℚ) }
  exact ⟨ULift.{u} ℚ, inferInstance, inferInstance⟩

/-- On the half-plane of absolute convergence the finite L-function of the trivial character is
the Dedekind zeta function. -/
private theorem dedekindZeta_perron_contour_in_zeroFreeRegion_false_zeta
    (F : Type*) [Field F] [NumberField F] (s : halfPlane) :
    finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- For every number field, the printed claim fails at the top left corner of the contour.
The width is the proved zero-free width with its numerator shrunk, `t₀ = 0`, `t = 2`,
`T = 4`, `c = 1`, and `α` is the midpoint of `η(6) / η(4) = log (7 B) / log (9 B)` and one.
Then `δ = α η(4) > η(6)`, so the corner `-δ + 4 i` lies strictly outside the region at
shifted height 6. -/
private theorem dedekindZeta_perron_contour_in_zeroFreeRegion_false_contra.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.dedekindZeta_perron_contour_in_zeroFreeRegion.{u}) : False := by
  obtain ⟨A₀, hA₀, hF⟩ := finiteHeckeL_zeroFreeRegion.{u}
  obtain ⟨B, hB, hzf⟩ := hF F (1 : U[F])
  obtain ⟨Z, hZ, hZS⟩ := finiteHeckeL_exists_continuation (1 : U[F])
  have hZSeries : ∀ s : halfPlane, Z s = dedekindZeta F s := fun s ↦ by
    rw [hZS s, dedekindZeta_perron_contour_in_zeroFreeRegion_false_zeta]
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Module.finrank ℚ F : ℝ) ^ 4 := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    rw [hd]
    have : (0 : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast Module.finrank_pos
    positivity
  rw [← hd] at hzf
  have hlogpos : ∀ v : ℝ, 0 < Real.log (B * (|v| + 3)) := fun v ↦
    Real.log_pos (by nlinarith [abs_nonneg v])
  have hlog3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = min (A₀ / d) (Real.log (B * 3) / 2) := ⟨_, rfl⟩
  have hA : 0 < A := hAdef ▸ lt_min (div_pos hA₀ hd0) (by positivity)
  have hA1 : A ≤ A₀ / d := hAdef ▸ min_le_left _ _
  have hA2 : A ≤ Real.log (B * 3) / 2 := hAdef ▸ min_le_right _ _
  have hmaps : MapsTo (fun v : ℝ ↦ A / Real.log (B * (|v| + 3))) (Ici 0) (Ioc 0 (1 / 2)) := by
    intro v _
    refine ⟨div_pos hA (hlogpos v), ?_⟩
    rw [div_le_iff₀ (hlogpos v)]
    have : Real.log (B * 3) ≤ Real.log (B * (|v| + 3)) :=
      Real.log_le_log (by linarith) (by nlinarith [abs_nonneg v])
    linarith
  have hzero : ∀ z : ℂ, 1 - (fun v : ℝ ↦ A / Real.log (B * (|v| + 3))) |z.im| < z.re →
      meromorphicOrderAt Z z ≤ 0 := by
    intro z hz
    apply hzf Z hZ hZS z
    simp only [abs_abs] at hz
    have h1 : A / Real.log (B * (|z.im| + 3)) ≤ A₀ / d / Real.log (B * (|z.im| + 3)) :=
      div_le_div_of_nonneg_right hA1 (hlogpos z.im).le
    rw [div_div] at h1
    linarith
  have h7 : 0 < Real.log (B * 7) := Real.log_pos (by linarith)
  have h9 : 0 < Real.log (B * 9) := Real.log_pos (by linarith)
  have h79 : Real.log (B * 7) < Real.log (B * 9) :=
    Real.log_lt_log (by linarith) (by linarith)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.log (B * 7) / Real.log (B * 9) := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ div_pos h7 h9
  have hr1 : r < 1 := hr ▸ (div_lt_one h9).mpr h79
  have hα : (r + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hδ : 0 < (r + 1) / 2 * (A / Real.log (B * (|(|(4 : ℝ) - 0|)| + 3))) :=
    mul_pos hα.1 (div_pos hA (hlogpos _))
  have key : 1 - A / Real.log (B * (|(|(2 : ℝ) + 4 - 0|)| + 3)) <
      1 + -((r + 1) / 2 * (A / Real.log (B * (|(|(4 : ℝ) - 0|)| + 3)))) :=
    h F (1 : U[F]) 0 (by simp) Z hZ hZSeries A B hA hB hmaps hzero
      ((r + 1) / 2) 2 4 1 hα (by norm_num) (by norm_num) one_pos
      (-((r + 1) / 2 * (A / Real.log (B * (|(|(4 : ℝ) - 0|)| + 3)))))
      ⟨le_rfl, by linarith⟩ 4 ⟨by norm_num, le_rfl⟩ (Or.inl rfl)
  rw [show |(|(2 : ℝ) + 4 - 0|)| + 3 = 9 by norm_num,
    show |(|(4 : ℝ) - 0|)| + 3 = 7 by norm_num] at key
  have hrA : r * (A / Real.log (B * 7)) = A / Real.log (B * 9) := by
    rw [hr]
    field_simp
  have hgap : 0 < (1 - r) * (A / Real.log (B * 7)) := mul_pos (by linarith) (div_pos hA h7)
  linarith

/-- Paper: Contour preceding Equation (B.7.1.12), p. 647. Take `t₀ = 0`,
`t = 2`, `T = 4`, and `c = 1`. At the top left corner the shifted
height is 6. Take the trivial character over the rationals and any genuine
logarithmic zero-free width from Proposition B.6.1.1, shrinking its numerator
to ensure the range condition. For every such width, `η(6) / η(4) < 1`.
Choose `α` strictly between that ratio and one. -/
theorem Printed.dedekindZeta_perron_contour_in_zeroFreeRegion_false :
    ¬ Printed.dedekindZeta_perron_contour_in_zeroFreeRegion := by
  intro h
  obtain ⟨F, _, _⟩ := dedekindZeta_perron_contour_in_zeroFreeRegion_false_numberField
  exact dedekindZeta_perron_contour_in_zeroFreeRegion_false_contra F h

end RiemannMasullo
