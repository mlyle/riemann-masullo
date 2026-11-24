module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # The divisor of the Hecke L-function

Masullo, §13.3.1, p. 522. The two sides of the proposed trace formula are
continuous on the Mellin-jet test subspace. The printed equality and codimension
claim are recorded in `Sec3_Printed.lean`.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "sectionCharacters(" τ ")" => {χ : U𝔽 // ∀ t, χ (τ t) = 1}

-- TODO(paper-gap): §§13.1 and 13.2 are headings with no text on p. 522.
-- TODO(paper-gap): Footnote 1 to Theorem 13.3.1.1 says “Correct statement.” The
-- cited `traceFormula` uses a positive-width strip, full zero orders and tests
-- vanishing on the norm-one classes. The manuscript gives no derivation of the
-- changes to the zero weights, test space or local coefficients.

/-- Paper: (13.3.1.1), p. 522. The spectral multiplicity is the order of the
completed Hecke zero capped at the degree of the number field. -/
def criticalTraceMultiplicity (χ : U𝔽) (s : ℂ) (_hs : 0 < ord(χ, s)) : ℕ :=
  min (ord(χ, s)).toNat (Module.finrank ℚ F)

/-- Paper: (13.3.1.1), p. 522. A zero whose order exceeds the field degree is
counted with weight equal to the degree. -/
theorem criticalTraceMultiplicity_of_degree_le (χ : U𝔽) (s : ℂ) (hs : 0 < ord(χ, s))
    (_h : Module.finrank ℚ F ≤ (ord(χ, s)).toNat) :
    criticalTraceMultiplicity χ s hs = Module.finrank ℚ F := by
  unfold criticalTraceMultiplicity
  exact min_eq_right _h

local notation "momentIntegrand(" χ ", " k ", " φ ")" =>
  (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g)

private theorem criticalTraceMoment_isLinearMap_integrable (χ : U𝔽) (k : ℕ) (φ : D𝔽) :
    Integrable (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g) μ𝔽 := by
  have hφ : Continuous (φ : D𝔽).val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hc : HasCompactSupport (φ : D𝔽).val := φ.property.2
  have hlog : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous))).log fun g ↦
        ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hj : Continuous (spectralZeroJet (F := F) χ 0 0 k) := by
    unfold spectralZeroJet
    exact (ideleClassNormTwist χ _).continuous.mul
      ((Complex.continuous_ofReal.comp hlog).pow k)
  exact (hφ.mul hj).integrable_of_hasCompactSupport (hc.mul_right)

/-- Paper: (13.3.1.2), p. 522. A fixed character and jet order give a linear
functional by integration against the character times a power of the log norm. -/
theorem criticalTraceMoment_isLinearMap (χ : U𝔽) (k : ℕ) :
    IsLinearMap ℂ (fun φ : D𝔽 ↦ ∫ g, momentIntegrand(χ, k, φ) g ∂μ𝔽) := by
  refine ⟨fun φ ψ ↦ ?_, fun c φ ↦ ?_⟩
  · have e : (fun g : C𝔽 ↦ ((φ + ψ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ φ.val g * spectralZeroJet (F := F) χ 0 0 k g +
          ψ.val g * spectralZeroJet (F := F) χ 0 0 k g := by
      ext g
      exact add_mul _ _ _
    simp only [e]
    exact integral_add (criticalTraceMoment_isLinearMap_integrable χ k φ)
      (criticalTraceMoment_isLinearMap_integrable χ k ψ)
  · have e : (fun g : C𝔽 ↦ ((c • φ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ c * (φ.val g * spectralZeroJet (F := F) χ 0 0 k g) := by
      ext g
      exact mul_assoc _ _ _
    simp only [e]
    exact integral_const_mul c _

/-- Paper: (13.3.1.2), p. 522. The test subspace is the common kernel of the
first `[F : ℚ]` log-norm moments for each unitary character trivial on the section.
Deviation: The degree bounds the jet orders in each character, with no finite
codimension imposed on the common kernel. -/
def criticalTraceTestSubmodule (τ : ℝ≥0ˣ →ₜ* C𝔽) : Submodule ℂ D𝔽 :=
  ⨅ (χ : sectionCharacters(τ)) (k : Fin (Module.finrank ℚ F)),
    ((criticalTraceMoment_isLinearMap χ.val k.val).mk' _).ker

/-- Differentiation under the integral sign for exponential moments on a measure space: if
every moment of `h` against `exp (σ * ℓ x)` is integrable for `σ` in an open interval, then on
the corresponding vertical strip the `k`th derivative of the integral of `h x * exp (w * ℓ x)`
is the `k`th moment. Adapted from `iteratedDeriv_exp_moment_of_measurable` in
`Ch09_HardySobolev/Sec2.lean`. -/
private theorem mem_criticalTraceTestSubmodule_iff_expMoment {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {h : X → ℂ} {ℓ : X → ℝ} (hℓ : Measurable ℓ) {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ,
      Integrable (fun x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (ℓ x : ℂ))) μ)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    iteratedDeriv k (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) z =
      ∫ x, h x * (ℓ x : ℂ) ^ k * Complex.exp (z * (ℓ x : ℂ)) ∂μ := by
  let F : ℕ → ℂ → X → ℂ := fun n w x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))
  have hℓc : Measurable fun x ↦ (ℓ x : ℂ) := Complex.measurable_ofReal.comp hℓ
  have hexpc : ∀ w : ℂ, Measurable fun x ↦ Complex.exp (w * (ℓ x : ℂ)) := fun w ↦
    Complex.measurable_exp.comp (hℓc.const_mul w)
  have hm : AEStronglyMeasurable h μ := by
    refine ((hint z.re hz 0).aestronglyMeasurable.mul
      (hexpc (-(z.re : ℂ))).aestronglyMeasurable).congr (ae_of_all _ fun x ↦ ?_)
    show h x * (ℓ x : ℂ) ^ 0 * Complex.exp ((z.re : ℂ) * (ℓ x : ℂ)) *
      Complex.exp (-(z.re : ℂ) * (ℓ x : ℂ)) = h x
    rw [pow_zero, mul_one, mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel,
      Complex.exp_zero, mul_one]
  have hFm : ∀ n w, AEStronglyMeasurable (F n w) μ := fun n w ↦
    (hm.mul (hℓc.pow_const n).aestronglyMeasurable).mul (hexpc w).aestronglyMeasurable
  have hnorm : ∀ n (w : ℂ) (x : X),
      ‖F n w x‖ = ‖h x‖ * |ℓ x| ^ n * Real.exp (w.re * ℓ x) := by
    intro n w x
    have hre : (w * (ℓ x : ℂ)).re = w.re * ℓ x := by simp
    show ‖h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))‖ = _
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      hre]
  have hFi : ∀ n (w : ℂ), w.re ∈ Ioo α β → Integrable (F n w) μ := fun n w hw ↦
    (hint w.re hw n).mono (hFm n w) (ae_of_all _ fun x ↦ le_of_eq (by
      show ‖F n w x‖ = ‖F n (w.re : ℂ) x‖
      rw [hnorm, hnorm, Complex.ofReal_re]))
  have hderiv : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      HasDerivAt (fun w ↦ ∫ x, F n w x ∂μ) (∫ x, F (n + 1) w x ∂μ) w := by
    intro n w hw
    obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ α < w.re - ε ∧ w.re + ε < β := by
      have h0 : 0 < min (w.re - α) (β - w.re) := lt_min (sub_pos.2 hw.1) (sub_pos.2 hw.2)
      have h1 := min_le_left (w.re - α) (β - w.re)
      have h2 := min_le_right (w.re - α) (β - w.re)
      exact ⟨min (w.re - α) (β - w.re) / 2, half_pos h0, by linarith, by linarith⟩
    have hlo : ((w.re - ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨hεa, by linarith⟩
    have hhi : ((w.re + ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨by linarith, hεb⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w hε)
      (Filter.Eventually.of_forall (hFm n)) (hFi n w hw) (hFm (n + 1) w)
      (ae_of_all _ fun x w' hw' ↦ ?_)
      ((hFi (n + 1) _ hlo).norm.add (hFi (n + 1) _ hhi).norm)
      (ae_of_all _ fun x w' _ ↦ ?_)).2
    · show ‖F (n + 1) w' x‖ ≤
        ‖F (n + 1) ((w.re - ε : ℝ) : ℂ) x‖ + ‖F (n + 1) ((w.re + ε : ℝ) : ℂ) x‖
      rw [hnorm, hnorm, hnorm, Complex.ofReal_re, Complex.ofReal_re]
      have h2 : ‖w' - w‖ < ε := by
        rw [← dist_eq_norm]
        exact hw'
      have h1 := (Complex.abs_re_le_norm (w' - w)).trans_lt h2
      rw [Complex.sub_re] at h1
      obtain ⟨hl, hu⟩ := abs_lt.1 h1
      have hexp : Real.exp (w'.re * ℓ x) ≤
          Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x) := by
        rcases le_total 0 (ℓ x) with hx | hx
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w.re + ε - w'.re) hx
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_left (Real.exp_pos _).le)
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w'.re - w.re + ε) (neg_nonneg.2 hx)
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_right (Real.exp_pos _).le)
      calc ‖h x‖ * |ℓ x| ^ (n + 1) * Real.exp (w'.re * ℓ x)
          ≤ ‖h x‖ * |ℓ x| ^ (n + 1) *
            (Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := mul_add _ _ _
    · exact (((hasDerivAt_id' w').mul_const (ℓ x : ℂ)).cexp.const_mul
        (h x * (ℓ x : ℂ) ^ n)).congr_deriv (by
          show h x * (ℓ x : ℂ) ^ n * (Complex.exp (w' * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))) =
            h x * (ℓ x : ℂ) ^ (n + 1) * Complex.exp (w' * (ℓ x : ℂ))
          ring)
  have hS : IsOpen {w : ℂ | w.re ∈ Ioo α β} := isOpen_Ioo.preimage Complex.continuous_re
  have hM : (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) =
      fun w ↦ ∫ x, F 0 w x ∂μ := by
    funext w
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show h x * Complex.exp (w * (ℓ x : ℂ)) = h x * (ℓ x : ℂ) ^ 0 * Complex.exp (w * (ℓ x : ℂ))
    rw [pow_zero, mul_one]
  have hiter : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) w = ∫ x, F n w x ∂μ := by
    intro n
    induction n with
    | zero =>
      intro w _
      rw [iteratedDeriv_zero]
    | succ n ih =>
      intro w hw
      have hev : iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) =ᶠ[nhds w]
          fun w ↦ ∫ x, F n w x ∂μ :=
        (hS.eventually_mem hw).mono fun w' hw' ↦ ih w' hw'
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hderiv n w hw).deriv
  rw [hM]
  exact hiter k z hz

/-- Twisting a unitary character by a purely imaginary power of the norm gives a unitary
character. -/
private theorem mem_criticalTraceTestSubmodule_iff_unitaryTwist (χ : U𝔽) (y : ℝ) :
    ∃ η : U𝔽, ∀ g : C𝔽, (η g : ℂ) = ideleClassNormTwist χ ((y : ℂ) * Complex.I) g := by
  let c := ideleClassNormTwist χ ((y : ℂ) * Complex.I)
  have hunit (g : C𝔽) : ‖c g‖ = 1 := by
    change ‖(χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ ((y : ℂ) * Complex.I))‖ = 1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  exact ⟨(⟨⟨⟨fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hunit g)⟩, Subtype.ext c.map_one⟩,
      fun g k ↦ Subtype.ext (c.map_mul g k)⟩, c.continuous.subtype_mk _⟩ : C𝔽 →ₜ* Circle),
    fun g ↦ rfl⟩

/-- Along a continuous homomorphic section of the norm, the idele class measure is a nonzero
multiple of the product of `dt/t` and the norm-one class measure, so integrals of continuous
compactly supported functions are iterated integrals up to that constant. -/
private theorem mem_criticalTraceTestSubmodule_iff_decomp (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : C𝔽 → ℂ, Continuous f → HasCompactSupport f →
      ∫ x, f x ∂μ𝔽 = c * ∫ t : ℝ≥0ˣ, (∫ g : C₁, f (τ t * g.val)
        ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar := by
  let : MeasurableSpace C₁ := Subtype.instMeasurableSpace
  let ν := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hc
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : ν.IsHaarMeasure := hspec.2.2.2.1
  have hn : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hp (x : C𝔽) : x / τ (ideleClassNorm F x) ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  have hnτ (p : ℝ≥0ˣ × C₁) : ideleClassNorm F (τ p.1 * p.2.val) = p.1 := by
    rw [map_mul, hτ, MonoidHom.mem_ker.mp p.2.property, mul_one]
  let e : (ℝ≥0ˣ × C₁) ≃ₜ* C𝔽 :=
    { toFun := fun p ↦ τ p.1 * p.2.val
      invFun := fun x ↦ (ideleClassNorm F x, ⟨x / τ (ideleClassNorm F x), hp x⟩)
      left_inv := fun p ↦ by
        refine Prod.ext (hnτ p) (Subtype.ext ?_)
        change τ p.1 * p.2.val / τ (ideleClassNorm F (τ p.1 * p.2.val)) = p.2.val
        rw [hnτ p, mul_div_cancel_left]
      right_inv := fun x ↦ by
        change τ (ideleClassNorm F x) * (x / τ (ideleClassNorm F x)) = x
        exact mul_div_cancel _ _
      map_mul' := fun p q ↦ by
        change τ (p.1 * q.1) * (p.2.val * q.2.val) = τ p.1 * p.2.val * (τ q.1 * q.2.val)
        rw [map_mul, mul_mul_mul_comm]
      continuous_toFun :=
        (τ.continuous.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
      continuous_invFun :=
        hn.prodMk ((continuous_id.div' (τ.continuous.comp hn)).subtype_mk _) }
  let P := (positiveRealHaar.prod ν).map e
  obtain ⟨c, hc0, hμ⟩ : ∃ c : ℝ≥0, c ≠ 0 ∧ μ𝔽 = c • P :=
    ⟨_, (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne',
      Measure.isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hc0, fun f hf hfc ↦ ?_⟩
  have he : Measurable e := e.continuous.measurable
  have hfi : Integrable (f ∘ e) (positiveRealHaar.prod ν) :=
    (hf.comp e.continuous).integrable_of_hasCompactSupport (hfc.comp_homeomorph e.toHomeomorph)
  rw [hμ, integral_smul_nnreal_measure, integral_map he.aemeasurable hf.aestronglyMeasurable,
    integral_prod (fun p ↦ f (e p)) hfi, NNReal.smul_def, Complex.real_smul]
  rfl

/-- The `k`th derivative of the printed Mellin integral at `z` is the iterated integral,
along the norm section, of the test times the twist `χ |·|^z` times the `k`th power of the
log norm. -/
private theorem mem_criticalTraceTestSubmodule_iff_mellin (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (φ : D𝔽) (z : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ ↦ ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
        (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar) z =
      ∫ t : ℝ≥0ˣ, (∫ g : C₁, φ.val (τ t * g.val) * ideleClassNormTwist χ z (τ t * g.val) *
          (Real.log ((ideleClassNorm F (τ t * g.val)).val : ℝ) : ℂ) ^ k
            ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar := by
  let : MeasurableSpace C₁ := Subtype.instMeasurableSpace
  let ν := normOneIdeleClassTamagawaMeasure F
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hc
  have hspec := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : ν.IsHaarMeasure := hspec.2.2.2.1
  have hφ : Continuous φ.val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hχc : Continuous (fun x : C𝔽 ↦ (χ x : ℂ)) := continuous_subtype_val.comp χ.continuous
  have hpos (t : ℝ≥0ˣ) : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hval : Continuous (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp Units.continuous_val
  let ℓ : ℝ≥0ˣ → ℝ := fun t ↦ Real.log ((t : ℝ≥0) : ℝ)
  have hℓ : Continuous ℓ := hval.log fun t ↦ (hpos t).ne'
  let G : ℝ≥0ˣ → ℂ := fun t ↦ ∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ) ∂ν
  have hG : Continuous G := by
    have := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun t (g : C₁) ↦ φ.val (τ t * g.val) * (χ g.val : ℂ))
      ((hφ.comp ((τ.continuous.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd))).mul
        (hχc.comp (continuous_subtype_val.comp continuous_snd))) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  let K := (fun x : C𝔽 ↦ ideleClassNorm F x) '' tsupport φ.val
  have hK : IsCompact K :=
    φ.property.2.isCompact.image (isProperMap_ideleClassNorm F).continuous
  have hnτ (t : ℝ≥0ˣ) (g : C₁) : ideleClassNorm F (τ t * g.val) = t := by
    rw [map_mul, hτ t, MonoidHom.mem_ker.mp g.property, mul_one]
  have hGK (t : ℝ≥0ˣ) (ht : t ∉ K) : G t = 0 := by
    have hz : ∀ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ) = 0 := by
      intro g
      have hφz : φ.val (τ t * g.val) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        exact ht ⟨_, hm, hnτ t g⟩
      rw [hφz, zero_mul]
    simp only [G, hz, integral_zero]
  let h : ℝ≥0ˣ → ℂ := fun t ↦ (χ (τ t) : ℂ) * G t
  have hh : Continuous h := (hχc.comp τ.continuous).mul hG
  have hhc : HasCompactSupport h :=
    HasCompactSupport.intro hK fun t ht ↦ by simp only [h, hGK t ht, mul_zero]
  have hcpow (t : ℝ≥0ˣ) (s : ℂ) : (((t : ℝ≥0) : ℝ) : ℂ) ^ s = Complex.exp (s * (ℓ t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos t).ne'),
      ← Complex.ofReal_log (hpos t).le, mul_comm]
  have hfun : (fun s : ℂ ↦ ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s * G t
      ∂positiveRealHaar) = fun s ↦ ∫ t, h t * Complex.exp (s * (ℓ t : ℂ)) ∂positiveRealHaar := by
    funext s
    congr 1
    funext t
    rw [hcpow]
    ring
  have hint : ∀ σ ∈ Ioo (z.re - 1) (z.re + 1), ∀ n : ℕ, Integrable
      (fun t ↦ h t * (ℓ t : ℂ) ^ n * Complex.exp ((σ : ℂ) * (ℓ t : ℂ))) positiveRealHaar := by
    intro σ _ n
    exact ((hh.mul ((Complex.continuous_ofReal.comp hℓ).pow n)).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp hℓ)))).integrable_of_hasCompactSupport
      (hhc.mul_right.mul_right)
  change iteratedDeriv k (fun s : ℂ ↦ ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s * G t
    ∂positiveRealHaar) z = _
  rw [hfun, mem_criticalTraceTestSubmodule_iff_expMoment hℓ.measurable hint k
    ⟨by linarith, by linarith⟩]
  congr 1
  funext t
  have e (g : C₁) : φ.val (τ t * g.val) * ideleClassNormTwist χ z (τ t * g.val) *
      (Real.log ((ideleClassNorm F (τ t * g.val)).val : ℝ) : ℂ) ^ k =
      ((χ (τ t) : ℂ) * (ℓ t : ℂ) ^ k * Complex.exp (z * (ℓ t : ℂ))) *
        (φ.val (τ t * g.val) * (χ g.val : ℂ)) := by
    change φ.val (τ t * g.val) * ((χ (τ t * g.val) : ℂ) *
      ((((ideleClassNorm F (τ t * g.val) : ℝ≥0) : ℝ) : ℂ) ^ z)) *
      (Real.log ((ideleClassNorm F (τ t * g.val)).val : ℝ) : ℂ) ^ k = _
    rw [hnτ t g, hcpow, map_mul, Circle.coe_mul]
    ring
  simp only [e, integral_const_mul]
  simp only [h, G]
  ring

/-- Paper: (13.3.1.2), p. 522. Membership in the test subspace is equivalent to
the printed Mellin-derivative conditions at `−i x₀(χ)` for all unitary characters.
The continuous norm section and the exponent along it are given explicitly. -/
theorem mem_criticalTraceTestSubmodule_iff (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) :
    φ ∈ criticalTraceTestSubmodule τ ↔
      ∀ (χ : U𝔽) (x : ℝ),
        (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) →
        ∀ k : Fin (Module.finrank ℚ F),
          iteratedDeriv k.val (fun s : ℂ ↦
            ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
              (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ)
                ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar)
            (-((x : ℂ) * Complex.I)) = 0 := by
  obtain ⟨c, hc0, hc⟩ := mem_criticalTraceTestSubmodule_iff_decomp τ _hτ
  have hφ : Continuous φ.val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hlog : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous))).log fun g ↦
        ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))
  -- Each twisted log-norm moment is `c` times the printed Mellin derivative.
  have key (χ : U𝔽) (z : ℂ) (k : ℕ) :
      (∫ g, φ.val g * ideleClassNormTwist χ z g *
          (Real.log ((ideleClassNorm F g).val : ℝ) : ℂ) ^ k ∂μ𝔽) =
        c * iteratedDeriv k (fun s : ℂ ↦ ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
          (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ) ∂normOneIdeleClassTamagawaMeasure F)
            ∂positiveRealHaar) z := by
    rw [mem_criticalTraceTestSubmodule_iff_mellin τ _hτ χ φ z k]
    exact hc _ ((hφ.mul (ideleClassNormTwist χ z).continuous).mul
      ((Complex.continuous_ofReal.comp hlog).pow k)) φ.property.2.mul_right.mul_right
  have hmom (η : U𝔽) (k : ℕ) :
      (∫ g, momentIntegrand(η, k, φ) g ∂μ𝔽) =
        ∫ g, φ.val g * ideleClassNormTwist η 0 g *
          (Real.log ((ideleClassNorm F g).val : ℝ) : ℂ) ^ k ∂μ𝔽 := by
    congr 1
    funext g
    unfold spectralZeroJet
    simp only [Complex.ofReal_zero, zero_mul, add_zero, mul_assoc]
  have hmem : φ ∈ criticalTraceTestSubmodule τ ↔
      ∀ (η : sectionCharacters(τ)) (k : Fin (Module.finrank ℚ F)),
        (∫ g, momentIntegrand(η.val, k.val, φ) g ∂μ𝔽) = 0 := by
    simp only [criticalTraceTestSubmodule, Submodule.mem_iInf, LinearMap.mem_ker,
      IsLinearMap.mk'_apply]
  rw [hmem]
  constructor
  · intro h χ x hx k
    obtain ⟨η, hη⟩ := mem_criticalTraceTestSubmodule_iff_unitaryTwist χ (-x)
    have hητ : ∀ t, η (τ t) = 1 := by
      intro t
      apply Subtype.ext
      rw [hη]
      change (χ (τ t) : ℂ) * ((((ideleClassNorm F (τ t) : ℝ≥0) : ℝ) : ℂ) ^
        (((-x : ℝ) : ℂ) * Complex.I)) = 1
      rw [_hτ t, hx t, ← Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt t)).ne')]
      simp
    have h0 := h ⟨η, hητ⟩ k
    rw [hmom] at h0
    have htw : ∀ g,
        ideleClassNormTwist η 0 g = ideleClassNormTwist χ (-((x : ℂ) * Complex.I)) g := by
      intro g
      change (η g : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) = _
      rw [Complex.cpow_zero, mul_one, hη]
      congr 2
      push_cast
      ring
    simp only [htw] at h0
    rw [key] at h0
    exact (mul_eq_zero.mp h0).resolve_left hc0
  · intro h η k
    have hη0 : ∀ t : ℝ≥0ˣ, (η.val (τ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) * Complex.I) := by
      intro t
      rw [η.property t]
      simp
    have hD := h η.val 0 hη0 k
    have hz : (-(((0 : ℝ) : ℂ) * Complex.I)) = 0 := by simp
    rw [hz] at hD
    rw [hmom, key, hD, mul_zero]

open scoped NumberField.AdeleRing in
/-- The finite sign idele with real coordinate one gives a nontrivial involution. -/
private theorem criticalTrace_rat_sign :
    ∃ g : IdeleClassGroup (𝓞 ℚ) ℚ, g ≠ 1 ∧ g ^ 2 = 1 := by
  have hs : ((1, -1) : 𝔸[ℚ]) * (1, -1) = 1 :=
    Prod.ext (one_mul _) ((neg_mul_neg 1 1).trans (one_mul 1))
  let s : IdeleGroup (𝓞 ℚ) ℚ := ⟨(1, -1), (1, -1), hs, hs⟩
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)
  refine ⟨q s, ?_, ?_⟩
  · intro h
    obtain ⟨r, hr⟩ := (QuotientGroup.eq_one_iff s).mp h
    have hval := (congrArg Units.val hr).trans (show s.val = (1, -1) from rfl)
    have hreal := congrArg (fun x : 𝔸[ℚ] ↦ x.1 Rat.infinitePlace) hval
    change algebraMap ℚ Rat.infinitePlace.Completion r.val = 1 at hreal
    have hr₁ : r.val = 1 := (algebraMap ℚ Rat.infinitePlace.Completion).injective
      (hreal.trans (map_one _).symm)
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
    have hfinite := congrArg (fun x : 𝔸[ℚ] ↦ x.2 v) hval
    change algebraMap ℚ (v.adicCompletion ℚ) r.val = -1 at hfinite
    rw [hr₁, map_one] at hfinite
    have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
      (by simpa only [map_neg, map_one] using hfinite)
    norm_num at this
  · rw [← map_pow, sq]
    exact (congrArg q (Units.ext hs)).trans (map_one q)

open scoped ContDiff in
/-- A nonnegative bump near one has nonzero moment against characters with positive
real part on its support. -/
private theorem criticalTrace_exists_nonzero_moments (χ : U𝔽) :
    ∃ φ : D𝔽, ∀ η : U𝔽, (∀ x, 0 < (χ x : ℂ).re → 0 < (η x : ℂ).re) →
      (∫ x, φ.val x * (η x : ℂ) ∂μ𝔽) ≠ 0 := by
  have hχ : Continuous (fun x ↦ (χ x : ℂ).re) :=
    Complex.continuous_re.comp (continuous_subtype_val.comp χ.continuous)
  obtain ⟨v, hc, hs, hv⟩ := schwartzBruhat_exists_local_unit
    (U := {x | 0 < (χ x : ℂ).re}) (isOpen_lt continuous_const hχ)
    (x := 1) (by simp [map_one])
  let p (z : ℂ) : ℂ := (z.re ^ 2 : ℝ)
  have hp : ContDiff ℝ (∞) p := Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.pow 2)
  have hzero : p 0 = 0 := by simp [p]
  obtain ⟨f, hf⟩ := compact_schwartzBruhat_comp hc hp hzero
  have hfs : tsupport f.val ⊆ tsupport v.val := hf ▸ tsupport_comp_subset hzero _
  have hfc : HasCompactSupport f.val := hc.of_isClosed_subset (isClosed_tsupport _) hfs
  have hf₁ : f.val 1 = 1 := by rw [hf, comp_apply, hv.eq_of_nhds]; norm_num [p]
  refine ⟨⟨f.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth f), hfc⟩, fun η hη ↦ ?_⟩
  let G (x : C𝔽) := f.val x * (η x : ℂ)
  have hG : Continuous G :=
    (continuous_schwartzBruhat f).mul (continuous_subtype_val.comp η.continuous)
  have hGc : HasCompactSupport G := hfc.mul_right
  have hnonneg (x) : 0 ≤ (G x).re := by
    by_cases hx : x ∈ tsupport f.val
    · have he := hη x (hs (hfs hx))
      change 0 ≤ (f.val x * (η x : ℂ)).re
      rw [hf]
      simpa only [p, Function.comp_def, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using mul_nonneg (sq_nonneg (v.val x).re) he.le
    · have hz := image_eq_zero_of_notMem_tsupport hx
      simp [G, hz]
  have hpos := (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (μ := μ𝔽) (hGc.comp_left Complex.zero_re) hnonneg (x := 1) (by simp [G, hf₁])
  intro he
  exact hpos.ne' ((integral_re (hG.integrable_of_hasCompactSupport hGc)).trans
    (congrArg Complex.re he))

/-- Paper: Theorem 13.3.1.1, p. 522. The rational Mellin-jet test subspace has
codimension at least two, as witnessed by the trivial character and the character
modulo four on the norm-one classes.
Deviation: This replaces the printed codimension one over `ℚ` by a lower bound. -/
theorem criticalTraceTestSubmodule_rat_codimension_ge_two
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (_hτ : RightInverse τ (ideleClassNorm ℚ)) :
    2 ≤ Module.rank ℂ (BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) ⧸
      criticalTraceTestSubmodule τ) := by
  let g := criticalTrace_rat_sign.choose
  have hg : g ≠ 1 := criticalTrace_rat_sign.choose_spec.1
  have hg₂ : g ^ 2 = 1 := criticalTrace_rat_sign.choose_spec.2
  have hn : ideleClassNorm ℚ g = 1 := sq_eq_one.mp (by rw [← map_pow, hg₂, map_one])
  let ψ := (exists_pontryaginDual_apply_ne_one hg).choose
  have hψ : ψ g ≠ 1 := (exists_pontryaginDual_apply_ne_one hg).choose_spec
  let n : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  -- Retract onto the norm-one classes so the character is trivial on the section.
  let r : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ContinuousMonoidHom.id _ / τ.comp n
  let χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) := ψ.comp r
  have hr (x) : r x = x / τ (ideleClassNorm ℚ x) := rfl
  have hχτ (t) : χ (τ t) = 1 := by
    change ψ (r (τ t)) = 1
    rw [hr, _hτ t, div_self', map_one]
  have hχg : (χ g : ℂ) = -1 := by
    have he : ψ (r g) = ψ g := by rw [hr, hn, map_one, div_one]
    change (ψ (r g) : ℂ) = -1
    rw [he]
    have hsq : (ψ g : ℂ) ^ 2 = 1 := by
      rw [← Circle.coe_pow, ← map_pow, hg₂, map_one, Circle.coe_one]
    exact (sq_eq_one_iff.mp hsq).resolve_left (fun h ↦ hψ (Subtype.ext h))
  let f := (criticalTrace_exists_nonzero_moments χ).choose
  have hf := (criticalTrace_exists_nonzero_moments χ).choose_spec
  let f' : SchwartzBruhat (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨f.val, bruhatCompactSupport_mem_schwartz f.property⟩
  let v := schwartzBruhatTranslate g f'
  let u : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨v.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth v),
      f.property.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩
  let M (η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) :=
    (criticalTraceMoment_isLinearMap η 0).mk' _
  have hM (η) (w : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ)) :
      M η w = ∫ x, w.val x * (η x : ℂ) ∂ideleClassTamagawaMeasure ℚ := by
    change (∫ x, w.val x * spectralZeroJet η 0 0 0 x ∂ideleClassTamagawaMeasure ℚ) = _
    simp only [spectralZeroJet_zero]
  have hMu (η) : M η u = (η g : ℂ) * M η f := by
    let μ := ideleClassTamagawaMeasure ℚ
    let integrand x := u.val x * (η x : ℂ)
    calc
      M η u = ∫ x, integrand x ∂μ := hM η u
      _ = ∫ x, integrand (g * x) ∂μ :=
        (integral_mul_left_eq_self (μ := μ) integrand g).symm
      _ = ∫ x, (η g : ℂ) * (f.val x * (η x : ℂ)) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change v (g * x) * (η (g * x) : ℂ) = _
          rw [schwartzBruhatTranslate_apply_mul, map_mul, Circle.coe_mul, mul_left_comm]
      _ = (η g : ℂ) * (∫ x, f.val x * (η x : ℂ) ∂μ) := integral_const_mul _ _
      _ = (η g : ℂ) * M η f := congrArg ((η g : ℂ) * ·) (hM η f).symm
  let L := (M 1).prod (M χ)
  have hL : criticalTraceTestSubmodule τ ≤ LinearMap.ker L := by
    intro w hw
    let k : Fin (Module.finrank ℚ ℚ) := ⟨0, by simp⟩
    have hm (η : {η : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) // ∀ t, η (τ t) = 1}) :
        M η.val w = 0 := by
      have hle : criticalTraceTestSubmodule τ ≤ (M η.val).ker :=
        iInf_le_of_le η (iInf_le _ k)
      exact hle hw
    exact LinearMap.mem_ker.mpr (Prod.ext (hm ⟨1, by simp⟩) (hm ⟨χ, hχτ⟩))
  let A := M 1 f
  let B := M χ f
  have hA : A ≠ 0 := by
    rw [show A = M 1 f from rfl, hM]
    exact hf 1 (by simp)
  have hB : B ≠ 0 := by
    rw [show B = M χ f from rfl, hM]
    exact hf χ (fun _ h ↦ h)
  have hLf : L f = (A, B) := rfl
  have hLu : L u = (A, -B) := by
    change (M 1 u, M χ u) = (A, -B)
    refine Prod.ext ((hMu 1).trans ?_) ((hMu χ).trans ?_)
    · change (1 : ℂ) * A = A
      exact one_mul A
    · exact (congrArg (· * B) hχg).trans (neg_one_mul B)
  let Q := (criticalTraceTestSubmodule τ).liftQ L hL
  have hQ : Surjective Q := by
    intro z
    let a := z.1
    let b := z.2
    let c := (a / A + b / B) / 2
    let d := (a / A - b / B) / 2
    refine ⟨(criticalTraceTestSubmodule τ).mkQ (c • f + d • u), ?_⟩
    change L (c • f + d • u) = z
    calc
      L (c • f + d • u) = L (c • f) + L (d • u) := L.map_add _ _
      _ = c • (A, B) + d • (A, -B) :=
        congrArg₂ (· + ·) ((L.map_smul c f).trans (congrArg (c • ·) hLf))
          ((L.map_smul d u).trans (congrArg (d • ·) hLu))
      _ = z := by
        apply Prod.ext
        · change c * A + d * A = a
          dsimp [c, d]
          field_simp [hA, hB]
          ring
        · change c * B + d * (-B) = b
          dsimp [c, d]
          field_simp [hA, hB]
          ring
  calc
    2 = Module.rank ℂ (ℂ × ℂ) := by rw [rank_prod', Module.rank_self]; norm_num
    _ ≤ _ := Q.rank_le_of_surjective hQ

local notation "lineZeros(" τ ")" =>
  {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2) ∧ z.2.re = 1 / 2}
local notation "mellinAt(" φ ", " χ ", " s ")" =>
  (∫ g : C𝔽, (φ : D𝔽).val g * ideleClassNormTwist (F := F) χ s g ∂μ𝔽)
local notation "zeroTerm(" φ ", " z ")" =>
  ((criticalTraceMultiplicity (z).val.1.val (z).val.2 (z).property.1 : ℂ) *
    mellinAt(φ, (z).val.1.val, (z).val.2 - 1 / 2))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3), p. 522. The capped zero sum over the
critical line converges and gives a continuous linear functional on the test subspace.
Deviation: A norm section lists each quasi-character once by a unitary character
trivial on the section and a complex norm exponent. -/
theorem criticalTraceSpectral_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        HasSum (fun z : lineZeros(τ) ↦ zeroTerm(φ.val, z)) (L φ) := by
  classical
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let ι : C₁ →ₜ* C𝔽 := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  let p : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hp (x : C𝔽) : p x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, _hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨p.toMonoidHom.codRestrict _ hp, p.continuous.subtype_mk _⟩
  let χ (ω : PontryaginDual C₁) : U𝔽 := ω.comp r
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω
    ext g : 1
    change ω (r g.val) = ω g
    apply congrArg ω
    apply Subtype.ext
    change g.val / τ (ideleClassNorm F g.val) = g.val
    rw [show ideleClassNorm F g.val = 1 from g.property, map_one, div_one]
  have hnorm (ω) (t : ℝ≥0ˣ) : χ ω (τ t) = 1 := by
    change ω (r (τ t)) = 1
    rw [show r (τ t) = 1 from Subtype.ext (by change τ t / τ (ideleClassNorm F (τ t)) = 1; rw [_hτ, div_self']), map_one]
  let E : PontryaginDual C₁ ≃ sectionCharacters(τ) :=
    { toFun := fun ω ↦ ⟨χ ω, hnorm ω⟩
      invFun := fun η ↦ η.val.comp ι
      left_inv := hχ
      right_inv := fun η ↦ by
        apply Subtype.ext
        ext x : 1
        change η.val (x / τ (ideleClassNorm F x)) = η.val x
        rw [map_div, η.property, div_one] }
  let point (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  have hpoint (w : ℂ) (hw : w.re = 1 / 2) : point w.im = w := by
    apply Complex.ext <;> simp [point, hw]
  have hdiv (η : U𝔽) (w : ℂ) := MeromorphicOn.divisor_apply
    (continuedCompletedHeckeL_spec η).1.meromorphicOn (mem_univ w)
  have ordpos (η : U𝔽) (w : ℂ) :
      0 < ord(η, w) ↔ 0 < meromorphicOrderAt (continuedCompletedHeckeL η) w := by
    obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec η
    have htwo : meromorphicOrderAt (continuedCompletedHeckeL η) 2 ≠ ⊤ := by
      intro h
      have hp' : 0 < meromorphicOrderAt (continuedCompletedHeckeL η) 2 := by
        rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
      have hb := completedHeckeL_continuation_zeros η _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp'
      norm_num at hb
    have ht := hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ _) (mem_univ w) htwo
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [hdiv, ← hk, WithTop.untop₀_coe]
    exact WithTop.coe_lt_coe.symm
  let J := {z : PontryaginDual C₁ × ℝ //
    0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (point z.2)}
  let e : J ≃ lineZeros(τ) :=
    { toFun := fun z ↦ ⟨(E z.val.1, point z.val.2),
          (ordpos _ _).mpr z.property, by simp [point]⟩
      invFun := fun z ↦ ⟨(E.symm z.val.1, z.val.2.im), by
          have h := (ordpos _ _).mp z.property.1
          have he : χ (E.symm z.val.1) = z.val.1.val := congrArg Subtype.val (E.apply_symm_apply z.val.1)
          rwa [he, hpoint _ z.property.2]⟩
      left_inv := fun z ↦ Subtype.ext (Prod.ext (E.symm_apply_apply _) (by simp [point]))
      right_inv := fun z ↦ Subtype.ext (Prod.ext (E.apply_symm_apply _) (hpoint _ z.property.2)) }
  let s : ℝ := 2 * (Module.finrank ℚ F : ℝ) + 1
  have hs : 1 < s := by
    have hd : (0 : ℝ) < Module.finrank ℚ F := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
    dsimp only [s]; linarith
  have hc : ⌈(s - 1) / 2⌉₊ = Module.finrank ℚ F := by simp [s]
  obtain ⟨D, hD⟩ := spectralLineConvolution_trace_distribution (F := F) (1 / 2) hs
  refine ⟨D.comp (criticalTraceTestSubmodule τ).subtypeL, fun φ ↦ ?_⟩
  obtain ⟨T, hT, -⟩ := spectralLineConvolution_traceNorm_continuous (F := F) (1 / 2) hs
  change HasSum _ (D φ.val)
  rw [hD φ.val (T φ.val) (hT φ.val)]
  apply e.hasSum_iff.mp
  apply ((spectralLineConvolution_trace (F := F) (1 / 2) χ hχ hs φ.val (T φ.val) (hT φ.val)).2).congr_fun
  intro z
  simp only [Function.comp_apply, e, Equiv.coe_fn_mk, E, criticalTraceMultiplicity, hdiv,
    spectralBoundaryMultiplicity, hc]
  have hshift : point z.val.2 - 1 / 2 = ((0 : ℝ) : ℂ) + (z.val.2 : ℂ) * Complex.I := by
    push_cast [point]; ring
  rw [hshift, (spectralConvolution_mellin_integrable (F := F) φ.val (χ z.val.1) _).2]
  rfl

local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b)
local notation "finiteUnitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F (v : V)
    (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℂ)
local notation "archTests" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTests" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "restrictsAtInfinity(" a ", " φ ")" =>
  (∀ w u, ((a : archTests) w).val u = (φ : D𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "restrictsAtFinite(" b ", " φ ")" =>
  (∀ v u, ((b : finiteTests) v).val u = (φ : D𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))

/-- Paper: Theorem 13.3.1.1, p. 522. Every test has local components at the
archimedean and at the finite places restricting to it on the images of the local
multiplicative groups; they are the ones supplied by the explicit formula. -/
private theorem criticalTraceGeometric_converges_localData (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) :
    ∃ (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ) ∧ restrictsAtFinite(b, φ) := by
  obtain ⟨_, _, _, _, _, _, harch, hfin, _, _, _, _⟩ := idelicExplicitFormula τ hτ
  choose a ha using fun w ↦ harch w φ
  choose b hb using fun v ↦ hfin v φ
  exact ⟨a, b, fun w u ↦ (ha w).1 u, fun v u ↦ (hb v).1 u⟩

/-- Paper: Definition A.3.2.2(2), p. 560. The mass of the integer units at a
finite place is nonzero. -/
private theorem criticalTraceGeometric_converges_unitMass_ne_zero (v : V) :
    finiteUnitMass(v) ≠ 0 := by
  have h := finiteLocalMultiplicativeTamagawaMeasure_integerUnits (F := F) (v : V)
  rw [h]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  refine inv_ne_zero (Real.sqrt_pos.mpr ?_).ne'
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero h0
  positivity

/-- Paper: Theorem 13.3.1.1, (13.3.1.5), p. 522. For any test and any finite local
data restricting to it, the finite-place series of the printed local principal values
converges. The explicit formula gives a finite set of places outside which the local
principal value vanishes, and the printed scale is the explicit formula's scale times
the mass of the local integer units, which is nonzero. -/
theorem criticalTraceGeometric_converges_summable (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) (b : finiteTests)
    (hb : restrictsAtFinite(b, φ)) :
    Summable (fun v : V ↦ finiteTerm(v, b v)) := by
  obtain ⟨_, _, _, fin, _, _, _, hfin, _, hsupp, _, _⟩ := idelicExplicitFormula τ hτ
  choose b₀ hb₀ using fun v ↦ hfin v φ
  have hbb : b = b₀ := by
    funext v
    exact Subtype.ext (funext fun u ↦ by rw [hb v u, (hb₀ v).1 u])
  rw [hbb]
  refine summable_of_ne_finset_zero (s := (hsupp φ).toFinset) fun v hv ↦ ?_
  have hz : fin v φ = 0 := by
    by_contra h
    exact hv ((hsupp φ).mem_toFinset.mpr h)
  rw [(hb₀ v).2] at hz
  set W : ℝ := (finiteLocalMultiplicativeTamagawaMeasure F (v : V)
    (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal with hW
  have hW0 : (W : ℂ) ≠ 0 := by
    have hm := criticalTraceGeometric_converges_unitMass_ne_zero (F := F) v
    rw [hW]
    exact hm
  have hcast : ((Real.log ((v : V).asIdeal.absNorm : ℝ) : ℝ) : ℂ) =
      (W : ℂ) * (((Real.log ((v : V).asIdeal.absNorm : ℝ) / W : ℝ)) : ℂ) := by
    rw [Complex.ofReal_div]
    field_simp
  rw [hcast, mul_assoc, hz, mul_zero]

/-- Paper: Theorem 13.3.1.1, (13.3.1.4)–(13.3.1.5), p. 522. The polar terms minus
the archimedean and finite local principal values are a continuous linear functional
of the test, with the printed local scalings. -/
theorem criticalTraceGeometric_converges_functional (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : D𝔽 →L[ℂ] ℂ, ∀ (φ : D𝔽) (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ) → restrictsAtFinite(b, φ) →
      L φ = mellinAt(φ, 1, -1 / 2) + mellinAt(φ, 1, 1 / 2) -
        (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) -
        ∑' v : V, finiteTerm(v, b v) := by
  classical
  obtain ⟨_, poles, arch, fin, _, hpoles, harch, hfin, _, _, hsum, _⟩ :=
    idelicExplicitFormula τ hτ
  let vol : ℝ := (normOneIdeleClassTamagawaMeasure F univ).toReal
  have hvol : 0 < vol := by
    dsimp [vol]
    rw [normOneIdeleClassTamagawaMeasure_volume]
    have := NumberField.classNumber_pos F
    have := NumberField.Units.regulator_pos F
    have := NumberField.Units.torsionOrder_pos F
    have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  -- The printed finite-place coefficients change the dual series only at the different.
  let printed (v : V) : StrongDual ℂ D𝔽 := finiteUnitMass(v) • fin v
  have hmass : ∀ᶠ v : V in Filter.cofinite, finiteLocalMultiplicativeTamagawaMeasure F v
      (v.adicCompletionIntegers F).units = 1 := by
    simpa only [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, Filter.eventually_cofinite]
      using finiteLocalTamagawaMass_finite F
  have hprinted : Summable printed := hsum.congr_cofinite (hmass.mono fun v hv ↦ by
    simp [printed, hv])
  refine ⟨(vol : ℂ) • poles - (∑ w, arch w) - (∑' v, printed v), ?_⟩
  intro φ a b ha hb
  let ev : StrongDual ℂ D𝔽 →+ ℂ :=
    { toFun := fun L ↦ L φ, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have hp : (vol : ℂ) * poles φ = mellinAt(φ, 1, -1 / 2) + mellinAt(φ, 1, 1 / 2) := by
    have htwist (s : ℂ) (g : C𝔽) : ideleClassNormTwist (1 : U𝔽) s g =
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^ s := by
      exact one_mul ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ s)
    simp only [htwist, hpoles]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hvol.ne')
  have hinf : ev (∑ w, arch w) = ∑ w, infiniteConnesWeilPrincipalValue w (a w) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    obtain ⟨t, ht, he⟩ := harch w φ
    have ht' : t = a w := Subtype.ext (funext fun u ↦ (ht u).trans (ha w u).symm)
    exact ht' ▸ he
  have hfinite : ev (∑' v, printed v) = ∑' v : V, finiteTerm(v, b v) := by
    have heval : Continuous ev := continuous_eval_const φ
    refine (hprinted.hasSum.map ev heval).tsum_eq.symm.trans (tsum_congr fun v ↦ ?_)
    obtain ⟨t, ht, he⟩ := hfin v φ
    have ht' : t = b v := Subtype.ext (funext fun u ↦ (ht u).trans (hb v u).symm)
    change finiteUnitMass(v) * fin v φ = _
    rw [he, ht', Complex.ofReal_div, ← mul_assoc, mul_div_cancel₀ _
      (criticalTraceGeometric_converges_unitMass_ne_zero (F := F) v)]
  change (vol : ℂ) * poles φ - ev (∑ w, arch w) - ev (∑' v, printed v) = _
  rw [hp, hinf, hfinite]

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The finite-place
series converges, and the polar terms minus the local principal values form a
continuous linear functional on the test subspace. The local tests are pulled back
along the maps from the local multiplicative groups to the idele classes. -/
theorem criticalTraceGeometric_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        ∃ (a : archTests) (b : finiteTests),
          restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
          HasSum (fun v : V ↦ finiteTerm(v, b v))
            (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
              (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ) := by
  obtain ⟨L, hL⟩ := criticalTraceGeometric_converges_functional τ _hτ
  let L' : criticalTraceTestSubmodule τ →L[ℂ] ℂ :=
    L.comp (criticalTraceTestSubmodule τ).subtypeL
  refine ⟨L', fun φ ↦ ?_⟩
  obtain ⟨a, b, ha, hb⟩ := criticalTraceGeometric_converges_localData τ _hτ φ.val
  have hsum := criticalTraceGeometric_converges_summable τ _hτ φ.val b hb
  have hval : L' φ = mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
      (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) -
      ∑' v : V, finiteTerm(v, b v) :=
    hL φ.val a b ha hb
  refine ⟨a, b, ha, hb, ?_⟩
  have h2 : (∑' v : V, finiteTerm(v, b v)) =
      mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
        (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L' φ := by
    rw [hval]
    ring
  exact h2 ▸ hsum.hasSum

private theorem hasSum_fullDivisor_on_criticalTraceTests_vol :
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

private theorem hasSum_fullDivisor_on_criticalTraceTests_cpow (p a x s : ℂ) (hx : x ≠ 0) :
    p * (a * x ^ s) * x ^ (-1 / 2 : ℂ) = p * (a * x ^ (s - 1 / 2)) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hx]
  ring_nf

private theorem hasSum_fullDivisor_on_criticalTraceTests_hasSum_congr {ι : Type*}
    {f g : ι → ℂ} {a : ℂ} (h : HasSum f a) (hfg : ∀ i, f i = g i) : HasSum g a :=
  (funext hfg) ▸ h

private theorem hasSum_fullDivisor_on_criticalTraceTests_mul_div (v m I : ℂ) (hv : v ≠ 0) :
    v * (m / v * I) = m * I := by
  field_simp

private theorem hasSum_fullDivisor_on_criticalTraceTests_val {v x p A Fs P1 P2 M1 M2 A' F' : ℂ}
    (hv : v ≠ 0) (hx : x = p - A - Fs) (hp : p = (P1 + P2) / v) (hA : A = A') (hF : Fs = F')
    (h1 : M1 = P1) (h2 : M2 = P2) :
    v * x = M1 + M2 - v * (A' + F') := by
  subst hx hp hA hF h1 h2
  field_simp
  ring

private theorem hasSum_fullDivisor_on_criticalTraceTests_scale (a b : ℝ) (x : ℂ) :
    ((a / b : ℝ) : ℂ) * x = (a : ℂ) * x / (b : ℂ) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. On the Mellin-jet
test subspace the full zero divisor pairs against the test by the idelic explicit formula.
Deviation: This is the restriction of `idelicExplicitFormula` to the jet subspace.
It sums all completed zeros with full orders and uses the norm-one Tamagawa volume and
the canonical local factors. The capped critical-line equality is refuted in `Sec3_Printed.lean`. -/
theorem hasSum_fullDivisor_on_criticalTraceTests (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : criticalTraceTestSubmodule τ) :
    let zeros := {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2)}
    let classVolume := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
    ∃ (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v) / finiteUnitMass(v)) ∧
      HasSum (fun z : zeros ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
          mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2))
        (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) - classVolume *
          ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v))) := by
  obtain ⟨spectral, poles, arch, finite, hspec, hpoles, harch, hfin, _, hsupp, hsum, hHas⟩ :=
    idelicExplicitFormula τ _hτ
  choose a ha haPV using fun w => harch w φ.val
  choose b hb hbPV using fun v => hfin v φ.val
  let E : StrongDual ℂ D𝔽 →+ ℂ :=
    { toFun := fun L => L φ.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hEc : Continuous E := continuous_eval_const φ.val
  have hT := hsum.hasSum.map E hEc
  have hS := hHas.map E hEc
  have hvol : (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 :=
    hasSum_fullDivisor_on_criticalTraceTests_vol
  have hone (r : ℂ) : mellinAt(φ.val, 1, r) =
      ∫ g, (φ.val : D𝔽).val g * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r ∂μ𝔽 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    change (φ.val : D𝔽).val g * ((1 : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r) =
      (φ.val : D𝔽).val g * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r
    rw [one_mul]
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have hf : Summable (fun v : V => finite v φ.val) := hT.summable
    refine hf.congr fun v => ?_
    rw [hbPV v, hasSum_fullDivisor_on_criticalTraceTests_scale]
  · have hA : E (∑ w : InfinitePlace F, arch w) =
        ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w) :=
      (map_sum E arch Finset.univ).trans (Finset.sum_congr rfl fun w _ => haPV w)
    have hF : E (∑' v : V, finite v) = ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v) :=
      hT.tsum_eq.symm.trans (tsum_congr fun v => by
        rw [show (⇑E ∘ finite) v = (finite v) φ.val from rfl, hbPV v,
          hasSum_fullDivisor_on_criticalTraceTests_scale])
    have hx : E (poles - (∑ w, arch w) - (∑' v, finite v)) =
        E poles - E (∑ w, arch w) - E (∑' v, finite v) :=
      (map_sub E _ _).trans (congrArg (· - E _) (map_sub E _ _))
    have hval : (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
        E (poles - (∑ w, arch w) - (∑' v, finite v)) =
        mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
          (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
            ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
              ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v)) :=
      hasSum_fullDivisor_on_criticalTraceTests_val hvol hx (hpoles φ.val) hA hF
        (hone (-1 / 2)) (hone (1 / 2))
    have hZ := hS.mul_left (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
    rw [hval] at hZ
    refine hasSum_fullDivisor_on_criticalTraceTests_hasSum_congr hZ fun z => ?_
    rw [show (⇑E ∘ spectral) z = (spectral z) φ.val from rfl, hspec z φ.val]
    refine (hasSum_fullDivisor_on_criticalTraceTests_mul_div _ _ _ hvol).trans ?_
    have hI : (∫ g, (φ.val : D𝔽).val g *
        (ideleClassNormTwist (F := F) z.val.1.val z.val.2) g *
          (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-1 / 2 : ℂ) ∂μ𝔽) =
        mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have hn : ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      change (φ.val : D𝔽).val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ z.val.2) *
          ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-1 / 2 : ℂ) =
        (φ.val : D𝔽).val g *
          (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (z.val.2 - 1 / 2))
      exact hasSum_fullDivisor_on_criticalTraceTests_cpow _ _ _ _ hn
    rw [hI]
    rfl

-- TODO(paper-gap): The inference to the divisor statement cites “Theorem ??”
-- without identifying the theorem to be combined with Theorem 13.3.1.1.
-- TODO(paper-gap): Theorem 13.3.1.2 has only a title. Footnotes 2 and 3 ask for
-- the statement, proof, and an approximation by tests tending to e^(−s|log t|)
-- for Re(s) > 1.

end RiemannMasullo
