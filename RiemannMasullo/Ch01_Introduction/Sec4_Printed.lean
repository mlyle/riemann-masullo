module

public import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-! # Printed claims in the introduction's deduction of GRH -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "q(" v ")" => (((v) : HeightOneSpectrum _).asIdeal.absNorm : ℝ)
local notation "N[" F "](" g ")" => (((ideleClassNorm F) (g : C[F])).val : ℝ)
local notation "right(" a ")" => (Complex.re ⁻¹' Ioi (a : ℝ))
local notation "finiteL[" F "](" χ ")" => (finiteHeckeL_exists_continuation (F := F) χ).choose
local notation "approx(" h ", " ρ ", " n ", " z ")" => introTraceApprox (h n) (ρ n) z
local notation "finiteClass[" F "](" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "archClass[" F "](" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "zeroOrder[" F "](" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "windowZeros[" F "](" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder[F](χ, s) ∧ |s.re - 1 / 2| < (a : ℝ)}
local notation "chartBase[" F "](" χ ")" =>
  ((∀ u : (ideleClassNorm F).ker, (χ : U[F]) u.val = 1) → χ = 1)
local notation "literalZeros[" F "](" χ ", " a ")" =>
  {s : ℂ // 0 < zeroOrder[F](χ, s) ∧ |s.re| < (a : ℝ)}
local notation "moment[" F "](" f ", " χ ", " s ")" =>
  (∫ g : C[F], (f : C[F] → ℂ) g * ideleClassNormTwist χ s g ∂ideleClassTamagawaMeasure F)
local notation "printedFamily[" F "](" χ ", " h ", " ρ ", " n ", " z ")" =>
  (fun g : C[F] ↦ (χ g : ℂ) * approx(h, ρ, n, z) (N[F](g)))
local notation "printedArch[" F "](" χ ", " f ", " w ")" =>
  ((if InfinitePlace.IsReal w then (1 / 2 : ℂ) else 1 / (2 * (Real.pi : ℂ))) *
    ∫ u : (w : InfinitePlace F).Completionˣ,
      (χ (archClass[F](w) u) : ℂ) * (f : C[F] → ℂ) (archClass[F](w) u) * (Real.sqrt ‖u.val‖ : ℂ) /
        ((if InfinitePlace.IsReal w then |1 - ‖u.val‖| else ‖1 - u.val‖) : ℝ)
      ∂infiniteLocalMultiplicativeTamagawaMeasure F w)
local notation "printedReal[" F "](" χ ", " h ")" =>
  (∑ w : InfinitePlace F, if w.IsReal then printedArch[F](χ, h, w) else 0)
local notation "printedComplex[" F "](" χ ", " h ")" =>
  (∑ w : InfinitePlace F, if w.IsReal then 0 else printedArch[F](χ, h, w))
local notation "uniformizers[" F "]" => ((v : V[F]) → (v.adicCompletion F)ˣ)
local notation "isUniformizer[" F "](" v ", " π ")" =>
  ((Valued.v : Valuation (HeightOneSpectrum.adicCompletion F v) (WithZero (Multiplicative ℤ)))
    |>.IsUniformizer (π : HeightOneSpectrum.adicCompletion F v))
local notation "printedPrime[" F "](" χ ", " h ", " π ", " p ")" =>
  (let v := (p : V[F] × ℕ).1
   let m := (p : V[F] × ℕ).2 + 1
   let c := (χ (finiteClass[F](v) ((π : uniformizers[F]) v)) : ℂ)
   (Real.log q(v) : ℂ) * (c ^ m * h (q(v) ^ m) + star c ^ m * h ((q(v) ^ m)⁻¹)) /
     (q(v) : ℂ) ^ ((m : ℂ) / 2))

open Classical in
/-- Paper: §1.4, pp. 27–28. The opening trace identity sums zeros with abscissa
strictly between minus and plus the half-width. The Mellin argument is shifted by
one half. The complex denominator is the ordinary modulus in the display. -/
def Printed.introTrace_globalTrace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    ∀ φ : BruhatCompactSupport C[F], (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    ∀ α : ℝ, 0 < α →
      let zeros := {z : {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < zeroOrder[F](z.1.val, z.2) ∧ |z.2.re| < α}
      let finiteTerm := fun (v : HeightOneSpectrum (𝓞 F))
          (b : BruhatCompactSupport (v.adicCompletion F)ˣ) ↦
        let μ := finiteLocalMultiplicativeTamagawaMeasure F v
        let mass := (μ (v.adicCompletionIntegers F).units).toReal
        ((Real.log (v.asIdeal.absNorm : ℝ) / mass : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b
      let archTerm := fun (w : InfinitePlace F) (a : BruhatCompactSupport w.Completionˣ) ↦
        if w.IsReal then infiniteConnesWeilPrincipalValue w a
        else (1 / (2 * (Real.pi : ℂ))) * ∫ u : w.Completionˣ,
          a.val u * (‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
            ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        Summable (fun v ↦ finiteTerm v (b v)) ∧
        HasSum (fun z : zeros ↦ ((zeroOrder[F](z.val.1.val, z.val.2) : ℤ) : ℂ) *
            moment[F](φ.val, z.val.1.val, (z.val.2 - 1 / 2)))
          (moment[F](φ.val, (1 : U[F]), (1 / 2)) + moment[F](φ.val, (1 : U[F]), (-1 / 2)) -
            ((∑ w : InfinitePlace F, archTerm w (a w)) +
              ∑' v, finiteTerm v (b v)))

private theorem introTrace_globalTrace_false_hasSum_zero {X : Type*} (f : X → ℂ) (e : X ≃ X)
    (he : ∀ x, f (e x) = -f x) {S : ℂ} (h : HasSum f S) : S = 0 := by
  have h2 : HasSum (fun x ↦ f (e x)) S := e.hasSum_iff.mpr h
  simp only [he] at h2
  have h3 : -S = S := h.neg.unique h2
  linear_combination -h3 / 2

private theorem introTrace_globalTrace_false_natPow (n : ℕ) (k : ℤ) (hn : 0 < n)
    (h1 : Real.log (9 / 4) < |Real.log ((n : ℝ) ^ k)|)
    (h2 : |Real.log ((n : ℝ) ^ k)| < Real.log (11 / 4)) : False := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : |Real.log ((n : ℝ) ^ k)| = Real.log (((n ^ k.natAbs : ℕ) : ℝ)) := by
    rw [Real.log_zpow, abs_mul, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hn)),
      Nat.cast_pow, Real.log_pow, Nat.cast_natAbs, Int.cast_abs]
  rw [hl] at h1 h2
  have hm : (0 : ℝ) < ((n ^ k.natAbs : ℕ) : ℝ) := by exact_mod_cast pow_pos hn _
  rw [Real.log_lt_log_iff (by norm_num) hm] at h1
  rw [Real.log_lt_log_iff hm (by norm_num)] at h2
  have b1 : (2 : ℝ) < ((n ^ k.natAbs : ℕ) : ℝ) := by linarith
  have b2 : ((n ^ k.natAbs : ℕ) : ℝ) < 3 := by linarith
  have a1 : 2 < n ^ k.natAbs := by exact_mod_cast b1
  have a2 : n ^ k.natAbs < 3 := by exact_mod_cast b2
  omega

private theorem introTrace_globalTrace_false_bump :
    ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h ∧
      (∀ t, h (-t) = -h t) ∧
      (∀ t, h t ≠ 0 → Real.log (9 / 4) < |t| ∧ |t| < Real.log (11 / 4)) ∧
      (∀ t, 0 ≤ h t * t) ∧ ∃ t, h t ≠ 0 := by
  set A := Real.log (9 / 4)
  set B := Real.log (11 / 4)
  have hA : 0 < A := Real.log_pos (by norm_num)
  have hAB : A < B := Real.log_lt_log (by norm_num) (by norm_num)
  let b : ContDiffBump ((A + B) / 2) := ⟨(B - A) / 4, (B - A) / 2, by linarith, by linarith⟩
  have hsupp (t : ℝ) (ht : b t ≠ 0) : A < t ∧ t < B := by
    have : t ∈ Metric.ball ((A + B) / 2) ((B - A) / 2) := by
      rw [← b.support_eq]; exact ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  refine ⟨fun t ↦ b t - b (-t), ?_, ?_, ?_, ?_, ?_, ⟨(A + B) / 2, ?_⟩⟩
  · exact b.contDiff.sub (b.contDiff.comp contDiff_neg)
  · exact b.hasCompactSupport.sub (b.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))
  · intro t; simp only [neg_neg]; ring
  · intro t ht
    dsimp only at ht
    by_cases h1 : b t = 0
    · have h2 : b (-t) ≠ 0 := by intro h2; exact ht (by rw [h1, h2, sub_zero])
      obtain ⟨c1, c2⟩ := hsupp _ h2
      rw [abs_of_neg (by linarith)]
      exact ⟨c1, c2⟩
    · obtain ⟨c1, c2⟩ := hsupp _ h1
      rw [abs_of_pos (by linarith)]
      exact ⟨c1, c2⟩
  · intro t
    dsimp only
    by_cases h1 : b t = 0
    · by_cases h2 : b (-t) = 0
      · simp [h1, h2]
      · obtain ⟨c1, _⟩ := hsupp _ h2
        rw [h1, zero_sub]
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr b.nonneg) (by linarith)
    · obtain ⟨c1, _⟩ := hsupp _ h1
      have h2 : b (-t) = 0 := by
        by_contra h2; obtain ⟨c3, _⟩ := hsupp _ h2; linarith
      rw [h2, sub_zero]
      exact mul_nonneg b.nonneg (by linarith)
  · have h1 : b ((A + B) / 2) = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self
      b.rIn_pos.le)
    have h2 : b (-((A + B) / 2)) = 0 := by
      by_contra h2; obtain ⟨c3, _⟩ := hsupp _ h2; linarith
    simp [h1, h2]

private theorem introTrace_globalTrace_false_localPos {K : Type*} [NormedField K]
    {_ : MeasurableSpace Kˣ} [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsInvInvariant]
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (f : Kˣ → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (hodd : ∀ u, f u⁻¹ = -f u)
    (hsign : ∀ u, 0 ≤ f u * (‖(u : K)‖ - 1)) (ρ : ℝ) (hρ : 1 < ρ)
    (hz : ∀ u : Kˣ, ρ⁻¹ < ‖(u : K)‖ → ‖(u : K)‖ < ρ → f u = 0) (u₀ : Kˣ) (hu₀ : f u₀ ≠ 0) :
    0 < (∫ u, (f u : ℂ) * (‖(u : K)‖ : ℂ) / (‖1 - (u : K)‖ : ℂ) ∂μ).re := by
  have hnc : Continuous (fun u : Kˣ ↦ ‖(u : K)‖) := continuous_norm.comp Units.continuous_val
  let F1 : Kˣ → ℝ := fun u ↦ f u * (‖(u : K)‖ / ‖1 - (u : K)‖)
  let F2 : Kˣ → ℝ := fun u ↦ f u / ‖1 - (u : K)‖
  have hF1 : Continuous F1 := by
    refine continuous_iff_continuousAt.mpr fun u ↦ ?_
    by_cases hu : (u : K) = 1
    · have hopen : IsOpen {x : Kˣ | ρ⁻¹ < ‖(x : K)‖ ∧ ‖(x : K)‖ < ρ} :=
        (isOpen_lt continuous_const hnc).inter (isOpen_lt hnc continuous_const)
      have hev : F1 =ᶠ[nhds u] fun _ ↦ 0 := by
        filter_upwards [hopen.mem_nhds (show u ∈ {x : Kˣ | ρ⁻¹ < ‖(x : K)‖ ∧ ‖(x : K)‖ < ρ} by
          simp only [mem_ofPred_eq, hu, norm_one]; exact ⟨inv_lt_one_of_one_lt₀ hρ, hρ⟩)]
          with x hx
        simp [F1, hz x hx.1 hx.2]
      exact (continuousAt_congr hev).mpr continuousAt_const
    · have hne : ‖1 - (u : K)‖ ≠ 0 := by
        rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h ↦ hu h.symm
      exact hf.continuousAt.mul (hnc.continuousAt.div
        (continuous_norm.comp (continuous_const.sub Units.continuous_val)).continuousAt hne)
  have hF1c : HasCompactSupport F1 := hfc.mul_right
  have hF1i : Integrable F1 μ := hF1.integrable_of_hasCompactSupport hF1c
  have hinv (u : Kˣ) : F1 u⁻¹ = -F2 u := by
    simp only [F1, F2, hodd, Units.val_inv_eq_inv_val, norm_inv]
    have hu0 : ‖(u : K)‖ ≠ 0 := norm_ne_zero_iff.mpr u.ne_zero
    have h1 : 1 - (u : K)⁻¹ = -((1 - (u : K)) / (u : K)) := by
      field_simp; ring
    rw [h1, norm_neg, norm_div]
    by_cases h0 : ‖1 - (u : K)‖ = 0
    · simp [h0]
    · field_simp
  have hF2 : F2 = fun u ↦ -F1 u⁻¹ := by funext u; rw [hinv, neg_neg]
  have hF2i : Integrable F2 μ := by rw [hF2]; exact hF1i.comp_inv.neg
  have hI2 : ∫ u, F2 u ∂μ = -∫ u, F1 u ∂μ := by
    rw [hF2, integral_neg, integral_inv_eq_self (fun u ↦ F1 u) μ]
  let G : Kˣ → ℝ := fun u ↦ F1 u - F2 u
  have hGc : Continuous G := by
    refine hF1.sub ?_
    rw [hF2]; exact (hF1.comp continuous_inv).neg
  have hGe (u : Kˣ) : G u = f u * (‖(u : K)‖ - 1) / ‖1 - (u : K)‖ := by
    simp only [G, F1, F2]; ring
  have hGs : HasCompactSupport G := by
    refine hfc.mono fun u hu h0 ↦ hu ?_
    rw [hGe, h0, zero_mul, zero_div]
  have hGn : 0 ≤ G := fun u ↦ by rw [hGe]; exact div_nonneg (hsign u) (norm_nonneg _)
  have hG0 : G u₀ ≠ 0 := by
    have hn1 : ‖(u₀ : K)‖ ≠ 1 := by
      intro h1
      exact hu₀ (hz u₀ (by rw [h1]; exact inv_lt_one_of_one_lt₀ hρ) (by rw [h1]; exact hρ))
    have hne : ‖1 - (u₀ : K)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h; apply hn1; rw [← h, norm_one]
    rw [hGe]
    exact div_ne_zero (mul_ne_zero hu₀ (sub_ne_zero.mpr hn1)) hne
  have hpos := hGc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) hGs hGn hG0
  have hGI : ∫ u, G u ∂μ = 2 * ∫ u, F1 u ∂μ := by
    simp only [G]
    rw [integral_sub hF1i hF2i, hI2]; ring
  have hC : (fun u ↦ (f u : ℂ) * (‖(u : K)‖ : ℂ) / (‖1 - (u : K)‖ : ℂ)) =
      fun u ↦ ((F1 u : ℝ) : ℂ) := by
    funext u; simp only [F1]; push_cast; ring
  rw [hC, integral_complex_ofReal, Complex.ofReal_re]
  linarith


private theorem introTrace_globalTrace_false_unitsPos (u : ℝ≥0ˣ) : (0 : ℝ) < ((u : ℝ≥0) : ℝ) :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr u.ne_zero)

private theorem introTrace_globalTrace_false_field :
    ∀ w : InfinitePlace (CyclotomicField 4 ℚ), w.IsComplex := by
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    convert! CyclotomicField.isCyclotomicExtension 4 ℚ using 1
  exact (IsCyclotomicExtension.Rat.isTotallyComplex (CyclotomicField 4 ℚ) (n := 4)
    (by decide)).isComplex

/-- For a test odd under inversion, inverting the quasi-character negates the Mellin value. -/
private theorem introTrace_globalTrace_false_mellin_inv (F : Type) [Field F] [NumberField F]
    (φ : BruhatCompactSupport C[F]) (hφ : ∀ g, φ.val g⁻¹ = -φ.val g)
    (χ χ' : PontryaginDual C[F]) (r r' : ℂ)
    (hc : ∀ g, ideleClassNormTwist χ' r' g = ideleClassNormTwist χ r g⁻¹) :
    moment[F](φ.val, χ', r') = -moment[F](φ.val, χ, r) := by
  rw [← integral_inv_eq_self _ (ideleClassTamagawaMeasure F), ← integral_neg]
  congr 1
  funext g
  rw [hφ, hc, inv_inv]
  ring

private theorem introTrace_globalTrace_false_twist_inv (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (r : ℂ) (g : C[F]) :
    ideleClassNormTwist χ⁻¹ (-r) g = ideleClassNormTwist χ r g⁻¹ := by
  change (((χ⁻¹ g : Circle)) : ℂ) * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-r) =
    ((χ g⁻¹ : Circle) : ℂ) * ((((ideleClassNorm F g⁻¹ : ℝ≥0) : ℝ)) : ℂ) ^ r
  have hx := introTrace_globalTrace_false_unitsPos (ideleClassNorm F g)
  have harg : (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  rw [map_inv χ g, map_inv (ideleClassNorm F) g, Units.val_inv_eq_inv_val, NNReal.coe_inv,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  congr 1

private theorem introTrace_globalTrace_false_ord (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (s : ℂ) : zeroOrder[F](χ⁻¹, 1 - s) = zeroOrder[F](χ, s) := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hDh⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hεne, hfun⟩ :=
    completedHeckeL_continuation_functionalEquation χ _ _ hL hLh hD hDh
  have hcomp : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) s =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - s) := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) s := by fun_prop
    have hd : deriv (fun s : ℂ ↦ 1 - s) s ≠ 0 := by simp
    simpa [Function.comp_def] using
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL χ⁻¹) ha hd
  have hεord : meromorphicOrderAt ε s = 0 :=
    ((hε.analyticAt s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff).mpr (hεne s)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) = ε * continuedCompletedHeckeL χ from
      funext hfun, meromorphicOrderAt_mul (hε.analyticAt s).meromorphicAt
      (hL (mem_univ _)).meromorphicAt, hεord, zero_add] at hcomp
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← hcomp]

private theorem introTrace_globalTrace_false_zeroSum {X : Type*} (ι : X → X) (hι : ∀ x, ι (ι x) = x)
    (Z : Set X) (hZ : ∀ x ∈ Z, ι x ∈ Z) (G : X → ℂ) (hG : ∀ x ∈ Z, G (ι x) = -G x) {S : ℂ}
    (h : HasSum (fun z : Z ↦ G z) S) : S = 0 := by
  let e : Z ≃ Z :=
    { toFun := fun z ↦ ⟨ι z, hZ z z.2⟩
      invFun := fun z ↦ ⟨ι z, hZ z z.2⟩
      left_inv := fun z ↦ Subtype.ext (hι z)
      right_inv := fun z ↦ Subtype.ext (hι z) }
  exact introTrace_globalTrace_false_hasSum_zero _ e (fun z ↦ hG z z.2) h

private theorem introTrace_globalTrace_false_final {Mp Mm A Fs : ℂ} (h : Mp + Mm - (A + Fs) = 0)
    (h1 : Mm = -Mp) (h2 : Fs = 0) : A = 0 := by
  subst h2; rw [h1] at h; linear_combination -h

private theorem introTrace_globalTrace_false_sign (h : ℝ → ℝ) (hsign : ∀ t, 0 ≤ h t * t) {x : ℝ}
    (hx : 0 < x) : 0 ≤ h (Real.log (x ^ 2)) * (x - 1) := by
  have hs := hsign (Real.log (x ^ 2))
  rcases lt_trichotomy x 1 with h1 | h1 | h1
  · have hl : Real.log (x ^ 2) < 0 := Real.log_neg (by positivity) (by nlinarith)
    have : h (Real.log (x ^ 2)) ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    nlinarith
  · rw [h1, sub_self, mul_zero]
  · have hl : 0 < Real.log (x ^ 2) := Real.log_pos (by nlinarith)
    have : 0 ≤ h (Real.log (x ^ 2)) := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    nlinarith

private theorem introTrace_globalTrace_false_nearOne (h : ℝ → ℝ)
    (hsupp : ∀ t, h t ≠ 0 → Real.log (9 / 4) < |t| ∧ |t| < Real.log (11 / 4)) {x : ℝ}
    (h1 : (3 / 2 : ℝ)⁻¹ < x) (h2 : x < 3 / 2) : h (Real.log (x ^ 2)) = 0 := by
  by_contra hne
  have hA := (hsupp _ hne).1
  have hx : 0 < x := lt_trans (by norm_num) h1
  have hlt : Real.log (x ^ 2) < Real.log (9 / 4) :=
    Real.log_lt_log (by positivity) (by nlinarith)
  have hgt : -Real.log (9 / 4) < Real.log (x ^ 2) := by
    rw [← Real.log_inv]
    exact Real.log_lt_log (by norm_num) (by norm_num at h1 ⊢; nlinarith)
  have := abs_lt.mpr ⟨hgt, hlt⟩
  linarith

private theorem introTrace_globalTrace_false_adicNorm (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    ∃ k : ℤ, ‖(u : v.adicCompletion F)‖ = ((v.asIdeal.absNorm : ℕ) : ℝ) ^ k := by
  refine ⟨WithZero.log (Valued.v (u : v.adicCompletion F)), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (Valued.v.ne_zero_iff.mpr u.ne_zero)]
  simp

private theorem introTrace_globalTrace_false_sum_ne {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hs : s.Nonempty) (hpos : ∀ i ∈ s, 0 < (f i).re) : ∑ i ∈ s, f i ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at hre
  exact (Finset.sum_pos hpos hs).ne' hre

private theorem introTrace_globalTrace_false_dual_zero {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (L : StrongDual ℂ (BruhatCompactSupport G)) (x : BruhatCompactSupport G)
    (hx : ∀ u, x.val u = 0) : L x = 0 := by
  have : x = 0 := Subtype.ext (funext hx)
  rw [this, map_zero]


private theorem introTrace_globalTrace_false_noRight (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (s : ℂ) (hs : 1 < s.re) : zeroOrder[F](χ, s) = 0 := by
  obtain ⟨hL, hLh⟩ := continuedCompletedHeckeL_spec χ
  have hne : continuedCompletedHeckeL χ s ≠ 0 := by
    have h1 := hLh ⟨s, hs⟩
    change continuedCompletedHeckeL χ s = heckeGammaFactor χ s * finiteHeckeL χ ⟨s, hs⟩ at h1
    rw [h1]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs))
      (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s, hs⟩)
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _),
    ((hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff).mpr hne]
  rfl

private theorem introTrace_globalTrace_false_re_nonneg (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C[F]) (s : ℂ) (hs : 0 < zeroOrder[F](χ, s)) : 0 ≤ s.re := by
  by_contra h
  rw [← introTrace_globalTrace_false_ord F χ s, introTrace_globalTrace_false_noRight F χ⁻¹ (1 - s)
    (by rw [Complex.sub_re, Complex.one_re]; linarith)] at hs
  exact lt_irrefl 0 hs

private theorem introTrace_globalTrace_false_of_complex (F : Type) [Field F] [NumberField F]
    (hcx : ∀ w : InfinitePlace F, w.IsComplex) (hP : Printed.introTrace_globalTrace) : False := by
  obtain ⟨h, hh, hhc, hodd, hsupp, hsign, t₁, ht₁⟩ := introTrace_globalTrace_false_bump
  have h0 : h 0 = 0 := by have := hodd 0; rw [neg_zero] at this; linarith
  obtain ⟨φ, hφ⟩ := exists_normTest (F := F) (fun t ↦ (h t : ℂ))
    (Complex.ofRealCLM.contDiff.comp hh) (hhc.comp_left Complex.ofReal_zero)
  have hφinv (g : C[F]) : φ.val g⁻¹ = -φ.val g := by
    rw [hφ, hφ, map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, hodd,
      Complex.ofReal_neg]
  have hφ1 : ∀ g : (ideleClassNorm F).ker, φ.val g = 0 := fun g ↦ by
    rw [hφ, MonoidHom.mem_ker.mp g.2]; simp [h0]
  let τ : ℝ≥0ˣ →ₜ* C[F] :=
    ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection F),
      continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous _)⟩
  obtain ⟨a, b, ha, hb, _, hS⟩ :=
    hP F τ (canonicalIdeleNormSection_rightInverse _) φ hφ1 2 two_pos
  have hpos (v : HeightOneSpectrum (𝓞 F)) : 0 < v.asIdeal.absNorm :=
    zero_lt_one.trans (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  refine absurd (introTrace_globalTrace_false_final (introTrace_globalTrace_false_zeroSum
    (X := {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ)
    (fun p ↦ (⟨p.1.val⁻¹, fun t ↦ by
      change (p.1.val (τ t))⁻¹ = 1
      rw [p.1.2 t, inv_one]⟩, 1 - p.2))
    (fun p ↦ Prod.ext (Subtype.ext (inv_inv _)) (sub_sub_cancel 1 p.2))
    {p | 0 < zeroOrder[F](p.1.val, p.2) ∧ |p.2.re| < 2} ?_
    (fun p ↦ ((zeroOrder[F](p.1.val, p.2) : ℤ) : ℂ) *
      moment[F](φ.val, p.1.val, (p.2 - 1 / 2))) ?_ hS) ?_ ?_) ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hp
    have h0 := introTrace_globalTrace_false_re_nonneg F p.1.val p.2 h1
    refine ⟨?_, ?_⟩
    · change 0 < zeroOrder[F](p.1.val⁻¹, 1 - p.2)
      rw [introTrace_globalTrace_false_ord]
      exact h1
    · change |(1 - p.2).re| < 2
      rw [Complex.sub_re, Complex.one_re, abs_lt]
      have := (abs_lt.mp h2).2
      constructor <;> linarith
  · intro p _
    dsimp only
    rw [introTrace_globalTrace_false_ord, introTrace_globalTrace_false_mellin_inv _ φ hφinv
      p.1.val p.1.val⁻¹ (p.2 - 1 / 2) (1 - p.2 - 1 / 2) (fun g ↦ by
        rw [show (1 - p.2 - 1 / 2 : ℂ) = -(p.2 - 1 / 2) by ring]
        exact introTrace_globalTrace_false_twist_inv _ _ _ g)]
    ring
  · exact introTrace_globalTrace_false_mellin_inv _ φ hφinv 1 1 (1 / 2) (-1 / 2) (fun g ↦ by
      have := introTrace_globalTrace_false_twist_inv _ (1 : PontryaginDual C[F])
        (1 / 2) g
      rw [inv_one] at this
      rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
      exact this)
  · refine (tsum_congr fun v ↦ ?_).trans tsum_zero
    refine mul_eq_zero_of_right _ (introTrace_globalTrace_false_dual_zero _ (b v) fun u ↦ ?_)
    rw [hb v u, hφ, ideleClassNorm_ofAdicCompletion]
    obtain ⟨k, hk⟩ := introTrace_globalTrace_false_adicNorm _ v u
    change ((h (Real.log ‖(u : v.adicCompletion F)‖) : ℝ) : ℂ) = 0
    rw [hk, Complex.ofReal_eq_zero]
    by_contra hne
    exact introTrace_globalTrace_false_natPow _ k (hpos v) (hsupp _ hne).1 (hsupp _ hne).2
  · refine introTrace_globalTrace_false_sum_ne _ _ Finset.univ_nonempty (fun w _ ↦ ?_)
    beta_reduce
    have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr (hcx w)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hnr), show (1 / (2 * (Real.pi : ℂ))) =
      (((1 / (2 * Real.pi)) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    refine mul_pos (by positivity) ?_
    let : MeasurableSpace w.Completion := borel _
    let : BorelSpace w.Completion := ⟨rfl⟩
    let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
      infiniteLocalMultiplicativeTamagawaMeasure_haar _ w
    let : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    have : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsInvInvariant := inferInstance
    have hN (u : w.Completionˣ) : ((ideleClassNorm _
        (IdeleClassGroup.ofCompletion (𝓞 F) _ w u) : ℝ≥0) : ℝ) =
        ‖(u : w.Completion)‖ ^ 2 := by
      rw [ideleClassNorm_ofCompletion, (hcx w).mult_eq_two]
      simp
    have hval (u : w.Completionˣ) :
        (a w).val u = ((h (Real.log (‖(u : w.Completion)‖ ^ 2)) : ℝ) : ℂ) := by
      rw [ha, hφ, hN]
    simp_rw [hval]
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex (hcx w)
    have hen (x : w.Completion) : ‖e x‖ = ‖x‖ := e.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (hcx w))) x
    have hx0 : ‖e.symm (Real.exp (t₁ / 2) : ℂ)‖ = Real.exp (t₁ / 2) := by
      rw [← hen, e.apply_symm_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hx0' : e.symm (Real.exp (t₁ / 2) : ℂ) ≠ 0 := by
      rw [← norm_ne_zero_iff, hx0]; exact (Real.exp_pos _).ne'
    refine introTrace_globalTrace_false_localPos _
      (fun u : w.Completionˣ ↦ h (Real.log (‖(u : w.Completion)‖ ^ 2)))
      (hh.continuous.comp (((continuous_norm.comp Units.continuous_val).pow 2).log
        fun u ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero))) ?_ (fun u ↦ ?_)
      (fun u ↦ introTrace_globalTrace_false_sign h hsign (norm_pos_iff.mpr u.ne_zero)) (3 / 2)
      (by norm_num) (fun u h1 h2 ↦ introTrace_globalTrace_false_nearOne h hsupp h1 h2)
      (Units.mk0 _ hx0') ?_
    · refine (a w).2.2.mono fun u hu h0 ↦ hu ?_
      have := hval u
      rw [h0, eq_comm, Complex.ofReal_eq_zero] at this
      exact this
    · simp only [Units.val_inv_eq_inv_val, norm_inv, inv_pow, Real.log_inv, hodd]
    · rw [Units.val_mk0, hx0, ← Real.exp_nat_mul, Real.log_exp]
      convert ht₁ using 2
      push_cast; ring


/-- Paper: §1.4, p. 28. Over ℚ(i) take half-width two and
φ(g) = h(|g|) − h(1/|g|) with a nonzero nonnegative smooth bump in (9/4,11/4).
This width contains the full trivial-character divisor, which pairs to zero by
the functional equation and inversion. The poles cancel and the finite shells
miss the support. After inversion the complex term integrates a positive
multiple of h(r²)(r−1)/‖1−u‖ on the outer annulus, where r = ‖u‖. -/
theorem Printed.introTrace_globalTrace_false : ¬ Printed.introTrace_globalTrace :=
  introTrace_globalTrace_false_of_complex (CyclotomicField 4 ℚ) introTrace_globalTrace_false_field

open Classical in
/-- Paper: §1.4.1, p. 28. The local archimedean integrands multiply the restricted
test by the local character. For the bare positive arguments of φ in the finite
sum we use its values on the canonical norm section. Section 1.1.4 fixes the
base point of the pure-norm component. Both polar terms are the
Mellin integrals of φ. The zero index uses the strip printed on this page. -/
def Printed.introTrace_characterTrace : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F])
    (φ : BruhatCompactSupport C[F]) (h : ℝ → ℂ), chartBase[F](χ) →
    (∀ u : (ideleClassNorm F).ker, φ.val u.val = 0) →
    (∀ (g : C[F]) (u : (ideleClassNorm F).ker),
      φ.val (g * u.val) = star (χ u.val : ℂ) * φ.val g) →
    (∀ t : ℝ≥0ˣ, h (t.val : ℝ) = φ.val (QuotientGroup.mk (canonicalIdeleNormSection F t))) →
    ∀ a : ℝ, 0 < a → ∀ π : uniformizers[F], (∀ v, isUniformizer[F](v, π v)) →
      Summable (fun p : V[F] × ℕ ↦ printedPrime[F](χ, h, π, p)) ∧
      HasSum (fun ρ : literalZeros[F](χ, a) ↦ (zeroOrder[F](χ, ρ.val) : ℂ) *
        moment[F](φ.val, χ, (ρ.val - 1 / 2)))
        (moment[F](φ.val, (1 : U[F]), (1 / 2)) + moment[F](φ.val, (1 : U[F]), (-1 / 2)) -
          printedReal[F](χ, φ.val) - printedComplex[F](χ, φ.val) -
          ∑' p : V[F] × ℕ, printedPrime[F](χ, h, π, p))

private theorem introTrace_characterTrace_false_ne_one (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (v.adicCompletion ℚ)ˣ) (hu : u ≠ 1) :
    IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := (QuotientGroup.eq_one_iff _).mp h
  have h1 : (((a : ℚ) : ℝ)) = 1 := by
    rw [← NumberFieldKB.Chebotarev.RatIdele.realPart_diag,
      ← NumberFieldKB.Chebotarev.RatIdele.realPart_ofAdicCompletion v u]
    exact congrArg NumberFieldKB.Chebotarev.RatIdele.realPart ha
  have ha1 : a = 1 := Units.val_eq_one.mp (by exact_mod_cast h1)
  rw [ha1, map_one] at ha
  have h2 := congrArg (NumberFieldKB.Chebotarev.RatIdele.compV v) ha
  rw [NumberFieldKB.Chebotarev.RatIdele.compV_ofAdicCompletion_self, map_one] at h2
  exact hu h2.symm

private theorem introTrace_characterTrace_false_bump :
    ∃ H : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H ∧ HasCompactSupport H ∧ H (Real.log 2) ≠ 0 ∧
      ∀ t, H t ≠ 0 → |t - Real.log 2| < Real.log 2 / 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  let b : ContDiffBump (Real.log 2) := ⟨Real.log 2 / 4, Real.log 2 / 2, by positivity, by linarith⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_, fun t ht ↦ ?_⟩
  · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_ne_zero
  · have : t ∈ Metric.ball (Real.log 2) (Real.log 2 / 2) := by
      rw [← b.support_eq]; exact ht
    rwa [Metric.mem_ball, Real.dist_eq] at this

private theorem introTrace_characterTrace_false_cancel {X : Type*} {f : X → ℂ} {A T T' : ℂ}
    (h1 : HasSum f (A - T)) (h2 : HasSum f (A - T')) : T = T' := by
  have := h1.unique h2
  linear_combination -this

private theorem introTrace_characterTrace_false_diff (L c c' y z Q : ℂ) (m : ℕ) (hm : m = 1)
    (hL : L ≠ 0) (hcc : c ≠ c') (hy : y ≠ 0) (hz : z = 0) (hQ : Q ≠ 0) :
    L * (c ^ m * y + star c ^ m * z) / Q - L * (c' ^ m * y + star c' ^ m * z) / Q ≠ 0 := by
  subst hm hz
  rw [show L * (c ^ 1 * y + star c ^ 1 * 0) / Q - L * (c' ^ 1 * y + star c' ^ 1 * 0) / Q =
    L * y * (c - c') / Q by ring]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hL hy) (sub_ne_zero.mpr hcc)) hQ

private theorem introTrace_characterTrace_false_zero (L c y z Q : ℂ) (m : ℕ) (hy : y = 0) (hz : z = 0) :
    L * (c ^ m * y + star c ^ m * z) / Q = 0 := by
  rw [hy, hz]; ring

/-- Paper: §1.4.1, p. 28. Take the primitive quadratic character modulo
three over the rationals and a smooth radial bump equal to one at three
with support in `(5/2, 7/2)`. The only surviving prime power is three.
Its printed term changes sign when the uniformizer at three is changed
from three to minus three. Every other term is independent of this choice. -/
theorem Printed.introTrace_characterTrace_false : ¬ Printed.introTrace_characterTrace := by
  intro hall
  classical
  let v : HeightOneSpectrum (𝓞 ℚ) := NumberFieldKB.Chebotarev.RatIdele.placeOf 2 Nat.prime_two
  have hq : q(v) = 2 := by
    change ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) = 2
    rw [NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal, NumberFieldKB.Chebotarev.RatIdele.pr_placeOf]
    norm_num
  let w : (v.adicCompletion ℚ)ˣ := -1
  have hw1 : w ≠ 1 := by
    intro h
    have h2 : (2 : v.adicCompletion ℚ) ≠ 0 := by
      have := (algebraMap ℚ (v.adicCompletion ℚ)).injective.ne (two_ne_zero (α := ℚ))
      rwa [map_ofNat, map_zero] at this
    apply h2
    have := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at this
    linear_combination -this
  obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one
    (introTrace_characterTrace_false_ne_one v w hw1)
  have hwker : IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v w ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    ext
    simp [w]
  have hbase : chartBase[ℚ](χ) := fun h ↦ absurd (h ⟨_, hwker⟩) hχ
  obtain ⟨H, hH, hHc, hH2, hHs⟩ := introTrace_characterTrace_false_bump
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hHz (t : ℝ) (ht : Real.log 2 / 2 ≤ |t - Real.log 2|) : H t = 0 := by
    by_contra hne
    exact absurd (hHs t hne) (not_lt.mpr ht)
  have hH0 : H 0 = 0 := hHz 0 (by rw [zero_sub, abs_neg, abs_of_pos hl2]; linarith)
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := ℚ) χ⁻¹ (fun t ↦ (H t : ℂ))
    (Complex.ofRealCLM.contDiff.comp hH) (hHc.comp_left Complex.ofReal_zero)
  have hker : ∀ u : (ideleClassNorm ℚ).ker, φ.val u.val = 0 := by
    intro u
    rw [hφ, MonoidHom.mem_ker.mp u.2]
    simp [hH0]
  have hequiv : ∀ (g : C[ℚ]) (u : (ideleClassNorm ℚ).ker),
      φ.val (g * u.val) = star (χ u.val : ℂ) * φ.val g := by
    intro g u
    have hinv : ((χ⁻¹ u.val : Circle) : ℂ) = star (χ u.val : ℂ) :=
      Circle.coe_inv_eq_conj (χ u.val)
    rw [hφ, hφ, map_mul, map_mul (ideleClassNorm ℚ), MonoidHom.mem_ker.mp u.2, mul_one,
      Circle.coe_mul, hinv]
    ring
  let sec : ℝ≥0ˣ → C[ℚ] := fun t ↦ QuotientGroup.mk (canonicalIdeleNormSection ℚ t)
  have hsecN (t : ℝ≥0ˣ) : ideleClassNorm ℚ (sec t) = t :=
    canonicalIdeleNormSection_rightInverse ℚ t
  let tx : {x : ℝ // 0 < x} → ℝ≥0ˣ := fun x ↦
    Units.mk0 (Real.toNNReal x.val) (Real.toNNReal_pos.mpr x.2).ne'
  let h : ℝ → ℂ := fun x ↦ if hx : 0 < x then φ.val (sec (tx ⟨x, hx⟩)) else 0
  have hsec : ∀ t : ℝ≥0ˣ, h (t.val : ℝ) = φ.val (QuotientGroup.mk (canonicalIdeleNormSection ℚ t)) := by
    intro t
    have ht : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t.ne_zero)
    have htx : tx ⟨_, ht⟩ = t := Units.ext (by simp [tx])
    simp only [h, ht, ↓reduceDIte, htx]
    rfl
  have hform (x : ℝ) (hx : 0 < x) :
      h x = ((χ⁻¹ (sec (tx ⟨x, hx⟩)) : Circle) : ℂ) * (H (Real.log x) : ℂ) := by
    simp only [h, hx, ↓reduceDIte]
    rw [hφ, hsecN]
    simp [tx, Real.toNNReal_of_nonneg hx.le]
  have hzero (x : ℝ) (hx : H (Real.log x) = 0) : h x = 0 := by
    by_cases hx0 : 0 < x
    · rw [hform x hx0, hx, Complex.ofReal_zero, mul_zero]
    · simp only [h, hx0, ↓reduceDIte]
  have hh2 : h 2 ≠ 0 := by
    rw [hform 2 two_pos]
    exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.mpr hH2)
  have hpow (k : ℕ) : h (2 ^ (k + 1 + 1)) = 0 := by
    refine hzero _ (hHz _ ?_)
    rw [Real.log_pow]
    push_cast
    rw [show ((k : ℝ) + 1 + 1) * Real.log 2 - Real.log 2 = (k + 1) * Real.log 2 by ring,
      abs_of_nonneg (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpowinv (k : ℕ) : h ((2 ^ (k + 1))⁻¹) = 0 := by
    refine hzero _ (hHz _ ?_)
    rw [Real.log_inv, Real.log_pow]
    push_cast
    rw [show -(((k : ℝ) + 1) * Real.log 2) - Real.log 2 = -((k + 2) * Real.log 2) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  let val (v' : HeightOneSpectrum (𝓞 ℚ)) :
      Valuation (v'.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  let π₀ : uniformizers[ℚ] := fun v' ↦
    Units.mk0 ((val v').exists_isUniformizer_of_isCyclic_of_nontrivial.choose :
      v'.adicCompletion ℚ) (val v').exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero
  have hπ₀ : ∀ v', isUniformizer[ℚ](v', π₀ v') := fun v' ↦
    (val v').exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
  obtain ⟨π', hπ'v, hπ'ne⟩ : ∃ π' : uniformizers[ℚ], π' v = π₀ v * w ∧ ∀ v', v' ≠ v → π' v' = π₀ v' :=
    ⟨Function.update π₀ v (π₀ v * w), Function.update_self _ _ _,
      fun v' hv' ↦ Function.update_of_ne hv' _ _⟩
  have hπ' : ∀ v', isUniformizer[ℚ](v', π' v') := by
    intro v'
    by_cases hv' : v' = v
    · subst hv'
      rw [hπ'v]
      have := hπ₀ v
      unfold Valuation.IsUniformizer at this ⊢
      rw [Units.val_mul, map_mul, this]
      simp [w]
    · rw [hπ'ne v' hv']
      exact hπ₀ v'
  have hT := introTrace_characterTrace_false_cancel
    (hall ℚ χ φ h hbase hker hequiv hsec 1 one_pos π₀ hπ₀).2
    (hall ℚ χ φ h hbase hker hequiv hsec 1 one_pos π' hπ').2
  have hS := (hall ℚ χ φ h hbase hker hequiv hsec 1 one_pos π₀ hπ₀).1
  have hS' := (hall ℚ χ φ h hbase hker hequiv hsec 1 one_pos π' hπ').1
  have hD := hS.hasSum.sub hS'.hasSum
  rw [hT, sub_self] at hD
  have hsingle : ∀ p : HeightOneSpectrum (𝓞 ℚ) × ℕ, p ≠ (v, 0) →
      printedPrime[ℚ](χ, h, π₀, p) - printedPrime[ℚ](χ, h, π', p) = 0 := by
    rintro ⟨v', k⟩ hp
    by_cases hv' : v' = v
    · subst hv'
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 :=
        Nat.exists_eq_succ_of_ne_zero (fun hk ↦ hp (by rw [hk]))
      dsimp only
      rw [hq, hpow k, hpowinv (k + 1)]
      ring
    · dsimp only
      rw [hπ'ne v' hv', sub_self]
  have hD' := hasSum_single (f := fun p ↦ printedPrime[ℚ](χ, h, π₀, p) - printedPrime[ℚ](χ, h, π', p))
    (v, 0) hsingle
  have hd := hD.unique hD'
  revert hd
  dsimp only
  refine (introTrace_characterTrace_false_diff _ _ _ _ _ _ _ rfl ?_ ?_ ?_ ?_ ?_).symm
  · rw [hq]; exact Complex.ofReal_ne_zero.mpr hl2.ne'
  · rw [hπ'v, map_mul, map_mul, Circle.coe_mul]
    intro hc
    apply hχ
    apply Circle.coe_injective
    rw [Circle.coe_one]
    exact (mul_eq_left₀ (Circle.coe_ne_zero _)).mp hc.symm
  · rw [hq]; simpa using hh2
  · rw [hq]; simpa using hpowinv 0
  · rw [hq]
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (by norm_num)


/-- Paper: §§1.4.2–1.4.3, pp. 28–29. The displayed products can be chosen as a cofinal
family of approximants with conjugate norm-one weight. -/
def Printed.introTraceApprox_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]), chartBase[F](χ) →
    ∃ h ρ : ℕ → ℝ → ℝ, IsIntroTraceApproximation h ρ ∧
    ∀ (n : ℕ) (z : ℂ) (g : C[F]) (u : (ideleClassNorm F).ker),
      (χ (g * u.val) : ℂ) * approx(h, ρ, n, z) (N[F](g * u.val)) =
        star (χ u.val : ℂ) * ((χ g : ℂ) * approx(h, ρ, n, z) (N[F](g)))

private theorem printedTrace_localResidue_continuous (p : ℕ) [Fact p.Prime] :
    Continuous (PadicInt.toZMod : ℤ_[p] →+* ZMod p) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
  refine (tendsto_pure.mpr ?_).mono_right (pure_le_nhds _)
  filter_upwards [Metric.ball_mem_nhds (0 : ℤ_[p]) one_pos] with x hx
  rw [map_zero, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]
  simpa using hx

private theorem printedTrace_local_five_character :
    ∃ (v : HeightOneSpectrum (𝓞 ℚ)) (c : (v.adicCompletionIntegers ℚ)ˣ →ₜ* Circle)
      (a : (v.adicCompletionIntegers ℚ)ˣ), c a ^ 2 ≠ 1 := by
  classical
  let p : Nat.Primes := ⟨5, by decide⟩
  let : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  let v : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  let E := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p
  let φ : v.adicCompletionIntegers ℚ →+* ZMod 5 :=
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp E.symm.toRingEquiv.toRingHom
  have hφ : Continuous φ := (printedTrace_localResidue_continuous p).comp E.symm.continuous
  let r : (ZMod 5)ˣ := Units.mk0 2 (by decide)
  have hr : (Additive.ofMul (r ^ 2)) ≠ 0  := by
    intro he
    have hh := congrArg (fun u : (ZMod 5)ˣ ↦ (u : ZMod 5)) (show r^2 = 1 from he)
    exact (by decide : (2 : ZMod 5)^2 ≠ 1) hh
  obtain ⟨ψ₀, hψ₀⟩ := AddChar.exists_apply_ne_zero.mpr hr
  let ψ : (ZMod 5)ˣ →* Circle := (AddChar.circleEquivComplex.symm ψ₀).toMonoidHom
  have hψ : ψ (r ^ 2) ≠ 1 := fun h ↦ hψ₀ (congrArg (fun z : Circle ↦ (z : ℂ)) h)
  have hunit : IsUnit (2 : ℤ_[p]) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker]
    change PadicInt.toZMod (2 : ℤ_[5]) ≠ 0
    rw [show PadicInt.toZMod (2 : ℤ_[5]) = (2 : ZMod 5) from map_ofNat _ _]
    decide
  let a := Units.map E.toRingEquiv.toMonoidHom hunit.unit
  have ha : Units.map φ.toMonoidHom a = r := by
    apply Units.ext
    change PadicInt.toZMod (E.symm (E (hunit.unit : ℤ_[p]))) = 2
    rw [E.symm_apply_apply, hunit.unit_spec]
    exact map_ofNat _ _
  let c := ψ.comp (Units.map φ.toMonoidHom)
  have hc : Continuous c :=
    (continuous_of_discreteTopology (f := (ψ : (ZMod 5)ˣ → Circle))).comp (hφ.units_map _)
  refine ⟨v, ⟨c, hc⟩, a, ?_⟩
  change ψ (Units.map φ.toMonoidHom a) ^ 2 ≠ 1
  rw [ha, ← map_pow]
  exact hψ

private theorem printedTrace_ratIdeleClasses_norm_on_integral_units
    (e : (ℝ≥0ˣ × ((v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ)) ≃ₜ*
      IdeleClassGroup (𝓞 ℚ) ℚ) :
    ∀ u, ideleClassNorm ℚ (e (1, u)) = 1 := by
  let U := (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
  let (v : HeightOneSpectrum (𝓞 ℚ)) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let : CompactSpace U := by dsimp [U]; infer_instance
  let j : U →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ⟨e.toMonoidHom.comp (MonoidHom.inr ℝ≥0ˣ U), e.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let n : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ :=
    ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  have h := compactSubgroup_le_modulation_ker (n.comp j) ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set U)))
  exact fun u ↦ h (Subgroup.mem_top u)

private theorem printedTrace_exists_rat_quartic_twist :
    ∃ (χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) (u : (ideleClassNorm ℚ).ker),
      χ u.val ^ 2 ≠ 1 := by
  classical
  obtain ⟨v, c, a, ha⟩ := printedTrace_local_five_character
  obtain ⟨e, _⟩ := ratIdeleClassGroup_decomposition
  let units : (w : HeightOneSpectrum (𝓞 ℚ)) → (w.adicCompletionIntegers ℚ)ˣ := Pi.mulSingle v a
  let u : (ideleClassNorm ℚ).ker := ⟨e (1, units), printedTrace_ratIdeleClasses_norm_on_integral_units e units⟩
  let χh := c.toMonoidHom.comp ((Pi.evalMonoidHom _ v).comp ((MonoidHom.snd _ _).comp e.symm.toMonoidHom))
  let χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨χh, c.continuous.comp ((continuous_apply v).comp (continuous_snd.comp e.symm.continuous))⟩
  have hχu : χ u.val = c a := calc
    χ u.val = c ((e.symm (e (1, units))).2 v) := rfl
    _ = c (units v) := by rw [e.symm_apply_apply]
    _ = c a := by simp [units]
  exact ⟨χ, u, hχu ▸ ha⟩

/-- Paper: §§1.4.2–1.4.3, pp. 28–29. Use an order-four character modulo
five over the rationals with value `i` at two and let `u` have local unit
two at five and components one elsewhere. At norm two and parameter two,
the radial value is nonzero for all sufficiently late approximants.
Right translation by `u` multiplies the displayed test by `i`, while the
asserted conjugate weight would multiply it by `-i`. -/
theorem Printed.introTraceApprox_conjugateWeight_false :
    ¬ Printed.introTraceApprox_conjugateWeight := by
  intro hall
  obtain ⟨χ, u, hu⟩ := printedTrace_exists_rat_quartic_twist
  have hb : (∀ v : (ideleClassNorm ℚ).ker, χ v.val = 1) → χ = 1 := by
    intro ht
    exact (hu (by simp [ht u])).elim
  obtain ⟨h, ρ, hA, heq⟩ := hall ℚ χ hb
  have ht := introTraceApprox_tendsto h ρ hA 2 2 (by norm_num) (by norm_num)
  have hval : introTracePower 2 2 ≠ 0 := by rw [introTracePower_two.1]; norm_num
  obtain ⟨n, hn⟩ := (ht.eventually_ne hval).exists
  let two : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  have hsurj : Surjective (ideleClassNorm ℚ) := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.2.2.2.2.1
  obtain ⟨g, hg⟩ := hsurj two
  have hgu : ideleClassNorm ℚ (g * u.val) = two := by rw [map_mul, u.property, mul_one, hg]
  have he := heq n 2 g u
  rw [hgu, hg] at he
  change (χ (g * u.val) : ℂ) * introTraceApprox (h n) (ρ n) 2 2 =
    star (χ u.val : ℂ) * ((χ g : ℂ) * introTraceApprox (h n) (ρ n) 2 2) at he
  rw [map_mul, Circle.coe_mul] at he
  have hc : (χ u.val : ℂ) = star (χ u.val : ℂ) := by
    apply mul_left_cancel₀ (Circle.coe_ne_zero (χ g))
    apply mul_right_cancel₀ hn
    calc
      _ = _ := he
      _ = _ := by ring
  have hci : χ u.val = (χ u.val)⁻¹ := Subtype.ext (hc.trans (Circle.coe_inv_eq_conj _).symm)
  apply hu
  calc χ u.val ^ 2 = χ u.val * χ u.val := sq _
       _ = 1 := by nth_rw 2 [hci]; simp

open Classical in
/-- Paper: §1.4.3, p. 29. The printed real and complex archimedean
terms of the cutoff tests are uniformly bounded on the specified compact set. -/
def Printed.introTraceApprox_archimedean_bounded : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∃ C : ℝ, 0 < C ∧ ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
        ∀ (n : ℕ) (z : ℂ), z ∈ K →
          ‖printedReal[F](χ, printedFamily[F](χ, h, ρ, n, z))‖ ≤ C ∧
          ‖printedComplex[F](χ, printedFamily[F](χ, h, ρ, n, z))‖ ≤ C

/-- The closed disc around two lies in the right half-plane used in §1.4.3. -/
private theorem printedTrace_disk :
    Metric.closedBall (2 : ℂ) (1 / 4) ⊆ right(1) ∧
      (2 : ℂ) ∈ interior (Metric.closedBall (2 : ℂ) (1 / 4)) ∩ right(1) := by
  refine ⟨fun z hz ↦ ?_, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num)),
    by change (1 : ℝ) < (2 : ℂ).re; norm_num⟩
  have hd := (Complex.abs_re_le_norm (z - 2)).trans (mem_closedBall_iff_norm.mp hz)
  rw [Complex.sub_re, Complex.re_ofNat] at hd
  change (1 : ℝ) < z.re
  linarith [(abs_le.mp hd).1]

/-- At parameter two the radial approximant has real values between zero and one.
Its support lies in a compact interval strictly above one. -/
private theorem printedTrace_rat_two_profile (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) : ∃ (g : ℝ → ℝ) (c R : ℝ), 1 < c ∧ Measurable g ∧
      (∀ t, g t ∈ Icc 0 1) ∧ (∀ t, g t ≠ 0 → t ∈ Icc c R) ∧
      (∀ t, approx(h, ρ, n, (2 : ℂ)) t = (g t : ℂ)) := by
  let p (t : ℝ) := if 1 < t then (t ^ 2)⁻¹ else if t = 1 then 1 / 2 else 0
  have hp (t : ℝ) : p t ∈ Icc 0 1 := by
    unfold p
    split_ifs with h₁ h₂
    · exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ h₁.le)⟩
    · norm_num
    · norm_num
  have hm : Measurable p :=
    Measurable.ite measurableSet_Ioi (by fun_prop)
      (Measurable.ite (measurableSet_singleton 1) measurable_const measurable_const)
  have hpow (t : ℝ) : introTracePower 2 t = (p t : ℂ) := by
    unfold introTracePower p
    split_ifs <;> norm_num [Complex.cpow_neg]
  obtain ⟨hh, -, -, ε, _, hρ⟩ := hA
  let g (t : ℝ) := h n t * ∫ u, ρ n u * p (t - u)
  have hκ : Integrable (ρ n) := (hρ n).2.1.continuous.integrable_of_hasCompactSupport
    (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρ n).2.2.2.1)
  have hmem (t : ℝ) (ht : g t ≠ 0) : t ∈ tsupport (h n) := subset_tsupport _ (left_ne_zero_of_mul ht)
  have hK := (hh n).2.1
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℝ, 1 < c ∧ ∀ t ∈ tsupport (h n), c ≤ t := by
    rcases (tsupport (h n)).eq_empty_or_nonempty with he | hn
    · exact ⟨2, by norm_num, by simp [he]⟩
    · obtain ⟨c, hc, hlo⟩ := hK.exists_isMinOn hn continuousOn_id
      exact ⟨c, (hh n).2.2.1 hc, fun t ht ↦ hlo ht⟩
  obtain ⟨R, hmax⟩ := hK.bddAbove
  refine ⟨g, c, R, hc, ?_, ?_, fun t ht ↦ ⟨hmin _ (hmem _ ht), hmax (hmem _ ht)⟩, ?_⟩
  · have hk : Measurable (fun q : ℝ × ℝ ↦ ρ n q.2 * p (q.1 - q.2)) :=
      ((hρ n).2.1.continuous.measurable.comp measurable_snd).mul
        (hm.comp (measurable_fst.sub measurable_snd))
    exact (hh n).1.continuous.measurable.mul hk.stronglyMeasurable.integral_prod_right'.measurable
  · intro t
    have hi : Integrable (fun u ↦ ρ n u * p (t - u)) := hκ.mono
      (((hρ n).2.1.continuous.measurable.mul (hm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
      (Eventually.of_forall fun u ↦ by
        rw [norm_mul, Real.norm_of_nonneg (hp _).1]
        exact mul_le_of_le_one_right (norm_nonneg _) (hp _).2)
    have hlo : 0 ≤ ∫ u, ρ n u * p (t - u) := integral_nonneg fun u ↦ mul_nonneg ((hρ n).2.2.1 u) (hp _).1
    have hhi : (∫ u, ρ n u * p (t - u)) ≤ 1 := by
      rw [← (hρ n).2.2.2.2]
      exact integral_mono hi hκ fun u ↦ mul_le_of_le_one_right ((hρ n).2.2.1 u) (hp _).2
    exact ⟨mul_nonneg ((hh n).2.2.2 t).1 hlo,
      (mul_le_of_le_one_right ((hh n).2.2.2 t).1 hhi).trans ((hh n).2.2.2 t).2⟩
  · intro t
    simp only [introTraceApprox, hpow, g, ← Complex.ofReal_mul, integral_complex_ofReal]

/-- On the support of a nonnegative radial test the printed denominator is bounded away
from zero and is at most the denominator of the corrected real-place integrand. -/
private theorem printedTrace_rat_integral_le {K : Type*} [NormedField K] [ProperSpace K]
    [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ) [IsFiniteMeasureOnCompacts μ]
    {g : ℝ → ℝ} {c R : ℝ} (hc : 1 < c) (hg : Measurable g) (hb : ∀ t, g t ∈ Icc 0 1)
    (hs : ∀ t, g t ≠ 0 → t ∈ Icc c R) :
    (∫ u : Kˣ, g ‖u.val‖ * Real.sqrt ‖u.val‖ / ‖1 - u.val‖ ∂μ) ≤
      ∫ u : Kˣ, g ‖u.val‖ * Real.sqrt ‖u.val‖ / |1 - ‖u.val‖| ∂μ := by
  let f (u : Kˣ) := g ‖u.val‖ * Real.sqrt ‖u.val‖ / |1 - ‖u.val‖|
  let d (u : Kˣ) := g ‖u.val‖ * Real.sqrt ‖u.val‖ / ‖1 - u.val‖
  have hn : Continuous (fun u : Kˣ ↦ ‖u.val‖) := continuous_norm.comp Units.continuous_val
  have hf : Measurable f := ((hg.comp hn.measurable).mul (Real.continuous_sqrt.comp hn).measurable).div
    (continuous_abs.comp (continuous_const.sub hn)).measurable
  have hd : Measurable d := ((hg.comp hn.measurable).mul (Real.continuous_sqrt.comp hn).measurable).div
    ((continuous_const.sub Units.continuous_val).norm.measurable)
  have hf₀ (u : Kˣ) : 0 ≤ f u := div_nonneg (mul_nonneg (hb _).1 (Real.sqrt_nonneg _)) (abs_nonneg _)
  have hd₀ (u : Kˣ) : 0 ≤ d u := div_nonneg (mul_nonneg (hb _).1 (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hdf (u : Kˣ) : d u ≤ f u := by
    by_cases hz : g ‖u.val‖ = 0
    · simp [d, f, hz]
    have ht := hc.trans_le (hs _ hz).1
    have he : |1 - ‖u.val‖| ≤ ‖1 - u.val‖ := by
      simpa only [norm_one] using abs_norm_sub_norm_le (1 : K) u.val
    exact div_le_div_of_nonneg_left (mul_nonneg (hb _).1 (Real.sqrt_nonneg _))
      (abs_pos.mpr (sub_ne_zero.mpr ht.ne)) he
  let m : Kˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom
  let upper : ℝ≥0ˣ := Units.mk0 (⟨max R 2, by positivity⟩ : ℝ≥0) (by
    intro h
    have h' := congrArg ((↑) : ℝ≥0 → ℝ) h
    change max R 2 = 0 at h'
    linarith [le_max_right R (2 : ℝ)])
  let S := m ⁻¹' Icc 1 upper
  have hm : IsProperMap m := by simpa [m] using (isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero)
  have hI : IsCompact (Icc (1 : ℝ≥0ˣ) upper) := by
    apply (IsOpenUnits.isOpenEmbedding_unitsVal (M := ℝ≥0)).isEmbedding.isInducing.isCompact_iff.mpr
    have himage : Units.val '' Icc (1 : ℝ≥0ˣ) upper = Icc (1 : ℝ≥0) upper.val := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact hu
      · intro ht
        exact ⟨Units.mk0 t (zero_lt_one.trans_le ht.1).ne', ht, rfl⟩
    rw [himage]
    exact isCompact_Icc
  have hS : IsCompact S := hm.isCompact_preimage hI
  have hne (u : Kˣ) (hnz : g ‖u.val‖ ≠ 0) : u ∈ S := by
    have h := hs _ hnz
    exact ⟨show (1 : ℝ) ≤ ‖u.val‖ from hc.le.trans h.1,
      show ‖u.val‖ ≤ max R 2 from h.2.trans (le_max_left _ _)⟩
  let B := Real.sqrt (max R 2) / (c - 1)
  have hB : 0 ≤ B := div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hc.le)
  have hFI : Integrable f μ := by
    have ht : Integrable (S.indicator (fun _ : Kˣ ↦ B)) μ :=
      (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
    apply ht.mono' hf.aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_of_nonneg (hf₀ u)]
    by_cases hz : g ‖u.val‖ = 0
    · simp only [f, hz, zero_mul, zero_div]
      exact indicator_nonneg (fun _ _ ↦ hB) u
    rw [indicator_of_mem (hne u hz)]
    have hs' := hs _ hz
    dsimp only [f, B]
    rw [abs_of_neg (sub_neg.mpr (hc.trans_le hs'.1)), neg_sub]
    exact div_le_div₀ (Real.sqrt_nonneg _)
      ((mul_le_of_le_one_left (Real.sqrt_nonneg _) (hb _).2).trans
        (Real.sqrt_le_sqrt (hs'.2.trans (le_max_left _ _)))) (sub_pos.mpr hc) (by linarith [hs'.1])
  have hDI : Integrable d μ := hFI.mono' hd.aestronglyMeasurable
    (Eventually.of_forall fun u ↦ by rw [Real.norm_of_nonneg (hd₀ u)]; exact hdf u)
  exact integral_mono hDI hFI hdf

open Classical in
/-- For the trivial rational character the actual real-place kernel gives a lower bound
on the printed real-place term at parameter two. -/
private theorem printedTrace_rat_real_lower (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) :
    (∑ w : InfinitePlace ℚ, introTraceArchimedean (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) w).re ≤
      (printedReal[ℚ]((1 : U[ℚ]), printedFamily[ℚ]((1 : U[ℚ]), h, ρ, n, (2 : ℂ)))).re := by
  classical
  obtain ⟨g, c, R, hc, hg, hb, hs, hval⟩ := printedTrace_rat_two_profile h ρ hA n
  have hw := Rat.isReal_infinitePlace
  have hN (u : Rat.infinitePlace.Completionˣ) :
      N[ℚ](archClass[ℚ](Rat.infinitePlace) u) = ‖u.val‖ := by
    rw [ideleClassNorm_ofCompletion, hw.mult_eq_one, pow_one]
    rfl
  let : MeasurableSpace Rat.infinitePlace.Completion :=
    instMeasurableSpaceCompletion_riemannMasullo ℚ Rat.infinitePlace
  let : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
  let : BorelSpace Rat.infinitePlace.Completionˣ := borelSpace_units_of_continuousInv₀ _
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace
  let : ProperSpace Rat.infinitePlace.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  let μ := infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure Rat.infinitePlace
  have hcompare := printedTrace_rat_integral_le (K := Rat.infinitePlace.Completion) μ hc hg hb hs
  simp only [Fintype.sum_subsingleton _ Rat.infinitePlace, introTraceArchimedean, ite_eq_left hw,
    introTraceTest, PontryaginDual.one_apply, Circle.coe_one, star_one, one_mul, hw.mult_eq_one,
    pow_one, hN, hval, ← Complex.ofReal_mul, ← Complex.ofReal_div, integral_complex_ofReal,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left hcompare (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- Paper: §1.4.3, p. 29. Over the rationals take the trivial character,
half-width one, and the closed disk of radius one quarter about two. On
`1 < t < 2`, the positive real branch at parameter two dominates one half
of the integral of the approximant against `t^(-1/2)/(t-1) dt`. Fatou's
lemma gives divergence since the approximant tends to `t^(-2)`. -/
theorem Printed.introTraceApprox_archimedean_bounded_false :
    ¬ Printed.introTraceApprox_archimedean_bounded := by
  classical
  intro hall
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨C, _, hC⟩ := hall ℚ 1 1 (fun _ ↦ rfl) one_pos _ (isCompact_closedBall _ _)
    printedTrace_disk.1 ⟨2, printedTrace_disk.2⟩
  obtain ⟨n, hn⟩ := ((introTraceApprox_rat_archimedean_tendsto_atTop h ρ hA).eventually_gt_atTop C).exists
  exact (not_lt_of_ge ((printedTrace_rat_real_lower h ρ hA n).trans ((Complex.re_le_norm _).trans
    (hC h ρ hA n 2 (interior_subset printedTrace_disk.2.1)).1))) hn

open Classical in
/-- Paper: §1.4.3, p. 29. The two printed archimedean families have
holomorphic limits along a chosen cofinal cutoff sequence on the interior of
the specified compact set. -/
def Printed.introTraceApprox_archimedean_montel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∃ (h ρ : ℕ → ℝ → ℝ) (A B : ℂ → ℂ), IsIntroTraceApproximation h ρ ∧
        TendstoLocallyUniformlyOn (fun n z ↦ printedReal[F](χ, printedFamily[F](χ, h, ρ, n, z)))
          A atTop (interior K) ∧
        TendstoLocallyUniformlyOn (fun n z ↦ printedComplex[F](χ, printedFamily[F](χ, h, ρ, n, z)))
          B atTop (interior K) ∧
        AnalyticOnNhd ℂ A (interior K) ∧ AnalyticOnNhd ℂ B (interior K)

/-- Paper: §1.4.3, p. 29. At the trivial rational character, with half-width
one and the closed disk of radius one quarter about two, the real term at
the interior point two diverges along every cutoff subsequence. -/
theorem Printed.introTraceApprox_archimedean_montel_false :
    ¬ Printed.introTraceApprox_archimedean_montel := by
  classical
  intro hall
  obtain ⟨h, ρ, A, B, hA, hConv, _, _, _⟩ :=
    hall ℚ 1 1 (fun _ ↦ rfl) one_pos _ (isCompact_closedBall _ _)
      printedTrace_disk.1 ⟨2, printedTrace_disk.2⟩
  have ht := tendsto_atTop_mono (fun n ↦ printedTrace_rat_real_lower h ρ hA n)
    (introTraceApprox_rat_archimedean_tendsto_atTop h ρ hA)
  exact not_tendsto_nhds_of_tendsto_atTop ht _
    (Complex.continuous_re.continuousAt.tendsto.comp (hConv.tendsto_at printedTrace_disk.2.1))

/-- Paper: §1.4.3, p. 29. The spectral sums of the cutoff family converge
to a holomorphic function on the interior of the compact set outside the
window. The compact set is already to the right of the window. The
printed Mellin pairing is taken in the character of the zeros. -/
def Printed.introTraceApprox_spectral_limit : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ right(a) → (interior K ∩ right(1)).Nonempty →
      ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
        let term := fun n (z : ℂ) (r : windowZeros[F](χ, a)) ↦
          (zeroOrder[F](χ, r.val) : ℂ) *
            moment[F]((fun g : C[F] ↦ approx(h, ρ, n, z) (N[F](g))), χ, (r.val - 1 / 2))
        ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (interior K) ∧
          ∀ z ∈ interior K, (∀ n, Summable (term n z)) ∧
            Tendsto (fun n ↦ ∑' r, term n z r) atTop (𝓝 (H z))

/-- For the trivial rational character, the printed moment of a radial approximant is its
radial Mellin transform multiplied by the norm-one Tamagawa volume. -/
private theorem printedTrace_rat_moment (h ρ : ℕ → ℝ → ℝ) (hA : IsIntroTraceApproximation h ρ)
    (n : ℕ) (s : ℂ) :
    moment[ℚ]((fun g : C[ℚ] ↦ approx(h, ρ, n, (2 : ℂ)) (N[ℚ](g))), (1 : U[ℚ]), s) =
      (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ) *
        introTraceMellin approx(h, ρ, n, (2 : ℂ)) s := by
  obtain ⟨φ, hφ⟩ := introTraceApprox_exists_bruhat (F := ℚ) 1 h ρ hA n 2
  rw [← (introTraceTest_mellin (F := ℚ) 1 _ φ hφ s).2]
  refine integral_congr_ae (Eventually.of_forall fun g ↦ ?_)
  simp [hφ, introTraceTest]

/-- Paper: §1.4.3, p. 29. Take the trivial rational character, half-width
one, and the closed disk of radius one quarter about two. This window
contains the full zeta zero divisor. At two the full explicit formula
expresses the zero sum as the two bounded polar moments minus the bounded
prime-power sum and the real-place term tending to positive infinity.
Its real part tends to negative infinity, also along every subsequence. -/
theorem Printed.introTraceApprox_spectral_limit_false :
    ¬ Printed.introTraceApprox_spectral_limit := by
  classical
  intro hall
  have hdisk :
      Metric.closedBall (2 : ℂ) (1 / 4) ⊆ right(1) ∧
        (2 : ℂ) ∈ interior (Metric.closedBall (2 : ℂ) (1 / 4)) ∩ right(1) := by
    refine ⟨fun z hz ↦ ?_, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num)),
      by change (1 : ℝ) < (2 : ℂ).re; norm_num⟩
    have hd := (Complex.abs_re_le_norm (z - 2)).trans (mem_closedBall_iff_norm.mp hz)
    rw [Complex.sub_re, Complex.re_ofNat] at hd
    change (1 : ℝ) < z.re
    linarith [(abs_le.mp hd).1]
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  obtain ⟨H, _, hlimit⟩ := hall ℚ 1 1 (fun _ ↦ rfl) one_pos _ (isCompact_closedBall _ _)
    hdisk.1 ⟨2, hdisk.2⟩ h ρ hA
  have hlim := (hlimit 2 hdisk.2.1).2
  let V₁ : ℂ := ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal
  have hV : V₁ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    have hcl := NumberField.classNumber_pos ℚ
    have hreg := NumberField.Units.regulator_pos ℚ
    have htor := NumberField.Units.torsionOrder_pos ℚ
    have hdisc := Int.natAbs_pos.mpr (NumberField.discr_ne_zero ℚ)
    rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.toReal_ofReal (by positivity)]
    positivity
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ
  let Z := {r : ℂ // 0 < D r ∧ |r.re - 1 / 2| < (1 : ℝ)}
  have hscale (n : ℕ) :
      (∑' r : Z, (D r.val : ℂ) *
        moment[ℚ]((fun g : C[ℚ] ↦ approx(h, ρ, n, (2 : ℂ)) (N[ℚ](g))), (1 : U[ℚ]), (r.val - 1 / 2))) =
        V₁ * introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1 := by
    rw [introTraceSpectralSum, ← tsum_mul_left]
    apply tsum_congr
    intro r
    rw [printedTrace_rat_moment h ρ hA]
    dsimp [V₁]
    ring
  have hlim' : Tendsto (fun n ↦ V₁ * introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1)
      atTop (𝓝 (H 2)) := hlim.congr hscale
  have hconv : Tendsto (fun n ↦ introTraceSpectralSum (F := ℚ) 1 approx(h, ρ, n, (2 : ℂ)) 1)
      atTop (𝓝 (V₁⁻¹ * H 2)) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hV, one_mul] using hlim'.const_mul V₁⁻¹
  exact not_tendsto_nhds_of_tendsto_atBot (introTraceApprox_rat_spectral_tendsto_atBot h ρ hA) _
    (Complex.continuous_re.continuousAt.tendsto.comp hconv)

/-- Paper: §1.4.4, p. 29. The displayed prime-power sum converges locally
uniformly on the right of one to the positive shifted logarithmic derivative. -/
def Printed.introTraceApprox_primeSum_tendsto : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (π : uniformizers[F]), chartBase[F](χ) →
    (∀ v, isUniformizer[F](v, π v)) →
    ∀ (h ρ : ℕ → ℝ → ℝ), IsIntroTraceApproximation h ρ →
      TendstoLocallyUniformlyOn
        (fun n z ↦ ∑' p : V[F] × ℕ, printedPrime[F](χ, approx(h, ρ, n, z), π, p))
        (fun z ↦ logDeriv finiteL[F](χ) (z + 1 / 2)) atTop right(1)

open Classical in
/-- Paper: §1.4.5, pp. 29–30. Subtracting the two polar terms when the
character is trivial on the norm-one classes gives a holomorphic function
on the right of each positive half-width, with removable values filled in. -/
def Printed.introTrace_regularized_logDeriv_analytic : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (a : ℝ), chartBase[F](χ) → 0 < a →
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H right(a) ∧
      EqOn H (fun z ↦ logDeriv finiteL[F](χ) (z + 1 / 2) -
        if ∀ u : (ideleClassNorm F).ker, χ u.val = 1
        then 1 / (z + 1 / 2) + 1 / (z - 1 / 2) else 0) (right(a) \ {1 / 2})

open scoped ComplexOrder in
private theorem introTrace_regularized_logDeriv_neg (x : ℝ) (hx : 1 < x) :
    (logDeriv (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose x).re < 0 := by
  let L := (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose
  have hnear : L =ᶠ[𝓝 (x : ℂ)] riemannZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx] with z hz
    calc
      L z = finiteHeckeL (1 : U[ℚ]) ⟨z, hz⟩ :=
        (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose_spec.2 ⟨z, hz⟩
      _ = dedekindZeta ℚ z := finiteHeckeL_one_eq_dedekindZeta ⟨z, hz⟩
      _ = riemannZeta z := dedekindZeta_rat_eq_riemannZeta hz
  let a (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n
  have hpos : 0 < LSeries a (x : ℂ) := by
    have hterm (n : ℕ) : 0 ≤ LSeries.term a x n :=
      LSeries.term_nonneg (Complex.zero_le_real.mpr ArithmeticFunction.vonMangoldt_nonneg) x
    apply (ArithmeticFunction.LSeriesSummable_vonMangoldt hx).tsum_pos hterm 2
    apply LSeries.term_pos (by decide)
    apply Complex.zero_lt_real.mpr
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos one_lt_two
  change (logDeriv L x).re < 0
  rw [(logDeriv_congr_nhds hnear).eq_of_nhds]
  rw [show LSeries a (x : ℂ) = -logDeriv riemannZeta x by
    simpa only [logDeriv_apply, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hx] at hpos
  exact (Complex.lt_def.mp (neg_pos.mp hpos)).1

open scoped ComplexOrder in
private theorem introTraceApprox_primeSum_approx_nonneg (h ρ : ℕ → ℝ → ℝ)
    (hA : IsIntroTraceApproximation h ρ) (n : ℕ) (t : ℝ) :
    0 ≤ approx(h, ρ, n, (2 : ℂ)) t := by
  obtain ⟨ε, _, hρ⟩ := hA.2.2.2
  apply mul_nonneg (Complex.zero_le_real.mpr ((hA.1 n).2.2.2 t).1)
  apply integral_nonneg
  intro u
  apply mul_nonneg (Complex.zero_le_real.mpr ((hρ n).2.2.1 u))
  unfold introTracePower
  split_ifs with ht
  · rw [Complex.cpow_neg, Complex.cpow_ofNat]
    simpa only [Complex.ofReal_inv, Complex.ofReal_pow] using
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (sq_nonneg (t - u))))
  · simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      (Complex.zero_le_real.mpr (show 0 ≤ (1 / 2 : ℝ) by norm_num))
  · exact le_rfl

open scoped ComplexOrder in
/-- Paper: §1.4.4, p. 29. At parameter two the trivial rational character's
prime-power limit is strictly positive, with the prime two contributing a
positive term. The printed target `ζ'(5/2)/ζ(5/2)` is strictly negative. -/
theorem Printed.introTraceApprox_primeSum_tendsto_false :
    ¬ Printed.introTraceApprox_primeSum_tendsto := by
  classical
  intro hall
  obtain ⟨h, ρ, hA⟩ := exists_introTraceApproximation
  have hunif (v : V[ℚ]) : ∃ π : (v.adicCompletion ℚ)ˣ, isUniformizer[ℚ](v, π) := by
    obtain ⟨p, hp⟩ :=
      (Valued.v (R := v.adicCompletion ℚ)).exists_isUniformizer_of_isCyclic_of_nontrivial
    exact ⟨Units.mk0 _ hp.ne_zero, hp⟩
  choose π hπ using hunif
  have hlim := (hall ℚ 1 π (fun _ ↦ rfl) hπ h ρ hA).tendsto_at
    (show (2 : ℂ) ∈ right(1) by norm_num)
  have hsum : 0 ≤ logDeriv (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose (2 + 1 / 2) := by
    apply ge_of_tendsto hlim
    filter_upwards with n
    apply tsum_nonneg
    rintro ⟨v, k⟩
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_pow, star_one, one_mul]
    have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    rw [div_eq_mul_inv]
    apply mul_nonneg
    · exact mul_nonneg (Complex.zero_le_real.mpr (Real.log_nonneg hq.le))
        (add_nonneg (introTraceApprox_primeSum_approx_nonneg h ρ hA n _)
          (introTraceApprox_primeSum_approx_nonneg h ρ hA n _))
    · have hnorm := (Complex.inv_natCast_cpow_ofReal_pos
          (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne'
          (((k + 1 : ℕ) : ℝ) / 2)).le
      push_cast at hnorm ⊢
      exact hnorm
  have hneg := introTrace_regularized_logDeriv_neg (2 + 1 / 2) (by norm_num)
  push_cast at hneg
  exact hneg.not_ge (Complex.le_def.mp hsum).1

/-- Paper: §1.4.5, p. 30. With the trivial rational character and
half-width one quarter, the shifted log derivative has residue minus one
at one half because zeta has a simple pole at one. Subtracting the
printed correction gives residue minus two there. -/
theorem Printed.introTrace_regularized_logDeriv_analytic_false :
    ¬ Printed.introTrace_regularized_logDeriv_analytic := by
  intro hall
  obtain ⟨H, han, heq⟩ := hall ℚ 1 (1 / 4) (fun _ ↦ rfl) (by norm_num)
  have hhalf := (han _ (show (1 / 2 : ℂ) ∈ right(1 / 4) by norm_num)).continuousAt
  have hcont : ContinuousAt (fun t : ℝ ↦ (t - 1) * (H ((t : ℂ) - 1 / 2)).re) 1 := by
    apply (continuousAt_id.sub continuousAt_const).mul
    apply Complex.continuous_re.continuousAt.comp
    apply ContinuousAt.comp (g := H) _ (Complex.continuous_ofReal.continuousAt.sub_const _)
    convert hhalf using 1
    norm_num
  have hlim : Tendsto (fun t : ℝ ↦ (t - 1) * (H ((t : ℂ) - 1 / 2)).re)
      (𝓝[>] 1) (𝓝 0) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- The logarithmic derivative is negative to the right of one. The printed
  -- correction subtracts a further 1/(t-1), even arbitrarily close to one.
  have hbound : (0 : ℝ) ≤ -1 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
    have hz : (t : ℂ) - 1 / 2 ∈ right(1 / 4) \ {(1 / 2 : ℂ)} := by
      constructor
      · change 1 / 4 < ((t : ℂ) - 1 / 2).re
        norm_num
        linarith
      · intro h
        have := congrArg Complex.re (mem_singleton_iff.mp h)
        norm_num at this
        linarith
    have he := heq hz
    have htriv : ∀ u : (ideleClassNorm ℚ).ker, (1 : U[ℚ]) u.val = 1 := fun _ ↦ rfl
    simp only [ite_eq_left htriv, sub_add_cancel, show (t : ℂ) - 1 / 2 - 1 / 2 = t - 1 by ring] at he
    have hreal : (H ((t : ℂ) - 1 / 2)).re =
        (logDeriv (finiteHeckeL_exists_continuation (1 : U[ℚ])).choose t).re - (1 / t + 1 / (t - 1)) := by
      simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
        ← Complex.ofReal_add, Complex.sub_re, Complex.ofReal_re] using congrArg Complex.re he
    rw [hreal, mul_sub, mul_add, mul_one_div_cancel (sub_ne_zero.mpr ht.ne')]
    have hneg := introTrace_regularized_logDeriv_neg t ht
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.le) hneg.le,
      mul_nonneg (sub_nonneg.mpr ht.le) (show 0 ≤ 1 / t by positivity)]
  linarith

-- Section 1.1.4 (p. 12) chooses χ = 1 on the pure-norm component. In that
-- coordinate the possible pole of the shifted logarithmic derivative is at 1/2.
-- The twist |·|^i changes coordinates and supplies no refutation of §1.4.5.

/-- Paper: §1.4.7, p. 30. The Mellin transform of the extended test is the
local Mellin transform multiplied by the finite Euler product outside `S`.
Section 1.1.4 defines the local character by descent when χ is unramified
outside S. For the finite S specified on p. 30 the multiplier in print has no
outside integer-unit mass. The comparison is an identity of meromorphic germs. -/
def Printed.introTrace_transition_mellin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset V[F]) (χ : U[F])
    (hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))),
    let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
    let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous c
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦ sLocalIdelicZFunction f (twist s) *
        reciprocalPartialHeckeEulerProduct χ S s * finiteL[F](χ) s)

/-- The product of the omitted unit masses at the archimedean-only stage is
the reciprocal square root of the absolute discriminant. -/
private theorem introTrace_transition_mellin_false_mass (F : Type) [Field F] [NumberField F] :
    (∏ᶠ v : {v : V[F] // v ∉ (∅ : Finset V[F])},
      (((finiteLocalMultiplicativeTamagawaMeasure F v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) =
      (((Real.sqrt ((NumberField.discr F).natAbs : ℝ))⁻¹ : ℝ) : ℂ) := by
  classical
  let J := differentIdeal ℤ (𝓞 F)
  have hJ : J ≠ ⊥ := differentIdeal_ne_bot
  let T := (Ideal.finite_factors hJ).toFinset
  let d (v : V[F]) := multiplicity v.asIdeal J
  have hout (v : V[F]) (hv : v ∉ T) : d v = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    simpa [T, J] using hv
  have hfactor : ∏ v ∈ T, v.asIdeal ^ d v = J := by
    rw [← finprod_eq_finsetProd_of_mulSupport_subset (f := fun v : V[F] ↦ v.asIdeal ^ d v)]
    · exact Ideal.finprod_heightOneSpectrum_pow_multiplicity hJ
    · intro v hv
      by_contra hn
      exact hv (by simp [hout v hn])
  have hnorm : (∏ v ∈ T, (v.asIdeal.absNorm : ℝ) ^ d v) = ((NumberField.discr F).natAbs : ℝ) := by
    exact_mod_cast (by
      simpa only [map_prod, map_pow, J, NumberField.absNorm_differentIdeal F (𝓞 F)] using
        congrArg (fun I : Ideal (𝓞 F) ↦ Ideal.absNorm I) hfactor :
      (∏ v ∈ T, v.asIdeal.absNorm ^ d v) = (NumberField.discr F).natAbs)
  let m (v : V[F]) := (((finiteLocalMultiplicativeTamagawaMeasure F v)
    (v.adicCompletionIntegers F).units).toReal : ℂ)
  have hm (v : V[F]) : m v = (((Real.sqrt ((v.asIdeal.absNorm : ℝ) ^ d v))⁻¹ : ℝ) : ℂ) := by
    simp [m, finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_inv, d, J]
  change (∏ᶠ v : {v : V[F] // v ∉ (∅ : Finset V[F])}, m v.val) = _
  rw [finprod_subtype_eq_finprod_cond (f := m)]
  simp only [Finset.notMem_empty, not_false_eq_true, finprod_true]
  rw [finprod_eq_finsetProd_of_mulSupport_subset m (s := T)]
  · simp_rw [hm]
    rw [← Complex.ofReal_prod, Finset.prod_inv_distrib,
      ← Real.sqrt_prod T (fun _ _ ↦ by positivity), hnorm]
  · intro v hv
    by_contra hn
    exact hv (by simp [hm, hout v hn])

/-- Paper: §1.4.7, pp. 30–31. Take ℚ(i), the trivial character, S consisting
of the complex place alone, and a positive Gaussian there. The prime above 2
has different norm 4, hence unit mass 1/2. Every other finite unit mass is one.
The local transform and finite Euler product are positive for every real s > 1.
Their product must be multiplied by 1/2. Enlarging S as on p. 25 to contain
all field-ramified primes makes the printed multiplier valid in that case. -/
theorem Printed.introTrace_transition_mellin_false :
    ¬ Printed.introTrace_transition_mellin := by
  classical
  intro h
  let F := CyclotomicField 4 ℚ
  have : NeZero (4 : ℕ) := ⟨by decide⟩
  have : IsCyclotomicExtension {4} ℚ F := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  have : NumberField F := IsCyclotomicExtension.numberField {4} ℚ F
  have hdisc : (NumberField.discr F).natAbs = 4 := by
    rw [IsCyclotomicExtension.Rat.natAbs_discr (n := 4) (K := F)]
    have hfac : Nat.primeFactors 4 = {2} := by
      rw [show 4 = 2 ^ 2 by decide]
      exact Nat.primeFactors_prime_pow (by decide) Nat.prime_two
    rw [hfac, Finset.prod_singleton, show Nat.totient 4 = 2 by decide]
    norm_num
  let S : Finset V[F] := ∅
  let χ : U[F] := 1
  let ψ : PontryaginDual (SIdeleQuotient F S) := 1
  have hχ0 : ideleClassNormTwist χ 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S := by
    rw [hχ0]
    exact (mem_unramifiedOutside_iff F S 1).mpr fun _ _ _ ↦ rfl
  let c := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hχ⟩
  have hc : c = (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ := by
    ext g
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  let twist := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous c
  obtain ⟨f, hf⟩ := exists_sLocalIdelicZFunction_principalValue_attaining_poles (S := S) ψ
  let g := sAdelePrincipalValue F (Finset.Subset.refl S) f
  let Z (s : ℂ) := sLocalIdelicZFunction g (twist s)
  have hZ : meromorphicOrderAt Z 1 ≠ ⊤ := by
    dsimp only [Z, twist]
    rw [hc, hf]
    exact WithTop.coe_ne_top
  let L := finiteL[F](χ)
  obtain ⟨hL, hLf⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hnL : ∀ᶠ s in 𝓝[≠] (1 : ℂ), L s ≠ 0 := by
    apply ((hL (mem_univ (1 : ℂ))).meromorphicAt.eventually_eq_zero_or_eventually_ne_zero).resolve_left
    intro he
    have horder : meromorphicOrderAt L 1 ≤ 0 := introTrace_finiteL_no_zeros_one_line χ 0
    rw [meromorphicOrderAt_eq_top_iff.mpr he] at horder
    exact (not_le.mpr (WithTop.coe_lt_top (0 : ℤ))) horder
  have hraw := weilIdentity_unramifiedOutside_meromorphic (F := F) S g χ hχ L hL
    (fun z hz ↦ hLf ⟨z, hz⟩)
  have hbad := h F S χ hχ g
  have hmass := introTrace_transition_mellin_false_mass F
  rw [hdisc] at hmass
  have hs4 : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  norm_num [hs4] at hmass
  apply hZ (meromorphicOrderAt_eq_top_iff.mpr ?_)
  filter_upwards [hbad.filter_mono (nhdsNE_le_codiscrete 1),
    hraw.filter_mono (nhdsNE_le_codiscrete 1), hnL] with s h₁ h₂ hs
  have he := h₁.symm.trans h₂
  change Z s * reciprocalPartialHeckeEulerProduct χ S s * L s =
    _ * Z s * (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s at he
  simp only [reciprocalPartialHeckeEulerProduct, S, Finset.prod_empty, mul_one, hmass] at he
  apply (mul_eq_zero.mp ?_).resolve_right hs
  linear_combination 2 * he

end RiemannMasullo
