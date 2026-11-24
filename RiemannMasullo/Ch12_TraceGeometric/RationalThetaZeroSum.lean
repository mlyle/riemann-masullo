module
public import RiemannMasullo.Ch12_TraceGeometric.ThetaLiftCost
public import RiemannMasullo.Ch11_ShellStructure.RationalThetaLattice
public import Mathlib.NumberTheory.LSeries.ZetaZeros
import RiemannMasullo.Ch13_ZerosHecke.Targets
/-!
# A rational theta bound for the ordinary Riemann zeta zeros

A four-modulus theta approximation on the negative log-norm half-line supplies one
numerical error for the finite zero product. Over the rationals its principal
character gives a bound on the sum of the normalized displacements of all distinct
zeta zeros to the right of the critical line, and a closed zero-free disk.
-/

open Set Function MeasureTheory NumberField IsDedekindDomain
open scoped Topology NNReal NumberField.AdeleRing
public noncomputable section
namespace RiemannMasullo
set_option quotPrecheck false
local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "IQ" => IdeleGroup (𝓞 ℚ) ℚ
local instance : MeasurableSpace CQ := borel _

private theorem rationalTheta_zero_bounds :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧
      0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual CQ)) ρ}
    let d (ρ : Z) := (2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2
    (∀ ρ : Z, d ρ < 1 / 25) ∧ Summable d ∧ ∑' ρ : Z, d ρ < Real.log (25 / 24) := by
  intro Z d
  let σ : ℝ≥0ˣ →ₜ* IQ := ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hσ : RightInverse σ (ideleNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g (x : ℝ) : CQ := QuotientGroup.mk (σ (e x))
  have hg (x : ℝ) : ((ideleClassNorm ℚ (g x)).val : ℝ) = Real.exp x := by
    change ((ideleNorm ℚ (σ (e x))).val : ℝ) = _
    exact congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (hσ (e x))
  obtain ⟨f, hsup, hdist⟩ := exists_ratTheta_halfLine_sqError_lt_one_div_twentyFive
  have hθ (x : ℝ) : centeredLogThetaLift (1 : PontryaginDual CQ) σ f x =
      homogeneousAdelicTheta 1 f.val (g x) * Complex.exp ((x : ℂ) / 2) := by
    simp [centeredLogThetaLift, g, e, PontryaginDual.one_apply]
    rfl
  have hs (x : ℝ) (hx : 0 < x) : centeredLogThetaLift (1 : PontryaginDual CQ) σ f x = 0 := by
    rw [hθ, hsup (g x) (by rw [hg]; exact Real.one_lt_exp_iff.mpr hx), zero_mul]
  let E := hiddenThetaCost 0 0 0 (fun x ↦ Complex.exp ((x : ℂ) / 2) -
      centeredLogThetaLift (1 : PontryaginDual CQ) σ f x) ^ 2
  have hE : E < 1 / 25 := by
    simpa only [E, hiddenThetaCost, neg_zero, intervalSobolevDensity, mul_zero, zero_mul, Real.exp_zero,
      max_self, zero_div, Real.rpow_zero, mul_one, hθ, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
      using hdist g hg
  obtain ⟨h1, h2⟩ := centeredLogThetaLift_right_zero_sum (1 : PontryaginDual CQ) σ hσ f hs (lt_trans hE (by norm_num))
  have hsingle (ρ : Z) : d ρ < 1 / 25 := by
    have h := centeredLogThetaLift_halfLine_distance (1 : PontryaginDual CQ) σ hσ f hs ρ.val
      ρ.property.1 ρ.property.2
    have hp : 0 ≤ 2 * (ρ.val.re - 1 / 2) := by linarith [ρ.property.1]
    have hpow := pow_le_pow_left₀ (div_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) h 2
    rw [div_pow, Real.sq_sqrt hp] at hpow
    change (2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2 < 1 / 25
    exact lt_of_le_of_lt (by simpa only [show 2 * (ρ.val.re - 1 / 2) = 2 * ρ.val.re - 1 by ring] using hpow) hE
  refine ⟨hsingle, h1, lt_of_le_of_lt h2 ?_⟩
  change -Real.log (1 - E) < Real.log (25 / 24)
  rw [← Real.log_inv]
  apply Real.log_lt_log (inv_pos.mpr (by linarith))
  rw [inv_eq_one_div, div_lt_iff₀ (by linarith)]
  linarith

private theorem riemannZeta_right_zero_order (s : ℂ) (hs : 1 / 2 < s.re) (hz : riemannZeta s = 0) :
    0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual CQ)) s := by
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hne : s ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hz)
  rw [← meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual CQ) hm (fun t ↦
    (dedekindZeta_rat_eq_riemannZeta t.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) t).symm) (by linarith : 0 < s.re)]
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm _ (mem_univ _))).mp
  rw [← hz]
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

/-- The four-modulus theta approximation bounds the total normalized displacement of the
distinct ordinary zeta zeros to the right of the critical line. -/
theorem riemannZeta_right_zero_sum_lt_log :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ riemannZeta ρ = 0}
    let d (ρ : Z) := (2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2
    Summable d ∧ ∑' ρ : Z, d ρ < Real.log (25 / 24) := by
  intro Z d
  let H := {ρ : ℂ // 1 / 2 < ρ.re ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual CQ)) ρ}
  let f (ρ : H) := (2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2
  let i (ρ : Z) : H := ⟨ρ.val, ρ.property.1, riemannZeta_right_zero_order ρ.val ρ.property.1 ρ.property.2⟩
  have hi : Injective i := fun _ _ h ↦ Subtype.ext (congrArg (fun w : H ↦ (w.val : ℂ)) h)
  have h : Summable f := rationalTheta_zero_bounds.2.1
  have hb : ∑' ρ : H, f ρ < Real.log (25 / 24) := rationalTheta_zero_bounds.2.2
  have h' : Summable d := (h.comp_injective (i := i) hi : Summable (f ∘ i))
  have hf (ρ : H) : 0 ≤ f ρ := div_nonneg (by linarith [ρ.property.1]) (sq_nonneg _)
  have hl : ∑' ρ : Z, d ρ ≤ ∑' ρ : H, f ρ :=
    h'.tsum_le_tsum_of_inj i hi (fun a _ ↦ hf a) (fun _ ↦ le_rfl) h
  exact ⟨h', hl.trans_lt hb⟩

/-- The same adelic test gives a closed zero-free disk for the ordinary Riemann zeta
function, with center 25 and squared radius 600. -/
theorem riemannZeta_ne_zero_of_theta_disk (s : ℂ) (hdisk : ‖s - 25‖ ^ 2 ≤ 600) :
    riemannZeta s ≠ 0 := by
  have hs : ‖s‖ ^ 2 ≤ 25 * (2 * s.re - 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hdisk ⊢
    norm_num at hdisk
    nlinarith
  have hs0 : s ≠ 0 := fun e ↦ by subst s; norm_num at hs
  have hn := sq_pos_of_pos (norm_pos_iff.mpr hs0)
  have hr : 1 / 2 < s.re := by linarith
  intro hz
  have h := rationalTheta_zero_bounds.1 ⟨s, hr, riemannZeta_right_zero_order s hr hz⟩
  change (2 * s.re - 1) / ‖s‖ ^ 2 < 1 / 25 at h
  rw [div_lt_iff₀ hn] at h
  linarith

end RiemannMasullo
