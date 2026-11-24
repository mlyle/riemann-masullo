module

public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b

import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import Mathlib.Analysis.Meromorphic.Complex
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# §7.1.1–7.1.2 Almost periodic functions and S-local theta asymptotics

The finite set `S` lists the finite places. All archimedean places are included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators NNReal Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F

-- The Euler product, its reciprocal, and the upper density in (7.1.1.1),
-- (7.1.1.2), and (7.1.1.4) use the constructions of §B.5.3.

-- TODO(paper-gap): Lemma 7.1.1.1(1) forces T₀ = 0. The trivial character of ℚ
-- with a finite place above 2 has a pole at σ = T₀ = 0. For ramified places in S,
-- the phase in the printed product is undefined. Equation (7.1.1.3) also reverses
-- the phase sign in (7.1.1.1).

/-- A factor `1 - u r` with `r ∈ [m, M]` and `0 < m` has norm at least
`max (m |Im u|) (1 - M max (Re u) 0)`, a continuous function of `u` alone. -/
private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_factor
    (u : ℂ) {m M r : ℝ} (hm : 0 < m) (hr : r ∈ Icc m M) :
    max (m * |u.im|) (1 - M * max u.re 0) ≤ ‖1 - u * (r : ℂ)‖ := by
  have hr0 : 0 ≤ r := hm.le.trans hr.1
  refine max_le ?_ ?_
  · calc m * |u.im| ≤ r * |u.im| := mul_le_mul_of_nonneg_right hr.1 (abs_nonneg _)
      _ = |(1 - u * (r : ℂ)).im| := by
          simp [abs_mul, abs_of_nonneg hr0, mul_comm]
      _ ≤ ‖1 - u * (r : ℂ)‖ := Complex.abs_im_le_norm _
  · have h1 : r * u.re ≤ r * max u.re 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hr0
    have h2 : r * max u.re 0 ≤ M * max u.re 0 :=
      mul_le_mul_of_nonneg_right hr.2 (le_max_right _ _)
    calc 1 - M * max u.re 0 ≤ 1 - u.re * r := by nlinarith
      _ = (1 - u * (r : ℂ)).re := by simp
      _ ≤ ‖1 - u * (r : ℂ)‖ := Complex.re_le_norm _

private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_eventually_pos
    (z : ℂ) {ω m M : ℝ} (hω : ω ≠ 0) (hm : 0 < m) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
      (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0) := by
  have hc : Continuous (fun t : ℝ ↦ max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
      (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0)) := by fun_prop
  by_cases h0 : 0 < max (m * |z.im|) (1 - M * max z.re 0)
  · have h0' : 0 < (fun t : ℝ ↦ max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
        (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0)) 0 := by simpa using h0
    exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds h0')
  · rw [not_lt, max_le_iff] at h0
    have him : z.im = 0 := by
      have := h0.1
      have : |z.im| ≤ 0 := by nlinarith [abs_nonneg z.im]
      exact abs_nonpos_iff.mp this
    have hre : 0 < z.re := by
      by_contra h
      rw [max_eq_right (not_lt.mp h)] at h0
      linarith [h0.2]
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (Real.pi / |ω|) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hI] with t ht
    apply lt_max_of_lt_left
    apply mul_pos hm
    apply abs_pos.mpr
    rw [Circle.coe_exp, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, him, zero_mul, add_zero]
    refine mul_ne_zero hre.ne' ?_
    have hω' : 0 < |ω| := abs_pos.mpr hω
    have hlt : |t * ω| < Real.pi := by
      rw [abs_mul, abs_of_pos ht.1]
      have := ht.2
      rwa [lt_div_iff₀ hω'] at this
    intro hs
    rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le (t * ω)])
      (lt_of_le_of_lt (le_abs_self _) hlt)] at hs
    exact (mul_ne_zero ht.1.ne' hω) hs

private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_phaseShift
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (ω : ι → ℝ) (hω : ∀ i, ω i ≠ 0) (m M : ι → ℝ)
    (hm : ∀ i, 0 < m i) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → Circle, ∃ t ∈ Ioo (0 : ℝ) 1, ∀ r : ι → ℝ,
      (∀ i, r i ∈ Icc (m i) (M i)) →
      c ≤ ‖∏ i, (1 - a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ) * (r i : ℂ))‖ := by
  classical
  let h (i : ι) (u : ℂ) : ℝ := max (m i * |u.im|) (1 - M i * max u.re 0)
  let Q (t : ℝ) (x : ι → Circle) : ℝ :=
    ∏ i, h i (a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ))
  have hQ (t : ℝ) : Continuous (Q t) := by
    dsimp [Q, h]
    fun_prop
  have hshift (x : ι → Circle) : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < Q t x := by
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨t, ht, hf⟩ := (hI.and (eventually_all.mpr fun i ↦
      exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_eventually_pos
        (a i * x i) (M := M i) (hω i) (hm i))).exists
    exact ⟨t, ht, Finset.prod_pos fun i _ ↦ hf i⟩
  choose t ht hpos using hshift
  let d (x : ι → Circle) := Q (t x) x / 2
  let U (x : ι → Circle) := {y | d x < Q (t x) y}
  have hU (x) : U x ∈ 𝓝 x :=
    (isOpen_lt continuous_const (hQ (t x))).mem_nhds (half_lt_self (hpos x))
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  have cover (y : ι → Circle) : ∃ x ∈ s, y ∈ U x := by
    have : y ∈ ⋃ x ∈ s, U x := hs ▸ mem_univ y
    simpa only [mem_iUnion, exists_prop] using this
  obtain ⟨x, hx, _⟩ := cover 1
  obtain ⟨z, _, hz⟩ := s.exists_min_image d ⟨x, hx⟩
  refine ⟨d z, half_pos (hpos z), fun y ↦ ?_⟩
  obtain ⟨x, hx, hy⟩ := cover y
  refine ⟨t x, ht x, fun r hr ↦ (hz x hx).trans ((le_of_lt hy).trans ?_)⟩
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun i _ ↦ le_max_of_le_left (mul_nonneg (hm i).le (abs_nonneg _)))
    fun i _ ↦ exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_factor
      _ (hm i) (hr i)

/-- Paper: Lemma 7.1.1.1, p. 313.
There are ordered heights escaping to infinity on both tails at which the finite Euler
product is uniformly bounded on the closed strip from `-δ` to `1 + δ`.
Deviation: Uses the sign convention for index zero from §B.5.3.2 and the Euler factors
of §3.2.1, with factor one at ramified places. A positive lower bound on the reciprocal
product expresses both the upper bound and avoidance of poles. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow
    (S : Finset Primes) (_hPic : Subsingleton (CommRing.Pic ((S : Set Primes).integer F)))
    (χ : PontryaginDual C𝔽) (_hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    {δ : ℝ} (_hδ : 0 < δ) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-δ) (1 + δ),
        c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ := by
  classical
  let q (v : S) : ℝ := (v.val.asIdeal.absNorm : ℝ)
  have hq1 (v : S) : 1 < q v := by
    dsimp only [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  let a (v : S) : ℂ := if (ideleClassNormTwist χ 0).IsUnramifiedAt v.val then
    (ideleClassNormTwist χ 0).localValue v.val else 0
  let ω (v : S) := -Real.log (q v)
  let phase (r : ℝ) (v : S) := Circle.exp (r * ω v)
  have hω (v : S) : ω v ≠ 0 := neg_ne_zero.mpr (Real.log_pos (hq1 v)).ne'
  have hpow (σ r : ℝ) (v : S) :
      (v.val.asIdeal.absNorm : ℂ) ^ (-((σ : ℂ) + (r : ℂ) * Complex.I)) =
        (phase r v : ℂ) * ((q v ^ (-σ) : ℝ) : ℂ) := by
    have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val)).ne'
    rw [Complex.cpow_def_of_ne_zero hq, ← Complex.natCast_log, Circle.coe_exp,
      Real.rpow_def_of_pos (zero_lt_one.trans (hq1 v)), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [ω, q]
    push_cast
    ring
  have hfac (σ r t : ℝ) (v : S) :
      (finiteHeckeEulerFactor χ v.val ((σ : ℂ) + ((r + t : ℝ) : ℂ) * Complex.I))⁻¹ =
        1 - a v * (phase r v : ℂ) * (Circle.exp (t * ω v) : ℂ) * ((q v ^ (-σ) : ℝ) : ℂ) := by
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v.val
    · rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv, hpow]
      simp only [a, ite_eq_left hv, phase, add_mul, Circle.exp_add, Circle.coe_mul]
      ring
    · rw [finiteHeckeEulerFactor, ite_eq_right hv]
      simp [a, hv]
  obtain ⟨c, hc, hshift⟩ :=
    exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_phaseShift
      a ω hω (fun v ↦ q v ^ (-(1 + δ))) (fun v ↦ q v ^ δ)
      (fun v ↦ Real.rpow_pos_of_pos (zero_lt_one.trans (hq1 v)) _)
  choose t ht hbound using fun k : ℤ ↦ hshift (phase k)
  let T (k : ℤ) : ℝ := k + t k
  have hI (k : ℤ) : T k ∈ Ioo (k : ℝ) ((k : ℝ) + 1) :=
    ⟨lt_add_of_pos_right _ (ht k).1, add_lt_add_right (ht k).2 _⟩
  refine ⟨c, T, hc, ?_, ?_, ?_, ?_, fun k σ hσ ↦ ?_⟩
  · apply monotone_int_of_le_succ
    intro k
    exact ((hI k).2.trans (by simpa only [Int.cast_add, Int.cast_one] using (hI (k + 1)).1)).le
  · intro k hk
    exact (show 0 ≤ (k : ℝ) by exact_mod_cast hk).trans (hI k).1.le
  · intro k hk
    have h : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
    exact (hI k).2.le.trans h
  · have hlim : Tendsto (fun k : ℤ ↦ ((|k| : ℤ) : ℝ)) (comap (abs : ℤ → ℤ) atTop) atTop :=
      tendsto_intCast_atTop_atTop.comp tendsto_comap
    refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_atTop_add_const_right _ (-1) hlim)
    rw [Int.cast_abs]
    have h := abs_sub_abs_le_abs_sub (k : ℝ) (T k)
    rw [abs_of_nonpos (sub_nonpos.mpr (hI k).1.le)] at h
    linarith [(hI k).2]
  · have hr (v : S) : q v ^ (-σ) ∈ Icc (q v ^ (-(1 + δ))) (q v ^ δ) :=
      ⟨Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith [hσ.2]),
        Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith [hσ.1])⟩
    have h := hbound k (fun v ↦ q v ^ (-σ)) hr
    rw [reciprocalPartialHeckeEulerProduct, ← Finset.prod_coe_sort]
    simpa only [T, hfac] using h


-- TODO(paper-gap): The proof on p. 315 uses a different reflection for each place,
-- and positive symmetric upper density alone does not guarantee visits on both tails.
-- The zero list on p. 313 also omits the shift by -itᵥ in (7.1.1.1).

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
local notation "zetaGerm(" f "," c ")" => fun z ↦ sLocalIdelicZFunction f (twistₛ c z)

-- TODO(paper-gap): The preamble's a₋ₙ ≠ 0 condition at N = 0 fails at holomorphic zeros.

/-- Paper: Definition 7.1.2.1, p. 316.
The polar S-multiplicity is the order of the pole of the continued zeta function at `c`.
It is zero at every point without a pole, including when the germ vanishes identically. -/
def sLocalPolarMultiplicity (f : ℬₛ) (c : QuasiCharacter Jₛ) : ℕ :=
  (-(meromorphicOrderAt (zetaGerm(f, c)) 0).untop₀).toNat

/-- Paper: Definition 7.1.2.1, p. 316.
The multiplicity vanishes exactly at the quasi-characters with nonnegative meromorphic order. -/
theorem sLocalPolarMultiplicity_eq_zero_iff (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    sLocalPolarMultiplicity f c = 0 ↔
      0 ≤ meromorphicOrderAt (zetaGerm(f, c)) 0 := by
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (zetaGerm(f, c)) 0 = o
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n => simp

/-- Paper: Definition 7.1.2.1, p. 316.
The integer-indexed Laurent coefficient is computed in the norm-twist coordinate centered
at `c`, by taking the residue after shifting the desired power to exponent minus one. -/
def sLocalZLaurentCoeff (f : ℬₛ) (c : QuasiCharacter Jₛ) (m : ℤ) : ℂ :=
  complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (m + 1)) 0

/-- Circle integrals of `g z / z ^ (k + 1)` over small circles, for `g = z ^ (-N) * h`. -/
private theorem sLocalZLaurentCoeff_hasLaurentSeries_circleIntegral {g h : ℂ → ℂ} {N : ℕ}
    {R : ℝ≥0} (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (Metric.closedBall 0 R))
    (hg : ∀ z, z ≠ 0 → g z = z ^ (-(N : ℤ)) * h z) (k : ℤ) {r : ℝ} (hr : r ∈ Ioo 0 (R : ℝ)) :
    circleIntegral (fun z ↦ g z / z ^ (k + 1)) 0 r / (2 * (Real.pi : ℂ) * Complex.I) =
      if (-(N : ℤ)) ≤ k then cauchyPowerSeries h 0 R (k + N).toNat (fun _ ↦ 1) else 0 := by
  have hr0 : (0 : ℝ) < r := hr.1
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall hr.2.le
  have hne : ∀ z ∈ Metric.sphere (0 : ℂ) r, z ≠ 0 := fun z hz h0 ↦ by
    rw [h0, mem_sphere_zero_iff_norm, norm_zero] at hz; exact hr0.ne hz
  split_ifs with hk
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, k + N = j := ⟨(k + N).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hj, Int.toNat_natCast]
    let r' : ℝ≥0 := ⟨r, hr0.le⟩
    have hp1 : HasFPowerSeriesOnBall h (cauchyPowerSeries h 0 r') 0 r' :=
      (hh.mono hsub).hasFPowerSeriesOnBall (by exact_mod_cast hr0)
    have hp2 : HasFPowerSeriesOnBall h (cauchyPowerSeries h 0 R) 0 R := hh.hasFPowerSeriesOnBall hR
    rw [← hp1.hasFPowerSeriesAt.eq_formalMultilinearSeries hp2.hasFPowerSeriesAt,
      cauchyPowerSeries_apply, smul_eq_mul, inv_mul_eq_div]
    congr 1
    refine circleIntegral.integral_congr hr0.le fun z hz ↦ ?_
    have hz := hne z hz
    simp only [sub_zero, smul_eq_mul, hg z hz]
    have hk' : k + 1 = (j : ℤ) + 1 - N := by omega
    rw [hk', zpow_sub₀ hz, zpow_neg, zpow_add_one₀ hz, zpow_natCast, zpow_natCast]
    field_simp
    rw [one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]
  · rw [div_eq_zero_iff]
    left
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -(N : ℤ) - (k + 1) = m := ⟨(-(N : ℤ) - (k + 1)).toNat,
      (Int.toNat_of_nonneg (by omega)).symm⟩
    have hd : DifferentiableOn ℂ (fun z ↦ z ^ m * h z) (Metric.closedBall 0 r) :=
      ((differentiable_pow m).differentiableOn).mul (hh.mono hsub)
    rw [circleIntegral.integral_congr hr0.le (g := fun z ↦ z ^ m * h z) fun z hz ↦ ?_]
    · exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr0.le countable_empty
        hd.continuousOn fun z hz ↦ hd.differentiableAt
          (mem_of_superset (Metric.isOpen_ball.mem_nhds hz.1) Metric.ball_subset_closedBall)
    · have hz := hne z hz
      simp only [hg z hz]
      rw [← zpow_natCast, ← hm, zpow_sub₀ hz]
      field_simp

/-- A germ meromorphic at zero has the Laurent series given by its residue coefficients. -/
private theorem sLocalZLaurentCoeff_hasLaurentSeries_of_meromorphicAt {g : ℂ → ℂ}
    (hg : MeromorphicAt g 0) :
    HasVectorLaurentSeriesAt g 0 (fun k ↦ complexResidue (fun z ↦ g z / z ^ (k + 1)) 0) := by
  obtain ⟨N, hN⟩ := hg
  let h : ℂ → ℂ := fun z ↦ (z - 0) ^ N • g z
  obtain ⟨R₀, hR₀, hR₀h⟩ := hN.exists_ball_analyticOnNhd
  let R : ℝ≥0 := ⟨R₀ / 2, by positivity⟩
  have hR : (0 : ℝ≥0) < R := by
    change (0 : ℝ) < R₀ / 2; positivity
  have hRR : (R : ℝ) < R₀ := by change R₀ / 2 < R₀; linarith
  have hh : DifferentiableOn ℂ h (Metric.closedBall 0 R) := fun z hz ↦
    (hR₀h z (Metric.closedBall_subset_ball hRR hz)).differentiableAt.differentiableWithinAt
  have hgh : ∀ z, z ≠ 0 → g z = z ^ (-(N : ℤ)) * h z := fun z hz ↦ by
    simp only [h, sub_zero, smul_eq_mul, zpow_neg, zpow_natCast]
    field_simp
  let p := cauchyPowerSeries h 0 R
  have hp : HasFPowerSeriesOnBall h p 0 R := hh.hasFPowerSeriesOnBall hR
  have hcoef (k : ℤ) : complexResidue (fun z ↦ g z / z ^ (k + 1)) 0 =
      if (-(N : ℤ)) ≤ k then p (k + N).toNat (fun _ ↦ 1) else 0 := by
    refine (tendsto_const_nhds.congr' ?_).limUnder_eq
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < R from hR)] with r hr
    exact (sLocalZLaurentCoeff_hasLaurentSeries_circleIntegral hR hh hgh k hr).symm
  refine ⟨-(N : ℤ), R, hR, fun k hk ↦ ?_, ?_⟩
  · beta_reduce
    rw [hcoef, ite_eq_right_iff.mpr fun h ↦ absurd h (not_le.mpr hk)]
  intro K hK hKc
  have hK0 : ∀ w ∈ K, w ≠ 0 := fun w hw ↦ (hK hw).2
  obtain ⟨r', hr', hKr'⟩ := exists_pos_lt_subset_ball (show (0 : ℝ) < R from hR) hKc.isClosed
    (fun w hw ↦ (hK hw).1)
  let r'' : ℝ≥0 := ⟨r', hr'.1.le⟩
  have hU := hp.tendstoUniformlyOn (r' := r'') (by exact_mod_cast hr'.2)
  obtain ⟨C, hC⟩ : ∃ C, ∀ w ∈ K, ‖w ^ (-(N : ℤ))‖ ≤ C :=
    hKc.exists_bound_of_continuousOn (fun w hw ↦
      (continuousAt_zpow₀ _ _ (Or.inl (hK0 w hw))).continuousWithinAt)
  have hsum (n : ℕ) (w : ℂ) (hw : w ≠ 0) :
      ∑ j ∈ Finset.range n, (w - 0) ^ (-(N : ℤ) + (j : ℤ)) •
        complexResidue (fun z ↦ g z / z ^ (-(N : ℤ) + (j : ℤ) + 1)) 0 =
        w ^ (-(N : ℤ)) * p.partialSum n w := by
    rw [FormalMultilinearSeries.partialSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff (z := w), hcoef,
      ite_eq_left_iff.mpr fun h ↦ absurd (show -(N : ℤ) ≤ -(N : ℤ) + j by omega) h,
      show (-(N : ℤ) + j + N).toNat = j by omega, sub_zero, zpow_add₀ hw, zpow_natCast,
      smul_eq_mul, smul_eq_mul, FormalMultilinearSeries.coeff, mul_assoc]
    rfl
  rw [IsUniformAddGroup.rightUniformSpace_eq, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC' : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hU (ε / max C 1) (div_pos hε hC')] with n hn
  intro w hw
  have hwb : w ∈ Metric.ball (0 : ℂ) r'' := hKr' hw
  have h1 := hn w hwb
  rw [zero_add] at h1
  rw [hsum n w (hK0 w hw), hgh w (hK0 w hw), dist_eq_norm, ← mul_sub, norm_mul, ← dist_eq_norm]
  calc ‖w ^ (-(N : ℤ))‖ * dist (h w) (p.partialSum n w)
      ≤ max C 1 * dist (h w) (p.partialSum n w) :=
        mul_le_mul_of_nonneg_right ((hC w hw).trans (le_max_left _ _)) dist_nonneg
    _ < max C 1 * (ε / max C 1) := mul_lt_mul_of_pos_left h1 hC'
    _ = ε := by field_simp

/-- Every S-local quasi-character is a norm twist of a unitary character, so its norm-twist
line is a translate of a unitary chart. -/
private theorem sLocalZLaurentCoeff_hasLaurentSeries_chart (c : QuasiCharacter Jₛ) :
    ∃ (χ : PontryaginDual Jₛ) (s : ℂ), ∀ z : ℂ, twistₛ c z =
      twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) (s + z) := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  have hp := isProperMap_sIdeleQuotientNorm F S
  have hne : ∃ g, mₛ g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mₛ hp hne c
  let d := twistₛ c (-(a : ℂ))
  have hrad (g : Jₛ) : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mₛ hp hne]
  have hd (g : Jₛ) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jₛ) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jₛ :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  change c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z =
    d g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) + z)
  rw [hd, Complex.cpow_add _ _ hN, hrad, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (hn g))]

/-- Paper: Definition 7.1.2.1, p. 316.
The coefficient sequence gives a Laurent expansion of the centered zeta germ, with partial
sums converging uniformly on compact subsets of a punctured disc. -/
theorem sLocalZLaurentCoeff_hasLaurentSeries (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    HasVectorLaurentSeriesAt (zetaGerm(f, c)) 0 (sLocalZLaurentCoeff f c) := by
  obtain ⟨χ, s, hχ⟩ := sLocalZLaurentCoeff_hasLaurentSeries_chart (F := F) (S := S) c
  refine sLocalZLaurentCoeff_hasLaurentSeries_of_meromorphicAt ?_
  simp only [hχ]
  exact (((sLocalIdelicZFunction_meromorphic f χ).meromorphicOn (s + 0) trivial)).comp_analyticAt
    (g := fun t ↦ s + t) (by fun_prop)

/-- An analytic function of order at most one has a reciprocal of order `-1` at its zeros
and of order `0` elsewhere. -/
private theorem sLocalRhoFactor_poles_iff_order_inv {g : ℂ → ℂ} {x : ℂ}
    (hg : AnalyticAt ℂ g x) (h1 : meromorphicOrderAt g x ≤ 1) :
    meromorphicOrderAt (fun u ↦ (g u)⁻¹) x = if g x = 0 then -1 else 0 := by
  change meromorphicOrderAt g⁻¹ x = _
  rw [meromorphicOrderAt_inv]
  split_ifs with h
  · have hne : analyticOrderAt g x ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      push Not
      exact ⟨hg, h⟩
    have hge : (1 : WithTop ℤ) ≤ meromorphicOrderAt g x := by
      rw [hg.meromorphicOrderAt_eq]
      cases hn : analyticOrderAt g x with
      | top => simp
      | coe n =>
        rw [hn] at hne
        have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
        simpa using (show ((1 : ℤ) : WithTop ℤ) ≤ ((n : ℤ) : WithTop ℤ) by exact_mod_cast this)
    rw [le_antisymm h1 hge]
  · rw [hg.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h)]
    simp

/-- The order `-1` is negative. -/
private theorem sLocalRhoFactor_poles_iff_neg_one_lt : (-1 : WithTop ℤ) < 0 :=
  WithTop.coe_lt_coe.mpr (by norm_num)

/-- The reciprocal Gamma function vanishes to order at most one. -/
private theorem sLocalRhoFactor_poles_iff_invGamma_le_one (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x ≤ 1 := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hzero : ∀ {f : ℂ → ℂ} {y : ℂ}, AnalyticAt ℂ f y → f y ≠ 0 →
      meromorphicOrderAt f y = 0 := by
    intro f y hf hy
    rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
      CharP.cast_eq_zero, WithTop.coe_zero]
  have hstep : ∀ y : ℂ, meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y =
      meromorphicOrderAt (id : ℂ → ℂ) y +
        meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) (y + 1) := by
    intro y
    have heq : (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) =
        (id : ℂ → ℂ) * ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) := by
      funext u
      exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one u
    have hcomp : MeromorphicAt ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) y :=
      ((hg (y + 1)).comp (f := fun u : ℂ ↦ u + 1) (by fun_prop)).meromorphicAt
    calc meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y
        = meromorphicOrderAt ((id : ℂ → ℂ) *
            ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1))) y := by rw [← heq]
      _ = _ := by
        rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hcomp,
          meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  by_cases hx : ∃ m : ℕ, x = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hx
    refine le_of_eq ?_
    induction m with
    | zero =>
      rw [hstep, Nat.cast_zero, neg_zero, zero_add, meromorphicOrderAt_id,
        hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
    | succ m ih =>
      rw [hstep, hzero analyticAt_id (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero m))),
        zero_add, show -((m + 1 : ℕ) : ℂ) + 1 = -(m : ℂ) by push_cast; ring]
      exact ih
  · rw [hzero (hg x) (inv_ne_zero (Complex.Gamma_ne_zero fun m hm ↦ hx ⟨m, hm⟩))]
    exact zero_le_one

/-- The Gamma function has order `-1` where its value is the junk value zero, that is at its
poles, and order `0` elsewhere. -/
private theorem sLocalRhoFactor_poles_iff_Gamma_order (x : ℂ) :
    meromorphicOrderAt Complex.Gamma x = if Complex.Gamma x = 0 then -1 else 0 := by
  have h := sLocalRhoFactor_poles_iff_order_inv
    (Complex.differentiable_one_div_Gamma.analyticAt x) (sLocalRhoFactor_poles_iff_invGamma_le_one x)
  simpa only [inv_inv, inv_eq_zero] using h

/-- Order of a product `e * P * Q` with `e` a unit, `Q` analytic and nonvanishing in the closed
left half-plane, and `P` with at most simple poles, all in the closed left half-plane. -/
private theorem sLocalRhoFactor_poles_iff_order_of_eq {f e P Q : ℂ → ℂ} {s : ℂ}
    (hf : f =ᶠ[𝓝[≠] s] fun z ↦ e z * P z * Q z) (he : AnalyticAt ℂ e s) (he0 : e s ≠ 0)
    (hQ : AnalyticAt ℂ Q s) (hQ0 : s.re ≤ 0 → Q s ≠ 0) (hP : MeromorphicAt P s)
    (hPo : meromorphicOrderAt P s = 0 ∨ meromorphicOrderAt P s = -1)
    (hPre : meromorphicOrderAt P s < 0 → s.re ≤ 0) :
    MeromorphicAt f s ∧ (meromorphicOrderAt f s < 0 ↔ meromorphicOrderAt P s < 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt f s = meromorphicOrderAt P s) := by
  have hR : MeromorphicAt (fun z ↦ e z * P z * Q z) s :=
    (he.meromorphicAt.mul hP).mul hQ.meromorphicAt
  have hord : meromorphicOrderAt f s =
      meromorphicOrderAt e s + meromorphicOrderAt P s + meromorphicOrderAt Q s := by
    rw [meromorphicOrderAt_congr hf]
    change meromorphicOrderAt (e * P * Q) s = _
    rw [meromorphicOrderAt_mul (he.meromorphicAt.mul hP) hQ.meromorphicAt,
      meromorphicOrderAt_mul he.meromorphicAt hP]
  have he' : meromorphicOrderAt e s = 0 := by
    rw [he.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr he0)]
    simp
  have hQnn : 0 ≤ meromorphicOrderAt Q s := hQ.meromorphicOrderAt_nonneg
  have hQ' : s.re ≤ 0 → meromorphicOrderAt Q s = 0 := fun hs ↦ by
    rw [hQ.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr (hQ0 hs))]
    simp
  rw [he', zero_add] at hord
  refine ⟨hR.congr hf.symm, ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun hs ↦ by rw [hord, hQ' hs, add_zero]⟩
  · rcases hPo with h0 | h1
    · rw [hord, h0, zero_add] at h
      exact absurd h (not_lt.mpr hQnn)
    · rw [h1]; exact WithTop.coe_lt_coe.mpr (by norm_num)
  · rw [hord, hQ' (hPre h), add_zero]
    exact h

/-- At a real place, the restricted local Tate factor is the epsilon factor times the ratio of
real Gamma factors. Its poles are those of the Gamma factor of the quasi-character, they are
simple and lie in the closed left half-plane, where the factor has no zeros. -/
theorem sLocalRhoFactor_poles_iff_real (χ : PontryaginDual Jₛ) (w : InfinitePlace F)
    (hw : w.IsReal) (s : ℂ) :
    let c := fun z : ℂ ↦ twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) z
    let A := fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))
    let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (c 0))).exists.choose
    MeromorphicAt A s ∧
      (meromorphicOrderAt A s < 0 ↔ ∃ n : ℕ, s = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∧
      (meromorphicOrderAt A s < 0 → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt A s = 0 ∨ meromorphicOrderAt A s = -1) := by
  intro c A p
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, a, ht, hbase⟩ := realPlaceUnitary_shape w hw η
  have hsh := realChart_shape w hw η t a hbase
  have hp : p = (0 + t, a) := by
    have h0 := hsh 0
    rw [← ha 0] at h0
    exact (realLocalEulerParameters w hw _).unique
      (realLocalEulerParameters w hw _).exists.choose_spec h0
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let L : ℂ → ℂ := fun z ↦ (z + t + (a.val : ℂ)) / 2
  let e : ℂ → ℂ := fun z ↦ Complex.I ^ a.val * (Real.pi : ℂ) ^ (-(z + t + (a.val : ℂ)) / 2)
  let P : ℂ → ℂ := fun z ↦ Complex.Gamma (L z)
  let Q : ℂ → ℂ := fun z ↦ (Complex.Gammaℝ (1 - (z + t) + (a.val : ℂ)))⁻¹
  have hstrip : ∀ z : ℂ, z.re ∈ Ioo (0 : ℝ) 1 → A z = e z * P z * Q z := by
    intro z hz
    have h := realTate_ratio_strip w hw η z hz
    have h₁ := realEuler_of_shape w hw _ (z + t) a (hsh z)
    have h₂ := realEuler_of_shape w hw _ (1 - (z + t)) a (realDual_shape w hw _ (z + t) a (hsh z))
    change infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z)) = _
    rw [ha z, h, h₁.1, h₁.2, h₂.1, Complex.Gammaℝ_def]
    simp only [e, P, Q, L, div_eq_mul_inv]
    ring_nf
  have hAm : Meromorphic A := by
    have hT := ((infiniteLocalTateFactor_spec w).1 η).meromorphicOn
    have hA : A = fun z ↦ infiniteLocalTateFactor w (quasiCharacterNormTwist
        ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
          (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w)
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z) :=
      funext fun z ↦ congrArg (infiniteLocalTateFactor w) (ha z)
    intro z
    rw [hA]
    exact hT z (mem_univ z)
  have hL : ∀ z, AnalyticAt ℂ L z := fun z ↦ by fun_prop
  have he : ∀ z, AnalyticAt ℂ e z := fun z ↦ by
    have : Differentiable ℂ e := by fun_prop (disch := exact Or.inl hpi)
    exact this.analyticAt z
  have hQ : ∀ z, AnalyticAt ℂ Q z := fun z ↦
    (Complex.differentiable_Gammaℝ_inv.comp (by fun_prop :
      Differentiable ℂ fun z : ℂ ↦ 1 - (z + t) + (a.val : ℂ))).analyticAt z
  have hPm : ∀ z, MeromorphicAt P z := fun z ↦ (Meromorphic.Gamma (L z)).comp_analyticAt (hL z)
  have hRm : Meromorphic fun z ↦ e z * P z * Q z := fun z ↦
    ((he z).meromorphicAt.mul (hPm z)).mul (hQ z).meromorphicAt
  have hmid : ∀ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (by norm_num [mem_preimage, mem_Ioo]))
  have hf : A =ᶠ[𝓝[≠] s] fun z ↦ e z * P z * Q z :=
    nhdsNE_le_codiscrete s (meromorphic_eq_of_germ hAm hRm (hmid.mono fun z hz ↦ hstrip z hz))
  have hdL : deriv L s ≠ 0 := by
    have hd : HasDerivAt L (1 / 2) s :=
      (((hasDerivAt_id' s).add_const t).add_const (a.val : ℂ)).div_const 2
    rw [hd.deriv]
    norm_num
  have hPo : meromorphicOrderAt P s = if Complex.Gamma (L s) = 0 then -1 else 0 := by
    rw [show P = Complex.Gamma ∘ L from rfl, meromorphicOrderAt_comp_of_deriv_ne_zero (hL s) hdL]
    exact sLocalRhoFactor_poles_iff_Gamma_order (L s)
  have hpole : meromorphicOrderAt P s < 0 ↔ ∃ n : ℕ, s = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ) := by
    rw [hPo, hp]
    split_ifs with h
    · rw [Complex.Gamma_eq_zero_iff] at h
      simp only [sLocalRhoFactor_poles_iff_neg_one_lt, true_iff]
      obtain ⟨m, hm⟩ := h
      refine ⟨m, ?_⟩
      simp only [L] at hm
      push_cast
      linear_combination 2 * hm
    · rw [Complex.Gamma_eq_zero_iff] at h
      simp only [lt_irrefl, false_iff, not_exists]
      intro n hn
      exact h ⟨n, by simp only [L]; rw [hn]; push_cast; ring⟩
  have hPre : meromorphicOrderAt P s < 0 → s.re ≤ 0 := fun h ↦ by
    obtain ⟨n, hn⟩ := hpole.mp h
    rw [hp] at hn
    rw [hn]
    simp only [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.zero_re, ht,
      Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) (2 * n + a.val)]
  have hPo' : meromorphicOrderAt P s = 0 ∨ meromorphicOrderAt P s = -1 := by
    rw [hPo]; split_ifs <;> simp
  have he0 : e s ≠ 0 := mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (by simp [hpi])
  have hQ0 : s.re ≤ 0 → Q s ≠ 0 := fun hs ↦ inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by
    simp [ht]
    linarith [show (0 : ℝ) ≤ (a.val : ℝ) from Nat.cast_nonneg _]))
  obtain ⟨hm, hiff, hre⟩ := sLocalRhoFactor_poles_iff_order_of_eq hf (he s) he0 (hQ s) hQ0 (hPm s)
    hPo' hPre
  exact ⟨hm, hiff.trans hpole, fun h ↦ hPre (hiff.mp h), fun hs ↦ by rw [hre hs]; exact hPo'⟩

/-- At a complex place, the restricted local Tate factor is the epsilon factor times the ratio
of complex Gamma factors. Its poles are those of the Gamma factor of the quasi-character, they
are simple and lie in the closed left half-plane, where the factor has no zeros. -/
private theorem sLocalRhoFactor_poles_iff_complex (χ : PontryaginDual Jₛ) (w : InfinitePlace F)
    (hw : w.IsComplex) (s : ℂ) :
    let c := fun z : ℂ ↦ twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) z
    let A := fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))
    let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w (c 0))).exists.choose
    MeromorphicAt A s ∧
      (meromorphicOrderAt A s < 0 ↔ ∃ n : ℕ, s = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)) ∧
      (meromorphicOrderAt A s < 0 → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt A s = 0 ∨ meromorphicOrderAt A s = -1) := by
  intro c A p
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, r, ht, hbase⟩ := complexPlaceUnitary_shape w hw η
  have hsh := complexChart_shape w hw η t r hbase
  have hp : p = (0 + t, r) := by
    have h0 := hsh 0
    rw [← ha 0] at h0
    exact (complexLocalEulerParameters w hw _).unique
      (complexLocalEulerParameters w hw _).exists.choose_spec h0
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let L : ℂ → ℂ := fun z ↦ z + t + (r.natAbs : ℂ) / 2
  let e : ℂ → ℂ := fun z ↦ Complex.I ^ r.natAbs * (2 * Real.pi : ℂ) ^ (-(z + t + (r.natAbs : ℂ) / 2))
  let P : ℂ → ℂ := fun z ↦ Complex.Gamma (L z)
  let Q : ℂ → ℂ := fun z ↦ 2 * (Complex.Gammaℂ (1 - (z + t) + ((-r).natAbs : ℂ) / 2))⁻¹
  have hstrip : ∀ z : ℂ, z.re ∈ Ioo (0 : ℝ) 1 → A z = e z * P z * Q z := by
    intro z hz
    have h := complexTate_ratio_strip w hw η z hz
    have h₁ := complexEuler_of_shape w hw _ (z + t) r (hsh z)
    have h₂ := complexEuler_of_shape w hw _ (1 - (z + t)) (-r)
      (complexDual_shape w hw _ (z + t) r (hsh z))
    change infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z)) = _
    rw [ha z, h, h₁.1, h₁.2, h₂.1, Complex.Gammaℂ_def (z + t + (r.natAbs : ℂ) / 2)]
    simp only [e, P, Q, L, div_eq_mul_inv]
    ring
  have hAm : Meromorphic A := by
    have hT := ((infiniteLocalTateFactor_spec w).1 η).meromorphicOn
    have hA : A = fun z ↦ infiniteLocalTateFactor w (quasiCharacterNormTwist
        ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
          (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w)
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z) :=
      funext fun z ↦ congrArg (infiniteLocalTateFactor w) (ha z)
    intro z
    rw [hA]
    exact hT z (mem_univ z)
  have hL : ∀ z, AnalyticAt ℂ L z := fun z ↦ by fun_prop
  have he : ∀ z, AnalyticAt ℂ e z := fun z ↦ by
    have : Differentiable ℂ e := by fun_prop (disch := exact Or.inl h2pi)
    exact this.analyticAt z
  have hQ : ∀ z, AnalyticAt ℂ Q z := fun z ↦
    ((Complex.differentiable_Gammaℂ_inv.comp (by fun_prop :
      Differentiable ℂ fun z : ℂ ↦ 1 - (z + t) + ((-r).natAbs : ℂ) / 2)).const_mul 2).analyticAt z
  have hPm : ∀ z, MeromorphicAt P z := fun z ↦ (Meromorphic.Gamma (L z)).comp_analyticAt (hL z)
  have hRm : Meromorphic fun z ↦ e z * P z * Q z := fun z ↦
    ((he z).meromorphicAt.mul (hPm z)).mul (hQ z).meromorphicAt
  have hmid : ∀ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), z.re ∈ Ioo (0 : ℝ) 1 :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      (by norm_num [mem_preimage, mem_Ioo]))
  have hf : A =ᶠ[𝓝[≠] s] fun z ↦ e z * P z * Q z :=
    nhdsNE_le_codiscrete s (meromorphic_eq_of_germ hAm hRm (hmid.mono fun z hz ↦ hstrip z hz))
  have hdL : deriv L s ≠ 0 := by
    have hd : HasDerivAt L 1 s := ((hasDerivAt_id' s).add_const t).add_const ((r.natAbs : ℂ) / 2)
    rw [hd.deriv]
    exact one_ne_zero
  have hPo : meromorphicOrderAt P s = if Complex.Gamma (L s) = 0 then -1 else 0 := by
    rw [show P = Complex.Gamma ∘ L from rfl, meromorphicOrderAt_comp_of_deriv_ne_zero (hL s) hdL]
    exact sLocalRhoFactor_poles_iff_Gamma_order (L s)
  have hpole : meromorphicOrderAt P s < 0 ↔ ∃ n : ℕ, s = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ) := by
    rw [hPo, hp]
    split_ifs with h
    · rw [Complex.Gamma_eq_zero_iff] at h
      simp only [sLocalRhoFactor_poles_iff_neg_one_lt, true_iff]
      obtain ⟨m, hm⟩ := h
      refine ⟨m, ?_⟩
      simp only [L] at hm
      linear_combination hm
    · rw [Complex.Gamma_eq_zero_iff] at h
      simp only [lt_irrefl, false_iff, not_exists]
      intro n hn
      exact h ⟨n, by simp only [L]; rw [hn]; ring⟩
  have hPre : meromorphicOrderAt P s < 0 → s.re ≤ 0 := fun h ↦ by
    obtain ⟨n, hn⟩ := hpole.mp h
    rw [hp] at hn
    rw [hn]
    simp only [Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.zero_re, ht,
      Complex.natCast_re, Complex.div_ofNat_re]
    linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) r.natAbs]
  have hPo' : meromorphicOrderAt P s = 0 ∨ meromorphicOrderAt P s = -1 := by
    rw [hPo]; split_ifs <;> simp
  have he0 : e s ≠ 0 := mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) (by simp [h2pi])
  have hQ0 : s.re ≤ 0 → Q s ≠ 0 := fun hs ↦ by
    refine mul_ne_zero two_ne_zero (inv_ne_zero ?_)
    rw [Complex.Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero (by simp [h2pi])) (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, ht, Complex.div_ofNat_re,
      Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) (-r).natAbs]
  obtain ⟨hm, hiff, hre⟩ := sLocalRhoFactor_poles_iff_order_of_eq hf (he s) he0 (hQ s) hQ0 (hPm s)
    hPo' hPre
  exact ⟨hm, hiff.trans hpole, fun h ↦ hPre (hiff.mp h), fun hs ↦ by rw [hre hs]; exact hPo'⟩

/-- At a finite place, the restricted local Tate factor is the epsilon factor times the ratio of
the local Euler factors. It has a pole exactly when the restricted character is unramified and
its Euler factor has a pole, which is simple and lies on the imaginary axis; in the closed left
half-plane the factor has no zeros. -/
theorem sLocalRhoFactor_poles_iff_finite (χ : PontryaginDual Jₛ) (v : S) :
    let c := fun z : ℂ ↦ twistₛ ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) z
    let B := fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))
    let ψ := sLocalFiniteRestriction v (c 0)
    ∃ π : (v.val.adicCompletion F)ˣ, ‖π.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ ∧ ∀ s : ℂ,
      MeromorphicAt B s ∧
      (meromorphicOrderAt B s < 0 ↔
        (∀ u : (v.val.adicCompletionIntegers F)ˣ,
          ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) ∧
        ψ π * ((‖π.val‖ : ℝ) : ℂ) ^ s = 1) ∧
      (meromorphicOrderAt B s < 0 → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt B s = 0 ∨ meromorphicOrderAt B s = -1) := by
  intro c B ψ
  obtain ⟨η, ha, -⟩ := sLocalFinite_charts χ v
  let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπn : ‖π.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val _ hπ.choose_spec
  refine ⟨π, hπn, fun s ↦ ?_⟩
  let ch : PontryaginDual (v.val.adicCompletion F)ˣ → ℂ → QuasiCharacter (v.val.adicCompletion F)ˣ :=
    fun ξ z ↦ quasiCharacterNormTwist
      (Units.map nnNormHom.toMonoidHom : (v.val.adicCompletion F)ˣ →* ℝ≥0ˣ)
      (continuous_finiteLocalModule v.val)
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ξ) z
  have hval : ∀ ξ z x, ch ξ z x = (ξ x : ℂ) * ((‖x.val‖ : ℝ) : ℂ) ^ z := fun _ _ _ ↦ rfl
  have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hb0 : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
  have hb1 : ‖π.val‖ < 1 := by rw [hπn]; exact inv_lt_one_of_one_lt₀ hq
  have hnorm : ∀ ξ z, ‖ch ξ z π‖ = ‖π.val‖ ^ z.re := fun ξ z ↦ by
    rw [hval, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb0]
  have hunit : ∀ ξ z (u : (v.val.adicCompletionIntegers F)ˣ),
      ch ξ z (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) =
        (ξ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) : ℂ) := by
    intro ξ z u
    rw [hval, finite_integer_unit_norm v.val u, Complex.ofReal_one, Complex.one_cpow, mul_one]
  let U : PontryaginDual (v.val.adicCompletion F)ˣ → Prop := fun ξ ↦
    ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      (ξ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) : ℂ) = 1
  have hEU : ∀ ξ z, U ξ → finiteLocalEulerFactor v.val (ch ξ z) = (1 - ch ξ z π)⁻¹ := by
    intro ξ z hU
    have h : ∀ u : (v.val.adicCompletionIntegers F)ˣ,
        ch ξ z (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 :=
      fun u ↦ (hunit ξ z u).trans (hU u)
    simp only [finiteLocalEulerFactor, h, implies_true, ite_true]
    rfl
  have hEN : ∀ ξ z, ¬ U ξ → finiteLocalEulerFactor v.val (ch ξ z) = 1 := by
    intro ξ z hU
    have h : ¬ ∀ u : (v.val.adicCompletionIntegers F)ˣ,
        ch ξ z (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 :=
      fun h ↦ hU fun u ↦ (hunit ξ z u).symm.trans (h u)
    simp only [finiteLocalEulerFactor, h, ite_false]
  have hB : B = fun z ↦ finiteLocalTateFactor v.val (ch η z) :=
    funext fun z ↦ congrArg (finiteLocalTateFactor v.val) (ha z)
  have hψ : ψ = ch η 0 := ha 0
  let g : PontryaginDual (v.val.adicCompletion F)ˣ → ℂ → ℂ := fun ξ z ↦ 1 - ch ξ z π
  have hg : ∀ ξ z, HasDerivAt (g ξ) (ch ξ z π * (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)) z :=
    fun ξ z ↦ finite_den_hasDerivAt v.val ξ π hπn z
  have hga : ∀ ξ z, AnalyticAt ℂ (g ξ) z := fun ξ z ↦
    (show Differentiable ℂ (g ξ) from fun y ↦ (hg ξ y).differentiableAt).analyticAt z
  let e : ℂ → ℂ := fun z ↦ finiteLocalEpsilonFactor v.val (ch η z)
  let P : ℂ → ℂ := fun z ↦ finiteLocalEulerFactor v.val (ch η z)
  let Q : ℂ → ℂ := fun z ↦ (finiteLocalEulerFactor v.val (ch η⁻¹ (1 - z)))⁻¹
  have hgerm : ∀ᶠ z in 𝓝[≠] (1 / 2 : ℂ), B z = e z * P z * Q z := by
    filter_upwards [finiteTate_ratio_germ v.val η] with z hz
    rw [hB]
    refine hz.trans ?_
    rw [dual_norm_chart (Units.map nnNormHom.toMonoidHom : (v.val.adicCompletion F)ˣ →* ℝ≥0ˣ)
      (continuous_finiteLocalModule v.val) η z]
    simp only [e, P, Q, ch, div_eq_mul_inv, mul_assoc]
    rfl
  have hBm : Meromorphic B := by
    have hT := ((finiteLocalTateFactor_spec v.val).1 η).meromorphicOn
    intro z
    rw [hB]
    exact hT z (mem_univ z)
  have he : ∀ z, AnalyticAt ℂ e z := fun z ↦ finiteLocalEpsilonFactor_entire v.val η z trivial
  have hPm : ∀ z, MeromorphicAt P z := by
    by_cases hU : U η
    · have : P = fun z ↦ (g η z)⁻¹ := funext fun z ↦ hEU η z hU
      intro z; rw [this]; exact (hga η z).meromorphicAt.inv
    · have : P = fun _ ↦ 1 := funext fun z ↦ hEN η z hU
      intro z; rw [this]; exact MeromorphicAt.const _ _
  have hQ : ∀ z, AnalyticAt ℂ Q z := by
    by_cases hU : U η⁻¹
    · have : Q = fun z ↦ g η⁻¹ (1 - z) := funext fun z ↦ by
        simp only [Q]; rw [hEU η⁻¹ (1 - z) hU, inv_inv]
      intro z; rw [this]; exact (hga η⁻¹ (1 - z)).comp (by fun_prop)
    · have : Q = fun _ ↦ 1 := funext fun z ↦ by simp only [Q]; rw [hEN η⁻¹ (1 - z) hU, inv_one]
      intro z; rw [this]; exact analyticAt_const
  have hRm : Meromorphic fun z ↦ e z * P z * Q z := fun z ↦
    ((he z).meromorphicAt.mul (hPm z)).mul (hQ z).meromorphicAt
  have hf : B =ᶠ[𝓝[≠] s] fun z ↦ e z * P z * Q z :=
    nhdsNE_le_codiscrete s (meromorphic_eq_of_germ hBm hRm hgerm)
  have he0 : e s ≠ 0 := by
    have h := sLocalEpsilonFactor_ne_zero (S := S) (c s)
    rw [sLocalEpsilonFactor] at h
    have h' := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h) v (Finset.mem_univ v)
    rwa [ha s] at h'
  have hQ0 : s.re ≤ 0 → Q s ≠ 0 := fun hs ↦ by
    by_cases hU : U η⁻¹
    · simp only [Q]
      rw [hEU η⁻¹ (1 - s) hU, inv_inv, sub_ne_zero]
      intro h1
      have := hnorm η⁻¹ (1 - s)
      rw [← h1, norm_one, Complex.sub_re, Complex.one_re] at this
      have hlt : ‖π.val‖ ^ (1 - s.re) < 1 := Real.rpow_lt_one hb0.le hb1 (by linarith)
      linarith
    · simp only [Q]; rw [hEN η⁻¹ (1 - s) hU, inv_one]; exact one_ne_zero
  have hU0 : (∀ u : (v.val.adicCompletionIntegers F)ˣ,
      ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) ↔ U η := by
    rw [hψ]; exact forall_congr' fun u ↦ by rw [hunit]
  have hψπ : ψ π * ((‖π.val‖ : ℝ) : ℂ) ^ s = ch η s π := by
    rw [hψ, hval, hval, Complex.cpow_zero, mul_one]
  have hP : (meromorphicOrderAt P s = 0 ∨ meromorphicOrderAt P s = -1) ∧
      (meromorphicOrderAt P s < 0 ↔ U η ∧ ch η s π = 1) := by
    by_cases hU : U η
    · have hPg : P = fun z ↦ (g η z)⁻¹ := funext fun z ↦ hEU η z hU
      have h1 : meromorphicOrderAt (g η) s ≤ 1 := by
        by_cases h0 : g η s = 0
        · rw [(hga η s).meromorphicOrderAt_eq,
            (hga η s).analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 ?_]
          · simp
          · rw [(hg η s).deriv]
            have h1 : ch η s π = 1 := (sub_eq_zero.mp h0).symm
            rw [h1, one_mul]
            exact Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
        · rw [(hga η s).meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr h0)]
          simp
      have ho := sLocalRhoFactor_poles_iff_order_inv (hga η s) h1
      rw [hPg, ho]
      by_cases h0 : g η s = 0
      · have h1 : ch η s π = 1 := (sub_eq_zero.mp h0).symm
        simp [h0, hU, h1, sLocalRhoFactor_poles_iff_neg_one_lt]
      · have h1 : ch η s π ≠ 1 := fun h ↦ h0 (sub_eq_zero.mpr h.symm)
        simp [h0, h1]
    · have hP1 : P = fun _ ↦ 1 := funext fun z ↦ hEN η z hU
      have ho : meromorphicOrderAt P s = 0 := by
        rw [hP1, meromorphicOrderAt_const]
        simp
      simp [ho, hU]
  have hPre : meromorphicOrderAt P s < 0 → s.re ≤ 0 := fun h ↦ by
    obtain ⟨-, h1⟩ := hP.2.mp h
    by_contra hs
    push Not at hs
    have := hnorm η s
    rw [h1, norm_one] at this
    have hlt : ‖π.val‖ ^ s.re < 1 := Real.rpow_lt_one hb0.le hb1 hs
    linarith
  obtain ⟨hm, hiff, hre⟩ := sLocalRhoFactor_poles_iff_order_of_eq hf (he s) he0 (hQ s) hQ0 (hPm s)
    hP.1 hPre
  refine ⟨hm, hiff.trans (hP.2.trans ?_), fun h ↦ hPre (hiff.mp h), fun hs ↦ by
    rw [hre hs]; exact hP.1⟩
  rw [hU0, hψπ]

/-- At a finite place, a unitary character is unramified with value `q^{s}` at a normalized
uniformizer exactly when it is the norm to the power `i t` for a unique `t` in one period and `s`
lies on the corresponding lattice of the imaginary axis. -/
theorem sLocalRhoFactor_poles_iff_finite_explicit (v : HeightOneSpectrum (𝓞 F))
    (ψ : QuasiCharacter (v.adicCompletion F)ˣ) (hψ : ∀ x, ‖ψ x‖ = 1)
    (π : (v.adicCompletion F)ˣ) (hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹) (s : ℂ) :
    ((∀ u : (v.adicCompletionIntegers F)ˣ,
        ψ (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1) ∧
      ψ π * ((‖π.val‖ : ℝ) : ℂ) ^ s = 1) ↔
    ∃ (m : ℤ) (t : ℝ),
      let period := 2 * Real.pi / Real.log (v.asIdeal.absNorm : ℝ)
      t ∈ Ico 0 period ∧
        (∀ x : (v.adicCompletion F)ˣ,
          ψ x = ((‖(x : v.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
        s = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  set L := Real.log (v.asIdeal.absNorm : ℝ) with hL
  have hL0 : 0 < L := Real.log_pos hq
  set T := 2 * Real.pi / L with hT
  have hT0 : 0 < T := div_pos (by positivity) hL0
  have hTL : (L : ℂ) * (T : ℂ) = 2 * Real.pi := by
    rw [hT]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL0.ne']
  have hb0 : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
  have hcp : ∀ (k : ℤ) (w : ℂ), ((‖π.val‖ ^ k : ℝ) : ℂ) ^ w = Complex.exp (-(k : ℂ) * L * w) := by
    intro k w
    have hpos : 0 < ‖π.val‖ ^ k := zpow_pos hb0 k
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, Real.log_zpow, hπ, Real.log_inv, ← hL]
    push_cast
    ring_nf
  have hcp1 : ∀ w : ℂ, ((‖π.val‖ : ℝ) : ℂ) ^ w = Complex.exp (-L * w) := fun w ↦ by
    simpa using hcp 1 w
  obtain ⟨e, heπ, heι⟩ := finitePlace_unitDecomposition v π hπ
  have hdec : ∀ x : (v.adicCompletion F)ˣ, x = π ^ (e x).1.toAdd *
      Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (e x).2 := by
    intro x
    apply e.injective
    rw [map_mul, map_zpow, heπ, heι]
    exact Prod.ext (by change (e x).1.toAdd = (e x).1.toAdd * 1 + 0; simp) (by simp)
  have hnx : ∀ x : (v.adicCompletion F)ˣ, ‖x.val‖ = ‖π.val‖ ^ (e x).1.toAdd := by
    intro x
    conv_lhs => rw [hdec x]
    rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
      finite_integer_unit_norm v, mul_one]
  constructor
  · rintro ⟨hU, hs⟩
    rw [hcp1] at hs
    have hψπ : ψ π = Complex.exp (L * s) := by
      have h2 : Complex.exp (-L * s) * Complex.exp (L * s) = 1 := by
        rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
      calc ψ π = ψ π * (Complex.exp (-L * s) * Complex.exp (L * s)) := by rw [h2, mul_one]
        _ = Complex.exp (L * s) := by rw [← mul_assoc, hs, one_mul]
    have hre : s.re = 0 := by
      have h := hψ π
      rw [hψπ, Complex.norm_exp] at h
      have : (L * s : ℂ).re = 0 := by simpa using Real.exp_eq_one_iff _ |>.mp h
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at this
      exact (mul_eq_zero.mp this).resolve_left hL0.ne'
    have hsI : s = (s.im : ℂ) * Complex.I := Complex.ext (by simp [hre]) (by simp)
    refine ⟨⌈s.im / T⌉, ⌈s.im / T⌉ * T - s.im, ⟨?_, ?_⟩, ?_, ?_⟩
    · have := Int.le_ceil (s.im / T)
      rw [div_le_iff₀ hT0] at this
      linarith
    · have := Int.ceil_lt_add_one (s.im / T)
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hT0] at this
      linarith
    · intro x
      rw [hnx x, hcp, show ψ x = ψ π ^ (e x).1.toAdd by
        conv_lhs => rw [hdec x]
        rw [map_mul, map_zpow, hU, mul_one], hψπ, ← Complex.exp_int_mul,
        Complex.exp_eq_exp_iff_exists_int]
      refine ⟨(e x).1.toAdd * ⌈s.im / T⌉, ?_⟩
      push_cast
      linear_combination ((e x).1.toAdd : ℂ) * L * hsI + ((e x).1.toAdd : ℂ) * (⌈s.im / T⌉ : ℂ) *
        Complex.I * hTL
    · rw [show ((⌈s.im / T⌉ : ℝ) * T - (⌈s.im / T⌉ * T - s.im) : ℝ) = s.im by ring]
      exact hsI
  · rintro ⟨m, t, -, hψt, hs⟩
    refine ⟨fun u ↦ ?_, ?_⟩
    · rw [hψt, finite_integer_unit_norm v, Complex.ofReal_one, Complex.one_cpow]
    · rw [hψt, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hb0.ne'), hcp1, hs]
      have : -(L : ℂ) * ((t : ℂ) * Complex.I + (((m : ℝ) * T - t : ℝ) : ℂ) *
          Complex.I) = (-m : ℤ) * (2 * Real.pi * Complex.I) := by
        push_cast
        linear_combination (-(m : ℂ) * Complex.I) * hTL
      rw [this, Complex.exp_int_mul_two_pi_mul_I]

open Classical in
/-- The order of the correcting factor is the sum of the orders of its local factors. Every pole
of a local factor lies in the closed left half-plane, and there each local factor has order `0`
or `-1`, so the order of the product counts the local poles. -/
private theorem sLocalRhoFactor_poles_iff_count (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := fun z : ℂ ↦ twistₛ χ₀ z
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (c z)
    let arch := Finset.univ.filter (fun w : InfinitePlace F ↦
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))) s < 0)
    let fin := Finset.univ.filter (fun v : S ↦
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))) s < 0)
    (meromorphicOrderAt ρ s < 0 ∨ 0 < arch.card + fin.card → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt ρ s = ((-((arch.card + fin.card : ℕ) : ℤ) : ℤ) : WithTop ℤ)) ∧
      (meromorphicOrderAt ρ s < 0 ↔
        (∃ w : InfinitePlace F, meromorphicOrderAt
          (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))) s < 0) ∨
        ∃ v : S, meromorphicOrderAt
          (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))) s < 0) := by
  intro χ₀ c ρ arch fin
  let A := fun (w : InfinitePlace F) (z : ℂ) ↦
    infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))
  let B := fun (v : S) (z : ℂ) ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))
  have hA : ∀ w, MeromorphicAt (A w) s ∧ (meromorphicOrderAt (A w) s < 0 → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt (A w) s = 0 ∨ meromorphicOrderAt (A w) s = -1) := by
    intro w
    by_cases hw : w.IsReal
    · obtain ⟨h1, -, h3, h4⟩ := sLocalRhoFactor_poles_iff_real χ w hw s
      exact ⟨h1, h3, h4⟩
    · obtain ⟨h1, -, h3, h4⟩ := sLocalRhoFactor_poles_iff_complex χ w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) s
      exact ⟨h1, h3, h4⟩
  have hB : ∀ v, MeromorphicAt (B v) s ∧ (meromorphicOrderAt (B v) s < 0 → s.re ≤ 0) ∧
      (s.re ≤ 0 → meromorphicOrderAt (B v) s = 0 ∨ meromorphicOrderAt (B v) s = -1) := by
    intro v
    obtain ⟨π, -, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
    obtain ⟨h1, -, h3, h4⟩ := h s
    exact ⟨h1, h3, h4⟩
  have hprodA : MeromorphicAt (fun z ↦ ∏ w, A w z) s := by
    have h := MeromorphicAt.prod (s := Finset.univ) (fun w _ ↦ (hA w).1)
    rwa [Finset.prod_fn] at h
  have hprodB : MeromorphicAt (fun z ↦ ∏ v, B v z) s := by
    have h := MeromorphicAt.prod (s := Finset.univ) (fun v _ ↦ (hB v).1)
    rwa [Finset.prod_fn] at h
  have hord : meromorphicOrderAt ρ s =
      (∑ w, meromorphicOrderAt (A w) s) + ∑ v, meromorphicOrderAt (B v) s := by
    change meromorphicOrderAt ((fun z ↦ ∏ w, A w z) * fun z ↦ ∏ v, B v z) s = _
    rw [meromorphicOrderAt_mul hprodA hprodB, meromorphicOrderAt_fun_prod (fun w _ ↦ (hA w).1),
      meromorphicOrderAt_fun_prod (fun v _ ↦ (hB v).1)]
  have hreg : meromorphicOrderAt ρ s < 0 ∨ 0 < arch.card + fin.card → s.re ≤ 0 := by
    intro h
    by_contra hs
    push Not at hs
    have hA0 : ∀ w, 0 ≤ meromorphicOrderAt (A w) s := fun w ↦
      not_lt.mp fun h' ↦ absurd ((hA w).2.1 h') (not_le.mpr hs)
    have hB0 : ∀ v, 0 ≤ meromorphicOrderAt (B v) s := fun v ↦
      not_lt.mp fun h' ↦ absurd ((hB v).2.1 h') (not_le.mpr hs)
    rcases h with h | h
    · rw [hord] at h
      exact absurd h (not_lt.mpr (add_nonneg (Finset.sum_nonneg fun w _ ↦ hA0 w)
        (Finset.sum_nonneg fun v _ ↦ hB0 v)))
    · have harch : arch = ∅ := Finset.filter_eq_empty_iff.mpr fun w _ ↦ not_lt.mpr (hA0 w)
      have hfin : fin = ∅ := Finset.filter_eq_empty_iff.mpr fun v _ ↦ not_lt.mpr (hB0 v)
      rw [harch, hfin] at h
      simp at h
  have hcount : s.re ≤ 0 →
      meromorphicOrderAt ρ s = ((-((arch.card + fin.card : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
    intro hs
    have hAv : ∀ w, meromorphicOrderAt (A w) s = ((if w ∈ arch then -1 else 0 : ℤ) : WithTop ℤ) := by
      intro w
      rcases (hA w).2.2 hs with h | h
      · have hw : w ∉ arch := by simp [arch, A, h]
        rw [h]
        simp [hw]
      · have hw : w ∈ arch := by
          simp only [arch, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h ▸ (by decide : ((-1 : ℤ) : WithTop ℤ) < 0)
        rw [h]
        simp [hw]
    have hBv : ∀ v, meromorphicOrderAt (B v) s = ((if v ∈ fin then -1 else 0 : ℤ) : WithTop ℤ) := by
      intro v
      rcases (hB v).2.2 hs with h | h
      · have hv : v ∉ fin := by simp [fin, B, h]
        rw [h]
        simp [hv]
      · have hv : v ∈ fin := by
          simp only [fin, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h ▸ (by decide : ((-1 : ℤ) : WithTop ℤ) < 0)
        rw [h]
        simp [hv]
    rw [hord, Finset.sum_congr rfl fun w _ ↦ hAv w, Finset.sum_congr rfl fun v _ ↦ hBv v,
      ← WithTop.coe_sum, ← WithTop.coe_sum, ← WithTop.coe_add]
    congr 1
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_neg, nsmul_eq_mul,
      mul_one]
    push_cast
    ring
  refine ⟨hreg, hcount, fun h ↦ ?_, ?_⟩
  · have hs := hreg (Or.inl h)
    rw [hcount hs] at h
    have hpos : 0 < arch.card + fin.card := by
      by_contra h0
      have h0' : arch.card + fin.card = 0 := by omega
      rw [h0'] at h
      exact absurd h (lt_irrefl _)
    rcases Nat.eq_zero_or_pos arch.card with h1 | h1
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (show 0 < fin.card by omega)
      exact Or.inr ⟨v, (Finset.mem_filter.mp hv).2⟩
    · obtain ⟨w, hw⟩ := Finset.card_pos.mp h1
      exact Or.inl ⟨w, (Finset.mem_filter.mp hw).2⟩
  · rintro (⟨w, hw⟩ | ⟨v, hv⟩)
    · rw [hcount ((hA w).2.1 hw)]
      have hc : 0 < arch.card :=
        Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
      exact_mod_cast (show -(((arch.card + fin.card : ℕ)) : ℤ) < 0 by omega)
    · rw [hcount ((hB v).2.1 hv)]
      have hc : 0 < fin.card :=
        Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
      exact_mod_cast (show -(((arch.card + fin.card : ℕ)) : ℤ) < 0 by omega)

-- TODO(paper-gap): In Lemma 7.1.2.2(1), the complex-place shift has the wrong sign.
-- The uniqueness of the contributing place stated on p. 317 fails when poles coincide.

/-- Paper: Lemma 7.1.2.2, p. 316.
The poles of the S-local correcting factor are the union of the two archimedean families
and the periodic lattices at unramified finite places.
Deviation: As in §3.3, the complex-place abscissae start at minus half the absolute angular
weight. The union allows more than one place to contribute to the same pole. -/
theorem sLocalRhoFactor_poles_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := twistₛ χ₀ 0
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (twistₛ χ₀ z)) s < 0 ↔
      (∃ (w : InfinitePlace F) (hw : w.IsReal) (n : ℕ),
        let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∨
      (∃ (w : InfinitePlace F) (hw : w.IsComplex) (n : ℕ),
        let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)) ∨
      (∃ (v : S) (m : ℤ) (t : ℝ),
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ,
            sLocalFiniteRestriction v c x =
              ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          s = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I) := by
  intro χ₀ c
  have hψ : ∀ (v : S) (x : (v.val.adicCompletion F)ˣ), ‖sLocalFiniteRestriction v c x‖ = 1 := by
    intro v x
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  refine (sLocalRhoFactor_poles_iff_count χ s).2.2.trans ?_
  rw [← or_assoc]
  refine or_congr ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    by_cases hr : w.IsReal
    · exact Or.inl ⟨w, hr, (sLocalRhoFactor_poles_iff_real χ w hr s).2.1.mp hw⟩
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hr
      exact Or.inr ⟨w, hc, (sLocalRhoFactor_poles_iff_complex χ w hc s).2.1.mp hw⟩
  · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact ⟨w, (sLocalRhoFactor_poles_iff_real χ w hw s).2.1.mpr h⟩
    · exact ⟨w, (sLocalRhoFactor_poles_iff_complex χ w hw s).2.1.mpr h⟩
  · rintro ⟨v, hv⟩
    obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
    obtain ⟨m, t, ht⟩ :=
      (sLocalRhoFactor_poles_iff_finite_explicit v.val _ (hψ v) π hπ s).mp ((h s).2.1.mp hv)
    exact ⟨v, m, t, ht⟩
  · rintro ⟨v, m, t, ht⟩
    obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
    exact ⟨v, (h s).2.1.mpr
      ((sLocalRhoFactor_poles_iff_finite_explicit v.val _ (hψ v) π hπ s).mpr ⟨m, t, ht⟩)⟩

open Classical in
/-- Paper: Lemma 7.1.2.2, p. 317.
At a pole of the correcting factor, its order counts all the places where the
restricted local Tate factor has a pole.
Deviation: Each local pole is simple. The count includes coincident poles. -/
theorem sLocalRhoFactor_orderAt_pole (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := fun z : ℂ ↦ twistₛ χ₀ z
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (c z)
    let arch := Finset.univ.filter (fun w : InfinitePlace F ↦
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))) s < 0)
    let fin := Finset.univ.filter (fun v : S ↦
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))) s < 0)
    meromorphicOrderAt ρ s < 0 →
      meromorphicOrderAt ρ s = ((-((arch.card + fin.card : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  intro χ₀ c ρ arch fin h
  have H := sLocalRhoFactor_poles_iff_count χ s
  exact H.2.1 (H.1 (Or.inl h))

end SLocal

-- TODO(paper-gap): Theorem 7.1.2.3 omits the real Gaussian's constant term, uses
-- a_{k-1} in place of a_{-k}, and counts coincident poles once per contributing place.
-- The strict cutoff can omit higher-order poles on Re(s) = -A, where the claimed
-- L¹ remainder constant is undefined. The bounded-set version has the same defects.
-- TODO(paper-gap): Footnote 1, p. 321, flags the missing growth control on the
-- horizontal heights for the appeal to Theorem B.3.2.1.

section Counterexample

local notation "Jℚ" => SIdeleQuotient ℚ ∅
local notation "Jℚ₁" => MonoidHom.ker (sIdeleQuotientNorm ℚ ∅)
local notation "μℚ₁" => sLocalNormOneQuotientMeasure ℚ ∅

local instance instMeasurableNormOneRatSec1a : MeasurableSpace Jℚ₁ := borel _
local instance instHaarNormOneRatSec1a : Measure.IsHaarMeasure μℚ₁ :=
  (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1

/-- At the rational archimedean stage, the real Gaussian evaluated on an idele
depends only on its idelic norm. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_gaussian :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      ∀ g : (SAdeleRing ℚ ∅)ˣ, f (Multiplicative.ofAdd g.val) =
        (Real.exp (-(((sIdeleNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ) := by
  let w := Rat.infinitePlace
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : SAdeleRing ℚ ∅ ≃ₜ ℝ := ((Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans j.toHomeomorph
  let a : SAdeleRing ℚ ∅ ≃+ ℝ :=
    { e.toEquiv with
      map_add' := fun x y ↦
        map_add (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
          (x.1 w) (y.1 w) }
  let E : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative ℝ :=
    { a.toMultiplicative with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) :=
    e.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  obtain ⟨b, hb⟩ := exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  refine ⟨⟨(T b).val ∘ E, schwartzBruhat_mem_comp_equiv E (T b).property⟩, fun g ↦ ?_⟩
  change T b (Multiplicative.ofAdd (j (g.val.1 w))) = _
  rw [hT, hb, neg_one_mul, j.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace))]
  have hn : ((sIdeleNorm ℚ ∅ g).val : ℝ) = ‖g.val.1 w‖ := by
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  rw [hn]

/-- Both rational unit translates have the same Gaussian value. Averaging the
result over norm-one classes multiplies it by their total Haar mass. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_eval
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ g : (SAdeleRing ℚ ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ)) (g : Jℚ) :
    sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f g =
      ((μℚ₁).real univ : ℂ) * (2 * (Real.exp (-(((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ)) := by
  let φ (t : ℝ≥0ˣ) : ℂ := Real.exp (-((t.val : ℝ) ^ 2))
  have hclass (x : Jℚ) : sLocalAdelicThetaOnClasses ℚ ∅ f x = 2 * φ (sIdeleQuotientNorm ℚ ∅ x) := by
    refine Quotient.inductionOn x fun y ↦ ?_
    refine (sLocalAdelicThetaOnClasses_mk ℚ ∅ f y).trans ((sLocalAdelicTheta_apply ℚ ∅ f y).trans ?_)
    let U := (((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ
    have hcard : Nat.card U = 2 := by
      dsimp only [U]
      rw [Finset.coe_empty, integer_empty]
      let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
      let units := Units.mapEquiv (e.toRingEquiv.trans Rat.ringOfIntegersEquiv).toMulEquiv
      rw [Nat.card_congr units.toEquiv, Nat.card_eq_fintype_card, Fintype.card_units_int]
    calc
      _ = ∑' _ : U, φ (sIdeleNorm ℚ ∅ y) := by
        apply tsum_congr
        intro u
        let d := Units.map
          ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype).toMonoidHom
          (Units.map (integralAdeleDiagonal ℚ ∅).toMonoidHom u)
        have hu : sIdeleNorm ℚ ∅ d = 1 := (sIdeleNorm_spec ℚ ∅).2 ⟨u, rfl⟩
        exact (hf (d * y)).trans (congrArg φ (by rw [map_mul, hu, one_mul]))
      _ = _ := by
        change (∑' _ : U, φ (sIdeleNorm ℚ ∅ y)) = 2 * φ (sIdeleNorm ℚ ∅ y)
        rw [tsum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  change (∫ h : Jℚ₁, sLocalAdelicThetaOnClasses ℚ ∅ f (g * h.val) *
    ((1 : PontryaginDual Jℚ₁) h : ℂ) ∂μℚ₁) = _
  have hker (h : Jℚ₁) : sIdeleQuotientNorm ℚ ∅ h.val = 1 := h.property
  simp only [hclass, map_mul, hker, mul_one,
    PontryaginDual.one_apply, Circle.coe_one, integral_const, Complex.real_smul, φ]

/-- A radial Gaussian profile with nonzero mass has a nonzero limit along the
norm, whereas a square-root bound would force its limit to be zero. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit
    {X : Type*} (r : X → ℝ) (hr : Ioi 0 ⊆ range r) (c : ℂ) (hc : c ≠ 0)
    (θ : X → ℂ) (hθ : ∀ x, θ x = c * (2 * (Real.exp (-(r x ^ 2)) : ℂ))) :
    ¬ Asymptotics.IsBigO (comap r (𝓝[>] (0 : ℝ))) θ (fun x ↦ r x ^ (1 / 2 : ℝ)) := by
  let l := comap r (𝓝[>] (0 : ℝ))
  have : l.NeBot := (inferInstance : (𝓝[>] (0 : ℝ)).NeBot).comap_of_range_mem
    (mem_of_superset self_mem_nhdsWithin hr)
  have hr₀ : Tendsto r l (𝓝 0) := tendsto_comap.mono_right nhdsWithin_le_nhds
  have hroot : Tendsto (fun x ↦ r x ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hr₀
  have hlim : Tendsto θ l (𝓝 (c * 2)) := by
    rw [funext hθ]
    have h : Continuous (fun t : ℝ ↦ c * (2 * (Real.exp (-(t ^ 2)) : ℂ))) := by fun_prop
    simpa [Function.comp_def] using (h.tendsto 0).comp hr₀
  exact fun hO ↦ (mul_ne_zero hc (by norm_num)) (tendsto_nhds_unique hlim (hO.trans_tendsto hroot))

/-- Paper: Theorem 7.1.2.3, p. 317.
Over the rationals with only the real place and the trivial character, the square-root
bound at norm zero fails for some test function. The real Gaussian gives a witness.
Deviation: States a counterexample to (7.1.2.3) at `A = 1/2`, where both printed sums are empty. -/
theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      let normℝ (g : Jℚ) := ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ)
      ¬ Asymptotics.IsBigO (comap normℝ (𝓝[>] (0 : ℝ)))
        (sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f : Jℚ → ℂ)
        (fun g ↦ (normℝ g) ^ (1 / 2 : ℝ)) := by
  let r (g : Jℚ) : ℝ := (sIdeleQuotientNorm ℚ ∅ g).val
  have hr : Ioi 0 ⊆ range r := by
    intro t ht
    obtain ⟨s, hs⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    let u : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (ne_of_gt (show (0 : ℝ≥0) < ⟨t, ht.le⟩ from ht))
    exact ⟨s u, congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) (hs u)⟩
  have : CompactSpace Jℚ₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ ∅).isCompact_preimage (isCompact_singleton (x := 1)))
  have : IsFiniteMeasure μℚ₁ := CompactSpace.isFiniteMeasure (μ := μℚ₁)
  let c : ℂ := (μℚ₁).real univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μℚ₁)).ne'
  refine sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_gaussian.elim fun f hf ↦ ?_
  let θ : Jℚ → ℂ := sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f
  have he : ∀ g, θ g = c * (2 * (Real.exp (-(r g ^ 2)) : ℂ)) :=
    sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_eval f hf
  exact ⟨f, sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit r hr c hc θ he⟩

end Counterexample

-- TODO(paper-gap): Remark 7.1.2.4 drops the imaginary-unit conversion in the phase
-- and reverses the phase sign in the displayed list for the saturated product.

/-- The reciprocal of `1 - b exp(-L z)`, with `exp(-L) ≠ 1`, is meromorphic with a nonpositive
integer order, which is negative exactly at the zeros of `1 - b exp(-L z)`. -/
private theorem finiteHeckeEulerFactor_poles_iff_exp
    (b L : ℂ) (hL : Complex.exp (-L) ≠ 1) (s : ℂ) :
    MeromorphicAt (fun z ↦ (1 - b * Complex.exp (-(L * z)))⁻¹) s ∧ ∃ k : ℤ, k ≤ 0 ∧
      meromorphicOrderAt (fun z ↦ (1 - b * Complex.exp (-(L * z)))⁻¹) s = k ∧
      (k < 0 ↔ 1 - b * Complex.exp (-(L * s)) = 0) := by
  let g : ℂ → ℂ := fun z ↦ 1 - b * Complex.exp (-(L * z))
  have hg : ∀ z, AnalyticAt ℂ g z := fun z ↦ by fun_prop
  have hne : analyticOrderAt g s ≠ ⊤ := by
    intro htop
    have h0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hg).mp htop
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    simp only [g, Pi.zero_apply, mul_zero, neg_zero, Complex.exp_zero, mul_one,
      sub_eq_zero] at e0 e1
    subst e0
    exact hL (by simpa using e1.symm)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨(hg s).meromorphicAt.inv, -(k : ℤ), by omega, ?_, ?_⟩
  · change meromorphicOrderAt g⁻¹ s = _
    rw [meromorphicOrderAt_inv, (hg s).meromorphicOrderAt_eq, ← hk]
    simp
  · have : (-(k : ℤ) < 0) ↔ analyticOrderAt g s ≠ 0 := by
      rw [← hk]; simp; omega
    rw [this, analyticOrderAt_ne_zero]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hg s, h⟩⟩

/-- Every finite Hecke Euler factor is meromorphic with a nonpositive integer order, negative
exactly at the zeros of the Euler polynomial at an unramified place. -/
private theorem finiteHeckeEulerFactor_poles_iff_order
    (χ : PontryaginDual C𝔽) (v : Primes) (s : ℂ) :
    MeromorphicAt (finiteHeckeEulerFactor χ v) s ∧ ∃ k : ℤ, k ≤ 0 ∧
      meromorphicOrderAt (finiteHeckeEulerFactor χ v) s = k ∧
      (k < 0 ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
        1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) = 0) := by
  classical
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    let L := Complex.log (v.asIdeal.absNorm : ℂ)
    have hpow (z : ℂ) : (v.asIdeal.absNorm : ℂ) ^ (-z) = Complex.exp (-(L * z)) := by
      rw [Complex.cpow_def_of_ne_zero hN0]
      congr 1
      ring
    have hL : Complex.exp (-L) ≠ 1 := by
      rw [Complex.exp_neg, Complex.exp_log hN0]
      intro h
      have := inv_eq_one.mp h
      have h2 := HeightOneSpectrum.one_lt_absNorm v
      have : (v.asIdeal.absNorm : ℕ) = 1 := by exact_mod_cast this
      omega
    have hfun : finiteHeckeEulerFactor χ v = fun z ↦
        (1 - (ideleClassNormTwist χ 0).localValue v * Complex.exp (-(L * z)))⁻¹ := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_left hv, hpow]
    obtain ⟨hm, k, hk, ho, hiff⟩ :=
      finiteHeckeEulerFactor_poles_iff_exp ((ideleClassNormTwist χ 0).localValue v) L hL s
    rw [hfun]
    exact ⟨hm, k, hk, ho, by rw [hiff, hpow]; simp [hv]⟩
  · have hfun : finiteHeckeEulerFactor χ v = fun _ ↦ 1 := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_right hv]
    rw [hfun]
    refine ⟨MeromorphicAt.const _ _, 0, le_rfl, ?_, by simp [hv]⟩
    rw [meromorphicOrderAt_const]
    simp

/-- Paper: Remark 7.1.2.4, p. 318.
At an unramified finite place the poles of the Hecke Euler factor are equally spaced on
the imaginary axis. The phase is specified by the value at a local uniformizer.
Deviation: Uses the global character after extension and the phase convention
`χ(πᵥ) = qᵥ^(-it)` of Lemma 7.1.2.2. The period lattice is a subgroup of `ℂ`. -/
theorem finiteHeckeEulerFactor_poles_iff (χ : PontryaginDual C𝔽) (v : Primes)
    (_hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (t : ℝ)
    (_ht : (ideleClassNormTwist χ 0).localValue v =
      (v.asIdeal.absNorm : ℂ) ^ (-(t : ℂ) * Complex.I)) (s : ℂ) :
    meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 ↔
      ∃ m : ℤ, s = (((m : ℝ) * (2 * Real.pi / Real.log (v.asIdeal.absNorm : ℝ)) - t : ℝ) : ℂ) *
        Complex.I := by
  obtain ⟨-, k, -, ho, hiff⟩ := finiteHeckeEulerFactor_poles_iff_order χ v s
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hℓ : 0 < Real.log (v.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  set ℓ := Real.log (v.asIdeal.absNorm : ℝ) with hℓdef
  have hlog : Complex.log (v.asIdeal.absNorm : ℂ) = (ℓ : ℂ) := by
    rw [hℓdef, Complex.natCast_log]
  rw [ho, show ((k : WithTop ℤ) < 0 ↔ k < 0) from by exact_mod_cast Iff.rfl, hiff, _ht,
    and_iff_right _hv, sub_eq_zero, ← Complex.cpow_add _ _ hN0, eq_comm,
    Complex.cpow_def_of_ne_zero hN0, hlog, Complex.exp_eq_one_iff]
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    push_cast
    field_simp
    linear_combination -hn
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rw [hm]
    push_cast
    field_simp
    ring

open Classical in
/-- Paper: Remark 7.1.2.4, p. 318.
At a rational prime with all places above it in `S`, the poles of the product are precisely
the poles of the individual local Euler factors at those places.
Deviation: The factors at ramified places are one, as in §3.2.1. -/
theorem finiteHeckeEulerProduct_poles_iff (χ : PontryaginDual C𝔽) (S : Finset Primes)
    (p : HeightOneSpectrum (𝓞 ℚ)) (_hsat : ∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S)
    (s : ℂ) :
    let Sₚ := S.filter (fun v ↦ v.under (𝓞 ℚ) = p)
    meromorphicOrderAt (fun z ↦ ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v z) s < 0 ↔
      ∃ v ∈ Sₚ, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 := by
  intro Sₚ
  choose hm k hk ho _ using fun v ↦ finiteHeckeEulerFactor_poles_iff_order χ v s
  have hfun : (fun z ↦ ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v z) =
      ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v := by
    funext z
    simp [Finset.prod_apply]
  rw [hfun, meromorphicOrderAt_prod (fun v _ ↦ hm v)]
  simp only [ho]
  norm_cast
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ∑ v ∈ Sₚ, k v = 0 :=
      Finset.sum_eq_zero fun v hv ↦ le_antisymm (hk v) (hne v hv)
    omega
  · rintro ⟨v, hv, hlt⟩
    have h := Finset.single_le_sum (f := fun w ↦ -k w) (fun w _ ↦ neg_nonneg.mpr (hk w)) hv
    rw [Finset.sum_neg_distrib] at h
    omega

-- TODO(prerequisite): The induced Euler-factor identity in Remark 7.1.2.4 needs
-- global Weil groups and their induction and local L-factor constructions.
-- TODO(later): needs §7.2.1 for continuity of the Laurent coefficient operators and
-- their descent to the coinvariants (Theorem 7.2.1.1(1)–(2)).
-- TODO(paper-gap): The eigendistribution interpretation on pp. 319–321 fails for
-- general Laurent coefficients. For the real Gaussian at the trivial character,
-- scaling f(x) to f(x/r) adds log(r) * a₋₁ to a₀. At a multiple pole, lower polar
-- coefficients also mix under dilation. The leading polar coefficient transforms by
-- the character, and all coefficients have the character law on norm-one elements.
-- On p. 321 the lattice index is also used as a Laurent index. At index zero a
-- test function compactly supported in the S-ideles can have nonzero a₀.
-- TODO(paper-gap): The contour formula on p. 323 needs positive orientation and
-- exclusion of the other poles, as in Lemma C.5.3.2. Compare scalar normal forms
-- away from the distributional poles, as in infiniteLocalIdelicZFunction_distribution.

end RiemannMasullo
