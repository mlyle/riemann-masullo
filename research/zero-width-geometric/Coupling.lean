module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_GeometricBlocks
public import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Spacing forced by zero-width geometric blocks

This certificate for Theorem 10.4.3.5(2), p. 472 (#7406), combines the zero-width
secant estimate (#7606), anadodik's geometric singleton bound (#7560) and willzh0's
fixed-support first-moment theorem (#7598). For each fixed Hecke character and
Sobolev order `s > 3`, the bound for every compact test forces an inverse-polynomial
distance from each simple zero on the chosen line to every other finite positive-order
zero on that line. The exponent and constant are uniform in both heights.

The parents are #7598 at `05db739a93a87039bed1027d80c5f2a82b0794b2` and the
one-file secant proof of #7606 at `eef8307ddb15e67a36860940dd18d0fb8c2f544e`.
On their integration branch, with the repository toolchain, run

```sh
lake build RiemannMasullo.Ch10_TraceSpectral.Sec4b_GeometricBlocks
lake build RiemannMasullo.Ch10_TraceSpectral.Sec4b_Isolated
lake env lean research/zero-width-geometric/Coupling.lean
```
-/

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology
namespace RiemannMasullo.Isolated
@[expose] public noncomputable section
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {s : ℝ} (hα : 0 ≤ (0 : ℝ)) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (x : SpectralStripJetIndex χ a (0 : ℝ) s →
    spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le))
  (f : SpectralStripJetIndex χ a (0 : ℝ) s → StrongDual ℂ
    (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le)))

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) (0 : ℝ) s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀
local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " width ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-width) width ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity (0 : ℝ) s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a (0 : ℝ) s
local notation "jet(" z ", " m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)
local notation "stripU(" j ")" => (spectralStripJet_memLp χ hα hs₀ j).toLp
  (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)
local notation "geometricBlock(" z ")" =>
  (∑ m : Fin (jetCount(z)),
    (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight (Gₐ (Aφ (Sₐ(x jet(z, m))))),
      smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))
local notation "blockOf(" ψ ", " z ")" =>
  (∑ m : Fin (jetCount(z)), (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight
    (Gₐ ((hardySobolevTestAction μ𝔽 m𝔽 (-(0 : ℝ)) (0 : ℝ) s hI hs₀ ψ) (Sₐ(x jet(z, m))))),
    smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))

/-- At zero width, one simple retained site and any other positive-order site of the same
character force the first Mellin moment of a fixed test to decay with their gap. -/
theorem spectralStripGeometricKernel_line_firstMoment_pair
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1) (hsδ : 3 + 2 * δ < s)
    (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : BddAbove (range fun K : Finset zeros(F, χ, a, (0 : ℝ)) ↦
      traceNorm (∑ z ∈ K, geometricBlock(z)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (t u : ℝ),
      meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) ((a : ℂ) + (t : ℂ) * Complex.I) = 1 →
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        ((a : ℂ) + (u : ℂ) * Complex.I)).untop₀.toNat →
      u ≠ t → ‖∫ g : C𝔽, φ.val g * spectralZeroJet (χ ω) 0 t 1 g ∂μ𝔽‖ ≤
        C * |u - t| ^ δ := by
  obtain ⟨c, hc, hlow⟩ := spectralStripJet_lowerBound (a := a) χ hχ hα hs
  obtain ⟨B, hB, hblock⟩ := spectralStripGeometricKernel_blocks_bddAbove_forces_firstJet_separation
    a hα hs φ χ x f hb hbound
  obtain ⟨D, hD, hsec⟩ := spectralStrip_firstJet_near_retained_span_on_line χ a hδ hδ₁ hsδ
  refine ⟨B * D / c, by positivity, ?_⟩
  intro ω t u ht hu hne
  let z : zeros(F, χ, a, 0) := ⟨(ω, 0, t), by simp, by
    simpa only [add_zero, ht] using (show (0 : WithTop ℤ) < 1 by norm_num)⟩
  have hsimple : spectralStripMultiplicity 0 s 0 1 = 1 := by
    rw [spectralStripMultiplicity_boundary le_rfl (Or.inr rfl), spectralBoundaryMultiplicity, min_eq_left]
    apply Nat.lt_ceil.mpr
    push_cast
    linarith
  have hz : spectralStripMultiplicity 0 s 0 (order(χ, a, z.val)).untop₀.toNat = 1 := by
    simpa only [z, add_zero, ht, WithTop.untop₀_one, Int.toNat_one] using hsimple
  let j : SpectralStripJetIndex χ a 0 s :=
    ⟨(ω, 0, t, 0), by
      simpa only [add_zero, ht, WithTop.untop₀_one, Int.toNat_one] using
        (show 0 < spectralStripMultiplicity 0 s 0 1 by omega)⟩
  let k : SpectralStripJetIndex χ a 0 s := ⟨(ω, 0, u, 0), by
    rw [spectralStripMultiplicity_boundary le_rfl (Or.inr rfl), lt_spectralBoundaryMultiplicity]
    exact ⟨by simpa only [add_zero] using hu, by push_cast; linarith⟩⟩
  let m : Fin (spectralStripMultiplicity 0 s 0 (order(χ, a, z.val)).untop₀.toNat) := ⟨0, by omega⟩
  obtain ⟨d, v, hd, hv, hdist⟩ := hsec ω t u j k rfl rfl hne
  have heq : (fun i : SpectralStripJetIndex χ a 0 s ↦ Dₐ (f i)) = (fun i ↦ stripU(i)) :=
    funext hb.2
  have hsingle := hblock z m hz.le d hd v (by rw [heq]; exact hv)
  have hc' : c ≤ ‖(f j).comp (Θ₀).mkQL‖ := by
    calc c ≤ ‖stripU(j)‖ := hlow _
         _ = ‖Dₐ (f j)‖ := by rw [hb.2 j]
         _ = _ := by
           rw [spectralSobolevDualEmbedding]
           exact LinearIsometryEquiv.norm_map _ ((f j).comp (Θ₀).mkQL)
  let M := ‖∫ g : C𝔽, φ.val g * spectralZeroJet (χ ω) 0 t 1 g ∂μ𝔽‖
  have hM : 0 ≤ M := norm_nonneg _
  change M * ‖(f j).comp (Θ₀).mkQL‖ ≤ B * ‖d - v‖ at hsingle
  change M ≤ B * D / c * |u - t| ^ δ
  have hMc := (mul_le_mul_of_nonneg_left hc' hM).trans (hsingle.trans
    (mul_le_mul_of_nonneg_left hdist hB))
  apply le_of_mul_le_mul_right ?_ hc
  calc
    M * c ≤ B * (D * |u - t| ^ δ) := hMc
    _ = (B * D / c * |u - t| ^ δ) * c := by field_simp

/-- If every compact test has bounded finite geometric sums at zero width and
`s>3`, a simple zero on the chosen line is polynomially separated from every
other positive-order zero on the same line. -/
theorem spectralStripGeometricKernel_line_allTests_forces_pair_spacing
    {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hsδ : 3 + 2 * δ < s)
    (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : ∀ ψ : BruhatCompactSupport C𝔽, BddAbove (range fun K : Finset zeros(F, χ, a, (0 : ℝ)) ↦
      traceNorm (∑ z ∈ K, blockOf(ψ, z)))) (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ t u : ℝ,
      meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) ((a : ℂ) + (t : ℂ) * Complex.I) = 1 →
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        ((a : ℂ) + (u : ℂ) * Complex.I)).untop₀.toNat →
      u ≠ t → c / (1 + |t|) ^ N ≤ |u - t| ^ δ := by
  let pairs := {p : ℝ × ℝ // meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
    ((a : ℂ) + (p.1 : ℂ) * Complex.I) = 1 ∧
    0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
      ((a : ℂ) + (p.2 : ℂ) * Complex.I)).untop₀.toNat ∧ p.2 ≠ p.1}
  obtain ⟨c, hc, N, hN⟩ := GeometricBaire.ideleFirstMoment_denominator_lower (χ ω)
    (A := 0) (fun _ : pairs ↦ 0) (fun p ↦ p.val.1) (fun p ↦ |p.val.2 - p.val.1| ^ δ)
    (fun _ ↦ by simp) (fun p ↦ Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr p.property.2.2)) δ)
    (fun ψ ↦ by
      obtain ⟨C, _, hC⟩ := spectralStripGeometricKernel_line_firstMoment_pair a hα hs ψ χ x f
        hδ.le hδ₁ hsδ hχ hb (hbound ψ)
      exact ⟨C, fun p ↦ hC ω p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2⟩)
  exact ⟨c, hc, N, fun t u ht hu hne ↦ hN ⟨(t, u), ht, hu, hne⟩⟩

/-- The zero-width geometric bound for every compact test and any fixed `s>3`
forces an inverse-polynomial lower bound on the gaps themselves. -/
theorem spectralStripGeometricKernel_line_allTests_forces_polynomial_spacing
    (hs₃ : 3 < s) (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : ∀ ψ : BruhatCompactSupport C𝔽, BddAbove (range fun K : Finset zeros(F, χ, a, (0 : ℝ)) ↦
      traceNorm (∑ z ∈ K, blockOf(ψ, z)))) (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ t u : ℝ,
      meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) ((a : ℂ) + (t : ℂ) * Complex.I) = 1 →
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        ((a : ℂ) + (u : ℂ) * Complex.I)).untop₀.toNat →
      u ≠ t → c / (1 + |t|) ^ N ≤ |u - t| := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 + 2 / (s - 3))
  have hsm : 0 < s - 3 := sub_pos.mpr hs₃
  have h₁ : (1 : ℝ) < m := by linarith [div_pos (show (0 : ℝ) < 2 by norm_num) hsm]
  have hm₀ : (0 : ℝ) < m := by linarith
  have hsmall : 3 + 2 * (1 / (m : ℝ)) < s := by
    have hdiv : 2 / (s - 3) < m := by linarith
    have hl := (div_lt_iff₀ hsm).mp hdiv
    have hl' : (2 : ℝ) / m < s - 3 := (div_lt_iff₀ hm₀).mpr (by linarith)
    rw [mul_one_div]
    linarith
  obtain ⟨c, hc, N, hgaps⟩ := spectralStripGeometricKernel_line_allTests_forces_pair_spacing
    a hα hs χ x f (δ := 1 / m) (by positivity) (by apply (div_le_iff₀ hm₀).mpr; linarith)
    hsmall hχ hb hbound ω
  refine ⟨c ^ m, by positivity, N * m, ?_⟩
  intro t u ht hu hne
  have H := pow_le_pow_left₀ (by positivity : 0 ≤ c / (1 + |t|) ^ N) (hgaps t u ht hu hne) m
  rw [div_pow, ← pow_mul, ← Real.rpow_mul_natCast (abs_nonneg _),
    one_div_mul_cancel hm₀.ne', Real.rpow_one] at H
  exact H

/-- Superpolynomially small simple-to-positive gaps in one character produce a single compact
test with unbounded finite geometric block sums. The same test applies to every bound. -/
theorem spectralStripGeometricKernel_line_exists_unbounded_test_of_small_gaps
    (hs₃ : 3 < s) (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (ω : PontryaginDual (ideleClassNorm F).ker)
    (hsmall : ∀ c > (0 : ℝ), ∀ N : ℕ, ∃ t u : ℝ,
      meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) ((a : ℂ) + (t : ℂ) * Complex.I) = 1 ∧
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        ((a : ℂ) + (u : ℂ) * Complex.I)).untop₀.toNat ∧
      u ≠ t ∧ |u - t| < c / (1 + |t|) ^ N) :
    ∃ ψ : BruhatCompactSupport C𝔽, ¬ BddAbove (range fun K : Finset zeros(F, χ, a, 0) ↦
      traceNorm (∑ z ∈ K, blockOf(ψ, z))) := by
  by_contra h
  have hall (ψ : BruhatCompactSupport C𝔽) : BddAbove (range fun K : Finset zeros(F, χ, a, 0) ↦
      traceNorm (∑ z ∈ K, blockOf(ψ, z))) := by
    by_contra hψ
    exact h ⟨ψ, hψ⟩
  obtain ⟨c, hc, N, hN⟩ := spectralStripGeometricKernel_line_allTests_forces_polynomial_spacing
    a hα hs χ x f hs₃ hχ hb hall ω
  obtain ⟨t, u, ht, hu, hne, hgap⟩ := hsmall c hc N
  exact hgap.not_ge (hN t u ht hu hne)

#print axioms spectralStripGeometricKernel_line_firstMoment_pair
#print axioms spectralStripGeometricKernel_line_allTests_forces_pair_spacing

#print axioms spectralStripGeometricKernel_line_allTests_forces_polynomial_spacing
#print axioms spectralStripGeometricKernel_line_exists_unbounded_test_of_small_gaps

end

end RiemannMasullo.Isolated
