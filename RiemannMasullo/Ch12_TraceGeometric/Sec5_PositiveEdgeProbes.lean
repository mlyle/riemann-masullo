module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLaplaceEdges
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_Isolated
import all RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Compact positive probes for the width comparison in §12.5 -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F]
local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "m𝔽" => (continuousIdeleClassNorm F : C →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "M(" φ ", " χ ", " w ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C).val
    (ideleClassNormTwist (F := F) χ w)

/-- Lifting a smooth compact radial test with the inverse angular twist gives its
ordinary bilateral Laplace transform times the volume of the norm-one classes. -/
theorem exists_characterNormTest_laplace (χ : PontryaginDual C) (g : ℝ → ℂ)
    (hs : ContDiff ℝ (∞) g) (hc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport C,
      (∀ x, φ.val x = (χ⁻¹ x : ℂ) * g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ))) ∧
      ∀ w : ℂ, M(φ, χ, w) =
        (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) * bilateralLaplace g w := by
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) χ⁻¹ g hs hc
  refine ⟨φ, hφ, fun w ↦ ?_⟩
  rw [characterNormTest_mellin g hs hc χ⁻¹ φ hφ χ w]
  have hone : χ * χ⁻¹ = 1 := mul_inv_cancel _
  rw [ite_eq_left (fun u ↦ by rw [hone]; rfl)]
  have hconst (u) : ((χ * χ⁻¹) (QuotientGroup.mk (canonicalIdeleNormSection F u) : C) : ℂ) = 1 := by
    rw [hone]; rfl
  have hi := grh_shift_integral g hs.continuous _ hconst 0 w
  simp only [sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hi
  rw [hi]
  rfl

/-- For each character and each real strip half-width, an actual compact Bruhat test has
Mellin transform with strictly positive real part at every ordinate on both centered edges. -/
theorem exists_hecke_positive_edge_probes (χ : PontryaginDual C) (b : ℝ) :
    ∃ φ : BruhatCompactSupport C, ∀ w : ℂ, |w.re| = |b| → 0 < (M(φ, χ, w)).re := by
  obtain ⟨K, -, -, -, -, hK⟩ := exists_compact_positive_laplace_edges
  let H := fun x : ℝ ↦ K x / Real.cosh (b*x)
  obtain ⟨hs, hc, -, hp⟩ := hK b
  let g := fun x : ℝ ↦ (H x : ℂ)
  have hgs : ContDiff ℝ (∞) g := Complex.ofRealCLM.contDiff.comp hs
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  obtain ⟨φ, -, hM⟩ := exists_characterNormTest_laplace χ g hgs hgc
  refine ⟨φ, fun w hw ↦ ?_⟩
  rw [hM, Complex.re_ofReal_mul]
  apply mul_pos
  · exact lt_of_le_of_ne ENNReal.toReal_nonneg (Complex.ofReal_ne_zero.mp (grh_classVolume_ne_zero (F := F))).symm
  · have h := hp w.re hw w.im
    rw [Complex.re_add_im] at h
    exact h

namespace Isolated

local notation "Chars(" τ ")" => {χ : PontryaginDual C // ∀ t : ℝ≥0ˣ, χ ((τ) t) = 1}
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Sites(" χ ")" => {z : ℂ // 0 < ord(χ,z)}
local notation "Off(" z ")" => ((z).val.re - 1/2)
local notation "m(" χ "," z ")" => (ord(χ,(z).val)).toNat
local notation "Ext(" τ ", " α ")" => {p : Chars(τ) × ℂ // 0 < ord(p.1.val,p.2) ∧ α ≤ |p.2.re - 1/2|}

/-- The probes in the signed width comparison of Theorem 12.5.1.1 (pp. 519–520) can be
chosen unconditionally. The only remaining hypothesis compares the two actual signed sums. -/
theorem exists_positive_probe_traceFormula_exteriorZeros_of_widthComparison (τ : ℝ≥0ˣ →ₜ* C)
    (hτ : RightInverse τ (ideleClassNorm F)) {α s : ℝ} (hα : 0 < α) (hs : 1 < s) :
    ∃ probe : Chars(τ) → ℝ → BruhatCompactSupport C,
      (∀ (χ : Chars(τ)) (b : ℝ) (w : ℂ), |w.re| = |b| → 0 < (M(probe χ b, χ.val, w)).re) ∧
      ((∀ (χ : Chars(τ)) (b : ℝ), α ≤ b → b < 1/2 →
          -(∑' z : Sites(χ.val), if |Off(z)| < b then (m(χ.val,z) : ℝ) *
            (M(probe χ b, χ.val, z.val - 1/2)).re else 0) ≤
          -(∑' z : Sites(χ.val), (spectralStripMultiplicity b s Off(z) m(χ.val,z) : ℝ) *
            (M(probe χ b, χ.val, z.val - 1/2)).re)) →
        ∀ φ : BruhatCompactSupport C, HasSum (fun p : Ext(τ, α) ↦
          ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ, p.val.1.val, p.val.2 - 1/2)) 0) := by
  choose probe hp using fun (χ : Chars(τ)) (b : ℝ) ↦ exists_hecke_positive_edge_probes χ.val b
  refine ⟨probe, hp, fun hcomp φ ↦ traceFormula_exteriorZeros_of_signedWidthComparison τ hτ hα hs
    probe ?_ hcomp φ⟩
  intro χ b hab _ z hz
  apply hp
  rw [abs_of_pos (hα.trans_le hab)]
  simpa only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] using hz

private theorem positive_sum_subset {ι : Type*} (f : ι → ℝ) {S : ℝ} (hf : HasSum f S)
    (hp : ∀ i, 0 < f i) (E : Set ι) :
    (∑' i, E.indicator f i) ≤ S ∧ (S ≤ ∑' i, E.indicator f i ↔ E = univ) := by
  classical
  have hle : E.indicator f ≤ f := by
    intro i
    by_cases h : i ∈ E <;> simp [h, (hp i).le]
  have hi := hf.summable.indicator E
  rw [← hf.tsum_eq]
  refine ⟨hi.tsum_le_tsum hle hf.summable, fun h ↦ eq_univ_of_forall fun i ↦ ?_, ?_⟩
  · by_contra hn
    have hs : E.indicator f i < f i := by simp [hn, hp i]
    exact (hi.tsum_lt_tsum hle hs hf.summable).not_ge h
  · rintro rfl
    simp

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "volume₁" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archRestricts(" φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u =
    (φ).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "finiteRestricts(" φ ", " b ")" =>
  (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u =
    (φ).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) /
    (finiteLocalMultiplicativeTamagawaMeasure F v
      ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "signedLocal(" a ", " b ")" =>
  (-(volume₁ * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑' v : V, finiteTerm(v, b v))))
local notation "weight(" φ ", " χ ", " z ")" =>
  (((ord(χ,(z).val) : ℤ) : ℝ) * (M(φ, χ, (z).val - 1/2)).re)

/-- One fixed radial profile, lifted separately to each normalized character, gives
strictly positive weights at every Hecke zero. The actual signed sum of principal values
equals the total weight. A subset accounts for that entire sum exactly when it contains
every zero of the selected character. -/
theorem exists_polar_free_positive_mass_test (τ : ℝ≥0ˣ →ₜ* C) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ H : ℝ → ℝ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ (∀ x, H (-x) = H x) ∧
      ∀ χ : Chars(τ), ∃ (φ : BruhatCompactSupport C) (a : archTest) (b : finiteTest),
        (∀ x, φ.val x = (χ.val⁻¹ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ))) ∧
        archRestricts(φ, a) ∧ finiteRestricts(φ, b) ∧
        M(φ, 1, 1/2) = 0 ∧ M(φ, 1, -1/2) = 0 ∧
        (∀ z : Sites(χ.val), 0 < weight(φ, χ.val, z)) ∧
        HasSum (fun z : Sites(χ.val) ↦ weight(φ, χ.val, z)) (signedLocal(a, b)).re ∧
        ∀ E : Set (Sites(χ.val)),
          (∑' z, E.indicator (fun u ↦ weight(φ, χ.val, u)) z) ≤ (signedLocal(a, b)).re ∧
          ((signedLocal(a, b)).re ≤ ∑' z, E.indicator (fun u ↦ weight(φ, χ.val, u)) z ↔ E = univ) := by
  classical
  obtain ⟨H, hs, hc, he, hplus, hminus, hp⟩ := exists_compact_polar_free_positive_laplace_strip
    (by norm_num : (0:ℝ)<1/2)
  refine ⟨H, hs, hc, he, fun χ ↦ ?_⟩
  let g := fun x : ℝ ↦ (H x : ℂ)
  have hgs : ContDiff ℝ (∞) g := Complex.ofRealCLM.contDiff.comp hs
  have hgc : HasCompactSupport g := hc.comp_left Complex.ofReal_zero
  obtain ⟨φ, hφ, hm⟩ := exists_characterNormTest_laplace χ.val g hgs hgc
  obtain ⟨a, b, ha, hb, -, -⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1/2 : ℝ))
  have hψ (t) : χ.val⁻¹ (τ t) = 1 := by change (χ.val (τ t))⁻¹ = 1; rw [χ.property, inv_one]
  have pole (w : ℂ) (hw : bilateralLaplace g w = 0) : M(φ, 1, w) = 0 := by
    by_cases h : (1 : PontryaginDual C) = χ.val
    · rw [h, hm, hw, mul_zero]
    · rw [characterNormTest_mellin g hgs hgc χ.val⁻¹ φ hφ 1 w]
      rw [ite_eq_right (fun hone ↦ h (grh_character_eq τ hτ (fun _ ↦ rfl) χ.property hone)), zero_mul]
  have h₁ : M(φ, 1, 1/2) = 0 := pole _ (by convert hplus using 1; norm_num [g])
  have h₂ : M(φ, 1, -1/2) = 0 := pole _ (by convert hminus using 1; norm_num [g])
  have hpos (z : Sites(χ.val)) : 0 < weight(φ, χ.val, z) := by
    have hz : |z.val.re-1/2|<1/2 := lt_of_not_ge fun hn ↦
      (exteriorZeros_isEmpty_of_half_le τ (le_refl (1/2 : ℝ))).false ⟨(χ, z.val), z.property, hn⟩
    rw [hm, Complex.re_ofReal_mul]
    exact mul_pos (Int.cast_pos.mpr z.property) (mul_pos
      (lt_of_le_of_ne ENNReal.toReal_nonneg (Complex.ofReal_ne_zero.mp (grh_classVolume_ne_zero (F := F))).symm)
      (hp _ (by simpa using hz)))
  have h := translatedLocalTerms_hasSum τ hτ χ.val⁻¹ hψ g hgs hgc 0 φ (by simpa using hφ) a b ha hb
  rw [inv_inv] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, h₁, h₂, zero_add,
    zero_sub] at h
  have hsum : HasSum (fun z : Sites(χ.val) ↦ weight(φ, χ.val, z)) (signedLocal(a, b)).re := by
    convert Complex.hasSum_re h using 1
    · funext z
      rw [hm]
      simp [bilateralLaplace, Complex.mul_re]
  refine ⟨φ, a, b, hφ, ha, hb, h₁, h₂, hpos, hsum, fun E ↦ ?_⟩
  exact positive_sum_subset _ hsum hpos E


/-- The gap of Theorem 12.5.1.1 at every positive width is equivalent to one upper bound
on the actual signed local terms for each normalized character, evaluated against the
same radial profile. The proposed upper bound is its positive critical-line mass. -/
theorem exists_local_mass_comparison_iff_exteriorZeros (τ : ℝ≥0ˣ →ₜ* C) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (probe : Chars(τ) → BruhatCompactSupport C) (a : Chars(τ) → archTest) (b : Chars(τ) → finiteTest),
      (∀ χ, archRestricts(probe χ, a χ) ∧ finiteRestricts(probe χ, b χ) ∧
        M(probe χ, 1, 1/2) = 0 ∧ M(probe χ, 1, -1/2) = 0) ∧
      ((∀ χ : Chars(τ), (signedLocal(a χ, b χ)).re ≤
          ∑' z : Sites(χ.val), if z.val.re = 1/2 then weight(probe χ, χ.val, z) else 0) ↔
        ∀ α : ℝ, 0 < α → ∀ φ : BruhatCompactSupport C, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
          HasSum (fun p : Ext(τ, α) ↦
            ((ord(p.val.1.val,p.val.2) : ℤ) : ℂ) * M(φ, p.val.1.val, p.val.2 - 1/2)) 0) := by
  classical
  obtain ⟨H, _, _, _, hH⟩ := exists_polar_free_positive_mass_test τ hτ
  choose probe a b _ ha hb hplus hminus _ _ hm using hH
  refine ⟨probe, a, b, fun χ ↦ ⟨ha χ, hb χ, hplus χ, hminus χ⟩, ?_⟩
  let E (χ : Chars(τ)) : Set (Sites(χ.val)) := {z | z.val.re = 1/2}
  have hcomp (χ : Chars(τ)) := (hm χ (E χ)).2
  simp only [E, Set.indicator, Set.mem_ofPred_eq] at hcomp
  constructor
  · intro h α hα
    apply (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mpr
    refine ⟨fun p ↦ ?_⟩
    have hu := (hcomp p.val.1).mp (h p.val.1)
    let z : Sites(p.val.1.val) := ⟨p.val.2, p.property.1⟩
    have hz : z ∈ E p.val.1 := (Set.eq_univ_iff_forall.mp hu) z
    change p.val.2.re = 1/2 at hz
    exact (not_le.mpr hα) (by simpa only [hz, sub_self, abs_zero] using p.property.2)
  · intro h χ
    apply (hcomp χ).mpr
    apply Set.eq_univ_of_forall
    intro z
    change z.val.re = 1/2
    by_contra hz
    have hα : 0 < |Off(z)| := abs_pos.mpr (sub_ne_zero.mpr hz)
    exact ((hasSum_exteriorZeros_iff_isEmpty τ hτ _).mp (h _ hα)).false ⟨(χ,z.val),z.property,le_rfl⟩

end Isolated
end RiemannMasullo
