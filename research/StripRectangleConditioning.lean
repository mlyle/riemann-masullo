module
import Lean
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch10_TraceSpectral.Sec3_Printed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import all RiemannMasullo.Ch09_HardySobolev.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
/-!
# A necessary height bound for the strip trace rectangles

For Theorem 10.3.2.1(1), pp. 453–455. The hypotheses on the quotient, its
biorthogonal vectors and its coordinate forms are those of the strip rectangle
statement in Chapter 10. Both results assume trace-Cauchy rectangles for all
compact Bruhat tests and admissible enumerations.

* `rational_site_polynomial` bounds the distance from a zeroth coordinate form
  to the annihilator of its complete jet block, uniformly in the rational
  untwisted row.
* `rational_zeta_ordinate_separation` gives a polynomial lower bound for the
  difference between any two distinct critical-line Riemann zeta ordinates.
  It uses the width-zero quotient with Sobolev exponent four.

The first part reproduces the single-column estimate recorded on issue #6993.
The new estimates use Banach–Steinhaus on real-line Schwartz profiles supported
after multiplication by one fixed cutoff. The two root theorems are audited
at the end of the file.
-/

noncomputable section
open Function Set Filter MeasureTheory Topology
open scoped SchwartzMap ContDiff
open IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => (logIdeleClassNorm F)
local notation "W'(" l ", " r ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm l r s true
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open Classical in
private theorem spectralRectangle_coordinate {J Z : Type*} (A : H →L[ℂ] H)
    (x : J → H) (L : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x L)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Injective (fun u : (z : Z) × Fin (N z) ↦ j u.1 u.2))
    (K : Finset Z) (z : Z) (m : Fin (N z)) (v : H) :
    L (j z m) (spectralConvolutionFiniteSum A x L K N j v) =
      if z ∈ K then L (j z m) (A v) else 0 := by
  classical
  split_ifs with hz
  · exact spectralConvolutionFiniteSum_limit_of_traceCauchy_coordinate A x L K N j hb hj z hz m v
  · simp only [spectralConvolutionFiniteSum, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro u hu
    apply Finset.sum_eq_zero
    intro n _
    rw [hb.2.1, mul_zero]
    intro h
    have hzw : u = z := congrArg Sigma.fst (hj (a₁ := ⟨u, n⟩) (a₂ := ⟨z, m⟩) h)
    exact hz (hzw ▸ hu)

private theorem spectralRectangle_good_enumeration {Z U : Type*}
    (eχ : U ↪ ℕ) (π : Z → U) (old : Z ↪ ℕ × ℕ) :
    ∃ e : Z ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ (π z)) ∧ Injective (fun z ↦ (e z).2) := by
  let c := old.trans Nat.pairEquiv.toEmbedding
  exact ⟨⟨fun z ↦ (eχ (π z), c z), fun _ _ h ↦ c.injective (congrArg Prod.snd h)⟩,
    fun _ ↦ rfl, c.injective⟩

private theorem spectralRectangle_column_annihilator {J Z : Type*} (A : H →L[ℂ] H)
    (x : J → H) (L : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x L)
    (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (hj : Injective (fun u : (z : Z) × Fin (N z) ↦ j u.1 u.2))
    (e : Z ↪ ℕ × ℕ) (he : Injective (fun z ↦ (e z).2))
    (hc : SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) N j)) :
    ∀ ε > (0 : ℝ), ∃ C : ℕ, ∀ z : Z, C < (e z).2 →
      ∀ (m : Fin (N z)) (Ψ : StrongDual ℂ H), (∀ n, Ψ (x (j z n)) = 0) →
        ‖(L (j z m)).comp A‖ ≤ ε * ‖L (j z m) - Ψ‖ := by
  classical
  intro ε hε
  obtain ⟨i, hi⟩ := hc ε hε
  refine ⟨i.2, fun z hz m Ψ hΨ ↦ ?_⟩
  let row := max i.1 (e z).1
  let c := (e z).2
  let rect (t : ℕ) := ((Finset.Iic row).product (Finset.Iic t)).preimage e e.injective.injOn
  let B (t : ℕ) := spectralConvolutionFiniteSum A x L (rect t) N j
  have hmem (u : Z) (t : ℕ) : u ∈ rect t ↔ (e u).1 ≤ row ∧ (e u).2 ≤ t := by simp [rect]
  have zpos : 0 < c := (Nat.zero_le i.2).trans_lt hz
  have zmem : z ∈ rect c := (hmem ..).2 ⟨le_max_right .., le_rfl⟩
  have znot : z ∉ rect (c - 1) := by
    intro hm
    have h := ((hmem ..).1 hm).2
    change c ≤ c - 1 at h
    omega
  have rect_eq : rect c = insert z (rect (c - 1)) := by
    ext w
    by_cases h : w = z
    · simpa [h] using zmem
    · have hcol : (e w).2 ≠ c := fun ht ↦ h (he ht)
      rw [Finset.mem_insert, or_iff_right h, hmem, hmem]
      omega
  have kill (v : H) : Ψ ((B c - B (c - 1)) v) = 0 := by
    simp only [B, spectralConvolutionFiniteSum, rect_eq, Finset.sum_insert znot, add_sub_cancel_right,
      sum_apply, map_sum, ContinuousLinearMap.smulRight_apply, map_smul, hΨ, smul_zero, Finset.sum_const_zero]
  have coord (v : H) : L (j z m) ((B c - B (c - 1)) v) = L (j z m) (A v) := by
    simp only [B, sub_apply, map_sub, spectralRectangle_coordinate A x L hb N j hj,
      ite_eq_left zmem, ite_eq_right znot, sub_zero]
  have eq : (L (j z m) - Ψ).comp (B c - B (c - 1)) = (L (j z m)).comp A := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, sub_apply (L (j z m)) Ψ, coord, kill, sub_zero]
  obtain ⟨T, hT, ht⟩ := hi (row, c) (row, c - 1) ⟨le_max_left .., hz.le⟩ ⟨le_max_left .., by dsimp only [c]; omega⟩
  have top : ‖T.val‖ ≤ traceNorm T := by
    rw [← approximationNumber_zero_eq_opNorm T.val (isCompactOperator_of_isNuclearOperator T.property)]
    simpa using spectralConvolutionFiniteSum_limit_of_traceCauchy_bound T {0}
  change T.val = B c - B (c - 1) at hT
  rw [←eq]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [mul_comm ε, ←hT]
  exact mul_le_mul_of_nonneg_left (top.trans ht.le) (norm_nonneg _)
#print axioms spectralRectangle_column_annihilator

variable (a : ℝ)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
private theorem spectralRectangle_norm_smul {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (c : ℂ) (Λ : StrongDual ℂ H) : ‖c • Λ‖ = ‖c‖ * ‖Λ‖ := norm_smul ..

set_option backward.isDefEq.respectTransparency false in
private theorem spectralRectangles_actual_necessary
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {α s : ℝ} (hα : 0 ≤ α) (hs₁ : 1 < s)
    (φ : BruhatCompactSupport C𝔽) (eχ : PontryaginDual C₁ ↪ ℕ) (old : Z(χ, α) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → Q(a, neg_le_self hα, hs₀(hs₁)))
    (L : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, neg_le_self hα, hs₀(hs₁)))
    (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ j, spectralSobolevDualEmbedding F a (neg_le_self hα) hs₀(hs₁) (L j) =
      (spectralStripJet_memLp χ hα hs₀(hs₁) j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    let count (z : Z(χ, α)) := N(χ, α, s, z)
    let j (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex χ a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    let A := spectralConvolution (F := F) a (neg_le_self hα) hs₀(hs₁) φ
    let u (i : SpectralStripJetIndex χ a α s) := (spectralStripJet_memLp χ hα hs₀(hs₁) i).toLp
      (spectralZeroJet (χ i.val.1) i.val.2.1 i.val.2.2.1 i.val.2.2.2)
    (∀ e : Z(χ, α) ↪ ℕ × ℕ, (∀ z, (e z).1 = eχ z.val.1) →
      SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A x L
        (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) count j)) →
    ∀ ε > (0 : ℝ), ∃ S : Finset Z(χ, α), ∀ z : Z(χ, α), z ∉ S →
      ∀ (hz : 0 < count z) (Ψ : StrongDual ℂ Q(a, neg_le_self hα, hs₀(hs₁))),
      (∀ n, Ψ (x (j z n)) = 0) →
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g ∂μ𝔽‖ *
        ‖u (j z ⟨0, hz⟩)‖ ≤ ε * ‖(show W'(-α, α, s) from u (j z ⟨0, hz⟩)) -
        spectralSobolevDualEmbedding F a (neg_le_self hα) hs₀(hs₁) Ψ‖ := by
  intro count j A u hc ε hε
  let index (i : SpectralStripJetIndex χ a α s) : (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(i.val.1, i.val.2.1, i.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα i⟩, ⟨i.val.2.2.2, i.property⟩⟩
  let eqv : ((z : Z(χ, α)) × Fin (count z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun zm ↦ j zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  classical
  obtain ⟨e, hr, he⟩ := spectralRectangle_good_enumeration eχ (fun z : Z(χ, α) ↦ z.val.1) old
  obtain ⟨C, hC⟩ := spectralRectangle_column_annihilator A x L hb count j eqv.injective e he (hc e hr) ε hε
  let S := (Finset.Iic C).preimage (fun z ↦ (e z).2) he.injOn
  refine ⟨S, fun z hS hz Ψ hΨ ↦ ?_⟩
  have hcol : C < (e z).2 := by simpa [S] using hS
  let i := j z ⟨0, hz⟩
  have h := hC z hcol ⟨0, hz⟩ Ψ hΨ
  change ‖(L i).comp A‖ ≤ ε * ‖L i - Ψ‖ at h
  let c := ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g ∂μ𝔽
  have eig : (L i).comp A = c • L i := by
    ext v
    have top := spectralStripConvolution_jet_top a hα hs₁ χ L hj φ z ⟨0, hz⟩ v
      (fun k hk ↦ False.elim (Nat.not_lt_zero k.val hk))
    rw [(spectralConvolution_mellin_integrable φ (χ z.val.1) (shift(z.val.2.1, z.val.2.2))).2] at top
    exact top
  rw [eig, spectralRectangle_norm_smul] at h
  let D := spectralSobolevDualEmbedding F a (neg_le_self hα) hs₀(hs₁)
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := F) a (neg_le_self hα) hs₀(hs₁)).1
  have hdv : ‖L i‖ = ‖u i‖ := by
    have hd := hD.dist_eq (L i) 0
    simpa only [map_zero, dist_eq_norm, sub_zero, hj] using hd.symm
  have hdk : ‖L i - Ψ‖ = ‖(show W'(-α, α, s) from u i) - D Ψ‖ := by
    have hd := hD.dist_eq (L i) Ψ
    simpa only [dist_eq_norm, hj] using hd.symm
  rwa [hdv, hdk] at h
#print axioms spectralRectangles_actual_necessary
end RiemannMasullo
namespace RiemannMasullo
local notation "S" => 𝓢(ℝ, ℂ)
private def phase (t x : ℝ) : ℂ := Complex.exp (((t : ℂ) * Complex.I) * x)
private theorem phase_smooth (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phase t) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
private theorem phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]
private theorem phase_iters (t : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (phase t) x = ((t : ℂ) * Complex.I)^n * phase t x := by
  induction n generalizing x with
  | zero => simp
  | succ n h =>
    rw [iteratedDeriv_succ, funext h]
    let c := (t : ℂ) * Complex.I
    have h1 : HasDerivAt (phase t) (c * phase t x) x := by
      have h := (((Complex.hasDerivAt_exp (c * (x : ℂ))).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_mul c)).comp_ofReal)
      change HasDerivAt (fun y : ℝ ↦ Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x
      simpa [mul_comm] using h
    change deriv (fun y ↦ c^n * phase t y) x = c^(n+1) * phase t x
    rw [(h1.const_mul _).deriv, pow_succ]; ring
private def atom (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (t : ℝ) : S :=
  (hc.mul_right (f' := phase (-t))).toSchwartzMap (b.smooth'.mul (phase_smooth (-t)))
private theorem atom_seminorm (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (k n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, (SchwartzMap.seminorm ℂ k n) (atom b hc t) ≤ C*(1+|t|)^n := by
  classical
  let B (i : ℕ) := (n.choose i : ℝ) * (SchwartzMap.seminorm ℂ k i) b
  have hB (i) : 0 ≤ B i := mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  refine ⟨∑ i ∈ Finset.range (n+1), B i, Finset.sum_nonneg (fun i _ ↦ hB i), fun t ↦ ?_⟩
  apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity)
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖x‖^k * ‖iteratedDeriv n ((b : ℝ → ℂ) * phase (-t)) x‖ ≤ _
  rw [iteratedDeriv_mul (b.smooth n).contDiffAt ((phase_smooth (-t)).of_le (by simp)).contDiffAt]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [phase_iters, norm_mul, norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
    phase_norm, mul_one, Complex.norm_real, norm_neg, Complex.norm_natCast, Real.norm_eq_abs t]
  have hx := SchwartzMap.le_seminorm ℂ k i b x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hx
  have htp : |t|^(n-i) ≤ (1+|t|)^n :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |t| ≤ 1+|t|) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Nat.sub_le _ _))
  calc
    _ = ((n.choose i : ℝ)*(‖x‖^k*‖iteratedDeriv i (b : ℝ → ℂ) x‖))*|t|^(n-i) := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) htp (by positivity) (hB i)
private theorem orbitBound (b : S) (hc : HasCompactSupport (b : ℝ → ℂ)) (q : Seminorm ℂ S)
    (hq : Continuous q) : ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ t : ℝ, q (atom b hc t) ≤ C*(1+|t|)^k := by
  classical
  let P := schwartzSeminormFamily ℂ ℝ ℂ
  obtain ⟨s,D,_,hD⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  choose K hK hbound using atom_seminorm b hc
  let k := s.sup Prod.snd
  let C := ∑ i ∈ s, K i.1 i.2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ ↦ hK i.1 i.2)
  refine ⟨(D:ℝ)*C, by positivity, k, fun t ↦ ?_⟩
  refine (hD (atom b hc t)).trans ?_
  change (D:ℝ)*(s.sup P) (atom b hc t) ≤ _
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ D.coe_nonneg
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro i hi
  exact (hbound i.1 i.2 t).trans (mul_le_mul (Finset.single_le_sum (f := fun j : ℕ × ℕ ↦ K j.1 j.2)
    (fun j _ ↦ hK j.1 j.2) hi)
    (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Finset.le_sup hi)) (by positivity) hC)
open IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μ" => (ideleClassTamagawaMeasure ℚ)
private def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
private def inletBump : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
private def bumpS (b : ContDiffBump (0 : ℝ)) : S :=
  (b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
private theorem bumpS_compact (b : ContDiffBump (0 : ℝ)) : HasCompactSupport (bumpS b : ℝ → ℂ) :=
  b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)
private def liftProfile {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ)
    (hp : IsProperMap (fun g : G ↦ Real.log ((m g).val : ℝ)))
    (u : ℝ → ℂ) (hs : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    BruhatCompactSupport G := by
  let l (g : G) := Real.log ((m g).val : ℝ)
  have smooth := isBruhatSmooth_logProfile (G := G) (f := u) m hs
  have compact : HasCompactSupport (fun g : G ↦ u (l g)) :=
    HasCompactSupport.intro (K := l ⁻¹' tsupport u) (hp.isCompact_preimage hc)
      (fun g hg ↦ image_eq_zero_of_notMem_tsupport hg)
  exact ⟨_, (mem_bruhatSmoothSubmodule_iff _).2 smooth, compact⟩
private def radialTest (f : S) : BruhatCompactSupport Cℚ := by
  let m : Cℚ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩
  have hp : IsProperMap (logIdeleClassNorm ℚ) := by
    rw [show logIdeleClassNorm ℚ = (fun g ↦ ((thetaLog ℚ) g).toAdd) from funext (fun g ↦ (thetaLog_apply (F := ℚ) g).symm)]
    exact isProperMap_thetaLog ℚ
  exact liftProfile (G := Cℚ) m hp ((bumpS cutBump : ℝ → ℂ) * (f : ℝ → ℂ))
    ((bumpS cutBump).smooth'.mul f.smooth') ((bumpS_compact _).mul_right)
private def scalarEval (t : ℝ) : S →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ volume).comp (SchwartzMap.smulLeftCLM ℂ
    (fun x ↦ (bumpS cutBump) x * phase t x))
private theorem scalarEval_eq (t : ℝ) (f : S) : scalarEval t f =
    ∫ x : ℝ, (bumpS cutBump) x * f x * phase t x := by
  rw [scalarEval,ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
  have hh : (fun x ↦ (bumpS cutBump) x * phase t x).HasTemperateGrowth :=
    ((bumpS_compact cutBump).mul_right).hasTemperateGrowth ((bumpS cutBump).smooth'.mul (phase_smooth t))
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [SchwartzMap.smulLeftCLM_apply_apply hh, smul_eq_mul]; ring
private def radScale : ℝ := ((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal
private theorem radScale_pos : 0 < radScale := by
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  exact ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top ν _)
private theorem radialMellin (t : ℝ) (f : S) :
    (∫ g : Cℚ, (radialTest f).val g * ideleClassNormTwist (1 : PontryaginDual Cℚ)
      ((t:ℂ)*Complex.I) g ∂μ) = (radScale:ℂ)* scalarEval t f := by
  let l := logIdeleClassNorm ℚ
  let U (x : ℝ) := (bumpS cutBump) x * f x * phase t x
  have hl : Continuous l := ((NNReal.continuous_coe.comp Units.continuous_val).comp
      (isProperMap_ideleClassNorm ℚ).continuous).log fun g ↦ (show 0 < ((ideleClassNorm ℚ g).val : ℝ) from NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hU : Continuous U := ((bumpS cutBump).continuous.mul f.continuous).mul (phase_smooth t).continuous
  have he (g : Cℚ) : ideleClassNormTwist (1 : PontryaginDual Cℚ) ((t:ℂ)*Complex.I) g = phase t (l g) := by
    change (1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ):ℂ) ^ ((t:ℂ)*Complex.I)) = _
    have hp : 0 < ((ideleClassNorm ℚ g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
    rw [one_mul]
    exact congrArg Complex.exp (mul_comm _ _)
  simp_rw [he]
  change (∫ g : Cℚ, U (l g) ∂μ) = _
  rw [← integral_map hl.aemeasurable hU.aestronglyMeasurable,
    show (ideleClassTamagawaMeasure ℚ).map l = _ from classTamagawa_map_log_norm (F := ℚ), integral_smul_nnreal_measure,
    NNReal.smul_def,Complex.real_smul,scalarEval_eq]
  rfl
private theorem scalarEval_on_atom (t : ℝ) :
    scalarEval t (atom (bumpS inletBump) (bumpS_compact _) t) = ((∫ x : ℝ, inletBump x : ℝ) : ℂ) := by
  rw [scalarEval_eq]
  refine Eq.trans ?_ (show (∫ x : ℝ, ((inletBump x : ℝ):ℂ)) = _ from integral_ofReal)
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  change (cutBump x : ℂ) * ((inletBump x : ℂ) * phase (-t) x) * phase t x = _
  by_cases hx : inletBump x = 0
  · simp [hx]
  · have hm := subset_tsupport _ (show x ∈ support inletBump from hx)
    rw [inletBump.tsupport_eq, Metric.mem_closedBall] at hm
    have hcut : cutBump x = 1 := cutBump.one_of_mem_closedBall (hm.trans (by norm_num [cutBump,inletBump]))
    simp only [hcut, Complex.ofReal_one, one_mul, mul_assoc, phase, ← Complex.exp_add]
    simp
#print axioms orbitBound
#print axioms radialMellin
#print axioms scalarEval_on_atom
/-- Testing all compact smooth profiles bounds the sample weights by one polynomial. -/
private theorem mellin_polynomial_bound {Z : Type*} (t w : Z → ℝ) (hw : ∀ z, 0 ≤ w z)
    (h : ∀ φ : BruhatCompactSupport Cℚ, BddAbove (range (fun z ↦
      ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (1 : PontryaginDual Cℚ) ((t z:ℂ)*Complex.I) g ∂μ‖ * w z))) :
    ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ z, w z ≤ C*(1+|t z|)^k := by
  have : CompleteSpace S := completeSpace_schwartzMap
  have : (uniformity S).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero S]; infer_instance
  let P (z : Z) := (normSeminorm ℂ ℂ).comp
    ((((w z : ℂ) * (radScale : ℂ)) • scalarEval (t z)).toLinearMap)
  have he (z : Z) (f : S) : P z f = w z * (radScale * ‖scalarEval (t z) f‖) := by
    change ‖((w z : ℂ)*(radScale:ℂ)) • scalarEval (t z) f‖ = _
    rw [norm_smul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (hw _),Real.norm_of_nonneg radScale_pos.le,mul_assoc]
  have hbd : BddAbove (range P) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro f
    obtain ⟨B,hB⟩ := h (radialTest f)
    refine ⟨B, forall_mem_range.mpr (fun z ↦ ?_)⟩
    have hz := hB (mem_range_self z)
    rw [he,mul_comm]
    rwa [radialMellin,norm_mul,Complex.norm_real,Real.norm_of_nonneg radScale_pos.le] at hz
  have hcont : Continuous (⨆ z, P z : Seminorm ℂ S) := by
    rw [Seminorm.coe_iSup_eq hbd]
    exact Seminorm.continuous_iSup P (fun z ↦ (((w z:ℂ)*(radScale:ℂ)) • scalarEval (t z)).continuous.norm) hbd
  obtain ⟨A,hA,k,hk⟩ := orbitBound (bumpS inletBump) (bumpS_compact _) _ hcont
  let c : ℝ := ∫ x : ℝ, inletBump x
  have hc : 0 < c := inletBump.integral_pos
  refine ⟨A / (radScale*c), div_nonneg hA (mul_nonneg radScale_pos.le hc.le), k, fun z ↦ ?_⟩
  have h₁ := (le_ciSup hbd z) (atom (bumpS inletBump) (bumpS_compact _) (t z))
  rw [he,scalarEval_on_atom,Complex.norm_real,Real.norm_of_nonneg hc.le] at h₁
  have h₂ := h₁.trans (hk (t z))
  change w z * (radScale*c) ≤ _ at h₂
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos radScale_pos hc)).2 h₂
#print axioms mellin_polynomial_bound
end RiemannMasullo
namespace RiemannMasullo
set_option quotPrecheck false
open IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
variable (a : ℝ)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "H(" hα ", " hs ")" => spectralSobolevQuotient ℚ a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs))
set_option maxHeartbeats 650000 in
set_option backward.isDefEq.respectTransparency false in
/-- The conditioning of the rational central-row blocks grows at most polynomially in height. -/
private theorem rational_site_polynomial
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (eχ : PontryaginDual C₁ ↪ ℕ) (old : Z(χ, α) ↪ ℕ × ℕ)
    (x : SpectralStripJetIndex χ a α s → H(hα, hs))
    (L : SpectralStripJetIndex χ a α s → StrongDual ℂ H(hα, hs))
    (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ i, spectralSobolevDualEmbedding ℚ a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs)) (L i) =
      (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) i).toLp
        (spectralZeroJet (χ i.val.1) i.val.2.1 i.val.2.2.1 i.val.2.2.2)) :
    let count (z : Z(χ, α)) := N(χ, α, s, z)
    let j (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex χ a α s :=
      ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
    (∀ (φ : BruhatCompactSupport Cℚ) (e : Z(χ, α) ↪ ℕ × ℕ), (∀ z, (e z).1 = eχ z.val.1) →
      SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum
        (spectralConvolution (F := ℚ) a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs)) φ) x L
        (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) count j)) →
    ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ z : Z(χ, α), χ z.val.1 = 1 → z.val.2.1 = 0 → ∀ hz : 0 < count z,
      ∀ Ψ : StrongDual ℂ H(hα, hs), (∀ n, Ψ (x (j z n)) = 0) →
        ‖L (j z ⟨0, hz⟩)‖ ≤ C*(1+|z.val.2.2|)^k * ‖L (j z ⟨0,hz⟩) - Ψ‖ := by
  intro count j hc
  classical
  let Z₀ := {z : Z(χ, α) // χ z.val.1 = 1 ∧ z.val.2.1 = 0 ∧ 0 < count z}
  let i (z : Z₀) := j z.val ⟨0,z.property.2.2⟩
  let Y := (z : Z₀) × {Ψ : StrongDual ℂ H(hα,hs) // ∀ n, Ψ (x (j z.val n)) = 0}
  let d (y : Y) := ‖L (i y.1) - y.2.val‖
  have hcond (y : Y) : 1 ≤ d y * ‖x (i y.1)‖ := by
    have h := (L (i y.1) - y.2.val).le_opNorm (x (i y.1))
    simpa only [sub_apply, hb.1, y.2.property ⟨0,y.1.property.2.2⟩,sub_zero,norm_one,i] using h
  have hd (y : Y) : 0 < d y := by
    refine lt_of_le_of_ne (norm_nonneg (L (i y.1) - y.2.val)) (fun h ↦ ?_)
    have h₀ := hcond y
    rw [←h,zero_mul] at h₀
    linarith
  let w (y : Y) := ‖L (i y.1)‖ / d y
  let t (y : Y) := y.1.val.val.2.2
  let D := spectralSobolevDualEmbedding ℚ a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs))
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := ℚ) a (neg_le_self hα)
    (le_of_lt (zero_lt_one.trans hs))).1
  have hM (φ : BruhatCompactSupport Cℚ) : BddAbove (range (fun y : Y ↦
     ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (1 : PontryaginDual Cℚ) ((t y:ℂ)*Complex.I) g
       ∂ideleClassTamagawaMeasure ℚ‖ * w y)) := by
    let M (z : Z₀) := ‖∫ g : Cℚ, φ.val g * ideleClassNormTwist (1 : PontryaginDual Cℚ)
      ((z.val.val.2.2:ℂ)*Complex.I) g ∂ideleClassTamagawaMeasure ℚ‖
    obtain ⟨S, hS⟩ := spectralRectangles_actual_necessary (F := ℚ) a χ hα hs φ eχ old x L hb hj (hc φ) 1 one_pos
    let exc := S.preimage (fun z : Z₀ ↦ z.val) Subtype.val_injective.injOn
    obtain ⟨B,hB⟩ := (exc.finite_toSet.image (fun z ↦ M z * (‖L (i z)‖ * ‖x (i z)‖))).bddAbove
    refine ⟨max B 1, forall_mem_range.mpr (fun y ↦ ?_)⟩
    change M y.1 * w y ≤ _
    by_cases hy : y.1.val ∈ S
    · refine le_trans ?_ (le_max_left _ _)
      have hm : y.1 ∈ exc := (Finset.mem_preimage).mpr hy
      apply le_trans _ (hB ⟨y.1,hm,rfl⟩)
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (div_le_iff₀ (hd y)).mpr
      calc ‖L (i y.1)‖ ≤ ‖L (i y.1)‖ * (d y * ‖x (i y.1)‖) :=
            le_mul_of_one_le_right (norm_nonneg (L (i y.1))) (hcond _)
           _ = _ := by ring
    · refine le_trans ?_ (le_max_right _ _)
      change M y.1 * (‖L (i y.1)‖ / d y) ≤ 1
      rw [← mul_div_assoc, div_le_one (hd y)]
      have h := hS y.1.val hy y.1.property.2.2 y.2.val y.2.property
      have htw : ideleClassNormTwist (χ y.1.val.val.1) (shift(y.1.val.val.2.1, y.1.val.val.2.2)) =
          ideleClassNormTwist (1 : PontryaginDual Cℚ) ((y.1.val.val.2.2 : ℂ)*Complex.I) := by
        rw [y.1.property.1,y.1.property.2.1,Complex.ofReal_zero,zero_add]
      rw [htw,one_mul] at h
      have hn : ‖D (L (i y.1))‖ = ‖L (i y.1)‖ := by
        have e := hD.dist_eq (L (i y.1)) 0
        simpa only [D,map_zero,dist_eq_norm,sub_zero] using e
      have hn' : ‖D (L (i y.1)) - D y.2.val‖ = d y := by
        have e := hD.dist_eq (L (i y.1)) y.2.val
        simpa only [D,d,dist_eq_norm] using e
      change M y.1 * ‖_‖ ≤ ‖_ - D y.2.val‖ at h
      change M y.1 * ‖L (i y.1)‖ ≤ d y
      rw [← hn, ← hn']
      simpa only [D,hj] using h
  obtain ⟨C,hC,k,hk⟩ := mellin_polynomial_bound t w (fun y ↦ div_nonneg (norm_nonneg (L (i y.1))) (hd y).le) hM
  refine ⟨C,hC,k,fun z hχ hz hcount Ψ hΨ ↦ ?_⟩
  let y : Y := ⟨⟨z,hχ,hz,hcount⟩,Ψ,hΨ⟩
  exact (div_le_iff₀ (hd y)).mp (hk y)
#print axioms rational_site_polynomial
end RiemannMasullo
namespace RiemannMasullo
open IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "l" => (logIdeleClassNorm ℚ)
local notation "ν" => (intervalSobolevMeasure (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-(0:ℝ)) 0 4 true)
private theorem phase_first_moment : MemLp (fun g : Cℚ ↦ (l g : ℂ)) 2 ν := by
  let m : Cℚ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ,(isProperMap_ideleClassNorm ℚ).continuous⟩
  have hm : IsModulation (G := Cℚ) m := by
    constructor
    · exact isProperMap_ideleClassNorm ℚ
    · exact ideleClassNorm_ne_one (F := ℚ)
  have hs : Surjective m := (ideleGroup_quotient.{_,0} ℚ).2.2.2.2.2.2.2.2.2.1
  have hl : Continuous (fun g : Cℚ ↦ (l g:ℂ)) := Complex.continuous_ofReal.comp
    (continuous_logModule' (G := Cℚ) m)
  have hmval (x : Cℚ) : m x = ideleClassNorm ℚ x := rfl
  have h := spectralLineJet_memLp_of_norm_sq (G := Cℚ) m hm hs (ideleClassTamagawaMeasure ℚ) 4 1
    (by norm_num) _ hl (fun g ↦ by simp [Complex.norm_real,Real.norm_eq_abs,sq_abs,hmval,logIdeleClassNorm])
  simpa only [intervalSobolevMeasure,ite_true,neg_zero,intervalSobolevDensity,mul_zero,zero_mul,
    Real.exp_zero,max_self,one_mul,hmval,logIdeleClassNorm] using h
/-- The first log moment gives a height-independent Lipschitz constant in the actual weighted L² space. -/
private theorem actual_phase_lipschitz :
    ∃ B ≥ (0:ℝ), ∀ (t u : ℝ) (f g : Lp ℂ 2 ν),
      (⇑f =ᵐ[ν] fun x ↦ phase t (l x)) → (⇑g =ᵐ[ν] fun x ↦ phase u (l x)) →
      ‖f-g‖ ≤ B*|t-u| := by
  let h := phase_first_moment.toLp (fun g : Cℚ ↦ (l g:ℂ))
  refine ⟨‖h‖,norm_nonneg _,fun t u f g hf hg ↦ ?_⟩
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := h)
  filter_upwards [Lp.coeFn_sub f g, hf,hg,MemLp.coeFn_toLp phase_first_moment] with x hs hf hg hz
  change (f - g) x = f x-g x at hs
  rw [hs,hf,hg,hz,Complex.norm_real]
  have h₁ : phase t (l x)-phase u (l x) = (phase (t-u) (l x)-1)*phase u (l x) := by
    simp only [phase,sub_mul,one_mul,←Complex.exp_add,Complex.ofReal_sub]
    congr 2; ring
  have h₂ : phase (t-u) (l x) = Complex.exp (Complex.I * ((((t-u)*l x):ℝ):ℂ)) := by
    simp only [phase,Complex.ofReal_mul]; congr 1; ring
  rw [h₁,norm_mul,phase_norm,mul_one,h₂]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (t-u)*l x)).trans ?_
  rw [norm_mul,Real.norm_eq_abs (t-u)]
#print axioms actual_phase_lipschitz
end RiemannMasullo
namespace RiemannMasullo
namespace RationalOrdinates
set_option quotPrecheck false
open IsDedekindDomain NumberField
open scoped NNReal ENNReal NumberField.AdeleRing
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁" => (ideleClassNorm ℚ).ker
local notation "J(" χ ")" => SpectralStripJetIndex χ (1/2) 0 4
local notation "H" => spectralSobolevQuotient ℚ (1/2) (neg_le_self (show 0 ≤ (0:ℝ) from le_rfl))
  (show 0 ≤ (4:ℝ) from by norm_num)
local notation "ν" => (intervalSobolevMeasure (ideleClassTamagawaMeasure ℚ) (logIdeleClassNorm ℚ) (-(0:ℝ)) 0 4 true)
local notation "ζ₀" => {t : ℝ // riemannZeta (1/2 + (t:ℂ)*Complex.I) = 0}
local notation "order(" ψ ", " b ", " t ")" => meromorphicOrderAt (continuedCompletedHeckeL ψ)
  (((1/2 + (b:ℝ) : ℝ):ℂ) + (t:ℂ)*Complex.I)
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-(0:ℝ)) 0 ∧ 0 < order(χ z.1, z.2.1, z.2.2)}
local notation "n(" χ ", " z ")" => spectralStripMultiplicity 0 4 (z).val.2.1
  (order(χ (z).val.1, (z).val.2.1, (z).val.2.2)).untop₀.toNat
local notation "D" => spectralSobolevDualEmbedding ℚ (1/2)
  (neg_le_self (show 0 ≤ (0:ℝ) from le_rfl)) (show 0 ≤ (4:ℝ) from by norm_num)
private theorem crit_count (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : χ 1 = 1) (v : ζ₀) :
    0 < spectralStripMultiplicity 0 4 0 (order(χ 1, 0, v.val)).untop₀.toNat := by
  obtain ⟨j,hj⟩ := spectralLineJet_rational_zero_index χ hχ v v.property
  have hm := j.property
  rw [hj] at hm
  rw [spectralStripMultiplicity_boundary (show (0:ℝ) ≤ 0 from le_rfl) (Or.inr rfl),
    lt_spectralBoundaryMultiplicity]
  have h := (lt_spectralBoundaryMultiplicity 2 _ _).mp hm
  exact ⟨by simpa only [add_zero] using h.1, by norm_num⟩
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Conditional arithmetic consequence of the trace rectangle estimate on the given quotient basis. -/
private theorem rational_zeta_ordinate_separation
    (χ : PontryaginDual C₁ → PontryaginDual Cℚ) (hχ : χ 1 = 1)
    (eχ : PontryaginDual C₁ ↪ ℕ) (old : Z(χ) ↪ ℕ × ℕ)
    (x : J(χ) → H) (L : J(χ) → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x L)
    (hj : ∀ i, D (L i) = (spectralStripJet_memLp χ (by norm_num : (0:ℝ) ≤ 0)
      (by norm_num : (0:ℝ) ≤ 4) i).toLp
      (spectralZeroJet (χ i.val.1) i.val.2.1 i.val.2.2.1 i.val.2.2.2)) :
    let j (z : Z(χ)) (m : Fin (n(χ,z))) : J(χ) :=
      ⟨(z.val.1,z.val.2.1,z.val.2.2,m.val),m.isLt⟩
    (∀ (φ : BruhatCompactSupport Cℚ) (e : Z(χ) ↪ ℕ × ℕ), (∀ z, (e z).1 = eχ z.val.1) →
      SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum
        (spectralConvolution (F := ℚ) (1/2) (neg_le_self (show (0:ℝ) ≤ 0 from le_rfl))
          (by norm_num : (0:ℝ) ≤ 4) φ) x L
        (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
        (fun z ↦ n(χ,z)) j)) →
    ∃ c > (0 : ℝ), ∃ k : ℕ, ∀ t u : ζ₀, t ≠ u → c ≤ (1+|t.val|)^k * |t.val-u.val| := by
  intro j hc
  classical
  let i (v : ζ₀) : J(χ) := ⟨(1,0,v.val,0),crit_count χ hχ v⟩
  let z (v : ζ₀) : Z(χ) := ⟨(1,0,v.val),SpectralStripJetIndex.mem_strip_order_pos le_rfl (i v)⟩
  obtain ⟨C,hC,k,hk⟩ := rational_site_polynomial (1/2) χ le_rfl (show 1 < (4:ℝ) by norm_num)
    eχ old x L hb hj hc
  let f (v : ζ₀) := D (L (i v))
  have hf (v : ζ₀) : (f v : Cℚ → ℂ) =ᵐ[ν] fun g ↦ phase v.val (logIdeleClassNorm ℚ g) := by
    dsimp only [f]
    rw [hj]
    refine (MemLp.coeFn_toLp (spectralStripJet_memLp χ (show (0:ℝ) ≤ 0 from le_rfl) (show (0:ℝ) ≤ 4 by norm_num) (i v))).trans (.of_forall fun g ↦ ?_)
    change spectralZeroJet (χ 1) 0 v.val 0 g = _
    rw [hχ,stripProfile_jet]
    simp only [pow_zero,mul_one,Complex.ofReal_zero,zero_add,phase]
    exact one_mul _
  have hD := (spectralSobolevDualEmbedding_isometry_range (F := ℚ) (1/2) (neg_le_self (show (0:ℝ) ≤ 0 from le_rfl))
    (by norm_num : (0:ℝ) ≤ 4)).1
  have hn (v : ζ₀) : ‖f v‖ = ‖L (i v)‖ := by
    simpa only [f,map_zero,dist_eq_norm,sub_zero] using hD.dist_eq (L (i v)) 0
  obtain ⟨B,hB,hLip⟩ := actual_phase_lipschitz
  by_cases he : Nonempty ζ₀
  · let v := Classical.choice he
    have hnz : L (i v) ≠ 0 := by
      intro hz
      have h := hb.1 (i v)
      rw [hz,zero_apply] at h
      exact zero_ne_one h
    have hpos : 0 < ‖L (i v)‖ := (norm_pos_iff (a := L (i v))).mpr hnz
    have eql (t : ζ₀) : ‖f t‖ = ‖f v‖ := by
      have he : ∀ᵐ g ∂ν, ‖f t g‖ = ‖f v g‖ := by
        filter_upwards [hf t,hf v] with g h₁ h₂; rw [h₁,h₂,phase_norm,phase_norm]
      exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h ↦ h.le)))
        (Lp.norm_le_norm_of_ae_le (he.mono (fun _ h ↦ h.ge)))
    let K := max 1 (C*B)
    have hK : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
    refine ⟨‖L (i v)‖ / K,div_pos hpos hK,k,fun t u htu ↦ ?_⟩
    have kill (m : Fin (n(χ,z t))) : L (i u) (x (j (z t) m)) = 0 := by
      apply hb.2.1
      intro hh
      exact htu (Subtype.ext (congrArg (fun q : J(χ) ↦ q.val.2.2.1) hh))
    have hbnd := hk (z t) hχ rfl (crit_count χ hχ t) (L (i u)) kill
    change ‖L (i t)‖ ≤ C*(1+|t.val|)^k * ‖L (i t)-L (i u)‖ at hbnd
    have hd : ‖f t-f u‖ = ‖L (i t)-L (i u)‖ := by
      simpa only [f,dist_eq_norm] using hD.dist_eq (L (i t)) (L (i u))
    rw [← hn, eql, hn, ← hd] at hbnd
    have htu' := hLip t.val u.val (f t) (f u) (hf t) (hf u)
    apply (div_le_iff₀ hK).mpr
    calc
      _ ≤ C*(1+|t.val|)^k * (B*|t.val-u.val|) :=
        hbnd.trans (mul_le_mul_of_nonneg_left htu' (by positivity))
      _ = (1+|t.val|)^k * |t.val-u.val| * (C*B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  · exact ⟨1,one_pos,0,fun t ↦ (he ⟨t⟩).elim⟩
#print axioms rational_zeta_ordinate_separation
end RationalOrdinates
end RiemannMasullo

open Lean Elab Command

private def auditRoot (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "unknown audit root {n}"
  let axioms ← Lean.collectAxioms n
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for ax in axioms do unless allowed.contains ax do throwError "unexpected axiom {ax} at {n}"
  let mut pending := #[n]
  let mut visited : Std.HashSet Name := {}
  let mut mods : Std.HashSet Name := {}
  let mut directSorry : Array Name := #[]
  while let some d := pending.back? do
    pending := pending.pop
    if visited.contains d then continue
    visited := visited.insert d
    let some info := env.find? d | continue
    if let some ix := env.getModuleIdxFor? d then
      mods := mods.insert (env.header.moduleNames[ix.toNat]!)
    let inType := info.type.getUsedConstants
    let inBody := if let some v := info.value? true then v.getUsedConstants else #[]
    if inType.contains ``sorryAx || inBody.contains ``sorryAx then
      directSorry := directSorry.push d
    for dep in inType ++ inBody do
      if !visited.contains dep then pending := pending.push dep
  if !directSorry.isEmpty then throwError "{n} reaches admissions at {directSorry}"
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; zero direct sorryAx dependencies; kernel axioms {axioms}"


run_cmd do
  for n in [``RiemannMasullo.rational_site_polynomial,
      ``RiemannMasullo.RationalOrdinates.rational_zeta_ordinate_separation] do
    auditRoot n
