module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2

import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Logic.Equiv.Nat

/-! # §10.2 assertions that are false as printed -/

@[expose] public noncomputable section

open MeasureTheory NumberField Set Filter Function Topology
open scoped NNReal ENNReal Topology

namespace RiemannMasullo

attribute [local instance] instIdeleClassMeasurableSpaceSec1

set_option quotPrecheck false

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "order(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "weight(" F ", " α ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity (-α) α s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)

local notation "lineWeight(" F ", " s ")" =>
  ((ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦ ENNReal.ofReal
    (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹)
local notation "floorCut(" s ", " N ")" => min N (Nat.floor ((s - 1) / 2 + 1))
local notation "stripFloor(" α ", " s ", " b ", " N ")" =>
  (if b = -α ∨ b = α then floorCut(s, N) else if b ∈ Ioo (-α) α then N else 0)

/-- Paper: Theorem 10.2.1.1, p. 440. For the printed index set the jets
belong to the negative line space and, in any enumeration, are the
functional half of a Markushevich basis of the theta quotient. -/
def Printed.spectralLineMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. The printed floor cutoff
makes each selected jet belong to the negative Sobolev space on the line. -/
def Printed.spectralLineJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
    k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
    MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s))

/-- The critical first-jet density has a divergent harmonic tail. -/
private theorem spectralLineJet_memLp_false_tail :
    ¬ Integrable (fun x : ℝ ↦ x ^ 2 * ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹) := by
  intro h
  apply not_integrableOn_Ioi_inv (a := 1)
  refine (h.integrableOn.const_mul 8).mono' (measurable_id.inv.aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun x hx ↦ ?_))
  have hx : 1 < x := hx
  have hx₀ : 0 < x := by linarith
  have hp : 0 < (1 + x ^ 2) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hbound : (1 + x ^ 2) ^ ((3 : ℝ) / 2) ≤ (2 * x) ^ 3 := by
    calc
      _ ≤ ((2 * x) ^ 2) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
      _ = (2 * x) ^ 3 := by
        rw [← Real.rpow_natCast (2 * x) 2, ← Real.rpow_mul (by positivity)]
        norm_num
  rw [Real.norm_of_nonneg (inv_pos.mpr hx₀).le, ← div_eq_mul_inv, ← mul_div_assoc,
    le_div_iff₀ hp, ← div_eq_inv_mul, div_le_iff₀ hx₀]
  linarith only [hbound, show (2 * x) ^ 3 = 8 * x ^ 2 * x by ring]

/-- At Sobolev degree three, the first logarithmic jet fails to be square integrable. -/
private theorem spectralLineJet_memLp_false_firstJet (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C𝔽(F)) (t : ℝ) :
    ¬ MemLp (spectralZeroJet χ 0 t 1) 2 (weight(F, 0, 3)) := by
  let : BorelSpace C𝔽(F) := ⟨rfl⟩
  let μ := ideleClassTamagawaMeasure F
  let l (g : C𝔽(F)) := Real.log ((ideleClassNorm F g).val : ℝ)
  let w (x : ℝ) := ((1 + x ^ 2) ^ ((3 : ℝ) / 2))⁻¹
  have hpos (x : ℝ) : 0 < (1 + x ^ 2) ^ ((3 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hw : Continuous w := ((continuous_const.add (continuous_id.pow 2)).rpow_const
    (fun x : ℝ ↦ Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity))).inv₀ fun x ↦ (hpos x).ne'
  have hl : Continuous l := tate_continuous_classNormReal.log fun g ↦ (tate_classNormReal_pos g).ne'
  intro h
  have hm : MemLp (spectralZeroJet χ 0 t 1) 2 (μ.withDensity fun g ↦ ENNReal.ofReal (w (l g))) := by
    simpa only [intervalSobolevDensity, neg_zero, mul_zero, zero_mul, Real.exp_zero, max_self, one_mul]
      using h
  have hnorm (g : C𝔽(F)) : ‖spectralZeroJet χ 0 t 1 g‖ ^ 2 = (l g) ^ 2 := by
    change ‖((χ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (0 + (t : ℂ) * Complex.I)) *
      (l g : ℂ) ^ 1‖ ^ 2 = _
    rw [norm_mul, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (tate_classNormReal_pos g)]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hg := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hμ : Integrable (fun g ↦ (l g) ^ 2 * w (l g)) μ := by
    apply ((integrable_withDensity_iff (hw.comp hl).measurable.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hg).congr
    exact .of_forall fun g ↦ by
      change ‖spectralZeroJet χ 0 t 1 g‖ ^ 2 * (ENNReal.ofReal (w (l g))).toReal = _
      rw [hnorm, ENNReal.toReal_ofReal (inv_pos.mpr (hpos (l g))).le]
  have hmap := (integrable_map_measure
    (g := fun x : ℝ ↦ x ^ 2 * w x) ((continuous_id.pow 2).mul hw).aestronglyMeasurable
    hl.measurable.aemeasurable).mpr hμ
  rw [show μ.map l = _ from classTamagawa_map_log_norm (F := F)] at hmap
  let ν := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hc : (ν univ).toNNReal ≠ 0 := (ENNReal.toNNReal_pos (NeZero.ne (ν univ)) (measure_ne_top ν univ)).ne'
  exact spectralLineJet_memLp_false_tail ((integrable_smul_measure
    (by exact_mod_cast hc) ENNReal.coe_ne_top).mp hmap)

/-- Paper: Theorem 10.2.1.1, p. 440. The trivial Hecke character of some
number field has a completed L-function with a zero of multiplicity at least two.
The intended witness is the splitting field of X³ − 2, whose Dedekind zeta
function contains the square of the two-dimensional Artin factor. -/
private theorem spectralLineJet_memLp_false_multipleZero :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (a t : ℝ),
      1 < order((1 : PontryaginDual C𝔽(F)), shift(a, t)) := by
  obtain ⟨F, _, _, z, _, _, hz⟩ := exists_completedDedekindZeta_multipleZero
  exact ⟨F, inferInstance, inferInstance, z.re, z.im, by simpa only [Complex.re_add_im] using hz⟩

/-- Paper: Theorem 10.2.1.1 and (10.2.1.6), p. 440. Take the splitting
field of X³−2, the trivial character, s = 3, and a+it a nontrivial zero of the
two-dimensional Artin factor. That factor occurs squared in the Dedekind
zeta function. The cutoff includes k = 1, whose squared norm has a 1/|x|
tail in the log norm coordinate x. -/
theorem Printed.spectralLineJet_memLp_false : ¬ Printed.spectralLineJet_memLp := by
  classical
  intro h
  obtain ⟨F, _, _, a, t, hz⟩ := spectralLineJet_memLp_false_multipleZero
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(F))
  have htriv : χ' 1 = 1 := Function.update_self ..
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases hω : ω = 1
    · subst ω
      rw [htriv]
      rfl
    · simpa [χ', Function.update_of_ne hω] using hχ ω
  apply spectralLineJet_memLp_false_firstJet F (χ' 1) t
  apply h F χ' hχ' a 3 (by norm_num) 1 t 1
  exact lt_min (htriv.symm ▸ hz) (by norm_num)


/-- Paper: Theorem 10.2.1.1, p. 440. The squared Artin factor of the
splitting field of X³−2 supplies a double zero. At s = 3 its first
derivative is among the printed jets and fails square integrability. -/
theorem Printed.spectralLineMarkushevichBasis_false :
    ¬ Printed.spectralLineMarkushevichBasis := by
  intro h
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  obtain ⟨hh, _⟩ := (h F χ hχ a s hs).2
  simpa only [neg_zero] using hh ⟨(ω, t, k), hk⟩

/-- Paper: Proposition 10.2.1.3, p. 443. The printed annulus statement uses
all derivative orders below the full zero multiplicity. -/
def Printed.spectralLineJet_annulus : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      let η := spectralZeroJet (χ ω) 0 t k
      ∃ h : MemLp η 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp η‖ ∧ ‖h.toLp η‖ ≤ C

/-- Paper: Proposition 10.2.1.3, p. 443. In the splitting field of X³−2
use the trivial character and a nontrivial zero of its squared two-dimensional
Artin factor. For s = 3 the printed full multiplicity includes k = 1 and the
squared norm diverges logarithmically. -/
theorem Printed.spectralLineJet_annulus_false : ¬ Printed.spectralLineJet_annulus := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  obtain ⟨_, _, h⟩ := hall F χ hχ a s hs
  exact (h ω t k (lt_of_lt_of_le hk (min_le_left _ _))).choose

/-- Paper: Proposition 10.2.1.3, p. 443. As printed, the a-line family
fails to be contained in an open ball of some positive radius. -/
def Printed.spectralLineJet_not_subset_ball : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < order(χ ω, shift(a, t)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. Take F = ℚ, a = 2 and s = 2.
All the completed Hecke L-functions are zero-free on this line by the
absolutely convergent Euler products and the nonvanishing gamma factors.
The resulting empty family is contained in every open ball. -/
theorem Printed.spectralLineJet_not_subset_ball_false :
    ¬ Printed.spectralLineJet_not_subset_ball := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, hn⟩ := hall ℚ χ hχ 2 2 (by norm_num)
  apply hn
  intro ω t k hk
  let z := shift((2 : ℝ), t)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hk

/-- Paper: Proposition 10.2.1.3, p. 443. One constant gives (10.2.1.12)
and the asserted noncontainment for the family with full multiplicities. -/
def Printed.spectralLineJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ // j.2.2 < order(χ j.1, shift(a, j.2.1))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.1.3, p. 443. For ℚ at a = 2 the zero
family is empty and hence lies in the open ball for every C > 0. -/
theorem Printed.spectralLineJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralLineJet_annulus_and_noncontainment := by
  intro hall
  apply Printed.spectralLineJet_not_subset_ball_false
  intro F _ _ χ hχ a s hs
  obtain ⟨C, hC, _, hn⟩ := hall F χ hχ a s hs
  refine ⟨C, hC, fun h ↦ hn ?_⟩
  intro j
  exact h j.val.1 j.val.2.1 j.val.2.2 j.property

/-- Paper: Terminology 10.2.1.2(2), p. 444. The printed implication says
that the functionals paired with a regular Markushevich family are bounded. -/
def Printed.spectralRegular_dual_bounded : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (x : ℕ → E) (Λ : ℕ → StrongDual ℂ E),
    (∀ i, Λ i (x i) = 1) → (∀ i j, i ≠ j → Λ j (x i) = 0) →
    Dense (Submodule.span ℂ (range x) : Set E) →
    (∀ v : E, (∀ i, Λ i v = 0) → v = 0) → IsRegularSpectralFamily x →
    ∃ C : ℝ, ∀ n, ‖Λ n‖ ≤ C

/-- Let `b` be a Hilbert basis indexed by `ℕ ⊕ ℕ`. Put `x (inl n) = b (inl n)` and
`x (inr n) = b (inl n) + (n + 1)⁻¹ • b (inr n)`. Then `x` has a total biorthogonal family `Λ`
with `‖Λ (inr n)‖ ≥ n + 1`. -/
private theorem Printed.spectralRegular_dual_bounded_false_exists {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis (ℕ ⊕ ℕ) ℂ E) :
    ∃ (x : ℕ ⊕ ℕ → E) (Λ : ℕ ⊕ ℕ → StrongDual ℂ E),
      (∀ i, Λ i (x i) = 1) ∧ (∀ i j, i ≠ j → Λ j (x i) = 0) ∧
      Dense (Submodule.span ℂ (Set.range x) : Set E) ∧
      (∀ v : E, (∀ i, Λ i v = 0) → v = 0) ∧ (∀ i, 1 ≤ ‖x i‖) ∧
      ∀ n : ℕ, (n : ℝ) + 1 ≤ ‖Λ (Sum.inr n)‖ := by
  classical
  have hb : ∀ i j, inner ℂ (b i) (b j) = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  have hn1 : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hne : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => Nat.cast_add_one_ne_zero n
  refine ⟨Sum.elim (fun n => b (Sum.inl n))
      (fun n => b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)),
    Sum.elim
      (fun n => innerSL ℂ (b (Sum.inl n)) - ((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n)))
      (fun n => ((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (n | n)
    · simp [hb, hn1, innerSL_apply_apply]
    · simp [hb, hn1, innerSL_apply_apply, inner_add_right, inner_smul_right, hne n]
  · rintro (n | n) (m | m) hij
    · have : m ≠ n := fun h => hij (by rw [h])
      simp [hb, innerSL_apply_apply, this]
    · simp [hb, innerSL_apply_apply]
    · by_cases hmn : m = n
      · subst hmn
        simp [hb, hn1, innerSL_apply_apply, inner_add_right, inner_smul_right, hne m]
      · simp [hb, innerSL_apply_apply, inner_add_right, inner_smul_right, hmn]
    · have : m ≠ n := fun h => hij (by rw [h])
      simp [hb, innerSL_apply_apply, inner_add_right, inner_smul_right, this]
  · rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff, ← b.dense_span]
    refine Submodule.topologicalClosure_mono (Submodule.span_le.mpr ?_)
    rintro _ ⟨(n | n), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inl n, rfl⟩
    · have hx : b (Sum.inr n) = ((n : ℂ) + 1) •
          ((b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)) - b (Sum.inl n)) := by
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ (hne n), one_smul]
      rw [SetLike.mem_coe, hx]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr n, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl n, rfl⟩))
  · intro v hv
    have hr : ∀ n : ℕ, inner ℂ (b (Sum.inr n)) v = 0 := by
      intro n
      have := hv (Sum.inr n)
      simpa [innerSL_apply_apply, hne n] using this
    have hl : ∀ n : ℕ, inner ℂ (b (Sum.inl n)) v = 0 := by
      intro n
      have := hv (Sum.inl n)
      simpa [innerSL_apply_apply, hr n] using this
    have hall : ∀ k, b.repr v k = 0 := by
      rintro (n | n)
      · rw [b.repr_apply_apply, hl n]
      · rw [b.repr_apply_apply, hr n]
    have hs := b.hasSum_repr v
    simp only [hall, zero_smul] at hs
    exact hs.unique hasSum_zero
  · rintro (n | n)
    · simp [hn1]
    · have h1 : inner ℂ (b (Sum.inl n))
          (b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n)) = 1 := by
        rw [inner_add_right, inner_smul_right, hb, hb]
        simp
      have h2 := norm_inner_le_norm (𝕜 := ℂ) (b (Sum.inl n))
        (b (Sum.inl n) + ((n : ℂ) + 1)⁻¹ • b (Sum.inr n))
      rw [h1, hn1, one_mul, norm_one] at h2
      simpa using h2
  · intro n
    have h := ContinuousLinearMap.le_opNorm (((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n)))
      (b (Sum.inr n))
    have hv : (((n : ℂ) + 1) • innerSL ℂ (b (Sum.inr n))) (b (Sum.inr n)) =
        ((n : ℕ) + 1 : ℕ) := by
      simp [hn1, innerSL_apply_apply]
    rw [hv, hn1, mul_one, Complex.norm_natCast] at h
    simpa using h

/-- Paper: Terminology 10.2.1.2(2), p. 444. In complex ℓ² take
x₂ₙ = e₂ₙ and x₂ₙ₊₁ = e₂ₙ + (n+1)⁻¹ e₂ₙ₊₁. If eⱼ* is coordinate evaluation,
the dual pair is e₂ₙ* − (n+1)e₂ₙ₊₁* and (n+1)e₂ₙ₊₁*. Both spans contain
the finite-support families, every x has norm at least one, and the dual
norms are unbounded. -/
theorem Printed.spectralRegular_dual_bounded_false :
    ¬ Printed.spectralRegular_dual_bounded := by
  intro h
  obtain ⟨x, Λ, h1, h2, h3, h4, h5, h6⟩ := Printed.spectralRegular_dual_bounded_false_exists
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℕ ⊕ ℕ => ℂ) 2)))
  let σ : ℕ ≃ ℕ ⊕ ℕ := Equiv.natSumNatEquivNat.symm
  obtain ⟨C, hC⟩ := h (lp (fun _ : ℕ ⊕ ℕ => ℂ) 2) (x ∘ σ) (Λ ∘ σ)
    (fun i => h1 (σ i)) (fun i j hij => h2 (σ i) (σ j) (σ.injective.ne hij))
    (by rwa [σ.surjective.range_comp])
    (fun v hv => h4 v (fun k => by simpa using hv (σ.symm k)))
    ⟨1, one_pos, fun i => h5 (σ i)⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hCn := hC (σ.symm (Sum.inr n))
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at hCn
  linarith [h6 n]

/-- Paper: Corollary 10.2.1.4, p. 444. The printed floor-indexed
line jets form a normalized basis in the image of the quotient dual. -/
def Printed.spectralLineMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j))

/-- Paper: Corollary 10.2.1.4, p. 444. The splitting-field example at
s = 3 includes a positive-order jet of infinite squared integral. -/
theorem Printed.spectralLineMarkushevichBasis_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_normalized := by
  intro hall
  apply Printed.spectralLineMarkushevichBasis_false
  intro F _ _ χ hχ a s hs
  obtain ⟨hc, h, x, Λ, hb, hΛ, _⟩ := hall F χ hχ a s hs
  exact ⟨hc, h, x, Λ, hb, hΛ⟩

/-- Paper: Theorem 10.2.1.1 and Remark 10.2.1.5, pp. 440, 444. The
asserted basis and its claimed primal normalization together give a bounded
regular family biorthogonal to the prescribed jets. -/
def Printed.spectralLineMarkushevichBasis_primal_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < floorCut(s, order(χ j.1, shift(a, j.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (lineWeight(F, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily x

/-- Paper: Remark 10.2.1.5, p. 444. Use the rational trivial component
at a = 1/2 and s = 2. For close simple zeta zeros the two evaluation
vectors approach one another in the dual norm. A vector pairing to one
with the first and zero with the second has norm at least the reciprocal
of their distance. The required primal bound fails. -/
theorem Printed.spectralLineMarkushevichBasis_primal_normalized_false :
    ¬ Printed.spectralLineMarkushevichBasis_primal_normalized := by
  intro hall
  apply Printed.spectralLineMarkushevichBasis_false
  intro F _ _ χ hχ a s hs
  obtain ⟨hc, h, x, Λ, hb, hΛ, _⟩ := hall F χ hχ a s hs
  exact ⟨hc, h, x, Λ, hb, hΛ⟩

/-- Paper: Theorem 10.2.2.1, p. 446. The jets indexed by the printed
interior and boundary multiplicities belong to the reciprocal strip space
and are the functionals of a Markushevich basis in any enumeration. -/
def Printed.spectralStripMarkushevichBasis : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let Q := spectralSobolevQuotient F a hI hs
      let D := spectralSobolevDualEmbedding F a hI hs
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        ∀ j, D (Λ j) = (h j).toLp (η j)

/-- Paper: Theorem 10.2.2.1, p. 446. On the singleton strip with s = 1
a Riemann zeta zero supplies a zeroth jet with divergent squared norm. -/
theorem Printed.spectralStripMarkushevichBasis_false :
    ¬ Printed.spectralStripMarkushevichBasis := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  let h := (hall F χ hχ a 0 s le_rfl (zero_lt_one.trans hs).le).2.choose
  exact h ⟨(ω, 0, t, k), by simpa using hk⟩

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5)–(10.2.2.6), p. 446.
The printed floor cutoff on the boundary and the full cutoff in the interior
are asserted to produce elements of the reciprocal strip space. -/
def Printed.spectralStripJet_memLp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 0 ≤ s → ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ) (k : ℕ),
    let N := order(χ ω, shift(a + b, t))
    ((b = -α ∨ b = α) ∧ k < min N (Nat.floor ((s - 1) / 2 + 1)) ∨
      b ∈ Ioo (-α) α ∧ k < N) →
    MemLp (spectralZeroJet (χ ω) b t k) 2 (weight(F, α, s))

/-- Paper: Theorem 10.2.2.1 and (10.2.2.5), p. 446. Take F = ℚ,
the trivial character, s = 1, α = b = 0 and a+it the first nontrivial
Riemann zeta zero with positive ordinate. The printed cutoff includes k = 0.
Its squared norm has a 1/|x| tail in log coordinates. -/
theorem Printed.spectralStripJet_memLp_false : ¬ Printed.spectralStripJet_memLp := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  apply hall F χ hχ a 0 s le_rfl (zero_lt_one.trans hs).le ω 0 t k
  exact Or.inl ⟨Or.inr rfl, by simpa using hk⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. The annulus uses the
reciprocal strip norm and the final open ball uses the negative line norm.
The ordinate is required to occur on the a-line as printed in (2). The
displacement in the displayed family is constrained by the multiplicity
at a+b+it, using the two cases of the definition on the same page. -/
def Printed.spectralStripJet_annulus_and_noncontainment : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s →
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      ∃ C : ℝ, 0 < C ∧
        (∀ j, ∃ h : MemLp (η j) 2 (weight(F, α, s)), C⁻¹ ≤ ‖h.toLp (η j)‖ ∧ ‖h.toLp (η j)‖ ≤ C) ∧
        ¬ (∀ j, ∃ h : MemLp (η j) 2 (weight(F, 0, s)), ‖h.toLp (η j)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. In ℚ take a = 2, s = 2
and α = 0. The family is empty, so it is contained in every open ball. -/
theorem Printed.spectralStripJet_annulus_and_noncontainment_false :
    ¬ Printed.spectralStripJet_annulus_and_noncontainment := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, _, hn⟩ := hall ℚ χ hχ 2 0 2 (by norm_num) (by norm_num)
  apply hn
  intro j
  have hj := j.property.1
  let z := shift((2 : ℝ), j.val.2.2.1)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ j.val.1) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ j.val.1) z = completedHeckeL (χ j.val.1) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ j.val.1)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ j.val.1) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ j.val.1) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ j.val.1)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hj

/-- Paper: Proposition 10.2.2.2, p. 447. The asserted noncontainment in an
open ball is specialized to the allowed singleton interval, where the
repeated boundary reference and the stated ambient line norm both apply. -/
def Printed.spectralStripJet_not_subset_ball_singleton : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∃ C : ℝ, 0 < C ∧
    ¬ (∀ (ω : PontryaginDual C₁(F)) (t : ℝ) (k : ℕ),
      k < min (order(χ ω, shift(a, t))) (Nat.floor ((s - 1) / 2 + 1)) →
      ∃ h : MemLp (spectralZeroJet (χ ω) 0 t k) 2 (weight(F, 0, s)),
        ‖h.toLp (spectralZeroJet (χ ω) 0 t k)‖ < C⁻¹)

/-- Paper: Proposition 10.2.2.2, p. 447. Take F = ℚ, a = 2, s = 2 and
I = {0}. On that strip every Hecke L-function is zero-free, so the empty
family is contained in every open ball. -/
theorem Printed.spectralStripJet_not_subset_ball_singleton_false :
    ¬ Printed.spectralStripJet_not_subset_ball_singleton := by
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  obtain ⟨_, _, hn⟩ := hall ℚ χ hχ 2 2 (by norm_num)
  apply hn
  intro ω t k hk
  let z := shift((2 : ℝ), t)
  have hz : 1 < z.re := by norm_num [z]
  have hval : continuedCompletedHeckeL (χ ω) z ≠ 0 := by
    rw [show continuedCompletedHeckeL (χ ω) z = completedHeckeL (χ ω) ⟨z, hz⟩ from
      (continuedCompletedHeckeL_spec (χ ω)).2 ⟨z, hz⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos (χ ω) (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re (χ ω) ⟨z, hz⟩)
  have horder := ((continuedCompletedHeckeL_spec (χ ω)).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval
  simp [z] at horder
  simp [horder] at hk

/-- Paper: Corollary 10.2.2.3, p. 447. The printed index requires an
ordinate from the a-line. The conclusion identifies the normalized family
in the reciprocal strip space and also locates the annihilator in the negative line space. -/
def Printed.spectralStripMarkushevichBasis_normalized : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℝ × ℕ //
        0 < order(χ j.1, shift(a, j.2.2.1)) ∧
        j.2.2.2 < stripFloor(α, s, j.2.1, order(χ j.1, shift(a + j.2.1, j.2.2.1)))}
      let η := fun j : J ↦ spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
      let hI := (neg_nonpos.mpr hα).trans hα
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let Q := spectralSobolevQuotient F a hI hs₀
      let D := spectralSobolevDualEmbedding F a hI hs₀
      Countable J ∧ ∃ (h : ∀ j, MemLp (η j) 2 (weight(F, α, s)))
        (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ ∧
        (∀ j, D (Λ j) = (h j).toLp (η j)) ∧ IsNormalizedSpectralFamily (fun j ↦ D (Λ j)) ∧
        (∀ L : StrongDual ℂ Q, ∃ v : Lp ℂ 2 (lineWeight(F, s)),
          (v : C𝔽(F) → ℂ) =ᵐ[ideleClassTamagawaMeasure F] (D L : C𝔽(F) → ℂ))

/-- Paper: Corollary 10.2.2.3, p. 447. For ℚ at a = α = s = 2 the
a-line has no zeros. A nontrivial critical-line Riemann zero with ordinate γ
supplies a nonzero quotient functional: the jet with b = -3/2 and t = γ
is strip-integrable in squared norm and vanishes on polar-free weighted theta
tests by the forward zeta integral factorization. An empty family cannot span
this dual. -/
theorem Printed.spectralStripMarkushevichBasis_normalized_false :
    ¬ Printed.spectralStripMarkushevichBasis_normalized := by
  intro hall
  apply Printed.spectralLineJet_memLp_false
  intro F _ _ χ hχ a s hs ω t k hk
  let h := (hall F χ hχ a 0 s le_rfl hs).2.choose
  exact h ⟨(ω, 0, t, k), Nat.zero_lt_of_lt (hk.trans_le (min_le_left _ _)), by simpa using hk⟩

/-- Paper: Theorem 10.2.1.1, proof after (10.2.1.7), p. 441.
As printed: the exponential-decay topology is generated by the seminorms
with weights exp(−m |log t|) on the Euler derivatives. In the library's
logarithmic coordinates the Euler derivative becomes the ordinary derivative.
See `existsUnique_spectralLineTestCompletion` and ERRATA F153. -/
def Printed.spectralLineTestTopology : Prop :=
  let E := PositiveRealExponentialDecay (Set.univ : Set ℝ)
  ∃ p : SeminormFamily ℂ E (ℕ × ℕ), WithSeminorms p ∧
    ∀ (m n : ℕ) (f : E), p (m, n) f =
      ⨆ x : ℝ, Real.exp (-(m : ℝ) * |x|) * ‖iteratedDeriv n f.val x‖

open scoped ContDiff in
/-- Paper: Theorem 10.2.1.1, proof after (10.2.1.7), p. 441.
In x = log t take a nonzero smooth bump h supported in (0, 1) and the
profiles fⱼ(x) = exp(−j/2) h(x − j). Every printed seminorm tends to zero,
since its weight is at most one. The genuine topology includes the zeroth
Schwartz seminorm after the exp(x) twist, which grows as exp(j/2). -/
theorem Printed.spectralLineTestTopology_false : ¬ Printed.spectralLineTestTopology := by
  rintro ⟨p, hp, hval⟩
  let E := PositiveRealExponentialDecay (univ : Set ℝ)
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let h (x : ℝ) : ℂ := b x
  have hc : HasCompactSupport h := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ h := Complex.ofRealCLM.contDiff.comp b.contDiff
  let u := hc.toSchwartzMap hd
  let f (t : ℝ) : E := ⟨fun x ↦ h (x - t),
    mem_logExponentialDecaySubmodule_of_hasCompactSupport univ
      (by
        have ht := hc.comp_homeomorph (Homeomorph.addRight (-t))
        change HasCompactSupport (fun x ↦ h (x + -t)) at ht
        simpa only [sub_eq_add_neg] using ht)
      (hd.comp (contDiff_id.sub contDiff_const))⟩
  have hb : Bornology.IsVonNBounded ℂ (range f) := by
    apply hp.isVonNBounded_iff_seminorm_bounded.mpr
    rintro ⟨m,n⟩
    let C := SchwartzMap.seminorm ℂ 0 n u
    refine ⟨C + 1, by positivity, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [hval]
    apply lt_of_le_of_lt (ciSup_le fun x ↦ ?_) (lt_add_one C)
    have hw : Real.exp (-(m : ℝ) * |x|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg m)) (abs_nonneg _))
    change _ * ‖iteratedDeriv n (fun z ↦ h (z - t)) x‖ ≤ C
    rw [iteratedDeriv_comp_sub_const]
    apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ u n (x - t)
  obtain ⟨T, -, hT⟩ := positiveRealExponentialDecay_continuous_inclusion univ (mem_univ (0 : ℝ))
  obtain ⟨R, hR, hbound⟩ := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp
    (hb.image T) (1, 0)
  have hlt := hbound (T (f R)) ⟨f R, ⟨R, rfl⟩, rfl⟩
  have hle := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T (f R)) 1 R
  have hx : T (f R) R = 1 := by
    rw [hT]
    change (b (R - R) : ℂ) = 1
    rw [sub_self, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    rfl
  rw [hx, norm_one, mul_one, pow_one, Real.norm_eq_abs, abs_of_pos hR] at hle
  exact (not_lt_of_ge hle) hlt

section BandProjection

set_option maxSynthPendingDepth 3

attribute [local instance] instIdeleClassBorelSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1 instIdeleClassHaarMeasureSec1

local instance instDualMeasurableSpaceSec2Printed (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

/-- Paper: Theorem 10.2.1.1, proof following (10.2.1.10), p. 443.
As printed: each in-band jet is in the range of the continuous adjoint of
the quotient band projection. This is the inclusion of the claimed spanning
family in the adjoint range. The band uses the characters χ |·|ⁱˣ
specified on p. 442(3). See `spectralLineIsotype_bandProjections` and ERRATA F155. -/
def Printed.spectralLineIsotype_bandAdjoint_contains_jets : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (basepoint : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)),
    IsSpectralBasepointChoice basepoint →
    ∀ (ω : PontryaginDual C₁(F)) (a s : ℝ) (hs : 1 < s) (m : ℕ)
      (ν : Measure (PontryaginDual C𝔽(F))),
    let μ := ideleClassTamagawaMeasure F
    ∀ hν : IsLCAPlancherelMeasure μ ν,
      let χ := basepoint ω
      let hI := le_rfl (a := (0 : ℝ))
      let hs₀ := le_of_lt (zero_lt_one.trans hs)
      let normMap : C𝔽(F) →ₜ* ℝ≥0ˣ :=
        ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
      let E := actionIsotype ((hardySobolevTranslation μ normMap 0 0 s hI hs₀).comp
        (ideleClassNorm F).ker.subtype) ω
      let N := (globalThetaSobolev F a hI hs₀).comap E.subtype
      let Q := spectralSobolevIsotypeQuotient F a hI hs₀ ω
      let U := (lcaFourier_unitary μ ν hν).exists.choose
      let B : Set Q := {q | ∃ f : E, q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μ,
        (u : C𝔽(F) → ℂ) =ᵐ[μ] (f.val : C𝔽(F) → ℂ) ∧
          ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand normMap χ (-(m : ℝ)) m → U u ψ = 0}
      ∀ P : Q →L[ℂ] Q, Set.range P = closure B →
        (∀ q y, y ∈ closure B → ‖q - P q‖ ≤ ‖q - y‖) →
        ∀ (t : ℝ) (k : ℕ), t ∈ Icc (-(m : ℝ)) m →
          k < floorCut(s, order(χ, shift(a, t))) →
          ∃ d : StrongDual ℂ Q, d ∈ Set.range (P.precomp ℂ) ∧
            ∀ f : E,
              let integrand := fun g ↦ f.val g * spectralZeroJet χ 0 t k g
              Integrable integrand μ ∧ d (N.mkQ f) = ∫ g, integrand g ∂μ

local notation "C" => C𝔽(ℚ)
local notation "logNorm" => (logIdeleClassNorm ℚ)
local notation "μQ" => ideleClassTamagawaMeasure ℚ
local notation "mQ" =>
  (⟨ideleClassNorm ℚ, (isProperMap_ideleClassNorm ℚ).continuous⟩ : C →ₜ* ℝ≥0ˣ)

-- The radial chart also appears in the §10.3 selected-evaluation counterexample (#6231).
private theorem continuous_ratLogNorm : Continuous logNorm :=
  Real.continuousOn_log.comp_continuous
    ((NNReal.continuous_coe.comp Units.continuous_val).comp (isProperMap_ideleClassNorm ℚ).continuous)
    (fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))).ne')

private def radialCharacter (r : ℝ) : PontryaginDual C where
  toFun g := Circle.exp (r * logNorm g)
  map_one' := by simp [logIdeleClassNorm]
  map_mul' g h := by
    change Circle.exp (r * Real.log (((ideleClassNorm ℚ (g * h)).val : ℝ≥0) : ℝ)) = _
    rw [map_mul (ideleClassNorm ℚ), Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))).ne'
      (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ h))).ne', mul_add, Circle.exp_add]
  continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul continuous_ratLogNorm)

private theorem radialCharacter_injective : Injective radialCharacter := by
  intro r s h
  by_contra hrs
  let x := Real.pi / (r - s)
  let a : ℝ≥0 := ⟨Real.exp x, (Real.exp_pos x).le⟩
  let a' : ℝ≥0ˣ := Units.mk0 a (by exact ne_of_gt (Real.exp_pos x))
  obtain ⟨g, hg⟩ := (ideleGroup_quotient.{_, 0} ℚ).2.2.2.2.2.2.2.2.2.1 a'
  have hlog : logNorm g = x := by
    change Real.log ((ideleClassNorm ℚ g).val : ℝ) = x
    rw [hg]
    exact Real.log_exp x
  have heq : Circle.exp (r * logNorm g) = Circle.exp (s * logNorm g) :=
    DFunLike.congr_fun h g
  rw [hlog] at heq
  apply Circle.exp_pi_ne_one
  calc
    Circle.exp Real.pi = Circle.exp ((r - s) * x) := by
      change Circle.exp Real.pi = Circle.exp ((r - s) * (Real.pi / (r - s)))
      rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hrs)]
    _ = Circle.exp (r * x) * (Circle.exp (s * x))⁻¹ := by
      rw [sub_mul, sub_eq_add_neg, Circle.exp_add, Circle.exp_neg]
    _ = 1 := by rw [heq, mul_inv_cancel]

private theorem continuous_radialCharacter : Continuous radialCharacter :=
  ContinuousMonoidHom.continuous_of_continuous_uncurry _ <|
    Circle.exp.continuous.comp (continuous_fst.mul (continuous_ratLogNorm.comp continuous_snd))

private theorem ratDual_singleton_null (ν : Measure (PontryaginDual C))
    (hν : ν.IsHaarMeasure) (χ : PontryaginDual C) : ν {χ} = 0 := by
  let : ν.IsHaarMeasure := hν
  let : BorelSpace (PontryaginDual C) := ⟨rfl⟩
  let K := radialCharacter '' Icc (0 : ℝ) 1
  have hc : IsCompact K := isCompact_Icc.image continuous_radialCharacter
  have hi : K.Infinite := (Set.Icc_infinite zero_lt_one).image radialCharacter_injective.injOn
  by_contra hn
  have hv : ν K = ⊤ := hi.meas_eq_top ⟨ν {χ}, hn, fun ψ _ ↦ by
    rw [Measure.haar_singleton ν ψ, Measure.haar_singleton ν χ]⟩
  exact hc.measure_lt_top.ne hv

private theorem ratLogNorm_proper : IsProperMap logNorm := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he : (e ∘ mQ) = logNorm := funext fun g ↦
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g)))).symm
  exact he ▸ e.isProperMap.comp (isProperMap_ideleClassNorm ℚ)

private theorem ratJet_nonzero_trivial_isotype (χ : PontryaginDual C)
    (hχ : ∀ k : C₁(ℚ), χ k.val = 1) :
    ∃ f : actionIsotype ((hardySobolevTranslation μQ mQ 0 0 2 le_rfl
      (by norm_num)).comp (ideleClassNorm ℚ).ker.subtype) 1,
      (∫ g, f.val g * spectralZeroJet χ 0 0 0 g ∂μQ) ≠ 0 := by
  let L := logNorm ⁻¹' Icc (-1 : ℝ) 1
  have hL : IsCompact L := ratLogNorm_proper.isCompact_preimage isCompact_Icc
  have hLm := hL.isClosed.measurableSet
  have hLfin := (hL.measure_lt_top (μ := μQ)).ne
  have hLpos : 0 < μQ L := by
    have hO : IsOpen (logNorm ⁻¹' Ioo (-1 : ℝ) 1) := isOpen_Ioo.preimage continuous_ratLogNorm
    exact (hO.measure_pos μQ ⟨1, by simp [logIdeleClassNorm]⟩).trans_le (measure_mono (preimage_mono Ioo_subset_Icc_self))
  let ρ (g : C) := ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm g))
  have hρ (g : C) : intervalSobolevDensity 0 0 2 (logNorm g) = 1 + (logNorm g) ^ 2 := by
    norm_num [intervalSobolevDensity]
  have hρm : Measurable ρ := by
    simp_rw [ρ, hρ]
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.add (continuous_ratLogNorm.pow 2)) |>.measurable
  let μW := (μQ).withDensity ρ
  have hac : μQ ≪ μW :=
    withDensity_absolutelyContinuous' hρm.aemeasurable (.of_forall fun g ↦ by
      dsimp [ρ]
      rw [hρ]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  have hca : μW ≪ μQ := withDensity_absolutelyContinuous _ _
  have hWfin : μW L ≠ ⊤ := by
    change (μQ).withDensity ρ L ≠ ⊤
    rw [withDensity_apply _ hLm]
    refine (lt_of_le_of_lt (lintegral_mono_ae (g := fun _ ↦ 2) ?_) ?_).ne
    · filter_upwards [ae_restrict_mem hLm] with g hg
      have hx : logNorm g ∈ Icc (-1 : ℝ) 1 := hg
      change ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm g)) ≤ 2
      rw [hρ, ← ENNReal.ofReal_ofNat]
      have hleft : 0 ≤ 1 + logNorm g := by linarith [hx.1]
      have hright : 0 ≤ 1 - logNorm g := by linarith [hx.2]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hleft hright])
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top (by norm_num) hLfin.lt_top
  let : IsFiniteMeasure (μW.restrict L) := isFiniteMeasure_restrict.mpr hWfin
  let w : C → ℂ := L.indicator fun g ↦ star (χ g : ℂ)
  have hw : MemLp w 2 μW :=
    (memLp_indicator_iff_restrict hLm.nullMeasurableSet).mpr <|
      MemLp.of_bound (continuous_star.comp (continuous_subtype_val.comp χ.continuous)).aestronglyMeasurable
        1 (.of_forall fun g ↦ by simp)
  let f := hw.toLp w
  refine ⟨⟨f, ?_⟩, ?_⟩
  · rw [mem_actionIsotype]
    intro k
    simp only [PontryaginDual.one_apply, Circle.coe_one, one_smul]
    apply Lp.ext
    apply hca.ae_eq
    have h₁ := hardySobolevTranslation_apply μQ mQ 0 0 2 le_rfl (by norm_num) k.val f
    have h₂ : (f : C → ℂ) =ᵐ[μQ] w := hac.ae_eq hw.coeFn_toLp
    have h₃ := (measurePreserving_mul_left μQ k.val⁻¹).quasiMeasurePreserving.ae_eq_comp h₂
    filter_upwards [h₁, h₂, h₃] with g hg hg' hg''
    refine hg.trans ((hg'').trans (?_ : w (k.val⁻¹ * g) = f g))
    rw [hg']
    have hk : ideleClassNorm ℚ k.val = 1 := k.property
    have hlog : logNorm (k.val⁻¹ * g) = logNorm g := by
      change Real.log ((ideleClassNorm ℚ (k.val⁻¹ * g)).val : ℝ) = _
      rw [map_mul, map_inv, hk, inv_one, one_mul]
    have hL' : k.val⁻¹ * g ∈ L ↔ g ∈ L := by simp only [L, mem_preimage, hlog]
    have hchar : χ (k.val⁻¹ * g) = χ g := by rw [map_mul, map_inv, hχ k, inv_one, one_mul]
    by_cases hm : g ∈ L
    · simp [w, indicator_of_mem hm, indicator_of_mem (hL'.mpr hm), hchar]
    · simp [w, indicator_of_notMem hm, indicator_of_notMem (mt hL'.mp hm)]
  · change (∫ g, f g * spectralZeroJet χ 0 0 0 g ∂μQ) ≠ 0
    rw [integral_congr_ae ((hac.ae_eq hw.coeFn_toLp).mono fun g hg ↦
      congrArg (· * spectralZeroJet χ 0 0 0 g) hg)]
    rw [show (fun g ↦ w g * spectralZeroJet χ 0 0 0 g) = L.indicator (fun _ ↦ (1 : ℂ)) by
      funext g
      by_cases hg : g ∈ L
      · rw [spectralZeroJet_zero, show w g = star (χ g : ℂ) from indicator_of_mem hg _,
          indicator_of_mem hg, mul_comm]
        simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Circle.norm_coe, one_pow, Complex.ofReal_one]
      · simp [w, hg]]
    rw [integral_indicator hLm, integral_const, Measure.real, Measure.restrict_apply_univ,
      Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hLpos.ne' hLfin).ne'
/-- A frequency set of Plancherel measure zero yields only the zero class. -/
private theorem singleFrequency_quotientBand_eq_singleton
    {G D E Q : Type*} [MeasurableSpace G] [MeasurableSpace D]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup Q] [Module ℂ Q]
    {μ σ : Measure G} {ν : Measure D} {U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν}
    {i : E →ₗ[ℂ] Lp ℂ 2 σ} {p : E →ₗ[ℂ] Q} {band : Set D}
    (hi : Injective i) (hσ : σ ≪ μ) (hμ : μ ≪ σ) (hband : ν band = 0) :
    {q | ∃ f : E, q = p f ∧ ∃ u : Lp ℂ 2 μ,
        (u : G → ℂ) =ᵐ[μ] (i f : G → ℂ) ∧ ∀ᵐ ψ ∂ν, ψ ∉ band → U u ψ = 0}
      = ({0} : Set Q) := by
  ext q
  constructor
  · rintro ⟨f, rfl, u, hu, hsupp⟩
    have houtside : ∀ᵐ ψ ∂ν, ψ ∉ band := ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hband)
    have hfu : U u = 0 := by
      apply Lp.ext
      filter_upwards [hsupp, houtside, Lp.coeFn_zero ℂ 2 ν] with ψ hs hh h0
      rw [h0]
      exact hs hh
    have hu₀ : u = 0 := U.injective (hfu.trans (map_zero U).symm)
    have hu' : (u : G → ℂ) =ᵐ[μ] (0 : G → ℂ) := by
      rw [hu₀]
      exact Lp.coeFn_zero ℂ 2 μ
    have hf : f = 0 := by
      apply hi
      rw [map_zero]
      exact Lp.ext ((hσ.ae_eq (hu.symm.trans hu')).trans (Lp.coeFn_zero ℂ 2 σ).symm)
    simp [hf]
  · rintro rfl
    refine ⟨0, (map_zero p).symm, 0, ?_, ?_⟩
    · rw [map_zero]
      exact (Lp.coeFn_zero ℂ 2 μ).trans (hμ.ae_eq (Lp.coeFn_zero ℂ 2 σ)).symm
    · rw [map_zero]
      exact (Lp.coeFn_zero ℂ 2 ν).mono (fun _ hψ _ ↦ hψ)

private theorem zeroBand_projection_of_singleton {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℂ Q] (B : Set Q) (hB : B = {0}) :
    range (0 : Q →L[ℂ] Q) = closure B ∧
      ∀ q y, y ∈ closure B → ‖q - (0 : Q →L[ℂ] Q) q‖ ≤ ‖q-y‖ := by
  rw [hB, isClosed_singleton.closure_eq]
  refine ⟨range_const, ?_⟩
  rintro q _ rfl
  rfl

private theorem ratBand_zero_refutation
    (basepoint : PontryaginDual C₁(ℚ) → PontryaginDual C)
    (hbasepoint : IsSpectralBasepointChoice basepoint)
    (horder : 0 < order(basepoint 1, (1 / 2 : ℂ)))
    (h : Printed.spectralLineIsotype_bandAdjoint_contains_jets) : False := by
  classical
  let χ := basepoint 1
  have hχ (k : C₁(ℚ)) : χ k.val = 1 := DFunLike.congr_fun (hbasepoint 1) k
  have hs : (1 : ℝ) < 2 := by norm_num
  let hs₀ : (0 : ℝ) ≤ 2 := le_of_lt (zero_lt_one.trans hs)
  let E := actionIsotype ((hardySobolevTranslation μQ mQ 0 0 2 le_rfl hs₀).comp
    (ideleClassNorm ℚ).ker.subtype) 1
  let N := (globalThetaSobolev ℚ (1 / 2) (le_rfl (a := (0 : ℝ))) hs₀).comap E.subtype
  let Q := spectralSobolevIsotypeQuotient ℚ (1 / 2) (le_rfl (a := (0 : ℝ))) hs₀ 1
  let : BorelSpace (PontryaginDual C) := ⟨rfl⟩
  obtain ⟨ν, hν, -⟩ := lcaPlancherelMeasure_existsUnique μQ
  let U := (lcaFourier_unitary μQ ν hν).exists.choose
  let B : Set Q := {q | ∃ f : E, q = N.mkQ f ∧ ∃ u : Lp ℂ 2 μQ,
    (u : C → ℂ) =ᵐ[μQ] (f.val : C → ℂ) ∧
    ∀ᵐ ψ ∂ν, ψ ∉ modulatedFrequencyBand mQ χ 0 0 → U u ψ = 0}
  let ρ (g : C) := ENNReal.ofReal (intervalSobolevDensity 0 0 2 (logNorm g))
  let σ := (μQ).withDensity ρ
  have hρ (g : C) : intervalSobolevDensity 0 0 2 (logNorm g) = 1 + (logNorm g) ^ 2 := by
    norm_num [intervalSobolevDensity]
  have hρm : Measurable ρ := by
    simp_rw [ρ, hρ]
    exact ENNReal.continuous_ofReal.comp
      (continuous_const.add (continuous_ratLogNorm.pow 2)) |>.measurable
  have hac : μQ ≪ σ :=
    withDensity_absolutelyContinuous' hρm.aemeasurable (.of_forall fun g ↦ by
      dsimp [ρ]
      rw [hρ]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  have hb : ν (modulatedFrequencyBand mQ χ 0 0) = 0 := by
    rw [modulatedFrequencyBand_zero]
    exact ratDual_singleton_null ν hν.1 χ
  have hB : B = {0} := singleFrequency_quotientBand_eq_singleton
    (i := (E.subtype : E →ₗ[ℂ] Lp ℂ 2 σ)) (p := N.mkQ) (U := U)
    Subtype.val_injective (withDensity_absolutelyContinuous _ _) hac hb
  obtain ⟨hrange, hclosest⟩ := zeroBand_projection_of_singleton B hB
  have hidx : 0 < floorCut((2 : ℝ), order(χ, shift((1 / 2 : ℝ), (0 : ℝ)))) := by
    have he : shift((1 / 2 : ℝ), (0 : ℝ)) = (1 / 2 : ℂ) := by push_cast; norm_num
    rw [he]
    exact lt_min horder (by norm_num [Nat.floor_pos])
  obtain ⟨d, hd, hpair⟩ := h ℚ basepoint hbasepoint 1 (1 / 2) 2 hs 0 ν hν 0
    (by simpa only [Nat.cast_zero, neg_zero] using hrange)
    (by simpa only [Nat.cast_zero, neg_zero] using hclosest) 0 0 (by simp) hidx
  have hd₀ : d = 0 := by
    obtain ⟨l, hl⟩ := hd
    ext q
    rw [← hl]
    simp
  obtain ⟨f, hf⟩ := ratJet_nonzero_trivial_isotype χ hχ
  apply hf
  rw [← (hpair f).2, hd₀]
  rfl


local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "UQ" => PontryaginDual CQ
local notation "U₁Q" => PontryaginDual (ideleClassNorm ℚ).ker

/-- A norm twist moves a critical-line zero of rational zeta to frequency zero
in the trivial norm-one isotype. -/
private theorem exists_spectralBasepoint_zero_at_half :
    ∃ χ : U₁Q → UQ, IsSpectralBasepointChoice χ ∧
      0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ 1)) (1/2)).untop₀.toNat := by
  classical
  obtain ⟨t, -, hzero⟩ := HardyFirstZero.first_zero_on_line
  let b := (t : ℂ) * Complex.I
  have hb : b.re = 0 := by simp [b, Complex.mul_re]
  let z : ℂ := 1 / 2 + b
  have hre : z.re = 1/2 := by simp [z, hb]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hz : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at hzero
    rw [← hzero]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [htwo]; simp)
  have hnat : 0 < (meromorphicOrderAt riemannZeta z).untop₀.toNat := by
    rw [← WithTop.coe_untop₀_of_ne_top hfin] at hz
    have hint : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hz
    omega
  let η := ideleClassNormTwist (1 : UQ) b
  have hu (g : CQ) : ‖η g‖ = 1 := by
    change ‖(1 : ℂ) * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ b‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm ℚ g))), hb, Real.rpow_zero]
  let ψ := unitaryHeckeCharacterToPontryaginDual η hu
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 ψ
  refine ⟨χ, ?_, ?_⟩
  · intro ω
    by_cases h : ω = 1
    · subst ω
      rw [show χ 1 = ψ from Function.update_self ..]
      ext g : 1
      apply Circle.ext
      change (1 : ℂ) * (((ideleClassNorm ℚ g.val).val : ℝ) : ℂ) ^ b = 1
      rw [show ideleClassNorm ℚ g.val = 1 from g.property]
      simp
    · simpa [χ, Function.update_of_ne h] using hχ₀ ω
  · rw [show χ 1 = ψ from Function.update_self ..]
    let L := continuedCompletedHeckeL (1 : UQ)
    have hL := (continuedCompletedHeckeL_spec (1 : UQ)).1
    have hshift : MeromorphicOn (fun w ↦ L (w + b)) univ :=
      fun _ _ ↦ (meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr
        (hL (mem_univ _))).meromorphicAt
    have heq := meromorphicContinuation_eventuallyEq (continuedCompletedHeckeL_spec ψ).1.meromorphicOn
      hshift (fun w hw ↦ by
        rw [show continuedCompletedHeckeL ψ w = completedHeckeL ψ ⟨w, hw⟩ from
          (continuedCompletedHeckeL_spec ψ).2 ⟨w, hw⟩,
          completedHeckeL_of_normTwist ψ b hb
            (ideleClassNormTwist_unitaryHeckeCharacter_zero η hu)]
        exact ((continuedCompletedHeckeL_spec (1 : UQ)).2 _).symm) (1/2)
    rw [meromorphicOrderAt_congr heq, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : UQ)) z).untop₀.toNat
    rwa [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
      (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
        (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]

/-- Paper: Theorem 10.2.1.1, proof following (10.2.1.10), p. 443.
Over ℚ a norm twist of the first certified zeta zero gives a zero at the
center of a singleton band. This band is Plancherel-null, so the projection
and its adjoint are zero. The zeroth jet still has a nonzero pairing with
a compactly supported test in the trivial norm-one isotype. -/
theorem Printed.spectralLineIsotype_bandAdjoint_contains_jets_false :
    ¬ Printed.spectralLineIsotype_bandAdjoint_contains_jets := by
  intro h
  obtain ⟨basepoint, hbasepoint, horder⟩ := exists_spectralBasepoint_zero_at_half
  exact ratBand_zero_refutation basepoint hbasepoint horder h

end BandProjection

end RiemannMasullo
