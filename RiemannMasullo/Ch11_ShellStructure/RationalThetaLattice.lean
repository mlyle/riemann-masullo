module

public import RiemannMasullo.Ch11_ShellStructure.Sec1b
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integer sums for rational polar-free theta lifts

With integer indicators at the finite places, a real Schwartz test gives a rational
adelic test. In the trivial character, its homogeneous theta lift is a sum over the
positive integers times twice the norm-one Tamagawa mass. A support bound makes its
evaluation finite, and the substitution from log norm to physical norm gives the
ordinary unit-interval approximation error in Theorem 12.5.1.1 (pp. 519–520).

The standard insertion and the rational theta series proofs are adapted from
Sergii Penner's `RationalThetaSpan` and `RationalThetaSeries` at revision
63ea7fc880fdf27febeea6f5acdef268c506b7b7.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap

namespace RiemannMasullo

set_option quotPrecheck false

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "realCoord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "𝓢ℝ" => SchwartzMap ℝ ℂ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U" => (v : V) → (v.adicCompletionIntegers ℚ)ˣ

private theorem real_arch_test_mem (f : 𝓢ℝ) :
    (fun x : Multiplicative (InfiniteAdeleRing ℚ) ↦ f (realCoord (x.toAdd Rat.infinitePlace))) ∈
      schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing ℚ)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  apply (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ f (realCoord (x Rat.infinitePlace)))).2
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f, fun _ ↦ rfl⟩

private def realArchTest (f : 𝓢ℝ) : B∞ :=
  ⟨_, real_arch_test_mem f⟩

private def realEmptyTest (f : 𝓢ℝ) :=
  sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 (realArchTest f)

private theorem realEmptyTest_apply (f : 𝓢ℝ) (x : SAdeleRing ℚ ∅) :
    realEmptyTest f (Multiplicative.ofAdd x) = f (realCoord (x.1 Rat.infinitePlace)) := by
  rw [realEmptyTest, sLocalStandardThetaTensor_apply, Fintype.prod_empty, mul_one]
  rfl

/-- A real Schwartz function at infinity, with the integer indicator at each finite place. -/
def ratStandardAdelicTest (f : 𝓢ℝ) : Bℚ :=
  sAdeleSchwartzToGlobal ℚ ∅ (realEmptyTest f)

open Classical in
/-- The finite components restrict the argument to integral finite adeles. -/
theorem ratStandardAdelicTest_apply (f : 𝓢ℝ) (x : 𝔸) :
    ratStandardAdelicTest f (Multiplicative.ofAdd x) =
      if ∀ v : HeightOneSpectrum (𝓞 ℚ), x.2 v ∈ v.adicCompletionIntegers ℚ then
        f (realCoord (x.1 Rat.infinitePlace)) else 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_apply, realEmptyTest_apply]
  simp [adeleProjection]
  rfl

/-- Both global polar conditions are exactly the two real conditions for this insertion. -/
theorem ratStandardAdelicTest_polar_iff (f : 𝓢ℝ) :
    ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ↔ f 0 = 0 ∧ 𝓕 f 0 = 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_mem_polarSubspace_iff, realEmptyTest_apply,
    sAdeleSchwartzFourier_ratEmpty_apply f (realEmptyTest f) (realEmptyTest_apply f)]
  change (f (realCoord 0) = 0 ∧ 𝓕 f (realCoord 0) = 0) ↔ _
  rw [map_zero]

private theorem finite_integral_iff (x : ℚ) :
    (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  have h := diagonal_mem_integralAdelesOutside ℚ ∅ x
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, forall_const, Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  rw [show (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔
    ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r = x from h]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨Rat.ringOfIntegersEquiv r, (Rat.ringOfIntegersEquiv_apply_coe r).trans hr⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, (map_intCast _ n).trans hn⟩⟩

private theorem finite_unit_mul_iff (x : ℚ) (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) :
    (∀ v : V, ((algebraMap ℚ 𝔸 x) * g.val).2 v ∈ v.adicCompletionIntegers ℚ) ↔
      ∃ n : ℤ, (n : ℚ) = x := by
  rw [← finite_integral_iff]
  constructor
  · intro hm v
    have he : (u v).val.val * (u v).inv.val = 1 := congrArg Subtype.val (u v).val_inv
    have h := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).inv.property
    change ((algebraMap ℚ 𝔸 x).2 v * g.val.2 v) * (u v).inv.val ∈ _ at h
    change (algebraMap ℚ 𝔸 x).2 v ∈ (v.adicCompletionIntegers ℚ).toSubring
    simpa only [hg, mul_assoc, he, mul_one] using h
  · intro hm v
    change (algebraMap ℚ 𝔸 x).2 v * g.val.2 v ∈ _
    rw [hg]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).val.property

private theorem norm_of_integral_unit_representative (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ≥0ˣ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t.val) :
    ((ideleNorm ℚ g).val : ℝ) = t.val := by
  rw [((ideleNorm_spec ℚ).1 _).2, Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : V) : ‖g.val.2 v‖ = 1 := by
    rw [hg]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (u v))).mp
    exact ⟨(u v).val.property, (u v).inv.property⟩
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) (g.val.1 Rat.infinitePlace)
  change ‖realCoord (g.val.1 Rat.infinitePlace)‖ = _ at h
  rw [← h, ht]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

private theorem hasSum_integer_theta (f : 𝓢ℝ) (hf : f 0 = 0)
    (g : 𝔸ˣ) (u : U) (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t) :
    HasSum (fun n : ℤ ↦ f ((n : ℝ) * t))
      (adelicTheta (ratStandardAdelicTest f) (QuotientGroup.mk g)) := by
  classical
  let F (r : ℚˣ) := ratStandardAdelicTest f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (r : ℚ) * g.val))
  let G (n : ℤ) := f ((n : ℝ) * t)
  have hterm (r : ℚˣ) : F r = if ∃ n : ℤ, (n : ℚ) = r.val then f ((r.val : ℝ) * t) else 0 := by
    dsimp only [F]
    rw [ratStandardAdelicTest_apply, finite_unit_mul_iff _ g u hg]
    congr 2
    change realCoord (algebraMap ℚ Rat.infinitePlace.Completion (r : ℚ) * g.val.1 Rat.infinitePlace) = _
    rw [map_mul, ht]
    simp
  have hG0 : G 0 = 0 := by simp [G, hf]
  let i (n : Function.support G) : ℚˣ := Units.mk0 (n.val : ℚ) (by
    exact_mod_cast (show n.val ≠ 0 from fun h ↦ n.property (h ▸ hG0)))
  have hi : Injective i := by
    intro a b h
    apply Subtype.ext
    exact_mod_cast (show (a.val : ℚ) = b.val from congrArg Units.val h)
  have hval (n : Function.support G) : F (i n) = G n.val := by
    rw [hterm, ite_eq_left (show ∃ m : ℤ, (m : ℚ) = (i n).val from ⟨n.val, rfl⟩)]
    change f (((n.val : ℚ) : ℝ) * t) = _
    simp [G]
  have hcov : Function.support F ⊆ Set.range i := by
    intro r hr
    change F r ≠ 0 at hr
    rw [hterm] at hr
    split at hr
    · rename_i h
      obtain ⟨n, hn⟩ := h
      have hG : G n ≠ 0 := by simpa [G, ← hn] using hr
      exact ⟨⟨n, hG⟩, Units.ext hn⟩
    · exact (hr rfl).elim
  rw [adelicTheta_mk]
  apply (hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := G) i hi hcov hval).mp
  apply Summable.hasSum
  have H := (adelicAverage_summableUniformlyOn (ratStandardAdelicTest f) {(g, (0 : 𝔸))}
    isCompact_singleton).summable (Set.mem_singleton (g, (0 : 𝔸)))
  exact (show Summable (fun r ↦ ‖F r‖) by simpa [F, mul_comm] using H).of_norm

/-- The actual unaveraged adelic theta on rational idele classes is twice the scalar positive
integer theta of an even test vanishing at zero. Its value depends only on the idelic norm. -/
theorem ratStandardAdelicTest_theta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    adelicTheta (ratStandardAdelicTest f) x =
      2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ)) := by
  obtain ⟨e, herep⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨⟨t, u⟩, rfl⟩ := e.surjective x
  obtain ⟨g, harch, hfin, hclass⟩ := herep t u
  rw [hclass]
  have hnorm : ((ideleClassNorm ℚ (QuotientGroup.mk g)).val : ℝ) = t.val :=
    norm_of_integral_unit_representative g u hfin harch
  rw [hnorm]
  have hsum := hasSum_integer_theta f hf g u hfin harch
  rw [← hsum.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ hsum.summable]
  · simp only [Int.cast_zero, zero_mul, hf, zero_add, Int.cast_natCast, nsmul_eq_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f ((n : ℝ) * t.val))]
    simp
  · intro n
    simpa only [Int.cast_neg, neg_mul] using he ((n : ℝ) * t.val)

local instance : MeasurableSpace Cℚ := borel _
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)

/-- The trivial homogeneous average used in Chapter 10 contributes its norm-one Tamagawa
mass to the physical positive-integer theta formula. -/
theorem ratStandardAdelicTest_homogeneousTheta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x =
      mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))) := by
  let H := (ideleClassNorm ℚ).ker
  change (∫ k : H, adelicTheta (ratStandardAdelicTest f) (k.val * x) * _ ∂_) = _
  have hr (k : H) : ideleClassNorm ℚ (k.val * x) = ideleClassNorm ℚ x := by
    rw [map_mul, show ideleClassNorm ℚ k.val = 1 from k.property, one_mul]
  simp only [ratStandardAdelicTest_theta f he hf, hr, PontryaginDual.one_apply,
    Circle.coe_one, mul_one, integral_const, Measure.real, Complex.real_smul]

/-- Above a positive norm cutoff, a one-sided support bound on the real test truncates
the actual homogeneous adelic theta to a finite sum with its exact Haar factor. -/
theorem ratStandardAdelicTest_homogeneousTheta_eq_sum (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) {B : ℝ} (hs : ∀ r : ℝ, B < r → f r = 0) (x : Cℚ) (N : ℕ)
    (hN : B < ((N : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ)) :
    homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x =
      mass * (2 * ∑ n ∈ Finset.range N, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))) := by
  rw [ratStandardAdelicTest_homogeneousTheta f he hf x]
  congr 2
  apply tsum_eq_sum
  intro n hn
  apply hs
  apply hN.trans_le
  apply mul_le_mul_of_nonneg_right _ (ideleClassNorm ℚ x).val.property
  exact add_le_add_left (Nat.cast_le.mpr (Nat.le_of_not_gt (by simpa using hn))) 1

/-- A polar-free real test supported on positive norms at most one gives an actual
polar-free adelic source. Its theta vanishes at every class of norm greater than one. -/
theorem ratStandardAdelicTest_polar_of_unit_support (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (hF : 𝓕 f 0 = 0) (hs : ∀ r : ℝ, 1 < r → f r = 0) :
    ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ∧
      ∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) →
        homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x = 0 := by
  refine ⟨(ratStandardAdelicTest_polar_iff f).2 ⟨hf, hF⟩, fun x hx ↦ ?_⟩
  simpa using ratStandardAdelicTest_homogeneousTheta_eq_sum f he hf hs x 0 (by simpa using hx)

private theorem ratTheta_centered_changeVariables (A : ℝ → ℂ) :
    (∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) -
      A (Real.exp x) * Complex.exp ((x : ℂ) / 2)‖ ^ 2) =
      ∫ r in Ioc (0 : ℝ) 1, ‖1 - A r‖ ^ 2 := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Iic (0 : ℝ)) measurableSet_Iic
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun r ↦ ‖1 - A r‖ ^ 2)
  rw [Real.image_exp_Iic, Real.exp_zero] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Iic
  intro x _
  dsimp only
  rw [← one_sub_mul, norm_mul, mul_pow, Complex.norm_exp]
  have hpow : Real.exp (((x : ℂ) / 2).re) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [hpow, abs_of_pos (Real.exp_pos x)]
  exact mul_comm _ _

/-- In the rational trivial character the centered log-norm error from the indicator
is exactly the ordinary unit-interval error of the real-place positive integer series.
The parametrization can be any family of classes with prescribed norm. -/
theorem ratStandardAdelicTest_halfLine_error (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (g : ℝ → Cℚ) (hg : ∀ x, ((ideleClassNorm ℚ (g x)).val : ℝ) = Real.exp x) :
    (∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) -
      homogeneousAdelicTheta 1 (ratStandardAdelicTest f) (g x) * Complex.exp ((x : ℂ) / 2)‖ ^ 2) =
      ∫ r in Ioc (0 : ℝ) 1, ‖1 - mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * r))‖ ^ 2 := by
  simp_rw [ratStandardAdelicTest_homogeneousTheta f he hf, hg]
  exact ratTheta_centered_changeVariables
    (fun r ↦ mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * r)))

private theorem ratTheta_dilationDifference (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    (hs : ∀ r : ℝ, 1 < r → b r = 0) (k m : ℝ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ h : 𝓢ℝ, (∀ r : ℝ, h r = (b r - (k : ℂ) * b (r * k)) -
        (b (r * m) - (k : ℂ) * b (r * m * k))) ∧
      Function.Even (h : ℝ → ℂ) ∧ h 0 = 0 ∧ 𝓕 h 0 = 0 ∧ ∀ r : ℝ, 1 < r → h r = 0 := by
  let D (q : ℝ) (hq : 0 < q) : 𝓢ℝ →L[ℂ] 𝓢ℝ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 q hq.ne'))
  have hD (q : ℝ) (hq : 0 < q) (v : 𝓢ℝ) (x : ℝ) : D q hq v x = v (x * q) := rfl
  have hDF (q : ℝ) (hq : 0 < q) (v : 𝓢ℝ) : 𝓕 (D q hq v) 0 = ((q⁻¹ : ℝ) : ℂ) * 𝓕 v 0 := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      one_smul]
    simpa only [hD, abs_of_pos (inv_pos.mpr hq), Complex.real_smul] using
      Measure.integral_comp_mul_right (fun x : ℝ ↦ v x) q
  have hk' : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hm' : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let v := b - (k : ℂ) • D k hk' b
  let h := v - D m hm' v
  have hval (r : ℝ) : h r = (b r - (k : ℂ) * b (r * k)) -
      (b (r * m) - (k : ℂ) * b (r * m * k)) := rfl
  have hfv : 𝓕 v 0 = 0 := by
    simp only [v, FourierTransform.fourier_sub, FourierTransform.fourier_smul, sub_apply, smul_apply,
      smul_eq_mul, hDF, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hk'.ne'), one_mul, sub_self]
  refine ⟨h, hval, ?_, ?_, ?_, ?_⟩
  · intro r
    simp only [hval, neg_mul, he _]
  · simp [hval]
  · simp only [h, FourierTransform.fourier_sub, sub_apply, hDF, hfv, mul_zero, sub_zero]
  · intro r hr
    have hg (x q : ℝ) (hx : 1 < x) (hq : 1 ≤ q) : 1 < x * q :=
      hx.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hx).le hq)
    simp [hval, hs r hr, hs _ (hg r k hr hk), hs _ (hg r m hr hm),
      hs _ (hg _ k (hg r m hr hm) hk)]

/-- Finite combinations of two dilation differences of a single even Schwartz cutoff
give genuine polar-free rational adelic tests. Their theta profiles vanish above norm
one. The pointwise formula specifies the source used for integer-dilation approximants. -/
theorem exists_ratStandardAdelicTest_dilationDifferences (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    (hs : ∀ r : ℝ, 1 < r → b r = 0) (m : ℝ) (hm : 1 ≤ m)
    (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k) :
    ∃ h : 𝓢ℝ, (∀ r : ℝ, h r = ∑ k ∈ S, a k *
        ((b r - (k : ℂ) * b (r * k)) - (b (r * m) - (k : ℂ) * b (r * m * k)))) ∧
      Function.Even (h : ℝ → ℂ) ∧ h 0 = 0 ∧ (∀ r : ℝ, 1 < r → h r = 0) ∧
      ratStandardAdelicTest h ∈ adelePolarSubspace ℚ ∧
      ∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 (ratStandardAdelicTest h) x = 0 := by
  classical
  choose v hv hev hz hF hsup using fun (k : S) ↦ ratTheta_dilationDifference b he hs k.val m
    (by exact_mod_cast hk k.val k.property) hm
  let h : 𝓢ℝ := ∑ k : S, a k.val • v k
  have happ (r : ℝ) : h r = ∑ k : S, a k.val * v k r := by simp [h]
  have hhe : Function.Even (h : ℝ → ℂ) := by
    intro r
    simp only [happ, hev _ _]
  have hh0 : h 0 = 0 := by simp [happ, hz]
  have hhF : 𝓕 h 0 = 0 := by simp [h, hF]
  have hhs (r : ℝ) (hr : 1 < r) : h r = 0 := by simp [happ, fun k ↦ hsup k r hr]
  refine ⟨h, fun r ↦ ?_, hhe, hh0, hhs, ratStandardAdelicTest_polar_of_unit_support h hhe hh0 hhF hhs⟩
  rw [happ, ← Finset.sum_attach S]
  simp only [Finset.attach_eq_univ, hv, Complex.ofReal_natCast]

private theorem ratTheta_plateau_sum (b : ℝ → ℂ) {c r : ℝ}
    (hb : ∀ x ∈ Icc 0 c, b x = 1) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (hr : 0 ≤ r) (n k : ℕ) (hk : 0 < k) (hlo : 1 < ((n : ℝ) + 1) * r) (hhi : (n : ℝ) * r ≤ c) :
    (∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k)) = ((n / k : ℕ) : ℂ) := by
  have hcut : (∑ j ∈ Finset.range (n / k), b ((((j : ℝ) + 1) * r) * k)) =
      ∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.div_le_self n k))
    intro j _ hj
    apply hs
    have hj' : n / k < j + 1 := by simp only [Finset.mem_range] at hj; omega
    have hnat := (Nat.div_lt_iff_lt_mul hk).mp hj'
    have hh : (n : ℝ) + 1 ≤ ((j : ℝ) + 1) * k := by exact_mod_cast Nat.succ_le_of_lt hnat
    exact hlo.trans_le (by simpa only [mul_right_comm _ r] using mul_le_mul_of_nonneg_right hh hr)
  rw [← hcut]
  calc
    _ = ∑ _j ∈ Finset.range (n / k), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply hb
      refine ⟨by positivity, ?_⟩
      have hnat := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      have hh : ((j : ℝ) + 1) * k ≤ n := by exact_mod_cast hnat
      exact (by simpa only [mul_right_comm _ r] using mul_le_mul_of_nonneg_right hh hr : _ ≤ (n : ℝ) * r).trans hhi
    _ = _ := by simp

/-- A single polar-free adelic test realizes the prescribed remainder combination on
every reciprocal interval where the smooth cutoff agrees with the sharp one. The same
test vanishes identically at norm greater than one. -/
theorem exists_ratTheta_residue_intervals (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    {c : ℝ} (hb : ∀ r ∈ Icc 0 c, b r = 1) (hs : ∀ r : ℝ, 1 < r → b r = 0)
    (m : ℝ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k) :
    ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ (n : ℕ) (x : Cℚ), let r := ((ideleClassNorm ℚ x).val : ℝ)
        1 < r * m → 1 < ((n : ℝ) + 1) * r → (n : ℝ) * r ≤ c →
          homogeneousAdelicTheta 1 f.val x = mass * (2 * ∑ k ∈ S, a k * (n % k : ℕ)) := by
  obtain ⟨h, happ, hhe, hh0, hsup, hpol, hout⟩ :=
    exists_ratStandardAdelicTest_dilationDifferences b he hs m hm S a hk
  refine ⟨⟨ratStandardAdelicTest h, hpol⟩, hout, fun n x ↦ ?_⟩
  intro r hmcut hlo hhi
  rw [ratStandardAdelicTest_homogeneousTheta_eq_sum h hhe hh0 hsup x n hlo]
  congr 2
  change (∑ j ∈ Finset.range n, h (((j : ℝ) + 1) * r)) = _
  simp_rw [happ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hmem
  rw [← Finset.mul_sum]
  congr 1
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk k hmem
  have hd (j : ℕ) : 1 < (((j : ℝ) + 1) * r) * m := by
    rw [mul_assoc]
    exact hmcut.trans_le (le_mul_of_one_le_left (zero_lt_one.trans hmcut).le (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  have hdk (j : ℕ) : 1 < (((j : ℝ) + 1) * r) * m * k :=
    (hd j).trans_le (le_mul_of_one_le_right (zero_lt_one.trans (hd j)).le hk')
  simp only [hs _ (hd _), hs _ (hdk _), mul_zero, sub_zero]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 := ratTheta_plateau_sum b hb hs (ideleClassNorm ℚ x).val.property n 1 (by decide) hlo hhi
  have hkstep := ratTheta_plateau_sum b hb hs (ideleClassNorm ℚ x).val.property n k (hk k hmem) hlo hhi
  simp only [Nat.cast_one, mul_one, Nat.div_one] at h1
  change (∑ j ∈ Finset.range n, b (((j : ℝ) + 1) * r)) = (n : ℂ) at h1
  change (∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k)) = ((n / k : ℕ) : ℂ) at hkstep
  rw [h1, hkstep]
  have hnat := Nat.mod_add_div n k
  exact sub_eq_of_eq_add (by exact_mod_cast hnat.symm)

open scoped ContDiff

private theorem ratTheta_block_discrepancy (b : ℕ → ℝ) (hb : Antitone b) (k N : ℕ) :
    let S (n : ℕ) := (∑ j ∈ Finset.range (n * k), b (j + 1)) -
      (k : ℝ) * ∑ q ∈ Finset.range n, b ((q + 1) * k)
    0 ≤ S N ∧ S N ≤ (k : ℝ) * (b 0 - b (N * k)) := by
  intro S
  induction N with
  | zero => simp [S]
  | succ n ih =>
    let d (j : ℕ) := b (n * k + j + 1) - b ((n + 1) * k)
    have hrec : S (n + 1) = S n + ∑ j ∈ Finset.range k, d j := by
      dsimp [S, d]
      rw [Nat.add_one_mul, Finset.sum_range_add, Finset.sum_range_succ (f := fun q ↦ b ((q + 1) * k)),
        Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [Nat.add_one_mul]
      ring
    have hp : 0 ≤ ∑ j ∈ Finset.range k, d j := by
      refine Finset.sum_nonneg fun j hj ↦ sub_nonneg.mpr (hb ?_)
      rw [Nat.add_one_mul]
      have := Finset.mem_range.mp hj
      omega
    have hle : (∑ j ∈ Finset.range k, d j) ≤ (k : ℝ) * (b (n * k) - b ((n + 1) * k)) := by
      calc _ ≤ ∑ _j ∈ Finset.range k, (b (n * k) - b ((n + 1) * k)) := by
                exact Finset.sum_le_sum fun j _ ↦ sub_le_sub_right (hb (by omega)) _
           _ = _ := by simp [mul_sub]
    rw [hrec]
    refine ⟨add_nonneg ih.1 hp, ?_⟩
    calc _ ≤ _ := add_le_add ih.2 hle
         _ = _ := by ring

private theorem ratTheta_lattice_discrepancy_bounds (b : ℝ → ℝ) (hb : AntitoneOn b (Ici 0))
    (hn : ∀ x ≥ 0, 0 ≤ b x) (h1 : b 0 ≤ 1) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 1 ≤ k) :
    let A := (∑' j : ℕ, b (((j : ℝ) + 1) * r)) -
      (k : ℝ) * ∑' j : ℕ, b ((((j : ℝ) + 1) * r) * k)
    0 ≤ A ∧ A ≤ k := by
  intro A
  obtain ⟨N, hN⟩ := exists_nat_gt r⁻¹
  have hNr : 1 < (N : ℝ) * r := (inv_lt_iff_one_lt_mul₀ hr).mp hN
  have htr (L : ℕ) (r' : ℝ) (hr' : 0 ≤ r') (hcut : 1 < (L : ℝ) * r') :
      (∑' j : ℕ, b (((j : ℝ) + 1) * r')) = ∑ j ∈ Finset.range L, b (((j : ℝ) + 1) * r') := by
    apply tsum_eq_sum
    intro j hj
    have hj' : L ≤ j := Nat.le_of_not_gt fun hj' ↦ hj (Finset.mem_range.mpr hj')
    apply hs
    exact hcut.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ_of_le hj') hr')
  let u (j : ℕ) := b ((j : ℝ) * r)
  have hu : Antitone u := fun i j hij ↦ hb (by positivity : (0 : ℝ) ≤ i * r)
    (by positivity : (0 : ℝ) ≤ j * r) (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hr.le)
  have h0 := ratTheta_block_discrepancy u hu k N
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hNr' : 1 < (N : ℝ) * r * k := hNr.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hNr).le hk')
  have hE : A = (∑ j ∈ Finset.range (N * k), u (j + 1)) -
      (k : ℝ) * ∑ q ∈ Finset.range N, u ((q + 1) * k) := by
    dsimp only [A]
    simp_rw [mul_assoc _ r (k : ℝ)]
    rw [htr (N * k) r hr.le (by push_cast; simpa [mul_right_comm] using hNr'),
      htr N (r * k) (by positivity) (by simpa [mul_assoc] using hNr')]
    simp [u, mul_assoc, mul_comm]
  rw [hE]
  refine ⟨h0.1, h0.2.trans ?_⟩
  have hhi : u 0 ≤ 1 := by simpa [u] using h1
  have hlo : 0 ≤ u (N * k) := hn _ (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left (show u 0 - u (N * k) ≤ 1 by linarith) (Nat.cast_nonneg (α := ℝ) k)]

private def ratThetaSmoothCutoff (i : ℕ) (r : ℝ) : ℝ := Real.smoothTransition (((i : ℝ) + 1) * (1 - r ^ 2))

private theorem ratThetaSmoothCutoff_properties (i : ℕ) :
    AntitoneOn (ratThetaSmoothCutoff i) (Ici 0) ∧ (∀ r, 0 ≤ ratThetaSmoothCutoff i r ∧ ratThetaSmoothCutoff i r ≤ 1) ∧
    (∀ r, 1 < r → ratThetaSmoothCutoff i r = 0) ∧
    ∃ b : SchwartzMap ℝ ℂ, (∀ r, b r = (ratThetaSmoothCutoff i r : ℂ)) ∧ Function.Even (b : ℝ → ℂ) := by
  have houtside (r : ℝ) (hr : 1 ≤ r ^ 2) : ratThetaSmoothCutoff i r = 0 :=
    Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith))
  refine ⟨fun x hx y hy hxy ↦ ?_, fun r ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun r hr ↦ houtside r (by nlinarith [sq_nonneg (r - 1)]), ?_⟩
  · exact Real.smoothTransition.monotone (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (pow_le_pow_left₀ hx hxy 2) _) (by positivity))
  · let f (r : ℝ) : ℂ := ratThetaSmoothCutoff i r
    have hc : HasCompactSupport f := by
      apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
      intro r hr
      simp only [mem_Icc, not_and_or, not_le] at hr
      have := houtside r (by rcases hr with h|h <;> nlinarith [sq_nonneg (r - 1), sq_nonneg (r + 1)])
      simp [f, this]
    have hdiff : ContDiff ℝ (∞) f := by
      have hs : ContDiff ℝ (∞) (fun r : ℝ ↦ Real.smoothTransition (((i : ℝ) + 1) * (1 - r ^ 2))) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact Complex.ofRealCLM.contDiff.comp hs
    refine ⟨hc.toSchwartzMap hdiff, fun r ↦ rfl, fun r ↦ ?_⟩
    change ((ratThetaSmoothCutoff i (-r) : ℝ) : ℂ) = ((ratThetaSmoothCutoff i r : ℝ) : ℂ)
    simp [ratThetaSmoothCutoff]

private theorem ratThetaSmoothCutoff_plateau {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    ∀ᶠ i : ℕ in atTop, ∀ x ∈ Icc 0 c, ratThetaSmoothCutoff i x = 1 := by
  have hpos : 0 < 1 - c ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hc1) (show 0 < 1 + c by positivity)]
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - c ^ 2))
  filter_upwards [eventually_ge_atTop N] with i hi
  intro x hx
  apply Real.smoothTransition.one_of_one_le
  have hNc : 1 < (N : ℝ) * (1 - c ^ 2) := (div_lt_iff₀ hpos).mp hN
  have hstep : ((N : ℝ)) ≤ (i : ℝ) + 1 := by exact_mod_cast Nat.le_succ_of_le hi
  exact hNc.le.trans (mul_le_mul hstep
    (sub_le_sub_left (pow_le_pow_left₀ hx.1 hx.2 2) _) hpos.le (by positivity))

private def ratThetaDiscrepancy (b : ℝ → ℝ) (k : ℕ) (r : ℝ) :=
  (∑' j : ℕ, b (((j : ℝ) + 1) * r)) - (k : ℝ) * ∑' j : ℕ, b ((((j : ℝ) + 1) * r) * k)

private theorem ratThetaDiscrepancy_eq_zero (b : ℝ → ℝ) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (k : ℕ) (hk : 1 ≤ k) {r : ℝ} (hr : 1 < r) : ratThetaDiscrepancy b k r = 0 := by
  have hh (j : ℕ) : 1 < ((j : ℝ) + 1) * r :=
    hr.trans_le (le_mul_of_one_le_left (zero_lt_one.trans hr).le (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  have hhk (j : ℕ) : 1 < ((j : ℝ) + 1) * r * k :=
    (hh j).trans_le (le_mul_of_one_le_right (zero_lt_one.trans (hh j)).le (by exact_mod_cast hk))
  simp [ratThetaDiscrepancy, fun j ↦ hs _ (hh j), fun j ↦ hs _ (hhk j)]

private theorem ratThetaDiscrepancy_eq_mod (b : ℝ → ℝ) {c : ℝ} (hb : ∀ x ∈ Icc 0 c, b x = 1)
    (hs : ∀ x : ℝ, 1 < x → b x = 0) (r : ℝ) (hr : 0 < r)
    (n k : ℕ) (hk : 1 ≤ k) (hlo : 1 < ((n : ℝ) + 1) * r) (hhi : (n : ℝ) * r ≤ c) :
    ratThetaDiscrepancy b k r = ((n % k : ℕ) : ℝ) := by
  have hh (j : ℕ) (hj : j ∉ Finset.range n) : 1 < ((j : ℝ) + 1) * r := by
    apply hlo.trans_le (mul_le_mul_of_nonneg_right _ hr.le)
    have hh' : n ≤ j := by simpa using hj
    exact_mod_cast Nat.add_le_add_right hh' 1
  have hhk (j : ℕ) (hj : j ∉ Finset.range n) : 1 < ((j : ℝ) + 1) * r * k :=
    (hh j hj).trans_le (le_mul_of_one_le_right (zero_lt_one.trans (hh j hj)).le (by exact_mod_cast hk))
  rw [ratThetaDiscrepancy, tsum_eq_sum (s := Finset.range n) (fun j hj ↦ hs _ (hh j hj)),
    tsum_eq_sum (s := Finset.range n) (fun j hj ↦ hs _ (hhk j hj))]
  have hstep (l : ℕ) (hl : 0 < l) :
      (∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * l)) = ((n / l : ℕ) : ℝ) := by
    have hh := ratTheta_plateau_sum (fun x ↦ (b x : ℂ)) (c := c) (r := r)
      (fun x hx ↦ by rw [hb _ hx]; simp) (fun x hx ↦ by rw [hs _ hx]; simp) hr.le n l hl hlo hhi
    exact_mod_cast hh
  have h1 := hstep 1 (by decide)
  simp only [Nat.cast_one, mul_one, Nat.div_one] at h1
  rw [h1, hstep k hk]
  exact sub_eq_of_eq_add (by exact_mod_cast (Nat.mod_add_div n k).symm)

private theorem ratThetaDiscrepancy_eventually_eq (r : ℝ) (hr : 0 < r)
    (hne : r ∉ range (fun j : ℕ ↦ (j : ℝ)⁻¹)) :
    ∀ᶠ i : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      ratThetaDiscrepancy (ratThetaSmoothCutoff i) k r - ratThetaDiscrepancy (ratThetaSmoothCutoff i) k (r * ((i : ℝ) + 1)) = ((⌊r⁻¹⌋₊ % k : ℕ) : ℝ) := by
  let n := ⌊r⁻¹⌋₊
  have hinv : (n : ℝ) < r⁻¹ := (Nat.floor_le (inv_nonneg.mpr hr.le)).lt_of_ne fun he ↦
    hne ⟨n, by change (n : ℝ)⁻¹ = r; rw [he, inv_inv]⟩
  have hnon : 0 ≤ (n : ℝ) * r := by positivity
  have hhi : (n : ℝ) * r < 1 := (lt_div_iff₀ hr).mp (by simpa [one_div] using hinv : (n : ℝ) < 1 / r)
  have hlo : 1 < ((n : ℝ) + 1) * r := (inv_lt_iff_one_lt_mul₀ hr).mp (Nat.lt_floor_add_one _)
  obtain ⟨N, hN⟩ := exists_nat_gt r⁻¹
  filter_upwards [ratThetaSmoothCutoff_plateau hnon hhi, eventually_ge_atTop N] with i hb hi
  intro k hk
  have hr' : 1 < r * ((i : ℝ) + 1) := by
    rw [mul_comm]
    apply (inv_lt_iff_one_lt_mul₀ hr).mp
    exact hN.trans_le (by exact_mod_cast Nat.le_succ_of_le hi)
  have hs := (ratThetaSmoothCutoff_properties i).2.2.1
  rw [ratThetaDiscrepancy_eq_zero _ hs k hk hr', sub_zero]
  exact ratThetaDiscrepancy_eq_mod _ hb hs r hr n k hk hlo le_rfl

private theorem ratThetaDiscrepancy_hasSum (b : ℝ → ℝ) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (r : ℝ) (hr : 0 < r) (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun j : ℕ ↦ ((b (((j : ℝ) + 1) * r) : ℝ) : ℂ) -
      (k : ℂ) * (b ((((j : ℝ) + 1) * r) * k) : ℂ)) (ratThetaDiscrepancy b k r : ℂ) := by
  have hsum (t : ℝ) (ht : 0 < t) : Summable (fun j : ℕ ↦ b (((j : ℝ) + 1) * t)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt t⁻¹
    refine summable_of_ne_finset_zero (s := Finset.range N) fun j hj ↦ hs _ ?_
    apply (inv_lt_iff_one_lt_mul₀ ht).mp
    apply hN.trans_le
    have : N ≤ j := by simpa using hj
    exact_mod_cast Nat.le_succ_of_le this
  have h₁ := Complex.ofRealCLM.hasSum (hsum r hr).hasSum
  have h₂ := (Complex.ofRealCLM.hasSum (hsum (r * k) (mul_pos hr (by exact_mod_cast hk))).hasSum).mul_left (k : ℂ)
  simpa only [ratThetaDiscrepancy, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofRealCLM_apply, mul_assoc] using h₁.sub h₂

private theorem ratTheta_dilationDifference_tsum (b : ℝ → ℝ) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (r m : ℝ) (hr : 0 < r) (hm : 0 < m) (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k)
    (h : ℝ → ℂ) (hh : ∀ z : ℝ, h z = ∑ k ∈ S, a k *
      (((b z : ℝ) : ℂ) - k * b (z * k) - (b (z * m) - (k : ℂ) * b (z * m * k)))) :
    (∑' j : ℕ, h (((j : ℝ) + 1) * r)) = ∑ k ∈ S, a k * ((ratThetaDiscrepancy b k r - ratThetaDiscrepancy b k (r * m) : ℝ) : ℂ) := by
  have H (k : ℕ) (hmem : k ∈ S) := ((ratThetaDiscrepancy_hasSum b hs r hr k (hk k hmem)).sub
    (ratThetaDiscrepancy_hasSum b hs (r * m) (mul_pos hr hm) k (hk k hmem))).mul_left (a k)
  simp_rw [hh, mul_assoc]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk'
    simpa only [Complex.ofReal_sub, mul_assoc] using (H k hk').tsum_eq
  · intro k hk'
    simpa only [mul_assoc] using (H k hk').summable

private def ratThetaSmoothRemainderSum (S : Finset ℕ) (a : ℕ → ℂ) (i : ℕ) (r : ℝ) : ℂ :=
  ∑ k ∈ S, a k * ((ratThetaDiscrepancy (ratThetaSmoothCutoff i) k r - ratThetaDiscrepancy (ratThetaSmoothCutoff i) k (r * ((i : ℝ) + 1)) : ℝ) : ℂ)

private def ratThetaRemainderSum (S : Finset ℕ) (a : ℕ → ℂ) (r : ℝ) : ℂ :=
  ∑ k ∈ S, a k * ((⌊r⁻¹⌋₊ % k : ℕ) : ℂ)

private theorem ratThetaSmoothRemainderSum_error_tendsto (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k)
    (H : ℝ → ℂ) (hH : Measurable H) (M : ℝ) (hM : ∀ r ∈ Ioc (0 : ℝ) 1, ‖H r‖ ≤ M) :
    Tendsto (fun i : ℕ ↦ ∫ r in Ioc (0 : ℝ) 1, ‖ratThetaSmoothRemainderSum S a i r - H r‖^2)
      atTop (𝓝 (∫ r in Ioc (0 : ℝ) 1, ‖ratThetaRemainderSum S a r - H r‖^2)) := by
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let B := ∑ k ∈ S, ‖a k‖ * (k : ℝ)
  have hm (i : ℕ) (k : ℕ) : Measurable (ratThetaDiscrepancy (ratThetaSmoothCutoff i) k) := by
    have hc : Continuous (ratThetaSmoothCutoff i) := by unfold ratThetaSmoothCutoff; fun_prop
    unfold ratThetaDiscrepancy
    exact (Measurable.tsum (fun j ↦ (hc.comp (by fun_prop)).measurable)).sub
      (measurable_const.mul (Measurable.tsum (fun j ↦ (hc.comp (by fun_prop)).measurable)))
  have hsm (i : ℕ) : Measurable (ratThetaSmoothRemainderSum S a i) := by
    unfold ratThetaSmoothRemainderSum
    fun_prop (disch := assumption)
  have hSM (i : ℕ) (r : ℝ) (hr : 0 < r) : ‖ratThetaSmoothRemainderSum S a i r‖ ≤ B := by
    unfold ratThetaSmoothRemainderSum
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro k hmem
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    obtain ⟨hmono, hbd, hs, _⟩ := ratThetaSmoothCutoff_properties i
    have hx (w : ℝ) (hw : 0 < w) : 0 ≤ ratThetaDiscrepancy (ratThetaSmoothCutoff i) k w ∧ ratThetaDiscrepancy (ratThetaSmoothCutoff i) k w ≤ k :=
      ratTheta_lattice_discrepancy_bounds _ hmono (fun x _ ↦ (hbd x).1) (hbd 0).2 hs w hw k (hk k hmem)
    obtain ⟨hp, hq⟩ := hx r hr
    obtain ⟨hp', hq'⟩ := hx (r * ((i : ℝ) + 1)) (by positivity)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply tendsto_integral_of_dominated_convergence (μ := μ) (fun _ ↦ (B + M) ^ 2)
    (fun i ↦ (((hsm i).sub hH).norm.pow_const 2).aestronglyMeasurable) (integrable_const _)
  · intro i
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc] with r hr
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans (add_le_add (hSM i r hr.1) (hM r hr))
  · filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc,
      (countable_range (fun j : ℕ ↦ (j : ℝ)⁻¹)).ae_notMem μ] with r hr hn
    apply Filter.EventuallyEq.tendsto
    filter_upwards [ratThetaDiscrepancy_eventually_eq r hr.1 hn] with i hi
    have he : ratThetaSmoothRemainderSum S a i r = ratThetaRemainderSum S a r := by
      unfold ratThetaSmoothRemainderSum ratThetaRemainderSum
      exact Finset.sum_congr rfl fun k hmem ↦ by rw [hi k (hk k hmem)]; norm_cast
    simp [he]

/-- Every finite combination of integer remainders transfers its squared error against a bounded
measurable target to a polar-free rational theta lift, with arbitrarily small loss. The lift
vanishes above norm one, and the estimate holds along every family with the prescribed norms. -/
theorem exists_ratTheta_lt_remainder_error_add (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k)
    (H : ℝ → ℂ) (hH : Measurable H) (M : ℝ) (hM : ∀ r ∈ Ioc (0 : ℝ) 1, ‖H r‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) : ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ g : ℝ → Cℚ, (∀ r > 0, ((ideleClassNorm ℚ (g r)).val : ℝ) = r) →
        (∫ r in Ioc (0 : ℝ) 1, ‖homogeneousAdelicTheta 1 f.val (g r) - H r‖ ^ 2) <
          (∫ r in Ioc (0 : ℝ) 1, ‖(∑ k ∈ S, a k * ((⌊r⁻¹⌋₊ % k : ℕ) : ℂ)) - H r‖^2) + ε := by
  obtain ⟨i, hi⟩ := ((ratThetaSmoothRemainderSum_error_tendsto S a hk H hH M hM).eventually_lt_const
    (lt_add_of_pos_right _ hε)).exists
  obtain ⟨_, _, hs, b, hb, he⟩ := ratThetaSmoothCutoff_properties i
  let μ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let c : ℂ := (μ univ).toReal * 2
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ)).ne') (by norm_num)
  let m : ℝ := (i : ℝ) + 1
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) i]
  let a' (k : ℕ) := a k / c
  obtain ⟨h, hval, hEven, h0,_, hpol, hout⟩ := exists_ratStandardAdelicTest_dilationDifferences
    b he (fun r hr ↦ by rw [hb, hs _ hr]; simp) m hm S a' hk
  refine ⟨⟨ratStandardAdelicTest h, hpol⟩, hout, fun g hg ↦ ?_⟩
  have hid (r : ℝ) (hr : 0 < r) :
      homogeneousAdelicTheta 1 (ratStandardAdelicTest h) (g r) = ratThetaSmoothRemainderSum S a i r := by
    rw [ratStandardAdelicTest_homogeneousTheta h hEven h0, hg r hr,
      ratTheta_dilationDifference_tsum (ratThetaSmoothCutoff i) hs r m hr (zero_lt_one.trans_le hm) S a' hk h
        (by intro x; simpa only [hb] using hval x)]
    change ((μ univ).toReal : ℂ) * (2 * _) = _
    rw [← mul_assoc]
    change c * _ = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk'
    dsimp only [a', m]
    field_simp
  change (∫ r in Ioc (0 : ℝ) 1, ‖homogeneousAdelicTheta 1 (ratStandardAdelicTest h) (g r) -
    H r‖^2) < (∫ r in Ioc (0 : ℝ) 1, ‖ratThetaRemainderSum S a r - H r‖^2) + ε
  exact lt_of_eq_of_lt (setIntegral_congr_fun measurableSet_Ioc fun r hr ↦ by rw [hid r hr.1]) hi

/-- Every finite combination of the remainders of the reciprocal floor lies in the ordinary
unit-interval squared-mean closure of supported, polar-free rational theta lifts. -/
theorem exists_ratTheta_approximate_remainders (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ g : ℝ → Cℚ, (∀ r > 0, ((ideleClassNorm ℚ (g r)).val : ℝ) = r) →
        (∫ r in Ioc (0 : ℝ) 1, ‖homogeneousAdelicTheta 1 f.val (g r) -
          ∑ k ∈ S, a k * ((⌊r⁻¹⌋₊ % k : ℕ) : ℂ)‖ ^ 2) < ε := by
  have hm : Measurable (ratThetaRemainderSum S a) := by
    unfold ratThetaRemainderSum
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul ((measurable_of_countable (fun n : ℕ ↦ ((n % k : ℕ) : ℂ))).comp
      measurable_id.inv.nat_floor)
  have hbound (r : ℝ) : ‖ratThetaRemainderSum S a r‖ ≤ ∑ k ∈ S, ‖a k‖ * (k : ℝ) := by
    unfold ratThetaRemainderSum
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro k hmem
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.mod_lt _ (hk k hmem)).le) (norm_nonneg _)
  obtain ⟨f, hs, hf⟩ := exists_ratTheta_lt_remainder_error_add S a hk _ hm _ (fun r _ ↦ hbound r) hε
  exact ⟨f, hs, fun g hg ↦ by simpa [ratThetaRemainderSum] using hf g hg⟩

private theorem ratTheta_floor_integral_le (v : ℕ → ℝ) (M : ℝ) (hv : ∀ n, 0 ≤ v n ∧ v n ≤ M) (N : ℕ) :
    (∫ r in Ioc (0 : ℝ) 1, v ⌊r⁻¹⌋₊) ≤ M / ((N : ℝ) + 1) +
      ∑ j ∈ Finset.range N, v (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  let F (r : ℝ) := v ⌊r⁻¹⌋₊
  let u (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
  have hu (n : ℕ) : 0 < u n := by dsimp [u]; positivity
  have hU (n : ℕ) : u (n + 1) ≤ u n := by
    apply inv_anti₀ (by positivity)
    push_cast
    linarith
  have hmeas : Measurable F := (measurable_of_countable v).comp measurable_id.inv.nat_floor
  have hint (a b : ℝ) : IntegrableOn F (Ioc a b) := by
    apply (integrable_const (μ := volume.restrict (Ioc a b)) M).mono' hmeas.aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_of_nonneg (hv _).1]
    exact (hv _).2
  have hcell (n : ℕ) : (∫ r in Ioc (u (n + 1)) (u n), F r) =
      v (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    have he : ∀ r ∈ Ioc (u (n + 1)) (u n), F r = v (n + 1) := by
      intro r hr
      have hr0 := (hu _).trans hr.1
      apply congrArg v
      apply (Nat.floor_eq_iff (inv_nonneg.mpr hr0.le)).mpr
      refine ⟨?_, ?_⟩
      · have hh := (inv_anti₀ hr0 hr.2)
        simpa [u] using hh
      · have hh := (inv_lt_inv₀ hr0 (hu _)).2 hr.1
        simpa [u] using hh
    rw [setIntegral_congr_fun measurableSet_Ioc he, setIntegral_const, Real.volume_real_Ioc_of_le (hU n)]
    simp only [smul_eq_mul, u, Nat.cast_add_one]
    field_simp
    ring
  have hind (n : ℕ) : (∫ r in Ioc (0 : ℝ) 1, F r) = (∫ r in Ioc 0 (u n), F r) +
      ∑ j ∈ Finset.range n, v (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    induction n with
    | zero => simp [u]
    | succ n ih =>
      have hp := setIntegral_union (μ := volume) (f := F) (Ioc_disjoint_Ioc_of_le (a := 0) (d := u n) (le_refl (u (n + 1))))
        measurableSet_Ioc (hint 0 _) (hint _ _)
      rw [Ioc_union_Ioc_eq_Ioc (hu _).le (hU n), hcell n] at hp
      rw [ih, hp, Finset.sum_range_succ]
      ring
  have hh := setIntegral_mono_on (hint 0 (u N)) (integrable_const (μ := volume.restrict (Ioc 0 (u N))) M)
    measurableSet_Ioc (fun r _ ↦ (hv ⌊r⁻¹⌋₊).2)
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (hu N).le, sub_zero] at hh
  rw [hind N]
  apply add_le_add_left
  simpa [u, div_eq_mul_inv, mul_comm] using hh

private theorem ratTheta_fourModuli_error_lt :
    (∫ r in Ioc (0 : ℝ) 1,
      (((7 * (⌊r⁻¹⌋₊ % 2) + 4 * (⌊r⁻¹⌋₊ % 3) + 2 * (⌊r⁻¹⌋₊ % 5) + ⌊r⁻¹⌋₊ % 7 : ℕ) : ℝ) / 15 - 1) ^ 2) <
      1 / 25 := by
  let d (n : ℕ) := 7 * (n % 2) + 4 * (n % 3) + 2 * (n % 5) + n % 7
  let q (n : ℕ) : ℚ := ((d n : ℚ) / 15 - 1) ^ 2
  let v (n : ℕ) : ℝ := ((d n : ℝ) / 15 - 1) ^ 2
  have hbound (n : ℕ) : 0 ≤ v n ∧ v n ≤ 1 := by
    have hd : d n ≤ 29 := by dsimp [d]; omega
    have hd' : (d n : ℝ) ≤ 29 := by exact_mod_cast hd
    have h : |(d n : ℝ) / 15 - 1| ≤ 1 := abs_le.mpr ⟨by linarith [Nat.cast_nonneg (α := ℝ) (d n)], by linarith⟩
    exact ⟨sq_nonneg _, by simpa [v, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2⟩
  have hrational : (1 : ℚ) / (85 + 1) + ∑ j ∈ Finset.range 85,
      q (j + 1) / (((j : ℚ) + 1) * ((j : ℚ) + 2)) < 1 / 25 := by
    dsimp only [q, d]
    decide +kernel
  have hreal : (1 : ℝ) / ((85 : ℕ) + 1) + ∑ j ∈ Finset.range 85,
      v (j + 1) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) < 1 / 25 := by
    have hcast := (Rat.cast_lt (K := ℝ)).2 hrational
    push_cast [q] at hcast
    simpa [v] using hcast
  exact lt_of_le_of_lt (ratTheta_floor_integral_le v 1 hbound 85) hreal

/-- There is a polar-free rational adelic test whose theta vanishes above norm one and has
ordinary unit-interval squared error less than one twenty-fifth from the constant one. -/
theorem exists_ratTheta_unitInterval_sqError_lt_one_div_twentyFive :
    ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ g : ℝ → Cℚ, (∀ r > 0, ((ideleClassNorm ℚ (g r)).val : ℝ) = r) →
        (∫ r in Ioc (0 : ℝ) 1, ‖homogeneousAdelicTheta 1 f.val (g r) - 1‖ ^ 2) < 1 / 25 := by
  let S : Finset ℕ := {2, 3, 5, 7}
  let a (k : ℕ) : ℂ := (if k = 2 then 7 else if k = 3 then 4 else if k = 5 then 2 else 1) / 15
  have hk : ∀ k ∈ S, 1 ≤ k := by intro k hk; simp [S] at hk; omega
  let E := ∫ r in Ioc (0 : ℝ) 1, ‖(∑ k ∈ S, a k * ((⌊r⁻¹⌋₊ % k : ℕ) : ℂ)) - 1‖ ^ 2
  have he : E < 1 / 25 := by
    convert ratTheta_fourModuli_error_lt using 1
    dsimp only [E]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    let n := ⌊r⁻¹⌋₊
    let y : ℝ := ((7 * (n % 2) + 4 * (n % 3) + 2 * (n % 5) + n % 7 : ℕ) : ℝ) / 15 - 1
    have hs : (∑ k ∈ S, a k * ((n % k : ℕ) : ℂ)) - 1 = (y : ℂ) := by
      norm_num [S, a, y, Finset.sum_insert]
      ring
    change ‖(∑ k ∈ S, a k * ((n % k : ℕ) : ℂ)) - 1‖ ^ 2 = y ^ 2
    rw [hs, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  obtain ⟨f, hs, hf⟩ := exists_ratTheta_lt_remainder_error_add S a hk (fun _ ↦ 1) measurable_const 1 (by simp) (sub_pos.mpr he)
  refine ⟨f, hs, fun g hg ↦ ?_⟩
  have h := hf g hg
  change _ < E + (1 / 25 - E) at h
  linarith

/-- For the rational trivial character, a supported polar-free adelic test approximates the
centered exponential on the negative log-norm half-line with squared error below one twenty-fifth. -/
theorem exists_ratTheta_halfLine_sqError_lt_one_div_twentyFive :
    ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ g : ℝ → Cℚ, (∀ x, ((ideleClassNorm ℚ (g x)).val : ℝ) = Real.exp x) →
        (∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) -
          homogeneousAdelicTheta 1 f.val (g x) * Complex.exp ((x : ℂ) / 2)‖ ^ 2) < 1 / 25 := by
  obtain ⟨f, hs, hf⟩ := exists_ratTheta_unitInterval_sqError_lt_one_div_twentyFive
  refine ⟨f, hs, fun g hg ↦ ?_⟩
  let E (r : ℝ) := ‖homogeneousAdelicTheta 1 f.val (g (Real.log r)) - 1‖ ^ 2
  have hi : (∫ r in Ioc (0 : ℝ) 1, E r) < 1 / 25 :=
    hf (g ∘ Real.log) (fun r hr ↦ (hg (Real.log r)).trans (Real.exp_log hr))
  have he := ratTheta_centered_changeVariables (fun r ↦ homogeneousAdelicTheta 1 f.val (g (Real.log r)))
  simp only [Real.log_exp] at he
  rw [he]
  simpa only [E, norm_sub_rev (homogeneousAdelicTheta 1 _ _) 1] using hi

end RiemannMasullo
