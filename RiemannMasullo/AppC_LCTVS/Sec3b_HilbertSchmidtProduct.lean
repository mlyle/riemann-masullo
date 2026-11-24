module

public import RiemannMasullo.AppC_LCTVS.Sec3b
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Products of Hilbert–Schmidt operators and the trace of a truncated convolution

* `comp_mem_traceClass`: the composite `A ∘ B` of Hilbert–Schmidt operators `B : E → F` and
  `A : F → G` is trace class.
* `nuclear_hilbertSchmidt_comp`: when the composite is an endomorphism (`B : E → F`,
  `A : F → E`), it is nuclear.
* `hilbertTrace_integralKernelOperator_comp_of_hilbertSchmidt`: discharges the nuclearity premise
  of `hilbertTrace_integralKernelOperator_comp`, the two-factor trace calculation of §C.3.7,
  pp. 707–708.
* On the real line, for a measurable window `C` of finite measure and `u, v ∈ L²`, the doubly
  truncated convolution `f ↦ 1_C · ((u ⋆ v) ⋆ (1_C f))` is the composite of the Hilbert–Schmidt
  factors `P_C conv u` and `conv v P_C` (`cutConv_comp_apply`, `cutConv_comp_unique`), and its trace is
  `|C| (u ⋆ v)(0)` (`hilbertTrace_cutConv_comp`).

This is a model for ERRATA I395 (nuclearity of the truncated operator in Theorem 12.4.1.1):
a Hilbert–Schmidt factorization gives nuclearity and the diagonal trace together. It does not
treat the paper's operator, whose dilations do not commute with the additive frequency cutoff.

The trace-class product argument and the operator identity were first written by ChatGPT in
local scratch files during this work.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RiemannMasullo

variable {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The composite of two Hilbert–Schmidt operators is trace class (`S₂ · S₂ ⊆ S₁`). The proof
bounds the approximation numbers, `a_{2n+1}(AB) ≤ a_n(A) a_n(B)` (`approximationNumber_comp_le`),
and uses `2ab ≤ a² + b²`. -/
theorem comp_mem_traceClass (A : hilbertSchmidtOperators F G)
    (B : hilbertSchmidtOperators E F) :
    A.val.comp B.val ∈ traceClassOperators E G := by
  let T := A.val.comp B.val
  have hc : IsCompactOperator T := A.property.1.comp_clm B.val
  obtain ⟨d⟩ := (isCompactOperator_iff_nonempty_singularExpansion T).mp hc
  have hn (n : ℕ) : 0 ≤ approximationNumber T n := d.coeff_eq_approximationNumber n ▸
    (d.coeff n).coe_nonneg
  have hmono : Antitone (approximationNumber T) := by
    intro i j hij
    rw [← d.coeff_eq_approximationNumber i, ← d.coeff_eq_approximationNumber j]
    exact d.antitone_coeff hij
  have hA : Summable (fun n ↦ approximationNumber A.val n ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using A.property.2
  have hB : Summable (fun n ↦ approximationNumber B.val n ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using B.property.2
  have hb (n j : ℕ) (hj : n + n + 1 ≤ j) : approximationNumber T j ≤
      approximationNumber A.val n ^ 2 + approximationNumber B.val n ^ 2 := by
    refine (hmono hj).trans ((approximationNumber_comp_le A.val B.val n n).trans ?_)
    nlinarith [sq_nonneg (approximationNumber A.val n - approximationNumber B.val n),
      sq_nonneg (approximationNumber A.val n), sq_nonneg (approximationNumber B.val n)]
  change IsCompactOperator T ∧ Summable (fun n ↦ approximationNumber T n ^ (1 : ℝ))
  simp only [Real.rpow_one]
  refine ⟨hc, (summable_nat_add_iff 1).mp ?_⟩
  apply Summable.even_add_odd
  · exact (hA.add hB).of_nonneg_of_le (fun _ ↦ hn _) (fun n ↦ hb n _ (by omega))
  · exact (hA.add hB).of_nonneg_of_le (fun _ ↦ hn _) (fun n ↦ hb n _ (by omega))

/-- For Hilbert–Schmidt operators `B : E → F` and `A : F → E`, the endomorphism `A ∘ B` of `E` is
nuclear. -/
theorem nuclear_hilbertSchmidt_comp (A : hilbertSchmidtOperators F E)
    (B : hilbertSchmidtOperators E F) : IsNuclearOperator (A.val.comp B.val) :=
  (mem_traceClassOperators_iff_isNuclearOperator _).mp (comp_mem_traceClass A B)

/-- Paper: §C.3.7, pp. 707–708, the trace of a product of two Hilbert–Schmidt factors. The
composite of two integral operators with square-integrable kernels is nuclear, and its trace is
the product-space integral of the first kernel times the second with its variables reversed.
Deviation: Nuclearity is proved here (`nuclear_hilbertSchmidt_comp`); the existing statement
`hilbertTrace_integralKernelOperator_comp` takes it as a hypothesis. Theorem C.3.7.1(2)(b),
p. 708, is a different statement: it asserts a smoothed diagonal for the kernel of one nuclear
operator, and nothing here is about smoothing. -/
theorem hilbertTrace_integralKernelOperator_comp_of_hilbertSchmidt {X : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ] (a b : Lp ℂ 2 (μ.prod μ)) :
    hilbertTrace ⟨(integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val,
      nuclear_hilbertSchmidt_comp _ _⟩ =
        ∫ p : X × X, a p * b p.swap ∂(μ.prod μ) :=
  hilbertTrace_integralKernelOperator_comp μ a b _

/-! ### The truncated convolution kernels on the real line -/

/-- The kernel `(x, z) ↦ 1_C(x) u(x − z)` of `P_C conv u`. -/
def cutConvKernel (C : Set ℝ) (u : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  C.indicator (fun _ ↦ (1 : ℂ)) p.1 * u (p.1 - p.2)

theorem memLp_cutConvKernel {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {u : ℝ → ℂ} (hu : MemLp u 2) : MemLp (cutConvKernel C u) 2 (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (cutConvKernel C u) (volume.prod volume) := by
    have hsub : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ u (p.1 - p.2)) (volume.prod volume) :=
      hu.aestronglyMeasurable.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)
    exact (((measurable_const.indicator hC).comp measurable_fst).aestronglyMeasurable).mul hsub
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hu2 : Integrable (fun w ↦ ‖u w‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hpt (p : ℝ × ℝ) : ‖cutConvKernel C u p‖ ^ 2 =
      C.indicator (fun _ ↦ (1 : ℝ)) p.1 * ‖u (p.1 - p.2)‖ ^ 2 := by
    by_cases h : p.1 ∈ C <;> simp [cutConvKernel, h]
  have hsq_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) p.1 * ‖u (p.1 - p.2)‖ ^ 2)
      (volume.prod volume) :=
    (hmeas.norm.pow 2).congr (Filter.Eventually.of_forall hpt)
  simp_rw [hpt]
  refine (integrable_prod_iff hsq_meas).mpr ⟨Filter.Eventually.of_forall fun x ↦ ?_, ?_⟩
  · show Integrable (fun z : ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (x - z)‖ ^ 2)
    exact (hu2.comp_sub_left x).const_mul (C.indicator (fun _ ↦ (1 : ℝ)) x)
  · show Integrable (fun x : ℝ ↦ ∫ z, ‖C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (x - z)‖ ^ 2‖)
    have hK (x : ℝ) : (∫ z, ‖C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (x - z)‖ ^ 2‖) =
        C.indicator (fun _ ↦ ∫ w, ‖u w‖ ^ 2) x := by
      by_cases h : x ∈ C
      · simp only [h, Set.indicator_of_mem, one_mul, norm_pow, norm_norm]
        exact integral_sub_left_eq_self (fun w ↦ ‖u w‖ ^ 2) volume x
      · simp [h]
    simp_rw [hK]
    exact (integrable_indicator_iff hC).mpr (integrableOn_const hCf)

/-- The kernel `(z, y) ↦ v(z − y) 1_C(y)` of `conv v P_C`, written as a swap of a cut kernel. -/
theorem memLp_convCutKernel {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {v : ℝ → ℂ} (hv : MemLp v 2) :
    MemLp (fun p : ℝ × ℝ ↦ v (p.1 - p.2) * C.indicator (fun _ ↦ (1 : ℂ)) p.2)
      2 (volume.prod volume) := by
  have hv' : MemLp (fun w ↦ v (-w)) 2 := hv.comp_measurePreserving (Measure.measurePreserving_neg _)
  have h := (memLp_cutConvKernel hC hCf hv').comp_measurePreserving
    (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun p ↦ ?_)
  · exact h.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun p ↦ by
      simp [cutConvKernel, Function.comp, neg_sub, mul_comm])
  · simp [cutConvKernel, Function.comp, neg_sub, mul_comm]

/-- **Route 2 at the real place.** The truncated convolution factors as a product of two
Hilbert–Schmidt operators; the product is nuclear and its trace is `|C| · ∫ u(w) v(−w) dw`,
that is `|C| (u ⋆ v)(0)`. -/
theorem hilbertTrace_cutConv_comp {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {u v : ℝ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) :
    let a := (memLp_cutConvKernel hC hCf hu).toLp
    let b := (memLp_convCutKernel hC hCf hv).toLp
    hilbertTrace ⟨(integralKernelOperator volume a).val.comp (integralKernelOperator volume b).val,
      nuclear_hilbertSchmidt_comp _ _⟩ =
      (volume C).toReal * ∫ w, u w * v (-w) := by
  intro a b
  rw [hilbertTrace_integralKernelOperator_comp]
  have ha := (memLp_cutConvKernel hC hCf hu).coeFn_toLp
  have hb := (memLp_convCutKernel hC hCf hv).coeFn_toLp
  have hbs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
    ).quasiMeasurePreserving.ae_eq_comp hb
  have heq : (fun p : ℝ × ℝ ↦ a p * b p.swap) =ᵐ[volume.prod volume]
      fun p ↦ C.indicator (fun _ ↦ (1 : ℂ)) p.1 * (u (p.1 - p.2) * v (p.2 - p.1)) := by
    filter_upwards [ha, hbs] with p hpa hpb
    rw [hpa]
    rw [show b p.swap = _ from hpb]
    by_cases h : p.1 ∈ C <;> simp [cutConvKernel, h, Prod.swap]
  rw [integral_congr_ae heq]
  have hint : Integrable (fun p : ℝ × ℝ ↦
      C.indicator (fun _ ↦ (1 : ℂ)) p.1 * (u (p.1 - p.2) * v (p.2 - p.1)))
      (volume.prod volume) := by
    have hprod := (memLp_cutConvKernel hC hCf hu).integrable_mul
      ((memLp_convCutKernel hC hCf hv).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))
    refine hprod.congr (Filter.Eventually.of_forall fun p ↦ ?_)
    by_cases h : p.1 ∈ C <;> simp [cutConvKernel, h, Prod.swap, Function.comp, mul_comm]
  rw [integral_prod _ hint]
  have hin (x : ℝ) : (∫ z, C.indicator (fun _ ↦ (1 : ℂ)) x * (u (x - z) * v (z - x))) =
      C.indicator (fun _ ↦ ∫ w, u w * v (-w)) x := by
    by_cases h : x ∈ C
    · simp only [h, Set.indicator_of_mem, one_mul]
      have := integral_sub_left_eq_self (fun w ↦ u w * v (-w)) volume x
      simpa [neg_sub] using this
    · simp [h]
  simp_rw [hin]
  rw [integral_indicator hC, setIntegral_const, Measure.real, Complex.real_smul]

open MeasureTheory

/-- Equality on every L² input with the integral against the doubly truncated convolution. -/
theorem cutConv_comp_apply {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {u v : ℝ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    let a := (memLp_cutConvKernel hC hCf hu).toLp
    let b := (memLp_convCutKernel hC hCf hv).toLp
    ∀ᵐ x ∂volume,
      ((integralKernelOperator volume a).val.comp (integralKernelOperator volume b).val f) x =
      C.indicator (fun _ ↦ (1 : ℂ)) x * ∫ y, (∫ w, u w * v ((x-y)-w)) *
        (C.indicator (fun _ ↦ (1 : ℂ)) y * f y) := by
  intro a b
  let I := C.indicator (fun _ ↦ (1 : ℂ))
  let B (p : ℝ × ℝ) := v (p.1-p.2) * I p.2
  let g := (integralKernelOperator volume b).val f
  have hb : MemLp B 2 (volume.prod volume) := memLp_convCutKernel hC hCf hv
  have gb : ∀ᵐ z, g z = ∫ y, B (z,y) * f y := by
    filter_upwards [integralKernelOperator_apply volume b f,
      Measure.ae_ae_of_ae_prod hb.coeFn_toLp] with z hz hzb
    refine hz.2.trans (integral_congr_ae ?_)
    filter_upwards [hzb] with y hy
    exact congrArg (· * f y) hy
  filter_upwards [integralKernelOperator_apply volume a g,
    Measure.ae_ae_of_ae_prod (memLp_cutConvKernel hC hCf hu).coeFn_toLp] with x hx hxa
  let r (z : ℝ) := u (x-z)
  have hr : MemLp r 2 := hu.comp_measurePreserving (volume.measurePreserving_sub_left x)
  let J (p : ℝ × ℝ) := r p.1 * B p * f p.2
  have hj : Integrable J (volume.prod volume) := by
    have hr2 := (memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr
    have hf2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    have hb2 := (memLp_two_iff_integrable_sq_norm hb.aestronglyMeasurable).mp hb
    apply (((hr2.mul_prod hf2).add hb2).const_mul (1/2 : ℝ)).mono'
    · exact ((hr.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        hb.aestronglyMeasurable).mul
        ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    · filter_upwards with p
      dsimp only [J,Pi.add_apply]
      simp only [norm_mul]
      nlinarith [sq_nonneg (‖r p.1‖ * ‖f p.2‖ - ‖B p‖)]
  calc
    _ = ∫ z, a (x,z) * g z := hx.2
    _ = I x * ∫ z, ∫ y, J (z,y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hxa,gb] with z haz hgz
      rw [haz,hgz,← integral_const_mul]
      simp only [cutConvKernel,J,r,I,mul_assoc]
      exact integral_const_mul _ _
    _ = I x * ∫ y, ∫ z, J (z,y) := congrArg (I x * ·)
      ((integral_prod J hj).symm.trans (integral_prod_symm J hj))
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      calc
        _ = ∫ z, (u (x-z) * v (z-y)) * (I y * f y) := by
          apply integral_congr_ae
          filter_upwards with z
          simp only [J,r,B,mul_assoc]
        _ = (∫ z, u (x-z) * v (z-y)) * (I y * f y) := integral_mul_const _ _
        _ = _ := by
          congr 1
          have h := integral_sub_left_eq_self (fun w ↦ u w * v ((x-y)-w)) volume x
          simpa only [show ∀ z : ℝ, (x-y)-(x-z) = z-y from fun z ↦ by ring] using h

/-- The composite is the unique bounded map with the double-window convolution action. -/
theorem cutConv_comp_unique {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {u v : ℝ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    (∀ f : Lp ℂ 2 (volume : Measure ℝ), ∀ᵐ x ∂volume, T f x =
      C.indicator (fun _ ↦ (1 : ℂ)) x * ∫ y, (∫ w, u w * v ((x-y)-w)) *
        (C.indicator (fun _ ↦ (1 : ℂ)) y * f y)) ↔
    T = (integralKernelOperator volume (memLp_cutConvKernel hC hCf hu).toLp).val.comp
      (integralKernelOperator volume (memLp_convCutKernel hC hCf hv).toLp).val := by
  constructor
  · intro h
    ext1 f
    apply Lp.ext
    filter_upwards [h f, cutConv_comp_apply hC hCf hu hv f] with x hx hprod
    exact hx.trans hprod.symm
  · rintro rfl
    exact cutConv_comp_apply hC hCf hu hv


end RiemannMasullo
