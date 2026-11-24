module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import all RiemannMasullo.AppC_LCTVS.Sec1
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.TranslationDifference
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Baire.CompleteMetrizable
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWiener
import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.Topology.MetricSpace.CompactQuotient

/-!
# Periodization and Schauder bases on the positive real axis

Masullo, §4.2, pp. 161–174. The logarithmic coordinate is (x = log t).
The circle coordinate is (x / log γ) modulo one.
-/

@[expose] public noncomputable section

open Bornology Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace RiemannMasullo

local notation "E" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "G" => ElementaryLieGroup 0 1 0 (PUnit : Type)
local notation "T" => AddCircle (1 : ℝ)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) : G)
local notation "freq" => Equiv.intEquivNat.symm
local notation "phase[" γ ", " m "]" => (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (Real.log γ : ℂ))

section Periodization

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Definition 4.2.1.1, p. 162. Sum the translates of a logarithmic profile
at a representative of the unit-circle coordinate.
Deviation: The same formula is used on ordinary Schwartz profiles, as in Remark 4.2.2.6. -/
def cyclicPeriodizationValue (_hγ : 1 < γ) (f : 𝓢(ℝ, ℂ)) (g : G) : ℂ :=
  ∑' k : ℤ, f (Real.log γ * ((AddCircle.equivIco 1 0 (g.2.1 0)).val + k))

/-- Paper: Definition 4.2.1.1, p. 162. The sum converges and can be computed at
any real lift of the circle coordinate.
Deviation: This also checks the formula on the ordinary Schwartz space. -/
theorem cyclicPeriodizationValue_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodizationValue γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (f.compSubConstCLM ℂ (-x))
  have hs : Summable (fun k : ℤ ↦ F (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  let a (k : ℤ) := f (x + (k : ℝ) * L)
  have ha : Summable a := by
    simpa [a, F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, add_comm] using hs
  let r := ((AddCircle.equivIco (1 : ℝ) 0) ((x / L : ℝ) : T)).val
  change HasSum a (∑' k : ℤ, f (L * (r + k)))
  have hr : r = x / L - ⌊x / L⌋ := by
    dsimp only [r]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, ← Int.self_sub_floor]
  convert ha.hasSum using 1
  calc
    (∑' k : ℤ, f (L * (r + k))) = ∑' k : ℤ, a ((Equiv.subRight ⌊x / L⌋) k) := by
      apply tsum_congr
      intro k
      simp only [a, Equiv.subRight_apply, Int.cast_sub, hr]
      congr 1
      field_simp
      ring
    _ = ∑' k : ℤ, a k := (Equiv.subRight ⌊x / L⌋).tsum_eq a

/-- A smooth periodic lift gives an elementary Schwartz function on the circle. -/
private theorem mem_elementarySchwartz_circle_of_contDiff {h : T → ℂ}
    (hs : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x : T))) :
    (fun g : G ↦ h (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let X := EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)
  let φ : G → ℂ := fun g ↦ h (g.2.1 0)
  let L : X →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have hφ (a : Fin 0 → ℤ) (b : PUnit) :
      ContDiff ℝ ∞ (fun xt ↦ φ (elementaryCover xt a b)) := hs.comp L.contDiff
  refine ⟨hφ, fun i ↦ ?_⟩
  let s (x : ℝ) : X := (0, x • EuclideanSpace.single 0 1)
  have hsc : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
  let D := elementaryPartial φ i.2.1 i.2.2.1
  have hD := elementaryPartial_descends φ i.2.1 i.2.2.1 0 PUnit.unit (hφ 0 PUnit.unit)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hD.1.continuous.comp hsc).continuousOn
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = PUnit.unit := Subsingleton.elim _ _
  subst a b
  let r := (AddCircle.equivIco (1 : ℝ) 0) (xt.2 0 : T)
  have hr : (r : ℝ) ∈ Icc 0 1 := Ico_subset_Icc_self (by simpa using r.property)
  have he : elementaryCover (s r) (0 : Fin 0 → ℤ) PUnit.unit =
      elementaryCover xt 0 PUnit.unit := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r.val • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) : T) = _
    trans (r.val : T)
    · simp [PiLp.smul_apply]
    · exact AddCircle.coe_equivIco
  have hbound : ‖D xt 0 PUnit.unit‖ ≤ C := by
    dsimp only [D]
    rw [← hD.2 (s r) xt he]
    exact hC r hr
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Paper: Lemma 4.2.1.5(1), p. 165. The orbit sum gives a smooth function
on the circle.
Deviation: Smoothness also holds on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_mem (f : 𝓢(ℝ, ℂ)) :
    cyclicPeriodizationValue γ hγ f ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let h (z : T) := cyclicPeriodizationValue γ hγ f (point z)
  change (fun g : G ↦ h (g.2.1 0)) ∈ _
  apply mem_elementarySchwartz_circle_of_contDiff
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have he : (fun x : ℝ ↦ h (x : T)) = fun x : ℝ ↦ ∑' n : ℤ, F (x + n) := by
    funext x
    simpa [h, F, e, L, hL, (Real.log_pos hγ).ne', add_mul] using
      (cyclicPeriodizationValue_hasSum γ hγ f (x * L)).tsum_eq.symm
  rw [he]
  exact schwartz_contDiff_periodization F

/-- Paper: Lemma 4.2.1.5(2), p. 165. The orbit sum is linear and continuous
in the Schwartz profile.
Deviation: The bundled properties also hold on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_spec :
    (∀ f g, cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g) ∧
    (∀ (c : ℂ) f, cyclicPeriodizationValue γ hγ (c • f) = c • cyclicPeriodizationValue γ hγ f) ∧
    Continuous (Y := S) (fun f ↦ (⟨cyclicPeriodizationValue γ hγ f,
      cyclicPeriodizationValue_mem γ hγ f⟩ : S)) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have he (g : G) : ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] ℂ, ∀ f, L f = cyclicPeriodizationValue γ hγ f g := by
    let r := ((AddCircle.equivIco (1 : ℝ) 0) (g.2.1 0)).val
    let t (k : ℤ) := Real.log γ * (r + k)
    have ht (k : ℤ) : t k = Real.log γ * r + (k : ℝ) * Real.log γ := by dsimp [t]; ring
    let ev (k : ℤ) := (BoundedContinuousFunction.evalCLM ℂ (t k)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    let P (s : Finset ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := ∑ k ∈ s, ev k
    have hlim : Filter.Tendsto (fun s f ↦ P s f) Filter.atTop
        (𝓝 (fun f ↦ cyclicPeriodizationValue γ hγ f g)) := by
      rw [tendsto_pi_nhds]
      intro f
      have hs : Summable fun k : ℤ ↦ f (t k) := by
        simpa only [ht] using (cyclicPeriodizationValue_hasSum γ hγ f (Real.log γ * r)).summable
      have hP (s : Finset ℤ) : P s f = ∑ k ∈ s, f (t k) := by
        simp only [P, sum_apply]
        rfl
      simp_rw [hP]
      exact hs.hasSum
    exact ⟨continuousLinearMapOfTendsto P hlim, fun _ ↦ rfl⟩
  choose L hL using he
  have hadd (f g : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g := by
    funext x
    simpa only [Pi.add_apply, ← hL] using (L x).map_add f g
  have hsmul (c : ℂ) (f : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (c • f) =
      c • cyclicPeriodizationValue γ hγ f := by
    funext x
    simpa only [Pi.smul_apply, ← hL] using (L x).map_smul c f
  let A : 𝓢(ℝ, ℂ) →ₗ[ℂ] S :=
    { toFun f := ⟨_, cyclicPeriodizationValue_mem γ hγ f⟩
      map_add' f g := Subtype.ext (hadd f g)
      map_smul' c f := Subtype.ext (hsmul c f) }
  exact ⟨hadd, hsmul, continuous_toElementarySchwartz_of_eval A (fun g ↦ ⟨L g, hL g⟩)⟩

/-- Paper: Remark 4.2.2.6, p. 173. The cyclic orbit sum is a continuous linear
map from ordinary Schwartz profiles to smooth functions on the circle. -/
def cyclicSchwartzPeriodization : 𝓢(ℝ, ℂ) →L[ℂ] S where
  toFun f := ⟨cyclicPeriodizationValue γ hγ f, cyclicPeriodizationValue_mem γ hγ f⟩
  map_add' f g := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).1 f g)
  map_smul' c f := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).2.1 c f)
  cont := (cyclicPeriodizationValue_spec γ hγ).2.2

/-- Paper: Remark 4.2.2.6, p. 173. On the ordinary Schwartz space, periodization
has the same absolutely convergent orbit sum on a logarithmic lift. -/
theorem cyclicSchwartzPeriodization_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicSchwartzPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  exact cyclicPeriodizationValue_hasSum γ hγ f x

/-- Paper: Definition 4.2.1.1, p. 162. Periodization of an exponentially
decaying Schwartz function sums its translates by integer powers of γ.
Deviation: The source is represented by logarithmic profiles and the target
by the elementary Schwartz space on the unit circle. -/
def cyclicPeriodization : E →ₗ[ℂ] S :=
  (cyclicSchwartzPeriodization γ hγ).toLinearMap.comp
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩)

/-- Paper: (4.2.1.2), p. 162. The periodized value is the sum over the orbit
of any logarithmic lift. The statement records convergence of the series. -/
theorem cyclicPeriodization_hasSum (f : E) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f.val (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  refine (cyclicSchwartzPeriodization_hasSum γ hγ
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩ f) x).congr_fun fun k ↦ ?_
  simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
    (logExponentialDecayTwist_apply univ ⟨0, mem_univ _⟩ f
      (x + (k : ℝ) * Real.log γ)).symm

end Periodization

section Fourier

/-- Paper: (4.2.1.3), p. 162. The circle Fourier monomial is smooth and
belongs to the elementary Schwartz space. -/
theorem cyclicExponential_mem (m : ℤ) :
    (fun g : G ↦ fourier m (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  apply mem_elementarySchwartz_circle_of_contDiff
  have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  simp only [fourier_coe_apply]
  fun_prop

/-- Paper: (4.2.1.3), p. 162. The exponential system consists of the usual
Fourier monomials in the normalized circle coordinate. -/
def cyclicExponential (m : ℤ) : S :=
  ⟨fun g ↦ fourier m (g.2.1 0), cyclicExponential_mem m⟩

/-- Paper: (4.2.1.3), p. 162. The monomial pulled back to the positive real
axis is the power with exponent (2πim / log γ).
Deviation: The argument x on the cover is the logarithm of the positive variable. -/
theorem cyclicExponential_apply (γ : ℝ) (hγ : 1 < γ) (m : ℤ) (x : ℝ) :
    cyclicExponential m (point ((x / Real.log γ : ℝ) : T)) =
      Complex.exp (phase[γ, m] * (x : ℂ)) := by
  change fourier m ((x / Real.log γ : ℝ) : T) = _
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [ne_of_gt (Real.log_pos hγ)]

/-- Paper: (4.2.1.4), p. 162. The normalized circle Fourier coefficient is
linear and continuous for the smooth topology. -/
theorem cyclicFourierCoeff_spec (m : ℤ) :
    (∀ f g : S, fourierCoeff (fun z : T ↦ (f + g) (point z)) m =
      fourierCoeff (fun z : T ↦ f (point z)) m + fourierCoeff (fun z : T ↦ g (point z)) m) ∧
    (∀ (c : ℂ) (f : S), fourierCoeff (fun z : T ↦ (c • f) (point z)) m =
      c * fourierCoeff (fun z : T ↦ f (point z)) m) ∧
    Continuous (fun f : S ↦ fourierCoeff (fun z : T ↦ f (point z)) m) := by
  let ev (f : S) (z : T) := f (point z)
  have hc (f : S) : Continuous (ev f) := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    let s (x : ℝ) := ((0, x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
      EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1))
    have hs : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
    have he (x : ℝ) : elementaryCover (s x) (0 : Fin 0 → ℤ) PUnit.unit = point (x : T) := by
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [elementaryCover, s, PiLp.smul_apply]
    simpa only [Function.comp_def, ev, he] using ((f.property.1 0 PUnit.unit).continuous.comp hs)
  have hInt (f : S) : Integrable (ev f) AddCircle.haarAddCircle :=
    (hc f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd (f g : S) : fourierCoeff (ev (f + g)) m = fourierCoeff (ev f) m + fourierCoeff (ev g) m :=
    congrFun (fourierCoeff.add (hInt f) (hInt g)) m
  have hsmul (c : ℂ) (f : S) : fourierCoeff (ev (c • f)) m = c * fourierCoeff (ev f) m :=
    fourierCoeff.const_mul (ev f) c m
  let L : S →ₗ[ℂ] ℂ := { toFun f := fourierCoeff (ev f) m, map_add' := hadd, map_smul' := hsmul }
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, 0, 0)
  have hp : Continuous (fun f : S ↦ elementarySchwartzSeminorm i f) :=
    (withGeneratingSeminorms_spec _ _).continuous_seminorm i
  refine ⟨hadd, hsmul, (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    Seminorm.continuous_of_le (q := (elementarySchwartzSeminorm i : Seminorm ℂ S)) hp ?_⟩
  intro f
  have hb (z : T) : ‖ev f z‖ ≤ elementarySchwartzSeminorm i f := by
    change (‖ev f z‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
    apply ENNReal.toReal_mono (f.property.2 i).ne
    rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
    exact le_iSup (fun g ↦ (‖f g‖₊ : ENNReal)) (point z)
  have h := norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure T))
    (f := fun z : T ↦ fourier (-m) z • ev f z)
    (ae_of_all _ fun z ↦ by simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb z)
  change ‖fourierCoeff (ev f) m‖ ≤ elementarySchwartzSeminorm i f
  rw [fourierCoeff]
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- Paper: (4.2.1.4), p. 162. The coefficient uses Mathlib's Fourier integral
with probability Haar measure, which absorbs the factor (1 / log γ). -/
def cyclicFourierCoeff (m : ℤ) : StrongDual ℂ S where
  toFun f := fourierCoeff (fun z : T ↦ f (point z)) m
  map_add' := (cyclicFourierCoeff_spec m).1
  map_smul' := (cyclicFourierCoeff_spec m).2.1
  cont := (cyclicFourierCoeff_spec m).2.2

/-- Paper: Lemma 4.2.1.2, p. 162. A monomial has its own coefficient equal to
one and every other coefficient zero. -/
theorem cyclicFourierCoeff_exponential (m n : ℤ) :
    cyclicFourierCoeff m (cyclicExponential n) = if m = n then 1 else 0 := by
  change fourierCoeff (fourier n : C(T, ℂ)) m = _
  rw [fourierCoeff_fourier]
  by_cases h : m = n <;> simp [h]

local notation "Cover" => EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)

/-- Pull a circle Schwartz function back to its real periodic lift. -/
private def cyclicLift (f : S) (x : ℝ) : ℂ := f (point (x : T))

private theorem cyclicCover_eq_point (xt : Cover) (a : Fin 0 → ℤ) (b : PUnit) :
    elementaryCover xt a b = point ((xt.2 0 : ℝ) : T) := by
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Subsingleton.elim _ _))
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

private theorem cyclicLift_contDiff (f : S) : ContDiff ℝ ∞ (cyclicLift f) := by
  let s (x : ℝ) : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : ContDiff ℝ ∞ s := contDiff_const.prodMk (contDiff_id.smul contDiff_const)
  have he (x : ℝ) : elementaryCover (s x) 0 PUnit.unit = point (x : T) := by
    rw [cyclicCover_eq_point]
    simp [s, PiLp.smul_apply]
  unfold cyclicLift
  simpa only [Function.comp_def, he] using (f.property.1 0 PUnit.unit).comp hs

private theorem cyclicLift_periodic (f : S) : Periodic (cyclicLift f) 1 := by
  intro x
  simp [cyclicLift]

/-- The mixed partial in the one-circle case is the ordinary iterated derivative. -/
private theorem cyclicPartial_eq (f : S) (i : ElementarySchwartzIndex 0 1 0)
    (xt : Cover) (a : Fin 0 → ℤ) (b : PUnit) :
    elementaryPartial f.val i.2.1 i.2.2.1 xt a b =
      iteratedDeriv (i.2.2.1 0) (cyclicLift f) (xt.2 0) := by
  let L : Cover →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  let v : Cover := (0, EuclideanSpace.single 0 1)
  have hL : L v = 1 := by simp [L, v]
  let directions : List Cover := List.replicate (i.2.2.1 0) v
  have hdirs :
      (List.ofFn (fun j : Fin 0 ↦ List.replicate (i.2.1 j)
        ((EuclideanSpace.single j 1, 0) : Cover))).flatten ++
      (List.ofFn (fun j : Fin 1 ↦ List.replicate (i.2.2.1 j)
        ((0, EuclideanSpace.single j 1) : Cover))).flatten = directions := by
    simp [directions, v, List.ofFn_succ]
  dsimp only [elementaryPartial]
  rw [hdirs]
  simp only [cyclicCover_eq_point]
  change iteratedFDeriv ℝ directions.length (cyclicLift f ∘ L) xt directions.get = _
  rw [L.iteratedFDeriv_comp_right (cyclicLift_contDiff f) xt (by simp)]
  have hget : (fun j : Fin directions.length ↦ L (directions.get j)) = fun _ ↦ 1 := by
    funext j
    simp [directions, List.get_eq_getElem, hL]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, hget,
    ← iteratedDeriv_eq_iteratedFDeriv, show directions.length = i.2.2.1 0 by simp [directions]]
  rfl

/-- Bounding the derivative on a fundamental interval bounds the Schwartz seminorm. -/
private theorem cyclicSeminorm_le (f : S) (i : ElementarySchwartzIndex 0 1 0)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ Ico (0 : ℝ) 1, ‖iteratedDeriv (i.2.2.1 0) (cyclicLift f) x‖ ≤ C) :
    elementarySchwartzSeminorm i f ≤ C := by
  change (elementarySchwartzBound f.val i).toReal ≤ C
  rw [← ENNReal.toReal_ofReal hC]
  apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  obtain ⟨x, hx, he⟩ := AddCircle.eq_coe_Ico ((xt.2 0 : ℝ) : T)
  let s : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : s.2 0 = x := by simp [s, PiLp.smul_apply]
  have hcover : elementaryCover s a b = elementaryCover xt a b := by
    rw [cyclicCover_eq_point, cyclicCover_eq_point, hs, he]
  have hD := elementaryPartial_descends f.val i.2.1 i.2.2.1 a b (f.property.1 a b)
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  rw [← hD.2 s xt hcover, cyclicPartial_eq, hs]
  exact ENNReal.ofReal_le_ofReal (h x hx)

private theorem cyclicSeminorm_ge (f : S) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (cyclicLift f) x‖ ≤
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ k, 0)
  let s : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : s.2 0 = x := by simp [s, PiLp.smul_apply]
  change (‖iteratedDeriv k (cyclicLift f) x‖₊ : ENNReal).toReal ≤
    (elementarySchwartzBound f.val i).toReal
  apply ENNReal.toReal_mono (f.property.2 i).ne
  refine le_iSup_of_le s (le_iSup_of_le 0 (le_iSup_of_le PUnit.unit ?_))
  simp only [Fin.prod_univ_zero, one_mul, cyclicPartial_eq f i s 0 PUnit.unit, hs, i, le_rfl]

private theorem cyclicFourierCoeff_eq_on (f : S) (m : ℤ) :
    cyclicFourierCoeff m f = fourierCoeffOn zero_lt_one (cyclicLift f) m := by
  change fourierCoeff (fun z : T ↦ f (point z)) m = _
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
  simp [cyclicLift]

/-- The net of finite Fourier sums converges in the circle Schwartz topology. -/
private theorem cyclicFourier_hasSum (f : S) :
    HasSum (fun m : ℤ ↦ cyclicFourierCoeff m f • cyclicExponential m) f := by
  let P (s : Finset ℤ) : S := ∑ m ∈ s, cyclicFourierCoeff m f • cyclicExponential m
  change Filter.Tendsto P Filter.atTop (𝓝 f)
  rw [elementarySchwartz_withSeminorms.tendsto_nhds]
  intro i ε hε
  have hP (s : Finset ℤ) : cyclicLift (P s) = fun t : ℝ ↦
      ∑ m ∈ s, fourierCoeffOn zero_lt_one (cyclicLift f) m * fourier m (t : T) := by
    funext t
    let ev : S →+ ℂ :=
      (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) (point (t : T))).comp
        (elementarySchwartzSubmodule 0 1 0 PUnit).subtype.toAddMonoidHom
    change ev (∑ m ∈ s, cyclicFourierCoeff m f • cyclicExponential m) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← cyclicFourierCoeff_eq_on]
    rfl
  have h := smooth_fourier_series (cyclicLift_contDiff f) (cyclicLift_periodic f) (i.2.2.1 0)
  simp only [← hP, Metric.tendstoUniformlyOn_iff, dist_eq_norm] at h
  filter_upwards [h (ε / 2) (by positivity)] with s hs
  refine lt_of_le_of_lt (cyclicSeminorm_le (P s - f) i (C := ε / 2) (by positivity) fun x hx ↦ ?_)
    (by linarith)
  change ‖iteratedDeriv (i.2.2.1 0) (fun x ↦ cyclicLift (P s) x - cyclicLift f x) x‖ ≤ _
  rw [iteratedDeriv_fun_sub ((cyclicLift_contDiff (P s)).of_le (by simp)).contDiffAt
    ((cyclicLift_contDiff f).of_le (by simp)).contDiffAt]
  rw [norm_sub_rev]
  exact (hs x hx).le

private def cyclicFrequency (m : ℤ) : ℂ := 2 * Real.pi * Complex.I * m

private theorem fourierCoeffOn_iteratedDeriv_cyclic (f : S) (m : ℤ) (k : ℕ) :
    fourierCoeffOn zero_lt_one (iteratedDeriv k (cyclicLift f)) m =
      cyclicFrequency m ^ k * cyclicFourierCoeff m f := by
  have hdiff (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j (cyclicLift f)) := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using cyclicLift_contDiff f
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2
  have hper (j : ℕ) : Periodic (iteratedDeriv j (cyclicLift f)) 1 := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using cyclicLift_periodic f
    | succ j ih =>
      rw [iteratedDeriv_succ]
      intro x
      rw [← deriv_comp_add_const, show (fun y ↦ iteratedDeriv j (cyclicLift f) (y + 1)) =
        iteratedDeriv j (cyclicLift f) from funext ih]
  induction k with
  | zero => simp [cyclicFourierCoeff_eq_on]
  | succ k ih =>
    rw [iteratedDeriv_succ, fourierCoeffOn_deriv_one_periodic (hdiff k) (hper k), ih,
      pow_succ', cyclicFrequency]
    ring

private theorem norm_fourierCoeffOn_iteratedDeriv_cyclic (f : S) (m : ℤ) (k : ℕ) :
    ‖fourierCoeffOn zero_lt_one (iteratedDeriv k (cyclicLift f)) m‖ ≤
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have h x (_ : x ∈ uIoc (0 : ℝ) 1) :
      ‖fourier (-m) (x : T) • iteratedDeriv k (cyclicLift f) x‖ ≤
        elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact cyclicSeminorm_ge f k x
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const h

private theorem cyclicTerm_deriv (f : S) (m : ℤ) (k : ℕ) :
    iteratedDeriv k (cyclicLift (cyclicFourierCoeff m f • cyclicExponential m)) =
      fun x : ℝ ↦ (cyclicFrequency m ^ k * cyclicFourierCoeff m f) * fourier m (x : T) := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((hasDerivAt_fourier 1 m x).const_mul
      (cyclicFrequency m ^ k * cyclicFourierCoeff m f)).deriv]
    simp only [Complex.ofReal_one, div_one, pow_succ', cyclicFrequency]
    ring

private def cyclicWeight (m : ℤ) : ℝ :=
  if m = 0 then 1 else ‖cyclicFrequency m‖⁻¹ ^ 2

private theorem cyclicWeight_nonneg (m : ℤ) : 0 ≤ cyclicWeight m := by
  unfold cyclicWeight
  split_ifs <;> positivity

private theorem cyclicWeight_summable : Summable cyclicWeight := by
  let a : ℂ := 2 * Real.pi * Complex.I
  have h := Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))
  refine (h.mul_left (‖a‖⁻¹ ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
  rw [cyclicWeight, ite_eq_right hm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖a * (m : ℂ)‖⁻¹ ^ 2 ≤ ‖a‖⁻¹ ^ 2 * (1 / (m : ℝ) ^ 2)
  rw [norm_mul, mul_inv, mul_pow, Complex.norm_intCast]
  simp only [inv_pow, sq_abs, one_div, le_rfl]

/-- Two extra derivatives give an inverse-square bound for every nonzero Fourier mode. -/
private theorem cyclicTerm_seminorm_le (f : S) (i : ElementarySchwartzIndex 0 1 0) (m : ℤ) :
    elementarySchwartzSeminorm i (cyclicFourierCoeff m f • cyclicExponential m) ≤
      cyclicWeight m * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
        elementarySchwartzSeminorm (0, 0, fun _ ↦ i.2.2.1 0 + 2, 0) f) := by
  let k := i.2.2.1 0
  have hp₀ : 0 ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := apply_nonneg _ _
  have hp₂ : 0 ≤ elementarySchwartzSeminorm (0, 0, fun _ ↦ k + 2, 0) f := apply_nonneg _ _
  refine cyclicSeminorm_le _ i (mul_nonneg (cyclicWeight_nonneg m) (add_nonneg hp₀ hp₂))
    fun x _ ↦ ?_
  rw [cyclicTerm_deriv, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  change ‖cyclicFrequency m ^ k * cyclicFourierCoeff m f‖ ≤
    cyclicWeight m * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k + 2, 0) f)
  by_cases hm : m = 0
  · subst m
    have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f 0 0
    rw [iteratedDeriv_zero, ← cyclicFourierCoeff_eq_on] at h
    rw [cyclicWeight, ite_eq_left rfl, one_mul]
    by_cases hk : k = 0
    · rw [hk, pow_zero, one_mul]
      exact h.trans (le_add_of_nonneg_right (apply_nonneg _ _))
    · simpa [cyclicFrequency, zero_pow hk] using add_nonneg hp₀ hp₂
  · rw [cyclicWeight, ite_eq_right hm]
    have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f m (k + 2)
    rw [fourierCoeffOn_iteratedDeriv_cyclic, pow_add, mul_right_comm, norm_mul, norm_pow] at h
    have ha : 0 < ‖cyclicFrequency m‖ ^ 2 := by
      have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have ha' : cyclicFrequency m ≠ 0 := by simp [cyclicFrequency, Real.pi_ne_zero, hmc]
      exact pow_pos (norm_pos_iff.mpr ha') _
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ ha]
    exact h.trans (le_add_of_nonneg_left hp₀)

/-- Dominate any continuous seminorm by finitely many of the defining seminorms. -/
private theorem cyclicFourier_isAbsolute :
    SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by
  classical
  intro q hq
  let p (i : ElementarySchwartzIndex 0 1 0) : Seminorm ℂ S := elementarySchwartzSeminorm i
  have hp : WithSeminorms p := elementarySchwartz_withSeminorms
  obtain ⟨I, C, _, hdom⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let r (i : ElementarySchwartzIndex 0 1 0) : Seminorm ℂ S :=
    p (0, 0, 0, 0) + p (0, 0, fun _ ↦ i.2.2.1 0 + 2, 0)
  let D : NNReal := ⟨∑' m : ℤ, cyclicWeight m, tsum_nonneg cyclicWeight_nonneg⟩
  have hsum (v : S) (g : ElementarySchwartzIndex 0 1 0 → Seminorm ℂ S) :
      (∑ i ∈ I, g i) v = ∑ i ∈ I, g i v := by
    change FunLike.coeAddMonoidHom (Seminorm ℂ S) S ℝ (∑ i ∈ I, g i) v = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have hr (i) : Continuous (r i) :=
    (hp.continuous_seminorm _).add (hp.continuous_seminorm _)
  have hr' := Seminorm.continuous_finsetSum (s := I) (fun i _ ↦ hr i)
  refine ⟨(D * C) • ∑ i ∈ I, r i, hr'.const_smul (D * C), fun f ↦ ?_⟩
  let term (m : ℤ) := cyclicFourierCoeff m f • cyclicExponential m
  have hle (m : ℤ) : q (term m) ≤ cyclicWeight m * ((C : ℝ) * ∑ i ∈ I, r i f) := by
    calc
      _ ≤ (C : ℝ) * ∑ i ∈ I, p i (term m) := by
        simpa only [smul_apply, NNReal.smul_def, smul_eq_mul, hsum]
          using hdom (term m)
      _ ≤ (C : ℝ) * ∑ i ∈ I, cyclicWeight m * r i f :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ ↦ cyclicTerm_seminorm_le f i m)) C.coe_nonneg
      _ = _ := by rw [← Finset.mul_sum, mul_left_comm]
  have hmajor := cyclicWeight_summable.mul_right ((C : ℝ) * ∑ i ∈ I, r i f)
  have hqsum := hmajor.of_nonneg_of_le (fun m ↦ apply_nonneg q (term m)) hle
  have hbound := hqsum.tsum_le_tsum hle hmajor
  rw [tsum_mul_right] at hbound
  change Summable ((q ∘ term) ∘ freq) ∧
    (∑' n, (q ∘ term) (freq n)) ≤ ((D * C) • ∑ i ∈ I, r i) f
  refine ⟨(freq).summable_iff.mpr hqsum, ?_⟩
  rw [(freq).tsum_eq (q ∘ term), smul_apply, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_mul, hsum, mul_assoc]
  exact hbound

/-- Paper: Lemma 4.2.1.2(1), p. 162. The circle exponentials form an absolute
Schauder basis with the Fourier coefficient functionals.
Deviation: The Schauder basis predicates of §4.1 use the natural-number
enumeration of the integer frequencies. -/
theorem cyclicExponential_absoluteBasis :
    IsSchauderBasis (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) ∧
      SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by
  refine ⟨⟨fun m n ↦ ?_, fun f ↦ ?_⟩, cyclicFourier_isAbsolute⟩
  · change cyclicFourierCoeff (freq m) (cyclicExponential (freq n)) = _
    simp [cyclicFourierCoeff_exponential]
  · exact ((freq).hasSum_iff.mpr (cyclicFourier_hasSum f)).mono_left
      (SummationFilter.conditional ℕ).le_atTop

/-- Paper: Lemma 4.2.1.2(2), p. 162. Fourier coefficients are an unconditional
Schauder basis of the strong dual, with coordinates given by evaluation on the monomials.
Deviation: Frequencies are enumerated by the natural numbers. -/
theorem cyclicFourierCoeff_unconditionalBasis :
    let ev := fun n : ℕ ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))
    IsSchauderBasis (cyclicFourierCoeff ∘ freq) ev ∧
      SchauderBasis.IsUnconditional (cyclicFourierCoeff ∘ freq) ev := by
  have hFrechet : IsFrechetTVS S := elementarySchwartz_isFrechet
  let : BarrelledSpace ℂ S := isFrechetTVS_barrelled hFrechet
  let : T2Space S := elementarySchwartz_t2
  obtain ⟨_, _, _, hComplete⟩ := hFrechet
  obtain ⟨e, he⟩ := elementarySchwartz_reflexive (m := 0) (n := 1) (r := 0) (F := PUnit)
  let eval : S →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ S) :=
    ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ)
  have hReflexive : IsHomeomorph eval := by
    have heq : (eval : S → StrongDual ℂ (StrongDual ℂ S)) = e := by
      funext f
      exact DFunLike.ext _ _ fun L ↦ (he f L).symm
    rw [heq]
    exact e.isHomeomorph
  obtain ⟨hb, ha⟩ := cyclicExponential_absoluteBasis
  exact ⟨SchauderBasis.isShrinking_of_isAbsolute hComplete hReflexive hb ha,
    SchauderBasis.strongDual_isUnconditional_of_isAbsolute hComplete hReflexive hb ha⟩

/-- Paper: Lemma 4.2.1.2(3), p. 162. The quotient Fourier coefficient is the
normalized integral of the lift over the multiplicative fundamental interval. -/
theorem cyclicFourierCoeff_interval (γ : ℝ) (hγ : 1 < γ) (f : S) (m : ℤ) :
    cyclicFourierCoeff m f =
      (Real.log γ : ℂ)⁻¹ * ∫ t in (1 : ℝ)..γ,
        f (point ((Real.log t / Real.log γ : ℝ) : T)) *
          Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) / (t : ℂ) := by
  let F (x : ℝ) : ℂ := fourier (-m) (x : T) * cyclicLift f x
  have hF : Continuous F :=
    ((fourier (-m)).continuous.comp (AddCircle.continuous_mk' 1)).mul
      (cyclicLift_contDiff f).continuous
  have hlog : Real.log γ ≠ 0 := (Real.log_pos hγ).ne'
  have ht : ∀ t ∈ uIcc (1 : ℝ) γ, t ≠ 0 := by
    rw [uIcc_of_le hγ.le]
    exact fun t ht ↦ (zero_lt_one.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) γ,
      HasDerivAt (fun x ↦ Real.log x / Real.log γ) (t⁻¹ / Real.log γ) t :=
    fun t h ↦ (Real.hasDerivAt_log (ht t h)).div_const _
  have hsub : (∫ t in (1 : ℝ)..γ, (t⁻¹ / Real.log γ) • F (Real.log t / Real.log γ)) =
      ∫ x in (0 : ℝ)..1, F x := by
    simpa only [Function.comp_apply, Real.log_one, zero_div, div_self hlog] using
      intervalIntegral.integral_deriv_smul_comp hderiv
        ((continuousOn_id.inv₀ ht).div_const (Real.log γ)) hF
  have hphase (t : ℝ) :
      fourier (-m) ((Real.log t / Real.log γ : ℝ) : T) =
        Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) := by
    change cyclicExponential (-m) (point ((Real.log t / Real.log γ : ℝ) : T)) = _
    rw [cyclicExponential_apply γ hγ]
    simp only [Int.cast_neg, mul_neg, neg_div]
  change fourierCoeff (fun z : T ↦ f (point z)) m = _
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [div_one, one_smul, zero_add, smul_eq_mul]
  change (∫ x in (0 : ℝ)..1, F x) = _
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [F, cyclicLift, hphase, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
  ring

-- TODO(paper-gap): The estimate (4.2.1.7) uses m^k for negative frequencies.
-- For f = e₋₁ and k = 1 the printed right-hand side is negative.

end Fourier

section QuotientDual

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X] [PolynormableSpace ℂ X]

/-- Paper: Lemma 4.2.1.3, p. 163. Pullback along the quotient embeds the weak dual
and has image the continuous functionals vanishing on the closed subspace. -/
theorem quotientDual_weakEmbedding (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    let pull := fun l : WeakDual ℂ (X ⧸ M) ↦ StrongDual.toWeakDual (l.toStrongDual.comp M.mkQL)
    IsEmbedding pull ∧ range pull = {l | ∀ x ∈ M, l x = 0} := by
  dsimp only
  constructor
  · have he : IsEmbedding (fun l : WeakDual ℂ (X ⧸ M) ↦ (l : (X ⧸ M) → ℂ)) :=
      WeakBilin.isEmbedding (B := topDualPairing ℂ (X ⧸ M)) ContinuousLinearMap.coe_injective
    have hπ := M.mkQ_surjective.isEmbedding_comp (X := ℂ) M.mkQ
    apply Topology.IsEmbedding.of_comp (g := fun l : WeakDual ℂ X ↦ (l : X → ℂ))
      (WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M.mkQ x))
      WeakDual.coeFn_continuous
    exact hπ.comp he
  · ext l
    constructor
    · rintro ⟨v, rfl⟩ x hx
      change v (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
    · intro h
      refine ⟨StrongDual.toWeakDual (M.liftQL l.toStrongDual (fun x hx ↦ h x hx)), ?_⟩
      exact DFunLike.ext _ _ fun _ ↦ rfl

/-- Paper: Lemma 4.2.1.3, p. 163. The image of the quotient adjoint in the
strong dual consists precisely of the functionals vanishing on the subspace. -/
theorem quotientDual_strongRange (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) =
      {l : StrongDual ℂ X | ∀ x ∈ M, l x = 0} := by
  exact (quotientDual_weakEmbedding M hM).2

/-- Paper: Lemma 4.2.1.3(1), p. 163. For a nuclear Fréchet space the quotient adjoint
is a topological embedding for the strong dual topologies. The separate theorem
`quotientDual_strongRange` identifies its image with the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_nuclear (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : IsNuclearTVS X) (hF : IsFrechetTVS X) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  -- Lift the compact closure of each bounded set in the nuclear Fréchet quotient.
  have hlift : LiftsBoundedSets M.mkQL := by
    let : T0Space X := inferInstance
    let : IsClosed (M : Set X) := hM
    let : PolynormableSpace ℂ (X ⧸ M) := polynormableSpace_quotient M
    have hNQ := isNuclearTVS_quotient hN M
    obtain ⟨_, _, _, hcompleteQ⟩ := isFrechetTVS_quotient hF M hM
    obtain ⟨_, _, hmetr, hcomplete⟩ := hF
    let : MetrizableSpace X := hmetr
    let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
    let : CompleteSpace X := hcomplete
    let : (uniformity X).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
    let := UniformSpace.metricSpace X
    let : UniformSpace (X ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (X ⧸ M)
    let : IsUniformAddGroup (X ⧸ M) := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (X ⧸ M) := hcompleteQ
    intro B hB
    have htotal := (isPrecompactInCompletion_iff_totallyBounded B).mp
      (isPrecompactInCompletion_of_isNuclearTVS (X ⧸ M) hNQ hB)
    obtain ⟨A, hA, himage⟩ := exists_isCompact_image_eq_of_isOpenQuotientMap
      M.isOpenQuotientMap_mkQL (htotal.closure.isCompact_of_isClosed isClosed_closure)
    exact ⟨A, hA.isVonNBounded ℂ, himage.symm ▸ subset_closure⟩
  let pull : StrongDual ℂ (X ⧸ M) →L[ℂ] StrongDual ℂ X :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL
  have hind : IsUniformInducing pull := by
    constructor
    refine le_antisymm ?_ pull.uniformContinuous.le_comap
    have hX := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X) (F := ℂ)).uniformity_of_nhds_zero
    have hQ := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X ⧸ M) (F := ℂ)).uniformity_of_nhds_zero
    refine ((hX.comap (Prod.map pull pull)).le_basis_iff hQ).mpr ?_
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨A, hA, hcover⟩ := hlift B hB
    refine ⟨(A, U), ⟨hA, hU⟩, ?_⟩
    intro p hp
    change ∀ x ∈ A, (pull p.2 - pull p.1) x ∈ U at hp
    change ∀ y ∈ B, (p.2 - p.1) y ∈ U
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcover hy
    exact hp x hx
  refine ⟨hind.isInducing, ?_⟩
  intro f g hfg
  ext y
  obtain ⟨x, rfl⟩ := M.mkQ_surjective y
  exact congrArg (fun l : StrongDual ℂ X ↦ l x) hfg

/-- Paper: Lemma 4.2.1.3(2), p. 164. For a Hilbert space the quotient adjoint
is a topological embedding for the strong dual topologies. The separate theorem
`quotientDual_strongRange` identifies its image with the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  have : CompleteSpace M := hM.completeSpace_coe
  let s : (H ⧸ M) →L[ℂ] H :=
    Mᗮ.subtypeL.comp M.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  let r := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ s
  apply Topology.IsEmbedding.of_leftInverse (f := r) _ r.continuous
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL).continuous
  intro φ
  ext x
  change φ (M.mkQ ((M.quotientEquivOrthogonal x : Mᗮ) : H)) = φ x
  congr 1
  exact (M.quotientEquivOrthogonal_symm_eq_mk _ (M.quotientEquivOrthogonal x).property).symm.trans
    (M.quotientEquivOrthogonal.symm_apply_apply x)

/-- Paper: Remark 4.2.1.4, p. 164. In a totally reflexive Fréchet space, a
strong embedding of the quotient adjoint implies bounded lifting for the quotient. -/
theorem liftsBoundedSets_of_quotientDual_strongEmbedding (hF : IsFrechetTVS X)
    (hR : ∀ (N : Submodule ℂ X), IsClosed (N : Set X) →
      ∃ e : (X ⧸ N) ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (X ⧸ N)),
        ∀ x l, e x l = l x)
    (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (h : IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) :
    LiftsBoundedSets M.mkQL := by
  clear hF
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  let : IsClosed (M : Set X) := hM
  let : UniformSpace (X ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (X ⧸ M)
  let : IsUniformAddGroup (X ⧸ M) := isUniformAddGroup_of_addCommGroup
  let : PolynormableSpace ℂ (StrongDual ℂ X) :=
    uniformConvergenceCLM_polynormable (F := ℂ) {B : Set X | IsVonNBounded ℂ B}
      (fun _ h ↦ h) (by rw [sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  -- Total reflexivity at the zero subspace represents every bidual functional on X.
  have represent (ψ : StrongDual ℂ (StrongDual ℂ X)) : ∃ x : X, ∀ l : StrongDual ℂ X, l x = ψ l := by
    let N : Submodule ℂ X := ⊥
    let j : (X ⧸ N) ≃L[ℂ] X :=
      { N.quotEquivOfEqBot rfl with
        continuous_toFun := N.isQuotientMap_mkQL.continuous_iff.mpr continuous_id
        continuous_invFun := N.mkQL.continuous }
    let d := j.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)
    obtain ⟨i, hi⟩ := hR N (by simp [N])
    obtain ⟨z, hz⟩ := i.surjective (ψ.comp d.toContinuousLinearMap)
    refine ⟨j z, fun l ↦ ?_⟩
    have hz' := congrArg (fun φ : StrongDual ℂ (StrongDual ℂ (X ⧸ N)) ↦ φ (d.symm l)) hz
    change i z (d.symm l) = ψ (d (d.symm l)) at hz'
    rw [hi, d.apply_symm_apply] at hz'
    exact hz'
  let pull := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL
  let e := LinearEquiv.ofInjective pull.toLinearMap h.injective
  intro B hB
  let tests := {s : Set (X ⧸ M) | IsVonNBounded ℂ s}
  let p := mappingSeminorm (F := ℂ) ⟨B, hB⟩ ⟨normSeminorm ℂ ℂ, continuous_norm⟩
  have hp : Continuous p :=
    (uniformConvergenceCLM_withSeminorms tests (fun _ hs ↦ hs)
      (by rw [show ⋃₀ tests = univ from sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
      _ (norm_withSeminorms ℂ ℂ)).continuous_seminorm (⟨B, hB⟩, ())
  obtain ⟨q, hq, hdom⟩ := Seminorm.exists_le_comp_of_isInducing hp (f := pull.toLinearMap) h.isInducing
  -- A single polar bounds all Hahn–Banach extensions simultaneously.
  let A := {x : X | ∀ l : StrongDual ℂ X, ‖l x‖ ≤ q l}
  refine ⟨A, (isVonNBounded_iff_dual_image A).2 (fun l ↦ ?_), fun y hy ↦ ?_⟩
  · refine isBounded_iff_forall_norm_le.mpr ⟨q l, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hx l
  · let ev := (ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) y).toLinearMap.comp e.symm.toLinearMap
    have hev (l : pull.range) : ‖ev l‖ ≤ q l := by
      obtain ⟨g, rfl⟩ := e.surjective l
      change ‖(e.symm (e g)) y‖ ≤ q (pull g)
      rw [e.symm_apply_apply]
      refine le_trans ?_ (hdom g)
      change ‖g y‖ ≤ p g
      dsimp only [p]
      rw [mappingSeminorm_apply]
      obtain ⟨r, hr⟩ := isBounded_iff_forall_norm_le.mp ((NormedSpace.isVonNBounded_iff ℂ).mp (hB.image g))
      exact le_ciSup (f := fun x : B ↦ ‖g x‖)
        ⟨r, forall_mem_range.mpr fun x ↦ hr _ (mem_image_of_mem _ x.property)⟩ ⟨y, hy⟩
    obtain ⟨ψ, hψ, hψq⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm pull.range ev hq hev
    obtain ⟨x, hx⟩ := represent ψ
    refine ⟨x, fun l ↦ (hx l) ▸ hψq l, ?_⟩
    obtain ⟨i, hi⟩ := hR M hM
    apply i.injective
    ext l
    rw [hi, hi]
    change pull l x = l y
    refine (hx _).trans ((hψ (e l)).trans ?_)
    change (e.symm (e l)) y = l y
    rw [e.symm_apply_apply]

-- TODO(paper-gap): The classification in Remark 4.2.1.4 needs a hypothesis
-- about bounded lifting for all closed-subspace quotients of X.

end QuotientDual

section Kernel

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Lemma 4.2.1.5(2), p. 165. The periodization of exponential profiles
is continuous. Smoothness in part (1) is built into its elementary Schwartz target. -/
theorem cyclicPeriodization_continuous : Continuous (cyclicPeriodization γ hγ) := by
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  have h : Continuous (fun f : E ↦ logExponentialDecayTwist univ a f) :=
    continuous_pi_iff.mp (positiveRealExponentialDecay_isEmbedding (univ : Set ℝ) univ_nonempty).continuous a
  exact (cyclicSchwartzPeriodization γ hγ).continuous.comp h

/-- An integer sequence that is zero up to `A` and one from `A + n` on has consecutive
differences summing to one: the finite telescoping sum is all that is left. -/
private theorem hasSum_int_sub_of_zero_of_one {a : ℤ → ℝ} (A : ℤ) (n : ℕ)
    (h0 : ∀ k ≤ A, a k = 0) (h1 : ∀ k, A + n ≤ k → a k = 1) :
    HasSum (fun k ↦ a (k + 1) - a k) 1 := by
  have hs : ∀ k ∉ (Finset.range n).image (fun i : ℕ ↦ A + i), a (k + 1) - a k = 0 := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and] at hk
    by_cases hkA : k < A
    · rw [h0 k hkA.le, h0 (k + 1) (by omega), sub_zero]
    · have hk' : A + n ≤ k := by
        by_contra hlt
        exact hk (k - A).toNat (by omega) (by omega)
      rw [h1 k hk', h1 (k + 1) (by omega), sub_self]
  convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) hs using 1
  have ht := Finset.sum_range_sub (fun i : ℕ ↦ a (A + i)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero, ← add_assoc] at ht
  rw [Finset.sum_image (fun i _ j _ h ↦ by simpa using h), ht, h1 _ le_rfl, h0 _ le_rfl,
    sub_zero]

/-- The differences of the smooth step `smoothTransition` along integer translates form a
partition of unity: for every `u`, the sum over `k : ℤ` of
`smoothTransition (u + k + 1) - smoothTransition (u + k)` is one. -/
private theorem hasSum_smoothTransition_sub (u : ℝ) :
    HasSum (fun k : ℤ ↦ Real.smoothTransition (u + k + 1) - Real.smoothTransition (u + k)) 1 := by
  have h := hasSum_int_sub_of_zero_of_one (a := fun k : ℤ ↦ Real.smoothTransition (u + k))
    ⌊-u⌋ (⌈1 - u⌉ - ⌊-u⌋).toNat (fun k hk ↦ ?_) (fun k hk ↦ ?_)
  · simpa only [Int.cast_add, Int.cast_one, ← add_assoc] using h
  · apply Real.smoothTransition.zero_of_nonpos
    have hk' : (k : ℝ) ≤ ⌊-u⌋ := by exact_mod_cast hk
    linarith [Int.floor_le (-u)]
  · apply Real.smoothTransition.one_of_one_le
    have hk' : (⌈1 - u⌉ : ℝ) ≤ k := by exact_mod_cast (show ⌈1 - u⌉ ≤ k by omega)
    linarith [Int.le_ceil (1 - u)]

/-- Paper: Lemma 4.2.1.5(2), p. 165. Every smooth quotient function has an
exponentially decaying lift under periodization. -/
theorem cyclicPeriodization_surjective : Surjective (cyclicPeriodization γ hγ) := by
  -- Cut the periodic lift of `g` off with a smooth bump whose translates by `log γ` sum
  -- to one; the result has compact support, and its periodization is `g` again.
  intro g
  set L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  let F (u : ℝ) : ℂ := ((Real.smoothTransition (u + 1) - Real.smoothTransition u : ℝ) : ℂ)
  let φ (x : ℝ) : ℂ := F (x / L) * cyclicLift g (x / L)
  have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have hst : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hdiv : ContDiff ℝ ∞ (fun x : ℝ ↦ x / L) := contDiff_id.div_const L
  have hF : ContDiff ℝ ∞ F :=
    hcoe.comp ((hst.comp (contDiff_id.add contDiff_const)).sub hst)
  have hφd : ContDiff ℝ ∞ φ := (hF.comp hdiv).mul ((cyclicLift_contDiff g).comp hdiv)
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun x hx ↦ ?_
    have hF0 : F (x / L) = 0 := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      simp only [F, Complex.ofReal_eq_zero, sub_eq_zero]
      rcases hx with hx | hx
      · have hu : x / L < -1 := by rw [div_lt_iff₀ hL]; linarith
        rw [Real.smoothTransition.zero_of_nonpos (by linarith),
          Real.smoothTransition.zero_of_nonpos (by linarith)]
      · have hu : 1 < x / L := by rw [lt_div_iff₀ hL]; linarith
        rw [Real.smoothTransition.one_of_one_le (by linarith),
          Real.smoothTransition.one_of_one_le (by linarith)]
    simp only [φ, hF0, zero_mul]
  have hmem := mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hφs hφd
  refine ⟨⟨φ, hmem⟩, ?_⟩
  apply Subtype.ext
  funext y
  -- Every point of the circle group is the image of a real logarithmic coordinate.
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (y.2.1 0)
  have hy : y = point (u : T) := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Subsingleton.elim _ _))
    funext j
    have : j = 0 := Subsingleton.elim _ _
    subst j
    exact hu.symm
  subst hy
  have h1 := cyclicPeriodization_hasSum γ hγ ⟨φ, hmem⟩ (u * L)
  rw [mul_div_cancel_right₀ u hL.ne'] at h1
  have h2 : HasSum (fun k : ℤ ↦ φ (u * L + (k : ℝ) * L)) (g (point (u : T))) := by
    have hsum := (Complex.hasSum_ofReal.mpr (hasSum_smoothTransition_sub u)).mul_right
      (cyclicLift g u)
    rw [Complex.ofReal_one, one_mul] at hsum
    refine hsum.congr_fun fun k ↦ ?_
    have hk : (u * L + (k : ℝ) * L) / L = u + k := by field_simp
    have hper : cyclicLift g (u + k) = cyclicLift g u := by
      simpa only [mul_one] using (cyclicLift_periodic g).int_mul k u
    simp only [φ, F, hk, hper, add_assoc]
  exact h1.unique h2

/-- Paper: Lemma 4.2.1.5(2), p. 165. Periodization sends open sets to open sets. -/
theorem cyclicPeriodization_isOpenMap : IsOpenMap (cyclicPeriodization γ hγ) := by
  -- Open mapping theorem: a continuous linear surjection from a Fréchet space onto a Fréchet
  -- space is open, because the range, being everything, is not meagre in the Baire target.
  obtain ⟨hTE, -, hME, hCE⟩ :=
    positiveRealExponentialDecay_frechet univ ordConnected_univ univ_nonempty
  obtain ⟨hTS, -, hMS, hCS⟩ := elementarySchwartz_isFrechet (m := 0) (n := 1) (r := 0) (F := PUnit)
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace S := IsTopologicalAddGroup.rightUniformSpace S
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup S := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hCE
  have : CompleteSpace S := hCS
  have : MetrizableSpace E := hME
  have : MetrizableSpace S := hMS
  have : T2Space S := elementarySchwartz_t2
  have : (uniformity S).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero S]
    infer_instance
  have : BaireSpace S := BaireSpace.of_completelyPseudoMetrizable
  let A : E →L[ℂ] S := ⟨cyclicPeriodization γ hγ, cyclicPeriodization_continuous γ hγ⟩
  refine isOpenMap_of_not_isMeagre_range A ?_
  change ¬ IsMeagre (range (cyclicPeriodization γ hγ))
  rw [(cyclicPeriodization_surjective γ hγ).range_eq]
  exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty

/-- Paper: Lemma 4.2.1.5(2), p. 165. Bundle the periodization and its continuity
as a continuous linear map. -/
def cyclicPeriodizationCLM : E →L[ℂ] S :=
  ⟨cyclicPeriodization γ hγ, cyclicPeriodization_continuous γ hγ⟩

/-- Paper: (4.2.1.2), p. 162. Evaluating the bundled periodization at a quotient
point gives the sum of the translates over all integer multiples of the logarithmic period. -/
theorem cyclicPeriodizationCLM_apply (f : E) (x : ℝ) :
    cyclicPeriodizationCLM γ hγ f (point ((x / Real.log γ : ℝ) : T)) =
      ∑' k : ℤ, f.val (x + (k : ℝ) * Real.log γ) :=
  (cyclicPeriodization_hasSum γ hγ f x).tsum_eq.symm

local notation "Φ" => cyclicPeriodizationCLM γ hγ
local notation "Mγ" => LinearMap.ker (ContinuousLinearMap.toLinearMap Φ)
local notation "Q" => E ⧸ Mγ
local notation "desc" => Submodule.liftQL Mγ Φ le_rfl

private theorem orbitDifference_hasSum {f : ℝ → ℂ} {x L : ℝ} {z : ℂ}
    (h : HasSum (fun n : ℤ ↦ f (x + n * L)) z) :
    HasSum (fun n : ℤ ↦ f (x + n * L) - f (x + n * L + L)) 0 := by
  have ht := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr h
  simpa [Function.comp_def, add_mul, add_assoc] using h.sub ht

private theorem cyclic_eq_zero_of_lifts {L : ℝ} (hL : L ≠ 0) (u : S)
    (h : ∀ x : ℝ, u (point ((x/L : ℝ) : T)) = 0) : u = 0 := by
  apply Subtype.ext
  funext g
  let r := (AddCircle.equivIco 1 0) (g.2.1 0)
  have he : (point (((r : ℝ) * L / L : ℝ) : T)) = g := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (funext fun j ↦ ?_) (Subsingleton.elim _ _))
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r : ℝ) * L / L) : T) = _
    rw [mul_div_cancel_right₀ _ hL]
    exact AddCircle.coe_equivIco
  exact he ▸ h ((r : ℝ) * L)

/-- Paper: Lemma 4.2.1.5(3), p. 165. The kernel is the closed linear span of
the differences between a function and its translate by γ.
Deviation: The difference is expressed in logarithmic coordinates. -/
theorem cyclicPeriodization_ker :
    Mγ = (Submodule.span ℂ {g : E | ∃ f : E,
      ∀ x : ℝ, g.val x = f.val x - f.val (x + Real.log γ)}).topologicalClosure := by
  let L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  let P := cyclicPeriodizationCLM γ hγ
  apply le_antisymm
  · intro f hf
    change P f = 0 at hf
    let a₀ : (univ : Set ℝ) := ⟨0, mem_univ _⟩
    let F₀ := logExponentialDecayTwist univ a₀ f
    have hF (x : ℝ) : F₀ x = f.val x := by
      exact (logExponentialDecayTwist_apply univ a₀ f x).trans (by simp [a₀])
    have horb (x : ℝ) : HasSum (fun n : ℤ ↦ f.val (x + n * L)) 0 := by
      have hs := cyclicPeriodization_hasSum γ hγ f x
      change HasSum _ (P f _) at hs
      rwa [hf] at hs
    obtain ⟨g, hg, hdiff⟩ := schwartzOrbitPrimitive L hL F₀ (by simpa only [hF] using horb)
    simp only [hF] at hg hdiff
    have hback (x : ℝ) : g x = -(∑' n : ℕ, f.val (x - (n + 1) * L)) := by
      let v (m : ℤ) := f.val (x + m * L)
      have hp : Summable (fun n : ℕ ↦ v n) := (horb x).summable.comp_injective Nat.cast_injective
      have hm : Summable (fun n : ℕ ↦ v (-(n + 1))) :=
        (horb x).summable.comp_injective (fun i j h ↦ by omega)
      have h := (hp.hasSum.of_nat_of_neg_add_one hm.hasSum).unique (horb x)
      rw [hg]
      apply eq_neg_of_add_eq_zero_left
      simpa only [v, Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one,
        neg_mul, ← sub_eq_add_neg] using h
    have hmem : (g : ℝ → ℂ) ∈ logExponentialDecaySubmodule univ := by
      apply (Submodule.mem_iInf _).2
      intro a
      let c := a.val
      let F := logExponentialDecayTwist univ a f
      have hFa (x : ℝ) : F x = (Real.exp (c * x) : ℂ) * f.val x :=
        logExponentialDecayTwist_apply _ _ _ _
      rcases lt_trichotomy 0 c with hc | hc | hc
      · let r := Real.exp (-c * L)
        obtain ⟨v, hv⟩ := schwartzGeometricTranslates F L r (Real.exp_pos _)
          (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc) hL))
        refine ⟨v, funext fun x ↦ ?_⟩
        change v x = (Real.exp (c * x) : ℂ) * g x
        rw [hv, hg, ← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hFa, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
        congr 2
        dsimp only [r]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      · refine ⟨g, funext fun x ↦ ?_⟩
        change g x = (Real.exp (c * x) : ℂ) * g x
        simp [← hc]
      · let r := Real.exp (c * L)
        obtain ⟨v, hv⟩ := schwartzGeometricTranslates F (-L) r (Real.exp_pos _)
          (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos hc hL))
        refine ⟨-(r • (v.compSubConstCLM ℂ L)), funext fun x ↦ ?_⟩
        change -(r • v (x - L)) = (Real.exp (c * x) : ℂ) * g x
        rw [hv, hback, mul_neg, Complex.real_smul, ← tsum_mul_left, ← tsum_mul_left]
        simp only [Complex.real_smul]
        congr 1
        apply tsum_congr
        intro n
        rw [hFa, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        have hx : x - L + n * (-L) = x - (n + 1) * L := by ring
        rw [hx]
        congr 2
        dsimp only [r]
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨⟨g, hmem⟩, hdiff⟩
  · have : T2Space S := elementarySchwartz_t2
    apply Submodule.topologicalClosure_minimal _ _ P.isClosed_ker
    apply Submodule.span_le.mpr
    rintro g ⟨f, hf⟩
    apply cyclic_eq_zero_of_lifts hL.ne'
    intro x
    apply (cyclicPeriodization_hasSum γ hγ g x).unique
    simpa only [hf] using orbitDifference_hasSum (cyclicPeriodization_hasSum γ hγ f x)

/-- Paper: Lemma 4.2.1.5(3), p. 165. The quotient functional is obtained from
the Fourier coefficient by undoing probability Haar normalization.
Its pullback is the Mellin evaluation at the negative Fourier frequency. -/
def cyclicQuotientMellinCoeff (m : ℤ) : StrongDual ℂ Q :=
  (Real.log γ : ℂ) • (cyclicFourierCoeff m).comp desc

/-- Paper: Lemma 4.2.1.5(3), p. 165. On representatives the quotient functional
is the Mellin integral with exponent −2πim/log γ. -/
theorem cyclicQuotientMellinCoeff_mk (m : ℤ) (f : E) :
    cyclicQuotientMellinCoeff γ hγ m (Submodule.mkQL Mγ f) =
      mellin (fun t ↦ f.val (Real.log t)) (-phase[γ, m]) := by
  let L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  -- Rescale the logarithmic profile so its periodization has period one.
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩ f)
  let u : C(ℝ, ℂ) := ⟨g, g.continuous⟩
  have hu (x : ℝ) : u x = f.val (x * L) := by
    change logExponentialDecayTwist univ ⟨0, mem_univ _⟩
      (show logExponentialDecaySubmodule univ from f) (x * L) = _
    rw [logExponentialDecayTwist_apply]
    simp
  have hs (K : Compacts ℝ) :
      Summable fun n : ℤ ↦ ‖(u.comp (ContinuousMap.addRight n)).restrict K‖ := by
    have h := isBigO_norm_restrict_cocompact u (by norm_num) (g.isBigO_cocompact_rpow (-2)) K
    exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (h.comp_tendsto Int.tendsto_coe_cofinite)
  have hperiod : (fun z : T ↦ Φ f (point z)) = (u.periodic_tsum_comp_add_zsmul 1).lift := by
    funext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [Function.Periodic.lift_coe]
    simp only [zsmul_one]
    rw [← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hs)]
    have hsum := (cyclicPeriodization_hasSum γ hγ f (x * L)).tsum_eq.symm
    rw [show x * L / Real.log γ = x from mul_div_cancel_right₀ x hL.ne'] at hsum
    refine hsum.trans (tsum_congr fun n ↦ ?_)
    change f.val (x * L + (n : ℝ) * L) = u (x + n)
    rw [hu, add_mul]
  -- Logarithmic substitution in the Mellin integral and dilation in the Fourier integral
  -- give the same integral, with the Jacobian of the dilation as the only factor.
  let phase := -(2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (L : ℂ))
  let w (x : ℝ) := Complex.exp (phase * (x : ℂ)) * f.val x
  have hmellin : mellin (fun t ↦ f.val (Real.log t)) phase = ∫ x, w x := by
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with x
    change Real.exp x • (((Real.exp x : ℝ) : ℂ) ^ (phase - 1) • f.val (Real.log (Real.exp x))) = _
    rw [Real.log_exp, Complex.real_smul, smul_eq_mul,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
      ← mul_assoc, ← Complex.exp_add, show (x : ℂ) + x * (phase - 1) = phase * x by ring]
  have hFourier : FourierTransform.fourier (u : ℝ → ℂ) (m : ℝ) = |L⁻¹| • ∫ x, w x := by
    rw [← Measure.integral_comp_mul_left w, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hu, w, smul_eq_mul, mul_comm L x, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_intCast]
    congr 2
    dsimp [phase]
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  change (L : ℂ) * fourierCoeff (fun z : T ↦ Φ f (point z)) m = _
  rw [hperiod, Real.fourierCoeff_tsum_comp_add hs, hFourier, hmellin, abs_of_pos (inv_pos.mpr hL),
    Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]

-- TODO(paper-gap): In the continuity proof, (4.2.1.14) cannot hold for fixed T
-- and arbitrary ε. At t = T γⁿ the term k = -n alone equals T⁻ᴺ.
-- The difference quotient in (4.2.1.17) has the opposite derivative sign.

private def periodizationQuotientEquiv : Q ≃L[ℂ] S := by
  let P := cyclicPeriodizationCLM γ hγ
  have hs : Surjective P := cyclicPeriodization_surjective γ hγ
  have hq : IsOpenQuotientMap P := ⟨hs, P.continuous, cyclicPeriodization_isOpenMap γ hγ⟩
  let e := P.toLinearMap.quotKerEquivOfSurjective hs
  refine { e with
    continuous_toFun := P.ker.isQuotientMap_mkQL.continuous_iff.mpr P.continuous
    continuous_invFun := hq.isQuotientMap.continuous_iff.mpr (by
      change Continuous (fun x ↦ e.symm (P x))
      exact P.ker.mkQL.continuous.congr fun x ↦ (P.toLinearMap.quotKerEquivOfSurjective_symm_apply hs x).symm) }

section BasisTransport

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (e : X ≃L[ℂ] Y) {x : ℕ → X} {c : ℕ → StrongDual ℂ X}

private theorem transportSchauderBasis (hb : IsSchauderBasis x c) :
    IsSchauderBasis (e ∘ x) (fun n ↦ (c n).comp e.symm.toContinuousLinearMap) := by
  refine ⟨fun m n ↦ ?_, fun y ↦ ?_⟩
  · change c m (e.symm (e (x n))) = _
    rw [e.symm_apply_apply]
    exact hb.1 m n
  · simpa only [Function.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, map_smul, e.apply_symm_apply] using
      (hb.2 (e.symm y)).mapL e.toContinuousLinearMap

private theorem transportUnconditionalBasis (hu : SchauderBasis.IsUnconditional x c) :
    SchauderBasis.IsUnconditional (e ∘ x) (fun n ↦ (c n).comp e.symm.toContinuousLinearMap) := by
  intro y
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    map_smul, e.apply_symm_apply] using (hu (e.symm y)).mapL e.toContinuousLinearMap

end BasisTransport

/-- Pullback along the quotient isomorphism, scaled to undo Haar normalization. -/
private def mellinDualEquiv {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (e : X ≃L[ℂ] S) (γ : ℝ) (hγ : 1 < γ) : StrongDual ℂ S ≃L[ℂ] StrongDual ℂ X :=
  e.symm.arrowCongr (ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (Real.log γ : ℂ) (Complex.ofReal_ne_zero.mpr (Real.log_pos hγ).ne')))

private theorem mellinDualEquiv_apply {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (e : X ≃L[ℂ] S) (γ : ℝ) (hγ : 1 < γ) (f : StrongDual ℂ S) :
    mellinDualEquiv e γ hγ f = (Real.log γ : ℂ) • f.comp e.toContinuousLinearMap := by
  ext z
  exact mul_comm _ _

/-- Paper: Lemma 4.2.1.5(3), p. 165. The Mellin evaluations form an unconditional
Schauder basis on the strong quotient dual. Lemma 4.2.1.3 identifies this dual
with the annihilator with its inherited strong topology. -/
theorem cyclicQuotientMellinCoeff_unconditionalBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ Q),
      IsSchauderBasis δ c ∧ SchauderBasis.IsUnconditional δ c := by
  let e := periodizationQuotientEquiv γ hγ
  let d := mellinDualEquiv e γ hγ
  have he : d ∘ (cyclicFourierCoeff ∘ freq) = cyclicQuotientMellinCoeff γ hγ ∘ freq := by
    funext n
    exact mellinDualEquiv_apply e γ hγ _
  obtain ⟨hb, hu⟩ := cyclicFourierCoeff_unconditionalBasis
  exact ⟨_, he ▸ transportSchauderBasis d hb, he ▸ transportUnconditionalBasis d hu⟩

/-- Paper: Remark 4.2.1.6, p. 165. Every bounded subset of a Hausdorff
quotient of the exponential decay space has a bounded lift. -/
theorem positiveRealExponentialDecay_liftsBoundedSets (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) : LiftsBoundedSets M.mkQL := by
  have hE := positiveRealExponentialDecay_frechet (univ : Set ℝ) ordConnected_univ univ_nonempty
  have hN := positiveRealExponentialDecay_nuclear.{0} (univ : Set ℝ) ordConnected_univ univ_nonempty
  exact liftsBoundedSets_mkQL_of_schwartz_frechet hE (isSchwartzTVS_of_isNuclearTVS hN) M hM

end Kernel

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient basis of the
strong dual is absolute, with coordinates given by evaluation on the monomials. -/
theorem cyclicFourierCoeff_absolute :
    SchauderBasis.IsAbsolute (cyclicFourierCoeff ∘ freq)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))) := by
  let : T2Space S := elementarySchwartz_t2
  let : BarrelledSpace ℂ (StrongDual ℂ S) := elementarySchwartz_strongDual_barrelled
  let : PolynormableSpace ℂ (StrongDual ℂ S) :=
    uniformConvergenceCLM_polynormable (F := ℂ) {B : Set S | IsVonNBounded ℂ B}
      (fun _ h ↦ h) (by rw [sUnion_isVonNBounded_eq_univ, Submodule.span_univ]; simp)
  apply SchauderBasis.isAbsolute_iff_summable_of_barrelled.2
  intro q hq L
  have hw (m : ℤ) : 0 < cyclicWeight m := by
    by_cases hm : m = 0
    · simp [cyclicWeight, hm]
    · simp [cyclicWeight, hm, cyclicFrequency, Real.pi_ne_zero, sq_pos_iff]
  let v (m : ℤ) := (cyclicWeight m : ℂ)⁻¹ • (L (cyclicExponential m) • cyclicFourierCoeff m)
  -- In the bidual it suffices to test these rescaled terms on circle functions.
  have hv : IsVonNBounded ℂ (range v) := by
    apply (isVonNBounded_iff_dual_image _).2
    intro φ
    obtain ⟨e, he⟩ := elementarySchwartz_reflexive (m := 0) (n := 1) (r := 0) (F := PUnit)
    obtain ⟨f, rfl⟩ := e.surjective φ
    let t (m : ℤ) := (cyclicWeight m : ℂ)⁻¹ • (cyclicFourierCoeff m f • cyclicExponential m)
    have ht : IsVonNBounded ℂ (range t) := by
      apply elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bounded.mpr
      intro i
      let C := elementarySchwartzSeminorm (0, 0, 0, 0) f +
        elementarySchwartzSeminorm (0, 0, fun _ ↦ i.2.2.1 0 + 2, 0) f
      have hC : 0 ≤ C := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
      refine ⟨C + 1, by positivity, ?_⟩
      rintro _ ⟨m, rfl⟩
      refine (map_smul_eq_mul (elementarySchwartzSeminorm i : Seminorm ℂ S)
        (cyclicWeight m : ℂ)⁻¹ (cyclicFourierCoeff m f • cyclicExponential m)).trans_lt ?_
      rw [norm_inv, Complex.norm_of_nonneg (hw m).le]
      exact lt_of_le_of_lt ((inv_mul_le_iff₀ (hw m)).mpr (cyclicTerm_seminorm_le f i m))
        (lt_add_one _)
    apply ((NormedSpace.isVonNBounded_iff ℂ).mp (ht.image L)).subset
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    refine ⟨_, mem_range_self m, ?_⟩
    rw [he]
    simp only [t, v, map_smul, smul_apply, smul_eq_mul, mul_comm (L _)]
  obtain ⟨C, _, hC⟩ :=
    (PolynormableSpace.withSeminorms ℂ (StrongDual ℂ S)).isVonNBounded_iff_seminorm_bounded.mp hv ⟨q, hq⟩
  change Summable ((fun m : ℤ ↦ q (L (cyclicExponential m) • cyclicFourierCoeff m)) ∘ freq)
  apply (freq).summable_iff.mpr
  apply (cyclicWeight_summable.mul_right C).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _)
  intro m
  have h : q (v m) ≤ C := (hC _ (mem_range_self m)).le
  dsimp only [v] at h
  rw [map_smul_eq_mul, norm_inv, Complex.norm_of_nonneg (hw m).le] at h
  exact (inv_mul_le_iff₀ (hw m)).mp h

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals
are bounded in the strong dual. -/
theorem cyclicFourierCoeff_bounded :
    IsVonNBounded ℂ (range cyclicFourierCoeff) := by
  apply ContinuousLinearMap.isVonNBounded_iff.mpr
  intro B hB
  obtain ⟨C, _, hC⟩ := elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bounded.mp
    hB (0, 0, fun _ ↦ 0, 0)
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨_, ⟨m, rfl⟩, f, hf, rfl⟩
  have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f m 0
  rw [iteratedDeriv_zero, ← cyclicFourierCoeff_eq_on] at h
  exact h.trans (hC f hf).le

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals are
equicontinuous as maps on the circle Schwartz space. -/
theorem cyclicFourierCoeff_equicontinuous :
    Equicontinuous (fun m : ℤ ↦ (cyclicFourierCoeff m : S → ℂ)) := by
  -- Every coefficient is bounded by the uniform norm, uniformly in the frequency.
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ 0, 0)
  intro f₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  filter_upwards [(elementarySchwartz_withSeminorms.tendsto_nhds id f₀).mp Filter.tendsto_id i ε hε]
    with f hf m
  have h := norm_fourierCoeffOn_iteratedDeriv_cyclic (f - f₀) m 0
  rw [iteratedDeriv_zero, ← cyclicFourierCoeff_eq_on, map_sub] at h
  rw [dist_comm, dist_eq_norm]
  exact h.trans_lt hf

-- TODO(paper-gap): The proof on p. 169 gives the positive Mellin frequency
-- and drops the Haar normalization factor. Formula (4.2.1.5) fixes both.

/-- Paper: Remark 4.2.1.8, p. 170. Periodization identifies the exponential-decay
quotient with the smooth circle Schwartz space.
Deviation: The source is the quotient by the kernel of the periodization. -/
theorem cyclicPeriodization_quotient_equiv (γ : ℝ) (hγ : 1 < γ) :
    let P := cyclicPeriodizationCLM γ hγ
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] S, ∀ f : E, e (P.ker.mkQL f) = P f := by
  exact ⟨periodizationQuotientEquiv γ hγ, fun _ ↦ rfl⟩

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is regular in
the smooth topology. -/
theorem cyclicExponential_regular :
    SchauderBasis.IsRegular (cyclicExponential ∘ freq) := by
  -- A monomial has its own coefficient one, and coefficients are bounded by the uniform norm,
  -- so no monomial lies in the open unit ball of that norm.
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ 0, 0)
  have hp : Continuous (fun f : S ↦ elementarySchwartzSeminorm i f) :=
    elementarySchwartz_withSeminorms.continuous_seminorm i
  refine ⟨{f | elementarySchwartzSeminorm i f < 1},
    (isOpen_lt hp continuous_const).mem_nhds
      ((map_zero (elementarySchwartzSeminorm i)).trans_lt one_pos), fun n hn ↦ ?_⟩
  have h := norm_fourierCoeffOn_iteratedDeriv_cyclic (cyclicExponential (freq n)) (freq n) 0
  rw [iteratedDeriv_zero, ← cyclicFourierCoeff_eq_on, cyclicFourierCoeff_exponential,
    ite_eq_left rfl, norm_one] at h
  exact lt_irrefl _ (h.trans_lt hn)

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is unbounded
in the smooth topology. -/
theorem cyclicExponential_not_bounded :
    ¬ IsVonNBounded ℂ (range cyclicExponential) := by
  -- The first-derivative seminorm of the monomial of frequency m is at least 2π|m|.
  intro hb
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ 1, 0)
  obtain ⟨r, -, hr⟩ :=
    (elementarySchwartz_withSeminorms.isVonNBounded_iff_seminorm_bounded).mp hb i
  let m : ℤ := ⌈r⌉₊
  have h := norm_fourierCoeffOn_iteratedDeriv_cyclic (cyclicExponential m) m 1
  rw [fourierCoeffOn_iteratedDeriv_cyclic, cyclicFourierCoeff_exponential, ite_eq_left rfl,
    mul_one, pow_one] at h
  have hnorm : ‖cyclicFrequency m‖ = 2 * Real.pi * ⌈r⌉₊ := by
    simp [cyclicFrequency, m, abs_of_pos Real.pi_pos]
  have hm : r ≤ ‖cyclicFrequency m‖ := by
    rw [hnorm]
    have h1 : r ≤ (⌈r⌉₊ : ℝ) := Nat.le_ceil r
    have h2 : (⌈r⌉₊ : ℝ) ≤ 2 * Real.pi * ⌈r⌉₊ :=
      le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith [Real.pi_gt_three])
    exact h1.trans h2
  exact (hm.trans h).not_gt (hr _ ⟨m, rfl⟩)

section CompactSupport

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "symmInterval[" a ", " b "]" =>
  Compacts.mk (Icc (Real.log b - Real.log a) (Real.log b + Real.log a)) isCompact_Icc

/-- Paper: §4.2.2, p. 170. A smooth logarithmic profile supported in a fixed
compact set satisfies all exponential Schwartz weights. -/
theorem compactLogProfile_mem (K : Compacts ℝ) (f : D[K]) :
    (f : ℝ → ℂ) ∈ logExponentialDecaySubmodule univ := by
  exact mem_logExponentialDecaySubmodule_of_hasCompactSupport univ f.hasCompactSupport f.contDiff

/-- Paper: §4.2.2, p. 170. Including profiles supported in a fixed compact set
into the exponential decay space is continuous for the uniform derivative topology. -/
theorem compactLogProfile_continuous (K : Compacts ℝ) :
    Continuous (Y := E) (fun f : D[K] ↦ ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩) := by
  exact (supportedToLogDecayCLM univ univ_nonempty K).continuous

/-- Paper: §4.2.2, p. 170. The inclusion of the fixed-support test space
takes the same function as an exponentially decaying profile.
Deviation: The support set is the logarithmic image of the paper's K. -/
def compactLogProfileInclusion (K : Compacts ℝ) : D[K] →L[ℂ] E where
  toFun f := ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := compactLogProfile_continuous K

/-- Forgetting the exponential weights is the continuous projection to the zero twist. -/
private def unweightedLogProfile : E →L[ℂ] 𝓢(ℝ, ℂ) :=
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  ⟨logExponentialDecayTwist univ a, (continuous_apply a).comp
    (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous⟩

private theorem unweightedLogProfile_apply (f : E) (x : ℝ) : unweightedLogProfile f x = f.val x := by
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  change logExponentialDecayTwist univ a (show logExponentialDecaySubmodule univ from f) x = _
  rw [logExponentialDecayTwist_apply]
  simp [a]

/-- Paper: §4.2.2, p. 170. A decay profile lies in the image of the test
space precisely when its topological support is contained in the designated compact set. -/
theorem compactLogProfileInclusion_range (K : Compacts ℝ) (f : E) :
    f ∈ range (compactLogProfileInclusion K) ↔ tsupport f.val ⊆ (K : Set ℝ) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.tsupport_subset
  · intro h
    have hs : ContDiff ℝ ∞ f.val := by
      simpa only [show (unweightedLogProfile f : ℝ → ℂ) = f.val from funext (unweightedLogProfile_apply f)] using
        (unweightedLogProfile f).smooth (⊤ : ℕ∞)
    exact ⟨⟨f.val, hs, support_subset_iff'.mp ((subset_tsupport _).trans h)⟩, rfl⟩

/-- Paper: Theorem 4.2.2.1, p. 170. An entire function is a Fourier integral
of an L² function supported on the indicated interval exactly when it has
the stated exponential type and an L² trace on the real line. -/
theorem paleyWiener_compactInterval (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z, f z = ∫ x in Ioo (-A) A, F x * Complex.exp (Complex.I * (x : ℂ) * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ ↦ f x) 2 volume) := by
  exact paleyWiener_interval A hA f hf

-- TODO(paper-gap): The multiplicative restatement following 4.2.2.1
-- uses A directly as an interval endpoint. The endpoint for type A is exp A.

variable (γ : ℝ) (hγ : 1 < γ)

local notation "Φ[" K "]" =>
  ContinuousLinearMap.comp (cyclicPeriodizationCLM γ hγ) (compactLogProfileInclusion K)

-- TODO(paper-gap): Proposition 4.2.2.2(1) asserts surjectivity for all compact K
-- mapping onto the quotient. For K = [1, γ], the class of 1 has only endpoint
-- representatives in K, where every smooth test function supported in K vanishes.

include hγ in
/-- Paper: Proposition 4.2.2.2(1), p. 171. The closed multiplicative interval
of radius a about b covers the quotient when its logarithmic length exceeds log γ.
Deviation: The interval and quotient map are in logarithmic coordinates. -/
theorem cyclicQuotient_surjOn_interval (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T))
      (symmInterval[a, b] : Set ℝ) univ := by
  intro z _
  let L := Real.log γ
  let A := Real.log (b / a)
  have hL : 0 < L := Real.log_pos hγ
  have hA : A = Real.log b - Real.log a := Real.log_div hb.ne' (lt_trans zero_lt_one ha).ne'
  let r := (AddCircle.equivIco (1 : ℝ) (A / L)) z
  have hr : (r : ℝ) ∈ Ico (A / L) (A / L + 1) := r.property
  refine ⟨(r : ℝ) * L, ⟨?_, ?_⟩, ?_⟩
  · rw [← hA]
    exact (div_le_iff₀ hL).mp hr.1
  · have hu := mul_lt_mul_of_pos_right hr.2 hL
    rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul] at hu
    change _ ≤ Real.log b + Real.log a
    dsimp only [L] at hu
    linarith [hA]
  · change ((↑((r : ℝ) * L / L) : T)) = z
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco

/-- Multiply a rescaled periodic lift by a fixed compactly supported window. -/
private def windowedCyclicLift (K : Compacts ℝ) (χ : D[K]) (t : ℝ) : S →L[ℂ] D[K] := by
  let g (f : S) (x : ℝ) := cyclicLift f (t * x)
  have hg (f : S) : ContDiff ℝ ∞ (g f) :=
    (cyclicLift_contDiff f).comp (contDiff_const.mul contDiff_id)
  let A : S →ₗ[ℂ] D[K] :=
    { toFun f := ⟨fun x ↦ χ x * g f x, χ.contDiff.mul (hg f), fun x hx ↦ by
        change χ x * g f x = 0
        simp [χ.zero_on_compl hx]⟩
      map_add' f f' := ContDiffMapSupportedIn.ext fun x ↦ mul_add _ _ _
      map_smul' c f := ContDiffMapSupportedIn.ext fun x ↦ mul_left_comm _ _ _ }
  refine ⟨A, (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K).continuous_of_continuous_comp A ?_⟩
  intro n
  choose C hC using fun i : ℕ ↦ K.isCompact.exists_bound_of_continuousOn
    (χ.contDiff.continuous_iteratedDeriv i (by simp)).continuousOn
  let w (i : ℕ) : NNReal := ⟨(n.choose i : ℝ) * |C i| * ‖t ^ (n - i)‖, by positivity⟩
  let p (i : ℕ) : Seminorm ℂ S := elementarySchwartzSeminorm (0, 0, fun _ ↦ n - i, 0)
  let q := ∑ i ∈ Finset.range (n + 1), w i • p i
  have hq : Continuous q := Seminorm.continuous_finsetSum fun i _ ↦
    (elementarySchwartz_withSeminorms.continuous_seminorm _).const_smul (w i)
  apply Seminorm.continuous_of_le (q := q) hq
  intro f
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg q f) n (A f)).2
  intro x hx
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv n (fun y ↦ χ y * g f y) x‖ ≤ q f
  rw [iteratedDeriv_fun_mul (χ.contDiff.of_le (by simp)).contDiffAt ((hg f).of_le (by simp)).contDiffAt]
  refine (norm_sum_le _ _).trans ?_
  have hqf : q f = ∑ i ∈ Finset.range (n + 1), (w i : ℝ) * p i f := by
    change FunLike.coeAddMonoidHom (Seminorm ℂ S) S ℝ _ f = _
    rw [map_sum, Finset.sum_apply]
    rfl
  rw [hqf]
  apply Finset.sum_le_sum
  intro i _
  dsimp only [g]
  rw [iteratedDeriv_comp_const_smul ((cyclicLift_contDiff f).of_le (by simp)) t]
  simp only [norm_mul, Complex.norm_natCast, norm_smul]
  change _ ≤ ((n.choose i : ℝ) * |C i| * ‖t ^ (n - i)‖) * p i f
  simp only [mul_assoc]
  gcongr
  · exact (hC i x hx).trans (le_abs_self _)
  · exact cyclicSeminorm_ge f (n - i) _
/-- A difference of two translated smooth steps partitions unity along each orbit.
The extra width of the interval accommodates the transition between adjacent translates. -/
private theorem compactIntervalSection (a b : ℝ)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    ∃ s : S →L[ℂ] D[K], RightInverse s ((cyclicPeriodizationCLM γ hγ).comp
      (compactLogProfileInclusion K)) := by
  let L := Real.log γ
  let l := Real.log b - Real.log a
  let w := min L (2 * Real.log a - L)
  have hL : 0 < L := Real.log_pos hγ
  have hw : 0 < w := lt_min hL (sub_pos.mpr hwide)
  have hwL : w ≤ L := min_le_left _ _
  have hwidth : l + L + w ≤ Real.log b + Real.log a := by
    have := min_le_right L (2 * Real.log a - L)
    dsimp only [l, w]
    linarith
  let u (x : ℝ) : ℂ := Real.smoothTransition ((x - l)/w)
  have hu : ContDiff ℝ ∞ u := Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const w))
  have u₀ {x} (hx : x ≤ l) : u x = 0 := by
    simp [u, Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hw.le)]
  have u₁ {x} (hx : l + w ≤ x) : u x = 1 := by
    simp [u, Real.smoothTransition.one_of_one_le ((le_div_iff₀ hw).mpr (by linarith) : 1 ≤ (x - l)/w)]
  let K := symmInterval[a, b]
  let χ : D[K] :=
    ⟨fun x ↦ u x - u (x - L), hu.sub (hu.comp (contDiff_id.sub contDiff_const)), fun x hx ↦ by
      change u x - u (x - L) = 0
      change ¬(l ≤ x ∧ x ≤ Real.log b + Real.log a) at hx
      by_cases hxl : l ≤ x
      · have : Real.log b + Real.log a < x := lt_of_not_ge (fun h ↦ hx ⟨hxl, h⟩)
        rw [u₁ (by linarith), u₁ (by linarith), sub_self]
      · rw [u₀ (by linarith), u₀ (by linarith), sub_self]⟩
  let s := windowedCyclicLift K χ L⁻¹
  refine ⟨s, fun f ↦ ?_⟩
  apply Subtype.ext
  funext g
  let r := (AddCircle.equivIco 1 (l/L)) (g.2.1 0)
  let x := (r : ℝ) * L
  have hx : l ≤ x ∧ x < l + L := by
    obtain ⟨hr₁, hr₂⟩ := r.property
    exact ⟨(div_le_iff₀ hL).mp hr₁, by
      change (r : ℝ) * L < l + L
      convert mul_lt_mul_of_pos_right hr₂ hL using 1
      rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul]⟩
  have hxg : (point ((x/L : ℝ) : T)) = g := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext (funext fun j ↦ ?_) (Subsingleton.elim _ _))
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r : ℝ) * L / L) : T) = _
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco
  have hper (k : ℤ) : cyclicLift f (L⁻¹ * (x + k * L)) = f g := by
    have he : L⁻¹ * (x + k * L) = x/L + k * 1 := by field_simp [hL.ne']
    rw [he, (cyclicLift_periodic f).int_mul k]
    exact congrArg (fun z : G ↦ f z) hxg
  let F := compactLogProfileInclusion K (s f)
  have hterm (k : ℤ) : F.val (x + k * L) = (u (x + k * L) - u (x + k * L - L)) * f g := by
    change (u _ - u _) * cyclicLift f (L⁻¹ * (x + k * L)) = _
    rw [hper]
  have hs := cyclicPeriodization_hasSum γ hγ F x
  change ((cyclicPeriodization γ hγ F) g) = f g
  rw [← hxg, ← hs.tsum_eq, hxg]
  change (∑' k : ℤ, F.val (x + k * L)) = _
  rw [tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
  · simp only [Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)), Finset.sum_singleton,
      hterm, Int.cast_zero, Int.cast_one, zero_mul, add_zero, one_mul, add_sub_cancel_right]
    rw [u₀ (x := x - L) (by linarith [hx.2]), u₁ (x := x + L) (by linarith [hx.1])]
    ring
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [hterm]
    rcases lt_or_ge k 0 with hneg | hpos
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have h := mul_le_mul_of_nonneg_right hk' hL.le
      rw [u₀ (by linarith [hx.2]), u₀ (by linarith [hx.2]), sub_self, zero_mul]
    · have hk' : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
      have h := mul_le_mul_of_nonneg_right hk' hL.le
      rw [u₁ (by linarith [hx.1]), u₁ (by linarith [hx.1]), sub_self, zero_mul]

/-- Paper: Proposition 4.2.2.2(1), p. 171. Periodization gives a continuous
linear isomorphism from the fixed-support interval quotient to the smooth circle space.
Deviation: This states the strict-width interval case treated on p. 172. -/
theorem compactIntervalPeriodization_quotient_equiv (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ e : (D[K] ⧸ P.ker) ≃L[ℂ] S, ∀ f : D[K], e (P.ker.mkQL f) = P f := by
  clear ha hb
  let P := Φ[symmInterval[a, b]]
  obtain ⟨s, hs⟩ := compactIntervalSection γ hγ a b hwide
  let e := P.toLinearMap.quotKerEquivOfSurjective hs.surjective
  have hinv : Continuous e.symm := (P.ker.mkQL.continuous.comp s.continuous).congr fun y ↦ by
    change P.ker.mkQL (s y) = e.symm y
    apply e.injective
    exact (hs y).trans (e.apply_symm_apply y).symm
  let d : (_ ⧸ P.ker) ≃L[ℂ] S :=
    { e with
      continuous_toFun := P.ker.isQuotientMap_mkQL.continuous_iff.mpr P.continuous
      continuous_invFun := hinv }
  exact ⟨d, fun _ ↦ rfl⟩

-- TODO(paper-gap): Proposition 4.2.2.2(2) with a = γ, b = 1, and A₀ = γ
-- forces ψ to be supported in {1}. For a nonzero smooth bump u supported
-- in (1, γ), the function x ↦ u(x) - u(γx) is nonzero and in the stated kernel.

include hγ in
/-- Paper: Remark 4.2.2.3, p. 171. A compact set containing a slightly
enlarged translated fundamental interval covers the quotient. -/
theorem cyclicQuotient_surjOn_of_contains (K : Compacts ℝ) (n : ℤ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hK : Icc (n * Real.log γ + Real.log (1 - ε))
      (n * Real.log γ + Real.log (γ + ε)) ⊆ (K : Set ℝ)) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T)) (K : Set ℝ) univ := by
  intro z _
  let L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  let r := (AddCircle.equivIco (1 : ℝ) (n : ℝ)) z
  have hr : (r : ℝ) ∈ Ico (n : ℝ) ((n : ℝ) + 1) := r.property
  refine ⟨(r : ℝ) * L, hK ⟨?_, ?_⟩, ?_⟩
  · have hlog := Real.log_nonpos (by linarith : 0 ≤ 1 - ε) (by linarith : 1 - ε ≤ 1)
    exact (add_le_of_nonpos_right hlog).trans (mul_le_mul_of_nonneg_right hr.1 hL.le)
  · have hlog : L ≤ Real.log (γ + ε) :=
      Real.log_le_log (by linarith) (by linarith)
    have hu := mul_le_mul_of_nonneg_right hr.2.le hL.le
    rw [add_mul, one_mul] at hu
    exact hu.trans (add_le_add (le_refl _) hlog)
  · change (↑((r : ℝ) * L / L) : T) = z
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco

/-- Paper: Lemma 4.2.2.4, p. 171. The test space with support in a given
compact set is a closed subspace of the exponential decay space. -/
theorem compactLogProfileInclusion_closed (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsClosed (range (compactLogProfileInclusion K)) := by
  clear hK
  have he : range (compactLogProfileInclusion K) = ⋂ x : ↥((K : Set ℝ)ᶜ), {f : E | f.val x = 0} := by
    ext f
    rw [compactLogProfileInclusion_range, mem_iInter]
    constructor
    · intro h x
      exact support_subset_iff'.mp ((subset_tsupport _).trans h) x x.property
    · intro h
      exact closure_minimal (support_subset_iff'.mpr fun x hx ↦ h ⟨x, hx⟩) K.isCompact.isClosed
  rw [he]
  apply isClosed_iInter
  intro x
  have hc : Continuous (fun f : E ↦ f.val x) := by
    simpa only [Function.comp_def, SchwartzMap.toBoundedContinuousFunctionCLM_apply, unweightedLogProfile_apply] using
      ((continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) (x : ℝ)).comp
        ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp unweightedLogProfile.continuous))
  exact isClosed_eq hc continuous_const

/-- Paper: Lemma 4.2.2.4, p. 171. The test space's uniform derivative topology
agrees with the topology inherited from the exponential decay space. -/
theorem compactLogProfileInclusion_isEmbedding (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsEmbedding (compactLogProfileInclusion K) := by
  clear hK
  let P := compactLogProfileInclusion K
  have hi : Injective P := by
    intro f g he
    exact ContDiffMapSupportedIn.ext fun x ↦ congrArg (fun F : E ↦ F.val x) he
  let e := LinearEquiv.ofInjective P.toLinearMap hi
  let U := unweightedLogProfile.comp P.range.subtypeL
  have hfun (f : P.range) : (e.symm f : ℝ → ℂ) = (U f : ℝ → ℂ) := by
    obtain ⟨g, rfl⟩ := e.surjective f
    rw [e.symm_apply_apply]
    exact funext fun x ↦ (unweightedLogProfile_apply (P g) x).symm
  have hc : Continuous e.symm := by
    apply (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K).continuous_of_continuous_comp e.symm.toLinearMap
    intro n
    let q := (SchwartzMap.seminorm ℂ 0 n).comp U.toLinearMap
    apply Seminorm.continuous_of_le (q := q) (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0,n)).comp U.continuous)
    intro f
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg q f) n (e.symm f)).2
    intro x _
    rw [hfun]
    exact (U f).norm_iteratedFDeriv_le_seminorm ℂ n x
  let H : D[K] ≃L[ℂ] P.range :=
    { e with continuous_toFun := P.rangeRestrict.continuous, continuous_invFun := hc }
  exact IsEmbedding.subtypeVal.comp H.toHomeomorph.isEmbedding

private theorem transportAbsoluteBasis {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (e : X ≃L[ℂ] Y) {x : ℕ → X} {c : ℕ → StrongDual ℂ X}
    (ha : SchauderBasis.IsAbsolute x c) :
    SchauderBasis.IsAbsolute (e ∘ x) (fun n ↦ (c n).comp e.symm.toContinuousLinearMap) := by
  intro q hq
  obtain ⟨p, hp, h⟩ := ha (q.comp e.toLinearMap) (hq.comp e.continuous)
  refine ⟨p.comp e.symm.toLinearMap, hp.comp e.symm.continuous, fun y ↦ ?_⟩
  have ht (n : ℕ) : (q.comp e.toLinearMap) (c n (e.symm y) • x n) =
      q ((c n).comp e.symm.toContinuousLinearMap y • (e ∘ x) n) :=
    congrArg q (map_smul e _ _)
  change _ ∧ _ ≤ p (e.symm y)
  simpa only [ht] using h (e.symm y)

/-- Paper: Proposition 4.2.2.5(1), p. 173. The Mellin evaluation sequence
is an absolute Schauder basis of the strong quotient dual. This dual is
identified with the annihilator by Lemma 4.2.1.3. -/
theorem cyclicQuotientMellinCoeff_absoluteBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ (cyclicPeriodizationCLM γ hγ).ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by
  let e := periodizationQuotientEquiv γ hγ
  let d := mellinDualEquiv e γ hγ
  have he : d ∘ (cyclicFourierCoeff ∘ freq) = cyclicQuotientMellinCoeff γ hγ ∘ freq := by
    funext n
    exact mellinDualEquiv_apply e γ hγ _
  exact ⟨_, he ▸ transportSchauderBasis d cyclicFourierCoeff_unconditionalBasis.1,
    he ▸ transportAbsoluteBasis d cyclicFourierCoeff_absolute⟩

/-- Paper: Proposition 4.2.2.5(2), p. 173. For an interval wider than a
fundamental interval, all monomials have lifts supported in that same interval,
whose classes are an absolute Schauder basis for the fixed-support quotient. -/
theorem compactIntervalPeriodization_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ u : ℤ → D[K], (∀ m, P (u m) = cyclicExponential m) ∧
      let basis := P.ker.mkQL ∘ u ∘ freq
      let coeff := fun n ↦ (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
      IsSchauderBasis basis coeff ∧ SchauderBasis.IsAbsolute basis coeff := by
  let P := Φ[symmInterval[a, b]]
  obtain ⟨e, he⟩ := compactIntervalPeriodization_quotient_equiv γ hγ a b
    ((Real.log_pos_iff ha.le).mp (by linarith [Real.log_pos hγ])) hb hwide
  choose u hu using fun m ↦ P.ker.mkQ_surjective (e.symm (cyclicExponential m))
  refine ⟨u, fun m ↦ (he _).symm.trans ((congrArg e (hu m)).trans (e.apply_symm_apply _)), ?_⟩
  have hbasis : P.ker.mkQL ∘ u ∘ freq = e.symm ∘ (cyclicExponential ∘ freq) :=
    funext fun n ↦ hu (freq n)
  have hd : P.ker.liftQL P le_rfl = e.toContinuousLinearMap := by
    ext z
    obtain ⟨f, rfl⟩ := P.ker.mkQ_surjective z
    exact (he f).symm
  dsimp only
  rw [hbasis, hd]
  exact ⟨transportSchauderBasis e.symm cyclicExponential_absoluteBasis.1,
    transportAbsoluteBasis e.symm cyclicExponential_absoluteBasis.2⟩

/-- Paper: Proposition 4.2.2.5(2), p. 173. Descending the restricted Mellin
evaluations gives an absolute Schauder basis of the strong fixed-support quotient dual. -/
theorem compactIntervalPeriodization_dual_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    let δ := fun n ↦ (Real.log γ : ℂ) •
      (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (D[K] ⧸ P.ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by
  let P := Φ[symmInterval[a, b]]
  obtain ⟨e, he⟩ := compactIntervalPeriodization_quotient_equiv γ hγ a b
    ((Real.log_pos_iff ha.le).mp (by linarith [Real.log_pos hγ])) hb hwide
  let d := mellinDualEquiv e γ hγ
  have hd : d ∘ (cyclicFourierCoeff ∘ freq) = fun n ↦
      (Real.log γ : ℂ) • (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl) := by
    funext n
    rw [Function.comp_apply, mellinDualEquiv_apply]
    congr 2
    ext z
    obtain ⟨f, rfl⟩ := P.ker.mkQ_surjective z
    exact he f
  exact ⟨_, hd ▸ transportSchauderBasis d cyclicFourierCoeff_unconditionalBasis.1,
    hd ▸ transportAbsoluteBasis d cyclicFourierCoeff_absolute⟩

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on ordinary Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicSchwartzPeriodization_hasSection :
    ∃ s : S →L[ℂ] 𝓢(ℝ, ℂ), Function.RightInverse s (cyclicSchwartzPeriodization γ hγ) := by
  obtain ⟨s, hs⟩ := compactIntervalSection γ hγ γ 1 (by linarith [Real.log_pos hγ])
  exact ⟨unweightedLogProfile.comp ((compactLogProfileInclusion _).comp s), hs⟩

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on exponential Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicPeriodization_hasSection :
    ∃ s : S →L[ℂ] E, Function.RightInverse s (cyclicPeriodizationCLM γ hγ) := by
  obtain ⟨s, hs⟩ := compactIntervalSection γ hγ γ 1 (by linarith [Real.log_pos hγ])
  exact ⟨(compactLogProfileInclusion _).comp s, hs⟩

/-- The enumeration of the rank-one lattice `Fin 1 → ℤ` by `ℕ`, through `Equiv.intEquivNat`. -/
abbrev latticeIndex : ℕ ≃ (Fin 1 → ℤ) :=
  (freq).trans (Equiv.funUnique (Fin 1) ℤ).symm

/-- The weight `1 + |k|` of the `n`-th lattice point `k` in the enumeration `latticeIndex`. -/
def latticeWeight (n : ℕ) : ℝ := 1 + |((freq n : ℤ) : ℝ)|

/-- The lattice weight of the `n`-th point is between `(n + 1) / 2` and `n + 1`, and at least `1`. -/
theorem latticeWeight_bounds (n : ℕ) :
    1 ≤ latticeWeight n ∧ latticeWeight n ≤ n + 1 ∧ (n : ℝ) + 1 ≤ 2 * latticeWeight n := by
  obtain ⟨m, rfl⟩ := Equiv.intEquivNat.surjective n
  rw [latticeWeight, Equiv.symm_apply_apply]
  cases m with
  | ofNat m =>
    change 1 ≤ 1 + |(m : ℝ)| ∧ 1 + |(m : ℝ)| ≤ ((2 * m : ℕ) : ℝ) + 1 ∧
      ((2 * m : ℕ) : ℝ) + 1 ≤ 2 * (1 + |(m : ℝ)|)
    push_cast
    rw [abs_of_nonneg (Nat.cast_nonneg m)]
    exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) m], by linarith [Nat.cast_nonneg (α := ℝ) m], by linarith⟩
  | negSucc m =>
    simp only [Int.cast_negSucc, abs_neg]
    change _ ∧ _ ≤ ((2 * m + 1 : ℕ) : ℝ) + 1 ∧ ((2 * m + 1 : ℕ) : ℝ) + 1 ≤ _
    push_cast
    rw [abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1)]
    exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) m], by linarith [Nat.cast_nonneg (α := ℝ) m], by linarith⟩

private theorem rapidBound_eq (a : (Fin 1 → ℤ) → ℂ) (j : ℕ) :
    rapidDecaySequenceBound j a =
      ∑' n, ENNReal.ofReal (latticeWeight n ^ j * ‖a (latticeIndex n)‖) := by
  unfold rapidDecaySequenceBound
  rw [← latticeIndex.tsum_eq]
  apply tsum_congr
  intro n
  have hw : 0 ≤ latticeWeight n := zero_le_one.trans (latticeWeight_bounds n).1
  rw [ENNReal.ofReal_mul (pow_nonneg hw _), ENNReal.ofReal_pow hw, ofReal_norm]
  congr 2
  rw [latticeWeight, ENNReal.ofReal_add zero_le_one (abs_nonneg _), ENNReal.ofReal_one]
  congr 1
  change ‖(WithLp.toLp 2 (fun i ↦ ((latticeIndex n i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin 1))‖ₑ = _
  rw [← ofReal_norm, EuclideanSpace.norm_eq]
  simp [latticeIndex, Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

/-- A sequence on the rank-one lattice decays rapidly exactly when it is summable against every
power of the lattice weight. -/
theorem rapidSequence_mem_iff (a : (Fin 1 → ℤ) → ℂ) :
    a ∈ rapidDecaySequenceSubmodule 1 ↔
      ∀ j : ℕ, Summable (fun n ↦ latticeWeight n ^ j * ‖a (latticeIndex n)‖) := by
  change (∀ j, rapidDecaySequenceBound j a < ⊤) ↔ _
  have hw (j n : ℕ) : 0 ≤ latticeWeight n ^ j * ‖a (latticeIndex n)‖ :=
    mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _) (norm_nonneg _)
  simp_rw [rapidBound_eq]
  constructor
  · intro h j
    simpa only [ENNReal.toReal_ofReal (hw j _)] using ENNReal.summable_toReal (h j).ne
  · intro h j
    rw [← ENNReal.ofReal_tsum_of_nonneg (hw j) (h j)]
    exact ENNReal.ofReal_lt_top

private theorem rapidSeminorm_eq (a : RapidDecaySequence 1) (j : ℕ) :
    rapidDecaySequenceSeminorm j a = ∑' n, latticeWeight n ^ j * ‖a (latticeIndex n)‖ := by
  change (rapidDecaySequenceBound j a.val).toReal = _
  rw [rapidBound_eq, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  exact ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)
    (norm_nonneg _))
/-- Each coordinate of a rapidly decaying sequence on the rank-one lattice is continuous. -/
theorem rapidCoordinate_continuous (n : ℕ) :
    Continuous (fun a : RapidDecaySequence 1 ↦ a (latticeIndex n)) := by
  let L : RapidDecaySequence 1 →ₗ[ℂ] ℂ :=
    { toFun a := a (latticeIndex n), map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let p (j : ℕ) : Seminorm ℂ (RapidDecaySequence 1) := rapidDecaySequenceSeminorm j
  have hp : WithSeminorms p := rapidDecaySequence_withSeminorms
  apply hp.continuous_normedSpace_rng ℂ L
  refine ⟨{0}, 1, fun a ↦ ?_⟩
  have hs := (rapidSequence_mem_iff a.val).mp a.property 0
  simp only [pow_zero, one_mul] at hs
  have h : ‖L a‖ ≤ p 0 a := by
    rw [show p 0 a = _ from rapidSeminorm_eq a 0]
    simp only [pow_zero, one_mul]
    exact hs.le_tsum n (fun _ _ ↦ norm_nonneg _)
  simpa [Seminorm.comp_apply] using h

private theorem summable_latticeWeight_inv_sq : Summable (fun n ↦ (latticeWeight n ^ 2)⁻¹) := by
  have h := (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective
  apply (h.mul_left 4).of_nonneg_of_le (fun n ↦ by positivity)
  intro n
  change (latticeWeight n ^ 2)⁻¹ ≤ 4 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hn := (latticeWeight_bounds n).2.2
  have hw := (latticeWeight_bounds n).1
  rw [Nat.cast_succ, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (sq_pos_of_pos (by linarith))
    (sq_pos_of_pos (by positivity))]
  nlinarith [sq_nonneg (latticeWeight n), mul_self_le_mul_self (by positivity : 0 ≤ (n : ℝ) + 1) hn]

section RapidSynthesis

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X]
  {ι : Type*} {p : ι → Seminorm ℂ X}

/-- Synthesis from polynomially growing vectors with rapidly decreasing, separating coordinates. -/
private theorem rapidSynthesisEquiv (hX : IsFrechetTVS X) (hp : WithSeminorms p)
    (b : ℕ → X) (c : ℕ → StrongDual ℂ X)
    (hortho : ∀ n m, c n (b m) = if n = m then 1 else 0)
    (hsep : ∀ x, (∀ n, c n x = 0) → x = 0)
    (hgrowth : ∀ i, ∃ (C : ℝ) (k : ℕ), ∀ n, p i (b n) ≤ C * latticeWeight n ^ k)
    (hdecay : ∀ (j : ℕ) (x : X), ∃ C : ℝ, ∀ n, latticeWeight n ^ j * ‖c n x‖ ≤ C) :
    Nonempty (X ≃L[ℂ] RapidDecaySequence 1) := by
  classical
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _, hmet, hcomplete⟩ := hX
  let : PolynormableSpace ℂ X := hp.toPolynormableSpace
  let R := RapidDecaySequence 1
  have hR : IsFrechetTVS R := rapidDecaySequence_isFrechet
  let : MetrizableSpace R := hR.2.2.1
  let : BarrelledSpace ℂ R := isFrechetTVS_barrelled hR
  let coord (n : ℕ) : R →L[ℂ] ℂ :=
    { toFun a := a (latticeIndex n), map_add' _ _ := rfl, map_smul' _ _ := rfl,
      cont := rapidCoordinate_continuous n }
  let t (a : R) (n : ℕ) := coord n a • b n
  have ht (a : R) : Summable (t a) := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff,
      hp.tendsto_nhds]
    intro i ε hε
    obtain ⟨C, k, hC⟩ := hgrowth i
    let j : X →ₗ[ℂ] LocalBanach (p i) := UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hj (x : X) : ‖j x‖ = p i x := localBanach_norm_coe (p i) x
    have hsum : Summable (fun n ↦ j (t a n)) := by
      apply Summable.of_norm
      apply (((rapidSequence_mem_iff a.val).mp a.property k).mul_left C).of_nonneg_of_le
        (fun _ ↦ norm_nonneg _)
      intro n
      rw [hj, show p i (t a n) = ‖coord n a‖ * p i (b n) from map_smul_eq_mul ..]
      calc
        _ ≤ ‖coord n a‖ * (C * latticeWeight n ^ k) := mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _)
        _ = _ := by change _ = C * (latticeWeight n ^ k * ‖coord n a‖); ring
    have ht' := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp hsum)
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at ht'
    filter_upwards [ht' ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum,
      ← map_sub, hj] at hz
    simpa only [sub_zero, Function.comp_apply] using hz
  let synthesisSum (N : ℕ) := ∑ n ∈ Finset.range N, (coord n).smulRight (b n)
  have htend : Filter.Tendsto (fun N a ↦ synthesisSum N a) Filter.atTop (𝓝 (fun a ↦ ∑' n, t a n)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    simpa only [synthesisSum, sum_apply, ContinuousLinearMap.smulRight_apply] using (ht a).hasSum.tendsto_sum_nat
  let A : R →L[ℂ] X := continuousLinearMapOfTendsto synthesisSum htend
  have hc (a : R) (n : ℕ) : c n (A a) = coord n a := by
    have h := (ht a).hasSum.mapL (c n)
    change HasSum (fun m ↦ c n (coord m a • b m)) (c n (A a)) at h
    simp only [map_smul, hortho, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
    simpa using h.tsum_eq.symm
  have hinj : Injective A := by
    intro a d he
    apply Subtype.ext
    funext i
    obtain ⟨n, rfl⟩ := latticeIndex.surjective i
    exact (hc a n).symm.trans ((congrArg (c n) he).trans (hc d n))
  have hsurj : Surjective A := by
    intro x
    let v (i : Fin 1 → ℤ) := c (latticeIndex.symm i) x
    have hv : v ∈ rapidDecaySequenceSubmodule 1 := by
      apply (rapidSequence_mem_iff v).mpr
      intro j
      obtain ⟨C, hC⟩ := hdecay (j + 2) x
      apply (summable_latticeWeight_inv_sq.mul_right C).of_nonneg_of_le
        (fun n ↦ mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _) (norm_nonneg _))
      intro n
      simp only [v, latticeIndex.symm_apply_apply]
      rw [← div_eq_inv_mul, le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans_le (latticeWeight_bounds n).1))]
      simpa only [pow_add, mul_right_comm] using hC n
    let a : R := ⟨v, hv⟩
    refine ⟨a, sub_eq_zero.mp (hsep _ fun n ↦ ?_)⟩
    rw [map_sub, hc]
    change c (latticeIndex.symm (latticeIndex n)) x - c n x = 0
    simp
  let e := LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩
  have hop : IsOpenMap A := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS ⟨inferInstance,
    inferInstance, hmet, hcomplete⟩) (X := fun _ ↦ R) (fun _ ↦ hR) (fun _ ↦ ContinuousLinearMap.id ℂ R)
    (fun _ ↦ Subset.rfl) (fun a ↦ ⟨0, a, rfl⟩) A hsurj
  let d : R ≃L[ℂ] X :=
    { e with continuous_toFun := A.continuous, continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }
  exact ⟨d.symm⟩

end RapidSynthesis

/-- Paper: Remark 4.2.2.6, p. 173. The circle Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing integer sequences. -/
theorem cyclicSchwartz_equiv_rapidDecay :
    Nonempty (S ≃L[ℂ] RapidDecaySequence 1) := by
  let : T2Space S := elementarySchwartz_t2
  let b := cyclicExponential ∘ freq
  let c := cyclicFourierCoeff ∘ freq
  have hb := cyclicExponential_absoluteBasis.1
  have hn (m : ℤ) : ‖cyclicFrequency m‖ = (2 * Real.pi) * |(m : ℝ)| := by
    simp [cyclicFrequency, abs_of_pos Real.pi_pos]
  apply rapidSynthesisEquiv elementarySchwartz_isFrechet elementarySchwartz_withSeminorms b c hb.1
  · intro f hf
    have h := hb.2 f
    change HasSum (fun n ↦ c n f • b n) f (SummationFilter.conditional ℕ) at h
    simp only [hf, zero_smul] at h
    exact h.unique (by simp)
  · intro i
    let k := i.2.2.1 0
    refine ⟨(2 * Real.pi) ^ k, k, fun n ↦ cyclicSeminorm_le _ i (mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _)) fun x _ ↦ ?_⟩
    let m := freq n
    have hd := cyclicTerm_deriv (cyclicExponential m) m k
    simp only [cyclicFourierCoeff_exponential, ite_true, one_smul, mul_one] at hd
    change ‖iteratedDeriv k (cyclicLift (cyclicExponential m)) x‖ ≤ _
    rw [hd, norm_mul, fourier_apply, Circle.norm_coe, mul_one, norm_pow, hn, mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (by
      change |(m : ℝ)| ≤ 1 + |(m : ℝ)|
      linarith) _) (by positivity)
  · intro j f
    let p := (elementarySchwartzSeminorm (0, 0, fun _ ↦ j, 0) : Seminorm ℂ S)
    refine ⟨‖cyclicFourierCoeff 0 f‖ + p f, fun n ↦ ?_⟩
    let m := freq n
    by_cases hm : m = 0
    · change (1 + |(m : ℝ)|) ^ j * ‖cyclicFourierCoeff m f‖ ≤ _
      rw [hm]
      simp only [Int.cast_zero, abs_zero, add_zero, one_pow, one_mul]
      exact le_add_of_nonneg_right (apply_nonneg p f)
    · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
      have hw : latticeWeight n ≤ ‖cyclicFrequency m‖ := by
        rw [hn]
        change 1 + |(m : ℝ)| ≤ _
        nlinarith [Real.pi_gt_three, mul_le_mul_of_nonneg_right Real.pi_gt_three.le (abs_nonneg (m : ℝ))]
      have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f m j
      rw [fourierCoeffOn_iteratedDeriv_cyclic, norm_mul, norm_pow] at h
      refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
        (zero_le_one.trans (latticeWeight_bounds n).1) hw j) (norm_nonneg _)).trans ?_
      exact h.trans (le_add_of_nonneg_left (norm_nonneg _))

/-- Paper: Remark 4.2.2.6, p. 173. The real Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing sequences. -/
theorem realSchwartz_equiv_rapidDecay :
    Nonempty (𝓢(ℝ, ℂ) ≃L[ℂ] RapidDecaySequence 1) := by
  let V := EuclideanSpace ℝ (Fin 1)
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure V)
  obtain ⟨b, B, hb, hg, hd⟩ := euclideanSchwartz_hermite_estimates 1 (by decide)
  change ∀ n, J (b n) = B n at hb
  let c (n : ℕ) := (innerSL ℂ (B n)).comp J
  have hc (n : ℕ) (f : 𝓢(V, ℂ)) : c n f = B.repr (J f) n := (B.repr_apply_apply _ _).symm
  let e : V ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  suffices h : Nonempty (𝓢(V, ℂ) ≃L[ℂ] RapidDecaySequence 1) from
    ⟨(schwartzChangeVariable ℂ e).trans h.some⟩
  apply rapidSynthesisEquiv (euclideanSchwartz_frechet 1) (schwartz_withSeminorms ℂ V ℂ) b c
  · intro n m
    rw [hc, hb, B.repr_self]
    by_cases h : n = m <;> simp [h, lp.single_apply]
  · intro f hf
    have hJ : J f = 0 := by
      apply B.repr.injective
      ext n
      rw [map_zero]
      exact (hc n f).symm.trans (hf n)
    apply SchwartzMap.ext
    have he := f.coeFn_toLp 2 (volume : Measure V)
    change f.toLp 2 (volume : Measure V) = 0 at hJ
    rw [hJ] at he
    exact congrFun ((f.continuous.ae_eq_iff_eq _ continuous_const).mp
      (he.symm.trans (Lp.coeFn_zero ..)))
  · intro i
    obtain ⟨C, k, hC, h⟩ := hg _ ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i)
    refine ⟨C * 2 ^ k, k, fun n ↦ (h n).trans ?_⟩
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (latticeWeight_bounds n).2.2 k) hC
  · intro j f
    obtain ⟨p, _, h⟩ := hd j
    refine ⟨p f, fun n ↦ ?_⟩
    rw [hc, mul_comm]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (latticeWeight_bounds n).1) (latticeWeight_bounds n).2.1 j) (norm_nonneg _)).trans (h n f)

/-- Paper: Remark 4.2.2.6, p. 174. The kernel of periodization of ordinary
Schwartz functions is topologically and linearly isomorphic to the source. -/
theorem cyclicSchwartzPeriodization_ker_equiv :
    Nonempty ((cyclicSchwartzPeriodization γ hγ).ker ≃L[ℂ] 𝓢(ℝ, ℂ)) := by
  let L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  let P := cyclicSchwartzPeriodization γ hγ
  let A := ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) - SchwartzMap.compSubConstCLM ℂ (-L)
  have hA (f : 𝓢(ℝ, ℂ)) (x : ℝ) : A f x = f x - f (x + L) := by
    change f x - f (x - -L) = _
    rw [sub_neg_eq_add]
  let D := A.codRestrict P.ker (fun f ↦ by
    apply cyclic_eq_zero_of_lifts hL.ne'
    intro x
    apply (cyclicSchwartzPeriodization_hasSum γ hγ (A f) x).unique
    simpa only [hA] using orbitDifference_hasSum (cyclicSchwartzPeriodization_hasSum γ hγ f x))
  have hsur : Surjective D := by
    intro f
    have horb (x : ℝ) : HasSum (fun n : ℤ ↦ f.val (x + n * L)) 0 := by
      have hs := cyclicSchwartzPeriodization_hasSum γ hγ f.val x
      change HasSum _ (P f.val _) at hs
      rw [show P f.val = 0 from f.property] at hs
      exact hs
    obtain ⟨g, _, hg⟩ := schwartzOrbitPrimitive L hL f.val horb
    exact ⟨g, Subtype.ext (SchwartzMap.ext fun x ↦ (hA g x).trans (hg x).symm)⟩
  have hinj : Injective D := by
    suffices hz : ∀ f, D f = 0 → f = 0 by
      intro f g h
      exact sub_eq_zero.mp (hz _ (by rw [map_sub, h, sub_self]))
    intro f hf
    have he (x : ℝ) : f x = f (x + L) := sub_eq_zero.mp ((hA f x).symm.trans
      (congrArg (fun v : P.ker ↦ v.val x) hf))
    apply SchwartzMap.ext
    intro x
    have hper (n : ℕ) : f (x + n * L) = f x := by
      induction n with
      | zero => simp
      | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, ← he, ih]
    have hs := (cyclicSchwartzPeriodization_hasSum γ hγ f x).summable.comp_injective Nat.cast_injective
    change Summable (fun n : ℕ ↦ f (x + (n : ℤ) * L)) at hs
    change f x = 0
    simpa only [Int.cast_natCast, hper, summable_const_iff] using hs
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let : PolynormableSpace ℂ 𝓢(ℝ, ℂ) := (schwartz_withSeminorms ℂ ℝ ℂ).toPolynormableSpace
  let : MetrizableSpace 𝓢(ℝ, ℂ) := UniformSpace.metrizableSpace
  let : T2Space S := elementarySchwartz_t2
  have : CompleteSpace P.ker := P.isClosed_ker.completeSpace_coe
  have hsrc : IsFrechetTVS 𝓢(ℝ, ℂ) := ⟨inferInstance, inferInstance, inferInstance,
    by rw [IsUniformAddGroup.rightUniformSpace_eq]; infer_instance⟩
  let : IsUniformAddGroup P.ker := P.ker.toAddSubgroup.isUniformAddGroup
  have htgt : IsFrechetTVS P.ker := ⟨inferInstance, inferInstance, MetrizableSpace.subtype _,
    by rw [IsUniformAddGroup.rightUniformSpace_eq]; infer_instance⟩
  let e := LinearEquiv.ofBijective D.toLinearMap ⟨hinj, hsur⟩
  have hop : IsOpenMap D := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS htgt)
    (X := fun _ ↦ 𝓢(ℝ, ℂ)) (fun _ ↦ hsrc) (fun _ ↦ ContinuousLinearMap.id ℂ _)
    (fun _ ↦ Subset.rfl) (fun f ↦ ⟨0, f, rfl⟩) D hsur
  let d : 𝓢(ℝ, ℂ) ≃L[ℂ] P.ker :=
    { e with continuous_toFun := D.continuous, continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }
  exact ⟨d.symm⟩

/-- Restrict a sequence to an injective subsequence that controls the original weight. -/
private def rapidSubsequence (i : ℕ → ℕ) (hi : Injective i)
    (hw : ∀ n, latticeWeight n ≤ 2 * latticeWeight (i n)) :
    RapidDecaySequence 1 →L[ℂ] RapidDecaySequence 1 := by
  let v (a : RapidDecaySequence 1) (m : Fin 1 → ℤ) := a (latticeIndex (i (latticeIndex.symm m)))
  let term (a : RapidDecaySequence 1) (j n : ℕ) := latticeWeight n ^ j * ‖a (latticeIndex n)‖
  have hs (a : RapidDecaySequence 1) (j : ℕ) : Summable (term a j) :=
    (rapidSequence_mem_iff a.val).mp a.property j
  have hb (a : RapidDecaySequence 1) (j n : ℕ) :
      latticeWeight n ^ j * ‖v a (latticeIndex n)‖ ≤ 2 ^ j * term a j (i n) := by
    simp only [v, latticeIndex.symm_apply_apply, term, ← mul_assoc, ← mul_pow]
    gcongr
    · exact zero_le_one.trans (latticeWeight_bounds n).1
    · exact hw n
  have hv (a : RapidDecaySequence 1) : v a ∈ rapidDecaySequenceSubmodule 1 :=
    (rapidSequence_mem_iff _).2 fun j ↦ (((hs a j).comp_injective hi).mul_left (2 ^ j)).of_nonneg_of_le
      (fun n ↦ mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _) (norm_nonneg _)) (hb a j)
  let A : RapidDecaySequence 1 →ₗ[ℂ] RapidDecaySequence 1 :=
    { toFun a := ⟨v a, hv a⟩, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let p (j : ℕ) : Seminorm ℂ (RapidDecaySequence 1) := rapidDecaySequenceSeminorm j
  have hp : WithSeminorms p := rapidDecaySequence_withSeminorms
  refine ⟨A, hp.continuous_of_continuous_comp A fun j ↦ ?_⟩
  apply Seminorm.continuous_of_le (q := (2 ^ j : NNReal) • p j) ((hp.continuous_seminorm j).const_smul _)
  intro a
  change rapidDecaySequenceSeminorm j (A a) ≤ (2 ^ j : ℝ) * rapidDecaySequenceSeminorm j a
  rw [rapidSeminorm_eq, rapidSeminorm_eq]
  refine (((rapidSequence_mem_iff _).mp (hv a) j).tsum_le_tsum (hb a j)
    (((hs a j).comp_injective hi).mul_left _)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj (hs a j)
    (fun n ↦ mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds n).1) _) (norm_nonneg _)) hi)
    (by positivity)

/-- Paper: Remark 4.2.2.6, p. 174. The product of two rapid-decay sequence
spaces is topologically and linearly isomorphic to one such space. -/
theorem rapidDecaySequence_prod_equiv :
    Nonempty ((RapidDecaySequence 1 × RapidDecaySequence 1) ≃L[ℂ] RapidDecaySequence 1) := by
  let R := RapidDecaySequence 1
  let pick (d : ℕ) := rapidSubsequence (fun n ↦ 2 * n + d) (fun x y h ↦ by change 2 * x + d = 2 * y + d at h; omega) fun n ↦ by
    have h := (latticeWeight_bounds (2 * n + d)).2.2
    push_cast at h
    linarith [(latticeWeight_bounds n).2.1, Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) d]
  let A := (pick 0).prod (pick 1)
  have hap (a : R) (d n : ℕ) : pick d a (latticeIndex n) = a (latticeIndex (2 * n + d)) := by
    change a (latticeIndex (2 * latticeIndex.symm (latticeIndex n) + d)) = _
    rw [latticeIndex.symm_apply_apply]
  have hinj : Injective A := by
    intro a b h
    apply Subtype.ext
    funext i
    obtain ⟨n, rfl⟩ := latticeIndex.surjective i
    by_cases hn : n%2 = 0
    · have hh := congrArg (fun z : R × R ↦ z.1 (latticeIndex (n/2))) h
      change pick 0 a (latticeIndex (n/2)) = pick 0 b (latticeIndex (n/2)) at hh
      simpa only [hap, show 2 * (n/2) + 0 = n by omega] using hh
    · have hh := congrArg (fun z : R × R ↦ z.2 (latticeIndex (n/2))) h
      change pick 1 a (latticeIndex (n/2)) = pick 1 b (latticeIndex (n/2)) at hh
      simpa only [hap, show 2 * (n/2) + 1 = n by omega] using hh
  have hsurj : Surjective A := by
    rintro ⟨a, b⟩
    let u (n : ℕ) := if n%2 = 0 then a (latticeIndex (n/2)) else b (latticeIndex (n/2))
    let v (i : Fin 1 → ℤ) := u (latticeIndex.symm i)
    have hv (n : ℕ) : v (latticeIndex n) = u n := by simp [v]
    have he (n : ℕ) : u (2 * n) = a (latticeIndex n) := by simp [u]
    have ho (n : ℕ) : u (2 * n + 1) = b (latticeIndex n) := by simp [u, Nat.add_div]
    have hsub (c : R) (d : ℕ) (hd : d ≤ 1) (j : ℕ) :
        Summable (fun n ↦ latticeWeight (2 * n + d) ^ j * ‖c (latticeIndex n)‖) := by
      apply (((rapidSequence_mem_iff c.val).mp c.property j).mul_left (4 ^ j)).of_nonneg_of_le
        (fun n ↦ mul_nonneg (pow_nonneg (zero_le_one.trans (latticeWeight_bounds _).1) _) (norm_nonneg _))
      intro n
      rw [← mul_assoc, ← mul_pow]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply pow_le_pow_left₀ (zero_le_one.trans (latticeWeight_bounds _).1)
      have h := (latticeWeight_bounds (2 * n + d)).2.1
      push_cast at h
      linarith [(latticeWeight_bounds n).2.2, (show (d : ℝ) ≤ 1 by exact_mod_cast hd)]
    have hmem : v ∈ rapidDecaySequenceSubmodule 1 := by
      apply (rapidSequence_mem_iff _).2
      intro j
      simp only [hv]
      apply Summable.even_add_odd
      · simpa only [Nat.add_zero, he] using hsub a 0 (by decide) j
      · simpa only [ho] using hsub b 1 (by decide) j
    let s : R := ⟨v, hmem⟩
    refine ⟨s, Prod.ext (Subtype.ext (funext fun i ↦ ?_)) (Subtype.ext (funext fun i ↦ ?_))⟩
    · obtain ⟨n, rfl⟩ := latticeIndex.surjective i
      exact (hap s 0 n).trans ((hv _).trans (by simpa only [Nat.add_zero] using he n))
    · obtain ⟨n, rfl⟩ := latticeIndex.surjective i
      exact (hap s 1 n).trans ((hv _).trans (ho n))
  obtain ⟨_, _, hm, hc⟩ := (rapidDecaySequence_isFrechet (r := 1))
  let : CompleteSpace R := by rwa [IsUniformAddGroup.rightUniformSpace_eq] at hc
  have hprod : IsFrechetTVS (R × R) := by
    refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
    rw [IsUniformAddGroup.rightUniformSpace_eq]
    infer_instance
  have hop : IsOpenMap A := isOpenMap_of_surjective_toLF (isLFSpace_of_isFrechetTVS hprod)
    (X := fun _ ↦ R) (fun _ ↦ rapidDecaySequence_isFrechet) (fun _ ↦ ContinuousLinearMap.id ℂ R)
    (fun _ ↦ Subset.rfl) (fun a ↦ ⟨0, a, rfl⟩) A hsurj
  let e := LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩
  let d : R ≃L[ℂ] R × R :=
    { e with continuous_toFun := A.continuous, continuous_invFun := e.toEquiv.continuous_symm_iff.mpr hop }
  exact ⟨d.symm⟩

end CompactSupport

end RiemannMasullo
