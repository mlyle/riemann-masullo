module
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Bounded
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Montel

/-!
# Periodic Schauder bases in the absence of multiplicity

Masullo, §4.5, pp. 197–209. We use the left translation and Haar measure
conventions of §4.4.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G)
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)

local notation "K" => m.toMonoidHom.ker
local notation "Γ" => Subgroup.zpowers γ
local notation "Q" => G ⧸ Γ
local notation "S" => SchwartzBruhat Q
local notation "E" => ModulatedExponentialDecay m (Set.univ : Set ℝ)
local notation "L" => Real.log ((m γ).val : ℝ)

local notation "zeroUniv" => (⟨(0 : ℝ), Set.mem_univ _⟩ : (Set.univ : Set ℝ))
local notation "twist₀" => modulatedExponentialDecayTwist m Set.univ zeroUniv
local notation "ρG" => schwartzBruhatTranslationAction (G := G)
local notation "ρQ" =>
  (letI : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
   schwartzBruhatTranslationAction (G := Q))
local notation "q" => QuotientGroup.mk' Γ

local instance instMeasurableSpaceCyclicQuotientSec5 : MeasurableSpace Q := borel _
local notation "H[" ω "]" =>
  (show Submodule ℂ E from (actionIsotype ((ρG).comp (K).subtype) ω).comap twist₀)

/-! ## 4.5.1 Periodization and its isotypic quotients -/

section Periodization

local notation "per" => modulatedPeriodization m γ hm hms hγ

include hm hms in
private theorem modulation_surjective_exists_section :
    ∃ τ : ℝ≥0ˣ →ₜ* G, RightInverse τ m := by
  refine hm.exists_section.elim fun s hs ↦ ?_
  exact ⟨s.comp ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ MonoidHom.mem_range.mpr (hms t),
    continuous_id.subtype_mk _⟩, fun t ↦ hs _⟩

private theorem cyclicCosetIntegral_hasSum [MeasurableSpace G] [BorelSpace G]
    [(Measure.count : Measure Γ).IsHaarMeasure] [(Measure.count : Measure Γ).Regular]
    (f : SchwartzBruhat G) (x : G) :
    HasSum (fun n : ℤ ↦ f (γ ^ n * x)) (schwartzBruhatCosetIntegral Γ Measure.count
      (modulatedCyclicSubgroup_closed m γ hγ) f (QuotientGroup.mk x)) := by
  let hΓ := modulatedCyclicSubgroup_closed m γ hγ
  let g : Γ → ℂ := fun z ↦ f (x * z.val)
  have hg := (lcaCosetIntegral_mem_schwartzBruhat Γ Measure.count hΓ f).1 x
  have hs : HasSum g (∫ z, g z ∂Measure.count) := by
    simpa [integral_countable hg, g] using (integrable_count_iff.mp hg).of_norm.hasSum
  let p : ℤ → Γ := fun n ↦ ⟨γ ^ n, Subgroup.zpow_mem_zpowers γ n⟩
  have hp : Injective p := by
    intro i j hij
    apply (zpow_right_injective₀ (Units.zero_lt (m γ)) hγ.ne')
    simpa only [p, map_zpow, Units.val_zpow_eq_zpow_val] using
      congrArg (fun z : Γ ↦ (m z.val).val) hij
  let e := Equiv.ofBijective p ⟨hp, fun ⟨z, n, hn⟩ ↦ ⟨n, Subtype.ext hn⟩⟩
  rw [schwartzBruhatCosetIntegral_mk]
  have ht : HasSum (fun n : ℤ ↦ f (x * γ ^ n)) (∫ z, g z ∂Measure.count) := e.hasSum_iff.mpr hs
  simpa only [g, mul_comm x] using ht

include hSC in
/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. The orbit sum of §4.4 is linear
and continuous for the two Schwartz–Bruhat topologies. -/
theorem modulatedPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ per ∧ Continuous per := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  refine (modulatedExponentialDecay_continuous_inclusion m univ hm ordConnected_univ univ_nonempty
    τ hτ (mem_univ 0)).elim fun j hj ↦ ?_
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count
    (modulatedCyclicSubgroup_closed m γ hγ)).elim fun A hA ↦ ?_
  have h (f : E) : A (j f) = per f := by
    refine (hA (j f)).trans (Subtype.ext (funext fun z ↦ ?_))
    refine QuotientGroup.induction_on z (fun x ↦ ?_)
    exact ((cyclicCosetIntegral_hasSum m γ hγ (j f) x).congr_fun
      (fun n ↦ (hj.2 f (γ ^ n * x)).symm)).unique (modulatedPeriodization_hasSum m γ hm hms hγ f x)
  exact Eq.mp (congrArg (fun F : E → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext h))
    ⟨(A.comp j).toLinearMap.isLinear, (A.comp j).continuous⟩

/-- Paper: Equation (4.5.1.1), p. 197. Ordinary periodization is the bundled
continuous linear map given by the orbit sum of §4.4. -/
def modulatedPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedPeriodization_isLinearMap_continuous m γ hm hms hγ
  ⟨IsLinearMap.mk' per h.1, h.2⟩

local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

-- Equation (4.5.1.2) at each lift is modulatedPeriodization_hasSum in §4.4.

omit hSC in
private theorem schwartzBruhat_norm_bounded (f : SchwartzBruhat G) : ∃ d : ℝ, ∀ x, ‖f x‖ ≤ d := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff _).mp f.property
  refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s, fun x ↦ ?_⟩
  rw [← show schwartzBruhatStageRealization a e s x = f x from congrFun hs x,
    schwartzBruhatStageRealization_apply]
  split_ifs
  · change (‖s _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val _).toReal
    apply ENNReal.toReal_mono (s.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖s y‖₊ : ENNReal)) _
  · exact norm_zero.trans_le (apply_nonneg _ _)

omit hSC in
include hγ in
private theorem exists_orbit_majorant (f : E) (C : Set G) (hC : IsCompact C) :
    ∃ d : ℤ → ℝ, Summable d ∧ ∀ n x, x ∈ C → ‖f.val (γ ^ n * x)‖ ≤ d n := by
  let w (x : G) : ℝ := (m x).val
  have hw (x : G) : 0 < w x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hwc : Continuous w := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  obtain ⟨a, ha⟩ := schwartzBruhat_norm_bounded (modulatedExponentialDecayTwist m univ ⟨1, mem_univ _⟩ f)
  obtain ⟨b, hb⟩ := schwartzBruhat_norm_bounded (modulatedExponentialDecayTwist m univ ⟨-1, mem_univ _⟩ f)
  have h₁ (y : G) : ‖f.val y‖ ≤ a * (w y)⁻¹ := by
    have h : ‖(((w y ^ (1 : ℝ)) : ℝ) : ℂ) * f.val y‖ ≤ a := ha y
    rw [Real.rpow_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw y).le] at h
    exact (le_div_iff₀ (hw y)).mpr ((mul_comm _ _).trans_le h) |>.trans_eq (div_eq_mul_inv _ _)
  have h₂ (y : G) : ‖f.val y‖ ≤ b * w y := by
    have h : ‖(((w y ^ (-1 : ℝ)) : ℝ) : ℂ) * f.val y‖ ≤ b := hb y
    rw [Real.rpow_neg_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (hw y).le)] at h
    exact ((inv_mul_le_iff₀ (hw y)).mp h).trans_eq (mul_comm _ _)
  obtain ⟨A, hA⟩ := (hC.image (continuous_const (y := a) |>.mul (hwc.inv₀ fun x ↦ (hw x).ne'))).bddAbove
  obtain ⟨B, hB⟩ := (hC.image (continuous_const (y := b) |>.mul hwc)).bddAbove
  let d : ℤ → ℝ
    | .ofNat n => A * (w γ)⁻¹ ^ n
    | .negSucc n => B * (w γ)⁻¹ ^ (n + 1)
  have hg : Summable fun n : ℕ ↦ (w γ)⁻¹ ^ n :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (hw γ).le) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hγ))
  have hmul (n : ℤ) (x : G) : w (γ ^ n * x) = w γ ^ n * w x := by
    simp only [w, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul, NNReal.coe_zpow]
  refine ⟨d, .of_nat_of_neg_add_one (hg.mul_left A) (((summable_nat_add_iff 1).mpr hg).mul_left B), ?_⟩
  intro n x hx
  cases n with
  | ofNat n =>
    calc
      _ ≤ a * (w (γ ^ (n : ℤ) * x))⁻¹ := h₁ _
      _ = (a * (w x)⁻¹) * (w γ)⁻¹ ^ n := by rw [hmul, mul_inv_rev, zpow_natCast, inv_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hA (mem_image_of_mem _ hx)) (pow_nonneg (inv_nonneg.mpr (hw γ).le) n)
  | negSucc n =>
    calc
      _ ≤ b * w (γ ^ (Int.negSucc n) * x) := h₂ _
      _ = (b * w x) * (w γ)⁻¹ ^ (n + 1) := by
        rw [hmul]
        change b * (w γ ^ (-(↑(n + 1) : ℤ)) * w x) = _
        rw [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ ≤ B * (w γ)⁻¹ ^ (n + 1) := mul_le_mul_of_nonneg_right
        (show b * w x ≤ B from hB ⟨x, hx, rfl⟩) (pow_nonneg (inv_nonneg.mpr (hw γ).le) (n + 1))

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. The ordinary orbit sums converge
uniformly on compact sets of representatives in the original group.
Deviation: Finite partial sums need representatives because they are generally
functions on G only. -/
theorem modulatedPeriodization_tendstoUniformlyOn (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, f.val (γ ^ n * x))
      (fun x ↦ P f (q x)) atTop C := by
  have hsum (x : G) : (∑' n : ℤ, f.val (γ ^ n * x)) = P f (q x) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f x).tsum_eq
  refine (exists_orbit_majorant m γ hγ f C hC).elim fun d h ↦ ?_
  have hd := h.1
  have hf := h.2
  have hu := tendstoUniformlyOn_tsum (f := fun (n : ℤ) x ↦ f.val (γ ^ n * x)) hd hf
  exact hu.congr_right (fun {_} _ ↦ hsum _)

private theorem bruhatOrbit_hasDerivAt (α : LCATopologicalLie G) (g : G → ℂ)
    (hg : IsBruhatContDiff 1 g) (z : G) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ g (z * α (Multiplicative.ofAdd s)))
      (bruhatDirectionalDeriv α g (z * α (Multiplicative.ofAdd t))) t := by
  have h := hasDerivAt_bruhatDirectionalDeriv α hg (z * α (Multiplicative.ofAdd t))
  have hshift := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)
  apply hshift.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)
  change g (z * α (Multiplicative.ofAdd s)) = g (z * α (Multiplicative.ofAdd t) * α (Multiplicative.ofAdd (s - t)))
  rw [mul_assoc, ← map_mul]
  change g (z * α (Multiplicative.ofAdd s)) = g (z * α (Multiplicative.ofAdd (t + (s - t))))
  rw [add_sub_cancel]

include hm hms in
private theorem modulated_directionalDerivative_mem (α : LCATopologicalLie G) (f : E) :
    bruhatDirectionalDeriv α f.val ∈ modulatedExponentialDecaySubmodule m univ :=
  modulatedExponentialDecay_invariantDiff m univ hm hms ordConnected_univ univ_nonempty
    (bruhatDiffGenerator α) f

private theorem periodization_directionalDerivative (α : LCATopologicalLie G) (f : E) :
    let df : E := ⟨bruhatDirectionalDeriv α f.val, modulated_directionalDerivative_mem m hm hms α f⟩
    bruhatDirectionalDeriv α (fun x ↦ P f (q x)) = fun x ↦ P df (q x) := by
  intro df
  funext x
  let path (t : ℝ) := x * α (Multiplicative.ofAdd t)
  have hc : Continuous path := continuous_const.mul (α.continuous.comp continuous_id)
  have hzero : path 0 = x := by simp [path]
  let g (n : ℤ) (t : ℝ) := f.val (γ ^ n * path t)
  let dg (n : ℤ) (t : ℝ) := df.val (γ ^ n * path t)
  have hdiff (n : ℤ) (t : ℝ) : HasDerivAt (g n) (dg n t) t := by
    have hs := (mem_bruhatSmoothSubmodule_iff f.val).mp
      (modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty f) 1
    simpa only [g, dg, path, df, mul_assoc] using bruhatOrbit_hasDerivAt α f.val hs (γ ^ n * x) t
  refine (exists_orbit_majorant m γ hγ df _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image hc)).elim fun d h ↦ ?_
  have hy : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hsum (t : ℝ) := modulatedPeriodization_hasSum m γ hm hms hγ f (path t)
  have H := hasDerivAt_tsum_of_isPreconnected (g := g) (g' := dg) h.1 isOpen_Ioo isPreconnected_Ioo
    (fun n t _ ↦ hdiff n t) (fun n t ht ↦ h.2 n _ ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
    hy (hsum 0).summable hy
  have hd := (modulatedPeriodization_hasSum m γ hm hms hγ df (path 0)).tsum_eq
  have hp : (fun t : ℝ ↦ ∑' n, g n t) = fun t ↦ P f (q (path t)) := funext fun t ↦ (hsum t).tsum_eq
  exact (congrArg (fun v : ℝ → ℂ ↦ deriv v 0) hp).symm.trans
    (H.deriv.trans (hd.trans (congrArg (fun y ↦ P df (q y)) hzero)))

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. On compact sets of lifts,
each iterated directional derivative of the orbit sum is the locally uniform
sum of the corresponding derivatives of the translates. -/
theorem modulatedPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, d f.val (γ ^ n * x))
      (d (fun x ↦ P f (q x))) atTop C := by
  intro d
  let D (g : E) : E :=
    ⟨bruhatDirectionalDeriv α g.val, modulated_directionalDerivative_mem m hm hms α g⟩
  let v (g : E) := g.val
  let p (g : E) := fun x ↦ P g (q x)
  have hv : Semiconj v D (bruhatDirectionalDeriv α) := fun _ ↦ rfl
  have hp : Semiconj p D (bruhatDirectionalDeriv α) := fun g ↦
    (periodization_directionalDerivative m γ hm hms hγ α g).symm
  let U (F H : G → ℂ) := TendstoUniformlyOn
    (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, F (γ ^ n * x)) H atTop C
  exact Eq.mp (congrArg₂ U (hv.iterate_right r f) (hp.iterate_right r f))
    (modulatedPeriodization_tendstoUniformlyOn m γ hm hms hγ (D^[r] f) C hC)

/-- Bruhat differentiability of a fixed order is preserved by products. -/
private theorem modulatedPeriodization_surjective_mul {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] {p : ℕ} {f g : A → ℂ}
    (hf : IsBruhatContDiff p f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (f * g) := by
  obtain ⟨k, hk, hfk, hfd⟩ := hf
  obtain ⟨l, hl, hgl, hgd⟩ := hg
  refine ⟨k ⊓ l, isBruhatGoodSubgroup_inf hk hl, ?_, ?_⟩
  · intro h x
    exact congrArg₂ (· * ·) (hfk ⟨h, h.property.1⟩ x) (hgl ⟨h, h.property.2⟩ x)
  · intro a ha
    obtain ⟨f₀, hf₀, hfSmooth⟩ := bruhatContDiff_descend_of_le hk hfd a (ha ▸ inf_le_left)
    obtain ⟨g₀, hg₀, hgSmooth⟩ := bruhatContDiff_descend_of_le hl hgd a (ha ▸ inf_le_right)
    exact ⟨f₀ * g₀, fun x ↦ congrArg₂ (· * ·) (hf₀ x) (hg₀ x),
      fun e z d ↦ (hfSmooth e z d).mul (hgSmooth e z d)⟩

/-- Bruhat differentiability pulls back along the quotient map by a closed subgroup. -/
private theorem modulatedPeriodization_surjective_comp_mk {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] (N : Subgroup A) [hN : IsClosed (N : Set A)]
    {p : ℕ} {φ : A ⧸ N → ℂ} (hφ : IsBruhatContDiff p φ) :
    IsBruhatContDiff p (fun x ↦ φ (QuotientGroup.mk x)) := by
  obtain ⟨kQ, hkQ, hinv, hdesc⟩ := hφ
  have hkc := isCompact_lcaDualAnnihilator (lcaAnnihilator kQ) hkQ.2.1
  rw [lcaDualAnnihilator_annihilator kQ hkQ.1] at hkc
  obtain ⟨J, hkJ⟩ := exists_openCompactlyGeneratedSubgroup_contains hkc
  let bQ : BruhatStructuralPair (A ⧸ N) :=
    ⟨(J.val, OrderDual.toDual kQ), J.property.1, J.property.2, hkQ, hkJ⟩
  obtain ⟨k, hk, hkmap⟩ := exists_good_subgroup_image_in_kernel
    (⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩ : A →ₜ* A ⧸ N) bQ
  have hmem (h : k) : (QuotientGroup.mk h.val : A ⧸ N) ∈ kQ := hkmap ⟨h.val, h.property, rfl⟩
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · change φ (QuotientGroup.mk (h.val * x)) = φ (QuotientGroup.mk x)
    rw [QuotientGroup.mk_mul]
    exact hinv ⟨_, hmem h⟩ _
  obtain ⟨a', ha'1, ha'2⟩ := bruhatStructuralPair_quotient_map N hN a
  have hle : OrderDual.ofDual a'.val.2 ≤ kQ := by
    rw [ha'2, ha]
    exact hkmap
  obtain ⟨φ₀, hφ₀, hsm⟩ := bruhatContDiff_descend_of_le hkQ hdesc a' hle
  obtain ⟨pq, hpc, -, -, -, hpmk⟩ := a.exists_quotient_hom N a' ha'1 ha'2
  refine ⟨φ₀ ∘ pq, fun x ↦ ?_, fun e z d ↦ ?_⟩
  · have hq : (QuotientGroup.mk x.val : A ⧸ N) ∈ a'.val.1 := by
      rw [ha'1]
      exact ⟨x.val, x.property, rfl⟩
    change φ₀ (pq (QuotientGroup.mk ⟨x.val, x.property⟩)) = _
    rw [hpmk x.val x.property hq]
    exact hφ₀ ⟨_, hq⟩
  · let e' := Classical.choice a'.elementary
    let Lh := AddMonoidHom.toMultiplicative.symm
      (e'.equiv.toMulEquiv.toMonoidHom.comp (pq.comp e.equiv.symm.toMulEquiv.toMonoidHom))
    have hL : Continuous Lh := e'.equiv.continuous.comp (hpc.comp e.equiv.symm.continuous)
    have hs := contDiff_comp_elementaryHom Lh hL
      (f := fun y ↦ φ₀ (e'.equiv.symm (Multiplicative.ofAdd y))) (hsm e') z d
    convert hs using 1
    funext u
    change φ₀ (pq (e.equiv.symm _)) = φ₀ (e'.equiv.symm (e'.equiv (pq (e.equiv.symm _))))
    rw [e'.equiv.symm_apply_apply]

/-- Compact subgroups lie in the kernel of the logarithm of the module. -/
private theorem modulatedPeriodization_surjective_log_compact {A : Type*} [CommGroup A]
    [TopologicalSpace A]
    (v : A →ₜ* ℝ≥0ˣ) {k : Subgroup A} (hk : IsCompact (k : Set A)) (h : A) (hh : h ∈ k) :
    Real.log ((v h).val : ℝ) = 0 := by
  have hpos (x : A) : 0 < ((v x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hcont : Continuous (fun x : A ↦ Real.log ((v x).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp v.continuous)).log fun x ↦ (hpos x).ne'
  obtain ⟨B, hB⟩ := (hk.image hcont).isBounded.exists_norm_le
  have hpow (n : ℕ) : (n : ℝ) * |Real.log ((v h).val : ℝ)| ≤ B := by
    have := hB _ ⟨h ^ n, k.pow_mem hh n, rfl⟩
    simp only at this
    rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow, Real.norm_eq_abs,
      abs_mul, Nat.abs_cast] at this
    exact this
  by_contra hne
  have hp : 0 < |Real.log ((v h).val : ℝ)| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (B / |Real.log ((v h).val : ℝ)|)
  have := (div_lt_iff₀ hp).mp hn
  linarith [hpow n]

/-- A smooth profile of the logarithm of the module is Bruhat smooth. -/
private theorem modulatedPeriodization_surjective_logProfile {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [T2Space A] [LocallyCompactSpace A] (v : A →ₜ* ℝ≥0ˣ) {ρ : ℝ → ℂ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (p : ℕ) :
    IsBruhatContDiff p (fun x ↦ ρ (Real.log ((v x).val : ℝ))) := by
  have hpos (x : A) : 0 < ((v x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let ℓ : A →* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (Real.log ((v x).val : ℝ))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos x).ne' (hpos y).ne']
        rfl }
  have hℓ : Continuous ℓ :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp v.continuous)).log fun x ↦ (hpos x).ne'
  obtain ⟨k, hk⟩ := exists_bruhatGoodSubgroup (G := A)
  have hkc := isCompact_of_bruhatGoodSubgroup k hk
  have hker (h : A) (hh : h ∈ k) : ℓ h = 1 :=
    congrArg Multiplicative.ofAdd (modulatedPeriodization_surjective_log_compact v hkc h hh)
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · have := congrArg Multiplicative.toAdd
      ((ℓ.map_mul h.val x).trans (by rw [hker _ h.property, one_mul]))
    exact congrArg ρ this
  let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
  let ℓ₀ : a.quotient →* Multiplicative ℝ :=
    QuotientGroup.lift N (ℓ.comp a.val.1.subtype) fun x hx ↦ hker x.val (ha ▸ hx)
  have hℓ₀ : Continuous ℓ₀ :=
    (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr (hℓ.comp continuous_subtype_val)
  refine ⟨fun y ↦ ρ (Multiplicative.toAdd (ℓ₀ y)), fun x ↦ rfl, fun e z d ↦ ?_⟩
  let χ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor →+ ℝ :=
    AddMonoidHom.toMultiplicative.symm (ℓ₀.comp e.equiv.symm.toMulEquiv.toMonoidHom)
  have hA : Continuous χ := hℓ₀.comp e.equiv.symm.continuous
  let c := elementaryCoverZeroHom (m := e.realDim) (n := e.torusDim) (r := e.latticeRank)
    (F := e.finiteFactor)
  let Lin := (χ.comp c).toRealLinearMap (hA.comp elementaryCoverZeroHom_continuous_isOpenMap.1)
  have hshift (u : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
      elementaryCover u z d = c u + elementaryCover 0 z d := by
    simp [c, elementaryCoverZeroHom, elementaryCover, Pi.zero_def]
  have hfun : (fun u ↦ ρ (Multiplicative.toAdd (ℓ₀ (e.equiv.symm (Multiplicative.ofAdd
      (elementaryCover u z d)))))) = fun u ↦ ρ (Lin u + χ (elementaryCover 0 z d)) := by
    funext u
    change ρ (χ (elementaryCover u z d)) = _
    rw [hshift, map_add]
    rfl
  rw [hfun]
  exact (hρ.of_le (WithTop.coe_le_coe.mpr le_top)).comp (Lin.contDiff.add contDiff_const)

include hγ in
/-- The product of a smooth profile of the logarithm of the module with the pullback
of a Schwartz–Bruhat function on the cyclic quotient is Bruhat smooth on G. This is
the smoothness of u₀ · (φ ∘ π) in the printed proof, for u₀ = ρ ∘ log |·|_G. -/
private theorem modulatedPeriodization_surjective_cutoff {ρ : ℝ → ℂ}
    (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (φ : S) :
    IsBruhatSmooth (fun x : G ↦ ρ (Real.log ((m x).val : ℝ)) * φ (q x)) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  intro p
  exact modulatedPeriodization_surjective_mul
    (modulatedPeriodization_surjective_logProfile m hρ p)
    (modulatedPeriodization_surjective_comp_mk Γ (schwartzBruhat_isBruhatSmooth φ p))

/-- A telescoping smooth profile: its translates by one period sum to one. -/
private theorem modulatedPeriodization_surjective_profile {T : ℝ} (hL : 0 < T) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      ∀ t, HasSum (fun n : ℤ ↦ ρ (t + n * T)) 1 := by
  let H (t : ℝ) := Real.smoothTransition (t / T)
  have H0 {t : ℝ} (ht : t ≤ 0) : H t = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hL.le)
  have H1 {t : ℝ} (ht : T ≤ t) : H t = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div hL).mpr ht)
  refine ⟨fun t ↦ H (t + T) - H t, ?_, ?_, fun t ↦ ?_⟩
  · have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H := Real.smoothTransition.contDiff.comp (contDiff_id.div_const T)
    exact (hH.comp (contDiff_id.add contDiff_const)).sub hH
  · refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht ↦ ?_
    rcases le_or_gt t T with h | h
    · have h' : t < -T := by
        by_contra h''
        exact ht ⟨not_lt.mp h'', h⟩
      simp only [H0 (show t + T ≤ 0 by linarith), H0 (show t ≤ 0 by linarith), sub_zero]
    · simp only [H1 (show T ≤ t + T by linarith), H1 h.le, sub_self]
  · let N : ℤ := ⌊-t / T⌋
    have hN : (N : ℝ) * T ≤ -t := (le_div_iff₀ hL).mp (Int.floor_le _)
    have hN' : -t < ((N : ℝ) + 1) * T := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one _)
    have hlow (n : ℤ) (hn : n ≤ N) : H (t + n * T) = 0 := H0 (by
      have : (n : ℝ) * T ≤ N * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hL.le
      linarith)
    have hhigh (n : ℤ) (hn : N + 2 ≤ n) : H (t + n * T) = 1 := H1 (by
      have : ((N : ℝ) + 2) * T ≤ n * T :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hL.le
      nlinarith)
    have hterm (n : ℤ) : H (t + n * T + T) - H (t + n * T) =
        H (t + ((n + 1 : ℤ) : ℝ) * T) - H (t + n * T) := by
      push_cast; ring_nf
    let g : ℤ → ℝ := fun n ↦ H (t + n * T + T) - H (t + n * T)
    have hs : HasSum g (∑ n ∈ ({N, N + 1} : Finset ℤ), g n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        change H _ - H _ = 0
        rw [hterm]
        rcases lt_or_gt_of_ne hn.1 with h | h
        · rw [hlow n h.le, hlow (n + 1) (by omega), sub_self]
        · rw [hhigh n (by omega), hhigh (n + 1) (by omega), sub_self])
    convert hs using 1
    simp only [g]
    rw [Finset.sum_pair (by omega), hterm, hterm]
    have e1 := hlow N le_rfl
    have e2 := hhigh (N + 1 + 1) (by omega)
    push_cast at e2 ⊢
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring] at e2 ⊢
    linarith

omit hSC in
include hm in
/-- A window in the logarithm of the module pulls back to a compact set. -/
private theorem modulatedPeriodization_surjective_window {C : Set ℝ} (hC : IsCompact C) :
    IsCompact {x : G | Real.log ((m x).val : ℝ) ∈ C} := by
  let e := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : (e t : ℝ) = Real.log ((t.val : ℝ≥0) : ℝ) := by
    exact Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t)) |>.symm
  have hc : IsCompact (e ⁻¹' C) := e.isProperMap.isCompact_preimage hC
  have : {x : G | Real.log ((m x).val : ℝ) ∈ C} = m ⁻¹' (e ⁻¹' C) := by
    ext x
    change Real.log _ ∈ C ↔ e (m x) ∈ C
    rw [he]
  rw [this]
  exact hm.1.isCompact_preimage hc

/-- Every test on the cyclic quotient lifts by multiplication with a fixed radial
cutoff supported in a compact window strictly below module one. -/
theorem modulatedPeriodization_compact_lift :
    ∃ (B : Set ℝ≥0ˣ) (c : ℝ≥0ˣ → ℂ), IsCompact B ∧ (∀ t ∈ B, t.val < 1) ∧
      (∀ t ∉ B, c t = 0) ∧ ∀ φ : S, ∃ f : E, P f = φ ∧
        ∀ x, f.val x = c (m x) * φ (q x) := by
  have hL : 0 < Real.log ((m γ).val : ℝ) := Real.log_pos (by exact_mod_cast hγ)
  obtain ⟨v, hv, hs, hsum⟩ := modulatedPeriodization_surjective_profile hL
  obtain ⟨R, hR⟩ := hs.isBounded.exists_norm_le
  let e := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let tr := Homeomorph.addRight (R + 1)
  let B := (e.trans tr) ⁻¹' tsupport v
  let ρ (s : ℝ) := v (s + (R + 1))
  have hρs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ := hv.comp (contDiff_id.add contDiff_const)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (tr.isCompact_preimage.mpr hs) fun t hx ↦
      (image_eq_zero_of_notMem_tsupport (f := v) (x := tr t) hx)
  have hρsum (t : ℝ) : HasSum (fun n : ℤ ↦ ρ (t + n * Real.log ((m γ).val : ℝ))) 1 :=
    (hsum (t + (R+1))).congr_fun fun n ↦ congrArg v (by ring)
  let ρc : ℝ → ℂ := fun t ↦ (ρ t : ℂ)
  have hρs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρc := Complex.ofRealCLM.contDiff.comp hρs
  have hcs : HasCompactSupport ρc := hρc.comp_left Complex.ofReal_zero
  refine ⟨B, fun t ↦ ρc (e t), (e.trans tr).isCompact_preimage.mpr hs, ?_, ?_, fun φ ↦ ?_⟩
  · intro t ht
    have h := (le_abs_self (e t + (R + 1))).trans (hR _ ht)
    have hlog : Real.log (t.val : ℝ) < 0 := by rw [← he]; linarith
    exact_mod_cast (Real.log_neg_iff (NNReal.coe_pos.mpr t.zero_lt)).mp hlog
  · intro t ht
    change ((v (e t + (R + 1)) : ℝ) : ℂ) = 0
    exact_mod_cast (image_eq_zero_of_notMem_tsupport (f := v) (x := e t + (R + 1)) ht)
  let f₀ : G → ℂ := fun x ↦ ρc (Real.log ((m x).val : ℝ)) * φ (q x)
  have hsupp : HasCompactSupport f₀ := by
    refine HasCompactSupport.intro (modulatedPeriodization_surjective_window m hm hcs) fun x hx ↦ ?_
    have h0 : ρc (Real.log ((m x).val : ℝ)) = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [f₀, h0, zero_mul]
  have hmem : f₀ ∈ bruhatCompactSupportSubmodule G :=
    ⟨(mem_bruhatSmoothSubmodule_iff f₀).mpr (modulatedPeriodization_surjective_cutoff m γ hγ hρs' φ), hsupp⟩
  let f : E := ⟨f₀, bruhatCompactSupport_le_modulatedExponentialDecay m univ hm hms hmem⟩
  refine ⟨f, Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z fun x ↦ ?_),
    fun x ↦ congrArg (fun z ↦ ρc z * φ (q x)) (he (m x)).symm⟩
  have hpos (u : ℝ≥0ˣ) : 0 < ((u.val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt u)
  have hℓ (n : ℤ) : Real.log ((m (γ ^ n * x)).val : ℝ) =
      Real.log ((m x).val : ℝ) + n * Real.log ((m γ).val : ℝ) := by
    rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos (m γ)).ne') (hpos (m x)).ne',
      Real.log_zpow]
    ring
  have hqx (n : ℤ) : q (γ ^ n * x) = q x := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ n), one_mul]
  have h2 : HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) (φ (q x)) := by
    have h := (Complex.hasSum_ofReal.mpr (hρsum (Real.log ((m x).val : ℝ)))).mul_right (φ (q x))
    rw [Complex.ofReal_one, one_mul] at h
    refine h.congr_fun fun n ↦ ?_
    change ρc _ * φ (q (γ ^ n * x)) = _
    rw [hℓ, hqx]
  exact (modulatedPeriodization_hasSum m γ hm hms hγ f x).unique h2

/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. Every Schwartz–Bruhat function
on the compact cyclic quotient is a periodization. -/
theorem modulatedPeriodization_surjective : Surjective P := by
  intro φ
  obtain ⟨_, _, _, _, _, hlift⟩ := modulatedPeriodization_compact_lift m γ hm hms hγ
  obtain ⟨f, hf, _⟩ := hlift φ
  exact ⟨f, hf⟩


-- TODO(paper-gap): Remarks 4.5.1.2 and 4.5.1.4 use arbitrary I for
-- periodization. For I = (1,2), a smooth log-profile equal to one near
-- minus infinity and zero near plus infinity has divergent orbit sums.

-- TODO(paper-gap): The continuity proof on pp. 199–200 assumes that a
-- convergent net in a locally convex space has a bounded tail.
-- The majorant on p. 199 also needs the supremum of the absolute values.
-- Remark 4.5.1.3 uses the tensor comparison of §D.3.3. For the valid
-- sequential assertion in Remarks 4.5.1.2 and 4.5.1.4 see the interval section.

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "perχ" => modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ

-- Proposition 4.5.1.1(2) is modulatedIsotypicPeriodization_mem in §4.4.

private theorem exists_schwartz_average {X Y : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] (μX : Measure X) [μX.IsHaarMeasure]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (π : X →ₜ* Y) (ω : PontryaginDual X) :
    ∃ A : (SchwartzBruhat Y) →L[ℂ] (SchwartzBruhat Y), ∀ (f : (SchwartzBruhat Y)) (z : Y), A f z = (μX.real univ : ℂ)⁻¹ *
      ∫ u : X, (ω u : ℂ) * f (π u * z) ∂μX := by
  let : LocallyConvexSpace ℝ (SchwartzBruhat Y) := (withGeneratingSeminorms_spec _ _).toLocallyConvexSpace
  let : T2Space (SchwartzBruhat Y) := schwartzBruhat_t2
  let : QuasiCompleteSpace ℂ (SchwartzBruhat Y) := schwartzBruhat_quasiComplete
  let ρ : X →* ((SchwartzBruhat Y) →L[ℂ] (SchwartzBruhat Y)) := (schwartzBruhatTranslationAction (G := Y)).comp π.toMonoidHom
  have hq : Continuous (π : X → Y) := π.continuous
  have hj : Continuous (fun p : X × (SchwartzBruhat Y) ↦ (π p.1, p.2)) := (hq.comp continuous_fst).prodMk continuous_snd
  have hTranslate := (schwartzBruhatTranslate_continuous (G := Y)).comp hj
  have hρ : Continuous (fun p : X × (SchwartzBruhat Y) ↦ ρ p.1 p.2) := hTranslate.congr fun p ↦
    ((Classical.choose_spec (existsUnique_schwartzBruhatTranslationAction (G := Y)).exists)
      (π p.1) p.2).symm
  have hseq {Z : Type _} [UniformSpace Z] (T : X → Z → Z)
      (hc : Continuous (fun p : X × Z ↦ T p.1 p.2)) (u : ℕ → Z) (v : Z) (hu : Tendsto u atTop (𝓝 v)) :
      TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
    intro U hU
    obtain ⟨W, hW, h⟩ := (isCompact_univ (X := X)).mem_uniformity_of_prod
      (f := fun f : Z ↦ fun k : X ↦ T k f) (s := univ) («q» := v)
      (hc.comp continuous_swap).continuousOn (mem_univ _) (symm_le_uniformity hU)
    rw [nhdsWithin_univ] at hW
    exact (hu.eventually hW).mono fun n hn k ↦ h (u n) hn k (mem_univ k)
  refine (existsUnique_compactActionIsotypicAverage μX ρ hρ schwartzBruhat_bornological (hseq (Z := SchwartzBruhat Y) (fun k f ↦ ρ k f) hρ) ω).exists.elim
    fun A hA ↦ ?_
  refine ⟨(μX.real univ : ℂ)⁻¹ • A, fun f z ↦ congrArg ((μX.real univ : ℂ)⁻¹ * ·) ?_⟩
  refine (schwartzBruhat_dirac_support z).elim fun δ hδ ↦ ?_
  have h := congrArg (fun v : PettisWeakCompletion (SchwartzBruhat Y) ↦
    (show Module.Dual ℂ (StrongDual ℂ (SchwartzBruhat Y)) from v) δ) (hA f).2
  change δ (A f) = ∫ k, δ (star (ω k : ℂ) • ρ k f) ∂μX.restrict univ at h
  let g (k : X) := (ω k : ℂ) * f (π k * z)
  have he (k : X) : δ (star (ω k : ℂ) • ρ k f) = g k⁻¹ := by
    have hw : star (ω k : ℂ) = (ω k⁻¹ : ℂ) := by rw [map_inv, Circle.coe_inv_eq_conj]; rfl
    have harg : ((π k)⁻¹ * z) = π k⁻¹ * z := congrArg (· * z) (π.map_inv k).symm
    calc
      δ (star (ω k : ℂ) • ρ k f) = star (ω k : ℂ) * δ (ρ k f) := δ.map_smul _ _
      _ = star (ω k : ℂ) * f ((π k)⁻¹ * z) := congrArg (star (ω k : ℂ) * ·)
        ((hδ.1 _).trans (schwartzBruhatTranslationAction_apply (π k) z f))
      _ = g k⁻¹ := congrArg₂ (· * ·) hw (congrArg (fun y ↦ f y) harg)
  have hint := integral_congr_ae (μ := μX) (ae_of_all μX he)
  have hi := integral_inv_eq_self g μX
  have h' : δ (A f) = ∫ k, δ (star (ω k : ℂ) • ρ k f) ∂μX := by
    simpa only [Measure.restrict_univ] using h
  exact (hδ.1 (A f)).symm.trans (h'.trans (hint.trans hi))

private theorem hasSum_integral_weighted_orbit (ω : PontryaginDual K) (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ ∫ u : K, (ω u : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let C := range (fun u : K ↦ u.val * x)
  have hC : IsCompact C := isCompact_range (continuous_subtype_val.mul continuous_const)
  have hc : Continuous f.val := (schwartzBruhat_continuous (twist₀ f)).congr fun y ↦
    congrFun (modulationWeight_zero m f.val) y
  let F (n : ℤ) (u : K) := (ω u : ℂ) * f.val (γ ^ n * (u.val * x))
  have hmeas (n : ℤ) : AEStronglyMeasurable (F n) μ₁ := ((continuous_subtype_val.comp (map_continuous ω)).mul
    (hc.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))).aestronglyMeasurable
  refine (exists_orbit_majorant m γ hγ f C hC).elim fun d hd ↦ ?_
  let result (u : K) := (ω u : ℂ) * P f (q (u.val * x))
  have hb (n : ℤ) : ∀ᵐ u ∂μ₁, ‖F n u‖ ≤ d n := .of_forall fun u ↦
    (norm_mul _ _).trans_le (by rw [Circle.norm_coe, one_mul]; exact hd.2 n _ ⟨u, rfl⟩)
  have hs (u : K) : HasSum (fun n ↦ F n u) (result u) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f (u.val * x)).mul_left (ω u : ℂ)
  exact hasSum_integral_of_dominated_convergence (F := F) (f := result) (μ := μ₁)
    (fun n _ ↦ d n) hmeas hb (.of_forall fun _ ↦ hd.1) (integrable_const _) (.of_forall hs)

private theorem exists_isotypic_periodization_factor :
    ∃ A : S →L[ℂ] S, (∀ f : E, perχ f = (μ₁.real univ : ℂ) • A (P f)) ∧
      ∀ f : E, A (perχ f) = perχ f := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let π : K →ₜ* Q := ⟨(q).comp (K).subtype, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  let ω := PontryaginDual.map (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_schwartz_average μ₁ π ω).elim fun A hA ↦ ⟨A, fun f ↦ ?_, fun f ↦ ?_⟩
  · refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ f x
    have hs := hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x
    have hi := ht.unique hs
    have he (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (π u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    change perχ f (q x) = M * (A (P f) (q x))
    exact hi.trans ((integral_congr_ae (ae_of_all μ₁ he)).trans
      ((mul_inv_cancel_left₀ hM _).symm.trans (congrArg (M * ·) (hA (P f) (q x)).symm)))
  · refine Subtype.ext (funext fun z ↦ ?_)
    have he (u : K) : (ω u : ℂ) * perχ f (π u * z) = perχ f z := by
      have ht := modulatedIsotypicPeriodization_homogeneous m γ hm hms hγ μ₁ χ f u (π u * z)
      have hi : QuotientGroup.mk u.val⁻¹ * (π u * z) = z :=
        (congrArg (· * (π u * z)) ((q).map_inv u.val)).trans (inv_mul_cancel_left (π u) z)
      exact ht.symm.trans (congrArg (fun y ↦ perχ f y) hi)
    have hi := integral_congr_ae (ae_of_all μ₁ he)
    have hc : (∫ _ : K, perχ f z ∂μ₁) = M * perχ f z := by
      rw [integral_const]
      exact Complex.real_smul
    exact (hA (perχ f) z).trans ((congrArg (M⁻¹ * ·) (hi.trans hc)).trans (inv_mul_cancel_left₀ hM _))

/-- Paper: Proposition 4.5.1.1(3), p. 198. The homogeneous orbit sum of §4.4
is linear and continuous. -/
theorem modulatedIsotypicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ perχ ∧ Continuous perχ := by
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  let B : E →L[ℂ] S := (μ₁.real univ : ℂ) • A.comp P
  have he : perχ = (B : E → S) := funext hA.1
  exact Eq.mpr (congrArg (fun F : E → S ↦ IsLinearMap ℂ F ∧ Continuous F) he)
    ⟨B.toLinearMap.isLinear, B.continuous⟩

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is the
bundled continuous linear map given by the character-weighted orbit sum. -/
def modulatedIsotypicPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedIsotypicPeriodization_isLinearMap_continuous m γ hm hms hγ μ₁ χ
  ⟨IsLinearMap.mk' perχ h.1, h.2⟩

local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- The pointwise sum in (2–3) is modulatedIsotypicPeriodization_hasSum in §4.4.

end Periodization

section FourierQuotientDefinitions

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

local notation "qK" => (q).comp (K).subtype
local notation "Sχ[" ω "]" => actionIsotype ((ρQ).comp qK) ω

-- TODO(paper-gap): In the proof on p. 201 the square of the unnormalized
-- quotient average is its Haar mass times the average itself.

include hm hγ in
/-- Paper: Notation 4.5.1.1, p. 204. The stated normalized compact average,
evaluated on the cyclic quotient, lands in the quotient Schwartz–Bruhat space. -/
theorem modulatedQuotientIsotypicProjector_mem (ω : PontryaginDual K) (f : S) :
    (fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁) ∈ schwartzBruhatSubmodule Q ∧
      ∀ z : Q, Integrable (fun u : K ↦ (ω u : ℂ) * f (qK u * z)) μ₁ := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  refine (exists_schwartz_average μ₁
    (⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩ : K →ₜ* Q) ω).elim fun A hA ↦ ?_
  refine ⟨Eq.mp (congrArg (· ∈ schwartzBruhatSubmodule Q) (funext (hA f))) (A f).property, fun z ↦ ?_⟩
  have hq : Continuous (qK : K → Q) := QuotientGroup.continuous_mk.comp continuous_subtype_val
  exact ((continuous_subtype_val.comp (map_continuous ω)).mul
    ((schwartzBruhat_continuous f).comp (hq.mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

local notation "avg[" ω "," f "]" => (⟨fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
  ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁,
  (modulatedQuotientIsotypicProjector_mem m γ hm hγ μ₁ ω f).1⟩ : S)

include hm hγ hSC in
/-- Paper: Notation 4.5.1.1, p. 204. The normalized compact average is linear
and continuous in the quotient test-function topology. -/
theorem modulatedQuotientIsotypicProjector_isLinearMap_continuous (ω : PontryaginDual K) :
    let A : S → S := fun f ↦ avg[ω, f]
    IsLinearMap ℂ A ∧ Continuous A := by
  intro B
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  refine (exists_schwartz_average μ₁
    (⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩ : K →ₜ* Q) ω).elim fun A hA ↦ ?_
  have h (f : S) : A f = B f := Subtype.ext (funext (hA f))
  exact Eq.mp (congrArg (fun F : S → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext h))
    ⟨A.toLinearMap.isLinear, A.continuous⟩

/-- Paper: Notation 4.5.1.1, p. 204. The quotient projector is the
character-weighted compact average divided by the mass of the norm-one group. -/
def modulatedQuotientIsotypicProjector (ω : PontryaginDual K) : S →L[ℂ] S :=
  let h := modulatedQuotientIsotypicProjector_isLinearMap_continuous m γ hm hγ μ₁ ω
  let T : S →ₗ[ℂ] S := IsLinearMap.mk' (fun f : S ↦ avg[ω, f]) h.1
  ⟨T, h.2⟩

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "volQ" => (L * μ₁.real univ : ℂ)

/-- Paper: Equation (4.5.1.12), p. 204. The quotient by the homogeneous
kernel maps to the test-function space by normalized homogeneous periodization.
Deviation: Normalizing recovers ordinary periodization on the isotypic representatives. -/
def modulatedIsotypicPeriodizationQuotient (ω : PontryaginDual K) : V[ω] →L[ℂ] S :=
  (μ₁.real univ : ℂ)⁻¹ • (Pχ[ω]).ker.liftQL (Pχ[ω]) le_rfl

local notation "T[" ω "]" => modulatedIsotypicPeriodizationQuotient m γ hm hms hγ μ₁ χ ω

/-- Paper: Equation (4.5.1.10), p. 204. The quotient functional multiplies the
Fourier coefficient of normalized periodization by the logarithmic period times
the kernel mass. For the compatible Weil measure this is the quotient volume. -/
def modulatedCyclicPairing (ω : PontryaginDual K) (n : ℤ) : StrongDual ℂ (V[ω]) :=
  volQ • (a (ω, n)).comp (T[ω])

end FourierQuotientDefinitions

section IsotypicPeriodizationProperties

local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

private theorem isOpenMap_to_quotient_of_strictLF {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (hX : IsStrictLFSpace X) (hY : IsStrictLFSpace Y)
    (C : Y →L[ℂ] Z) (hC : IsQuotientMap C) (F₀ : X →L[ℂ] Z) (hp : Surjective F₀) :
    IsOpenMap F₀ := by
  obtain ⟨hTX, U, hmono, hF, hc, _⟩ := hX
  let : T2Space X := hTX
  have hY' := (lfSpace_quotient_properties («E» := Y)).1 hY
  have hQ := (lfSpace_quotient_properties («E» := Y)).2 hY' C.ker C.isClosed_ker
  obtain ⟨e, _⟩ := exists_quotient_equiv_of_kernel C hC C.ker rfl
  let A := e.symm.toContinuousLinearMap.comp F₀
  have ho : IsOpenMap A := isOpenMap_of_surjective_toLF (X := fun k ↦ U k) hQ hF
    (fun k ↦ (U k).subtypeL)
    (fun k _ ⟨u, hu⟩ ↦ ⟨⟨u.val, hmono k.le_succ u.property⟩, hu⟩)
    (fun x ↦ (hc x).imp fun k hk ↦ ⟨⟨x, hk⟩, rfl⟩) A (e.symm.surjective.comp hp)
  have he : e ∘ A = F₀ := funext fun x ↦ e.apply_symm_apply _
  exact Eq.mp (congrArg IsOpenMap he) (e.isOpenMap.comp ho)

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization on the two-sided
exponentially decaying space is open. -/
theorem modulatedPeriodization_isOpenMap : IsOpenMap P := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  let Y := ModulatedExponentialDecay m ({0} : Set ℝ)
  have hX := modulatedExponentialDecay_strictLF m univ hm ordConnected_univ univ_nonempty τ hτ
  have hY := modulatedExponentialDecay_strictLF m ({0} : Set ℝ) hm (ordConnected_singleton) (singleton_nonempty _) τ hτ
  refine (modulatedExponentialDecay_singleton_schwartz m hm hms 0).elim fun e₀ _ ↦ ?_
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)).elim
    fun A hA ↦ ?_
  have hq : IsQuotientMap A := Eq.mpr (congrArg IsQuotientMap (funext hA))
    (schwartzBruhatCosetIntegral_isQuotientMap Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ))
  exact isOpenMap_to_quotient_of_strictLF (X := E) (Y := Y) (Z := S) hX hY
    (A.comp e₀.toContinuousLinearMap) (hq.comp e₀.toHomeomorph.isQuotientMap)
    P (modulatedPeriodization_surjective m γ hm hms hγ)

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–198.
The homogeneous orbit sums converge uniformly on compact sets of representatives.
Deviation: The finite sums are evaluated on G, where their summands are defined. -/
theorem modulatedIsotypicPeriodization_tendstoUniformlyOn
    (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun s : Finset ℤ ↦ fun x : G ↦
        ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (fun x ↦ Pχ f (q x)) atTop C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let C' := (fun p : K × G ↦ p.1.val * p.2) '' (univ ×ˢ C)
  have hC' : IsCompact C' := (isCompact_univ.prod hC).image
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
  have hsum (x : G) : (∑' n : ℤ, ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) =
      Pχ f (q x) := (modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ f x).tsum_eq
  refine (exists_orbit_majorant m γ hγ f C' hC').elim fun d h ↦ ?_
  have hd := h.1
  have hf := h.2
  have hb (n : ℤ) (x : G) (hx : x ∈ C) :
      ‖∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁‖ ≤ d n * μ₁.real univ := by
    apply norm_integral_le_of_norm_le_const
    exact .of_forall fun u ↦ (norm_mul _ _).trans_le (by
      rw [Circle.norm_coe, one_mul]
      exact hf n _ ⟨(u, x), ⟨mem_univ _, hx⟩, rfl⟩)
  have hu := tendstoUniformlyOn_tsum (f := fun (n : ℤ) (x : G) ↦
    ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) (hd.mul_right (μ₁.real univ)) hb
  exact hu.congr_right fun {_} _ ↦ hsum _

private theorem isotypicPeriodization_directionalDerivative (α : LCATopologicalLie G) (f : E) :
    let df : E := ⟨bruhatDirectionalDeriv α f.val, modulated_directionalDerivative_mem m hm hms α f⟩
    bruhatDirectionalDeriv α (fun x ↦ Pχ f (q x)) = fun x ↦ Pχ df (q x) := by
  intro df
  funext x
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let path (t : ℝ) := x * α (Multiplicative.ofAdd t)
  have hc : Continuous path := continuous_const.mul (α.continuous.comp continuous_id)
  have hzero : path 0 = x := by simp [path]
  let D (u : K × ℝ) := u.1.val * path u.2
  let C := D '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hC : IsCompact C := (isCompact_univ.prod isCompact_Icc).image
    ((continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd))
  refine (exists_orbit_majorant m γ hγ df C hC).elim fun b hb ↦ ?_
  let F (v : E) (n : ℤ) (t : ℝ) (u : K) := (χ u.val : ℂ) * v.val (γ ^ n * (u.val * path t))
  let g (v : E) (n : ℤ) (t : ℝ) := ∫ u, F v n t u ∂μ₁
  have hcont (v : E) (n : ℤ) (t : ℝ) : Continuous (F v n t) := by
    have hv : Continuous v.val := (schwartzBruhat_continuous (twist₀ v)).congr
      fun z ↦ congrFun (modulationWeight_zero m v.val) z
    exact ((continuous_subtype_val.comp χ.continuous).comp continuous_subtype_val).mul
      (hv.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))
  have hbound (n : ℤ) (u : K) (t : ℝ) (ht : t ∈ Ioo (-1) 1) : ‖F df n t u‖ ≤ b n :=
    (norm_mul _ _).trans_le (by rw [Circle.norm_coe, one_mul]
                                exact hb.2 n _ ⟨(u, t), ⟨mem_univ _, ht.1.le, ht.2.le⟩, rfl⟩)
  have hdiff (n : ℤ) (u : K) (t : ℝ) : HasDerivAt (fun s ↦ F f n s u) (F df n t u) t := by
    have hs := (mem_bruhatSmoothSubmodule_iff f.val).mp
      (modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty f) 1
    have ht := bruhatOrbit_hasDerivAt α f.val hs (γ ^ n * (u.val * x)) t
    simpa only [F, df, path, mul_assoc] using ht.const_mul (χ u.val : ℂ)
  have havg (n : ℤ) (t : ℝ) (ht : t ∈ Ioo (-1) 1) : HasDerivAt (g f n) (g df n t) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₁) (F := F f n) (F' := F df n)
      (bound := fun _ ↦ b n) (isOpen_Ioo.mem_nhds ht)
      (.of_forall fun s ↦ (hcont f n s).aestronglyMeasurable)
      ((hcont f n t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hcont df n t).aestronglyMeasurable (.of_forall (hbound n)) (integrable_const _)
      (.of_forall fun u s _ ↦ hdiff n u s)).2
  have hdom (n : ℤ) (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      ‖g df n t‖ ≤ b n * μ₁.real univ :=
    norm_integral_le_of_norm_le_const (.of_forall fun u ↦ hbound n u t ht)
  have hy : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hs (v : E) (t : ℝ) := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ v (path t)
  have H := hasDerivAt_tsum_of_isPreconnected (g := g f) (g' := g df) (hb.1.mul_right (μ₁.real univ))
    isOpen_Ioo isPreconnected_Ioo havg hdom hy (hs f 0).summable hy
  have hp : (fun t ↦ ∑' n, g f n t) = fun t ↦ Pχ f (q (path t)) := funext fun t ↦ (hs f t).tsum_eq
  exact (congrArg (fun v : ℝ → ℂ ↦ deriv v 0) hp).symm.trans
    (H.deriv.trans ((hs df 0).tsum_eq.trans (congrArg (fun y ↦ Pχ df (q y)) hzero)))

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–199.
On compact sets of lifts each directional derivative of homogeneous periodization
is the locally uniform sum of the averaged derivatives. -/
theorem modulatedIsotypicPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x : G ↦
      ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * d f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (d (fun x ↦ Pχ f (q x))) atTop C := by
  intro d
  let D (g : E) : E :=
    ⟨bruhatDirectionalDeriv α g.val, modulated_directionalDerivative_mem m hm hms α g⟩
  let v (g : E) := g.val
  let p (g : E) := fun x ↦ Pχ g (q x)
  have hv : Semiconj v D (bruhatDirectionalDeriv α) := fun _ ↦ rfl
  have hp : Semiconj p D (bruhatDirectionalDeriv α) := fun g ↦
    (isotypicPeriodization_directionalDerivative m γ hm hms hγ μ₁ χ α g).symm
  let U (F H : G → ℂ) := TendstoUniformlyOn
    (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * F (γ ^ n * (u.val * x)) ∂μ₁) H atTop C
  exact Eq.mp (congrArg₂ U (hv.iterate_right r f) (hp.iterate_right r f))
    (modulatedIsotypicPeriodization_tendstoUniformlyOn m γ hm hms hγ μ₁ χ (D^[r] f) C hC)

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is open
as a map to its image with the subspace topology. -/
theorem modulatedIsotypicPeriodization_isOpenMap_range :
    IsOpenMap ((Pχ).rangeRestrict) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  exact isOpenMap_rangeRestrict_of_factor (X := E) (Y := S) Pχ P A
    (modulatedPeriodization_surjective m γ hm hms hγ) (modulatedPeriodization_isOpenMap m γ hm hms hγ)
    M hM hA.1 hA.2

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization has closed range. -/
theorem modulatedIsotypicPeriodization_isClosed_range : IsClosed (range Pχ) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  exact isClosed_range_of_factor (X := E) (Y := S) Pχ P A
    (modulatedPeriodization_surjective m γ hm hms hγ) M hM hA.1 hA.2

end IsotypicPeriodizationProperties

section Difference

variable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)

local notation "D" => ModulatedExponentialDecay m I
local notation "diff" => (fun f : D ↦
  let g : modulatedExponentialDecaySubmodule m I := ⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
    modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩
  Sub.sub (α := D) f g)

include hSC hInt hne in
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. Subtracting the
translate by the inverse generator is linear and continuous on the decay space. -/
theorem modulatedCyclicDifference_isLinearMap_continuous :
    IsLinearMap ℂ diff ∧ Continuous diff := by
  have h := exists_modulatedExponentialDecay_translationAction (G := G) m I hm hms hInt hne
  obtain ⟨ρ, hρ, -⟩ := h
  let T : D →L[ℂ] D := ContinuousLinearMap.id ℂ D - ρ γ⁻¹
  have hpt : ∀ f : D, diff f = T f := fun f ↦
    congrArg (fun g : D ↦ f - g)
      (@Subtype.ext _ _ (⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
        modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩ :
          modulatedExponentialDecaySubmodule m I) (ρ γ⁻¹ f)
        (funext fun x ↦ (hρ γ⁻¹ f x).symm))
  have hadd : ∀ x y : D, diff (x + y) = diff x + diff y := fun x y ↦
    (hpt _).trans ((map_add T x y).trans (congrArg₂ (· + ·) (hpt x).symm (hpt y).symm))
  have hsmul : ∀ (c : ℂ) (x : D), diff (c • x) = c • diff x := fun c x ↦
    (hpt _).trans ((map_smul T c x).trans (congrArg (c • ·) (hpt x).symm))
  exact ⟨⟨hadd, hsmul⟩, T.continuous.congr fun f ↦ (hpt f).symm⟩

/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The cyclic
difference sends a function to itself minus its translate by the inverse generator. -/
def modulatedCyclicDifference : D →L[ℂ] D :=
  let h := modulatedCyclicDifference_isLinearMap_continuous m γ hm hms I hInt hne
  let T : D →ₗ[ℂ] D := IsLinearMap.mk' diff h.1
  ⟨T, h.2⟩
set_option linter.unusedSectionVars false in -- Avoid expensive unused-section-variable linting.
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The difference
at x subtracts the function's value at γx. -/
theorem modulatedCyclicDifference_apply (f : D) (x : G) :
    (modulatedCyclicDifference m γ hm hms I hInt hne f).val x =
      f.val x - f.val (γ * x) := congrArg (fun y : G ↦ f.val x - f.val (y * x)) (inv_inv γ)

end Difference

local notation "Δ" => modulatedCyclicDifference m γ hm hms Set.univ
  (ordConnected_univ) (Set.univ_nonempty)
local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

section Averages

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

include hm hms in
private theorem exists_continuous_decay_average (ω : PontryaginDual K) :
    ∃ A : E → E, Continuous A ∧ ∀ f, twist₀ (A f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (twist₀ f) := by
  refine (exists_modulatedExponentialDecay_translationAction m univ hm hms ordConnected_univ univ_nonempty).elim
    fun ρ hρ ↦ ?_
  let Hρ := actionIsotype (ρ.comp (K).subtype) ω
  refine (existsUnique_modulatedExponentialDecay_isotypicProjector m univ hm hms ordConnected_univ
    univ_nonempty μ₁ ρ hρ.1 ω).exists.elim fun A hA ↦ ?_
  have hc := modulatedExponentialDecay_isotypicProjector_continuous m univ hm hms ordConnected_univ
    univ_nonempty μ₁ ρ hρ.1 ω A hA
  exact ⟨fun f ↦ (A f).val, continuous_subtype_val.comp hc, fun f ↦ hA f zeroUniv⟩

include hm in
private theorem homogeneous_average_properties (ω : PontryaginDual K) (f g : E)
    (hg : twist₀ g = schwartzBruhatIsotypicProjector m hm μ₁ ω (twist₀ f)) :
    g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let A := schwartzBruhatIsotypicProjector m hm μ₁ ω
  refine ⟨?_, fun hf ↦ ?_, fun x ↦ ?_⟩
  · refine (schwartzBruhatIsotypicProjector_quotient_equiv m hm μ₁ ω).elim fun iso hiso ↦ ?_
    let y := iso (A.ker.mkQ (twist₀ f))
    have he : y.val = twist₀ g := (hiso (twist₀ f)).trans hg.symm
    exact Eq.mp (congrArg (· ∈ actionIsotype ((ρG).comp (K).subtype) ω) he) y.property
  · have he := hg.trans (schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ ω (twist₀ f) hf)
    exact Subtype.ext (funext fun x ↦ (congrFun (modulationWeight_zero m g.val) x).symm.trans
      ((congrArg (fun v : SchwartzBruhat G ↦ v x) he).trans (congrFun (modulationWeight_zero m f.val) x)))
  · let F (u : K) := (ω u : ℂ) * f.val (u.val * x)
    have hi (u : K) : star (ω u : ℂ) * (twist₀ f) (u.val⁻¹ * x) = F u⁻¹ := by
      have hw : star (ω u : ℂ) = (ω u⁻¹ : ℂ) := by rw [map_inv, Circle.coe_inv_eq_conj]; rfl
      exact congrArg₂ (· * ·) hw (congrFun (modulationWeight_zero m f.val) (u.val⁻¹ * x))
    have he := (integral_congr_ae (ae_of_all μ₁ hi)).trans (integral_inv_eq_self F μ₁)
    have h₀ := (congrFun (modulationWeight_zero m g.val) x).symm
    have h₁ := congrArg (fun v : SchwartzBruhat G ↦ v x) hg
    have h₂ := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω (twist₀ f) x).2
    let I₀ := ∫ u : K, star (ω u : ℂ) * (twist₀ f) (u.val⁻¹ * x) ∂μ₁
    have hc : (μ₁.real univ)⁻¹ • I₀ = (μ₁.real univ : ℂ)⁻¹ * (∫ u, F u ∂μ₁) :=
      (show (μ₁.real univ)⁻¹ • I₀ = (((μ₁.real univ)⁻¹ : ℝ) : ℂ) * I₀ from Complex.real_smul).trans (congrArg₂ (· * ·) (Complex.ofReal_inv _) he)
    exact h₀.trans (h₁.trans (h₂.trans hc))

include hm hms in
private theorem exists_homogeneous_average (ω : PontryaginDual K) (f : E) :
    ∃ g : E, g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁ := by
  refine (exists_continuous_decay_average m hm hms μ₁ ω).elim fun A hA ↦ ?_
  exact ⟨A f, homogeneous_average_properties m hm μ₁ ω f (A f) (hA.2 f)⟩

private theorem periodization_average_apply (ω : PontryaginDual K) (f g : E)
    (hg : ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁) (x : G) :
    P g (q x) = (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁ := by
  let M : ℂ := μ₁.real univ
  have hs := (hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x).mul_left M⁻¹
  have hp := modulatedPeriodization_hasSum m γ hm hms hγ g x
  have he (n : ℤ) : g.val (γ ^ n * x) =
      M⁻¹ * (∫ u : K, (ω u : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) :=
    (hg _).trans (congrArg (M⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ fun u ↦
      congrArg (fun z ↦ (ω u : ℂ) * f.val z) (mul_left_comm u.val (γ ^ n) x))))
  exact (hp.congr_fun (fun n ↦ (he n).symm)).unique hs

end Averages

/-- Paper: Proposition 4.5.1.1(1), p. 198. Periodization takes the corresponding
norm-one isotype on the decay space to a closed subspace of the quotient test space. -/
theorem modulatedPeriodization_isClosed_isotype_image (ω : PontryaginDual K) :
    IsClosed (P '' (H[ω] : Set E)) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let π : K →ₜ* Q := ⟨(q).comp (K).subtype, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  refine (exists_schwartz_average μ₁ π ω).elim fun A hA ↦ ?_
  have lifts (f : E) : ∃ g : E, g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ P g = A (P f) := by
    refine (exists_homogeneous_average m hm hms μ₁ ω f).elim fun g hg ↦ ⟨g, hg.1, hg.2.1, ?_⟩
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    have hp := periodization_average_apply m γ hm hms hγ μ₁ ω f g hg.2.2 x
    have he (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (π u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    exact hp.trans ((congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ he))).trans
      (hA (P f) (q x)).symm)
  have he : P '' (H[ω] : Set E) = {y | A y = y} := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (lifts f).elim fun g hg ↦ hg.2.2.symm.trans (congrArg (fun v ↦ P v) (hg.2.1 hf))
    · intro hy
      refine (modulatedPeriodization_surjective m γ hm hms hγ y).elim fun f hf ↦ ?_
      exact (lifts f).elim fun g hg ↦ ⟨g, hg.1, hg.2.2.trans ((congrArg A hf).trans hy)⟩
  exact Eq.mpr (congrArg IsClosed he) (isClosed_eq A.continuous continuous_id)

section DifferenceKernels

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "ωχ" => PontryaginDual.map
  (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- TODO(paper-gap): On p. 202 the multiplier needs χ(γ)⁻¹. With the Mellin
-- weight χ(x)m(x)^s its zero lattice is 2πin/log(m γ) − it₀. The print has
-- the i in the numerator and writes log γ for the logarithm of the module.

-- TODO(paper-gap): The opening of the proof of (6) on p. 203 uses equality
-- with the actual difference range. Part (5) only identifies its closure.

omit [MeasurableSpace G] [BorelSpace G] in
private theorem mem_schwartzTranslationIsotype_iff (ω : PontryaginDual K) (f : SchwartzBruhat G) :
    f ∈ actionIsotype ((ρG).comp (K).subtype) ω ↔
      ∀ (u : K) (x : G), f (u.val⁻¹ * x) = (ω u : ℂ) * f x := by
  refine (mem_actionIsotype _ _ _).trans (forall_congr' fun u ↦ ⟨fun h x ↦ ?_, fun h ↦ ?_⟩)
  · have hx := congrArg (fun g : SchwartzBruhat G ↦ g x) h
    change ρG u.val f x = (ω u : ℂ) * f x at hx
    exact (schwartzBruhatTranslationAction_apply u.val x f).symm.trans hx
  · refine Subtype.ext (funext fun x ↦ ?_)
    change ρG u.val f x = (ω u : ℂ) * f x
    exact (schwartzBruhatTranslationAction_apply u.val x f).trans (h x)

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(6), pp. 198, 203. Taking the range of the cyclic
difference commutes with passage to any norm-one isotype. -/
theorem modulatedCyclicDifference_range_isotype (ω : PontryaginDual K) :
    (Δ).range ⊓ H[ω] = (H[ω]).map (Δ).toLinearMap := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let F (v : E) (x : G) (u : K) := (ω u : ℂ) * v.val (u.val * x)
  have hint (v : E) (x : G) : Integrable (F v x) μ₁ := by
    have hv : Continuous v.val := (schwartzBruhat_continuous (twist₀ v)).congr
      fun z ↦ congrFun (modulationWeight_zero m v.val) z
    exact ((continuous_subtype_val.comp ω.continuous).mul (hv.comp
      (continuous_subtype_val.mul continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hΔ (v : E) (x : G) := modulatedCyclicDifference_apply m γ hm hms univ ordConnected_univ univ_nonempty v x
  have hmem (v : E) : v ∈ H[ω] ↔ ∀ (u : K) (x : G), v.val (u.val⁻¹ * x) = (ω u : ℂ) * v.val x := by
    change twist₀ v ∈ actionIsotype ((ρG).comp (K).subtype) ω ↔ _
    have he := mem_schwartzTranslationIsotype_iff m ω (twist₀ v)
    simpa only [show (twist₀ v).val = v.val from modulationWeight_zero m v.val] using he
  apply SetLike.ext
  intro f
  constructor
  · rintro ⟨⟨v, hv⟩, hf⟩
    refine (exists_homogeneous_average m hm hms μ₁ ω v).elim fun g hg ↦ ⟨g, hg.1, ?_⟩
    refine (exists_homogeneous_average m hm hms μ₁ ω f).elim fun u hu ↦ ?_
    have hfix := hu.2.1 hf
    refine Subtype.ext (funext fun x ↦ ?_)
    have he (k : K) : F v x k - F v (γ * x) k = F f x k := by
      have hpoint := (hΔ v (k.val * x)).symm.trans (congrArg (fun y : E ↦ y.val (k.val * x)) hv)
      change (ω k : ℂ) * v.val (k.val * x) - (ω k : ℂ) * v.val (k.val * (γ * x)) = _
      rw [mul_left_comm k.val γ, ← mul_sub, hpoint]
    have hi := (integral_sub (hint v x) (hint v (γ * x))).symm.trans (integral_congr_ae (ae_of_all μ₁ he))
    have hdiff := congrArg₂ (· - ·) (hg.2.2 x) (hg.2.2 (γ * x))
    exact (hΔ g x).trans (hdiff.trans ((mul_sub _ _ _).symm.trans
      ((congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) hi).trans ((hu.2.2 x).symm.trans
        (congrArg (fun t : E ↦ t.val x) hfix)))))
  · rintro ⟨v, hv, h⟩
    refine ⟨⟨v, h⟩, (hmem f).mpr fun u x ↦ ?_⟩
    have hd (z : G) := (congrArg (fun w : E ↦ w.val z) h).symm.trans (hΔ v z)
    have hh := (hmem v).mp hv u
    calc
      _ = v.val (u.val⁻¹ * x) - v.val (γ * (u.val⁻¹ * x)) := hd _
      _ = (ω u : ℂ) * (v.val x - v.val (γ * x)) := by rw [hh, mul_left_comm γ, hh, mul_sub]
      _ = (ω u : ℂ) * f.val x := congrArg ((ω u : ℂ) * ·) (hd x).symm

end DifferenceKernels

section QuotientIsotype

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

local notation "qK" => (q).comp (K).subtype
local notation "Sχ[" ω "]" => actionIsotype ((ρQ).comp qK) ω

-- TODO(paper-gap): In the proof on p. 201 the square of the unnormalized
-- quotient average is its Haar mass times the average itself.

local notation "Ψ[" ω "]" => modulatedQuotientIsotypicProjector m γ hm hγ μ₁ ω

/-- Paper: Notation 4.5.1.1, p. 204. The normalized average fixes every
function in the norm-one isotype. -/
theorem modulatedQuotientIsotypicProjector_fix (ω : PontryaginDual K) (f : Sχ[ω]) :
    Ψ[ω] f.val = f.val := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  have hμ : (μ₁.real univ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ₁)).ne'
  have hf := (mem_actionIsotype _ ω f.val).mp f.property
  -- Rewriting under `f.val` is very slow here, so the steps are explicit terms.
  have hpt (u : K) (z : Q) : (ω u : ℂ) * f.val (qK u * z) = f.val z := by
    have h : schwartzBruhatTranslationAction (G := Q) (qK u⁻¹) f.val z =
        (ω u⁻¹ : ℂ) * f.val z :=
      congrArg (fun g : S ↦ g z) (hf u⁻¹)
    have e : (qK u⁻¹)⁻¹ * z = qK u * z := by rw [map_inv, inv_inv]
    have h' : f.val (qK u * z) = (ω u⁻¹ : ℂ) * f.val z :=
      (congrArg (fun x ↦ f.val x) e).symm.trans
        ((schwartzBruhatTranslationAction_apply (G := Q) (qK u⁻¹) z f.val).symm.trans h)
    have hω : (ω u : ℂ) * (ω u⁻¹ : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel, map_one, Circle.coe_one]
    exact (congrArg (fun c ↦ (ω u : ℂ) * c) h').trans
      ((mul_assoc _ _ _).symm.trans ((congrArg (· * f.val z) hω).trans (one_mul _)))
  refine Subtype.ext (funext fun z ↦ ?_)
  change (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f.val (qK u * z) ∂μ₁ = f.val z
  have hint : ∫ u : K, (ω u : ℂ) * f.val (qK u * z) ∂μ₁ = (μ₁.real univ : ℂ) * f.val z :=
    (congrArg (fun g : K → ℂ ↦ ∫ u, g u ∂μ₁) (funext fun u ↦ hpt u z)).trans
      ((integral_const _).trans (Complex.real_smul ..))
  exact (congrArg (fun c ↦ (μ₁.real univ : ℂ)⁻¹ * c) hint).trans
    ((mul_assoc _ _ _).symm.trans ((congrArg (· * f.val z) (inv_mul_cancel₀ hμ)).trans
      (one_mul _)))

/-- Paper: Notation 4.5.1.1 and Equation (4.5.1.9), p. 204. The projector
has range exactly the norm-one isotype on the quotient. -/
theorem modulatedQuotientIsotypicProjector_range (ω : PontryaginDual K) :
    (Ψ[ω]).range = Sχ[ω] := by
  have : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  refine le_antisymm ?_ fun f hf ↦ ⟨f, modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω ⟨f, hf⟩⟩
  rintro _ ⟨f, rfl⟩
  refine (mem_actionIsotype _ ω _).mpr fun v ↦ Subtype.ext (funext fun z ↦ ?_)
  change schwartzBruhatTranslationAction (G := Q) (qK v) (Ψ[ω] f) z = (ω v : ℂ) * Ψ[ω] f z
  refine (schwartzBruhatTranslationAction_apply (G := Q) (qK v) z (Ψ[ω] f)).trans ?_
  change (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) ∂μ₁ =
    (ω v : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁)
  set g : K → ℂ := fun u ↦ (ω u : ℂ) * f (qK u * z) with hg
  have hpt (u : K) : (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) = (ω v : ℂ) * g (u * v⁻¹) := by
    have e : qK (u * v⁻¹) * z = qK u * ((qK v)⁻¹ * z) := by
      rw [map_mul, map_inv, mul_assoc]
    have hω : (ω (u * v⁻¹) : ℂ) = (ω u : ℂ) * (ω v : ℂ)⁻¹ := by
      rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
    have hv : (ω v : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h1 : g (u * v⁻¹) = (ω u : ℂ) * (ω v : ℂ)⁻¹ * f (qK u * ((qK v)⁻¹ * z)) :=
      (congrArg (· * f (qK (u * v⁻¹) * z)) hω).trans (congrArg (fun x ↦ _ * f x) e)
    rw [h1]
    field_simp
  have hint : ∫ u : K, (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) ∂μ₁ =
      (ω v : ℂ) * ∫ u : K, g u ∂μ₁ :=
    (congrArg (fun h : K → ℂ ↦ ∫ u, h u ∂μ₁) (funext hpt)).trans
      ((integral_const_mul _ _).trans
        (congrArg (fun c ↦ (ω v : ℂ) * c) (integral_mul_right_eq_self g v⁻¹)))
  rw [hint]
  ring

/-- Paper: Notation 4.5.1.1, p. 204. The normalized quotient projector is idempotent. -/
theorem modulatedQuotientIsotypicProjector_idempotent (ω : PontryaginDual K) :
    (Ψ[ω]).comp Ψ[ω] = Ψ[ω] := ContinuousLinearMap.ext fun f ↦ modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω ⟨Ψ[ω] f, Eq.mp (congrArg (fun T ↦ Ψ[ω] f ∈ T) (modulatedQuotientIsotypicProjector_range m γ hm hγ μ₁ ω)) (LinearMap.mem_range_self _ f)⟩

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν
local notation "e" => modulatedCyclicExponential m γ hm hγ χ t₀ ht₀

include hSC hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. For a fixed norm-one character the
integer family of Fourier coefficient functionals is bounded in the strong dual. -/
theorem modulatedCyclicFourierCoeff_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ a (ω, n)) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompleteSpace S := schwartzBruhat_complete
  apply isVonNBounded_range_clm_of_pointwise (fun n : ℤ ↦ a (ω, n))
  intro f
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  let c : ℂ := ((L * μ₁.real univ)⁻¹ : ℝ)
  refine ⟨‖c‖ * ∫ z, ‖f z‖ ∂ν, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := (modulatedCyclicFourierCoeff_apply m γ hm hγ χ t₀ ht₀ μ₁ ν (ω, n) f).2
  have hu : (∫ z, ‖f z * star (e (ω, n) z)‖ ∂ν) = ∫ z, ‖f z‖ ∂ν := by
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    exact (norm_mul _ _).trans ((congrArg (‖f z‖ * ·)
      ((norm_star _).trans (Circle.norm_coe _))).trans (mul_one _))
  calc
    ‖a (ω, n) f‖ = ‖c * ∫ z, f z * star (e (ω, n) z) ∂ν‖ := congrArg norm h
    _ = _ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq hu) (norm_nonneg c)

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form a bounded set in its strong dual. -/
theorem modulatedCyclicFourierCoeff_isotype_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ (a (ω, n)).comp (Sχ[ω]).subtypeL) := by
  let A : StrongDual ℂ S →L[ℂ] StrongDual ℂ (Sχ[ω]) := (Sχ[ω]).subtypeL.precomp ℂ
  have hb := modulatedCyclicFourierCoeff_isVonNBounded m γ hm hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω
  exact isVonNBounded_range_comp_clm A (fun n : ℤ ↦ a (ω, n)) hb

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form an equicontinuous family. -/
theorem modulatedCyclicFourierCoeff_isotype_equicontinuous (ω : PontryaginDual K) :
    Equicontinuous (fun (n : ℤ) (f : Sχ[ω]) ↦ a (ω, n) f.val) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : BarrelledSpace ℂ S := schwartzBruhat_barrelled
  have hb := modulatedCyclicFourierCoeff_isVonNBounded m γ hm hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω
  exact equicontinuous_comp_of_isVonNBounded_range_dual (fun n : ℤ ↦ a (ω, n)) hb
    (Sχ[ω]).subtypeL (Sχ[ω]).subtypeL.continuous

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "volQ" => (L * μ₁.real univ : ℂ)

local notation "T[" ω "]" => modulatedIsotypicPeriodizationQuotient m γ hm hms hγ μ₁ χ ω

private theorem periodization_on_isotype (η : PontryaginDual G) (ω : PontryaginDual K)
    (hη : ∀ u : K, η u.val = ω u) (f : E) (hf : f ∈ H[ω]) :
    modulatedIsotypicPeriodization m γ hm hms hγ μ₁ η f = (μ₁.real univ : ℂ) • P f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hval (x : G) : twist₀ f x = f.val x := congrFun (modulationWeight_zero m f.val) x
  have hω (u : K) (y : G) : (η u.val : ℂ) * f.val (u.val * y) = f.val y := by
    have h := (mem_schwartzTranslationIsotype_iff m ω (twist₀ f)).mp hf u (u.val * y)
    have h' : (twist₀ f) y = (ω u : ℂ) * (twist₀ f) (u.val * y) :=
      (congrArg (fun z ↦ (twist₀ f) z) (inv_mul_cancel_left u.val y).symm).trans h
    calc
      _ = (ω u : ℂ) * f.val (u.val * y) := congrArg (fun c : Circle ↦ (c : ℂ) * _) (hη u)
      _ = (ω u : ℂ) * (twist₀ f) (u.val * y) := congrArg ((ω u : ℂ) * ·) (hval _).symm
      _ = f.val y := h'.symm.trans (hval y)
  refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
  have hs := (modulatedPeriodization_hasSum m γ hm hms hγ f x).mul_left M
  have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ η f x
  have hconst (n : ℤ) : (∫ u : K, (η u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) =
      M * f.val (γ ^ n * x) := by
    have he (u : K) := hω u (γ ^ n * x)
    rw [integral_congr_ae (.of_forall fun u ↦ (congrArg (fun y ↦ (η u.val : ℂ) * f.val y)
      (mul_left_comm (γ ^ n) u.val x)).trans (he u)), integral_const]
    exact Complex.real_smul
  exact (ht.congr_fun fun n ↦ (hconst n).symm).unique hs

include hχ in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.12), p. 204. The normalized
quotient map agrees with ordinary periodization on the matching isotype.

Deviation: Corollary 4.5.1.6 uses ordinary periodization on quotient classes. Here ordinary
periodization is evaluated on a lift in the matching isotype.
-/
theorem modulatedIsotypicPeriodizationQuotient_mkQ (ω : PontryaginDual K)
    (f : E) (hf : f ∈ H[ω]) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = P f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have he := periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) f hf
  exact (congrArg (M⁻¹ • ·) he).trans (inv_smul_smul₀ hM (P f))

include hχ in
/-- Paper: Equations (4.5.1.7)–(4.5.1.9) and (4.5.1.12), pp. 201, 204.
On every lift the normalized quotient map applies the quotient projector after
ordinary periodization. The unnormalized map of §4.4 multiplies this by the kernel mass.

Deviation: Corollary 4.5.1.6 uses ordinary periodization on quotient classes. On an arbitrary
lift the normalized quotient map applies the isotype projector after ordinary periodization.
-/
theorem modulatedIsotypicPeriodizationQuotient_projector (ω : PontryaginDual K) (f : E) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = Ψ[ω] (P f) ∧
      Pχ[ω] f = (μ₁.real univ : ℂ) • Ψ[ω] (P f) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have h (x : G) : Pχ[ω] f (q x) = ∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁ := by
    have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ (χ ω) f x
    have hs := hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x
    exact (ht.congr_fun fun n ↦ integral_congr_ae (.of_forall fun u ↦
      congrArg (fun c : Circle ↦ (c : ℂ) * _) (hχ ω u).symm)).unique hs
  have normalized : T[ω] ((Pχ[ω]).ker.mkQ f) = Ψ[ω] (P f) := by
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    change M⁻¹ * Pχ[ω] f (q x) = M⁻¹ * ∫ u : K, (ω u : ℂ) * P f (qK u * q x) ∂μ₁
    refine congrArg (M⁻¹ * ·) ((h x).trans (integral_congr_ae (.of_forall fun u ↦ ?_)))
    exact congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
  refine ⟨normalized, ?_⟩
  exact (smul_inv_smul₀ hM (Pχ[ω] f)).symm.trans (congrArg (M • ·) normalized)

include hχ in
/-- Paper: Equation (4.5.1.12), p. 204. The induced periodization identifies
the kernel quotient topologically with the quotient isotype. -/
theorem modulatedIsotypicPeriodizationQuotient_equiv (ω : PontryaginDual K) :
    ∃ F : V[ω] ≃L[ℂ] Sχ[ω], ∀ v, (F v).val = T[ω] v := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have hR := range_smul_comp_of_surjective (X := E) (Y := S) Pχ[ω] P Ψ[ω] (modulatedPeriodization_surjective m γ hm hms hγ)
    M hM (fun f ↦ (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).2)
  exact quotient_equiv_of_scaled_range (X := E) (Y := S) Pχ[ω] (modulatedIsotypicPeriodization_isOpenMap_range
    m γ hm hms hγ μ₁ (χ ω)) M⁻¹ (inv_ne_zero hM) _ (hR.trans (modulatedQuotientIsotypicProjector_range
      m γ hm hγ μ₁ ω))

local notation "b[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω
local notation "pairing[" ω "," n "," f "]" =>
  fun x : G ↦ (f).val x * star (e (ω, n) (q x))

private theorem integral_average_character {X Y : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
    (μX : Measure X) [μX.IsHaarMeasure] (μY : Measure Y) [μY.IsHaarMeasure]
    (π : X →ₜ* Y) (ω : PontryaginDual X) (η : PontryaginDual Y)
    (hη : ∀ u, η (π u) = (ω u)⁻¹) (F : Y → ℂ) (hF : Continuous F) :
    (∫ z, ((μX.real univ : ℂ)⁻¹ * (∫ u, (ω u : ℂ) * F (π u * z) ∂μX)) * star (η z : ℂ) ∂μY) =
      ∫ z, F z * star (η z : ℂ) ∂μY := by
  let M : ℂ := μX.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μX))
  let H (z : Y) (u : X) := ((ω u : ℂ) * F (π u * z)) * star (η z : ℂ)
  let J := ∫ z, F z * star (η z : ℂ) ∂μY
  have hcont : Continuous (Function.uncurry H) := by
    exact (((continuous_subtype_val.comp ω.continuous).comp continuous_snd).mul
      (hF.comp ((π.continuous.comp continuous_snd).mul continuous_fst))).mul
      (((continuous_subtype_val.comp η.continuous).comp continuous_fst).star)
  have hs := integral_integral_swap (μ := μY) (ν := μX)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hinner (u : X) : (∫ z, H z u ∂μY) = J := by
    have he (z : Y) : H z u = F (π u * z) * star (η (π u * z) : ℂ) := by
      have hc : star (η (π u) : ℂ) = (ω u : ℂ) := by rw [hη, Circle.coe_inv_eq_conj]; exact star_star _
      rw [map_mul, Circle.coe_mul, star_mul', hc]
      dsimp only [H]
      ring
    exact (integral_congr_ae (ae_of_all μY he)).trans
      (integral_mul_left_eq_self (μ := μY) (fun z ↦ F z * star (η z : ℂ)) (π u))
  have hout (z : Y) : (M⁻¹ * (∫ u, (ω u : ℂ) * F (π u * z) ∂μX)) * star (η z : ℂ) =
      M⁻¹ * ∫ u, H z u ∂μX := by rw [mul_assoc, ← integral_mul_const]
  have hj : (∫ _ : X, J ∂μX) = M * J := by rw [integral_const]; exact Complex.real_smul
  exact (integral_congr_ae (ae_of_all μY hout)).trans ((integral_const_mul (μ := μY) _ _).trans
    ((congrArg (M⁻¹ * ·) (hs.trans ((integral_congr_ae (ae_of_all μX hinner)).trans hj))).trans
      (inv_mul_cancel_left₀ hM J)))

private theorem cosetIntegral_mul_pullback {A : Type*} [CommGroup A] [MeasurableSpace A]
    (H : Subgroup A) (μH : Measure H) (f : A → ℂ) (w : A ⧸ H → ℂ) (z : A ⧸ H) :
    lcaCosetIntegral H μH (fun x ↦ f x * w (QuotientGroup.mk x)) z =
      lcaCosetIntegral H μH f z * w z := by
  have he (h : H) : QuotientGroup.mk (z.out * h.val) = z := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h.val).mpr h.property, mul_one]
    exact Quotient.out_eq' _
  exact (integral_congr_ae (ae_of_all μH fun h ↦ congrArg (fun y ↦ f (z.out * h.val) * w y) (he h))).trans
    (integral_mul_const (w z) _)

private theorem periodization_eq_cosetIntegral [(Measure.count : Measure Γ).IsHaarMeasure]
    [(Measure.count : Measure Γ).Regular] (f : E) (z : Q) :
    lcaCosetIntegral Γ Measure.count f.val z = P f z := by
  refine QuotientGroup.induction_on z fun x ↦ ?_
  have hs := cyclicCosetIntegral_hasSum m γ hγ (twist₀ f) x
  have hp := modulatedPeriodization_hasSum m γ hm hms hγ f x
  have hval : (twist₀ f).val = f.val := modulationWeight_zero m f.val
  have h : lcaCosetIntegral Γ Measure.count (twist₀ f).val (q x) = P f (q x) :=
    (hs.congr_fun (fun n ↦ (congrFun hval _).symm)).unique hp
  exact (congrArg (fun v : G → ℂ ↦ lcaCosetIntegral Γ Measure.count v (q x)) hval).symm.trans h

include hχ in
private theorem modulatedCyclicCharacter_kernel (j : PontryaginDual K × ℤ) (u : K) :
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk u.val) = (j.1 u)⁻¹ := by
  have h := modulatedCyclicCharacter_mk m γ hγ χ t₀ ht₀ j u.val
  have hu : m u.val = 1 := u.property
  simpa only [hχ j.1 u, hu, Units.val_one, NNReal.coe_one, Real.log_one, mul_zero,
    Circle.exp_zero, mul_one] using h

include hχ hτ hμ hν in
/-- Paper: Equation (4.5.1.10), pp. 204–205. On a lift, the quotient functional
integrates the function against the corresponding annihilator character of G. -/
theorem modulatedCyclicPairing_mkQ (ω : PontryaginDual K) (n : ℤ) (f : E) :
    Integrable (pairing[ω, n, f]) μ ∧
      b[ω] n ((Pχ[ω]).ker.mkQ f) = ∫ x, pairing[ω, n, f] x ∂μ := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let := modulatedCyclicQuotient_compact m γ hm hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace Q := ⟨rfl⟩
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  let η := modulatedCyclicCharacter m γ hγ χ t₀ ht₀ (ω, n)
  let π : K →ₜ* Q := ⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  let w (z : Q) := star (η z : ℂ)
  have hη (u : K) : η (π u) = (ω u)⁻¹ :=
    modulatedCyclicCharacter_kernel m γ hγ χ t₀ ht₀ hχ (ω, n) u
  have hf : Integrable f.val μ := by
    have h := modulatedFourierMellin_integrable m univ hm ordConnected_univ univ_nonempty μ isOpen_univ hms f
      ⟨1, Set.mem_univ _⟩
    have he : (fun x : G ↦ f.val x * (1 : QuasiCharacter G) x) = f.val :=
      funext fun x ↦ mul_one (f.val x)
    exact Eq.mp (congrArg (fun F : G → ℂ ↦ Integrable F μ) he) h
  have hw : Continuous (fun x : G ↦ w (q x)) :=
    ((continuous_subtype_val.comp η.continuous).comp QuotientGroup.continuous_mk).star
  have hF : Integrable (fun x : G ↦ f.val x * w (q x)) μ :=
    hf.mul_bdd (c := 1) hw.aestronglyMeasurable (.of_forall fun x ↦ by
      change ‖star (η (q x) : ℂ)‖ ≤ 1
      rw [norm_star, Circle.norm_coe])
  refine ⟨hF, ?_⟩
  let v := (Pχ[ω]).ker.mkQ f
  have ht := (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).1
  have hc := (modulatedCyclicFourierCoeff_apply m γ hm hγ χ t₀ ht₀ μ₁ ν (ω, n) (T[ω] v)).2
  have hd : ((↑((L * μ₁.real univ)⁻¹) : ℂ)) = (volQ)⁻¹ :=
    (Complex.ofReal_inv _).trans (congrArg Inv.inv (Complex.ofReal_mul _ _))
  have hvol : (volQ) ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hγ)).ne')
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁)))
  have hcoeff : b[ω] n v = ∫ z, T[ω] v z * w z ∂ν :=
    (congrArg ((volQ) * ·) hc).trans ((congrArg (fun d : ℂ ↦ (volQ) * (d * _)) hd).trans
      (mul_inv_cancel_left₀ hvol _))
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have hproj := integral_average_character μ₁ ν π ω η hη (fun z ↦ P f z) (schwartzBruhat_continuous _)
  have heq (z : Q) : T[ω] v z * w z = (Ψ[ω] (P f)) z * w z :=
    congrArg (fun y : S ↦ y z * w z) ht
  have hweil := (weilQuotientIntegral_L1 Γ (modulatedCyclicSubgroup_closed m γ hγ) μ Measure.count ν hν hF).2.2
  have hfib (z : Q) : lcaCosetIntegral Γ Measure.count (fun x ↦ f.val x * w (q x)) z = P f z * w z :=
    (cosetIntegral_mul_pullback Γ Measure.count f.val w z).trans
      (congrArg (· * w z) (periodization_eq_cosetIntegral m γ hm hms hγ f z))
  exact hcoeff.trans ((integral_congr_ae (ae_of_all ν heq)).trans (hproj.trans
    (hweil.trans (integral_congr_ae (ae_of_all ν hfib))).symm))

include hχ in
private theorem isotypicProjector_exponential [DecidableEq (PontryaginDual K)] (ω : PontryaginDual K) (j : PontryaginDual K × ℤ) :
    Ψ[ω] (e j) = if j.1 = ω then e j else 0 := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let η := modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have he (z : Q) (u : K) : (ω u : ℂ) * e j (qK u * z) =
      (star (j.1 u : ℂ) * (ω u : ℂ)) * (η z : ℂ) := by
    change (ω u : ℂ) * (η (qK u * z) : ℂ) = _
    have h := modulatedCyclicCharacter_kernel m γ hγ χ t₀ ht₀ hχ j u
    rw [map_mul, Circle.coe_mul, show η (qK u) = (j.1 u)⁻¹ from h, Circle.coe_inv_eq_conj]
    change (ω u : ℂ) * (star (j.1 u : ℂ) * (η z : ℂ)) = _
    ring
  have h := integral_character_pair μ₁ j.1 ω
  have hf (z : Q) : Ψ[ω] (e j) z = M⁻¹ * ((if j.1 = ω then M else 0) * (η z : ℂ)) := by
    have hi := (integral_congr_ae (ae_of_all μ₁ (he z))).trans
      ((integral_mul_const (η z : ℂ) _).trans (congrArg (· * (η z : ℂ)) h))
    exact congrArg (M⁻¹ * ·) hi
  by_cases hω : j.1 = ω
  · refine Eq.trans (b := e j) ?_ (ite_eq_left hω).symm
    refine Subtype.ext (funext fun z ↦ (hf z).trans ?_)
    exact (congrArg (fun d : ℂ ↦ M⁻¹ * (d * (η z : ℂ))) (ite_eq_left hω)).trans
      (inv_mul_cancel_left₀ hM (η z : ℂ))
  · refine Eq.trans (b := (0 : S)) ?_ (ite_eq_right hω).symm
    refine Subtype.ext (funext fun z ↦ (hf z).trans ?_)
    exact (congrArg (fun d : ℂ ↦ M⁻¹ * (d * (η z : ℂ))) (ite_eq_right hω)).trans
      ((congrArg (M⁻¹ * ·) (zero_mul (η z : ℂ))).trans (mul_zero _))

private theorem absolute_basis_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : ℕ → Y) (l : ℕ → StrongDual ℂ Y) (hb : IsSchauderBasis y l)
    (hu : SchauderBasis.IsUnconditional y l) (ha : SchauderBasis.IsAbsolute y l)
    (s : ℕ → ℕ) (hs : Injective s) (hfix : ∀ n, T (R (y (s n))) = y (s n))
    (hzero : ∀ j ∉ range s, R (y j) = 0) (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (s n))
    let f := fun n ↦ c • (l (s n)).comp T
    IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f := by
  intro x f
  have he (i : ℕ) (u : X) : f i u • x i = R (l (s i) (T u) • y (s i)) := by
    change (c * l (s i) (T u)) • (c⁻¹ • R (y (s i))) = _
    rw [map_smul, smul_smul, mul_right_comm, mul_inv_cancel₀ hc, one_mul]
  have hbi (i j : ℕ) : f i (x j) = if i = j then 1 else 0 := by
    change c * l (s i) (T (c⁻¹ • R (y (s j)))) = _
    rw [map_smul, hfix, map_smul]
    change c * (c⁻¹ * l (s i) (y (s j))) = _
    rw [mul_inv_cancel_left₀ hc]
    exact (hb.1 (s i) (s j)).trans (by by_cases h : i = j <;> simp [h, hs.eq_iff])
  have hsum (u : X) : HasSum (fun i ↦ f i u • x i) u := by
    let g (j : ℕ) := R (l j (T u) • y j)
    have hall : HasSum g u := (hRT u) ▸ (hu (T u)).map R.toAddMonoidHom R.continuous
    have hvan (j : ℕ) (hj : j ∉ range s) : g j = 0 := by
      change R (_ • y j) = 0
      rw [map_smul, hzero j hj, smul_zero]
    exact ((hs.hasSum_iff hvan).mpr hall).congr_fun fun i ↦ he i u
  refine ⟨⟨hbi, fun u ↦ Tendsto.mono_left (hsum u) (SummationFilter.conditional ℕ).le_atTop⟩, ?_⟩
  intro p hp
  let q₀ := p.comp R.toLinearMap
  refine (ha q₀ (hp.comp R.continuous)).elim fun q₁ hq ↦
    ⟨q₁.comp T.toLinearMap, hq.1.comp T.continuous, fun u ↦ ?_⟩
  let b (j : ℕ) := q₀ (l j (T u) • y j)
  have hbnd := hq.2 (T u)
  have hsel : Summable (b ∘ s) := hbnd.1.comp_injective hs
  have hle := hsel.tsum_le_tsum_of_inj s hs (fun j _ ↦ apply_nonneg _ _) (fun j ↦ le_rfl) hbnd.1
  have heq : (fun j ↦ p (f j u • x j)) = b ∘ s := funext fun j ↦ congrArg p (he j u)
  exact ⟨heq ▸ hsel, (congrArg (fun v : ℕ → ℝ ↦ ∑' j, v j) heq).trans_le (hle.trans hbnd.2)⟩

private theorem dual_basis_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : ℕ → Y) (l : ℕ → StrongDual ℂ Y)
    (hd : ∀ g : StrongDual ℂ Y, HasSum (fun j ↦ g (y j) • l j) g)
    (s : ℕ → ℕ) (hs : Injective s) (hzero : ∀ j ∉ range s, R (y j) = 0)
    (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (s n))
    let f := fun n ↦ c • (l (s n)).comp T
    let d := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x n)
    IsSchauderBasis x f → IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  intro x f d hb
  have hbi (i j : ℕ) : d i (f j) = if i = j then 1 else 0 :=
    (hb.1 j i).trans (by by_cases h : i = j <;> simp [h, eq_comm])
  let C : StrongDual ℂ Y →L[ℂ] StrongDual ℂ X := ContinuousLinearMap.precomp ℂ T
  have hsum (g : StrongDual ℂ X) : HasSum (fun j ↦ d j g • f j) g := by
    let h := g.comp R
    have hg : C h = g := ContinuousLinearMap.ext fun u ↦ congrArg g (hRT u)
    let v (j : ℕ) := C (h (y j) • l j)
    have hall : HasSum v g := hg ▸ (hd h).map C.toAddMonoidHom C.continuous
    have hvan (j : ℕ) (hj : j ∉ range s) : v j = 0 := by
      have hz : h (y j) = 0 := (congrArg g (hzero j hj)).trans (map_zero g)
      exact (congrArg C ((congrArg (· • l j) hz).trans (zero_smul ℂ _))).trans (map_zero C)
    refine ((hs.hasSum_iff hvan).mpr hall).congr_fun fun j ↦ ?_
    change (g (c⁻¹ • R (y (s j)))) • (c • (l (s j)).comp T) = C (h (y (s j)) • l (s j))
    rw [map_smul, map_smul, smul_smul]
    change (c⁻¹ * g (R (y (s j))) * c) • _ = g (R (y (s j))) • _
    rw [mul_right_comm, inv_mul_cancel₀ hc, one_mul]
    rfl
  exact ⟨⟨hbi, fun g ↦ Tendsto.mono_left (hsum g) (SummationFilter.conditional ℕ).le_atTop⟩, hsum⟩

private theorem bases_on_selected_indices {X Y J : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [T2Space Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : J → Y) (l : J → StrongDual ℂ Y) (enum : ℕ ≃ J)
    (hb : ∀ σ : ℕ ≃ J, IsSchauderBasis (y ∘ σ) (l ∘ σ) ∧ SchauderBasis.IsAbsolute (y ∘ σ) (l ∘ σ))
    (hd : ∀ σ : ℕ ≃ J, IsSchauderBasis (l ∘ σ)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (y (σ n))))
    (t : ℕ → J) (ht : Injective t)
    (hfix : ∀ n, T (R (y (enum (enum.symm (t n))))) = y (enum (enum.symm (t n))))
    (hz : ∀ j ∉ range (enum.symm ∘ t), R (y (enum j)) = 0) (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (t n))
    let f := fun n ↦ c • (l (t n)).comp T
    let d := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x n)
    IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f ∧
      (∀ n, T (x n) = c⁻¹ • y (t n)) ∧ IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  let s := enum.symm ∘ t
  have hs : Injective s := enum.symm.injective.comp ht
  have hu := (SchauderBasis.isUnconditional_iff_forall_permutation _ _ (hb enum).1).mpr
    (fun u σ ↦ ((hb (σ.trans enum)).1.2 u).summable)
  have hv := (SchauderBasis.isUnconditional_iff_forall_permutation _ _ (hd enum)).mpr
    (fun g σ ↦ ((hd (σ.trans enum)).2 g).summable)
  have H := absolute_basis_of_retraction T R hRT (y ∘ enum) (l ∘ enum) (hb enum).1 hu
    (hb enum).2 s hs hfix hz c hc
  have D := dual_basis_of_retraction T R hRT (y ∘ enum) (l ∘ enum) hv s hs hz c hc H.1
  have he (j : ℕ) : enum (s j) = t j := enum.apply_symm_apply _
  dsimp only [Function.comp_apply] at H D
  simp only [he] at H D hfix
  exact ⟨H.1, H.2, fun n ↦ (map_smul T _ _).trans (congrArg (c⁻¹ • ·)
    (show T (R (y (t n))) = y (t n) by simpa only [Equiv.apply_symm_apply] using hfix n)), D⟩

private theorem retain_character_frequencies {X Y A : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [DecidableEq A]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (P₁ : Y → Y) (v : A × ℤ → Y)
    (hRT : ∀ x, R (T x) = x) (hTR : ∀ y, T (R y) = P₁ y)
    (ω : A) (σ : ℕ ≃ ℤ) (enum : ℕ ≃ A × ℤ)
    (he : ∀ j, P₁ (v j) = if j.1 = ω then v j else 0) :
    let s := fun i ↦ enum.symm (ω, σ i)
    (∀ i, T (R (v (enum (s i)))) = v (enum (s i))) ∧ ∀ j ∉ range s, R (v (enum j)) = 0 := by
  intro s
  constructor
  · intro i
    have heq : (enum (s i)).1 = ω := congrArg Prod.fst (enum.apply_symm_apply (ω, σ i))
    exact (hTR _).trans ((he _).trans (ite_eq_left heq))
  · intro j hj
    have hj' : (enum j).1 ≠ ω := by
      intro hω
      apply hj
      refine ⟨σ.symm (enum j).2, enum.injective ?_⟩
      exact (enum.apply_symm_apply _).trans (Prod.ext hω.symm (σ.apply_symm_apply _))
    have hz := (hTR _).trans ((he (enum j)).trans (ite_eq_right hj'))
    exact (hRT _).symm.trans ((congrArg R hz).trans (map_zero R))

private theorem quotient_bases_on_character_isotype {D₀ Y A : Type*}
    [AddCommGroup D₀] [Module ℂ D₀] [TopologicalSpace D₀] [IsTopologicalAddGroup D₀] [ContinuousSMul ℂ D₀]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [T2Space Y] [DecidableEq A]
    (N : Submodule ℂ D₀)
    (T : (D₀ ⧸ N) →L[ℂ] Y) (proj : Y → Y) (v : A × ℤ → Y) (l : A × ℤ → StrongDual ℂ Y)
    (ω : A) (σ : ℕ ≃ ℤ) (c : ℂ) (hc : c ≠ 0) (f : ℕ → StrongDual ℂ (D₀ ⧸ N))
    (hf : ∀ i, f i = c • (l (ω, σ i)).comp T)
    (hR : ∃ R : Y →L[ℂ] (D₀ ⧸ N), (∀ u, R (T u) = u) ∧ ∀ y, T (R y) = proj y)
    (he : ∀ j, proj (v j) = if j.1 = ω then v j else 0)
    (hp : Nonempty (ℕ ≃ A × ℤ) ∧ ∀ p : ℕ ≃ A × ℤ, IsSchauderBasis (v ∘ p) (l ∘ p) ∧
      SchauderBasis.IsAbsolute (v ∘ p) (l ∘ p))
    (hd : ∀ p : ℕ ≃ A × ℤ, IsSchauderBasis (l ∘ p)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (v (p n)))) :
    ∃ x : ℕ → (D₀ ⧸ N), IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f ∧
      (∀ i, T (x i) = c⁻¹ • v (ω, σ i)) ∧
      ∃ d : ℕ → StrongDual ℂ (StrongDual ℂ (D₀ ⧸ N)),
        IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  obtain ⟨⟨enum⟩, hb⟩ := hp
  obtain ⟨R, hRT, hTR⟩ := hR
  let t := fun i : ℕ ↦ (ω, σ i)
  have ht : Injective t := fun _ _ h ↦ σ.injective (congrArg Prod.snd h)
  have hz := retain_character_frequencies T R proj v hRT hTR ω σ enum he
  have h := bases_on_selected_indices T R hRT v l enum hb hd t ht hz.1 hz.2 c hc
  have ef : f = fun i ↦ c • (l (t i)).comp T := funext hf
  subst f
  exact ⟨_, h.1, h.2.1, h.2.2.1, _, h.2.2.2⟩

include hχ in
private theorem exists_basis_retraction (ω : PontryaginDual K) :
    ∃ R : S →L[ℂ] V[ω], (∀ u, R (T[ω] u) = u) ∧ ∀ y, T[ω] (R y) = Ψ[ω] y := by
  have hE := modulatedIsotypicPeriodizationQuotient_equiv m γ hm hms hγ μ₁ χ hχ ω
  have hA := modulatedQuotientIsotypicProjector_range m γ hm hγ μ₁ ω
  have hF := modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω
  refine hE.elim fun U hU ↦ ?_
  have hmem (y : S) : Ψ[ω] y ∈ Sχ[ω] :=
    (Iff.of_eq (congrArg (fun H : Submodule ℂ S ↦ Ψ[ω] y ∈ H) hA)).mp
      (LinearMap.mem_range_self _ y)
  let B := (Ψ[ω]).codRestrict Sχ[ω] hmem
  let R := U.symm.toContinuousLinearMap.comp B
  have hTR₀ (z : Sχ[ω]) : T[ω] (U.symm z) = z.val :=
    (hU (U.symm z)).symm.trans (congrArg (fun w : Sχ[ω] ↦ w.val) (U.apply_symm_apply z))
  have hB (x : V[ω]) : B (T[ω] x) = U x := by
    refine Subtype.ext ?_
    exact (congrArg Ψ[ω] (hU x).symm).trans (hF (U x))
  have hR (y : S) := ContinuousLinearMap.comp_apply U.symm.toContinuousLinearMap B y
  have hval (y : S) := ContinuousLinearMap.coe_codRestrict_apply Ψ[ω] Sχ[ω] hmem y
  have hRT (x : V[ω]) : R (T[ω] x) = x :=
    (hR _).trans ((congrArg U.symm (hB x)).trans (U.symm_apply_apply x))
  have hTR (y : S) : T[ω] (R y) = Ψ[ω] y :=
    (congrArg T[ω] (hR y)).trans ((hTR₀ (B y)).trans (hval y))
  exact ⟨R, hRT, hTR⟩

include hχ hτ hμ hν in
private theorem quotient_isotype_bases (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ v : ℕ → V[ω], IsSchauderBasis v (b[ω] ∘ σ) ∧ SchauderBasis.IsAbsolute v (b[ω] ∘ σ) ∧
      (∀ n, T[ω] (v n) = volQ⁻¹ • e (ω, σ n)) ∧
      ∃ d : ℕ → StrongDual ℂ (StrongDual ℂ (V[ω])),
        IsSchauderBasis (b[ω] ∘ σ) d ∧ SchauderBasis.IsUnconditional (b[ω] ∘ σ) d := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have hvol : (volQ) ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hγ)).ne')
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁)))
  have hfull := modulatedCyclicExponential_absoluteBasis m γ hm hms hγ χ hχ t₀ ht₀ μ₁ ν τ hτ μ hμ hν
  have hd (p : ℕ ≃ PontryaginDual K × ℤ) :=
    (modulatedCyclicFourierCoeff_absoluteBasis m γ hm hms hγ χ hχ t₀ ht₀ μ₁ ν τ hτ μ hμ hν p).1
  classical
  have hr := exists_basis_retraction m γ hm hms hγ μ₁ χ hχ ω
  have he := isotypicProjector_exponential m γ hm hγ μ₁ χ t₀ ht₀ hχ ω
  let coordinates := b[ω] ∘ σ
  have hfun (i : ℕ) : coordinates i = volQ • (a (ω, σ i)).comp T[ω] := rfl
  have result := quotient_bases_on_character_isotype (D₀ := E) (Y := S) (Pχ[ω]).ker T[ω] Ψ[ω] (e) (a) ω σ
    volQ hvol coordinates hfun hr he hfull hd
  exact result

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6, p. 204. For every enumeration of the integer
frequencies the integral functionals form an unconditional Schauder basis
of the strong dual of the kernel quotient. This dual represents the kernel annihilator. -/
theorem modulatedCyclicPairing_unconditionalBasis (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      IsSchauderBasis (b[ω] ∘ σ) c ∧
        SchauderBasis.IsUnconditional (b[ω] ∘ σ) c := by
  refine (quotient_isotype_bases m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ).elim
    fun _ hv ↦ hv.2.2.2

-- TODO(paper-gap): In Corollary 4.5.1.6 the full periodization depends on the
-- representative of the homogeneous kernel class. The unnormalized integral pairs to the
-- quotient volume against the matching unscaled exponential.

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.11), p. 204. The
biorthogonal vectors form an absolute basis of the kernel quotient.
Deviation: Periodization uses isotypic representatives, and the displayed
exponentials are divided by the quotient Haar volume to match (4.5.1.10). -/
theorem modulatedIsotypicPeriodizationQuotient_absoluteBasis
    (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ v : ℕ → V[ω], IsSchauderBasis v (b[ω] ∘ σ) ∧
      SchauderBasis.IsAbsolute v (b[ω] ∘ σ) ∧
      ∀ n, T[ω] (v n) = volQ⁻¹ • e (ω, σ n) := by
  refine (quotient_isotype_bases m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ).elim
    fun v hv ↦ ⟨v, hv.1, hv.2.1, hv.2.2.1⟩

end QuotientIsotype

/-! ## 4.5.2 Support conditions -/

section Support

variable (B : Set ℝ≥0ˣ) (k : Subgroup G)

-- TODO(paper-gap): The opening of §4.5.2 uses a global completed projective
-- tensor isomorphism despite the compact-generation restriction in Remark 4.5.1.3.

/-- Paper: §4.5.2, p. 205. The fixed-support space consists of compactly supported
two-sided decay functions that vanish off the module window. For the paper's
compact windows their topological support also lies in the window.
Deviation: The support cylinder is written as the preimage of the window under
the module. For a section τ this is τ(B) times the norm-one group. -/
def modulatedCompactSupportSubmodule : Submodule ℂ E :=
  (bruhatCompactSupportSubmodule G).comap (modulatedExponentialDecaySubmodule m Set.univ).subtype ⊓
    ⨅ x : {x : G // m x ∉ B}, LinearMap.ker
      ((LinearMap.proj x.val).comp (modulatedExponentialDecaySubmodule m Set.univ).subtype)

/-- An abstract form of `mem_modulatedCompactSupportSubmodule_iff`: in a function space with
generating seminorms, membership in a submodule `Tf` that cuts out compact support, intersected
with the kernels of evaluation off a closed set `Z`, means compact support with topological
support in `Z`. Stated abstractly so that elaboration does not unfold the decay space. -/
private theorem mem_comap_inf_iInf_ker_proj_iff {X : Type*} [TopologicalSpace X]
    (Sf Tf : Submodule ℂ (X → ℂ)) {ι : Type*} (p : SeminormFamily ℂ Sf ι) (Z : Set X)
    (hZ : IsClosed Z) (hT : ∀ g : Sf, g.val ∈ Tf ↔ HasCompactSupport g.val)
    (f : WithGeneratingSeminorms Sf p) :
    f ∈ (Tf.comap (Sf.subtype : WithGeneratingSeminorms Sf p →ₗ[ℂ] (X → ℂ)) ⊓
        ⨅ x : {x : X // x ∉ Z}, LinearMap.ker
          ((LinearMap.proj x.val).comp (Sf.subtype : WithGeneratingSeminorms Sf p →ₗ[ℂ] (X → ℂ))) :
        Submodule ℂ (WithGeneratingSeminorms Sf p)) ↔
      HasCompactSupport (f : Sf).val ∧ tsupport (f : Sf).val ⊆ Z := by
  refine Submodule.mem_inf.trans (and_congr (hT f) (Submodule.mem_iInf _ |>.trans
    ⟨fun h ↦ closure_minimal (fun x hx ↦ ?_) hZ, fun h x ↦ ?_⟩))
  · by_contra hxZ
    exact hx (LinearMap.mem_ker.mp (h ⟨x, hxZ⟩))
  · exact LinearMap.mem_ker.mpr
      (image_eq_zero_of_notMem_tsupport (f := (f : Sf).val) (x := x.val) fun hx ↦ x.2 (h hx))

-- The section-variable linter scans the large elaborated decay types and takes minutes.
set_option linter.unusedSectionVars false in
/-- Paper: §4.5.2, p. 205. For a closed module window, membership in the
fixed-support space is equivalent to the stated condition on topological support. -/
theorem mem_modulatedCompactSupportSubmodule_iff (hB : IsClosed B) (f : E) :
    f ∈ modulatedCompactSupportSubmodule m B ↔
      HasCompactSupport f.val ∧ tsupport f.val ⊆ m ⁻¹' B :=
  mem_comap_inf_iInf_ker_proj_iff (modulatedExponentialDecaySubmodule m Set.univ)
    (bruhatCompactSupportSubmodule G) _ (m ⁻¹' B) (hB.preimage m.continuous)
    (fun g ↦ ⟨fun h ↦ h.2, fun h ↦
      ⟨modulatedExponentialDecay_mem_bruhatSmooth m Set.univ Set.univ_nonempty g, h⟩⟩) f

/-- Paper: §4.5.2, p. 205. The fixed-support k-stage imposes k-invariance
on the supported decay space, with the topology inherited from the decay space. -/
def modulatedCompactSupportStage : Submodule ℂ E :=
  modulatedCompactSupportSubmodule m B ⊓ (schwartzBruhatInvariantSubmodule k).comap twist₀

/-- Paper: §4.5.2, p. 205. The stage consists of the supported functions
whose values are unchanged by translation by elements of k. -/
theorem mem_modulatedCompactSupportStage_iff (f : E) :
    f ∈ modulatedCompactSupportStage m B k ↔
      f ∈ modulatedCompactSupportSubmodule m B ∧
        ∀ (x : G) (u : k), f.val (u.val * x) = f.val x := by
  have htwist (x : G) : twist₀ f x = f.val x :=
    (modulatedExponentialDecayTwist_apply m Set.univ zeroUniv f x).trans
      ((congrArg (fun r : ℝ ↦ (r : ℂ) * f.val x) (Real.rpow_zero _)).trans
        ((congrArg (· * f.val x) Complex.ofReal_one).trans (one_mul _)))
  change f ∈ modulatedCompactSupportSubmodule m B ∧
    twist₀ f ∈ schwartzBruhatInvariantSubmodule k ↔ _
  refine and_congr_right fun _ ↦
    (mem_schwartzBruhatInvariantSubmodule_iff k (twist₀ f)).trans ?_
  exact forall_congr' fun x ↦ forall_congr' fun u ↦ iff_of_eq (congrArg₂ Eq
    ((htwist (x * u.val)).trans (congrArg f.val (mul_comm x u.val))) (htwist x))

variable (hk : IsCompact (k : Set G))
variable (hperp : IsCompactlyGeneratedGroup (lcaAnnihilator (k.comap m.toMonoidHom.ker.subtype)))
variable (hB : IsCompact B) (hBi : (interior B).Nonempty)

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The fixed-support k-stage is
a closed subspace of the two-sided decay space. -/
theorem modulatedCompactSupportStage_isClosed :
    IsClosed (modulatedCompactSupportStage m B k : Set E) := by
  let C := m ⁻¹' B
  have hC : IsCompact C := hm.1.isCompact_preimage hB
  have hev (x : G) : Continuous (fun f : E ↦ f.val x) := by
    refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
    refine (modulatedExponentialDecay_continuous_inclusion m univ hm ordConnected_univ univ_nonempty
      τ hτ (mem_univ 0)).elim fun j hj ↦ ?_
    refine (schwartzBruhat_dirac_support x).elim fun e he ↦ ?_
    exact (e.continuous.comp j.continuous).congr fun f ↦ (he.1 (j f)).trans (hj.2 f x)
  let vanish : Set E := ⋂ x : {x : G // x ∉ C}, {f | f.val x = 0}
  let invariant : Set E := ⋂ x : G, ⋂ u : k, {f | f.val (u.val * x) = f.val x}
  have hV : IsClosed vanish := isClosed_iInter fun x ↦ isClosed_eq (hev x) continuous_const
  have hJ : IsClosed invariant := isClosed_iInter fun x ↦ isClosed_iInter fun u ↦
    isClosed_eq (hev (u.val * x)) (hev x)
  have hset : (modulatedCompactSupportStage m B k : Set E) = vanish ∩ invariant := by
    apply Set.ext
    intro f
    refine (mem_modulatedCompactSupportStage_iff m B k f).trans ?_
    have hs : tsupport f.val ⊆ C ↔ ∀ x ∉ C, f.val x = 0 :=
      hC.isClosed.closure_subset_iff.trans Function.support_subset_iff'
    have hv : f ∈ modulatedCompactSupportSubmodule m B ↔ f ∈ vanish := by
      refine (mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed f).trans ?_
      constructor
      · intro h
        exact Set.mem_iInter.mpr fun x ↦ hs.mp h.2 _ x.property
      · intro h
        have hb := hs.mpr fun x hx ↦ Set.mem_iInter.mp h ⟨x, hx⟩
        exact ⟨hC.of_isClosed_subset (isClosed_tsupport _) hb, hb⟩
    exact and_congr hv ⟨fun h ↦ Set.mem_iInter.mpr fun x ↦ Set.mem_iInter.mpr (h x),
      fun h x ↦ Set.mem_iInter.mp (Set.mem_iInter.mp h x)⟩
  exact Eq.mpr (congrArg IsClosed hset) (hV.inter hJ)

include hm in
private theorem bruhatGood_of_modulation_kernel (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (hk : IsCompact (k : Set G))
    (hperp : IsCompactlyGeneratedGroup (lcaAnnihilator (k.comap (K).subtype))) :
    IsBruhatGoodSubgroup k := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let kernelSubgroup := k.comap (K).subtype
  have hL : IsClosed (kernelSubgroup : Set K) := hk.isClosed.preimage continuous_subtype_val
  have hgL : IsBruhatGoodSubgroup kernelSubgroup := ⟨hL, isOpen_lcaAnnihilator kernelSubgroup hL.isCompact, hperp⟩
  let line : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ _
  let chart : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ≥0ˣ :=
    line.toHomeomorph.trans positiveRealLogEquiv.symm.toHomeomorph
  have haxis : IsBruhatGoodSubgroup (⊥ : Subgroup ℝ≥0ˣ) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨1, ⟨chart.chartedSpace⟩⟩
  obtain ⟨d, hd⟩ := hm.exists_sectionEquiv τ hτ
  let j : K × ℝ≥0ˣ →ₜ* G := ⟨d.toMonoidHom, d.continuous⟩
  apply (openEmbedding_good_comap j d.toHomeomorph.isOpenEmbedding k hk).mp
  have hcomap : k.comap j.toMonoidHom = kernelSubgroup.prod ⊥ := by
    ext ⟨u,t⟩
    change d (u,t) ∈ k ↔ u.val ∈ k ∧ t = 1
    rw [hd]
    constructor
    · intro hx
      have ht : m (u.val * τ t) = 1 := compactSubgroup_le_modulation_ker m k hk hx
      rw [map_mul, show m u.val = 1 from u.property, hτ, one_mul] at ht
      exact ⟨by simpa [ht] using hx, ht⟩
    · rintro ⟨hu,rfl⟩
      simpa using hu
  rw [hcomap]
  exact prod_bruhat_good _ _ hgL haxis

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The inherited topology on the
supported k-stage agrees with the fixed-support test-function topology on G/k.
Deviation: The test space is represented by the elementary structural pair
with open subgroup G and compact subgroup k, using the fixed-support stage of §D.3.6. -/
theorem modulatedCompactSupportStage_testFunction_equiv :
    ∃ (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (C : TopologicalSpace.Compacts G)
      (F : bruhatCompactSupportStage p e C ≃L[ℂ] modulatedCompactSupportStage m B k),
      p.val.1 = ⊤ ∧ OrderDual.ofDual p.val.2 = k ∧ (C : Set G) = m ⁻¹' B ∧
      ∀ f, (F f).val.val = schwartzBruhatStageRealization p e f.val := by
  classical
  let τ := (modulation_surjective_exists_section m hm hms).choose
  have hτ := (modulation_surjective_exists_section m hm hms).choose_spec
  let top : (⊤ : Subgroup G) ≃ₜ* G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let p : BruhatStructuralPair G :=
    ⟨(⊤, OrderDual.toDual k), isOpen_univ,
      isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm
        (compactlyGenerated_of_surjective_modulation m hm hms),
      bruhatGood_of_modulation_kernel m hm k τ hτ hk hperp, le_top⟩
  let e := Classical.choice p.elementary
  let C : TopologicalSpace.Compacts G := ⟨m ⁻¹' B, hm.1.isCompact_preimage hB⟩
  let V := bruhatCompactSupportStage p e C
  let W := modulatedCompactSupportStage m B k
  let j : V →ₗ[ℂ] BruhatCompactSupport G := bruhatCompactSupportStageInclusion p e C
  have hj : Continuous j := (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp j
    (fun testNorm ↦ testNorm.property p e C)
  let T : V →L[ℂ] E := ⟨(bruhatCompactSupportToModulatedExponentialDecay m univ hm hms).comp j,
    (bruhatCompactSupport_continuous_modulatedExponentialDecay m univ hm hms
      ordConnected_univ univ_nonempty).comp hj⟩
  have hT (v : V) : (T v).val = schwartzBruhatStageRealization p e v.val := rfl
  have hTW (v : V) : T v ∈ W := by
    apply (mem_modulatedCompactSupportStage_iff m B k _).mpr
    have hs := (mem_bruhatCompactSupportStage_iff p e C _).mp v.property
    refine ⟨(mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed _).mpr ?_, ?_⟩
    · rw [hT]
      exact ⟨C.isCompact.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩
    · intro x u
      rw [hT]
      exact stage_realization_mul_kernel p e _ u.property x
  let F₀ := T.codRestrict W hTW
  have hi := modulatedExponentialDecay_continuous_inclusion m univ hm
    ordConnected_univ univ_nonempty τ hτ (mem_univ 0)
  let I := hi.choose
  have hI := hi.choose_spec.2
  let R := (schwartzBruhatStage_average_retraction p e).choose
  have hpoint := (schwartzBruhatStage_average_retraction p e).choose_spec.2
  let retract := R.comp (I.comp W.subtypeL)
  have hQ (w : W) : schwartzBruhatStageRealization p e (retract w) = w.val.val := by
    have hw := (mem_modulatedCompactSupportStage_iff m B k w.val).mp w.property
    funext x
    refine (hpoint (I w.val) x).trans ((stageAverage_eq_self_of_invariant p (I w.val).val
      (fun _ hx ↦ (hx trivial).elim) (fun y u hu ↦ ?_) x).trans (hI w.val x))
    rw [hI, hI, mul_comm y u]
    exact hw.2 y ⟨u,hu⟩
  have hQV (w : W) : retract w ∈ V := by
    apply (mem_bruhatCompactSupportStage_iff p e C _).mpr
    rw [hQ]
    exact ((mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed _).mp
      ((mem_modulatedCompactSupportStage_iff m B k _).mp w.property).1).2
  let J := retract.codRestrict V hQV
  have hleft (v : V) : J (F₀ v) = v := by
    apply Subtype.ext
    apply schwartzBruhatStageInclusion_injective p e
    exact Subtype.ext ((hQ (F₀ v)).trans (hT v))
  have hright (w : W) : F₀ (J w) = w :=
    Subtype.ext (Subtype.ext ((hT (J w)).trans (hQ w)))
  let equiv := ContinuousLinearEquiv.equivOfInverse F₀ J hleft hright
  exact ⟨p,e,C,equiv,rfl,rfl,rfl,hT⟩

-- Remark 4.5.2.2, p. 207, uses the Fréchet topology of this elementary
-- stage. See also modulatedExponentialDecayStage_frechet and
-- modulatedExponentialDecay_stageLimit in §D.3.3.

variable (a b : ℝ≥0ˣ)
variable (ha : 1 < a.val) (hwidth : Real.log ((m γ).val : ℝ) < 2 * Real.log (a.val : ℝ))

local notation "window" => Icc (b / a) (b * a)
local notation "W" => modulatedCompactSupportStage m window k

include hSC hm hms hγ ha hwidth in
/-- Paper: Proposition 4.5.2.1(2), p. 205. A module window wider than one
logarithmic period maps onto the cyclic quotient. -/
theorem modulatedCompactSupport_quotient_image :
    q '' (m ⁻¹' window) = (univ : Set Q) := by
  have hpos (u : ℝ≥0ˣ) : 0 < ((u.val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt u)
  have hle (u v : ℝ≥0ˣ) : u ≤ v ↔ Real.log (u.val : ℝ) ≤ Real.log (v.val : ℝ) := by
    rw [Real.log_le_log_iff (hpos u) (hpos v), NNReal.coe_le_coe, Units.val_le_val]
  have hdiv : Real.log ((b / a).val : ℝ) = Real.log (b.val : ℝ) - Real.log (a.val : ℝ) := by
    rw [Units.val_div_eq_div_val, NNReal.coe_div, Real.log_div (hpos b).ne' (hpos a).ne']
  have hmul : Real.log ((b * a).val : ℝ) = Real.log (b.val : ℝ) + Real.log (a.val : ℝ) := by
    rw [Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos b).ne' (hpos a).ne']
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hx (n : ℤ) : Real.log ((m (γ ^ n * x)).val : ℝ) =
      n * L + Real.log ((m x).val : ℝ) := by
    rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos (m γ)).ne') (hpos (m x)).ne',
      Real.log_zpow]
  generalize ht : (Real.log (b.val : ℝ) - Real.log (a.val : ℝ) -
    Real.log ((m x).val : ℝ)) / L = t
  have htL : t * L = Real.log (b.val : ℝ) - Real.log (a.val : ℝ) -
      Real.log ((m x).val : ℝ) := by
    rw [← ht, div_mul_cancel₀ _ hL.ne']
  have h1 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one t) hL
  have h2 := mul_le_mul_of_nonneg_right (Int.floor_le t) hL.le
  rw [add_one_mul] at h1
  refine ⟨γ ^ (⌊t⌋ + 1) * x, ⟨?_, ?_⟩, ?_⟩
  · rw [hle, hdiv, hx, Int.cast_add, Int.cast_one, add_one_mul]
    linarith
  · rw [hle, hmul, hx, Int.cast_add, Int.cast_one, add_one_mul]
    linarith
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ _), one_mul]

include hγ hwidth in
/-- Paper: Proposition 4.5.2.1(2), pp. 205–206. The interior of a strict-width
window already meets every orbit. -/
theorem modulatedCompactSupport_quotient_image_interior :
    q '' (m ⁻¹' interior window) = (univ : Set Q) := by
  let v : ℝ≥0ˣ → ℝ := fun t ↦ ((t.val : ℝ≥0) : ℝ)
  have hv : Continuous v := NNReal.continuous_coe.comp Units.continuous_val
  have hvpos (t : ℝ≥0ˣ) : 0 < v t := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : 0 < Real.log (v (m γ)) := Real.log_pos (by exact_mod_cast hγ)
  -- The open window lies in the interior of the closed one.
  have hsub : {t : ℝ≥0ˣ | v t ∈ Ioo (v (b / a)) (v (b * a))} ⊆ interior window := by
    refine interior_maximal (fun t ht ↦ ⟨?_, ?_⟩) (isOpen_Ioo.preimage hv)
    · exact Units.val_le_val.mp (NNReal.coe_le_coe.mp ht.1.le)
    · exact Units.val_le_val.mp (NNReal.coe_le_coe.mp ht.2.le)
  have hlo : Real.log (v (b / a)) = Real.log (v b) - Real.log (v a) := by
    simp only [v, Units.val_div_eq_div_val, NNReal.coe_div]
    exact Real.log_div (hvpos b).ne' (hvpos a).ne'
  have hhi : Real.log (v (b * a)) = Real.log (v b) + Real.log (v a) := by
    simp only [v, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (hvpos b).ne' (hvpos a).ne'
  have hℓ (x : G) (n : ℤ) :
      Real.log (v (m (x * γ ^ n))) = Real.log (v (m x)) + n * Real.log (v (m γ)) := by
    simp only [v, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow]
    rw [Real.log_mul (hvpos (m x)).ne' (zpow_pos (hvpos (m γ)) n).ne', Real.log_zpow]
  -- Every orbit meets the open window, since it is wider than one period.
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set lγ := Real.log (v (m γ))
  set A₀ := Real.log (v b) - Real.log (v a)
  let n : ℤ := ⌊(A₀ - Real.log (v (m x))) / lγ⌋ + 1
  have hf := Int.floor_le ((A₀ - Real.log (v (m x))) / lγ)
  have hf' := Int.lt_floor_add_one ((A₀ - Real.log (v (m x))) / lγ)
  rw [le_div_iff₀ hL] at hf
  rw [div_lt_iff₀ hL] at hf'
  have hn : (n : ℝ) = ⌊(A₀ - Real.log (v (m x))) / lγ⌋ + 1 := by push_cast [n]; rfl
  have hw : lγ < 2 * Real.log (v a) := hwidth
  refine ⟨x * γ ^ n, hsub ?_, ?_⟩
  · change v (m (x * γ ^ n)) ∈ Ioo (v (b / a)) (v (b * a))
    constructor
    · rw [← Real.log_lt_log_iff (hvpos _) (hvpos _), hlo, hℓ, hn]
      nlinarith
    · rw [← Real.log_lt_log_iff (hvpos _) (hvpos _), hhi, hℓ, hn]
      nlinarith
  · exact QuotientGroup.mk_mul_of_mem x (Subgroup.zpow_mem_zpowers γ n)

/-- A closed submodule of a Fréchet space is Fréchet. -/
private theorem modulatedCompactSupportStage_periodization_equiv_frechet_closed {X : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] (hX : IsFrechetTVS X) (M : Submodule ℂ X)
    (hM : IsClosed (M : Set X)) : IsFrechetTVS M := by
  obtain ⟨hadd, hpoly, hmet, hcomp⟩ := hX
  have : TopologicalSpace.MetrizableSpace X := hmet
  have : PolynormableSpace ℂ X := hpoly
  have hmetM : TopologicalSpace.MetrizableSpace M := IsEmbedding.subtypeVal.metrizableSpace
  have hpolyM : PolynormableSpace ℂ M := inferInstance
  refine ⟨inferInstance, hpolyM, hmetM, ?_⟩
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hcomp
  have hU : IsUniformAddGroup M := M.toAddSubgroup.isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := M)]
  exact hM.completeSpace_coe

/-- Open mapping: a continuous linear surjection from a closed submodule of a strict LF space
onto an LF space is open. -/
private theorem modulatedCompactSupportStage_periodization_equiv_isOpenMap {X Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (hX : IsStrictLFSpace X) (V : Submodule ℂ X) (hW : IsClosed (V : Set X))
    (hZ : IsLFSpace Z) (F₀ : V →L[ℂ] Z) (hs : Surjective F₀) : IsOpenMap F₀ := by
  obtain ⟨hT2, U, hmono, hF, hc, _⟩ := hX
  let : T2Space X := hT2
  let Y (n : ℕ) : Submodule ℂ (U n) := V.comap (U n).subtype
  let u (n : ℕ) : Y n →L[ℂ] V :=
    ((U n).subtypeL.comp (Y n).subtypeL).codRestrict V fun y ↦ y.property
  have hY (n : ℕ) : IsFrechetTVS (Y n) :=
    modulatedCompactSupportStage_periodization_equiv_frechet_closed (hF n) (Y n)
      (hW.preimage continuous_subtype_val)
  refine isOpenMap_of_surjective_toLF hZ hY u (fun n ↦ ?_) (fun w ↦ ?_) F₀ hs
  · rintro _ ⟨y, rfl⟩
    exact ⟨⟨⟨y.val.val, hmono n.le_succ y.val.property⟩, y.property⟩, rfl⟩
  · obtain ⟨n, hn⟩ := hc w.val
    exact ⟨n, ⟨⟨w.val, hn⟩, w.property⟩, rfl⟩

/-- A telescoping smooth profile whose support lies in `[-T, ε]`. -/
private theorem modulatedCompactSupportStage_periodization_equiv_profile {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) (hεT : ε ≤ T) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ t, t ∉ Icc (-T) ε → ρ t = 0) ∧
      ∀ t, HasSum (fun n : ℤ ↦ ρ (t + n * T)) 1 := by
  let H (t : ℝ) := Real.smoothTransition (t / ε)
  have H0 {t : ℝ} (ht : t ≤ 0) : H t = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ht hε.le)
  have H1 {t : ℝ} (ht : ε ≤ t) : H t = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr ht)
  refine ⟨fun t ↦ H (t + T) - H t, ?_, fun t ht ↦ ?_, fun t ↦ ?_⟩
  · have hH : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H :=
      Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)
    exact (hH.comp (contDiff_id.add contDiff_const)).sub hH
  · rcases not_and_or.mp ht with h | h
    · have h' : t < -T := not_le.mp h
      simp only [H0 (show t + T ≤ 0 by linarith), H0 (show t ≤ 0 by linarith), sub_zero]
    · have h' : ε < t := not_le.mp h
      simp only [H1 (show ε ≤ t + T by linarith), H1 h'.le, sub_self]
  · let N : ℤ := ⌊-t / T⌋
    have hN : (N : ℝ) * T ≤ -t := (le_div_iff₀ hT).mp (Int.floor_le _)
    have hN' : -t < ((N : ℝ) + 1) * T := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one _)
    have hlow (n : ℤ) (hn : n ≤ N) : H (t + n * T) = 0 := H0 (by
      have : (n : ℝ) * T ≤ N * T := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hT.le
      linarith)
    have hhigh (n : ℤ) (hn : N + 2 ≤ n) : H (t + n * T) = 1 := H1 (by
      have : ((N : ℝ) + 2) * T ≤ n * T :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hT.le
      nlinarith)
    have hterm (n : ℤ) : H (t + n * T + T) - H (t + n * T) =
        H (t + ((n + 1 : ℤ) : ℝ) * T) - H (t + n * T) := by
      push_cast; ring_nf
    let g : ℤ → ℝ := fun n ↦ H (t + n * T + T) - H (t + n * T)
    have hs : HasSum g (∑ n ∈ ({N, N + 1} : Finset ℤ), g n) :=
      hasSum_sum_of_ne_finset_zero (fun n hn ↦ by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        change H _ - H _ = 0
        rw [hterm]
        rcases lt_or_gt_of_ne hn.1 with h | h
        · rw [hlow n h.le, hlow (n + 1) (by omega), sub_self]
        · rw [hhigh n (by omega), hhigh (n + 1) (by omega), sub_self])
    convert hs using 1
    simp only [g]
    rw [Finset.sum_pair (by omega), hterm, hterm]
    have e1 := hlow N le_rfl
    have e2 := hhigh (N + 1 + 1) (by omega)
    push_cast at e2 ⊢
    rw [show (N : ℝ) + 1 + 1 = N + 2 by ring] at e2 ⊢
    linarith

include hγ in
/-- The subgroup generated by the generator and a compact subgroup is closed. -/
private theorem modulatedCompactSupportStage_periodization_equiv_sup_closed
    (hk : IsCompact (k : Set G)) :
    IsClosed ((Γ ⊔ k : Subgroup G) : Set G) := by
  have hΓ : IsClosed ((Γ : Subgroup G) : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  rw [sup_comm, Subgroup.normal_mul k Γ]
  exact hΓ.mul_left_of_isCompact hk

include hγ in
/-- The compact subgroup is open in `Γ ⊔ k`: it is the set of elements whose module has
logarithm strictly within one period of zero. -/
private theorem modulatedCompactSupportStage_periodization_equiv_kernel_isOpen
    (hk : IsCompact (k : Set G)) :
    IsOpen ((Subtype.val : ↥(Γ ⊔ k : Subgroup G) → G) ⁻¹' (k : Set G)) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hcont : Continuous (fun z : ↥(Γ ⊔ k : Subgroup G) ↦ Real.log ((m z.val).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ (hpos x).ne').comp continuous_subtype_val
  have heq : (Subtype.val : ↥(Γ ⊔ k : Subgroup G) → G) ⁻¹' (k : Set G) =
      (fun z : ↥(Γ ⊔ k : Subgroup G) ↦ Real.log ((m z.val).val : ℝ)) ⁻¹' Ioo (-L) L := by
    ext z
    constructor
    · intro hz
      change Real.log ((m z.val).val : ℝ) ∈ Ioo (-L) L
      rw [modulatedPeriodization_surjective_log_compact m hk z.val hz]
      exact ⟨by linarith, hL⟩
    · intro hz
      change Real.log ((m z.val).val : ℝ) ∈ Ioo (-L) L at hz
      obtain ⟨y, hy, u, hu, hyu⟩ := Subgroup.mem_sup.mp z.property
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hlog : Real.log ((m z.val).val : ℝ) = n * L := by
        rw [← hyu, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos _).ne' (hpos _).ne',
          modulatedPeriodization_surjective_log_compact m hk u hu, add_zero, map_zpow,
          Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Real.log_zpow]
      rw [hlog] at hz
      have h1 : ((-1 : ℤ) : ℝ) * L < n * L := by push_cast; linarith [hz.1]
      have h2 : (n : ℝ) * L < ((1 : ℤ) : ℝ) * L := by push_cast; linarith [hz.2]
      have h1' : (-1 : ℤ) < n := by exact_mod_cast lt_of_mul_lt_mul_right h1 hL.le
      have h2' : n < (1 : ℤ) := by exact_mod_cast lt_of_mul_lt_mul_right h2 hL.le
      have hn : n = 0 := by omega
      change z.val ∈ k
      rw [← hyu, hn, zpow_zero, one_mul]
      exact hu
  rw [heq]
  exact isOpen_Ioo.preimage hcont

include hγ in
/-- The Haar integral over `Γ ⊔ k` of a `k`-invariant function is the measure of `k` times
its orbit sum over the generator. -/
private theorem modulatedCompactSupportStage_periodization_equiv_integral [MeasurableSpace G]
    [BorelSpace G] (hk : IsCompact (k : Set G))
    (μ' : Measure ↥(Γ ⊔ k : Subgroup G)) [μ'.IsHaarMeasure]
    (g : G → ℂ) (hg : ∀ u ∈ k, ∀ y, g (u * y) = g y)
    (hint : Integrable (fun z : ↥(Γ ⊔ k : Subgroup G) ↦ g z.val) μ') :
    HasSum (fun n : ℤ ↦ (μ'.real ((Subtype.val : ↥(Γ ⊔ k : Subgroup G) → G) ⁻¹' (k : Set G)) : ℂ) *
      g (γ ^ n)) (∫ z, g z.val ∂μ') := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  let k' : Set ↥(Γ ⊔ k : Subgroup G) := Subtype.val ⁻¹' (k : Set G)
  have hk'm : MeasurableSet k' := (hk.isClosed.preimage continuous_subtype_val).measurableSet
  let γH : ↥(Γ ⊔ k : Subgroup G) := ⟨γ, Subgroup.mem_sup_left (Subgroup.mem_zpowers γ)⟩
  let c (n : ℤ) : Set ↥(Γ ⊔ k : Subgroup G) := (fun z ↦ (γH ^ n)⁻¹ * z) ⁻¹' k'
  have hcm (n : ℤ) : MeasurableSet (c n) := hk'm.preimage (measurable_const_mul _)
  have hmeas (n : ℤ) : μ' (c n) = μ' k' := measure_preimage_mul μ' _ k'
  have hval (n : ℤ) (z : ↥(Γ ⊔ k : Subgroup G)) (hz : z ∈ c n) : g z.val = g (γ ^ n) := by
    have hu : ((γH ^ n)⁻¹ * z).val ∈ k := hz
    have hzv : z.val = ((γH ^ n)⁻¹ * z).val * γ ^ n := by
      change z.val = (γ ^ n)⁻¹ * z.val * γ ^ n
      rw [mul_comm ((γ ^ n)⁻¹) z.val, inv_mul_cancel_right]
    rw [hzv, hg _ hu]
  have hdisj : Pairwise (Disjoint on c) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun z hi hj ↦ hij ?_
    have hi' : (γ ^ i)⁻¹ * z.val ∈ k := hi
    have hj' : (γ ^ j)⁻¹ * z.val ∈ k := hj
    have hmem : γ ^ (j - i) ∈ k := by
      have := k.mul_mem hi' (k.inv_mem hj')
      rw [zpow_sub]
      convert this using 1
      group
    have hlog := modulatedPeriodization_surjective_log_compact m hk _ hmem
    rw [map_zpow, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Real.log_zpow] at hlog
    have h0 : ((j - i : ℤ) : ℝ) = 0 := (mul_eq_zero.mp hlog).resolve_right hL.ne'
    have : j - i = 0 := by exact_mod_cast h0
    omega
  have hcover : (⋃ n, c n) = univ := by
    refine eq_univ_of_forall fun z ↦ mem_iUnion.mpr ?_
    obtain ⟨y, hy, u, hu, hyu⟩ := Subgroup.mem_sup.mp z.property
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨n, ?_⟩
    change (γ ^ n)⁻¹ * z.val ∈ k
    rw [← hyu, inv_mul_cancel_left]
    exact hu
  have hion : IntegrableOn (fun z : ↥(Γ ⊔ k : Subgroup G) ↦ g z.val) (⋃ n, c n) μ' := by
    rw [hcover]
    exact hint.integrableOn
  have hs := hasSum_integral_iUnion hcm hdisj hion
  have hu : (∫ z in ⋃ n, c n, g z.val ∂μ') = ∫ z, g z.val ∂μ' := by
    rw [hcover, Measure.restrict_univ]
  rw [hu] at hs
  refine hs.congr_fun fun n ↦ ?_
  rw [setIntegral_congr_fun (hcm n) (fun z hz ↦ hval n z hz), setIntegral_const, Complex.real_smul,
    measureReal_def, measureReal_def, hmeas n]

include hγ in
/-- Periodization descends to a continuous linear map from the supported stage to the
Schwartz–Bruhat space of `G/(Γ ⊔ k)`: a normalized coset integral over `Γ ⊔ k`. -/
private theorem modulatedCompactSupportStage_periodization_equiv_descent
    (hk : IsCompact (k : Set G)) :
    ∃ F₀ : W →L[ℂ] SchwartzBruhat (G ⧸ (Γ ⊔ k)),
      ∀ (f : W) (x : G), F₀ f (QuotientGroup.mk x) = P f.val (q x) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have hH : IsClosed ((Γ ⊔ k : Subgroup G) : Set G) :=
    modulatedCompactSupportStage_periodization_equiv_sup_closed m γ hγ k hk
  let : LocallyCompactSpace ↥(Γ ⊔ k : Subgroup G) := hH.locallyCompactSpace
  let μ' : Measure ↥(Γ ⊔ k : Subgroup G) := Measure.haar
  obtain ⟨C, hC⟩ := schwartzBruhatCosetIntegral_continuousLinear (Γ ⊔ k) μ' hH
  obtain ⟨τ, hτ⟩ := modulation_surjective_exists_section m hm hms
  obtain ⟨j, -, hj⟩ := modulatedExponentialDecay_continuous_inclusion m univ hm ordConnected_univ
    univ_nonempty τ hτ (mem_univ 0)
  let k' : Set ↥(Γ ⊔ k : Subgroup G) := Subtype.val ⁻¹' (k : Set G)
  have hk'o : IsOpen k' :=
    modulatedCompactSupportStage_periodization_equiv_kernel_isOpen m γ hγ k hk
  have hk'c : IsCompact k' := (hH.isClosedEmbedding_subtypeVal).isCompact_preimage hk
  have hne : k'.Nonempty := ⟨1, k.one_mem⟩
  have hpos : μ'.real k' ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (hk'o.measure_pos μ' hne).ne' hk'c.measure_lt_top.ne).ne'
  refine ⟨((μ'.real k' : ℂ)⁻¹) • (C.comp (j.comp (W).subtypeL)), fun f x ↦ ?_⟩
  have h1 : C (j f.val) (QuotientGroup.mk x) =
      ∫ z : ↥(Γ ⊔ k : Subgroup G), (j f.val) (x * z.val) ∂μ' := by
    rw [hC]
    exact schwartzBruhatCosetIntegral_mk (Γ ⊔ k) μ' hH _ x
  have hinv := ((mem_modulatedCompactSupportStage_iff m window k f.val).mp f.property).2
  have hg (u : G) (hu : u ∈ k) (y : G) : f.val.val (x * (u * y)) = f.val.val (x * y) := by
    rw [mul_left_comm]
    exact hinv (x * y) ⟨u, hu⟩
  have hint : Integrable (fun z : ↥(Γ ⊔ k : Subgroup G) ↦ f.val.val (x * z.val)) μ' := by
    refine ((lcaCosetIntegral_mem_schwartzBruhat (Γ ⊔ k) μ' hH (j f.val)).1 x).congr
      (Filter.Eventually.of_forall fun z ↦ ?_)
    exact hj f.val (x * z.val)
  have hsum := modulatedCompactSupportStage_periodization_equiv_integral m γ hγ k hk μ'
    (fun y ↦ f.val.val (x * y)) hg hint
  have hP := (modulatedPeriodization_hasSum m γ hm hms hγ f.val x).mul_left (μ'.real k' : ℂ)
  have heq : (∫ z : ↥(Γ ⊔ k : Subgroup G), f.val.val (x * z.val) ∂μ') =
      (μ'.real k' : ℂ) * P f.val (q x) :=
    (hsum.congr_fun fun n ↦
      congrArg ((μ'.real k' : ℂ) * ·) (congrArg f.val.val (mul_comm _ x))).unique hP
  have h2 : (∫ z : ↥(Γ ⊔ k : Subgroup G), (j f.val) (x * z.val) ∂μ') =
      ∫ z : ↥(Γ ⊔ k : Subgroup G), f.val.val (x * z.val) ∂μ' :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦ hj f.val (x * z.val))
  change (μ'.real k' : ℂ)⁻¹ * C (j f.val) (QuotientGroup.mk x) = P f.val (q x)
  rw [h1, h2, heq, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hpos), one_mul]

private theorem modulatedCompactSupportStage_periodization_equiv_window_isCompact (l r : ℝ≥0ˣ) :
    IsCompact (Icc l r) := by
  let e := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hmon (a b : ℝ≥0ˣ) : e a ≤ e b ↔ a ≤ b := by
    change Real.expOrderIso.symm _ ≤ Real.expOrderIso.symm _ ↔ _
    exact Real.expOrderIso.symm.le_iff_le
  have he : Icc l r = e ⁻¹' Icc (e l) (e r) :=
    Set.ext fun x ↦ and_congr (hmon l x).symm (hmon x r).symm
  exact he ▸ e.isProperMap.isCompact_preimage isCompact_Icc


include hγ hwidth in
/-- Every Schwartz–Bruhat function on `G/(Γ ⊔ k)` is the periodization of a `k`-invariant
function supported in the window: multiply its pullback by a telescoping cutoff of the
logarithm of the module. -/
private theorem modulatedCompactSupportStage_periodization_equiv_surjective
    (hk : IsCompact (k : Set G)) (φ : SchwartzBruhat (G ⧸ (Γ ⊔ k))) :
    ∃ f : W, ∀ x : G, P f.val (q x) = φ (QuotientGroup.mk x) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have hpos (u : ℝ≥0ˣ) : 0 < ((u.val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt u)
  have hle (u v : ℝ≥0ˣ) : u ≤ v ↔ Real.log (u.val : ℝ) ≤ Real.log (v.val : ℝ) := by
    rw [Real.log_le_log_iff (hpos u) (hpos v), NNReal.coe_le_coe, Units.val_le_val]
  have hdiv : Real.log ((b / a).val : ℝ) = Real.log (b.val : ℝ) - Real.log (a.val : ℝ) := by
    rw [Units.val_div_eq_div_val, NNReal.coe_div, Real.log_div (hpos b).ne' (hpos a).ne']
  have hmul : Real.log ((b * a).val : ℝ) = Real.log (b.val : ℝ) + Real.log (a.val : ℝ) := by
    rw [Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos b).ne' (hpos a).ne']
  set ε := min L (2 * Real.log (a.val : ℝ) - L) with hεdef
  have hε : 0 < ε := lt_min hL (by linarith)
  have hεL : ε ≤ L := min_le_left _ _
  have hεa : ε ≤ 2 * Real.log (a.val : ℝ) - L := min_le_right _ _
  obtain ⟨ρ, hρs, hρz, hρsum⟩ := modulatedCompactSupportStage_periodization_equiv_profile hL hε hεL
  set c := Real.log (b.val : ℝ) - Real.log (a.val : ℝ) + L with hcdef
  let ρc : ℝ → ℂ := fun t ↦ (ρ (t - c) : ℂ)
  have hρs' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρc :=
    Complex.ofRealCLM.contDiff.comp (hρs.comp (contDiff_id.sub contDiff_const))
  have hH : IsClosed ((Γ ⊔ k : Subgroup G) : Set G) :=
    modulatedCompactSupportStage_periodization_equiv_sup_closed m γ hγ k hk
  let f₀ : G → ℂ := fun x ↦ ρc (Real.log ((m x).val : ℝ)) * φ (QuotientGroup.mk x)
  have hsm : IsBruhatSmooth f₀ := fun p ↦
    modulatedPeriodization_surjective_mul (modulatedPeriodization_surjective_logProfile m hρs' p)
      (modulatedPeriodization_surjective_comp_mk (Γ ⊔ k) (schwartzBruhat_isBruhatSmooth φ p))
  have hsupp : support f₀ ⊆ {x : G | Real.log ((m x).val : ℝ) ∈ Icc (c - L) (c + ε)} := by
    intro x hx
    by_contra hxc
    refine hx ?_
    have h0 : ρ (Real.log ((m x).val : ℝ) - c) = 0 :=
      hρz _ fun h ↦ hxc ⟨by linarith [h.1], by linarith [h.2]⟩
    change ρc _ * _ = 0
    simp only [ρc, h0, Complex.ofReal_zero, zero_mul]
  have hcpt : HasCompactSupport f₀ :=
    HasCompactSupport.of_support_subset_isCompact
      (modulatedPeriodization_surjective_window m hm isCompact_Icc) hsupp
  have hmem : f₀ ∈ bruhatCompactSupportSubmodule G :=
    ⟨(mem_bruhatSmoothSubmodule_iff f₀).mpr hsm, hcpt⟩
  let f : E := ⟨f₀, bruhatCompactSupport_le_modulatedExponentialDecay m univ hm hms hmem⟩
  have hwin : {x : G | Real.log ((m x).val : ℝ) ∈ Icc (c - L) (c + ε)} ⊆ m ⁻¹' window := by
    intro x hx
    refine ⟨(hle _ _).mpr ?_, (hle _ _).mpr ?_⟩
    · rw [hdiv]; linarith [hx.1]
    · rw [hmul]; linarith [hx.2]
  have hfW : f ∈ W := by
    refine (mem_modulatedCompactSupportStage_iff m window k f).mpr ⟨?_, fun x u ↦ ?_⟩
    · have hBc := modulatedCompactSupportStage_periodization_equiv_window_isCompact (b / a) (b * a)
      refine (mem_modulatedCompactSupportSubmodule_iff m window hBc.isClosed f).mpr ⟨hcpt, ?_⟩
      exact closure_minimal (hsupp.trans hwin) (hBc.isClosed.preimage m.continuous)
    · change ρc (Real.log ((m (u.val * x)).val : ℝ)) * φ (QuotientGroup.mk (u.val * x)) =
        ρc (Real.log ((m x).val : ℝ)) * φ (QuotientGroup.mk x)
      rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos _).ne' (hpos _).ne',
        modulatedPeriodization_surjective_log_compact m hk u.val u.property, zero_add,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right u.property),
        one_mul]
  refine ⟨⟨f, hfW⟩, fun x ↦ ?_⟩
  have hℓ (n : ℤ) : Real.log ((m (γ ^ n * x)).val : ℝ) =
      Real.log ((m x).val : ℝ) + n * L := by
    rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos (m γ)).ne') (hpos (m x)).ne',
      Real.log_zpow]
    ring
  have hqx (n : ℤ) : (QuotientGroup.mk (γ ^ n * x) : G ⧸ (Γ ⊔ k)) = QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers γ n)),
      one_mul]
  have h2 : HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) (φ (QuotientGroup.mk x)) := by
    have h := (Complex.hasSum_ofReal.mpr (hρsum (Real.log ((m x).val : ℝ) - c))).mul_right
      (φ (QuotientGroup.mk x))
    rw [Complex.ofReal_one, one_mul] at h
    refine h.congr_fun fun n ↦ ?_
    change ρc _ * φ (QuotientGroup.mk (γ ^ n * x)) = _
    rw [hℓ, hqx]
    change ((ρ (Real.log ((m x).val : ℝ) + n * L - c) : ℝ) : ℂ) * _ = _
    rw [show Real.log ((m x).val : ℝ) + n * L - c = Real.log ((m x).val : ℝ) - c + n * L by ring]
  exact (modulatedPeriodization_hasSum m γ hm hms hγ f x).unique h2

include hk hperp ha hwidth in
/-- Paper: Proposition 4.5.2.1(2) and Equation (4.5.2.1), p. 205. On a window
wider than one period, the supported k-stage modulo the periodization kernel
is identified by periodization with the quotient test space on G/(γ^ℤ k). -/
theorem modulatedCompactSupportStage_periodization_equiv :
    let N := (P).ker.comap (W).subtype
    ∃ F : ((W) ⧸ N) ≃L[ℂ] SchwartzBruhat (G ⧸ (Γ ⊔ k)),
      ∀ (f : W) (x : G), F (N.mkQ f) (QuotientGroup.mk x) = P f.val (q x) := by
  intro N
  obtain ⟨F₀, hF₀⟩ :=
    modulatedCompactSupportStage_periodization_equiv_descent m γ hm hms hγ k a b hk
  have hs : Surjective F₀ := fun φ ↦ by
    obtain ⟨f, hf⟩ :=
      modulatedCompactSupportStage_periodization_equiv_surjective m γ hm hms hγ k a b hwidth hk φ
    exact ⟨f, Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z fun x ↦
      (hF₀ f x).trans (hf x))⟩
  have hBi : (interior window).Nonempty := by
    have h := modulatedCompactSupport_quotient_image_interior m γ hγ a b hwidth
    obtain ⟨x, hx, -⟩ : (QuotientGroup.mk (1 : G) : Q) ∈ q '' (m ⁻¹' interior window) :=
      h ▸ mem_univ _
    exact ⟨m x, hx⟩
  have hW : IsClosed ((W) : Set E) := modulatedCompactSupportStage_isClosed m hm hms window k hk
    hperp (modulatedCompactSupportStage_periodization_equiv_window_isCompact (b / a) (b * a)) hBi
  obtain ⟨τ, hτ⟩ := modulation_surjective_exists_section m hm hms
  have hX := modulatedExponentialDecay_strictLF m univ hm ordConnected_univ univ_nonempty τ hτ
  have hZ : IsLFSpace (SchwartzBruhat (G ⧸ (Γ ⊔ k))) := by
    let : IsClosed ((Γ ⊔ k : Subgroup G) : Set G) :=
      modulatedCompactSupportStage_periodization_equiv_sup_closed m γ hγ k hk
    exact schwartzBruhat_isLF
  have ho : IsOpenMap F₀ :=
    modulatedCompactSupportStage_periodization_equiv_isOpenMap hX (W) hW hZ F₀ hs
  have hker : F₀.ker = N := by
    ext f
    change F₀ f = 0 ↔ P f.val = 0
    constructor
    · intro h
      exact Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z fun x ↦
        ((hF₀ f x).symm.trans
          (congrArg (fun φ : SchwartzBruhat (G ⧸ (Γ ⊔ k)) ↦ φ (QuotientGroup.mk x)) h)))
    · intro h
      exact Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z fun x ↦
        ((hF₀ f x).trans (congrArg (fun φ : S ↦ φ (q x)) h)))
  obtain ⟨F, hF⟩ := exists_quotient_equiv_of_kernel F₀ (ho.isQuotientMap F₀.continuous hs) N hker
  exact ⟨F, fun f x ↦
    (congrArg (fun φ : SchwartzBruhat (G ⧸ (Γ ⊔ k)) ↦ φ (QuotientGroup.mk x)) (hF f)).trans
      (hF₀ f x)⟩

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "D[" B "]" => modulatedCompactSupportSubmodule m B

-- TODO(paper-gap): Equation (4.5.2.2) is false for arbitrary compact windows
-- with interior. Already G = ℝ_{>0}, χ = 1, B = [1, γ] misses the constant
-- periodization, since a smooth function supported there vanishes at both endpoints.

private theorem modulatedCompactSupport_isotypicQuotient_equiv_log (r t : ℝ≥0ˣ) (n : ℤ) :
    Real.log (((r ^ n * t).val : ℝ≥0) : ℝ) = Real.log (t.val : ℝ) + n * Real.log (r.val : ℝ) := by
  have hpos (s : ℝ≥0ˣ) : 0 < (s.val : ℝ) := NNReal.coe_pos.mpr s.zero_lt
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul, NNReal.coe_zpow,
    Real.log_mul (zpow_ne_zero _ (hpos r).ne') (hpos t).ne', Real.log_zpow, add_comm]

include hB hms in
private theorem modulatedCompactSupport_isotypicQuotient_equiv_window
    (hcover : (QuotientGroup.mk' (Subgroup.zpowers γ)) '' (m ⁻¹' interior B) =
      (univ : Set (G ⧸ Subgroup.zpowers γ))) :
    ∃ C : TopologicalSpace.Compacts ℝ, (∀ t : ℝ≥0ˣ, Real.log (t.val : ℝ) ∈ C ↔ t ∈ B) ∧
      ∀ x : ℝ, ∃ n : ℤ, x + n * L ∈ interior (C : Set ℝ) := by
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let C : TopologicalSpace.Compacts ℝ := ⟨e.symm ⁻¹' B, e.symm.isCompact_preimage.mpr hB⟩
  refine ⟨C, fun t ↦ ?_, fun x ↦ ?_⟩
  · change e.symm (Real.log (t.val : ℝ)) ∈ B ↔ t ∈ B
    rw [← he, e.symm_apply_apply]
  · obtain ⟨g, hg⟩ := hms (e.symm x)
    have hmem : q g ∈ q '' (m ⁻¹' interior B) := hcover.symm ▸ mem_univ _
    obtain ⟨y, hy, heq⟩ := hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_iff_div_mem.mp heq)
    have hmy : m y = (m γ) ^ n * m g := by
      rw [← map_zpow, ← map_mul, hn, div_mul_cancel]
    refine ⟨n, ?_⟩
    have hlog : Real.log ((m g).val : ℝ) = x := (he _).symm.trans (hg ▸ e.apply_symm_apply x)
    have hx : e (m y) = x + n * L := by
      rw [he, hmy, modulatedCompactSupport_isotypicQuotient_equiv_log, hlog]
    change _ ∈ interior (e.symm ⁻¹' B)
    rwa [← e.symm.preimage_interior, ← hx, mem_preimage, e.symm_apply_apply]

private theorem modulatedCompactSupport_isotypicQuotient_equiv_phase (r : ℝ≥0ˣ) (hr : 1 < r.val)
    (c : Circle) : ∃ η : PontryaginDual ℝ≥0ˣ, η r = c := by
  obtain ⟨a, ha⟩ := Circle.exp_surjective c
  let b := a / Real.log (r.val : ℝ)
  have hn (t : ℝ≥0ˣ) : (t.val : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr t.ne_zero
  let η : PontryaginDual ℝ≥0ˣ :=
    { toFun := fun t ↦ Circle.exp (b * Real.log (t.val : ℝ))
      map_one' := by simp
      map_mul' := fun u v ↦ by
        simp only [Units.val_mul, NNReal.coe_mul, Real.log_mul (hn u) (hn v), mul_add,
          Circle.exp_add]
      continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul
        ((NNReal.continuous_coe.comp Units.continuous_val).log hn)) }
  exact ⟨η, (congrArg Circle.exp (div_mul_cancel₀ a (Real.log_pos (by exact_mod_cast hr)).ne')).trans ha⟩

include hm in
/-- Tensor a scalar profile with the normalized conjugate character of the compact kernel.
Compact averaging recovers the profile, and the lift preserves its radial support. -/
private theorem modulatedCompactSupport_isotypicQuotient_equiv_profileLift
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (ξ : PontryaginDual G) :
    ∃ J : PositiveRealExponentialDecay univ →L[ℂ] E,
      (∀ p t, ∫ k : K, (ξ k.val : ℂ) * (J p).val (k.val * τ t) ∂μ₁ =
        p.val (Real.log (t.val : ℝ))) ∧
      ∀ p (x : G), p.val (Real.log ((m x).val : ℝ)) = 0 → (J p).val x = 0 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  let ω : PontryaginDual K := ξ.comp ⟨(K).subtype, continuous_subtype_val⟩
  let oneK := (compact_schwartzBruhat_one (H := K)).choose
  have honeK := (compact_schwartzBruhat_one (H := K)).choose_spec
  let M := (schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹).choose
  have hM := (schwartzBruhat_mul_unitaryCharacter (A := K) ω⁻¹).choose_spec
  let u := (μ₁.real univ : ℂ)⁻¹ • M oneK
  have hu (k : K) : (ξ k.val : ℂ) * u k = (μ₁.real univ : ℂ)⁻¹ := by
    change (ω k : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * M oneK k) = _
    have hc : M oneK k = (ω⁻¹ k : ℂ) :=
      (hM oneK k).trans ((congrArg ((ω⁻¹ k : ℂ) * ·) (honeK k)).trans (mul_one _))
    have hw : (ω k : ℂ) * (ω⁻¹ k : ℂ) = 1 :=
      (Circle.coe_mul _ _).symm.trans (congrArg ((↑) : Circle → ℂ) (mul_inv_cancel (ω k)))
    exact (congrArg (fun z : ℂ ↦ (ω k : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * z)) hc).trans
      ((mul_left_comm _ _ _).trans ((congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) hw).trans (mul_one _)))
  let P₁ := PositiveRealExponentialDecay univ
  have hTensor := modulatedExponentialDecay_tensor_equiv m univ hm ordConnected_univ univ_nonempty τ hτ
  let J : P₁ →L[ℂ] E := by
    with_reducible_and_instances exact completedTensor_right (X := SchwartzBruhat K) (Y := P₁) (Z := E) hTensor.choose u
  let ev (k : K) (t : ℝ≥0ˣ) (w : E) := w.val (k.val * τ t)
  have hJ (p : P₁) (k : K) (t : ℝ≥0ˣ) : (J p).val (k.val * τ t) = u k * p.val (Real.log (t.val : ℝ)) := by
    with_reducible_and_instances exact (congrArg (ev k t) (completedTensor_right_apply (X := SchwartzBruhat K)
      (Y := P₁) hTensor.choose u p)).trans (hTensor.choose_spec u p k t)
  refine ⟨J, fun p t ↦ ?_, fun p x hx ↦ ?_⟩
  · have heq (k : K) : (ξ k.val : ℂ) * (J p).val (k.val * τ t) =
        (μ₁.real univ : ℂ)⁻¹ * p.val (Real.log (t.val : ℝ)) := by
      exact (congrArg ((ξ k.val : ℂ) * ·) (hJ p k t)).trans
        ((mul_assoc _ _ _).symm.trans (congrArg (· * p.val _) (hu k)))
    exact (integral_congr_ae (.of_forall heq)).trans ((integral_const _).trans
      (Complex.real_smul.trans (mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr measureReal_univ_pos.ne') _)))
  · let k : K := ⟨x / τ (m x), by change m (x / τ (m x)) = 1; rw [map_div, hτ _, div_self']⟩
    have hk : k.val * τ (m x) = x := div_mul_cancel _ _
    exact (congrArg (J p).val hk.symm).trans ((hJ p k (m x)).trans ((congrArg (u k * ·) hx).trans (mul_zero _)))

open scoped ContDiff in
/-- Localize a logarithmic profile without changing its orbit sums: divide a positive
bump on the window by its periodization, then multiply by the periodic lift. -/
private theorem modulatedCompactSupport_isotypicQuotient_equiv_localize (r : ℝ) (hr : 1 < r)
    (C : TopologicalSpace.Compacts ℝ)
    (hc : ∀ x : ℝ, ∃ n : ℤ, x + n * Real.log r ∈ interior (C : Set ℝ)) :
    ∃ T : PositiveRealExponentialDecay univ →L[ℂ] PositiveRealExponentialDecay univ,
      (∀ p x, x ∉ (C : Set ℝ) → (T p).val x = 0) ∧
      ∀ p x, ∑' n : ℤ, (T p).val (x + n * Real.log r) =
        ∑' n : ℤ, p.val (x + n * Real.log r) := by
  obtain ⟨v, hv, hvd, hvr⟩ := isOpen_interior.exists_contDiff_support_eq (n := ⊤)
    (s := interior (C : Set ℝ))
  have hv0 {x : ℝ} (hx : x ∉ (C : Set ℝ)) : v x = 0 :=
    notMem_support.mp fun h ↦ hx (interior_subset (hv ▸ h))
  let w : ContDiffMapSupportedIn ℝ ℂ ⊤ C :=
    ⟨fun x ↦ (v x : ℂ), Complex.ofRealCLM.contDiff.comp hvd, fun x hx ↦ by simp [hv0 hx]⟩
  let P₁ := cyclicPeriodizationCLM r hr
  let l := Real.log r
  have hl : l ≠ 0 := (Real.log_pos hr).ne'
  let lift (p : PositiveRealExponentialDecay univ) (x : ℝ) := cyclicLift (P₁ p) (l⁻¹ * x)
  have hsum (p : PositiveRealExponentialDecay univ) (x : ℝ) :
      HasSum (fun n : ℤ ↦ p.val (x + n * l)) (lift p x) := by
    unfold lift
    rw [inv_mul_eq_div]
    change HasSum _ (cyclicLift (P₁ p) (x / l))
    unfold cyclicLift P₁ cyclicPeriodizationCLM
    exact cyclicPeriodization_hasSum r hr p x
  have hper (p : PositiveRealExponentialDecay univ) (x : ℝ) (n : ℤ) :
      lift p (x + n * l) = lift p x := by
    have he : l⁻¹ * (x + n * l) = l⁻¹ * x + n * 1 := by field_simp
    exact (congrArg (cyclicLift (P₁ p)) he).trans ((cyclicLift_periodic _).int_mul n _)
  let v₀ := compactLogProfileInclusion C w
  have hd (x : ℝ) : (lift v₀ x).re ≠ 0 := by
    have hs : HasSum (fun n : ℤ ↦ v (x + n * l)) (lift v₀ x).re :=
      Complex.reCLM.hasSum (hsum v₀ x)
    obtain ⟨n, hn⟩ := hc x
    have hnn (y : ℝ) : 0 ≤ v y := (hvr (mem_range_self y)).1
    have hp : 0 < v (x + n * l) := lt_of_le_of_ne (hnn _) (mem_support.mp (hv.symm ▸ hn)).symm
    exact ((hs.summable.tsum_pos (fun i ↦ hnn _) n hp).trans_eq hs.tsum_eq).ne'
  have hdc : ContDiff ℝ ∞ (fun x ↦ (lift v₀ x).re) :=
    Complex.reCLM.contDiff.comp ((cyclicLift_contDiff _).comp (contDiff_const.mul contDiff_id))
  let u : ContDiffMapSupportedIn ℝ ℂ ⊤ C := ⟨fun x ↦ (v x / (lift v₀ x).re : ℝ),
    Complex.ofRealCLM.contDiff.comp (hvd.div hdc hd), fun x hx ↦ by simp [hv0 hx]⟩
  let T := (compactLogProfileInclusion C).comp ((windowedCyclicLift C u l⁻¹).comp P₁)
  refine ⟨T, fun p x hx ↦ ((windowedCyclicLift C u l⁻¹) (P₁ p)).zero_on_compl hx, fun p x ↦ ?_⟩
  have hs : HasSum (fun n : ℤ ↦ v (x + n * l)) (lift v₀ x).re := Complex.reCLM.hasSum (hsum v₀ x)
  have he (n : ℤ) : (T p).val (x + n * l) = (v (x + n * l) : ℂ) *
      (((lift v₀ x).re : ℂ)⁻¹ * lift p x) := by
    change ((v _ / (lift v₀ _).re : ℝ) : ℂ) * lift p _ = _
    rw [hper, hper, Complex.ofReal_div, div_eq_mul_inv, mul_assoc]
  have hz : ∑' n : ℤ, (v (x + n * l) : ℂ) = ((lift v₀ x).re : ℂ) :=
    (Complex.ofRealCLM.hasSum hs).tsum_eq
  rw [tsum_congr he, tsum_mul_right, hz, (hsum p x).tsum_eq]
  exact mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hd x)) _

/-- After twisting by the compact component of the generator, the homogeneous orbit
sum is a scalar multiple of the ordinary orbit sum of the compact average profile. -/
private theorem modulatedCompactSupport_isotypicQuotient_equiv_orbit
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (ξ : PontryaginDual G)
    (A : E →L[ℂ] PositiveRealExponentialDecay univ)
    (hA : ∀ f t, (A f).val (Real.log (t.val : ℝ)) =
      ∫ k : K, (ξ k.val : ℂ) * f.val (k.val * τ t) ∂μ₁)
    (η : PontryaginDual ℝ≥0ˣ) (hη : η (m γ) = ξ (τ (m γ) * γ⁻¹))
    (U : PositiveRealExponentialDecay univ ≃L[ℂ] PositiveRealExponentialDecay univ)
    (hU : ∀ (p : PositiveRealExponentialDecay univ) (t : ℝ≥0ˣ),
      (U p).val (Real.log (t.val : ℝ)) = (η t : ℂ) * p.val (Real.log (t.val : ℝ)))
    (f : E) (x : G) :
    modulatedIsotypicPeriodization m γ hm hms hγ μ₁ ξ f (q x) =
      ((ξ (τ (m x) * x⁻¹) : ℂ) / (η (m x) : ℂ)) *
        ∑' n : ℤ, (U (A f)).val (Real.log ((m x).val : ℝ) + n * L) := by
  let d : G →* Circle := ξ.toMonoidHom.comp ((τ.toMonoidHom.comp m.toMonoidHom) * (MonoidHom.id G)⁻¹)
  have hd (y : G) : d y = ξ (τ (m y) * y⁻¹) := rfl
  let b : G →* Circle := d / (η.toMonoidHom.comp m.toMonoidHom)
  have hb (y : G) : b y = d y / η (m y) := rfl
  have hbγ : b γ = 1 := (congrArg (· / η (m γ)) ((hd γ).trans hη.symm)).trans (div_self' _)
  have hbpow (n : ℤ) : b (γ ^ n * x) = b x := by rw [map_mul, map_zpow, hbγ, one_zpow, one_mul]
  have havg (g : G) : (∫ k : K, (ξ k.val : ℂ) * f.val (g * (k.val * τ 1)) ∂μ₁) =
      (d g : ℂ) * (A f).val (Real.log ((m g).val : ℝ)) := by
    have h := modulatedMellin_average_translate m g univ τ hτ μ₁ ξ f 1
    rw [mul_one] at h
    exact h.trans (congrArg ((d g : ℂ) * ·) (hA f (m g)).symm)
  have hterm (n : ℤ) : (∫ k : K, (ξ k.val : ℂ) * f.val (γ ^ n * (k.val * x)) ∂μ₁) =
      (b x : ℂ) * (U (A f)).val (Real.log ((m x).val : ℝ) + n * L) := by
    let g := γ ^ n * x
    have hlog : Real.log ((m g).val : ℝ) = Real.log ((m x).val : ℝ) + n * L := by
      change Real.log ((m (γ ^ n * x)).val : ℝ) = _
      rw [map_mul, map_zpow, modulatedCompactSupport_isotypicQuotient_equiv_log]
    have hpt (k : K) : γ ^ n * (k.val * x) = g * (k.val * τ 1) := by
      rw [map_one, mul_one]; dsimp only [g]; ac_rfl
    have hchar : (d g : ℂ) = (b x : ℂ) * (η (m g) : ℂ) := by
      rw [← hbpow n, hb, Circle.coe_div]
      exact (div_mul_cancel₀ _ (Circle.coe_ne_zero _)).symm
    calc
      _ = ∫ k : K, (ξ k.val : ℂ) * f.val (g * (k.val * τ 1)) ∂μ₁ :=
        integral_congr_ae (.of_forall fun k ↦ congrArg (fun y ↦ (ξ k.val : ℂ) * f.val y) (hpt k))
      _ = (d g : ℂ) * (A f).val (Real.log ((m g).val : ℝ)) := havg g
      _ = _ := (congrArg (· * (A f).val _) hchar).trans ((mul_assoc _ _ _).trans
        (congrArg ((b x : ℂ) * ·) ((hU (A f) (m g)).symm.trans (congrArg (U (A f)).val hlog))))
  have hs := (modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ ξ f x).tsum_eq
  refine hs.symm.trans ((tsum_congr hterm).trans ((tsum_mul_left).trans ?_))
  exact congrArg (· * _) (Circle.coe_div _ _)

/-- Inclusion and a continuous choice of supported representative descend to inverse maps. -/
private theorem modulatedCompactSupport_isotypicQuotient_equiv_of_lift
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (P₁ : X →L[ℂ] Y) (D : Submodule ℂ X) (R : X →L[ℂ] D) (hR : ∀ f, P₁ (R f).val = P₁ f) :
    let N := P₁.ker.comap D.subtype
    ∃ F : (D ⧸ N) ≃L[ℂ] (X ⧸ P₁.ker), ∀ f : D, F (N.mkQ f) = P₁.ker.mkQ f.val := by
  intro N
  let i := N.liftQL (P₁.ker.mkQL.comp D.subtypeL) (fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr hf)
  let j := P₁.ker.liftQL (N.mkQL.comp R) (fun f hf ↦ (Submodule.Quotient.mk_eq_zero _).mpr
    (show P₁ (R f).val = 0 from (hR f).trans hf))
  refine ⟨ContinuousLinearEquiv.equivOfInverse i j ?_ ?_, fun _ ↦ rfl⟩
  · intro z
    obtain ⟨f, rfl⟩ := N.mkQ_surjective z
    apply (Submodule.Quotient.eq N).mpr
    change P₁ ((R f.val).val - f.val) = 0
    rw [map_sub, hR, sub_self]
  · intro z
    obtain ⟨f, rfl⟩ := P₁.ker.mkQ_surjective z
    apply (Submodule.Quotient.eq P₁.ker).mpr
    change P₁ ((R f).val - f) = 0
    rw [map_sub, hR, sub_self]

include hB in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. The supported
homogeneous quotient is identified with the full quotient by inclusion.
Deviation: The interior of the compact module window must cover the quotient.
Every strict-width interval in part (2) satisfies this condition. -/
theorem modulatedCompactSupport_isotypicQuotient_equiv
    (hcover : (QuotientGroup.mk' (Subgroup.zpowers γ)) '' (m ⁻¹' interior B) =
      (univ : Set (G ⧸ Subgroup.zpowers γ)))
    (ω : PontryaginDual K) :
    let N := (Pχ[ω]).ker.comap (D[B]).subtype
    ∃ F : ((D[B]) ⧸ N) ≃L[ℂ] V[ω],
      ∀ f : D[B], F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by
  let hsec := exists_section_of_surjective hm.1 hms
  let τ := hsec.choose
  have hτ := hsec.choose_spec
  let ξ := χ ω
  let hphase := modulatedCompactSupport_isotypicQuotient_equiv_phase (m γ) hγ (ξ (τ (m γ) * γ⁻¹))
  let η := hphase.choose
  have hη := hphase.choose_spec
  -- Average on the compact fibers, then twist away the phase of a generator step.
  let hA₀ := compactAverage_split m hm univ ordConnected_univ univ_nonempty τ hτ μ₁ ξ
  let A := hA₀.choose
  have hA := hA₀.choose_spec.choose_spec.2
  let hU₀ := scalarProfile_unitary univ ordConnected_univ univ_nonempty η
  let U := hU₀.choose
  have hU := hU₀.choose_spec
  let hwin := modulatedCompactSupport_isotypicQuotient_equiv_window m γ hms B hB hcover
  let C := hwin.choose
  have hC := hwin.choose_spec.1
  have hc := hwin.choose_spec.2
  let hloc := modulatedCompactSupport_isotypicQuotient_equiv_localize
    ((m γ).val : ℝ) (by exact_mod_cast hγ) C hc
  let T := hloc.choose
  have hT₀ := hloc.choose_spec.1
  have hT := hloc.choose_spec.2
  let hJ₀ := modulatedCompactSupport_isotypicQuotient_equiv_profileLift m hm μ₁ τ hτ ξ
  let J := hJ₀.choose
  have hJ := hJ₀.choose_spec
  -- Localize the twisted profile, untwist it, and lift it back to the group.
  let M := U.toContinuousLinearMap.comp A
  let V := U.symm.toContinuousLinearMap.comp (T.comp M)
  let R := J.comp V
  have hUV (f : E) : U (V f) = T (M f) := U.apply_symm_apply _
  have hRJ (f : E) : A (R f) = V f := by
    apply scalarProfile_ext_log univ
    exact fun t ↦ (hA (R f) t).trans (hJ.1 (V f) t)
  have hMR (f : E) : M (R f) = T (M f) := (congrArg U (hRJ f)).trans (hUV f)
  have hmem (f : E) : R f ∈ D[B] := by
    have hsup : support (R f).val ⊆ m ⁻¹' B := by
      apply support_subset_iff'.mpr
      intro x hx
      apply hJ.2 (V f) x
      let t := m x
      let z := Real.log (t.val : ℝ)
      have h0 : (T (M f)).val z = 0 := hT₀ _ z (fun hz ↦ hx ((hC t).mp hz))
      have h1 : (η t : ℂ) * (V f).val z = 0 := (hU (V f) t).symm.trans
        ((congrArg (fun p : PositiveRealExponentialDecay univ ↦ p.val z) (hUV f)).trans h0)
      exact (mul_eq_zero.mp h1).resolve_left (Circle.coe_ne_zero _)
    have hZ := hm.1.isCompact_preimage hB
    exact (mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed _).mpr
      ⟨HasCompactSupport.of_support_subset_isCompact hZ hsup, closure_minimal hsup hZ.isClosed⟩
  let R' := R.codRestrict (D[B]) hmem
  have he (f : E) (x : G) : modulatedIsotypicPeriodization m γ hm hms hγ μ₁ ξ (R f) (q x) =
      modulatedIsotypicPeriodization m γ hm hms hγ μ₁ ξ f (q x) := by
    let y := Real.log ((m x).val : ℝ)
    let s (p : PositiveRealExponentialDecay univ) := ∑' n : ℤ, p.val (y + n * L)
    have hs : s (M (R f)) = s (M f) := (congrArg s (hMR f)).trans (hT _ y)
    have horb := modulatedCompactSupport_isotypicQuotient_equiv_orbit m γ hm hms hγ μ₁ τ hτ
      ξ A hA η hη U hU
    exact (horb (R f) x).trans
      ((congrArg (((ξ (τ (m x) * x⁻¹) : ℂ) / (η (m x) : ℂ)) * ·) hs).trans (horb f x).symm)
  have hR (f : E) : (Pχ[ω]) (R' f).val = (Pχ[ω]) f :=
    Subtype.ext (funext (QuotientGroup.forall_mk.mpr (he f)))
  exact modulatedCompactSupport_isotypicQuotient_equiv_of_lift (Pχ[ω]) (D[B]) R' hR

/-- Restrict a quotient equivalence induced by inclusion, using a continuous map into `J`
which preserves the supported subspace and acts as the identity on `J` modulo `N`. -/
private theorem modulatedCompactSupportStage_isotypicQuotient_image_restrict
    {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (D J : Submodule ℂ X) (p₀ : X →L[ℂ] Y)
    (e : (D ⧸ p₀.ker.comap D.subtype) ≃L[ℂ] (X ⧸ p₀.ker))
    (he : ∀ d : D, e ((p₀.ker.comap D.subtype).mkQ d) = p₀.ker.mkQ d.val)
    (p : X →L[ℂ] X) (hP : ∀ x, p₀ (p x) = p₀ x) (hpD : ∀ x ∈ D, p x ∈ D)
    (hr : (∀ x, p x ∈ J) ∨ (∀ x ∈ J, p x = 0)) :
    let N := p₀.ker
    let W₀ := D ⊓ J
    let i : W₀ →ₗ[ℂ] J := Submodule.inclusion (inf_le_right : W₀ ≤ J)
    let M := N.comap W₀.subtype
    let M' := N.comap J.subtype
    ∃ F : (W₀ ⧸ M) ≃L[ℂ] (J ⧸ M'), ∀ w : W₀, F (M.mkQ w) = M'.mkQ (i w) := by
  intro N W₀ i M M'
  have hrep : ∃ A : X →L[ℂ] J, (∀ d : D, (A d.val).val ∈ D) ∧
      (∀ x ∈ N, (A x).val ∈ N) ∧ ∀ j : J, (A j.val).val - j.val ∈ N := by
    rcases hr with hr | hz
    · exact ⟨p.codRestrict J hr, fun d ↦ hpD d.val d.property,
        fun x hx ↦ (hP x).trans hx, fun j ↦ (map_sub p₀ (p j.val) j.val).trans (sub_eq_zero.mpr (hP j.val))⟩
    · refine ⟨0, fun _ ↦ D.zero_mem, fun _ _ ↦ N.zero_mem, fun j ↦ ?_⟩
      have hj := (hP j.val).symm.trans (congrArg p₀ (hz j.val j.property))
      exact (map_sub p₀ 0 j.val).trans (sub_eq_zero.mpr hj.symm)
  obtain ⟨A, hD, hN, hJ⟩ := hrep
  let iL : W₀ →L[ℂ] J := W₀.subtypeL.codRestrict J (fun w ↦ w.property.2)
  let a : D →L[ℂ] W₀ := ((J.subtypeL.comp A).comp D.subtypeL).codRestrict W₀
    (fun d ↦ ⟨hD d, (A d.val).property⟩)
  let H := M.liftQL (M'.mkQL.comp iL) (fun w hw ↦ (Submodule.Quotient.mk_eq_zero M').mpr hw)
  let U := M'.liftQL (N.mkQL.comp J.subtypeL) (fun j hj ↦ (Submodule.Quotient.mk_eq_zero N).mpr hj)
  let T := (N.comap D.subtype).liftQL (M.mkQL.comp a) (fun d hd ↦
    (Submodule.Quotient.mk_eq_zero M).mpr (hN d.val hd))
  let V := T.comp (e.symm.toContinuousLinearMap.comp U)
  have hv {j : J} {d : D} (hd : N.mkQ d.val = N.mkQ j.val) :
      V (M'.mkQ j) = M.mkQ (a d) := by
    change T (e.symm (N.mkQ j.val)) = _
    rw [← hd, ← he d, e.symm_apply_apply]
    rfl
  refine ⟨ContinuousLinearEquiv.equivOfInverse H V ?_ ?_, fun _ ↦ rfl⟩
  · intro z
    obtain ⟨w, rfl⟩ := M.mkQ_surjective z
    let d : D := ⟨w.val, w.property.1⟩
    change V (M'.mkQ (i w)) = M.mkQ w
    exact (hv (j := i w) (d := d) rfl).trans ((Submodule.Quotient.eq M).mpr (hJ (i w)))
  · intro z
    obtain ⟨j, rfl⟩ := M'.mkQ_surjective z
    obtain ⟨d, hd⟩ := (N.comap D.subtype).mkQ_surjective (e.symm (N.mkQ j.val))
    have hd' : N.mkQ d.val = N.mkQ j.val := (he d).symm.trans (e.toEquiv.eq_symm_apply.mp hd)
    rw [hv hd']
    apply (Submodule.Quotient.eq M').mpr
    have hn := hN _ ((Submodule.Quotient.eq N).mp hd')
    change (A (d.val - j.val)).val ∈ N at hn
    rw [map_sub] at hn
    change (A d.val).val - j.val ∈ N
    exact (sub_add_sub_cancel (A d.val).val (A j.val).val j.val) ▸ N.add_mem hn (hJ j)

private theorem modulatedCompactSupportStage_isotypicQuotient_image_bundle
    {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (T : Submodule ℂ X) (p : X →ₗ[ℂ] T) (hp : Continuous p) :
    ∃ A : X →L[ℂ] X, ∀ f, A f = (p f).val :=
  ⟨T.subtypeL.comp (show X →L[ℂ] T from ⟨p, hp⟩), fun _ ↦ rfl⟩

include hm hms hSC in
/-- Write the compact isotype projection in the same (forward translation) convention as
homogeneous periodization. In particular its value determines each summand of the orbit sum. -/
private theorem modulatedCompactSupportStage_isotypicQuotient_image_projector
    (η : PontryaginDual G) :
    ∃ A : E →L[ℂ] E, (∀ f x, (A f).val x = (μ₁.real univ)⁻¹ •
      ∫ u : K, (η u.val : ℂ) * f.val (u.val * x) ∂μ₁) ∧
      ∀ f, A (A f) = A f := by
  have htrans := exists_modulatedExponentialDecay_translationAction m univ hm hms
    ordConnected_univ univ_nonempty
  refine htrans.elim fun ρ hr ↦ ?_
  have hρ := hr.1
  let ξ : PontryaginDual K := η.comp ⟨(K).subtype, continuous_subtype_val⟩
  let T := actionIsotype (ρ.comp (K).subtype) ξ
  have hp0 := existsUnique_modulatedExponentialDecay_isotypicProjector m univ hm hms
    ordConnected_univ univ_nonempty μ₁ ρ hρ ξ
  refine hp0.elim fun p hp _ ↦ ?_
  have hc := modulatedExponentialDecay_isotypicProjector_continuous m univ hm hms ordConnected_univ
    univ_nonempty μ₁ ρ hρ ξ p hp
  refine (modulatedCompactSupportStage_isotypicQuotient_image_bundle T p hc).elim fun A happ ↦ ?_
  have ht (f : E) (x : G) : twist₀ f x = f.val x := congrFun (modulationWeight_zero m f.val) x
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let ev (x : G) (f : E) := f.val x
  refine ⟨A, fun f x ↦ ?_, fun f ↦ ?_⟩
  · let g (u : K) := (η u.val : ℂ) * f.val (u.val * x)
    have h (u : K) : star (ξ u : ℂ) * twist₀ f (u.val⁻¹ * x) = g u⁻¹ := by
      have e : star (η u.val : ℂ) = (η u.val⁻¹ : ℂ) := by
        rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
      exact congrArg₂ (· * ·) e (ht f (u.val⁻¹ * x))
    have he := congrArg (fun s : SchwartzBruhat G ↦ s x) (hp f zeroUniv)
    have hi := (integral_congr_ae (.of_forall h)).trans (integral_inv_eq_self g μ₁)
    have hv := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ξ (twist₀ f) x).2
    have hval := (ht (p f).val x).symm.trans (he.trans (hv.trans (congrArg ((μ₁.real univ)⁻¹ • ·) hi)))
    with_reducible_and_instances exact (congrArg (ev x) (happ f)).trans hval
  · have he := modulatedExponentialDecay_isotypicProjector_retract m univ hm hms
      ordConnected_univ univ_nonempty μ₁ ρ hρ ξ p hp (p f)
    have hval := congrArg (fun z : T ↦ z.val) he
    with_reducible_and_instances exact (happ (A f)).trans ((congrArg (fun y : E ↦ (p y).val) (happ f)).trans
      (hval.trans (happ f).symm))

/-- Right invariance of Haar measure gives the transformation law of the normalized average. -/
private theorem modulatedCompactSupportStage_isotypicQuotient_image_shift
    (η : PontryaginDual G) (f : G → ℂ) (v : K) (x : G) :
    (μ₁.real univ)⁻¹ • (∫ u : K, (η u.val : ℂ) * f (u.val * (v.val⁻¹ * x)) ∂μ₁) =
      (η v.val : ℂ) * ((μ₁.real univ)⁻¹ • ∫ u : K, (η u.val : ℂ) * f (u.val * x) ∂μ₁) := by
  have he : (∫ u : K, (η u.val : ℂ) * f (u.val * (v.val⁻¹ * x)) ∂μ₁) =
      (η v.val : ℂ) * ∫ u : K, (η u.val : ℂ) * f (u.val * x) ∂μ₁ := by
    rw [← integral_const_mul, ← integral_mul_right_eq_self (μ := μ₁) _ v]
    refine integral_congr_ae (.of_forall fun u ↦ ?_)
    change (η (u * v).val : ℂ) * f ((u * v).val * (v.val⁻¹ * x)) = _
    rw [Subgroup.coe_mul, map_mul η, Circle.coe_mul, mul_assoc u.val, mul_inv_cancel_left]
    ring
  rw [he, Complex.real_smul, Complex.real_smul, mul_left_comm]

/-- Idempotence of the compact projection makes each compact integral, hence the whole
orbit sum, unchanged by projection. -/
private theorem modulatedCompactSupportStage_isotypicQuotient_image_periodize
    (η : PontryaginDual G) (A : E →L[ℂ] E)
    (hA : ∀ f x, (A f).val x = (μ₁.real univ)⁻¹ •
      ∫ u : K, (η u.val : ℂ) * f.val (u.val * x) ∂μ₁)
    (hid : ∀ f, A (A f) = A f) (f : E) :
    modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ η (A f) =
      modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ η f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let avg (v : E) (x : G) := ∫ u : K, (η u.val : ℂ) * v.val (u.val * x) ∂μ₁
  have he (x : G) : avg (A f) x = avg f x := smul_right_injective ℂ
    (inv_ne_zero (measureReal_univ_pos (μ := μ₁)).ne') ((hA (A f) x).symm.trans
      ((congrArg (fun v : E ↦ v.val x) (hid f)).trans (hA f x)))
  have hi (v : E) (n : ℤ) (x : G) :
      (∫ u : K, (η u.val : ℂ) * v.val (γ ^ n * (u.val * x)) ∂μ₁) = avg v (γ ^ n * x) :=
    integral_congr_ae (.of_forall fun u ↦ congrArg (fun t ↦ (η u.val : ℂ) * v.val t)
      (mul_left_comm (γ ^ n) u.val x))
  exact Subtype.ext (funext fun z ↦ tsum_congr fun n ↦
    (hi (A f) n z.out).trans ((he _).trans (hi f n z.out).symm))

include hm hB in
/-- The projection averages only within a module fiber. Its support stays over the same
compact window, whose preimage is compact by properness. -/
private theorem modulatedCompactSupportStage_isotypicQuotient_image_support
    (η : PontryaginDual G) (A : E →L[ℂ] E)
    (hA : ∀ f x, (A f).val x = (μ₁.real univ)⁻¹ •
      ∫ u : K, (η u.val : ℂ) * f.val (u.val * x) ∂μ₁)
    (f : E) (hf : f ∈ D[B]) : A f ∈ D[B] := by
  have hs := ((mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed f).mp hf).2
  have hzero (x : G) (hx : m x ∉ B) (u : K) : (η u.val : ℂ) * f.val (u.val * x) = 0 := by
    have he : m (u.val * x) = m x := (map_mul m _ _).trans
      ((congrArg (· * m x) (show m u.val = 1 from u.property)).trans (one_mul _))
    have hy : m (u.val * x) ∉ B := fun h ↦ hx (he ▸ h)
    have h := image_eq_zero_of_notMem_tsupport (f := f.val) (x := u.val * x) (fun ht ↦ hy (hs ht))
    exact (congrArg ((η u.val : ℂ) * ·) h).trans (mul_zero _)
  have hs' : support (A f).val ⊆ m ⁻¹' B := by
    intro x hx
    by_contra hn
    have hi := integral_congr_ae (μ := μ₁) (.of_forall (hzero x hn))
    have hz := hi.trans (integral_zero K ℂ)
    exact hx ((hA f x).trans ((congrArg ((μ₁.real univ)⁻¹ • ·) hz).trans (smul_zero _)))
  exact (mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed (A f)).mpr
    ⟨HasCompactSupport.of_support_subset_isCompact (hm.1.isCompact_preimage hB) hs',
      closure_minimal hs' (hB.isClosed.preimage m.continuous)⟩

include hk hperp hB in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. On a compact window
whose interior covers the quotient, inclusion identifies the two quotients of
k-invariant functions with their quotient topologies.
Deviation: Uses the interior coverage condition on the window. -/
theorem modulatedCompactSupportStage_isotypicQuotient_image
    (hcover : (QuotientGroup.mk' (Subgroup.zpowers γ)) '' (m ⁻¹' interior B) =
      (univ : Set (G ⧸ Subgroup.zpowers γ)))
    (ω : PontryaginDual K) :
    let J : Submodule ℂ E := (schwartzBruhatInvariantSubmodule k).comap twist₀
    let W₀ := modulatedCompactSupportStage m B k
    let i : W₀ →ₗ[ℂ] J := Submodule.inclusion (inf_le_right : W₀ ≤ J)
    let N := (Pχ[ω]).ker.comap W₀.subtype
    let N' := (Pχ[ω]).ker.comap J.subtype
    ∃ F : (W₀ ⧸ N) ≃L[ℂ] (J ⧸ N'), ∀ f : W₀, F (N.mkQ f) = N'.mkQ (i f) := by
  classical
  intro J
  let η := χ ω
  have hfull := modulatedCompactSupport_isotypicQuotient_equiv m γ hm hms hγ B hB μ₁ χ hcover ω
  refine hfull.elim fun e he ↦ ?_
  have havg := modulatedCompactSupportStage_isotypicQuotient_image_projector m hm hms μ₁ η
  refine havg.elim fun A h ↦ ?_
  have hP := modulatedCompactSupportStage_isotypicQuotient_image_periodize m γ hm hms hγ μ₁ η A h.1 h.2
  have hshift (f : E) (u : K) (x : G) : (A f).val (u.val⁻¹ * x) = (η u.val : ℂ) * (A f).val x :=
    (h.1 f _).trans ((modulatedCompactSupportStage_isotypicQuotient_image_shift m μ₁ η f.val u x).trans
      (congrArg ((η u.val : ℂ) * ·) (h.1 f x)).symm)
  have ht (f : E) (x : G) : twist₀ f x = f.val x := congrFun (modulationWeight_zero m f.val) x
  have hJ (f : E) : f ∈ J ↔ ∀ (x : G) (u : k), f.val (x * u.val) = f.val x :=
    (mem_schwartzBruhatInvariantSubmodule_iff k (twist₀ f)).trans
      (forall_congr' fun x ↦ forall_congr' fun u ↦ iff_of_eq (congrArg₂ Eq (ht f _) (ht f x)))
  have incl := compactSubgroup_le_modulation_ker m k hk
  have hd := modulatedCompactSupportStage_isotypicQuotient_image_support m hm B hB μ₁ η A h.1
  have hres := @modulatedCompactSupportStage_isotypicQuotient_image_restrict E _ _ _ _ S _ _ _
    (D[B]) J (Pχ[ω]) e he A hP hd
  unfold modulatedCompactSupportStage
  with_reducible_and_instances refine hres ?_
  by_cases htriv : ∀ u : k, (η u.val : ℂ) = 1
  · left
    intro f
    refine (hJ _).mpr fun x u ↦ ?_
    let v : K := ⟨(u⁻¹).val, incl (u⁻¹).property⟩
    have hv : v.val⁻¹ * x = x * u.val := (congrArg (· * x) (inv_inv u.val)).trans (mul_comm _ _)
    exact (congrArg (A f).val hv).symm.trans ((hshift f v x).trans
      ((congrArg (· * (A f).val x) (htriv u⁻¹)).trans (one_mul _)))
  · right
    intro j hj
    refine (not_forall.mp htriv).elim fun u hu ↦ ?_
    let v : K := ⟨u.val, incl u.property⟩
    have hz (x : G) : (A j).val x = 0 := by
      have hi (t : K) : j.val (t.val * (u.val⁻¹ * x)) = j.val (t.val * x) :=
        (congrArg j.val (show t.val * (u.val⁻¹ * x) = (t.val * x) * (u⁻¹).val by
          change _ = _ * u.val⁻¹; ac_rfl)).trans ((hJ j).mp hj _ u⁻¹)
      have he := integral_congr_ae (μ := μ₁) (.of_forall fun t : K ↦ congrArg ((η t.val : ℂ) * ·) (hi t))
      exact eq_zero_of_mul_eq_self_left hu ((hshift j v x).symm.trans ((h.1 j _).trans
        ((congrArg ((μ₁.real univ)⁻¹ • ·) he).trans (h.1 j x).symm)))
    exact Subtype.ext (funext hz)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "bχ[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω

private theorem unconditionalBasis_int_of_nat {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (N : Submodule ℂ X) (b : ℤ → StrongDual ℂ (X ⧸ N)) (σ : ℕ ≃ ℤ)
    (h : ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (X ⧸ N)), IsSchauderBasis (b ∘ σ) c ∧
      SchauderBasis.IsUnconditional (b ∘ σ) c) :
    ∃ d : ℤ → StrongDual ℂ (StrongDual ℂ (X ⧸ N)), (∀ i j, d i (b j) = if i = j then 1 else 0) ∧
      ∀ x, HasSum (fun n ↦ d n x • b n) x := by
  obtain ⟨c, hb, hu⟩ := h
  refine ⟨c ∘ σ.symm, fun i j ↦ ?_, fun x ↦ ?_⟩
  · have h : c (σ.symm i) (b (σ (σ.symm j))) =
        (if σ.symm i = σ.symm j then 1 else 0) := hb.1 _ _
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq] using h
  · apply σ.hasSum_iff.mp
    exact (hu x).congr_fun fun n ↦ congrArg (fun k ↦ c k x • b (σ n)) (σ.symm_apply_apply n)

include hχ hτ hμ hν in
/-- Paper: Theorem 4.5.2.3(1), p. 207. The lattice integrals indexed by
the integer frequencies give an unconditional basis of the strong dual of
the homogeneous kernel quotient. -/
theorem modulatedCyclicPairing_int_unconditionalBasis (ω : PontryaginDual K) :
    ∃ c : ℤ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      (∀ m n, c m (bχ[ω] n) = if m = n then 1 else 0) ∧
      ∀ u, HasSum (fun n ↦ c n u • bχ[ω] n) u := by
  let σ := Equiv.intEquivNat.symm
  exact unconditionalBasis_int_of_nat (X := E) (Pχ[ω]).ker bχ[ω] σ
    (modulatedCyclicPairing_unconditionalBasis m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ)

private theorem isCompact_unit_interval (l r : ℝ≥0ˣ) : IsCompact (Icc l r) := by
  let e := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hmon (a b : ℝ≥0ˣ) : e a ≤ e b ↔ a ≤ b := by
    change Real.expOrderIso.symm _ ≤ Real.expOrderIso.symm _ ↔ _
    exact Real.expOrderIso.symm.le_iff_le
  have he : Icc l r = e ⁻¹' Icc (e l) (e r) :=
    Set.ext fun x ↦ and_congr (hmon l x).symm (hmon x r).symm
  exact he ▸ e.isProperMap.isCompact_preimage isCompact_Icc

/-- Transport a primal and dual Schauder basis along a quotient equivalence.
Biorthogonality recovers each dual coordinate by evaluating on its primal basis vector. -/
private theorem modulatedCompactSupport_isotypicQuotient_bases_transport
    {Y₀ X : Type*} [AddCommGroup Y₀] [Module ℂ Y₀] [TopologicalSpace Y₀]
    [IsTopologicalAddGroup Y₀] [ContinuousSMul ℂ Y₀]
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (N : Submodule ℂ Y₀) (e : (Y₀ ⧸ N) ≃L[ℂ] X) (v : ℕ → X) (c : ℕ → StrongDual ℂ X)
    (d : ℕ → StrongDual ℂ (StrongDual ℂ X)) (hb : IsSchauderBasis v c) (ha : SchauderBasis.IsAbsolute v c)
    (hd : IsSchauderBasis c d) (hu : SchauderBasis.IsUnconditional c d) :
    ∃ f : ℕ → Y₀, (∀ n, N.mkQ (f n) = e.symm (v n)) ∧
      let c' := fun n ↦ (c n).comp e.toContinuousLinearMap
      let ev := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (N.mkQ (f n))
      IsSchauderBasis (N.mkQ ∘ f) c' ∧ SchauderBasis.IsAbsolute (N.mkQ ∘ f) c' ∧
        IsSchauderBasis c' ev ∧ SchauderBasis.IsUnconditional c' ev := by
  choose f hf using fun n ↦ N.mkQ_surjective (e.symm (v n))
  refine ⟨f, hf, ?_⟩
  have hfun : N.mkQ ∘ f = e.symm ∘ v := funext hf
  have hcoeff (n : ℕ) (ℓ : StrongDual ℂ X) : d n ℓ = ℓ (v n) := by
    let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (v n)
    have heval (j : ℕ) : ev (d j ℓ • c j) = if j = n then d n ℓ else 0 := by
      change d j ℓ • c j (v n) = _
      have hpair : c j (v n) = if j = n then 1 else 0 := hb.1 j n
      rw [hpair]
      by_cases h : j = n
      · subst j; simp
      · simp [h]
    have hsum := (hu ℓ).mapL ev
    have hs : HasSum (fun j : ℕ ↦ if j = n then d n ℓ else 0) (ℓ (v n)) :=
      hsum.congr_fun fun j ↦ (heval j).symm
    exact (hasSum_ite_eq n _).unique hs
  let D := e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  have hev : (fun n ↦ (d n).comp D.symm.toContinuousLinearMap) =
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (N.mkQ (f n)) := by
    funext n
    apply ContinuousLinearMap.ext
    intro ℓ
    change d n (D.symm ℓ) = ℓ (N.mkQ (f n))
    rw [hcoeff, hf]
    rfl
  refine ⟨hfun ▸ transportSchauderBasis e.symm hb, hfun ▸ transportAbsoluteBasis e.symm ha, ?_⟩
  exact hev ▸ And.intro (transportSchauderBasis D hd) (transportUnconditionalBasis D hu)

include hχ hτ hμ hν hwidth in
/-- Paper: Theorem 4.5.2.3(2), pp. 207–208. Biorthogonal representatives can
be chosen with support in the wide module window. Their classes give an
absolute basis, and the induced integral functionals give an unconditional
basis of the strong dual of the supported quotient.
Deviation: The paper's integer family is expressed in an arbitrary enumeration,
as in Corollary 4.5.1.6. -/
theorem modulatedCompactSupport_isotypicQuotient_bases (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    let N := (Pχ[ω]).ker.comap (D[window]).subtype
    let U := (D[window]) ⧸ N
    ∃ (f : ℕ → D[window]) (c : ℕ → StrongDual ℂ U),
      (∀ n (g : D[window]), c n (N.mkQ g) = bχ[ω] (σ n) ((Pχ[ω]).ker.mkQ g.val)) ∧
      IsSchauderBasis (N.mkQ ∘ f) c ∧
      SchauderBasis.IsAbsolute (N.mkQ ∘ f) c ∧
      let d : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
        fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (N.mkQ (f n))
      IsSchauderBasis c d ∧ SchauderBasis.IsUnconditional c d := by
  intro N U
  have hcover := modulatedCompactSupport_quotient_image_interior m γ hγ a b hwidth
  obtain ⟨e, he⟩ := modulatedCompactSupport_isotypicQuotient_equiv m γ hm hms hγ window
    (isCompact_unit_interval _ _) μ₁ χ hcover ω
  obtain ⟨v, hb, ha, _, d, hd, hu⟩ :=
    quotient_isotype_bases m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ
  obtain ⟨f, _, h⟩ :=
    modulatedCompactSupport_isotypicQuotient_bases_transport N e v (bχ[ω] ∘ σ) d hb ha hd hu
  refine ⟨f, fun n ↦ (bχ[ω] (σ n)).comp e.toContinuousLinearMap, ?_, h⟩
  exact fun n g ↦ congrArg (bχ[ω] (σ n)) (he g)

end Support

/-! ## 4.5.3 Periodization for an open interval containing zero -/

section Interval

variable [MeasurableSpace G] [BorelSpace G]

local notation "S₀" => SchwartzBruhat G

include hγ in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. Counting
measure on the discrete cyclic subgroup is regular Haar measure. -/
theorem modulatedCyclic_countingMeasure :
    (Measure.count : Measure Γ).IsHaarMeasure ∧ (Measure.count : Measure Γ).Regular := by
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  exact ⟨count_isHaarMeasure_of_discreteTopology, count_regular_of_discreteTopology⟩

local notation "cosetPeriodization" => (fun f : S₀ ↦
  letI := (modulatedCyclic_countingMeasure m γ hγ).1
  letI := (modulatedCyclic_countingMeasure m γ hγ).2
  schwartzBruhatCosetIntegral Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ) f)

include hSC in
/-- Paper: Equation (4.5.3.2), p. 208. The coset integral of §D.1.7
with counting measure is linear and continuous on ordinary Schwartz–Bruhat functions. -/
theorem schwartzBruhatCyclicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ cosetPeriodization ∧ Continuous cosetPeriodization := by
  letI := (modulatedCyclic_countingMeasure m γ hγ).1
  letI := (modulatedCyclic_countingMeasure m γ hγ).2
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count
    (modulatedCyclicSubgroup_closed m γ hγ)).elim fun A hA ↦ ?_
  exact Eq.mp (congrArg (fun F : S₀ → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext hA))
    ⟨A.toLinearMap.isLinear, A.continuous⟩

/-- Paper: Equation (4.5.3.2), p. 208. Ordinary Schwartz–Bruhat periodization
is the coset integral with respect to counting measure on the cyclic subgroup. -/
def schwartzBruhatCyclicPeriodization : S₀ →L[ℂ] S :=
  let h := schwartzBruhatCyclicPeriodization_isLinearMap_continuous m γ hγ
  ⟨IsLinearMap.mk' cosetPeriodization h.1, h.2⟩

local notation "P₀" => schwartzBruhatCyclicPeriodization m γ hγ

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. At any lift of
a quotient point the cyclic sum converges to the coset integral. -/
theorem schwartzBruhatCyclicPeriodization_hasSum (f : S₀) (x : G) :
    HasSum (fun n : ℤ ↦ f (γ ^ n * x)) (P₀ f (q x)) := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  exact cyclicCosetIntegral_hasSum m γ hγ f x

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is surjective. -/
theorem schwartzBruhatCyclicPeriodization_surjective : Surjective P₀ := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  exact schwartzBruhatCosetIntegral_surjective Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is open. -/
theorem schwartzBruhatCyclicPeriodization_isOpenMap : IsOpenMap P₀ := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  have hq : IsQuotientMap (P₀).toLinearMap.toAddMonoidHom :=
    schwartzBruhatCosetIntegral_isQuotientMap Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)
  exact (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq).isOpenMap

variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (h0 : 0 ∈ I)

local notation "D" => ModulatedExponentialDecay m I
local notation "zeroI" => (⟨0, h0⟩ : I)
local notation "j₀" => modulatedExponentialDecayTwist m I zeroI
local notation "ΔI" => modulatedCyclicDifference m γ hm hms I hInt (⟨0, h0⟩ : I.Nonempty)

include hSC hm hms hInt in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
At exponent zero the canonical inclusion into ordinary Schwartz–Bruhat
functions is continuous. -/
theorem modulatedExponentialDecay_zeroTwist_continuous :
    Continuous (fun f : D ↦ (j₀ f : S₀)) := by
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  exact (continuous_apply (A := fun _ : I ↦ S₀) zeroI).comp
    (modulatedExponentialDecay_twists_continuous m I hm hInt ⟨0, h0⟩ τ hτ)

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
The zero twist preserves pointwise values and is the injective inclusion
of the interval decay space into ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecay_zeroTwist_injective :
    Injective j₀ ∧ ∀ (f : D) (x : G), j₀ f x = f.val x := by
  have h (f : D) (x : G) : j₀ f x = f.val x := by
    exact (modulatedExponentialDecayTwist_apply m I zeroI f x).trans (by simp)
  refine ⟨fun f g hfg ↦ Subtype.ext (funext fun x ↦ ?_), h⟩
  exact (h f x).symm.trans ((congrArg (fun u : S₀ ↦ u x) hfg).trans (h g x))

/-- Paper: Equation (4.5.3.1), p. 208. Periodization at an interval containing
zero composes the zero twist with ordinary Schwartz–Bruhat periodization. -/
def modulatedIntervalPeriodization : D →L[ℂ] S :=
  let j : D →L[ℂ] S₀ :=
    ⟨j₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  (P₀).comp j

local notation "PI" => modulatedIntervalPeriodization m γ hm hms hγ I hInt h0

/-- Paper: Equation (4.5.3.1), p. 208. At a lift of a quotient point the
orbit series for an interval-decaying function converges to its periodization. -/
theorem modulatedIntervalPeriodization_hasSum (f : D) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) (PI f (q x)) := by
  exact (schwartzBruhatCyclicPeriodization_hasSum m γ hγ (j₀ f) x).congr_fun
    fun n ↦ ((modulatedExponentialDecay_zeroTwist_injective m I h0).2 f (γ ^ n * x)).symm

private theorem fullDecay_to_interval_periodization :
    ∃ i : E →L[ℂ] D, (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      ∀ f, PI (i f) = P f := by
  let incl {A : Type _} [CommGroup A] [TopologicalSpace A] (n : A →ₜ* ℝ≥0ˣ) :
      modulatedExponentialDecaySubmodule n univ →ₗ[ℂ] modulatedExponentialDecaySubmodule n I :=
    Submodule.inclusion fun _ hf ↦ (Submodule.mem_iInf _).mpr fun b ↦
      (Submodule.mem_iInf _).mp hf (⟨b.val, mem_univ _⟩ : (univ : Set ℝ))
  let Good := {k : Subgroup G // IsCompact (k : Set G) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)}
  let finalSeminorms (J : Set ℝ) := {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m J) //
    ∀ k : Good, Continuous (p ∘ modulatedExponentialDecayStageInclusion m J k)}
  let gen (J : Set ℝ) := withGeneratingSeminorms_spec _ (Subtype.val : finalSeminorms J → _)
  let F : E →ₗ[ℂ] D := incl m
  have hc : Continuous F := by
    apply (gen I).continuous_of_continuous_comp F
    intro p
    let v : Seminorm ℂ E := p.val.comp F
    apply (gen univ).continuous_seminorm (⟨v, ?_⟩ : finalSeminorms univ)
    intro k
    let n := quotientModulation m k.val k.property.1
    let Y (J : Set ℝ) := ModulatedExponentialDecayStage m J k
    let stageGen (J : Set ℝ) := withGeneratingSeminorms_spec _
      (fun i : J × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
        i.2.val.comp (modulatedExponentialDecayTwist n J i.1))
    let Fk : Y univ →ₗ[ℂ] Y I := incl n
    have hj : Continuous Fk := by
      apply (stageGen I).continuous_of_continuous_comp Fk
      intro a
      exact (stageGen univ).continuous_seminorm (⟨a.1.val, mem_univ _⟩, a.2)
    exact (p.property k).comp hj
  let i : E →L[ℂ] D := ⟨F, hc⟩
  have comm (f : E) : PI (i f) = P f := by
    refine Subtype.ext (funext fun z ↦ ?_)
    refine QuotientGroup.induction_on z fun x ↦ ?_
    have h₁ := modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 (i f) x
    have h₂ := modulatedPeriodization_hasSum m γ hm hms hγ f x
    exact h₁.unique h₂
  exact ⟨i, fun _ _ ↦ rfl, comm⟩

private theorem intervalPeriodization_isQuotientMap : IsQuotientMap PI := by
  refine (fullDecay_to_interval_periodization m γ hm hms hγ I hInt h0).elim fun i hi ↦ ?_
  have hcomp : (PI) ∘ i = P := funext hi.2
  have hopen := (modulatedPeriodization_isOpenMap m γ hm hms hγ).isQuotientMap
    (P).continuous (modulatedPeriodization_surjective m γ hm hms hγ)
  exact IsQuotientMap.of_comp i.continuous (PI).continuous (Eq.mpr (congrArg IsQuotientMap hcomp) hopen)

include hOpen in
/-- Paper: Corollary 4.5.3.1 and Equations (4.5.3.1)–(4.5.3.2), p. 208.
The periodization is surjective, uniquely characterized by the diagram,
and extends two-sided exponential periodization along the canonical inclusion. -/
theorem modulatedIntervalPeriodization_factorization :
    ∃ i : E →L[ℂ] D,
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f, PI (i f) = P f) ∧
      Surjective PI ∧
      ∀ T : D →L[ℂ] S, T.comp i = P → T = PI := by
  refine (fullDecay_to_interval_periodization m γ hm hms hγ I hInt h0).elim fun i hi ↦ ?_
  have comm := hi.2
  refine ⟨i, hi.1, comm, fun y ↦ ?_, fun T hT ↦ ?_⟩
  · exact (modulatedPeriodization_surjective m γ hm hms hγ y).elim fun f hf ↦ ⟨i f, (comm f).trans hf⟩
  · let := modulatedCyclicSubgroup_closed m γ hγ
    let : T2Space S := schwartzBruhat_t2
    have hd := bruhatCompactSupport_dense_modulatedExponentialDecay m I hm hms hInt ⟨0, h0⟩
    apply DFunLike.coe_injective
    apply hd.equalizer T.continuous (PI).continuous
    funext f
    let g := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms f
    have hg : i g = bruhatCompactSupportToModulatedExponentialDecay m I hm hms f :=
      Subtype.ext (funext (hi.1 g))
    have heq := (DFunLike.congr_fun hT g).trans (comm g).symm
    exact (congrArg T hg).symm.trans (heq.trans (congrArg (PI) hg))

section ProjectivePeriodization

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

open UniformSpace
open scoped TensorProduct

section TensorFlip

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [PolynormableSpace ℂ X] [T2Space X] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]

private def inductiveTensorFlip : InductiveTensor X Y →L[ℂ] InductiveTensor Y X := by
  let F₀ : InductiveTensor X Y →ₗ[ℂ] InductiveTensor Y X := (TensorProduct.comm ℂ X Y).toLinearMap
  have h := (continuous_inductiveTensor_iff
    (LinearMap.id : InductiveTensor Y X →ₗ[ℂ] InductiveTensor Y X)).mp continuous_id
  have hc := @continuous_inductiveTensor_iff X Y _ _ _ _ _ _ _ _ _ _ (InductiveTensor Y X) _ _
    (inferInstanceAs (TopologicalSpace (InductiveTensor Y X)))
    (inferInstanceAs (PolynormableSpace ℂ (InductiveTensor Y X))) (inferInstanceAs (T2Space (InductiveTensor Y X))) F₀
  exact ⟨F₀, hc.mpr (⟨h.2, h.1⟩)⟩

private def projectiveTensorFlip : ProjectiveTensor X Y →L[ℂ] ProjectiveTensor Y X := by
  let F₀ : ProjectiveTensor X Y →ₗ[ℂ] ProjectiveTensor Y X := (TensorProduct.comm ℂ X Y).toLinearMap
  have h := (continuous_projectiveTensor_iff
    (LinearMap.id : ProjectiveTensor Y X →ₗ[ℂ] ProjectiveTensor Y X)).mp continuous_id
  have hc := @continuous_projectiveTensor_iff X Y _ _ _ _ _ _ _ _ _ _ (ProjectiveTensor Y X) _ _
    (inferInstanceAs (TopologicalSpace (ProjectiveTensor Y X)))
    (inferInstanceAs (PolynormableSpace ℂ (ProjectiveTensor Y X))) F₀
  exact ⟨F₀, hc.mpr (h.comp continuous_swap)⟩

private def inductiveProjectiveComparison : InductiveTensor X Y →L[ℂ] ProjectiveTensor X Y :=
  ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩

private theorem completion_tensor_flip_comparison
    (h : ∃ C : Completion (InductiveTensor Y X) →L[ℂ] Completion (ProjectiveTensor Y X),
      (C : _ → _) = @Completion.map (InductiveTensor Y X) _ (ProjectiveTensor Y X) _ id ∧
      Bijective C ∧ ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B) :
    ∃ C : Completion (InductiveTensor X Y) →L[ℂ] Completion (ProjectiveTensor X Y),
      (C : _ → _) = @Completion.map (InductiveTensor X Y) _ (ProjectiveTensor X Y) _ id ∧
      Bijective C ∧ ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  let ci := (inductiveProjectiveComparison (X := X) (Y := Y)).completion
  let cr := (inductiveProjectiveComparison (X := Y) (Y := X)).completion
  let i₀ := inductiveTensorFlip (X := X) (Y := Y)
  let i₁ := inductiveTensorFlip (X := Y) (Y := X)
  let p₀ := projectiveTensorFlip (X := X) (Y := Y)
  let p₁ := projectiveTensorFlip (X := Y) (Y := X)
  have hI (z) : i₁.completion (i₀.completion z) = z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (i₁.completion.continuous.comp i₀.completion.continuous) continuous_id
    | ih x => simp only [ContinuousLinearMap.completion_apply_coe]
              exact congrArg (fun v : InductiveTensor X Y ↦ (v : Completion (InductiveTensor X Y)))
                ((TensorProduct.comm ℂ X Y).symm_apply_apply x)
  have hP (z) : p₁.completion (p₀.completion z) = z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₁.completion.continuous.comp p₀.completion.continuous) continuous_id
    | ih x => simp only [ContinuousLinearMap.completion_apply_coe]
              exact congrArg (fun v : ProjectiveTensor X Y ↦ (v : Completion (ProjectiveTensor X Y)))
                ((TensorProduct.comm ℂ X Y).symm_apply_apply x)
  obtain ⟨C, hc, hj, hb⟩ := h
  have eqC (z) : C z = cr z := congrFun hc z
  have comm₀ (z) : p₀.completion (ci z) = C (i₀.completion z) := by
    rw [eqC]
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₀.completion.continuous.comp ci.continuous) (cr.continuous.comp i₀.completion.continuous)
    | ih x => simp only [ci, cr, ContinuousLinearMap.completion_apply_coe]; rfl
  have comm₁ (z) : p₁.completion (C z) = ci (i₁.completion z) := by
    rw [eqC]
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₁.completion.continuous.comp cr.continuous) (ci.continuous.comp i₁.completion.continuous)
    | ih x => simp only [ci, cr, ContinuousLinearMap.completion_apply_coe]; rfl
  refine ⟨ci, rfl, ⟨?_, ?_⟩, fun B ↦ ⟨?_, fun hh ↦ hh.image ci⟩⟩
  · intro x y hxy
    have he := hj.1 ((comm₀ x).symm.trans ((congrArg p₀.completion hxy).trans (comm₀ y)))
    exact (hI x).symm.trans ((congrArg i₁.completion he).trans (hI y))
  · intro y
    obtain ⟨x, hx⟩ := hj.2 (p₀.completion y)
    exact ⟨i₁.completion x, (comm₁ x).symm.trans ((congrArg p₁.completion hx).trans (hP y))⟩
  · intro hh
    have hem : C '' (i₀.completion '' B) = p₀.completion '' (ci '' B) := by
      rw [image_image, image_image]
      exact congrArg (fun f ↦ f '' B) (funext fun z ↦ (comm₀ z).symm)
    have h₁ := (hb _).mp (hem ▸ hh.image p₀.completion)
    have hel : i₁.completion '' (i₀.completion '' B) = B := by
      rw [image_image, show (fun z ↦ i₁.completion (i₀.completion z)) = id from funext hI, image_id]
    exact Eq.mp (congrArg (IsVonNBounded ℂ) hel) (h₁.image i₁.completion)

end TensorFlip

private theorem periodization_on_bounded_comparison {X Y W Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [T2Space X] [MontelSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul ℂ W] [T2Space W] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (U : Y ≃L[ℂ] X) (J : Y → W)
    (hJ : ∃ C : Y →L[ℂ] W, (C : Y → W) = J ∧ Bijective C ∧
      ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B)
    (F : X →L[ℂ] Z) (hF : IsQuotientMap F) :
    ∃ A : W →ₗ[ℂ] Z, SeqContinuous A ∧ Surjective A ∧ (∀ y, A (J y) = F (U y)) ∧
      ∃ B : Z ≃ₗ[ℂ] (W ⧸ A.ker), SeqContinuous B ∧ ∀ w, B (A w) = A.ker.mkQ w := by
  obtain ⟨C, hJC, hC, hb⟩ := hJ
  let C₀ := C.comp U.symm.toContinuousLinearMap
  let c := LinearEquiv.ofBijective C₀.toLinearMap (hC.comp U.symm.bijective)
  have hbound (B : Set X) (hh : IsVonNBounded ℂ (c '' B)) : IsVonNBounded ℂ B := by
    have h₁ : C '' (U.symm '' B) = c '' B := image_image _ _ _
    have h₂ := (hb _).mp (Eq.mpr (congrArg (IsVonNBounded ℂ) h₁) hh)
    exact Eq.mp (congrArg (IsVonNBounded ℂ) (U.image_symm_image B)) (h₂.image U.toContinuousLinearMap)
  have hs := seqContinuous_symm_of_bounded_comparison c C₀.continuous hbound
  obtain ⟨A, hA, hsur, hf, hinv⟩ := quotient_of_sequential_comparison c C₀.continuous hs F hF
  refine ⟨A, hA, hsur, fun y ↦ ?_, hinv⟩
  have hc : c (U y) = C y := congrArg C (U.symm_apply_apply y)
  exact (congrArg A (hc.trans (congrFun hJC y))).symm.trans (hf _)

open UniformSpace in
open scoped TensorProduct in
/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Periodization on the
projective tensor completion is sequentially continuous and surjective. The
induced bijection has a sequentially continuous inverse.
Deviation: The interval contains zero. The tensor factors are ordered as in
modulatedExponentialDecay_tensor_equiv. General forward continuity fails. -/
theorem modulatedIntervalPeriodization_projective
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (e : Completion (InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)) ≃L[ℂ] D)
    (he : ∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I))
        (h ⊗ₜ[ℂ] p))).val (u.val * τ t) = h u * p.val (Real.log (t.val : ℝ))) :
    let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    ∃ A : Completion TP →ₗ[ℂ] S, SeqContinuous A ∧ Surjective A ∧
      (∀ z : Completion TI, A (@Completion.map TI _ TP _ id z) = PI (e z)) ∧
      ∃ B : S ≃ₗ[ℂ] ((Completion TP) ⧸ A.ker),
        SeqContinuous B ∧ ∀ z, B (A z) = A.ker.mkQ z := by
  intro TI TP
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : T2Space (PositiveRealExponentialDecay I) := (positiveRealExponentialDecay_isEmbedding I ⟨0, h0⟩).t2Space
  have hstrict := modulatedExponentialDecay_strictLF m I hm hInt ⟨0, h0⟩ τ hτ
  let : T2Space D := hstrict.1
  let : MontelSpace ℂ D := (modulatedExponentialDecay_montel m I hm hInt ⟨0, h0⟩ τ hτ).2
  have hq := intervalPeriodization_isQuotientMap m γ hm hms hγ I hInt h0
  have hrev := modulatedExponentialDecay_tensor_comparison_bounded m I hm hInt ⟨0, h0⟩ τ hτ
  have hcomp := completion_tensor_flip_comparison (X := SchwartzBruhat K) (Y := PositiveRealExponentialDecay I) hrev
  let : PolynormableSpace ℂ (Completion TP) := polynormableSpace_completion
  let : ContinuousSMul ℂ (Completion TP) := PolynormableSpace.continuousSMul ℂ _
  have ha := periodization_on_bounded_comparison (X := D) (Y := Completion TI) (W := Completion TP) (Z := S)
    e (@Completion.map TI _
      TP _ id) hcomp PI hq
  with_reducible exact ha

end ProjectivePeriodization

-- TODO(paper-gap): Remark 4.5.1.4, p. 203, calls the forward quotient
-- bijection continuous. For an infinite product of copies of ℤ/2, the
-- quotient Schwartz space admits a continuous seminorm testing derivative
-- order j at the jth coordinate character. On a fixed compact set no single
-- continuous radial seminorm controls all those derivative orders.

-- TODO(paper-gap): In (4.5.3.6) the ordinary Schwartz–Bruhat quotient map
-- has the interval decay space printed in its codomain. On p. 208 the
-- proof uses the equality of the difference image with the pulled-back
-- closed range before justifying it.

/-- Translating a polynomial weight along an arithmetic progression costs at most a polynomial in the index. -/
private theorem intervalPrimitive_weight_bound {V : Type*} [NormedAddCommGroup V]
    (x t : V) (n k : ℕ) :
    1 + ‖x‖ ^ k ≤ (n + 1 : ℝ) ^ k * (2 * (1 + ‖t‖) ^ k) * (1 + ‖x + n • t‖ ^ k) := by
  let R := max 1 ‖x + n • t‖
  have hR : 1 ≤ R := le_max_left ..
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hnp : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hx : ‖x‖ ≤ (n + 1 : ℝ) * (1 + ‖t‖) * R := by
    have h := norm_sub_le (x + n • t) (n • t)
    rw [add_sub_cancel_right] at h
    calc
      _ ≤ R + n * ‖t‖ := h.trans (add_le_add (le_max_right ..) (norm_nsmul_le ..))
      _ ≤ (n + 1 : ℝ) * (1 + ‖t‖) * R := by
        nlinarith [mul_nonneg hnp (norm_nonneg t), mul_le_mul_of_nonneg_left hR (mul_nonneg hnp (norm_nonneg t)), mul_nonneg hnp hR0, mul_nonneg (norm_nonneg t) hR0]
  have hRp : R ^ k ≤ 1 + ‖x + n • t‖ ^ k := by
    dsimp [R]
    rcases le_total 1 ‖x + n • t‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h, one_pow]; exact le_add_of_nonneg_right (by positivity)
  let B := (n + 1 : ℝ) ^ k * (1 + ‖t‖) ^ k * (1 + ‖x + n • t‖ ^ k)
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith [norm_nonneg t]))
    · linarith [pow_nonneg (norm_nonneg (x + n • t)) k]
  have hxB : ‖x‖ ^ k ≤ B := (pow_le_pow_left₀ (norm_nonneg _) hx _).trans (by
    simp only [mul_pow]; dsimp [B]; gcongr)
  calc _ ≤ B + B := add_le_add hB hxB
       _ = _ := by dsimp [B]; ring

/-- Mixed partial derivatives of a translate are translates of the mixed partial derivatives. -/
private theorem intervalPrimitive_partial {d t r : ℕ} {F : Type*} [AddCommGroup F]
    (g : ElementaryLieGroup d t r F) (v) (hv : elementaryCover v g.2.2.1 g.2.2.2 = g)
    (f : ElementaryLieGroup d t r F → ℂ) (β γ) (u) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (fun x ↦ f (g + x)) β γ u a b =
      elementaryPartial f β γ (u + v) (a + g.2.2.1) (b + g.2.2.2) := by
  have h (w) : g + elementaryCover w a b = elementaryCover (w+v) (a+g.2.2.1) (b+g.2.2.2) := by
    rw [add_comm, ← hv]; exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_add _ _ _).symm) rfl)
  simp only [elementaryPartial, h]
  rw [iteratedFDeriv_comp_add_right (f := fun w ↦ f (elementaryCover w (a+g.2.2.1) (b+g.2.2.2))) _ v u]

/-- On an elementary group, polynomial growth of translated seminorms gives convergence of geometrically weighted translates in the Schwartz space. -/
private theorem intervalPrimitive_elementary {d t r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (g : ElementaryLieGroup d t r F) (f : ElementarySchwartz d t r F) (c : ℝ) (hc : 0 < c) (hc' : c < 1) :
    ∃ v : ElementarySchwartz d t r F, ∀ x, HasSum (fun n : ℕ ↦ (c ^ n : ℝ) • f (n • g + x)) (v x) := by
  let V := ElementarySchwartz d t r F
  obtain ⟨semin, hP, hval⟩ := elementarySchwartz_withSeminorms_P1 (m := d) (n := t) (r := r) (F := F)
  obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly (m := d) (n := t) (r := r) (F := F)
  let Gs (n : ℕ) : V := T (n • g, f)
  let s (n : ℕ) : V := ((c : ℂ) ^ n) • Gs n
  let lv (a : Fin r → ℤ) : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 fun i ↦ (a i : ℝ)
  let B (i : ℕ × ℕ × (Fin d → ℕ) × (Fin t → ℕ)) := (2 * (1 + ‖g.1‖) ^ i.1) * (2 * (1 + ‖lv g.2.2.1‖) ^ i.2.1) * semin i f
  have hbound (i) (n : ℕ) : semin i (Gs n) ≤ (n + 1 : ℝ) ^ (i.1 + i.2.1) * B i := by
    apply (ENNReal.ofReal_le_ofReal_iff (by dsimp [B]; positivity)).mp
    rw [hval]
    refine iSup_le fun u ↦ iSup_le fun a ↦ iSup_le fun b ↦ ENNReal.ofReal_le_ofReal ?_
    let z := n • g
    obtain ⟨v, hv⟩ := elementaryCover_surjective z.2.2.1 z.2.2.2 z.1 z.2.1
    have hv' : elementaryCover (z.1,v) z.2.2.1 z.2.2.2 = z := hv
    have he : (Gs n).val = fun x ↦ f (z + x) := funext (hT z f)
    have hpar := intervalPrimitive_partial z (z.1,v) hv' f.val i.2.2.1 i.2.2.2 u a b
    change (1 + ‖u.1‖ ^ i.1) * (1 + ‖lv a‖ ^ i.2.1) * ‖elementaryPartial (Gs n).val _ _ _ _ _‖ ≤ _
    rw [he, hpar]
    let dnorm := ‖elementaryPartial f.val i.2.2.1 i.2.2.2 (u + (z.1,v)) (a + z.2.2.1) (b + z.2.2.2)‖
    have hD : (1 + ‖u.1 + z.1‖ ^ i.1) * (1 + ‖lv (a + z.2.2.1)‖ ^ i.2.1) * dnorm ≤ semin i f := by
      apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
      rw [hval]; exact le_iSup_of_le (u + (z.1,v)) (le_iSup_of_le (a + z.2.2.1) (le_iSup_of_le (b + z.2.2.2) le_rfl))
    have hl : lv a + n • lv g.2.2.1 = lv (a + z.2.2.1) := by
      ext k; change (a k : ℝ) + n • (g.2.2.1 k : ℝ) = ((a k + n • g.2.2.1 k : ℤ) : ℝ); simp
    have ha := intervalPrimitive_weight_bound (lv a) (lv g.2.2.1) n i.2.1
    rw [hl] at ha
    have hx := intervalPrimitive_weight_bound u.1 g.1 n i.1
    let C := (n + 1 : ℝ) ^ (i.1 + i.2.1) * ((2 * (1 + ‖g.1‖) ^ i.1) * (2 * (1 + ‖lv g.2.2.1‖) ^ i.2.1))
    calc _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul hx ha (by positivity) (by positivity)) (norm_nonneg _)
         _ = C * ((1 + ‖u.1 + z.1‖ ^ i.1) * (1 + ‖lv (a + z.2.2.1)‖ ^ i.2.1) * dnorm) := by dsimp only [C, dnorm]; rw [pow_add, show z.1 = n • g.1 from rfl]; ac_rfl
         _ ≤ _ := by simpa only [C, B, mul_assoc] using mul_le_mul_of_nonneg_left hD (show 0 ≤ C by dsimp [C]; positivity)
  have hs (i) : Summable (fun n ↦ semin i (s n)) := by
    have hs := (summable_pow_mul_geometric_of_norm_lt_one (i.1 + i.2.1) (show ‖c‖ < 1 by rwa [Real.norm_of_nonneg hc.le])).comp_injective Nat.succ_injective
    have hs' : Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ (i.1 + i.2.1) * c ^ n) := by
      simpa only [Function.comp_def, Nat.cast_succ, pow_succ c, mul_assoc, mul_inv_cancel₀ hc.ne', mul_one] using hs.mul_right c⁻¹
    refine (hs'.mul_right (B i)).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) fun n ↦ ?_
    rw [show s n = (c : ℂ)^n • Gs n from rfl, map_smul_eq_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc.le]
    calc _ ≤ c ^ n * _ := mul_le_mul_of_nonneg_left (hbound i n) (pow_nonneg hc.le _)
         _ = _ := by ring
  let : IsTopologicalAddGroup V := hP.isTopologicalAddGroup
  let : UniformSpace V := IsTopologicalAddGroup.rightUniformSpace V
  have : IsUniformAddGroup V := isUniformAddGroup_of_addCommGroup
  obtain ⟨_, _, _, hcomplete⟩ := elementarySchwartz_isFrechet (m := d) (n := t) (r := r) (F := F)
  have hsum : Summable s := by
    apply summable_iff_cauchySeq_finset.mpr
    rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff, hP.tendsto_nhds]
    intro i ε hε
    let j : V →ₗ[ℂ] LocalBanach (semin i) := UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
    have hj (x : V) : ‖j x‖ = semin i x := localBanach_norm_coe (semin i) x
    have hj' : Summable (fun n ↦ j (s n)) := .of_norm (by simp only [hj]; exact hs i)
    have ht := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp hj')
    rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at ht
    filter_upwards [ht ε hε] with z hz
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum, ← map_sub, hj] at hz
    simpa only [sub_zero, Function.comp_apply] using hz
  refine ⟨∑' n, s n, fun x ↦ ?_⟩
  let A : V →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (elementarySchwartzSubmodule d t r F).subtype
  let i : ElementarySchwartzIndex d t r := (0,0,0,0)
  have hcA : Continuous A := by
    apply WithSeminorms.continuous_normedSpace_rng _ elementarySchwartz_withSeminorms A
    refine ⟨{i}, 1, fun u ↦ ?_⟩
    have hu : ‖A u‖ ≤ elementarySchwartzSeminorm i u := by
      change (‖u.val x‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound u.val i).toReal
      apply ENNReal.toReal_mono (u.property.2 i).ne
      rw [show i = (0,0,0,0) from rfl, elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (‖u.val z‖₊ : ENNReal)) x
    simp [Seminorm.comp_apply]
    exact hu.trans (Finset.le_sup (f := elementarySchwartzSeminorm) (Finset.mem_singleton_self i) u)
  let ev : V →L[ℂ] ℂ := ⟨A, hcA⟩
  exact (hsum.hasSum.mapL ev).congr_fun fun n ↦ by
    change c ^ n • f (n • g + x) = (c : ℂ) ^ n * T (n • g, f) x
    rw [hT, Complex.real_smul, Complex.ofReal_pow]

/-- Enlarge the elementary stage to contain the translating element, so that every term and the sum are realized on that same stage. -/
private theorem intervalPrimitive_geometric {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (g : G) (f : SchwartzBruhat G) (c : ℝ) (hc : 0 < c) (hc' : c < 1) :
    (fun x ↦ ∑' n : ℕ, c ^ n • f (g ^ n * x)) ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  obtain ⟨b, hab, hg⟩ : ∃ b : BruhatStructuralPair G, a ≤ b ∧ g ∈ b.val.1 := by
    let I := OpenCompactlyGeneratedSubgroups G
    have hGroups := openCompactlyGeneratedSubgroups_colimit (G := G)
    let : IsDirectedOrder I := hGroups.1
    obtain ⟨J, hgJ⟩ := hGroups.2.1 g
    let aGroup : I := ⟨a.val.1, a.property.1, a.property.2.1⟩
    obtain ⟨H, haH, hJH⟩ := exists_ge_ge aGroup J
    exact ⟨⟨(H.val, a.val.2), H.property.1, H.property.2, a.property.2.2.1, a.property.2.2.2.trans haH⟩,
      ⟨haH, le_rfl⟩, hJH hgJ⟩
  obtain ⟨e'⟩ := b.elementary
  obtain ⟨j, hj, _⟩ := schwartzBruhatStage_transition hab e e'
  let h : b.val.1 := ⟨g, hg⟩
  let coord (y : b.val.1) := (e'.equiv (QuotientGroup.mk y : b.quotient)).toAdd
  obtain ⟨v, hv⟩ := intervalPrimitive_elementary (coord h) (j s) c hc hc'
  apply (mem_schwartzBruhatSubmodule_iff _).mpr
  refine ⟨b, e', v, funext fun x ↦ ?_⟩
  have he (y : G) : f y = schwartzBruhatStageRealization b e' (j s) y := (congrFun hs y).symm.trans (congrFun (hj s) y).symm
  by_cases hx : x ∈ b.val.1
  · let y : b.val.1 := ⟨x, hx⟩
    rw [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    refine (hv (coord y)).tsum_eq.symm.trans (tsum_congr fun n ↦ congrArg (c ^ n • ·) ?_)
    rw [he, schwartzBruhatStageRealization_apply, dite_eq_left (b.val.1.mul_mem (b.val.1.pow_mem hg n) hx)]
    apply congrArg (fun z ↦ j s z)
    change n • coord h + coord y = coord (h ^ n * y)
    let coordHom := e'.equiv.toMonoidHom.comp (QuotientGroup.mk' (b.val.2.subgroupOf b.val.1))
    exact congrArg Multiplicative.toAdd ((coordHom.map_mul (h ^ n) y).trans (congrArg (· * coordHom y) (coordHom.map_pow h n))).symm
  · have hn (n : ℕ) : g ^ n * x ∉ b.val.1 := (b.val.1.mul_mem_cancel_left (x := g ^ n) (y := x) (b.val.1.pow_mem hg n)).not.mpr hx
    rw [schwartzBruhatStageRealization_apply, dite_eq_right hx]
    simp only [he, schwartzBruhatStageRealization_apply, dite_eq_right (hn _), smul_zero, tsum_zero]

/-- A contracting twist turns a one-sided orbit sum into a geometric sum of Schwartz–Bruhat translates. -/
private theorem intervalPrimitive_twist {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ)
    (g : G) (a : ℝ) (ha : 1 < ((m g).val : ℝ) ^ a) (f : G → ℂ)
    (hf : modulationWeight m a f ∈ schwartzBruhatSubmodule G) :
    modulationWeight m a (fun x ↦ ∑' n : ℕ, f (g ^ n * x)) ∈ schwartzBruhatSubmodule G := by
  let u : SchwartzBruhat G := ⟨modulationWeight m a f, hf⟩
  let b := ((m g).val : ℝ)
  have hb : 0 < b := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hba := Real.rpow_pos_of_pos hb a
  have h := intervalPrimitive_geometric g u (b ^ a)⁻¹ (inv_pos.mpr hba) (inv_lt_one_of_one_lt₀ ha)
  refine Eq.mp (congrArg (· ∈ schwartzBruhatSubmodule G) (funext fun x ↦ ?_)) h
  change (∑' n : ℕ, (b ^ a)⁻¹ ^ n • u (g ^ n * x)) = ((((m x).val : ℝ) ^ a : ℝ) : ℂ) * ∑' n : ℕ, f (g ^ n * x)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  change (b ^ a)⁻¹ ^ n • (((((m (g ^ n * x)).val : ℝ) ^ a : ℝ) : ℂ) * f (g ^ n * x)) = _
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
  apply congrArg (fun z : ℝ ↦ (z : ℂ) * f (g ^ n * x))
  simp only [map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, NNReal.coe_mul, NNReal.coe_pow]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul hb.le, mul_comm (n : ℝ) a, Real.rpow_mul_natCast hb.le, inv_pow]
  exact inv_mul_cancel_left₀ (pow_ne_zero _ hba.ne') _

/-- When the bilateral sum vanishes, the forward tail is a primitive and can also be evaluated using the backward tail. -/
private theorem intervalPrimitive_orbit {G : Type*} [CommGroup G] (g : G) (f : G → ℂ)
    (hf : ∀ x, HasSum (fun n : ℤ ↦ f (g ^ n * x)) 0) (x : G) :
    let v := fun y ↦ ∑' n : ℕ, f (g ^ n * y)
    v x - v (g * x) = f x ∧ v x = f x - ∑' n : ℕ, f (g⁻¹ ^ n * x) := by
  intro v
  let z := fun n : ℤ ↦ f (g ^ n * x)
  have hp : Summable (fun n : ℕ ↦ z n) := (hf x).summable.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ ↦ z (-(n + 1))) := (hf x).summable.comp_injective (fun i j h ↦ by omega)
  have hs : Summable (fun n : ℕ ↦ f (g ^ n * x)) := by simpa only [z, zpow_natCast] using hp
  have ht : Summable (fun n : ℕ ↦ f (g⁻¹ ^ n * x)) := by
    simpa only [z, comp_def, zpow_neg, zpow_natCast, inv_pow] using
      (hf x).summable.comp_injective (show Injective (fun n : ℕ ↦ -(n : ℤ)) from neg_injective.comp Nat.cast_injective)
  constructor
  · have he := hs.tsum_eq_zero_add
    simpa only [pow_zero, one_mul, pow_succ, mul_assoc] using sub_eq_of_eq_add he
  · have he := (hp.hasSum.of_nat_of_neg_add_one hn.hasSum).unique (hf x)
    have hzero : v x + (∑' n : ℕ, f (g⁻¹ ^ (n + 1) * x)) = 0 := by
      simpa only [v, z, zpow_natCast, zpow_neg, ← Int.natCast_succ, inv_pow] using he
    rw [ht.tsum_eq_zero_add, pow_zero, one_mul]
    linear_combination hzero

/-- Use the forward tail at positive exponents and the backward tail at negative exponents. Interpolation between two nonzero exponents covers zero. -/
private theorem intervalPrimitive_mem {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ)
    (hm : IsModulation m) (hms : Surjective m) (g : G) (hg : 1 < (m g).val)
    (I : Set ℝ) (ho : IsOpen I) (h0 : 0 ∈ I) (f : modulatedExponentialDecaySubmodule m I)
    (hf : ∀ x, HasSum (fun n : ℤ ↦ f.val (g ^ n * x)) 0) :
    (fun x ↦ ∑' n : ℕ, f.val (g ^ n * x)) ∈ modulatedExponentialDecaySubmodule m I := by
  let v := fun x ↦ ∑' n : ℕ, f.val (g ^ n * x)
  have hg' : 1 < ((m g).val : ℝ) := hg
  have hp (a : ℝ) (ha : a ∈ I) (hpos : 0 < a) : modulationWeight m a v ∈ schwartzBruhatSubmodule G :=
    intervalPrimitive_twist m g a (Real.one_lt_rpow hg' hpos) f.val (modulationWeight_mem_schwartzBruhat m I ⟨a, ha⟩ f)
  have hn (a : ℝ) (ha : a ∈ I) (hneg : a < 0) : modulationWeight m a v ∈ schwartzBruhatSubmodule G := by
    have hinv : 1 < ((m g⁻¹).val : ℝ) ^ a := by
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.inv_rpow (by positivity)]
      exact one_lt_inv₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hg') _) |>.mpr (Real.rpow_lt_one_of_one_lt_of_neg hg' hneg)
    have hfa := modulationWeight_mem_schwartzBruhat m I ⟨a, ha⟩ f
    have he : v = f.val - (fun x ↦ ∑' n : ℕ, f.val (g⁻¹ ^ n * x)) := funext fun x ↦ (intervalPrimitive_orbit g f.val hf x).2
    rw [he, map_sub]; exact sub_mem hfa (intervalPrimitive_twist m g⁻¹ a hinv f.val hfa)
  apply (Submodule.mem_iInf _).mpr
  rintro ⟨a, ha⟩
  change modulationWeight m a v ∈ schwartzBruhatSubmodule G
  rcases lt_trichotomy a 0 with h | rfl | h
  · exact hn a ha h
  · obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds h0)
    obtain ⟨l', hll, hl'⟩ := exists_between hlr.1
    obtain ⟨r', hr', hrr⟩ := exists_between hlr.2
    exact modulationWeight_mem_schwartzBruhat_between m hm hms v l' 0 r' hl' hr'
      (hn l' (hsub ⟨hll, hl'.trans hlr.2⟩) hl') (hp r' (hsub ⟨hlr.1.trans hr', hrr⟩) hr')
  · exact hp a ha h

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), p. 208. On the interval decay space the
periodization kernel is exactly the range of the cyclic difference. -/
theorem modulatedIntervalPeriodization_ker_eq_range :
    (PI).ker = (ΔI).range := by
  apply le_antisymm
  · intro f hf
    have hs (x : G) : HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) 0 := by
      have hp := modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 f x
      have he : PI f (q x) = 0 := congrArg (fun u : S ↦ u (q x)) (show PI f = 0 from hf)
      exact he ▸ hp
    let v : D := ⟨_, intervalPrimitive_mem m hm hms γ hγ I hOpen h0 f hs⟩
    refine ⟨v, Subtype.ext (funext fun x ↦ ?_)⟩
    exact (modulatedCyclicDifference_apply m γ hm hms I hInt ⟨0, h0⟩ v x).trans
      (intervalPrimitive_orbit γ f.val hs x).1
  · rintro _ ⟨f, rfl⟩
    change PI (ΔI f) = 0
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z fun x ↦ ?_)
    have hp := modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 f x
    have ht := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr hp
    apply (modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 (ΔI f) x).unique
    have hs := hp.sub ht
    rw [sub_self] at hs
    refine hs.congr_fun fun n ↦ (modulatedCyclicDifference_apply m γ hm hms I hInt ⟨0, h0⟩ f _).trans ?_
    change f.val _ - f.val (γ * (γ ^ n * x)) = f.val _ - f.val (γ ^ (n + 1) * x)
    rw [zpow_add_one, mul_comm (γ ^ n) γ, mul_assoc]

private theorem fullPeriodization_ker_eq_range : (P).ker = (Δ).range := by
  let Pu := modulatedIntervalPeriodization m γ hm hms hγ univ ordConnected_univ (mem_univ 0)
  have h (f : E) (x : G) : P f (q x) = Pu f (q x) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f x).unique
      (modulatedIntervalPeriodization_hasSum m γ hm hms hγ univ ordConnected_univ (mem_univ 0) f x)
  have hs (f : E) : P f = Pu f :=
    Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (h f))
  have hr := modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ univ isOpen_univ ordConnected_univ (mem_univ 0)
  refine SetLike.ext fun f ↦ ?_
  have hmemb := Iff.of_eq (congrArg (fun N : Submodule ℂ E ↦ f ∈ N) hr)
  have hzero : (P f = 0) ↔ (Pu f = 0) := Iff.of_eq (congrArg (· = 0) (hs f))
  exact hzero.trans hmemb

omit [MeasurableSpace G] [BorelSpace G] in
include hγ in
/-- Paper: Proposition 4.5.1.1(6), p. 198. The cyclic difference has closed range, for a
generator of module greater than one as in Situation 4.4.2.3. Without that hypothesis the
statement is false: a rotation by a Liouville number on ℝ_{>0} × S¹ has non-closed range. -/
theorem modulatedCyclicDifference_isClosed_range : IsClosed (range Δ) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  change IsClosed ((Δ).range : Set E)
  rw [← fullPeriodization_ker_eq_range m γ hm hms hγ]
  exact (P).isClosed_ker

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(5), p. 198. The ordinary periodization kernel
is the closure of the image of the cyclic difference. -/
theorem modulatedPeriodization_ker_eq_closure :
    (P).ker = (Δ).range.topologicalClosure := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  have h := fullPeriodization_ker_eq_range m γ hm hms hγ
  exact (IsClosed.submodule_topologicalClosure_eq (s := (P).ker) (P).isClosed_ker).symm.trans
    (congrArg Submodule.topologicalClosure h)

private theorem fullPeriodization_inter_isotype (ω : PontryaginDual K) :
    (P).ker ⊓ H[ω] = (H[ω]).map (Δ).toLinearMap := by
  have h₀ := fullPeriodization_ker_eq_range m γ hm hms hγ
  exact (congrArg (fun N : Submodule ℂ E ↦ N ⊓ H[ω]) h₀).trans
    (modulatedCyclicDifference_range_isotype m γ hm hms ω)

private theorem cyclicDifference_homogeneous_iff {A : Type*} [CommGroup A] (γ : A) (f : A → ℂ)
    (hs : ∀ x, Summable fun n : ℤ ↦ f (γ ^ n * x)) (k : A) (c : ℂ) :
    (∀ x, f (k * x) - f (γ * (k * x)) = c * (f x - f (γ * x))) ↔
      ∀ x, f (k * x) = c * f x := by
  let d (x : A) := f (k * x) - c * f x
  constructor
  · intro h x
    have hinv (z : A) : d (γ * z) = d z := by
      dsimp only [d]
      rw [mul_left_comm k γ]
      linear_combination -(h z)
    have hconst (n : ℕ) : d (γ ^ n * x) = d x := by
      induction n with
      | zero => simp
      | succ n ih => rwa [pow_succ', mul_assoc, hinv]
    have ht (z : A) : Summable (fun n : ℕ ↦ f (γ ^ n * z)) := by
      simpa only [Function.comp_def, zpow_natCast] using (hs z).comp_injective (Nat.cast_injective (R := ℤ))
    have hd : Summable (fun n : ℕ ↦ d (γ ^ n * x)) := by
      simpa only [d, mul_left_comm k] using (ht (k * x)).sub ((ht x).mul_left c)
    exact sub_eq_zero.mp ((summable_const_iff (β := ℕ) (d x)).mp (hd.congr hconst))
  · intro h x
    rw [h x, mul_left_comm γ k, h, mul_sub]

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), pp. 208–209. The intersection of the periodization
kernel with an isotype equals the image of that isotype under the difference map. Global
closedness follows from `modulatedIntervalPeriodization_ker_eq_range` and continuity
of periodization. -/
theorem modulatedIntervalDifference_range_isotype (ω : PontryaginDual K) :
    let H := (actionIsotype ((ρG).comp (K).subtype) ω).comap j₀
    (PI).ker ⊓ H = H.map (ΔI).toLinearMap := by
  intro H
  have val₀ := (modulatedExponentialDecay_zeroTwist_injective m I h0).2
  let homogeneous (g : G → ℂ) :=
    ∀ (u : K) (x : G), g (u.val⁻¹ * x) = (ω u : ℂ) * g x
  have hmem (f : D) : f ∈ H ↔ homogeneous f.val :=
    (mem_schwartzTranslationIsotype_iff m ω (j₀ f)).trans
      (Iff.of_eq (congrArg homogeneous (funext (val₀ f))))
  have iff_diff (f : D) : ΔI f ∈ H ↔ f ∈ H := by
    have hd : (ΔI f).val = fun x ↦ f.val x - f.val (γ * x) :=
      funext (modulatedCyclicDifference_apply m γ hm hms I hInt ⟨0, h0⟩ f)
    refine (hmem _).trans ((Iff.of_eq (congrArg homogeneous hd)).trans (Iff.trans ?_ (hmem f).symm))
    exact forall_congr' fun u ↦ cyclicDifference_homogeneous_iff γ f.val (fun x ↦
      (modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 f x).summable) u.val⁻¹ (ω u)
  have hpre : H.comap (ΔI).toLinearMap = H := Submodule.ext iff_diff
  exact (congrArg (· ⊓ H) (modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ I hOpen hInt h0)).trans
    ((Submodule.map_comap_eq (ΔI).toLinearMap H).symm.trans (congrArg (Submodule.map (ΔI).toLinearMap) hpre))

/-- Paper: Equation (4.5.3.3), p. 208. The cyclic difference on the ordinary
Schwartz–Bruhat space subtracts left translation by the inverse generator. -/
def schwartzBruhatCyclicDifference : S₀ →L[ℂ] S₀ :=
  ContinuousLinearMap.id ℂ S₀ - ρG γ⁻¹

local notation "Δ₀" => schwartzBruhatCyclicDifference γ

/-- Paper: Equation (4.5.3.3), p. 208. The ordinary cyclic difference at x
subtracts the function's value at γx. -/
theorem schwartzBruhatCyclicDifference_apply (f : S₀) (x : G) :
    Δ₀ f x = f x - f (γ * x) := by
  change f x - ρG γ⁻¹ f x = _
  rw [schwartzBruhatTranslationAction_apply, inv_inv]

open scoped ContDiff in
/-- Local uniform summability of all jets gives a smooth sum with termwise jets. -/
private theorem cyclicTail_smoothSeries {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : ℕ → X → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hb : ∀ (x : X) (k : ℕ), ∃ u : ℕ → ℝ, Summable u ∧ ∀ i y, y ∈ Metric.ball x 1 →
      ‖iteratedFDeriv ℝ k (f i) y‖ ≤ u i) :
    ContDiff ℝ ∞ (fun x ↦ ∑' i, f i x) ∧ ∀ k x,
      iteratedFDeriv ℝ k (fun y ↦ ∑' i, f i y) x = ∑' i, iteratedFDeriv ℝ k (f i) x := by
  let jet (k i : ℕ) := iteratedFDeriv ℝ k (f i)
  have hs (x : X) (k : ℕ) : Summable (fun i ↦ jet k i x) :=
    (hb x k).elim fun u hu ↦ .of_norm_bounded hu.1 fun i ↦ hu.2 i x (Metric.mem_ball_self one_pos)
  let p (x : X) (k : ℕ) := ∑' i, jet k i x
  have h : HasFTaylorSeriesUpTo ∞ (fun x ↦ ∑' i, f i x) p := by
    refine ⟨fun x ↦ ?_, fun k hk x ↦ ?_, fun k hk ↦ ?_⟩
    · change (continuousMultilinearCurryFin0 ℝ X ℂ) (∑' i, jet 0 i x) = _
      exact ((continuousMultilinearCurryFin0 ℝ X ℂ).toContinuousLinearEquiv.map_tsum).trans
        (tsum_congr fun i ↦ (hf i).ftaylorSeries.zero_eq x)
    · let c := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) ↦ X) ℂ
      obtain ⟨u, hu, hle⟩ := hb x (k+1)
      have he := c.toContinuousLinearEquiv.map_tsum (f := fun i ↦ jet (k+1) i x) («L» := SummationFilter.unconditional ℕ)
      change HasFDerivAt _ (c.toContinuousLinearEquiv (∑' i, jet (k+1) i x)) x
      rw [he]
      exact hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball x 1).isPreconnected
        (fun i y _ ↦ (hf i).ftaylorSeries.fderiv k hk y) (fun i y hy ↦ (c.norm_map _).le.trans (hle i y hy))
        (Metric.mem_ball_self one_pos) (hs x k) (Metric.mem_ball_self one_pos)
    · rw [continuous_iff_continuousAt]
      intro x
      obtain ⟨u, hu, hle⟩ := hb x k
      have hU := tendstoUniformlyOn_tsum (f := jet k) hu hle
      exact (hU.continuousOn (Frequently.of_forall fun _ ↦ (continuous_finsetSum _ fun i _ ↦
        (hf i).ftaylorSeries.cont k hk).continuousOn)).continuousAt (Metric.ball_mem_nhds x one_pos)
  exact ⟨h.contDiff, fun k x ↦ (h.eq_iteratedFDeriv (by simp) x).symm⟩

/-- Bound the full multilinear derivative on the cover by the weighted coordinate partials. -/
private theorem elementaryJetBound {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (f : ElementarySchwartz m n r F) (k l : ℕ) :
    ∃ C : ℝ, ∀ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) a b,
      (1 + ‖((x.1, WithLp.toLp 2 (fun i ↦ (a i : ℝ))) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))‖)^l *
        ‖iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x‖ ≤ C := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let Y := ElementaryLieGroup m n r F
  let Z := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r)
  let πZ (y : Y) : Z := (y.1, WithLp.toLp 2 (fun i ↦ (y.2.2.1 i : ℝ)))
  let J := Fin m ⊕ Fin n
  let e : J → X := Sum.elim
    (fun i ↦ ((EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin m)), 0))
    (fun i ↦ (0, (EuclideanSpace.single i 1 : EuclideanSpace ℝ (Fin n))))
  let c (v : X) : J → ℝ := Sum.elim (fun j ↦ v.1 j) (fun j ↦ v.2 j)
  have hrepr (v : X) : ∑ j, c v j • e j = v := elementary_coord_repr v
  have hc (v : X) (j : J) : ‖c v j‖ ≤ ‖v‖ := by
    cases j with
    | inl j => exact (PiLp.norm_apply_le v.1 j).trans (norm_fst_le v)
    | inr j => exact (PiLp.norm_apply_le v.2 j).trans (norm_snd_le v)
  choose β γ hβ using fun t : Fin k → J ↦ elementary_iteratedFDeriv_coord_eq (r := r) (F := F) k t
  obtain ⟨p, _, hp⟩ := elementarySchwartz_withSeminorms_P1 (F := F) (m := m) (n := n) (r := r)
  refine ⟨(2:ℝ)^l * ∑ t, p (l,l,β t,γ t) f, fun x a b ↦ ?_⟩
  let y := πZ (elementaryCover x a b)
  change (1 + ‖y‖)^l * _ ≤ _
  let T := iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b)) x
  have hT := norm_multilinear_le_sum_of_repr e c hrepr hc T
  refine (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ (1 + ‖y‖)^l)).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  have h := le_iSup_of_le x (le_iSup_of_le a (le_iSup_of_le b le_rfl))
    (f := fun (x : X) ↦ ⨆ (a : Fin r → ℤ) (b : F), ENNReal.ofReal ((1 + ‖x.1‖^l) *
      (1 + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖^l) *
      ‖elementaryPartial f (β t) (γ t) x a b‖))
  rw [← hp (l,l,β t,γ t) f] at h
  have hb := (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp h
  change (1 + ‖y.1‖^l) * (1 + ‖y.2‖^l) * _ ≤ _ at hb
  rw [show T (fun i ↦ e (t i)) = _ from hβ t f.val a b (f.property.1 a b) x]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2:ℝ)^l))
  rw [← mul_assoc ((2:ℝ)^l)]
  gcongr
  let s := max 1 ‖y‖
  have hs : 1 + ‖y‖ ≤ 2*s := by dsimp [s]; grind
  refine (pow_le_pow_left₀ (by positivity) hs l).trans ?_
  rw [mul_pow]
  gcongr
  change max 1 (max ‖y.1‖ ‖y.2‖) ^ l ≤ _
  rcases le_total ‖y.1‖ ‖y.2‖ with h | h
  all_goals first | rw [max_eq_right h] | rw [max_eq_left h]
  all_goals rw [max_def]; split <;> try rw [one_pow]
  all_goals
    nlinarith [pow_nonneg (norm_nonneg y.1) l, pow_nonneg (norm_nonneg y.2) l,
      mul_nonneg (pow_nonneg (norm_nonneg y.1) l) (pow_nonneg (norm_nonneg y.2) l)]

private theorem elementaryTranslatedJetBound {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (f : ElementarySchwartz m n r F) (k l : ℕ) :
    ∃ C : ℝ, ∀ (d : ElementaryLieGroup m n r F) (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) a b,
      (1 + ‖(((elementaryCover x a b + d).1, WithLp.toLp 2
          (fun i ↦ ((elementaryCover x a b + d).2.2.1 i : ℝ))) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))‖)^l *
        ‖iteratedFDeriv ℝ k (fun z ↦ f (elementaryCover z a b + d)) x‖ ≤ C := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  obtain ⟨C, hC⟩ := elementaryJetBound f k l
  refine ⟨C, fun d x a b ↦ ?_⟩
  obtain ⟨t, ht⟩ := elementaryCover_surjective d.2.2.1 d.2.2.2 d.1 d.2.1
  have he (z : X) : elementaryCover z a b + d =
      elementaryCover (z+(d.1,t)) (a+d.2.2.1) (b+d.2.2.2) :=
    (congrArg (elementaryCover z a b + ·) ht.symm).trans (elementaryCover_add ..)
  simp_rw [he]
  rw [iteratedFDeriv_comp_add_right (f := fun y ↦ f (elementaryCover y (a+d.2.2.1) (b+d.2.2.2)))]
  exact hC (x+(d.1,t)) (a+d.2.2.1) (b+d.2.2.2)

open scoped ContDiff in
/-- The two tails agree up to sign. Each supplies rapid decay in one half-space. -/
private theorem elementaryCyclicPrimitive {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
    (f : ElementarySchwartz m n r F) (v : ElementaryLieGroup m n r F)
    (hf : ∀ y : ElementaryLieGroup m n r F, HasSum (fun i : ℤ ↦ f (y + i • v)) 0) :
    (fun y ↦ ∑' i : ℕ, f (y + i • v)) ∈ elementarySchwartzSubmodule m n r F := by
  classical
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let Y := ElementaryLieGroup m n r F
  let Z := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r)
  let πZ (y : Y) : Z := (y.1, WithLp.toLp 2 (fun i ↦ (y.2.2.1 i : ℝ)))
  let A : Y →+ Z := {
    toFun := πZ
    map_zero' := by refine Prod.ext rfl ?_; ext i; exact Int.cast_zero
    map_add' := fun y z ↦ by refine Prod.ext rfl ?_; ext i; exact Int.cast_add .. }
  let d := A v
  let g (y : Y) := ∑' i : ℕ, f (y + i • v)
  by_cases hd : d = 0
  · -- All translated points lie on a compact orbit closure; summability forces f to vanish.
    have hv : v.1 = 0 := congrArg Prod.fst hd
    have ha : v.2.2.1 = 0 := by
      ext j
      have hh := congrArg (fun w : Z ↦ w.2 j) hd
      exact_mod_cast (show (v.2.2.1 j : ℝ) = 0 from hh)
    let H := (Fin n → AddCircle (1:ℝ)) × F
    let h : H := (v.2.1,v.2.2.2)
    let e : H →+ Y := {
      toFun := fun u ↦ (0,u.1,0,u.2)
      map_zero' := rfl
      map_add' := fun _ _ ↦ Prod.ext (zero_add _).symm (Prod.ext rfl (Prod.ext (zero_add _).symm rfl)) }
    have hev : e h = v := Prod.ext hv.symm (Prod.ext rfl (Prod.ext ha.symm rfl))
    have h0 (y : Y) : f y = 0 := by
      have hs : Summable fun i : ℕ ↦ f (y + i • v) := by
        simpa only [Function.comp_def, natCast_zsmul] using
          (hf y).summable.comp_injective (Nat.cast_injective (R := ℤ))
      have hc : Continuous (fun z : H ↦ f (y + e z)) := (elementarySchwartz_continuous f).comp
        (continuous_const.add (continuous_const.prodMk (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))))
      let : Fact (0 < (1:ℝ)) := ⟨one_pos⟩
      have hcl := (mapClusterPt_zero_atTop_nsmul h).continuousAt_comp hc.continuousAt
      have ht : Tendsto (fun i : ℕ ↦ f (y + e (i • h))) atTop (𝓝 0) := by
        simpa only [map_nsmul, hev] using hs.tendsto_atTop_zero
      obtain ⟨s, hs, hs'⟩ := MapClusterPt.tendsto_subseq hcl
      simpa only [map_zero, add_zero] using tendsto_nhds_unique hs' (ht.comp hs.tendsto_atTop)
    simp only [h0, tsum_zero]
    exact (elementarySchwartzSubmodule m n r F).zero_mem
  have hpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  let w (i : ℕ) := (((i:ℝ)+1)^2)⁻¹
  have hw : Summable w := by
    simpa only [Function.comp_def, Nat.cast_succ] using
      (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective
  let Fp (j : ℕ → ℤ) (a : Fin r → ℤ) (b : F) (i : ℕ) (z : X) := f (elementaryCover z a b + j i • v)
  let J (j : ℕ → ℤ) (k i : ℕ) (x : X) (a : Fin r → ℤ) (b : F) := iteratedFDeriv ℝ k (Fp j a b i) x
  have hshift (y : Y) (z : ℤ) : A (y + z • v) = A y + z • d := by simp only [map_add, map_zsmul, d]
  have hjet (j : ℕ → ℤ) (k l : ℕ) : ∃ C : ℝ, ∀ i (x : X) a b,
      (1 + ‖A (elementaryCover x a b) + j i • d‖)^l * ‖J j k i x a b‖ ≤ C := by
    obtain ⟨C,hC⟩ := elementaryTranslatedJetBound f k l
    exact ⟨C, fun i x a b ↦ hshift (elementaryCover x a b) (j i) ▸ hC (j i • v) x a b⟩
  have hsm (j : ℕ → ℤ) (a : Fin r → ℤ) (b : F) :=
    cyclicTail_smoothSeries (Fp j a b) (fun i ↦ by
      obtain ⟨T, hT⟩ := elementarySchwartz_translate_jointly (m := m) (n := n) (r := r) (F := F)
      have h := (T (j i • v, f)).property.1 a b
      change ContDiff ℝ ∞ (fun z : X ↦ T (j i • v,f) (elementaryCover z a b)) at h
      simpa only [Fp, hT, add_comm (j i • v)] using h)
  have hi_norm (z : ℤ) : ‖z • d‖ = ‖(z : ℝ)‖ * ‖d‖ := by rw [← Int.cast_smul_eq_zsmul ℝ z, norm_smul]
  -- Two extra powers pay for summation over the orbit.
  have hbound (j : ℕ → ℤ) (k l : ℕ) (B R : ℝ) (hR : 0 ≤ R) : ∃ C : ℝ,
      ∀ i (x : X) a b, let y := A (elementaryCover x a b); let s := ‖y + j i • d‖
        (i : ℝ)*‖d‖ ≤ s + R → 1 + ‖y‖ ≤ B*(1+s) →
          (1+‖y‖)^l * ‖J j k i x a b‖ ≤ w i * C := by
    obtain ⟨C, hC⟩ := hjet j k (l+2)
    let scale := (‖d‖ + R + 1)/‖d‖
    refine ⟨B^l * scale^2 * C, ?_⟩
    intro i x a b y s hi hy
    have hs : 0 ≤ s := norm_nonneg _
    have hi' : (i:ℝ) + 1 ≤ scale*(1+s) := by
      dsimp only [scale]; rw [div_mul_eq_mul_div, le_div_iff₀ hpos]; nlinarith
    rw [show w i = (((i:ℝ)+1)^2)⁻¹ from rfl, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    have hB : 0 ≤ B := by
      by_contra! hh
      linarith [mul_neg_of_neg_of_pos hh (show 0 < 1+s by positivity), norm_nonneg y]
    calc
      _ = ((1+‖y‖)^l * ((i:ℝ)+1)^2) * ‖J j k i x a b‖ := by ring
      _ ≤ ((B*(1+s))^l * (scale*(1+s))^2) * ‖J j k i x a b‖ := by gcongr
      _ = (B^l * scale^2) * ((1+s)^(l+2) * ‖J j k i x a b‖) := by rw [mul_pow, mul_pow, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC ..) (by positivity)
  -- On each unit ball, triangle inequalities give a locally uniform summable bound.
  have hseries (j : ℕ → ℤ) (hj : ∀ i : ℕ, (i:ℝ) ≤ ‖(j i : ℝ)‖) (a : Fin r → ℤ) (b : F) := by
    apply hsm j a b
    intro x k
    let R := 1 + ‖x.1‖ + ‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖
    have hR : 0 ≤ R := by dsimp [R]; positivity
    obtain ⟨C,hC⟩ := hbound j k 0 (1+R) R hR
    refine ⟨_, hw.mul_right C, fun i z hz ↦ ?_⟩
    let y := A (elementaryCover z a b)
    have hy : ‖y‖ ≤ R := by
      have h₁ : ‖z.1‖ ≤ ‖x.1‖ + 1 := calc
        _ ≤ ‖z.1-x.1‖ + ‖x.1‖ := by simpa using norm_add_le (z.1-x.1) x.1
        _ ≤ _ := by
          have hh : ‖z.1 - x.1‖ ≤ ‖z - x‖ := norm_fst_le (z - x)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          linarith
      let a' : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun i ↦ (a i : ℝ))
      change max ‖z.1‖ ‖a'‖ ≤ 1 + ‖x.1‖ + ‖a'‖
      rw [max_le_iff]; constructor <;> linarith [norm_nonneg x.1, norm_nonneg a']
    have hi : (i:ℝ)*‖d‖ ≤ ‖y + j i • d‖ + R := calc
      _ ≤ ‖j i • d‖ := hi_norm (j i) ▸ mul_le_mul_of_nonneg_right (hj i) hpos.le
      _ ≤ ‖y + j i • d‖ + ‖y‖ := by simpa using norm_sub_le (y + j i • d) y
      _ ≤ _ := by linarith
    have h₁ : 1+‖y‖ ≤ (1+R)*(1+‖y+j i • d‖) := by nlinarith [norm_nonneg (y+j i • d)]
    simpa only [pow_zero, one_mul] using hC i z a b hi h₁
  let pos (i : ℕ) : ℤ := i
  let neg (i : ℕ) : ℤ := -(i+1)
  have hp (i : ℕ) : (i:ℝ) ≤ ‖(pos i : ℝ)‖ := by simp [pos]
  have hn (i : ℕ) : (i:ℝ) ≤ ‖(neg i : ℝ)‖ := by
    simp [neg]; linarith [neg_le_abs (-1 + -(i:ℝ))]
  let T (j : ℕ → ℤ) a b (x : X) := ∑' i, Fp j a b i x
  have hpT (a : Fin r → ℤ) (b : F) : (fun x : X ↦ g (elementaryCover x a b)) = T pos a b := by
    simp only [g, T, pos, Fp, natCast_zsmul]
  have hpn (a : Fin r → ℤ) (b : F) : T pos a b = -T neg a b := by
    funext x
    let y := elementaryCover x a b
    let h (i : ℤ) := f (y + i • v)
    have H : HasSum h 0 := hf y
    have h₁ := H.summable.comp_injective (Nat.cast_injective (R := ℤ))
    have h₂ := H.summable.comp_injective (show Injective neg from fun i j eq ↦ by dsimp [neg] at eq; omega)
    exact eq_neg_of_add_eq_zero_left ((h₁.hasSum.of_nat_of_neg_add_one h₂.hasSum).unique H)
  have hdec (j : ℕ → ℤ) (hj : ∀ i : ℕ, (i:ℝ) ≤ ‖(j i : ℝ)‖) (k l : ℕ) : ∃ C : ℝ, ∀ (x : X) a b,
      let y := A (elementaryCover x a b)
      (∀ i, ‖j i • d‖ ≤ ‖y + j i • d‖) → (1+‖y‖)^l * ‖iteratedFDeriv ℝ k (T j a b) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hbound j k l 2 0 le_rfl
    refine ⟨∑' i, w i*C, ?_⟩
    intro x a b y hy
    let W := (1+‖y‖)^l
    have hW : 0 < W := by dsimp [W]; positivity
    have hle (i : ℕ) : ‖J j k i x a b‖ ≤ w i*C/W := by
      apply (le_div_iff₀ hW).mpr
      rw [mul_comm]
      apply hC
      · rw [add_zero]; exact ((mul_le_mul_of_nonneg_right (hj i) hpos.le).trans_eq (hi_norm _).symm).trans (hy i)
      · have h₀ : ‖y‖ ≤ ‖y+j i • d‖ + ‖j i • d‖ := by simpa using norm_sub_le (y+j i • d) (j i • d)
        linarith [hy i]
    rw [(hseries j hj a b).2 k x]
    change W * ‖∑' i, J j k i x a b‖ ≤ _
    rw [mul_comm, ← le_div_iff₀ hW]
    exact tsum_of_norm_bounded ((hw.mul_right C).hasSum.div_const W) hle
  -- A norming functional selects the tail that travels away from the origin.
  obtain ⟨ell, hL, hLd⟩ := exists_dual_vector ℝ d hpos.ne'
  have hLle (y : Z) : ‖ell y‖ ≤ ‖y‖ := (ell.le_opNorm y).trans_eq (by rw [hL,one_mul])
  have hfinal (k l : ℕ) : ∃ C : ℝ, ∀ (x : X) a b, (1 + ‖A (elementaryCover x a b)‖)^l *
      ‖iteratedFDeriv ℝ k (fun z ↦ g (elementaryCover z a b)) x‖ ≤ C := by
    obtain ⟨C,hC⟩ := hdec pos hp k l
    obtain ⟨C', hD⟩ := hdec neg hn k l
    refine ⟨max C C', fun x a b ↦ ?_⟩
    let y := A (elementaryCover x a b)
    rw [hpT]
    by_cases h : 0 ≤ ell y
    · refine (hC x a b fun i ↦ ?_).trans (le_max_left ..)
      refine le_trans ?_ (hLle (y + pos i • d))
      rw [hi_norm, map_add, map_zsmul, hLd, Real.norm_eq_abs,
        abs_of_nonneg (by simp [pos] : 0 ≤ (pos i : ℝ)), zsmul_eq_mul, Real.norm_eq_abs]
      exact (le_add_of_nonneg_left h).trans (le_abs_self _)
    · rw [hpn, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
      refine (hD x a b fun i ↦ ?_).trans (le_max_right ..)
      refine le_trans ?_ (hLle (y + neg i • d))
      have hz : (neg i : ℝ) ≤ 0 := by dsimp [neg]; push_cast; linarith
      rw [hi_norm, map_add, map_zsmul, hLd, Real.norm_eq_abs, abs_of_nonpos hz, zsmul_eq_mul, Real.norm_eq_abs, neg_mul]
      change -((neg i:ℝ)*‖d‖) ≤ |ell y + (neg i:ℝ)*‖d‖|
      exact (by linarith : -((neg i:ℝ)*‖d‖) ≤ -(ell y + (neg i:ℝ)*‖d‖)).trans (neg_le_abs _)
  refine ⟨fun a b ↦ ?_, fun ⟨α,β,δ,ε⟩ ↦ ?_⟩
  · change ContDiff ℝ ∞ (fun z ↦ g (elementaryCover z a b))
    rw [hpT]; exact (hseries pos hp a b).1
  let dirs : List X := (List.ofFn fun i ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0)).flatten ++
    (List.ofFn fun i ↦ List.replicate (δ i) (0, EuclideanSpace.single i 1)).flatten
  obtain ⟨C, hC⟩ := hfinal dirs.length ((∑ i, α i) + ∑ i, ε i)
  let dirWeight := ∏ i : Fin dirs.length, ‖dirs.get i‖
  refine lt_of_le_of_lt (b := ENNReal.ofReal (C * dirWeight))
    (iSup_le fun x ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_) ENNReal.ofReal_lt_top
  rw [ENNReal.coe_nnreal_eq, coe_nnNorm]; apply ENNReal.ofReal_le_ofReal
  let y := A (elementaryCover x a b)
  let M := 1+‖y‖
  let Jk := iteratedFDeriv ℝ dirs.length (fun z ↦ g (elementaryCover z a b)) x
  change ‖((∏ i, (x.1 i : ℂ)^α i) * (∏ i, (a i : ℂ)^ε i)) * Jk dirs.get‖ ≤ _
  have hx (i : Fin m) : ‖(x.1 i : ℂ)‖ ≤ M := by
    rw [Complex.norm_real]; exact (PiLp.norm_apply_le x.1 i).trans ((norm_fst_le y).trans (le_add_of_nonneg_left zero_le_one))
  have ha (i : Fin r) : ‖(a i : ℂ)‖ ≤ M := by
    rw [← Complex.ofReal_intCast, Complex.norm_real]; exact (PiLp.norm_apply_le y.2 i).trans ((norm_snd_le y).trans (le_add_of_nonneg_left zero_le_one))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  simp only [norm_mul, norm_prod, norm_pow]
  calc
    _ ≤ ((∏ i, M^α i)*(∏ i, M^ε i)) * (‖Jk‖ * dirWeight) := by
      apply mul_le_mul _ (Jk.le_opNorm _) (norm_nonneg _) (by positivity)
      exact mul_le_mul
        (Finset.prod_le_prod₀ (by intros; positivity) fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hx i) _)
        (Finset.prod_le_prod₀ (by intros; positivity) fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (ha i) _)
        (by positivity) (by positivity)
    _ = M^((∑ i,α i)+∑ i, ε i)*‖Jk‖ * dirWeight := by rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hC x a b) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)

/-- Realize the tail in a single elementary stage containing the translating element. -/
private theorem cyclicSchwartzTail_mem {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (γ : G) (f : SchwartzBruhat G)
    (h0 : ∀ x : G, HasSum (fun n : ℤ ↦ f (γ^n*x)) 0) :
    (fun x ↦ ∑' n : ℕ, f (γ^n*x)) ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨b,e,t,ht⟩ := (mem_schwartzBruhatSubmodule_iff _).mp f.property
  obtain ⟨p,hp,hγ⟩ := exists_bruhatStructuralPair_le_mem b γ
  obtain ⟨u⟩ := p.elementary
  obtain ⟨j,hj,-⟩ := schwartzBruhatStage_transition hp e u
  let s := j t
  let R := schwartzBruhatStageRealization p u
  have hs : R s = f.val := (hj t).trans ht
  let a : p.val.1 := ⟨γ,hγ⟩
  let Y := ElementaryLieGroup u.realDim u.torusDim u.latticeRank u.finiteFactor
  let π : p.val.1 →* Multiplicative Y := u.equiv.toMulEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  have hval (z : SchwartzBruhatStage u) (x : p.val.1) : R z x.val = z (π x).toAdd := by
    rw [schwartzBruhatStageRealization_apply, dite_eq_left x.property]
    rfl
  have hrep (x : p.val.1) : s (π x).toAdd = f x.val := (hval s x).symm.trans (congrFun hs x.val)
  have he (x : p.val.1) (n : ℤ) : s ((π x).toAdd + n • (π a).toAdd) = f (γ^n*x.val) := by
    have h : π (a^n*x) = π x * (π a)^n := by rw [map_mul, map_zpow, mul_comm]
    exact (congrArg (fun y : Multiplicative Y ↦ s y.toAdd) h.symm).trans (hrep (a^n*x))
  have hπ : Surjective π := u.equiv.surjective.comp QuotientGroup.mk_surjective
  have horbit (y : Y) : HasSum (fun n : ℤ ↦ s (y+n • (π a).toAdd)) 0 := by
    obtain ⟨x,hx⟩ := hπ (Multiplicative.ofAdd y)
    exact (h0 x.val).congr_fun fun n ↦ (congrArg (fun z : Multiplicative Y ↦ s (z.toAdd+n • (π a).toAdd)) hx.symm).trans (he x n)
  let g : SchwartzBruhatStage u := ⟨_, elementaryCyclicPrimitive s (π a).toAdd horbit⟩
  apply (mem_schwartzBruhatSubmodule_iff _).mpr
  refine ⟨p,u,g, funext fun x ↦ ?_⟩
  by_cases hx : x ∈ p.val.1
  · refine (hval g ⟨x,hx⟩).trans (tsum_congr fun n ↦ ?_)
    simpa only [natCast_zsmul, zpow_natCast] using he ⟨x,hx⟩ (n:ℤ)
  · have hz (n : ℕ) : f (γ^n*x) = 0 := by
      rw [← show R s (γ^n*x) = f (γ^n*x) from congrFun hs _, schwartzBruhatStageRealization_apply, dite_eq_right]
      exact fun h ↦ hx ((p.val.1.mul_mem_cancel_left (p.val.1.pow_mem hγ n)).mp h)
    rw [schwartzBruhatStageRealization_apply, dite_eq_right hx, funext hz, tsum_zero]

include hγ in
private theorem cyclic_tail_eq (f : SchwartzBruhat G) (x : G) :
    (∑' n : ℕ, f (γ ^ n * x)) - (∑' n : ℕ, f (γ ^ n * (γ * x))) = f x := by
  have h : Summable (fun n : ℕ ↦ f (γ ^ n * x)) := by
    simpa only [Function.comp_def, zpow_natCast] using
      (schwartzBruhatCyclicPeriodization_hasSum m γ hγ f x).summable.comp_injective
        (Nat.cast_injective (R := ℤ))
  rw [h.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, pow_succ, mul_assoc, add_sub_cancel_right]

private theorem cyclicTail_range_le : (Δ₀).range ≤ (P₀).ker := by
  rintro _ ⟨g, rfl⟩
  apply Subtype.ext
  funext z
  refine QuotientGroup.induction_on z fun x ↦ ?_
  have hg := schwartzBruhatCyclicPeriodization_hasSum m γ hγ g x
  have hs := (Equiv.addRight (1 : ℤ)).hasSum_iff.mpr hg
  have hd := hg.sub hs
  apply (schwartzBruhatCyclicPeriodization_hasSum m γ hγ (Δ₀ g) x).unique
  change HasSum (fun n : ℤ ↦ Δ₀ g (γ ^ n * x)) 0
  simpa only [schwartzBruhatCyclicDifference_apply, Function.comp_def, Equiv.coe_addRight,
    zpow_add_one, mul_assoc, mul_left_comm γ, sub_self] using hd

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On ordinary Schwartz–Bruhat
functions the periodization kernel is exactly the range of the cyclic difference. -/
theorem schwartzBruhatCyclicPeriodization_ker_eq_range :
    (P₀).ker = (Δ₀).range := by
  refine le_antisymm (fun f hf ↦ ?_) (cyclicTail_range_le m γ hγ)
  have h0 : P₀ f = 0 := hf
  have hs (x : G) : HasSum (fun n : ℤ ↦ f (γ ^ n * x)) 0 := by
    have h := schwartzBruhatCyclicPeriodization_hasSum m γ hγ f x
    rw [h0] at h
    exact h
  let g : SchwartzBruhat G := ⟨_, cyclicSchwartzTail_mem γ f hs⟩
  exact ⟨g, Subtype.ext (funext fun x ↦ (schwartzBruhatCyclicDifference_apply γ g x).trans
    (cyclic_tail_eq m γ hγ f x))⟩

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On each ordinary
Schwartz–Bruhat isotype the kernel consists of differences of functions of that isotype. -/
theorem schwartzBruhatCyclicDifference_range_isotype (ω : PontryaginDual K) :
    let H := actionIsotype ((ρG).comp (K).subtype) ω
    (P₀).ker ⊓ H = H.map (Δ₀).toLinearMap := by
  intro H
  have hpre : H.comap (Δ₀).toLinearMap = H := by
    apply Submodule.ext
    intro f
    refine (mem_schwartzTranslationIsotype_iff m ω (Δ₀ f)).trans (Iff.trans ?_
      (mem_schwartzTranslationIsotype_iff m ω f).symm)
    simp only [schwartzBruhatCyclicDifference_apply]
    exact forall_congr' fun u ↦ cyclicDifference_homogeneous_iff γ f.val (fun x ↦
      (schwartzBruhatCyclicPeriodization_hasSum m γ hγ f x).summable) u.val⁻¹ (ω u)
  exact (congrArg (· ⊓ H) (schwartzBruhatCyclicPeriodization_ker_eq_range m γ hm hms hγ)).trans
    ((Submodule.map_comap_eq (Δ₀).toLinearMap H).symm.trans (congrArg (Submodule.map (Δ₀).toLinearMap) hpre))

include hOpen hγ in
/-- Paper: Corollary 4.5.3.1, (4.5.3.4)–(4.5.3.6), pp. 208–209. The two
inclusions identify the quotients by the three difference ranges, as used
in Corollary 4.6.3.1. Both maps send each function to its own class. -/
theorem modulatedIntervalDifference_quotient_equivs :
    ∃ (i : E →L[ℂ] D)
      (F : (E ⧸ (Δ).range) ≃L[ℂ] (D ⧸ (ΔI).range))
      (J : (D ⧸ (ΔI).range) ≃L[ℂ] (S₀ ⧸ (Δ₀).range)),
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f : E, F ((Δ).range.mkQ f) = (ΔI).range.mkQ (i f)) ∧
      ∀ g : D, J ((ΔI).range.mkQ g) = (Δ₀).range.mkQ (j₀ g) := by
  refine (modulatedIntervalPeriodization_factorization m γ hm hms hγ I hOpen hInt h0).elim fun i h ↦ ?_
  have hi := h.1
  have hcomp := h.2.1
  have hP : IsQuotientMap P := (modulatedPeriodization_isOpenMap m γ hm hms hγ).isQuotientMap
    (P).continuous (modulatedPeriodization_surjective m γ hm hms hγ)
  have hPI : IsQuotientMap PI := by
    apply IsQuotientMap.of_comp i.continuous (PI).continuous
    exact Eq.mpr (congrArg IsQuotientMap (funext hcomp)) hP
  have hP₀ := (schwartzBruhatCyclicPeriodization_isOpenMap m γ hγ).isQuotientMap
    (P₀).continuous (schwartzBruhatCyclicPeriodization_surjective m γ hγ)
  have hN := fullPeriodization_ker_eq_range m γ hm hms hγ
  refine (exists_quotient_equiv_of_kernel P hP _ hN).elim fun A hA ↦ ?_
  refine (exists_quotient_equiv_of_kernel PI hPI _
    (modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ I hOpen hInt h0)).elim fun B hB ↦ ?_
  refine (exists_quotient_equiv_of_kernel P₀ hP₀ _
    (schwartzBruhatCyclicPeriodization_ker_eq_range m γ hm hms hγ)).elim fun C hC ↦ ?_
  refine ⟨i, A.trans B.symm, B.trans C.symm, hi, fun f ↦ ?_, fun g ↦ ?_⟩
  · exact B.symm_apply_eq.mpr ((hA f).trans ((hcomp f).symm.trans (hB (i f)).symm))
  · exact C.symm_apply_eq.mpr ((hB g).trans (hC (j₀ g)).symm)

end Interval

section IsotypicKernel

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "ωχ" => PontryaginDual.map
  (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

private theorem comap_ker_eq_comap_closure {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousConstSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [T2Space Y]
    (F T : X →L[ℂ] Y) (H N : Submodule ℂ X) (hH : IsClosed (H : Set X))
    (hN : T.ker ⊓ H = N) (c : ℂ) (hc : c ≠ 0) (h : ∀ x : H, F x = c • T x) :
    F.ker.comap H.subtype = N.topologicalClosure.comap H.subtype := by
  have hclosed : (T.ker ⊓ H).topologicalClosure = T.ker ⊓ H :=
    IsClosed.submodule_topologicalClosure_eq (s := T.ker ⊓ H) (T.isClosed_ker.inter hH)
  have hcl := (congrArg Submodule.topologicalClosure hN.symm).trans hclosed
  refine SetLike.ext fun x ↦ ?_
  have hzero : (F x = 0) ↔ (T x = 0) := (Iff.of_eq (congrArg (· = 0) (h x))).trans
    (smul_eq_zero_iff_right hc)
  have hmem := Iff.of_eq (congrArg (fun V : Submodule ℂ X ↦ x.val ∈ V) hcl)
  exact (hzero.trans ⟨fun hx ↦ ⟨hx, x.property⟩, fun hx ↦ hx.1⟩).trans hmem.symm

/-- Paper: Proposition 4.5.1.1(4), p. 198. Inside the isotype, the kernel of
homogeneous periodization is the closure of the differences of isotypic functions.
Deviation: Closure is taken in the ambient decay space and then restricted to
the closed isotype. The linear image already contains the span of the differences. -/
theorem modulatedIsotypicPeriodization_ker_eq_closure :
    (Pχ).ker.comap (H[ωχ]).subtype =
      ((H[ωχ]).map (Δ).toLinearMap).topologicalClosure.comap (H[ωχ]).subtype := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  let H := H[ωχ]
  have hc : IsClosed (H : Set E) := (isClosed_actionIsotype ((ρG).comp (K).subtype) (ωχ)).preimage
    (modulatedExponentialDecay_zeroTwist_continuous m hm hms univ ordConnected_univ (mem_univ 0))
  have hr := fullPeriodization_inter_isotype m γ hm hms hγ (ωχ)
  exact comap_ker_eq_comap_closure (X := E) (Y := S) Pχ P H (H.map (Δ).toLinearMap) hc hr M hM
    (fun v ↦ periodization_on_isotype m γ hm hms hγ μ₁ χ (ωχ) (fun _ ↦ rfl) v.val v.property)

end IsotypicKernel

section QuotientIsotypeInclusion

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)
variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "qK" => (q).comp (K).subtype
local notation "Ψ[" ω "]" => modulatedQuotientIsotypicProjector m γ hm hγ μ₁ ω
local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker

private theorem quotient_submodule_equiv_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (F : X →L[ℂ] Y) (H N : Submodule ℂ X) (A : X → H) (hc : Continuous A)
    (hA : ∀ x, F (A x).val = F x) (hN : ∀ x : H, F x.val = 0 ↔ x.val ∈ N) :
    ∃ U : (H ⧸ N.comap H.subtype) ≃L[ℂ] (X ⧸ F.ker),
      ∀ x : H, U ((N.comap H.subtype).mkQ x) = F.ker.mkQ x.val := by
  let T := F.ker.mkQL.comp H.subtypeL
  have h : (fun x ↦ T (A x)) = F.ker.mkQ := by
    funext x
    exact (Submodule.Quotient.eq F.ker).mpr ((F.map_sub _ _).trans (sub_eq_zero.mpr (hA x)))
  have hq : IsQuotientMap T := IsQuotientMap.of_comp hc T.continuous
    (Eq.mpr (congrArg IsQuotientMap h) F.ker.isQuotientMap_mkQ)
  have hk : T.ker = N.comap H.subtype := SetLike.ext fun x ↦
    (Submodule.Quotient.mk_eq_zero F.ker).trans (hN x)
  exact exists_quotient_equiv_of_kernel T hq _ hk

include hχ in
/-- Paper: Proposition 4.5.1.1(4,6) and Corollary 4.5.1.6, pp. 198, 202–204.
Inclusion identifies the isotype modulo its cyclic differences with the full
decay space modulo homogeneous periodization. -/
theorem modulatedIsotypicPeriodizationQuotient_fromIsotype (ω : PontryaginDual K) :
    let H₀ := H[ω]
    let N := (H₀.map (Δ).toLinearMap).comap H₀.subtype
    ∃ F : (H₀ ⧸ N) ≃L[ℂ] V[ω], ∀ f : H₀, F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by
  intro H₀
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_continuous_decay_average m hm hms μ₁ ω).elim fun A hA ↦ ?_
  have prop (f : E) := homogeneous_average_properties m hm μ₁ ω f (A f) (hA.2 f)
  let B (f : E) : H₀ := ⟨A f, (prop f).1⟩
  have hc : Continuous B := hA.1.subtype_mk _
  have he (f : E) : P (A f) = Ψ[ω] (P f) := by
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    change P (A f) (q x) = M⁻¹ * ∫ u : K, (ω u : ℂ) * P f (qK u * q x) ∂μ₁
    have h := periodization_average_apply m γ hm hms hγ μ₁ ω f (A f) (prop f).2.2 x
    have hπ (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (qK u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    exact h.trans (congrArg (M⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ hπ)))
  have hA' (f : E) : Pχ[ω] (B f).val = Pχ[ω] f :=
    (periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) _ (prop f).1).trans
      ((congrArg (M • ·) (he f)).trans
        (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).2.symm)
  have hi := fullPeriodization_inter_isotype m γ hm hms hγ ω
  have hN (x : H₀) : Pχ[ω] x.val = 0 ↔ x.val ∈ H₀.map (Δ).toLinearMap := by
    have hs := periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) x.val x.property
    have hz := (Iff.of_eq (congrArg (· = 0) hs)).trans (smul_eq_zero_iff_right hM)
    have hx : x.val ∈ (P).ker ⊓ H₀ ↔ x.val ∈ H₀.map (Δ).toLinearMap :=
      Iff.of_eq (congrArg (fun K₀ : Submodule ℂ E ↦ x.val ∈ K₀) hi)
    exact (hz.trans ⟨fun h ↦ ⟨h, x.property⟩, fun h ↦ h.1⟩).trans hx
  exact quotient_submodule_equiv_of_retraction (X := E) (Y := S) Pχ[ω] H₀ (H₀.map (Δ).toLinearMap) B hc hA' hN

end QuotientIsotypeInclusion

section SupportedPrimitive

variable (k : Subgroup G) (a b : ℝ≥0ˣ)
local notation "window" => Icc (b / a) (b * a)
local notation "W" => modulatedCompactSupportStage m window k

private theorem cyclicPrimitive_vanishes_outside {A : Type*} [CommGroup A]
    (w : A →* ℝ≥0ˣ) (t : A) (ht : 1 ≤ w t) (lo hi : ℝ≥0ˣ) (g : A → ℂ)
    (hs : ∀ x, Summable fun n : ℤ ↦ g (t ^ n * x))
    (hf : ∀ x, w x ∉ Icc lo hi → g x = g (t * x)) :
    ∀ x, w x ∉ Icc (w t * lo) hi → g x = 0 := by
  have tail (s : A) (x : A) (h : Summable fun n : ℕ ↦ g (s ^ n * x))
      (hi : ∀ n : ℕ, g (s ^ (n+1) * x) = g (s ^ n * x)) : g x = 0 := by
    have he (n : ℕ) : g (s ^ n * x) = g x := by
      induction n with
      | zero => simp
      | succ n ih => exact (hi n).trans ih
    exact (summable_const_iff (β := ℕ) (g x)).mp (h.congr he)
  intro x hx
  by_cases hh : hi < w x
  · refine tail t x ?_ fun n ↦ ?_
    · simpa only [Function.comp_def, zpow_natCast] using (hs x).comp_injective (Nat.cast_injective (R := ℤ))
    · have hb : hi < w (t ^ n * x) := by
        rw [map_mul, map_pow]
        exact hh.trans_le (le_mul_of_one_le_left' (one_le_pow_of_one_le' ht n))
      simpa only [pow_succ', mul_assoc] using (hf _ fun h ↦ hb.not_ge h.2).symm
  · have hl : w x < w t * lo := lt_of_not_ge fun h ↦ hx ⟨h, le_of_not_gt hh⟩
    have hfirst : (w t)⁻¹ * w x < lo := (inv_mul_lt_iff_lt_mul).mpr hl
    refine tail t⁻¹ x ?_ fun n ↦ ?_
    · have h := (hs x).comp_injective (neg_injective.comp (Nat.cast_injective (R := ℤ)))
      simpa only [Function.comp_def, zpow_neg, zpow_natCast, inv_pow] using h
    · let y := (t⁻¹) ^ (n+1) * x
      have hb : w y < lo := by
        change w ((t⁻¹) ^ (n+1) * x) < lo
        rw [map_mul, map_pow, map_inv, pow_succ, mul_assoc]
        exact (mul_le_of_le_one_left' (pow_le_one' (inv_le_one'.mpr ht) n)).trans_lt hfirst
      have ht' : t * y = (t⁻¹)^n * x := by simp [y, pow_succ', ← mul_assoc]
      exact (hf y fun h ↦ hb.not_ge h.1).trans (congrArg g ht')

-- TODO(paper-gap): Proposition 4.5.2.1(3) has a false support bound. For
-- G = ℝ_{>0}, γ = a > 1 and b = 1, its A is zero. A nonzero bump ψ in
-- (1, γ) gives φ(x) = ψ(x) - ψ(γx) in the kernel with the required support,
-- but a continuous ψ supported in {1} is zero.

/-- Paper: Proposition 4.5.2.1(3), pp. 205–207. A supported kernel element
has a k-invariant primitive supported over the window with its lower endpoint
multiplied by the generator's module.
Deviation: Forward and backward telescoping give this asymmetric interval
in place of the false symmetric bound. -/
theorem modulatedCompactSupportStage_exists_difference
    (f : W) (hf : P f.val = 0) :
    ∃ g : modulatedCompactSupportStage m (Icc (m γ * (b / a)) (b * a)) k,
      Δ g.val = f.val := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have hker : f.val ∈ (P).ker := hf
  have hr : f.val ∈ (Δ).range := Eq.mp (congrArg (fun N : Submodule ℂ E ↦ f.val ∈ N) (fullPeriodization_ker_eq_range m γ hm hms hγ)) hker
  refine hr.elim fun g hg ↦ ?_
  have hdiff (x : G) : g.val x - g.val (γ * x) = f.val.val x :=
    (modulatedCyclicDifference_apply m γ hm hms univ ordConnected_univ univ_nonempty g x).symm.trans
      (congrArg (fun v : E ↦ v.val x) hg)
  have hs (x : G) := (modulatedPeriodization_hasSum m γ hm hms hγ g x).summable
  have hW := (mem_modulatedCompactSupportStage_iff m window k f.val).mp f.property
  have hF := ((mem_modulatedCompactSupportSubmodule_iff m window (isCompact_unit_interval _ _).isClosed f.val).mp hW.1).2
  have hz (x : G) (hx : m x ∉ window) : g.val x = g.val (γ * x) :=
    sub_eq_zero.mp ((hdiff x).trans (notMem_support.mp fun h ↦ hx (hF (subset_tsupport _ h))))
  let J := Icc (m γ * (b / a)) (b * a)
  have hJ : IsCompact (m ⁻¹' J) := hm.1.isCompact_preimage (isCompact_unit_interval _ _)
  have hvan := cyclicPrimitive_vanishes_outside m.toMonoidHom γ
    (show (1 : ℝ≥0ˣ) ≤ m γ from hγ.le) (b / a) (b * a) g.val hs hz
  have hsup : tsupport g.val ⊆ m ⁻¹' J := hJ.isClosed.closure_subset_iff.mpr
    (Function.support_subset_iff'.mpr hvan)
  have hmem := (mem_modulatedCompactSupportSubmodule_iff m J (isCompact_unit_interval _ _).isClosed g).mpr
    ⟨hJ.of_isClosed_subset (isClosed_tsupport _) hsup, hsup⟩
  refine ⟨⟨g, (mem_modulatedCompactSupportStage_iff m J k g).mpr ⟨hmem, fun x u ↦ ?_⟩⟩, hg⟩
  have hi (z : G) : g.val (u.val * z) - g.val (γ * (u.val * z)) =
      (1 : ℂ) * (g.val z - g.val (γ * z)) :=
    (hdiff _).trans ((hW.2 z u).trans ((hdiff z).symm.trans (one_mul _).symm))
  exact ((cyclicDifference_homogeneous_iff γ g.val hs u.val 1).mp hi x).trans (one_mul _)

end SupportedPrimitive

end RiemannMasullo
