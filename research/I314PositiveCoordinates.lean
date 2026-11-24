module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec2
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec4
import Mathlib.LinearAlgebra.Vandermonde
import all RiemannMasullo.AppC_LCTVS.Sec3a_part2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
/-!
# Polynomial coordinate projections and complete strip zero blocks
For Theorem 10.3.2.1(1), pp. 453–455, on a fixed homogeneous component.
All derivative orders at a zero are included. No uniform bound on the
multiplicities is imposed for sufficiency. Conversely, if each site of the
selected component retains at most one jet, universal rank-one summability
forces that same polynomial bound. This gives an equivalence for compact
insertions. At a site with several jets, the necessary zeroth-coordinate
estimate in #7333 compares only with coordinates outside that site.

A separate complete-block criterion below treats multiple jets without splitting
their projections. If their number is uniformly bounded on the selected
component, the universal compact-insertion assertion is equivalent to polynomial
growth of the whole block projections. Rank-one insertions already imply the
bound, and it suffices for all bounded insertions and trace-norm Cauchy tails.
The last theorem expresses this condition intrinsically. It compares every linear
combination of the jets at a site against the span of all jets from other sites.
Whether the actual Hecke zeros satisfy the uniform bound remains open.
-/
@[expose] public noncomputable section
open Function Set Filter MeasureTheory Topology IsDedekindDomain NumberField
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
local notation "pt(" b ", " t ")" => ((b:ℝ):ℂ)+((t:ℝ):ℂ)*Complex.I
local notation "Z(" χ ", " a ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (pt(a+z.2.1,z.2.2))}
local notation "N(" χ ", " a ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (χ (z).val.1)) (pt(a+(z).val.2.1,(z).val.2.2))).untop₀.toNat
local notation "J(" χ ", " a ", " α ", " s ")" => SpectralStripJetIndex (F := F) χ a α s
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs))
local notation "D(" a ", " hα ", " hs ")" => spectralSobolevDualEmbedding F a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs))
local notation "raw(" χ ", " hα ", " hs ", " i ")" => (spectralStripJet_memLp χ hα (le_of_lt (zero_lt_one.trans hs)) i).toLp _
local notation "A(" a ", " hα ", " hs ", " φ ")" => spectralConvolution (F := F) a (neg_le_self hα) (le_of_lt (zero_lt_one.trans hs)) φ
local notation "jet(" z ", " m ")" => ⟨((z).val.1,(z).val.2.1,(z).val.2.2,(m).val),(m).isLt⟩
local notation "hom(" φ ", " η ")" => ∀ (k : C₁) (g : C𝔽), (φ : BruhatCompactSupport C𝔽).val (k.val⁻¹*g) = (η k : ℂ)*(φ : BruhatCompactSupport C𝔽).val g
local notation "X(" χ ", " a ", " α ", " s ", " η ")" => {z : Z(χ,a,α) // z.val.1 = η ∧ 0 < N(χ,a,α,s,z)}
local notation "z₀(" z ")" => (⟨0,(z).property.2⟩ : Fin _)
local notation "form(" L ", " z ")" => L (jet((z).val,z₀(z)))
local notation "b(" z ")" => (z).val.val.2.1
local notation "t(" z ")" => (z).val.val.2.2

/-- In a norm-dense Markushevich system the distance of a coordinate functional
from the span of all the *other coordinates*, including the other jets at its own
site, is the reciprocal norm of its biorthogonal vector. -/
theorem spectralMarkushevich_coordinate_distance {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : I → E) (L : I → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x L) (i : I) :
    Metric.infDist (L i) (Submodule.span ℂ (L '' {j | j ≠ i}) : Set (StrongDual ℂ E)) = ‖x i‖⁻¹ := by
  classical
  let P := Submodule.span ℂ (L '' {j | j ≠ i})
  let ev := ContinuousLinearMap.apply ℂ ℂ (x i)
  have hx : x i ≠ 0 := by
    intro h
    have h' := hb.1 i
    rw [h,map_zero] at h'
    exact zero_ne_one h'
  have hp := norm_pos_iff.mpr hx
  have hP : P ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    exact hb.2.1 i j hj.symm
  change Metric.infDist (L i) (P : Set _) = _
  apply le_antisymm
  · let T := ContinuousLinearMap.id ℂ (StrongDual ℂ E) - ev.smulRight (L i)
    have hT (f : StrongDual ℂ E) : T f ∈ P.topologicalClosure := by
      have h : Submodule.span ℂ (range L) ≤ P.topologicalClosure.comap T.toLinearMap := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j,rfl⟩
        change L j - L j (x i) • L i ∈ P.topologicalClosure
        by_cases hji : j=i
        · subst j; rw [hb.1,one_smul,sub_self]; exact P.topologicalClosure.zero_mem
        · rw [hb.2.1 _ _ (Ne.symm hji),zero_smul,sub_zero]
          exact P.le_topologicalClosure (Submodule.subset_span ⟨j,hji,rfl⟩)
      have h' := (Submodule.span ℂ (range L)).topologicalClosure_minimal h
        (show IsClosed ((P.topologicalClosure.comap T.toLinearMap : Submodule ℂ _) : Set _) by
          exact P.isClosed_topologicalClosure.preimage T.continuous)
      exact h' (hb.2.2.2 f)
    obtain ⟨f,hfn,hfx⟩ := exists_dual_vector ℂ (x i) hp.ne'
    let g : StrongDual ℂ E := (‖x i‖:ℂ)⁻¹ • f
    have hg : g (x i)=1 := by
      change (‖x i‖:ℂ)⁻¹ * f (x i)=1
      rw [hfx]
      exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne')
    have hm := hT (L i-g)
    change L i-g - ((L i) (x i)-g (x i)) • L i ∈ P.topologicalClosure at hm
    rw [hb.1,hg,sub_self,zero_smul,sub_zero] at hm
    rw [←Metric.infDist_closure]
    have hh := Metric.infDist_le_dist_of_mem (x:=L i) (s:=closure (P:Set _)) hm
    rw [dist_eq_norm,sub_sub_cancel] at hh
    simpa [g,norm_smul,hfn] using hh
  · apply (Metric.le_infDist (x:=L i) (s := (P : Set _)) ⟨0,P.zero_mem⟩).mpr
    intro g hg
    have hw : g (x i)=0 := hP hg
    have h := (L i-g).le_opNorm (x i)
    rw [sub_apply,hb.1,hw,sub_zero,norm_one] at h
    rw [dist_eq_norm, ← one_div, div_le_iff₀ hp]
    exact h
#print axioms spectralMarkushevich_coordinate_distance

/-- A single global bound on a closed vertical band. -/
private theorem uniform_mellin_height (ψ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    {q : ℝ} (hq : 0<q) (n : ℕ) (hn : 1≤n) :
    ∃ D≥(0:ℝ), ∀ w : ℂ, |w.re|≤q →
      ‖nuclearityTestMellin ψ φ w‖ * (1+|w.im|)^n ≤ D := by
  obtain ⟨C,hC,hf⟩ := spectralNuclearity_trace_vertical_decay ψ φ (-q) q (by linarith) n hn
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_comap.mp hf)
  obtain ⟨B,hB⟩ := (spectralNuclearityDenominator_closed_invariant_mellin ψ φ).2 (-q) q
  let W := (1+max T 1)^n
  refine ⟨max (C*2^n) (max B 0*W), le_trans (by positivity) (le_max_left _ _),fun w hw ↦ ?_⟩
  have hw' := abs_le.mp hw
  by_cases hy : max T 1 ≤ |w.im|
  · have h₁ := hT _ ((le_max_left _ _).trans hy) w.im rfl w.re hw'
    rw [Complex.re_add_im] at h₁
    have h₂ := (le_max_right _ _).trans hy
    have hp : (1+|w.im|)^n ≤ 2^n*|w.im|^n := by rw [←mul_pow]; gcongr; linarith
    apply le_trans _ (le_max_left _ _)
    calc
      _ ≤ (C/|w.im|^n)*(2^n*|w.im|^n) := mul_le_mul h₁ hp (by positivity) (by positivity)
      _ = _ := by
        have hh : 0 < |w.im| := by linarith
        field_simp
  · apply le_trans _ (le_max_right _ _)
    exact mul_le_mul ((hB w hw'.1 hw'.2).trans (le_max_left _ _))
      (pow_le_pow_left₀ (by positivity) (show 1+|w.im|≤1+max T 1 by linarith) n)
      (by positivity) (le_max_right _ _)

/-- The global rapid decay is uniform on the fixed Mellin circles from Chapter 10. -/
private theorem circle_decay (ψ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    {α R : ℝ} (hα : 0≤α) (hR : 0<R) (n : ℕ) (hn : 1≤n) :
    ∃ D≥(0:ℝ), ∀ z : ℂ, |z.re|≤α → ∀ w∈Metric.sphere z R,
      ‖nuclearityTestMellin ψ φ w‖ ≤ D/(1+|z.im|)^n := by
  obtain ⟨B,hB,hb⟩ := uniform_mellin_height ψ φ (show 0<α+R by linarith) n hn
  refine ⟨B*(1+R)^n,by positivity,fun z hz w hw ↦ ?_⟩
  have he : ‖w-z‖=R := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have h₁ := (Complex.abs_re_le_norm (w-z)).trans he.le
  have h₂ := (Complex.abs_im_le_norm (w-z)).trans he.le
  rw [Complex.sub_re] at h₁
  rw [Complex.sub_im,abs_sub_comm] at h₂
  have hwr : |w.re|≤α+R := by linarith [abs_sub_abs_le_abs_sub w.re z.re]
  have hzi : 1+|z.im|≤(1+|w.im|)*(1+R) := by
    nlinarith [abs_sub_abs_le_abs_sub z.im w.im,mul_nonneg (abs_nonneg w.im) hR.le]
  rw [le_div_iff₀ (by positivity)]
  calc
    _ ≤ ‖nuclearityTestMellin ψ φ w‖*((1+|w.im|)*(1+R))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hzi n) (norm_nonneg _)
    _ = (‖nuclearityTestMellin ψ φ w‖*(1+|w.im|)^n)*(1+R)^n := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb w hwr) (by positivity)

private theorem positive_strip_jet_count (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a α s : ℝ)
    (η : PontryaginDual C₁) :
    Summable (fun z : X(χ,a,α,s,η) ↦ (N(χ,a,α,s,z.val):ℝ)/(1+|t(z)|)^2) := by
  let X := X(χ,a,α,s,η)
  let ord (v : ℂ) := MeromorphicOn.divisor (continuedCompletedHeckeL (χ η)) univ v
  let p (z : X) := pt(a+b(z),t(z))
  have hb (z : X) : N(χ,a,α,s,z.val) ≤ (ord (p z)).toNat := by
    rw [show ord (p z) = (meromorphicOrderAt (continuedCompletedHeckeL (χ η)) (p z)).untop₀ from
      MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ η)).1.meromorphicOn (mem_univ _)]
    unfold spectralStripMultiplicity
    split_ifs <;> simpa only [z.property.1,p,spectralBoundaryMultiplicity] using
      (by first | exact le_refl _ | exact min_le_left _ _ | exact Nat.zero_le _)
  have ho (z : X) : 0<ord (p z) := by
    have h := z.property.2.trans_le (hb z)
    omega
  let Y := {r : ℂ // 0<ord r ∧ |r.re-1/2|<1}
  let e (z : X) : Y := ⟨p z,ho z,by
    obtain ⟨hl,hu⟩ := spectralNuclearity_trace_zero_strip (χ η) (ho z)
    exact abs_lt.mpr ⟨by linarith,by linarith⟩⟩
  have he : Injective e := by
    intro z w h
    have hre := congrArg (fun y : Y ↦ y.val.re) h
    have him := congrArg (fun y : Y ↦ y.val.im) h
    change (p z).re=(p w).re at hre
    change (p z).im=(p w).im at him
    simp [p] at hre him
    exact Subtype.ext (Subtype.ext (Prod.ext (z.property.1.trans w.property.1.symm) (Prod.ext hre him)))
  have H := (spectralNuclearity_trace_zero_count (χ η) 1).comp_injective he
  apply Summable.of_nonneg_of_le (fun _ ↦ by positivity) _ H
  intro z
  change _ ≤ (ord (p z):ℝ)/(1+|(p z).im|)^2
  have him : (p z).im=t(z) := by simp [p]
  rw [him]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h : (N(χ,a,α,s,z.val):ℤ) ≤ ord (p z) := by have h₁ := hb z; have h₂ := ho z; omega
  exact_mod_cast h

private theorem strip_polynomial_coordinates_majorant
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (η : PontryaginDual C₁)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ i : J(χ,a,α,s), i.val.1=η →
      ‖L i‖ * ‖x i‖ ≤ C*(1+|i.val.2.2.1|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) :
    ∃ M : Z(χ,a,α) → ℝ, (∀ z, 0≤M z) ∧
      (∀ z : Z(χ,a,α), ∀ w∈Metric.sphere (pt(z.val.2.1,z.val.2.2)) (2*Real.exp ((4*α+s)/2)),
        ‖∫ g, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M z) ∧
      Summable (fun z : Z(χ,a,α) ↦ M z * ∑ m : Fin (N(χ,a,α,s,z)),
        ‖L (jet(z,m))‖*‖x (jet(z,m))‖) := by
  classical
  obtain ⟨C,hC,d,hx⟩ := hpoly
  let R := 2*Real.exp ((4*α+s)/2)
  obtain ⟨B,hB,hb⟩ := circle_decay (χ η) φ hα (show 0<R by dsimp [R]; positivity) (d+2) (by omega)
  let M (z : Z(χ,a,α)) := if z.val.1=η then B/(1+|z.val.2.2|)^(d+2) else 0
  have hM (z) : 0≤M z := by dsimp only [M]; split_ifs <;> positivity
  refine ⟨M,hM,?_,?_⟩
  · intro z w hw
    by_cases hω : z.val.1=η
    · rw [show M z=_ from ite_eq_left hω,hω]
      simpa [nuclearityTestMellin] using hb (pt(z.val.2.1,z.val.2.2)) (by simpa using abs_le.mpr z.property.1) w hw
    · have H := spectralIsotype_mellin_eq_zero χ hχ hω φ hφ w
      rw [(spectralConvolution_mellin_integrable _ _ _).2] at H
      rw [H,norm_zero]; exact hM z
  · let X := X(χ,a,α,s,η)
    let f (z : Z(χ,a,α)) := M z * ∑ m : Fin (N(χ,a,α,s,z)), ‖L (jet(z,m))‖*‖x (jet(z,m))‖
    have hzero (z : Z(χ,a,α)) (hz : z ∉ range (Subtype.val : X → Z(χ,a,α))) : f z=0 := by
      by_cases he : z.val.1=η
      · have h : N(χ,a,α,s,z)=0 := by
          by_contra hn
          exact hz ⟨⟨z,he,Nat.pos_of_ne_zero hn⟩,rfl⟩
        have : IsEmpty (Fin (N(χ,a,α,s,z))) := ⟨fun m ↦ by have hh := m.isLt; omega⟩
        simp [f]
      · simp [f,M,he]
    change Summable f
    apply (Subtype.val_injective.summable_iff (f:=f) hzero).mp
    apply Summable.of_nonneg_of_le (fun z ↦ mul_nonneg (hM z.val) (Finset.sum_nonneg fun _ _ ↦ by positivity))
      _ ((positive_strip_jet_count χ a α s η).mul_left (B*C))
    intro z
    let r := 1+|t(z)|
    have hr : 0<r := by dsimp only [r]; positivity
    have ht : ∑ m : Fin (N(χ,a,α,s,z.val)), ‖L (jet(z.val,m))‖*‖x (jet(z.val,m))‖ ≤
        (N(χ,a,α,s,z.val):ℝ)*(C*r^d) := by
      calc
        _ ≤ ∑ _m : Fin (N(χ,a,α,s,z.val)), C*r^d := Finset.sum_le_sum (fun m _ ↦ hx (jet(z.val,m)) z.property.1)
        _ = _ := by simp
    change M z.val * _ ≤ (B*C)*((N(χ,a,α,s,z.val):ℝ)/r^2)
    rw [show M z.val = B/r^(d+2) from ite_eq_left z.property.1]
    apply (mul_le_mul_of_nonneg_left ht (div_nonneg hB (pow_pos hr _).le)).trans_eq
    rw [pow_add]; field_simp

/-- On each closed strip, polynomial growth of the individual coordinate projection
norms on one component suffices for absolute summability of all complete zero
blocks of a homogeneous test after every bounded insertion. -/
theorem spectralStrip_polynomial_coordinate_norms_bounded_blocks
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ i : J(χ,a,α,s), i.val.1=η →
      ‖L i‖ * ‖x i‖ ≤ C*(1+|i.val.2.2.1|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) (U : H(a,hα,hs) →L[ℂ] H(a,hα,hs)) :
    Summable (fun z : Z(χ,a,α) ↦ ‖∑ m : Fin (N(χ,a,α,s,z)),
      L (jet(z,m)) (A(a,hα,hs,φ) (U (x (jet(z,m)))))‖) := by
  obtain ⟨M,hM,hcirc,hS⟩ := strip_polynomial_coordinates_majorant χ hχ a hα hs x L η hpoly φ hφ
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ (hS.mul_left (4*‖U‖))
  intro z
  let j (m : Fin (N(χ,a,α,s,z))) : J(χ,a,α,s) := jet(z,m)
  let A := A(a,hα,hs,φ)
  rw [←mul_assoc,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m _
  have H := spectralStripConvolution_jet_norm_le_mellin_circle a hα hs χ L hj φ z m _ (hM z) (hcirc z)
  calc
    _ ≤ ‖(L (j m)).comp A‖ * ‖U (x (j m))‖ := ((L (j m)).comp A).le_opNorm _
    _ ≤ (4*M z*‖L (j m)‖)*(‖U‖*‖x (j m)‖) := mul_le_mul H (U.le_opNorm _) (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (hM z)) (norm_nonneg _))
    _ = _ := by ring

/-- Under the same componentwise polynomial bound, every enumeration of the
complete zero blocks has rectangular Cauchy tails in trace norm. -/
theorem spectralStrip_polynomial_coordinate_norms_trace_cauchy
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ i : J(χ,a,α,s), i.val.1=η →
      ‖L i‖ * ‖x i‖ ≤ C*(1+|i.val.2.2.1|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) (e : Z(χ,a,α) ↪ ℕ × ℕ) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A(a,hα,hs,φ) x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
      (fun z : Z(χ,a,α) ↦ N(χ,a,α,s,z)) (fun z m ↦ jet(z,m))) := by
  obtain ⟨M,hM,hcirc,hS⟩ := strip_polynomial_coordinates_majorant χ hχ a hα hs x L η hpoly φ hφ
  exact spectralStripConvolution_traceCauchy_of_summable_jetNorms a hα hs χ x L hj φ M hM hcirc hS e
#print axioms spectralStrip_polynomial_coordinate_norms_bounded_blocks
#print axioms spectralStrip_polynomial_coordinate_norms_trace_cauchy

open scoped ContDiff
namespace LineModulation
local notation "S" => SchwartzMap ℝ ℂ
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
private def cutBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
private def inletBump : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
private def bumpS (b : ContDiffBump (0 : ℝ)) : S :=
  (b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
private theorem bumpS_compact (b : ContDiffBump (0 : ℝ)) : HasCompactSupport (bumpS b : ℝ → ℂ) :=
  b.hasCompactSupport.comp_left (by simp : ((0:ℝ):ℂ) = 0)
variable (F) in
private def radScale : ℝ := ((normOneIdeleClassTamagawaMeasure F) univ).toReal
private theorem radScale_pos : 0 < radScale F := by
  let ν := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : ν.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  exact ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top ν _)
private def tilt (b x : ℝ) : ℂ := (Real.exp (b*x):ℂ)
private theorem tilt_smooth (b : ℝ) : ContDiff ℝ (⊤:ℕ∞) (tilt b) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
private def stripEval (b t : ℝ) : S →L[ℂ] ℂ :=
  (SchwartzMap.integralCLM ℂ volume).comp (SchwartzMap.smulLeftCLM ℂ
    (fun x ↦ bumpS cutBump x * (tilt b x * phase t x)))
private theorem stripEval_eq (b t : ℝ) (f : S) : stripEval b t f =
    ∫ x : ℝ, bumpS cutBump x * f x * (tilt b x * phase t x) := by
  rw [stripEval,ContinuousLinearMap.comp_apply,SchwartzMap.integralCLM_apply]
  have hh : (fun x ↦ bumpS cutBump x * (tilt b x * phase t x)).HasTemperateGrowth :=
    ((bumpS_compact cutBump).mul_right).hasTemperateGrowth
      ((bumpS cutBump).smooth'.mul ((tilt_smooth b).mul (phase_smooth t)))
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [SchwartzMap.smulLeftCLM_apply_apply hh, smul_eq_mul]; ring
private theorem stripEval_atom_lower {α b : ℝ} (hα : 0≤α) (hb : |b|≤α) (t : ℝ) :
    Real.exp (-α) * (∫ x : ℝ, inletBump x) ≤
      ‖stripEval b t (atom (bumpS inletBump) (bumpS_compact _) t)‖ := by
  let v (x : ℝ) := inletBump x * Real.exp (b*x)
  have he : stripEval b t (atom (bumpS inletBump) (bumpS_compact _) t) = ((∫ x : ℝ,v x : ℝ):ℂ) := by
    rw [stripEval_eq]
    refine Eq.trans ?_ (show (∫ x : ℝ, (v x:ℂ)) = _ from integral_ofReal)
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    change (cutBump x : ℂ) * ((inletBump x : ℂ) * phase (-t) x) * (tilt b x * phase t x) = _
    by_cases hx : inletBump x = 0
    · simp [v,hx]
    have hm := subset_tsupport _ (show x ∈ support inletBump from hx)
    rw [inletBump.tsupport_eq,Metric.mem_closedBall] at hm
    have cut : cutBump x = 1 := cutBump.one_of_mem_closedBall (hm.trans (by norm_num [cutBump,inletBump]))
    have hp : phase (-t) x * phase t x = 1 := by simp [phase,← Complex.exp_add]
    rw [cut,Complex.ofReal_one,one_mul]
    change _ = ((inletBump x * Real.exp (b*x):ℝ):ℂ)
    rw [Complex.ofReal_mul]
    unfold tilt
    linear_combination (inletBump x : ℂ) * (Real.exp (b*x) : ℂ) * hp
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun x ↦
    mul_nonneg inletBump.nonneg (Real.exp_pos _).le),← integral_const_mul]
  have hv : Integrable v := (inletBump.continuous.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport inletBump.hasCompactSupport.mul_right
  apply integral_mono (inletBump.integrable.const_mul _) hv
  intro x
  by_cases hx : inletBump x = 0
  · simp [v,hx]
  have hm := subset_tsupport _ (show x ∈ support inletBump from hx)
  rw [inletBump.tsupport_eq,Metric.mem_closedBall,Real.dist_eq,sub_zero] at hm
  have hx₁ : |x| ≤ 1 := hm.trans (by norm_num [inletBump])
  have hbx : -α ≤ b*x := (abs_le.mp ((abs_mul _ _).le.trans
    ((mul_le_mul hb hx₁ (abs_nonneg x) hα).trans_eq (mul_one α)))).1
  exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbx) inletBump.nonneg)
private theorem strip_polynomial_bound {Z : Type*} {α : ℝ} (hα : 0≤α) (b t w : Z → ℝ) (hb : ∀ z, |b z|≤α) (hw : ∀ z, 0 ≤ w z)
    (h : ∀ f : S, BddAbove (range (fun z ↦ (radScale F * ‖stripEval (b z) (t z) f‖) * w z))) :
    ∃ C ≥ (0 : ℝ), ∃ k : ℕ, ∀ z, w z ≤ C*(1+|t z|)^k := by
  have : CompleteSpace S := completeSpace_schwartzMap
  have : (uniformity S).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero S]; infer_instance
  let P (z : Z) := (normSeminorm ℂ ℂ).comp
    ((((w z : ℂ) * (radScale F : ℂ)) • stripEval (b z) (t z)).toLinearMap)
  have he (z : Z) (f : S) : P z f = w z * (radScale F * ‖stripEval (b z) (t z) f‖) := by
    change ‖((w z : ℂ)*(radScale F:ℂ)) • stripEval (b z) (t z) f‖ = _
    rw [norm_smul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (hw _),Real.norm_of_nonneg (radScale_pos (F := F)).le,mul_assoc]
  have hbd : BddAbove (range P) := by
    apply Seminorm.bddAbove_range_iff.mpr
    intro f
    obtain ⟨B,hB⟩ := h f
    refine ⟨B, forall_mem_range.mpr (fun z ↦ ?_)⟩
    have hz := hB (mem_range_self z)
    rw [he,mul_comm]
    exact hz
  have hcont : Continuous (⨆ z, P z : Seminorm ℂ S) := by
    rw [Seminorm.coe_iSup_eq hbd]
    exact Seminorm.continuous_iSup P (fun z ↦ (((w z:ℂ)*(radScale F:ℂ)) • stripEval (b z) (t z)).continuous.norm) hbd
  obtain ⟨A,hA,k,hk⟩ := orbitBound (bumpS inletBump) (bumpS_compact _) _ hcont
  let c : ℝ := Real.exp (-α) * ∫ x : ℝ, inletBump x
  have hc : 0 < c := mul_pos (Real.exp_pos _) inletBump.integral_pos
  refine ⟨A / (radScale F*c), div_nonneg hA (mul_nonneg (radScale_pos (F := F)).le hc.le), k, fun z ↦ ?_⟩
  have h₁ := (le_ciSup hbd z) (atom (bumpS inletBump) (bumpS_compact _) (t z))
  rw [he] at h₁
  have h₂ : w z * (radScale F*c) ≤ A*(1+|t z|)^k :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (stripEval_atom_lower hα (hb z) (t z))
      (radScale_pos (F := F)).le) (hw z)).trans (h₁.trans (hk (t z)))
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (mul_pos (radScale_pos (F := F)) hc)).2 h₂

private theorem homogeneous_strip_profile (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (η : PontryaginDual C₁) (f : S) :
    ∃ φ : BruhatCompactSupport C𝔽,
      (∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (η k : ℂ)*φ.val g) ∧
      ∀ σ t : ℝ, nuclearityTestMellin (χ η) φ ((σ:ℂ)+(t:ℂ)*Complex.I) = (radScale F:ℂ)*stripEval σ t f := by
  let b (x : ℝ) := bumpS cutBump x * f x
  obtain ⟨φ,hφ⟩ := exists_characterNormTest (F := F) (χ η)⁻¹ b
    ((bumpS cutBump).smooth'.mul f.smooth') (bumpS_compact cutBump).mul_right
  let l := logIdeleClassNorm F
  have form (g : C𝔽) : φ.val g = (χ η g : ℂ)⁻¹ * b (l g) := by
    rw [hφ]; change (↑((χ η g)⁻¹) : ℂ) * _ = _; rw [Circle.coe_inv]
  refine ⟨φ, fun k g ↦ ?_, fun σ t ↦ ?_⟩
  · have he := DFunLike.congr_fun (hχ η) k
    change χ η k.val = η k at he
    have hl : l (k.val⁻¹ * g) = l g := by
      change Real.log ((ideleClassNorm F (k.val⁻¹ * g)).val:ℝ) = _
      rw [map_mul,map_inv,k.property,inv_one,one_mul]
    rw [form,form,hl,map_mul,map_inv,he,Circle.coe_mul,Circle.coe_inv,mul_inv_rev,inv_inv]
    ring
  · let U (x : ℝ) := b x * (tilt σ x * phase t x)
    have hl : Continuous l := ((NNReal.continuous_coe.comp Units.continuous_val).comp
      (isProperMap_ideleClassNorm F).continuous).log fun g ↦
        (show 0 < ((ideleClassNorm F g).val : ℝ) from NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have hU : Continuous U := ((bumpS cutBump).continuous.mul f.continuous).mul ((tilt_smooth σ).continuous.mul (phase_smooth t).continuous)
    have he (g : C𝔽) : ideleClassNormTwist (χ η) ((σ:ℂ)+(t:ℂ)*Complex.I) g = (χ η g : ℂ)*(tilt σ (l g)*phase t (l g)) := by
      change (χ η g : ℂ) * ((((ideleClassNorm F g).val : ℝ):ℂ) ^ ((σ:ℂ)+(t:ℂ)*Complex.I)) = _
      have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'), ← Complex.ofReal_log hp.le]
      unfold tilt phase
      rw [Complex.ofReal_exp,←Complex.exp_add,Complex.ofReal_mul]
      congr 2
      change (l g:ℂ)*_ = _
      ring
    have eqI (g : C𝔽) : φ.val g * ideleClassNormTwist (χ η) ((σ:ℂ)+(t:ℂ)*Complex.I) g = U (l g) := by
      rw [he,form]
      dsimp only [U]
      calc
        _ = ((χ η g : ℂ)⁻¹*(χ η g : ℂ)) * (b (l g)*(tilt σ (l g)*phase t (l g))) := by ring
        _ = _ := by rw [inv_mul_cancel₀ (Circle.coe_ne_zero _),one_mul]
    unfold nuclearityTestMellin
    simp_rw [eqI]
    rw [← integral_map hl.aemeasurable hU.aestronglyMeasurable,
      show (ideleClassTamagawaMeasure F).map l = _ from classTamagawa_map_log_norm (F := F),
      integral_smul_nnreal_measure,NNReal.smul_def,Complex.real_smul,stripEval_eq]
    rfl
private theorem homogeneous_strip_mellin_polynomial {Z : Type*} {α : ℝ} (hα : 0≤α) (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (η : PontryaginDual C₁) (b t w : Z → ℝ) (hb : ∀ z, |b z|≤α) (hw : ∀ z, 0 ≤ w z)
    (h : ∀ φ : BruhatCompactSupport C𝔽,
      (∀ (k : C₁) (g : C𝔽), φ.val (k.val⁻¹*g) = (η k : ℂ)*φ.val g) →
      BddAbove (range (fun z ↦ ‖nuclearityTestMellin (χ η) φ ((b z:ℂ)+(t z:ℂ)*Complex.I)‖ * w z))) :
    ∃ C ≥ (0 : ℝ), ∃ n : ℕ, ∀ z, w z ≤ C*(1+|t z|)^n := by
  apply strip_polynomial_bound (F := F) hα b t w hb hw
  intro f
  obtain ⟨φ,hη,hφ⟩ := homogeneous_strip_profile χ hχ η f
  simpa only [hφ,norm_mul,Complex.norm_real,Real.norm_of_nonneg (radScale_pos (F := F)).le] using h φ hη
end LineModulation

/-- On a component with at most one surviving derivative per site, the universal
rank-one assertion already forces polynomially bounded coordinate projection norms. -/
theorem spectralStrip_simple_blocks_require_polynomial_coordinate_norms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hb : IsSpectralMarkushevichBasis x L) (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i))
    (η : PontryaginDual C₁) (hsimple : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z)≤1)
    (hc : ∀ φ : BruhatCompactSupport C𝔽, (hom(φ,η)) →
      ∀ (v : H(a,hα,hs)) (g : StrongDual ℂ H(a,hα,hs)),
        Summable (fun z : Z(χ,a,α) ↦ ∑ m : Fin (N(χ,a,α,s,z)),
          L (jet(z,m)) (A(a,hα,hs,φ) ((g.smulRight v) (x (jet(z,m))))))) :
    ∃ C≥(0:ℝ), ∃ k : ℕ, ∀ i : J(χ,a,α,s), i.val.1=η →
      ‖L i‖ * ‖x i‖ ≤ C*(1+|i.val.2.2.1|)^k := by
  let I := {i : J(χ,a,α,s) // i.val.1=η}
  let z (i : J(χ,a,α,s)) : Z(χ,a,α) := ⟨(i.val.1,i.val.2.1,i.val.2.2.1),i.mem_strip_order_pos hα⟩
  let ind (i : J(χ,a,α,s)) : Fin (N(χ,a,α,s,z i)) := ⟨i.val.2.2.2,i.property⟩
  let angle (i : I) := ‖L i.val‖*‖x i.val‖
  have hw (i : I) : 0≤angle i := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hm (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) :
      BddAbove (range fun i : I ↦ ‖nuclearityTestMellin (χ η) φ (pt(i.val.val.2.1,i.val.val.2.2.1))‖*angle i) := by
    obtain ⟨C,hC,hbd⟩ := spectralStripConvolution_mellin_norm_le_of_summable_rankOne_blocks a hα hs χ x L hb hj φ (hc φ hφ)
    refine ⟨C,forall_mem_range.mpr fun i ↦ ?_⟩
    have hs₁ := hsimple (z i.val) i.property
    have hi := (ind i.val).isLt
    have hzero : i.val.val.2.2.2=0 := by change i.val.val.2.2.2<_ at hi; omega
    let j : J(χ,a,α,s) := jet((z i.val),(⟨0,Nat.zero_lt_of_lt hi⟩ : Fin (N(χ,a,α,s,z i.val))))
    have hj' : j=i.val := Subtype.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hzero.symm)))
    let P := Submodule.span ℂ {f | ∃ (w : Z(χ,a,α)) (_ : w≠z i.val)
      (m : Fin (N(χ,a,α,s,w))), f = L (jet(w,m))}
    let Q := Submodule.span ℂ (L '' {k | k≠i.val})
    have hin : Q ≤ P := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,rfl⟩
      have hkz : z k ≠ z i.val := by
        intro he
        have h₁ : k.val.1=i.val.val.1 := congrArg (fun w : Z(χ,a,α) ↦ w.val.1) he
        have h₂ : k.val.2.1=i.val.val.2.1 := congrArg (fun w : Z(χ,a,α) ↦ w.val.2.1) he
        have h₃ : k.val.2.2.1=i.val.val.2.2.1 := congrArg (fun w : Z(χ,a,α) ↦ w.val.2.2) he
        have hk' := (ind k).isLt
        change k.val.2.2.2 < N(χ,a,α,s,z k) at hk'
        rw [he] at hk'
        exact hk (Subtype.ext (Prod.ext h₁ (Prod.ext h₂ (Prod.ext h₃ (by omega)))))
      exact Submodule.subset_span ⟨z k,hkz,ind k,rfl⟩
    have Hd := Metric.infDist_le_infDist_of_subset (x:=L i.val) (s:=(Q : Set _)) (t:=(P : Set _))
      hin ⟨0,Q.zero_mem⟩
    rw [show Metric.infDist (L i.val) (Q : Set _) = _ from spectralMarkushevich_coordinate_distance x L hb i.val] at Hd
    have H := hbd (z i.val) (Nat.zero_lt_of_lt hi)
    change ‖_‖*‖L j‖ ≤ C*Metric.infDist (L j) (P : Set _) at H
    rw [hj', (spectralConvolution_mellin_integrable _ _ _).2] at H
    change ‖nuclearityTestMellin (χ i.val.val.1) φ (pt(i.val.val.2.1,i.val.val.2.2.1))‖*‖L i.val‖ ≤ _ at H
    rw [i.property] at H
    have hx : x i.val ≠ 0 := by
      intro he
      have H₀ := hb.1 i.val
      rw [he,map_zero] at H₀
      exact zero_ne_one H₀
    change _ * (‖L i.val‖ * ‖x i.val‖) ≤ C
    rw [←mul_assoc]
    calc
      _ ≤ (C*‖x i.val‖⁻¹)*‖x i.val‖ := mul_le_mul_of_nonneg_right (H.trans (mul_le_mul_of_nonneg_left Hd hC.le)) (norm_nonneg _)
      _ = _ := by rw [mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx),mul_one]
  obtain ⟨C,hC,k,hk⟩ := LineModulation.homogeneous_strip_mellin_polynomial hα χ hχ η
    (fun i : I ↦ i.val.val.2.1) (fun i : I ↦ i.val.val.2.2.1) angle
    (fun i ↦ abs_le.mpr (z i.val).property.1) hw hm
  exact ⟨C,hC,k,fun i hi ↦ hk ⟨i,hi⟩⟩
#print axioms spectralStrip_simple_blocks_require_polynomial_coordinate_norms

/-- If each site of the chosen component retains at most one jet, the
homogeneous-test assertion for all compact insertions is equivalent to
polynomial growth of the actual coordinate projection norms. -/
theorem spectralStrip_simple_component_blocks_iff_polynomial_coordinate_norms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hb : IsSpectralMarkushevichBasis x L) (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i))
    (η : PontryaginDual C₁) (hsimple : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z)≤1) :
    (∀ φ : BruhatCompactSupport C𝔽, (hom(φ,η)) →
      ∀ U : compactOperator (RingHom.id ℂ) H(a,hα,hs) H(a,hα,hs), Summable (fun z : Z(χ,a,α) ↦
        ∑ m : Fin (N(χ,a,α,s,z)), L (jet(z,m)) (A(a,hα,hs,φ) (U.val (x (jet(z,m))))))) ↔
    ∃ C≥(0:ℝ), ∃ k : ℕ, ∀ i : J(χ,a,α,s), i.val.1=η → ‖L i‖*‖x i‖ ≤ C*(1+|i.val.2.2.1|)^k := by
  constructor
  · intro h
    apply spectralStrip_simple_blocks_require_polynomial_coordinate_norms χ hχ a hα hs x L hb hj η hsimple
    intro φ hφ v g
    exact h φ hφ ⟨g.smulRight v,(isCompactOperator_of_locallyCompactSpace_rng
      ((ContinuousLinearMap.id ℂ ℂ).smulRight v)).comp_clm g⟩
  · intro h φ hφ U
    exact (spectralStrip_polynomial_coordinate_norms_bounded_blocks χ hχ a hα hs x L hj η h φ hφ U.val).of_norm
#print axioms spectralStrip_simple_component_blocks_iff_polynomial_coordinate_norms


/-- Quotient translations act on every jet at one zero by the finite binomial matrix. -/
private theorem strip_translation_finite_block
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs)) (hj : ∀ j, D(a,hα,hs) (L j) = raw(χ,hα,hs,j)) :
    ∃ ρ : C𝔽 →* (H(a,hα,hs) →L[ℂ] H(a,hα,hs)),
      ∀ (z : Z(χ,a,α)) (m : Fin (N(χ,a,α,s,z))) (g : C𝔽) (u : H(a,hα,hs)),
        L (jet(z,m)) (ρ g u) = ∑ i : Fin (m.val+1),
          (ideleClassNormTwist (χ z.val.1) (pt(z.val.2.1,z.val.2.2)) g *
          (logIdeleClassNorm F g : ℂ)^(m.val-i.val) * (m.val.choose i.val : ℂ)) *
          L (jet(z,(⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ : Fin (N(χ,a,α,s,z))))) u := by
  let hS := le_of_lt (zero_lt_one.trans hs)
  let hI := neg_le_self hα
  let θ := globalThetaSobolev F (α := -α) (β := α) (s := s) a hI hS
  obtain ⟨ρ,hρ,_⟩ := spectralSobolevIsotypeQuotient_isometry (F:=F) a hI hS (1 : PontryaginDual C₁)
  refine ⟨ρ,?_⟩
  intro z m g u
  obtain ⟨v,hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (χ z.val.1) z.val.2.1 z.val.2.2 i
  let j : J(χ,a,α,s) := jet(z,m)
  have hnorm : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  let τ := stripJetTranslation (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s hI hS
  have heval (k : J(χ,a,α,s)) := spectralStripConvolution_jet_eval (a:=a) hα hs χ k (L k) (hj k)
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 := by
    let k : Fin (N(χ,a,α,s,z)) := ⟨i, hi.trans_lt m.isLt⟩
    exact (heval (jet(z,k)) v).1
  have hae := stripJetTranslation_apply (G := C𝔽) μ𝔽 (ideleClassNorm F) hnorm (-α) α s hI hS g v
  have ht := stripJet_all_translated_moments (F:=F) (α:=α) (s:=s) (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint g
  rw [← hv, hρ]
  refine (heval j (τ g v)).2.trans ((stripJet_integrated_product_congr μ𝔽 (J m.val) hae).trans (ht.trans ?_))
  apply Finset.sum_congr rfl
  intro i _
  let k : Fin (N(χ,a,α,s,z)) := ⟨i.val,(Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  exact congrArg (_ * ·) (heval (jet(z,k)) v).2.symm

open Matrix
/-- At a uniformly bounded jet length the moment interpolation matrix is fixed once and for all. -/
private theorem finite_jet_moment_interpolation (k : ℕ) :
    ∃ T : (Fin k → ℂ) →L[ℂ] (Fin k → ℂ), ∀ (a : Fin k → ℂ) (q : Fin k),
      ∑ j : Fin k, T a j * (j.val : ℂ)^q.val = a q := by
  classical
  let v : Fin k → ℂ := fun j ↦ (j.val : ℂ)
  let V := Matrix.vandermonde v
  have hv : Function.Injective v := fun i j h ↦ Fin.ext (by dsimp [v] at h; exact_mod_cast h)
  have hd : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  refine ⟨(V⁻¹.vecMulLinear).toContinuousLinearMap,?_⟩
  intro a q
  change ((a ᵥ* V⁻¹) ᵥ* V) q = _
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hd, Matrix.vecMul_one]

/-- On a complete block of length at most k, its convolution is a finite linear
combination of fixed translations, with weights given by interpolation of its moments. -/
private theorem complete_block_moment_interpolation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {k n : ℕ} (hn : n ≤ k) (L : Fin n → StrongDual ℂ V) (x : Fin n → V)
    (A : V →L[ℂ] V) (U : Fin k → (V →L[ℂ] V)) (κ : Fin k → ℂ) (hκ : ∀ j, κ j ≠ 0)
    (b c : Fin k → ℂ)
    (hm : ∀ q : Fin k, ∑ j : Fin k, c j * (j.val : ℂ)^q.val = b q)
    (hA : ∀ (m : Fin n) (v : V), L m (A v) =
      ∑ i : Fin (m.val+1), (m.val.choose i.val : ℂ) *
        b ⟨m.val-i.val, by have H := m.isLt; omega⟩ *
        L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v)
    (hU : ∀ (m : Fin n) (j : Fin k) (v : V), L m (U j v) =
      ∑ i : Fin (m.val+1), (κ j * (j.val : ℂ)^(m.val-i.val) * (m.val.choose i.val : ℂ)) *
        L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v) :
    (∑ m : Fin n, ((L m).comp A).smulRight (x m)) =
      ∑ j : Fin k, (c j / κ j) • ((∑ m : Fin n, (L m).smulRight (x m)).comp (U j)) := by
  classical
  have hrow (m : Fin n) (v : V) : L m (A v) = ∑ j, (c j / κ j) * L m (U j v) := by
    rw [hA]
    simp_rw [hU,Finset.mul_sum]
    rw [Finset.sum_comm (f := fun j (i : Fin (m.val+1)) ↦ _)]
    apply Finset.sum_congr rfl
    intro i _
    let q : Fin k := ⟨m.val-i.val, by have H := m.isLt; omega⟩
    let l := L ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ v
    change (m.val.choose i.val : ℂ) * b q * l = _
    rw [← hm q,Finset.mul_sum,Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [q,l]
    field_simp [hκ j]

  ext v
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, smul_apply]
  simp_rw [hrow,Finset.sum_smul,Finset.smul_sum,smul_smul]
  exact Finset.sum_comm

private theorem finite_jet_translation_insertion_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {k : ℕ} (U : Fin k → (V →L[ℂ] V)) (P B : V →L[ℂ] V) (κ c : Fin k → ℂ)
    (r : Fin k → ℝ) {M : ℝ} (hM : 0 ≤ M) (hr : ∀ j, ‖(κ j)⁻¹‖ ≤ r j)
    (hc : ∀ j, ‖c j‖ ≤ M) (hB : B = ∑ j : Fin k, (c j / κ j) • (P.comp (U j))) :
    ‖B‖ ≤ (∑ j : Fin k, r j * ‖U j‖) * M * ‖P‖ := by
  rw [hB,Finset.sum_mul,Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [norm_smul,div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (M*r j)*(‖P‖*‖U j‖) := mul_le_mul (mul_le_mul (hc j) (hr j) (norm_nonneg _) hM)
      (ContinuousLinearMap.opNorm_comp_le ..) (norm_nonneg _) (mul_nonneg hM ((norm_nonneg _).trans (hr j)))
    _ = _ := by ring

private theorem strip_block_jet_moments_cauchy (χ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (w₀ : ℂ) {M : ℝ} (hM : ∀ w∈Metric.sphere w₀ 1, ‖∫ g, φ.val g * ideleClassNormTwist χ w g ∂μ𝔽‖ ≤ M)
    (q : ℕ) : ‖∫ g, φ.val g * ideleClassNormTwist χ w₀ g * (logIdeleClassNorm F g : ℂ)^q ∂μ𝔽‖ ≤ q.factorial*M := by
  rw [stripMellinMoment_eq_twisted_integral χ φ w₀ q]
  have hφ := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F,(isProperMap_ideleClassNorm F).continuous⟩
  simpa only [one_pow,div_one] using
    stripMellinMoment_cauchy μ𝔽 (logIdeleClassNorm F) (fun g : C𝔽 ↦ φ.val g * (χ g : ℂ)) (continuous_logModule' n)
      (hφ.mul (continuous_subtype_val.comp χ.continuous)) (show HasCompactSupport φ.val from φ.property.2).mul_right w₀ q
      (show (0:ℝ)<1 by norm_num) (fun w hw ↦ by
        have h := stripMellinMoment_eq_twisted_integral χ φ w 0
        simp only [pow_zero,mul_one] at h
        exact (congrArg norm h.symm).le.trans (hM w hw))

/-- The operator norm of every complete convolved zero block of at most k jets
is controlled by its full projection and the Mellin transform on the unit circle. -/
theorem spectralStripConvolution_complete_block_circle (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (a : ℝ) {α s : ℝ} (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (k : ℕ) :
    ∃ C ≥ (0:ℝ), ∀ (z : Z(χ,a,α)), N(χ,a,α,s,z) ≤ k →
      ∀ (φ : BruhatCompactSupport C𝔽) (M : ℝ), 0 ≤ M →
      (∀ w∈Metric.sphere (pt(z.val.2.1,z.val.2.2)) 1, ‖∫ g, φ.val g * ideleClassNormTwist (χ z.val.1) w g ∂μ𝔽‖ ≤ M) →
      ‖∑ m : Fin (N(χ,a,α,s,z)), ((L (jet(z,m))).comp A(a,hα,hs,φ)).smulRight (x (jet(z,m)))‖ ≤
        C * M * ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ := by
  obtain ⟨ρ,hρ⟩ := strip_translation_finite_block χ a hα hs L hj
  obtain ⟨T,hT⟩ := finite_jet_moment_interpolation k
  let e : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  let g (j : Fin k) : C𝔽 := QuotientGroup.mk (canonicalIdeleNormSection F (e j.val))
  have hg (j) : logIdeleClassNorm F (g j) = j.val := by
    change Real.log ((ideleClassNorm F (g j)).val : ℝ) = _
    rw [show ideleClassNorm F (g j) = _ from canonicalIdeleNormSection_rightInverse F (e j.val)]
    exact Real.log_exp _
  let U (j : Fin k) := ρ (g j)
  let r (j : Fin k) := Real.exp (α*j.val)
  let S := ∑ j : Fin k, r j * ‖U j‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  refine ⟨S * ‖T‖ * k.factorial,by positivity,?_⟩
  intro z hn φ M hM hc
  let w₀ := pt(z.val.2.1,z.val.2.2)
  let κ (j : Fin k) := ideleClassNormTwist (χ z.val.1) w₀ (g j)
  let b (q : Fin k) := ∫ y, φ.val y * ideleClassNormTwist (χ z.val.1) w₀ y * (logIdeleClassNorm F y : ℂ)^q.val ∂μ𝔽
  have hb : ‖b‖ ≤ k.factorial*M := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro q
    exact (strip_block_jet_moments_cauchy (χ z.val.1) φ w₀ hc q.val).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le (Nat.le_of_lt q.isLt)) hM)
  have hκnorm (j) : ‖κ j‖ = Real.exp (z.val.2.1 * j.val) := by
    have hp : 0 < ((ideleClassNorm F (g j)).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ‖(χ z.val.1 (g j) : ℂ) * (((ideleClassNorm F (g j)).val : ℝ) : ℂ)^w₀‖ = _
    rw [norm_mul,Circle.norm_coe,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp, Real.rpow_def_of_pos hp]
    change Real.exp (logIdeleClassNorm F (g j) * _) = _
    rw [hg]
    simp [w₀,mul_comm]
  have hκ (j) : κ j ≠ 0 := norm_ne_zero_iff.mp ((hκnorm j).trans_ne (Real.exp_pos _).ne')
  have hr (j) : ‖(κ j)⁻¹‖ ≤ r j := by
    rw [norm_inv,hκnorm,←Real.exp_neg]; apply Real.exp_le_exp.mpr
    rw [←neg_mul]; exact mul_le_mul_of_nonneg_right (by linarith [z.property.1.1]) (Nat.cast_nonneg _)
  let l (m : Fin (N(χ,a,α,s,z))) := L (jet(z,m))
  let y (m : Fin (N(χ,a,α,s,z))) := x (jet(z,m))
  have row := complete_block_moment_interpolation hn l y A(a,hα,hs,φ) U κ hκ b (T b) (hT b)
    (spectralStripConvolution_all_jet_coefficients a hα hs χ L hj φ z)
    (fun m j v ↦ by simpa only [hg,Complex.ofReal_natCast] using hρ z m (g j) v)
  have est := finite_jet_translation_insertion_norm U _ _ κ (T b) r
    (show 0 ≤ ‖T‖*(k.factorial*M) by positivity) hr
    (fun j ↦ (norm_le_pi_norm (T b) j).trans ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _)))) row
  convert est using 1
  change S * ‖T‖ * _ * _ * _ = S * (_ * (_ * _)) * _
  ring
#print axioms spectralStripConvolution_complete_block_circle

private theorem finite_block_traceNorm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {n : ℕ} (L : Fin n → StrongDual ℂ V) (x : Fin n → V) :
    let r (m : Fin n) : nuclearEndomorphisms V := ⟨(L m).smulRight (x m),smulRight_mem_nuclearEndomorphisms _ _⟩
    traceNorm (∑ m, r m) ≤ n * ‖∑ m, (L m).smulRight (x m)‖ := by
  classical
  intro r
  let T := ∑ m, r m
  have hT : T.val = ∑ m, (L m).smulRight (x m) := by simp only [T, r, Submodule.coe_sum]
  have hr : Module.rank ℂ T.val.toLinearMap.range ≤ (n : Cardinal) := by
    let S := Submodule.span ℂ (range x)
    have hle : T.val.toLinearMap.range ≤ S := by
      rintro _ ⟨v,rfl⟩
      change T.val v ∈ S
      rw [hT,sum_apply]
      exact Submodule.sum_mem _ (fun m _ ↦ S.smul_mem _ (Submodule.subset_span ⟨m,rfl⟩))
    apply (Submodule.rank_mono hle).trans
    have := FiniteDimensional.span_of_finite ℂ (Set.finite_range x)
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (by simpa [Set.finrank,S] using finrank_range_le_card (R:=ℂ) x : Module.finrank ℂ S ≤ n)
  have hzero (i : ℕ) (hi : i ∉ Finset.range n) : approximationNumber T.val i = 0 := by
    exact approximationNumber_eq_zero_of_rank_le _ (hr.trans (by exact_mod_cast (by simpa using hi : n ≤ i)))
  have he := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at he
  change traceNorm T ≤ _
  rw [← he,tsum_eq_sum hzero,←hT]
  calc
    _ ≤ ∑ _i ∈ Finset.range n, ‖T.val‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa using approximationNumber_le_norm_sub T.val 0 (n:=i) (by simp)
    _ = _ := by simp
private theorem finite_block_trace_insertion_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {n : ℕ} (L : Fin n → StrongDual ℂ V) (x : Fin n → V) (U : V →L[ℂ] V) :
    ‖∑ m, L m (U (x m))‖ ≤ ‖U‖ * (n * ‖∑ m, (L m).smulRight (x m)‖) := by
  classical
  let r (m : Fin n) (v : V) : nuclearEndomorphisms V := ⟨(L m).smulRight v,smulRight_mem_nuclearEndomorphisms _ _⟩
  let T := ∑ m, r m (x m)
  let D : nuclearEndomorphisms V := ⟨U*T.val, mul_mem_nuclearEndomorphisms_left _ T⟩
  have hd : D = ∑ m, r m (U (x m)) := by
    apply Subtype.ext
    ext v
    change U (T.val v) = _
    simp only [T,r,Submodule.coe_sum,sum_apply,ContinuousLinearMap.smulRight_apply,map_sum,map_smul]
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H:=V)
  have ht : hilbertTrace D = ∑ m, L m (U (x m)) := by
    rw [← htr,hd,map_sum]; simp only [htr,r,hilbertTrace_smulRight]
  rw [← ht]
  exact (norm_hilbertTrace_le D).trans ((traceNorm_mul_left_le U T).trans (mul_le_mul_of_nonneg_left (finite_block_traceNorm_le L x) (norm_nonneg _)))

/-- A polynomial bound on the complete block projections of a component, with uniformly
bounded surviving multiplicities on that component only, suffices for the genuine block norms. -/
private theorem spectralStrip_polynomial_complete_projections_summable
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C*(1+|z.val.2.2|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) :
    Summable (fun z : Z(χ,a,α) ↦ (N(χ,a,α,s,z):ℝ) * ‖∑ m : Fin (N(χ,a,α,s,z)),
      ((L (jet(z,m))).comp A(a,hα,hs,φ)).smulRight (x (jet(z,m)))‖) := by
  classical
  obtain ⟨C,hC,d,hP⟩ := hpoly
  obtain ⟨B,hB,hcircle⟩ := circle_decay (χ η) φ hα (show (0:ℝ)<1 by norm_num) (d+2) (by omega)
  obtain ⟨D,hD,hd⟩ := spectralStripConvolution_complete_block_circle χ a hα hs x L hj k
  let Q (z : Z(χ,a,α)) := ∑ m : Fin (N(χ,a,α,s,z)), ((L (jet(z,m))).comp A(a,hα,hs,φ)).smulRight (x (jet(z,m)))
  let P (z : Z(χ,a,α)) := ∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))
  let f (z : Z(χ,a,α)) := (N(χ,a,α,s,z):ℝ)*‖Q z‖
  let X := X(χ,a,α,s,η)
  have hzero (z : Z(χ,a,α)) (hz : z ∉ range (Subtype.val : X → Z(χ,a,α))) : f z = 0 := by
    by_cases he : z.val.1=η
    · have hn : N(χ,a,α,s,z)=0 := by
        by_contra h
        exact hz ⟨⟨z,he,Nat.pos_of_ne_zero h⟩,rfl⟩
      dsimp only [f]; rw [hn]; norm_num
    · obtain ⟨D',_,hd'⟩ := spectralStripConvolution_complete_block_circle χ a hα hs x L hj (N(χ,a,α,s,z))
      have hc (w : ℂ) (_ : w∈Metric.sphere (pt(z.val.2.1,z.val.2.2)) 1) :
          ‖∫ y, φ.val y * ideleClassNormTwist (χ z.val.1) w y ∂μ𝔽‖ ≤ 0 := by
        have h := spectralIsotype_mellin_eq_zero χ hχ he φ hφ w
        rw [(spectralConvolution_mellin_integrable _ _ _).2] at h
        simp only [h,norm_zero,le_refl]
      have hb := hd' z le_rfl φ 0 le_rfl hc
      have hQ : ‖Q z‖ = 0 := le_antisymm (by simpa [Q] using hb) (norm_nonneg _)
      simp [f,hQ]
  change Summable f
  apply (Subtype.val_injective.summable_iff (f:=f) hzero).mp
  apply Summable.of_nonneg_of_le (fun z ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) _ ((positive_strip_jet_count χ a α s η).mul_left (D*B*C))
  intro z
  let r := 1+|t(z)|
  have hr : 0<r := by dsimp only [r]; positivity
  let M := B/r^(d+2)
  have hM : 0≤M := by dsimp only [M]; positivity
  have hcircle' (w) (hw : w∈Metric.sphere (pt(b(z),t(z))) 1) :
      ‖∫ g, φ.val g * ideleClassNormTwist (χ z.val.val.1) w g ∂μ𝔽‖ ≤ M := by
    rw [z.property.1]
    simpa [nuclearityTestMellin] using hcircle (pt(b(z),t(z))) (by simpa using abs_le.mpr z.val.property.1) w hw
  have hz := hd z.val (hk _ z.property.1) φ M hM hcircle'
  change (N(χ,a,α,s,z.val):ℝ)*‖Q z.val‖ ≤ D*B*C*((N(χ,a,α,s,z.val):ℝ)/r^2)
  calc
    _ ≤ (N(χ,a,α,s,z.val):ℝ)*(D*M*(C*r^d)) := mul_le_mul_of_nonneg_left
      (hz.trans (mul_le_mul_of_nonneg_left (hP _ z.property.1) (mul_nonneg hD hM))) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [M]; rw [pow_add]; field_simp

/-- A diagonal flag of jet rows annihilates the k-th power of the centered operator. -/
private theorem finite_block_triangular_annihilates {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {n k : ℕ} (hn : n ≤ k) (L : Fin n → StrongDual ℂ V) (x : Fin n → V)
    (A : V →L[ℂ] V) (c : ℂ)
    (ht : ∀ (m : Fin n) (u : V), (∀ i < m, L i u = 0) → L m (A u) = c*L m u) :
    (∑ m : Fin n, (L m).smulRight (x m)) * ((c • (1 : V →L[ℂ] V)) - A)^k = 0 := by
  let R := (c • (1 : V →L[ℂ] V)) - A
  have hv (j : ℕ) (m : Fin n) (hm : m.val < j) (u : V) : L m ((R^j) u) = 0 := by
    induction j generalizing m with
    | zero => omega
    | succ j ih =>
      rw [pow_succ']
      change L m (c • ((R^j) u) - A ((R^j) u)) = 0
      rw [map_sub,map_smul, ht m _ (fun i hi ↦ ih i (by change i.val < m.val at hi; omega))]
      exact sub_self _
  ext u
  change (∑ m : Fin n, (L m).smulRight (x m)) ((R^k) u) = 0
  simp only [sum_apply,ContinuousLinearMap.smulRight_apply]
  exact Finset.sum_eq_zero (fun m _ ↦ by rw [hv k m (m.isLt.trans_le hn),zero_smul])

/-- From a fixed uniform bound for the spectral parameter and the convolved blocks,
the eigenvalue to the power k controls each whole block. -/
private theorem bounded_blocks_control_power {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : V →L[ℂ] V) (k : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ B ≥ (0:ℝ), ∀ (P : V →L[ℂ] V) (c : ℂ), ‖c‖ ≤ M →
      P * (c • (1 : V →L[ℂ] V) - A)^k = 0 → ‖c‖^k * ‖P‖ ≤ ‖P*A‖ * B := by
  rcases subsingleton_or_nontrivial V with h | h
  · exact ⟨0,le_rfl,fun P _ _ _ ↦ by rw [Subsingleton.elim P 0]; simp⟩
  let := h
  let R := 1 + M * ‖(1 : V →L[ℂ] V)‖ + ‖A‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [mul_nonneg hM (norm_nonneg (1 : V →L[ℂ] V)),norm_nonneg A]
  refine ⟨k*R^k,by positivity,?_⟩
  intro P c hc hnil
  let X := c • (1 : V →L[ℂ] V)
  let Y := X-A
  have hXY : Commute X Y := (Commute.refl X).sub_right ((Commute.one_left A).smul_left c)
  let W := ∑ i ∈ Finset.range k, X^i * Y^(k-1-i)
  have he : A * W = X^k - Y^k := by simpa only [Y,sub_sub_cancel] using hXY.mul_geom_sum₂ k
  have hPW : P*A*W = (c^k) • P := by
    rw [mul_assoc,he,mul_sub,hnil,sub_zero,show X^k = c^k • (1 : V →L[ℂ] V) by simp [X,smul_pow]]
    simp only [mul_smul_comm,mul_one]
  have hX : ‖X‖ ≤ M*‖(1 : V →L[ℂ] V)‖ := by rw [show ‖X‖ = _ from norm_smul c _]; gcongr
  have hx : ‖X‖ ≤ R := hX.trans (by dsimp [R]; linarith [norm_nonneg A])
  have hy : ‖Y‖ ≤ R := (norm_sub_le _ _).trans (by dsimp only [R]; linarith)
  have hW : ‖W‖ ≤ k*R^k := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range k, R^k := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        apply (norm_mul_le ..).trans
        apply (mul_le_mul ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) hx _)) ((norm_pow_le ..).trans
          (pow_le_pow_left₀ (norm_nonneg _) hy _)) (norm_nonneg _) (by positivity)).trans
        rw [← pow_add]; apply pow_le_pow_right₀ hR; have := Finset.mem_range.mp hi; omega
      _ = _ := by simp
  calc
    _ = ‖P*A*W‖ := by rw [hPW,norm_smul,norm_pow]
    _ ≤ ‖P*A‖ * (k*R^k) := (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg _))

/-- For uniformly bounded complete jet multiplicities, rank-one summability for all
homogeneous tests forces polynomial operator-norm growth of the whole bare projections. -/
theorem spectralStrip_complete_blocks_require_polynomial_projection_norms
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k)
    (hc : ∀ φ : BruhatCompactSupport C𝔽, (hom(φ,η)) →
      ∀ (v : H(a,hα,hs)) (g : StrongDual ℂ H(a,hα,hs)),
        Summable (fun z : Z(χ,a,α) ↦ ∑ m : Fin (N(χ,a,α,s,z)),
          L (jet(z,m)) (A(a,hα,hs,φ) ((g.smulRight v) (x (jet(z,m))))))) :
    ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C*(1+|z.val.2.2|)^d := by
  classical
  let K := k+1
  have hK : K ≠ 0 := Nat.succ_ne_zero k
  let I := {z : Z(χ,a,α) // z.val.1=η}
  let j (z : Z(χ,a,α)) (m : Fin (N(χ,a,α,s,z))) : J(χ,a,α,s) := jet(z,m)
  let P (z : I) := ∑ m : Fin (N(χ,a,α,s,z.val)), (L (j z.val m)).smulRight (x (j z.val m))
  let w (z : I) := ‖P z‖^((K:ℝ)⁻¹)
  have hw (z : I) : 0≤w z := Real.rpow_nonneg (norm_nonneg _) _
  have hp (z : I) : w z ^ K = ‖P z‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) hK
  have hfix (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) :
      BddAbove (range fun z : I ↦ ‖nuclearityTestMellin (χ η) φ (pt(b(z),t(z)))‖ * w z) := by
    let A := A(a,hα,hs,φ)
    obtain ⟨C,hC,hb⟩ := spectralConvolutionFiniteSum_singleton_norm_bound A x L _ j (hc φ hφ)
    obtain ⟨M,hM⟩ := (spectralNuclearityDenominator_closed_invariant_mellin (χ η) φ).2 (-α) α
    obtain ⟨B,hB,hbound⟩ := bounded_blocks_control_power A K (max M 0) (le_max_right _ _)
    refine ⟨max 1 (C*B),forall_mem_range.mpr fun z ↦ ?_⟩
    let c := nuclearityTestMellin (χ η) φ (pt(b(z),t(z)))
    have hce : ‖c‖ ≤ max M 0 := (hM _ (by simpa using z.val.property.1.1)
      (by simpa using z.val.property.1.2)).trans (le_max_left _ _)
    have hid : P z * A = spectralConvolutionFiniteSum A x L {z.val} _ j := by
      ext u
      change (P z) (A u) = _
      simp [P,spectralConvolutionFiniteSum,sum_apply]
    have heq := finite_block_triangular_annihilates ((hk z.val z.property).trans (Nat.le_succ _))
      (fun m ↦ L (j z.val m)) (fun m ↦ x (j z.val m)) A c (fun m u hu ↦ by
        have e := spectralStripConvolution_jet_top a hα hs χ L hj φ z.val m u hu
        rw [(spectralConvolution_mellin_integrable _ _ _).2] at e
        simpa only [c,nuclearityTestMellin,←z.property] using e)
    have h := hbound (P z) c hce heq
    rw [hid] at h
    have hpow : (‖c‖*w z)^K ≤ C*B := by
      rw [mul_pow,hp]; exact h.trans (mul_le_mul_of_nonneg_right (hb _) hB)
    change ‖c‖*w z ≤ _
    rcases le_total (‖c‖*w z) 1 with hl | hl
    · exact hl.trans (le_max_left _ _)
    · exact (le_self_pow₀ hl hK).trans (hpow.trans (le_max_right _ _))
  obtain ⟨C,hC,d,hd⟩ := LineModulation.homogeneous_strip_mellin_polynomial hα χ hχ η
    (fun z : I ↦ b(z)) (fun z : I ↦ t(z)) w (fun z ↦ abs_le.mpr z.val.property.1) hw hfix
  refine ⟨C^K,by positivity,d*K,fun z hz ↦ ?_⟩
  let u : I := ⟨z,hz⟩
  change ‖P u‖ ≤ _
  rw [←hp u, pow_mul,←mul_pow]
  exact pow_le_pow_left₀ (hw u) (hd u) K
#print axioms spectralStrip_complete_blocks_require_polynomial_projection_norms

/-- Polynomial growth of the complete projections suffices for every bounded insertion. -/
theorem spectralStrip_complete_block_bounded_insertions
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C*(1+|z.val.2.2|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) (U : H(a,hα,hs) →L[ℂ] H(a,hα,hs)) :
    Summable (fun z : Z(χ,a,α) ↦ ‖∑ m : Fin (N(χ,a,α,s,z)), L (jet(z,m)) (A(a,hα,hs,φ) (U (x (jet(z,m)))))‖) := by
  have hb := spectralStrip_polynomial_complete_projections_summable χ hχ a hα hs x L hj η k hk hpoly φ hφ
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun z ↦ finite_block_trace_insertion_le
    (fun m : Fin (N(χ,a,α,s,z)) ↦ (L (jet(z,m))).comp A(a,hα,hs,φ)) (fun m ↦ x (jet(z,m))) U) (hb.mul_left ‖U‖)
#print axioms spectralStrip_complete_block_bounded_insertions

private theorem complete_rectangles_of_rank_majorant {H J Z : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (L : J → StrongDual ℂ H) (N : Z → ℕ)
    (j : (z : Z) → Fin (N z) → J) (e : Z ↪ ℕ × ℕ)
    (hg : Summable (fun z ↦ (N z : ℝ)*‖∑ m, ((L (j z m)).comp A).smulRight (x (j z m))‖)) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn) N j) := by
  classical
  let g (z : Z) := (N z : ℝ)*‖∑ m, ((L (j z m)).comp A).smulRight (x (j z m))‖
  let T (z : Z) (m : Fin (N z)) : nuclearEndomorphisms H :=
    ⟨((L (j z m)).comp A).smulRight (x (j z m)), smulRight_mem_nuclearEndomorphisms _ _⟩
  let R (z : Z) := ∑ m, T z m
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  let : NormedAddCommGroup (nuclearEndomorphisms H) :=
    NormedAddCommGroup.ofCore (traceNorm_normedSpaceCore (H := H))
  let : SeminormedAddCommGroup (nuclearEndomorphisms H) :=
    (inferInstance : NormedAddCommGroup (nuclearEndomorphisms H)).toSeminormedAddCommGroup
  let : MetricSpace (nuclearEndomorphisms H) := NormedAddCommGroup.toMetricSpace
  let : PseudoMetricSpace (nuclearEndomorphisms H) := MetricSpace.toPseudoMetricSpace
  let : UniformSpace (nuclearEndomorphisms H) := PseudoMetricSpace.toUniformSpace
  have hR (z : Z) : ‖R z‖ ≤ g z :=
    finite_block_traceNorm_le (fun m ↦ (L (j z m)).comp A) (fun m ↦ x (j z m))
  have hc := cauchySeq_finset_of_norm_bounded_eventually hg (Eventually.of_forall hR)
  intro ε hε
  obtain ⟨S, hS⟩ := (Metric.cauchySeq_iff (u := fun s : Finset Z ↦ ∑ z ∈ s, R z)).mp hc ε hε
  let i := S.sup (fun z ↦ (e z).1)
  let k := S.sup (fun z ↦ (e z).2)
  let E (v : ℕ × ℕ) := ((Finset.Iic v.1).product (Finset.Iic v.2)).preimage e e.injective.injOn
  have hsub (v : ℕ × ℕ) (hv : (i, k) ≤ v) : S ≤ E v := by
    intro z hz
    simpa [E] using And.intro ((Finset.le_sup hz).trans hv.1) ((Finset.le_sup hz).trans hv.2)
  have heq (v : ℕ × ℕ) : (∑ z ∈ E v, R z).val = spectralConvolutionFiniteSum A x L (E v) N j := by
    simp only [R, T, Submodule.coe_sum, spectralConvolutionFiniteSum]
  refine ⟨(i, k), fun v w hv hw ↦ ⟨(∑ z ∈ E v, R z) - (∑ z ∈ E w, R z), ?_,?_⟩⟩
  · exact congrArg₂ (· - ·) (heq _) (heq _)
  · have hdist (T U : nuclearEndomorphisms H) : dist T U = traceNorm (T - U) := by
      rw [dist_eq_norm]
      rfl
    have hr := hS (E v) (hsub v hv) (E w) (hsub w hw)
    rwa [hdist] at hr

/-- The same whole-projection hypothesis gives rectangular Cauchy tails in trace norm. -/
theorem spectralStrip_complete_block_projections_trace_cauchy
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k)
    (hpoly : ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C*(1+|z.val.2.2|)^d)
    (φ : BruhatCompactSupport C𝔽) (hφ : hom(φ,η)) (e : Z(χ,a,α) ↪ ℕ × ℕ) :
    SpectralRectanglesTraceCauchy (fun i ↦ spectralConvolutionFiniteSum A(a,hα,hs,φ) x L
      (((Finset.Iic i.1).product (Finset.Iic i.2)).preimage e e.injective.injOn)
      (fun z : Z(χ,a,α) ↦ N(χ,a,α,s,z)) (fun z m ↦ jet(z,m))) :=
  complete_rectangles_of_rank_majorant _ _ _ _ _ e
    (spectralStrip_polynomial_complete_projections_summable χ hχ a hα hs x L hj η k hk hpoly φ hφ)
#print axioms spectralStrip_complete_block_projections_trace_cauchy

/-- For uniformly bounded multiplicity on one actual component, the universal compact-insertion
assertion for homogeneous tests is equivalent to polynomial growth of its whole block projections. -/
theorem spectralStrip_bounded_multiplicity_iff_polynomial_complete_projections
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k) :
    (∀ φ : BruhatCompactSupport C𝔽, (hom(φ,η)) →
      ∀ U : compactOperator (RingHom.id ℂ) H(a,hα,hs) H(a,hα,hs), Summable (fun z : Z(χ,a,α) ↦
        ∑ m : Fin (N(χ,a,α,s,z)), L (jet(z,m)) (A(a,hα,hs,φ) (U.val (x (jet(z,m))))))) ↔
    ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C*(1+|z.val.2.2|)^d := by
  constructor
  · intro h
    apply spectralStrip_complete_blocks_require_polynomial_projection_norms χ hχ a hα hs x L hj η k hk
    intro φ hφ v g
    exact h φ hφ ⟨g.smulRight v,(isCompactOperator_of_locallyCompactSpace_rng
      ((ContinuousLinearMap.id ℂ ℂ).smulRight v)).comp_clm g⟩
  · intro h φ hφ U
    exact (spectralStrip_complete_block_bounded_insertions χ hχ a hα hs x L hj η k hk h φ hφ U.val).of_norm
#print axioms spectralStrip_bounded_multiplicity_iff_polynomial_complete_projections


/-- The norm of a *whole* finite spectral coordinate projection is at most C precisely
when adding functionals from the other coordinates cannot shrink a functional of
the block by a factor greater than C. Both subspaces use actual realized jet forms. -/
private theorem spectralMarkushevich_block_projection_iff {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (x : I → E) (L : I → StrongDual ℂ E) (hb : IsSpectralMarkushevichBasis x L)
    (s : Finset I) {C : ℝ} (hC : 0 ≤ C) :
    ‖∑ i ∈ s, (L i).smulRight (x i)‖ ≤ C ↔
      ∀ f ∈ Submodule.span ℂ (L '' (s : Set I)), ∀ g ∈ Submodule.span ℂ (L '' (s : Set I)ᶜ),
        ‖f‖ ≤ C*‖f+g‖ := by
  classical
  let B := Submodule.span ℂ (L '' (s : Set I))
  let N := Submodule.span ℂ (L '' (s : Set I)ᶜ)
  let P := ∑ i ∈ s, (L i).smulRight (x i)
  let T := ∑ i ∈ s, (ContinuousLinearMap.apply ℂ ℂ (x i)).smulRight (L i)
  have hTf (f : StrongDual ℂ E) : T f = f.comp P := by
    ext u
    simp [T,P,sum_apply,smul_eq_mul,mul_comm]
  have hTL (i : I) : T (L i) = if i∈s then L i else 0 := by
    have hδ (j : I) : L i (x j) • L j = if j = i then L i else 0 := by
      split_ifs with h
      · subst j; rw [hb.1,one_smul]
      · rw [hb.2.1 _ _ h,zero_smul]
    simp only [T,sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.apply_apply,hδ,Finset.sum_ite_eq']
  have hB : B ≤ (T - ContinuousLinearMap.id ℂ _).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change T (L i) - L i = 0
    rw [hTL,ite_eq_left (show i∈s from hi),sub_self]
  have hN : N ≤ T.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change T (L i) = 0
    rw [hTL,ite_eq_right (show i∉s from hi)]
  have hmem (f : StrongDual ℂ E) : T f ∈ B := by
    dsimp only [T]
    rw [sum_apply]
    exact Submodule.sum_mem B fun i hi ↦ B.smul_mem _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  have hfar (f : StrongDual ℂ E) : f - T f ∈ N.topologicalClosure := by
    let U := ContinuousLinearMap.id ℂ (StrongDual ℂ E) - T
    have h : Submodule.span ℂ (range L) ≤ N.topologicalClosure.comap U.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change L i - T (L i) ∈ N.topologicalClosure
      rw [hTL]
      split_ifs with hi
      · rw [sub_self]; exact N.topologicalClosure.zero_mem
      · rw [sub_zero]; exact N.le_topologicalClosure (Submodule.subset_span ⟨i,hi,rfl⟩)
    exact (Submodule.topologicalClosure_minimal _ h
      (N.isClosed_topologicalClosure.preimage U.continuous)) (hb.2.2.2 f)
  change ‖P‖ ≤ C ↔ ∀ f ∈ B, ∀ g ∈ N, ‖f‖ ≤ C*‖f+g‖
  constructor
  · intro hp f hf g hg
    have hgf : T (f+g) = f := by
      have hf' : T f - f = 0 := hB hf
      rw [map_add,sub_eq_zero.mp hf',show T g=0 from hN hg,add_zero]
    calc
      ‖f‖ = ‖(f+g).comp P‖ := congrArg norm (hgf.symm.trans (hTf _))
      _ ≤ ‖f+g‖*‖P‖ := ContinuousLinearMap.opNorm_comp_le ..
      _ ≤ C*‖f+g‖ := (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_comm _ _)
  · intro h
    have hnorm (f : StrongDual ℂ E) : ‖T f‖ ≤ C*‖f‖ := by
      let S := {g : StrongDual ℂ E | ‖T f‖ ≤ C*‖T f + g‖}
      have hc : IsClosed S := isClosed_le continuous_const (continuous_const.mul (continuous_const.add continuous_id).norm)
      have hin : (N : Set _) ⊆ S := fun g hg ↦ h (T f) (hmem _) g hg
      have hx := closure_minimal hin hc (hfar f)
      change ‖T f‖ ≤ C*‖T f+(f-T f)‖ at hx
      simpa only [add_sub_cancel] using hx
    apply P.opNorm_le_bound hC
    intro v
    obtain ⟨f,hf,hv⟩ := exists_dual_vector'' ℂ (P v)
    have he : ‖T f v‖ = ‖P v‖ := by
      rw [hTf]; change ‖f (P v)‖ = _; rw [hv]
      change ‖(‖P v‖ : ℂ)‖ = _
      simp
    rw [← he]
    exact ((T f).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((hnorm f).trans (mul_le_of_le_one_right hC hf)) (norm_nonneg _))

/-- The norm bound on a whole zero projection is equivalent to separation of the
entire span of its realized jet forms from the span of all jets at other zeros. -/
theorem spectralStrip_complete_projection_iff_interpolation
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (a : ℝ) {α s : ℝ} (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hb : IsSpectralMarkushevichBasis x L) (z : Z(χ,a,α)) {C : ℝ} (hC : 0≤C) :
    ‖∑ m : Fin (N(χ,a,α,s,z)), (L (jet(z,m))).smulRight (x (jet(z,m)))‖ ≤ C ↔
      ∀ f ∈ Submodule.span ℂ (range fun m : Fin (N(χ,a,α,s,z)) ↦ L (jet(z,m))),
      ∀ g ∈ Submodule.span ℂ {g | ∃ (w : Z(χ,a,α)) (_ : w≠z) (m : Fin (N(χ,a,α,s,w))), g=L (jet(w,m))},
      ‖f‖ ≤ C*‖f+g‖ := by
  classical
  let j (w : Z(χ,a,α)) (m : Fin (N(χ,a,α,s,w))) : J(χ,a,α,s) := jet(w,m)
  let e : Fin (N(χ,a,α,s,z)) ↪ J(χ,a,α,s) :=
    ⟨j z,fun i l he ↦ Fin.ext (congrArg (fun u : J(χ,a,α,s) ↦ u.val.2.2.2) he)⟩
  let S := Finset.univ.map e
  have near : L '' (S : Set _) = range (fun m ↦ L (j z m)) := by
    ext f
    constructor
    · rintro ⟨i,hi,rfl⟩
      obtain ⟨m,_,rfl⟩ := Finset.mem_map.mp hi
      exact ⟨m,rfl⟩
    · rintro ⟨m,rfl⟩
      exact ⟨e m, Finset.mem_map.mpr ⟨m,Finset.mem_univ _,rfl⟩,rfl⟩
  have cover (u : J(χ,a,α,s)) : ∃ (w : Z(χ,a,α)) (m : Fin (N(χ,a,α,s,w))), j w m = u :=
    ⟨⟨(u.val.1,u.val.2.1,u.val.2.2.1),u.mem_strip_order_pos hα⟩,⟨u.val.2.2.2,u.property⟩,rfl⟩
  have far : L '' (S : Set _)ᶜ = {g | ∃ (w : Z(χ,a,α)) (_ : w≠z) (m : Fin (N(χ,a,α,s,w))), g=L (j w m)} := by
    ext g
    constructor
    · rintro ⟨u,hu,rfl⟩
      obtain ⟨w,m,rfl⟩ := cover u
      refine ⟨w,?_,m,rfl⟩
      rintro rfl
      exact hu (Finset.mem_map.mpr ⟨m,Finset.mem_univ _,rfl⟩)
    · rintro ⟨w,hw,m,rfl⟩
      refine ⟨j w m,?_,rfl⟩
      intro h
      obtain ⟨l,_,hl⟩ := Finset.mem_map.mp h
      exact hw (Subtype.ext (congrArg (fun u : J(χ,a,α,s) ↦ (u.val.1,u.val.2.1,u.val.2.2.1)) hl).symm)
  have H := spectralMarkushevich_block_projection_iff x L hb S hC
  rw [near,far] at H
  have he (m) : e m = j z m := rfl
  have hsum : (∑ i ∈ S, (L i).smulRight (x i)) = ∑ m, (L (j z m)).smulRight (x (j z m)) := by
    rw [show S = Finset.univ.map e from rfl,Finset.sum_map]
    exact Finset.sum_congr rfl fun m _ ↦ congrArg (fun i ↦ (L i).smulRight (x i)) (he m)
  rw [hsum] at H
  exact H
#print axioms spectralStrip_complete_projection_iff_interpolation

/-- For uniformly bounded multiplicity on one actual component, the universal compact-insertion
assertion is equivalent to an intrinsic interpolation estimate for every linear
combination of surviving jets at a site against all the jets at other sites. -/
theorem spectralStrip_bounded_multiplicity_iff_jet_subspace_separation
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (a : ℝ) {α s : ℝ}
    (hα : 0≤α) (hs : 1<s)
    (x : J(χ,a,α,s) → H(a,hα,hs)) (L : J(χ,a,α,s) → StrongDual ℂ H(a,hα,hs))
    (hb : IsSpectralMarkushevichBasis x L) (hj : ∀ i, D(a,hα,hs) (L i) = raw(χ,hα,hs,i)) (η : PontryaginDual C₁)
    (k : ℕ) (hk : ∀ z : Z(χ,a,α), z.val.1=η → N(χ,a,α,s,z) ≤ k) :
    (∀ φ : BruhatCompactSupport C𝔽, (hom(φ,η)) →
      ∀ U : compactOperator (RingHom.id ℂ) H(a,hα,hs) H(a,hα,hs), Summable (fun z : Z(χ,a,α) ↦
        ∑ m : Fin (N(χ,a,α,s,z)), L (jet(z,m)) (A(a,hα,hs,φ) (U.val (x (jet(z,m))))))) ↔
    ∃ C≥(0:ℝ), ∃ d : ℕ, ∀ z : Z(χ,a,α), z.val.1=η →
      ∀ f ∈ Submodule.span ℂ (range fun m : Fin (N(χ,a,α,s,z)) ↦ L (jet(z,m))),
      ∀ g ∈ Submodule.span ℂ {g | ∃ (w : Z(χ,a,α)) (_ : w≠z) (m : Fin (N(χ,a,α,s,w))), g=L (jet(w,m))},
        ‖f‖ ≤ (C*(1+|z.val.2.2|)^d)*‖f+g‖ := by
  rw [spectralStrip_bounded_multiplicity_iff_polynomial_complete_projections χ hχ a hα hs x L hj η k hk]
  constructor <;> rintro ⟨C,hC,d,hh⟩ <;> refine ⟨C,hC,d,fun z hz ↦ ?_⟩
  · exact (spectralStrip_complete_projection_iff_interpolation χ a hα hs x L hb z (by positivity)).mp (hh z hz)
  · exact (spectralStrip_complete_projection_iff_interpolation χ a hα hs x L hb z (by positivity)).mpr (hh z hz)
#print axioms spectralStrip_bounded_multiplicity_iff_jet_subspace_separation

end RiemannMasullo
