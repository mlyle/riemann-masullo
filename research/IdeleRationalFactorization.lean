module
import Lean
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import all RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Dixmier–Malliavin factorization for rational idele classes

Every compactly supported Bruhat test on the rational idele class group is an algebraic
finite sum of test convolutions with the Tamagawa Haar measure. More generally, the proof
applies over any number field whose compact norm-one idele class group is totally disconnected.

A compact Bruhat test is invariant under an open subgroup of the compact norm-one group.
Finite Fourier inversion splits it into homogeneous tests, and the single-character
factorization proved in Chapter 10, §3 applies to each summand. For the rational field, the
norm-one group embeds into the product of the nonarchimedean local unit groups.

This fork-only check imports Chapter 10's private homogeneous factorization proof and runs a
transitive audit against all proof terms at the end. From the pinned repository root run
`lake build RiemannMasullo.Ch10_TraceSpectral.Sec3`, then
`lake env lean research/IdeleRationalFactorization.lean`.
-/

open Filter MeasureTheory NumberField Function Set IsDedekindDomain
open scoped NNReal NumberField.AdeleRing Topology BigOperators
noncomputable section
set_option quotPrecheck false
namespace RiemannMasullo.Isolated.Factorization
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "G₀" => IdeleClassGroup (𝓞 F) F
local notation "K" => (ideleClassNorm F).ker
local notation "D" => BruhatCompactSupport G₀
local notation "μ" => ideleClassTamagawaMeasure F
private abbrev homogeneousSums := AddSubmonoid.closure {θ : D | ∃ ω : PontryaginDual K,
  ∀ (c : K) (x : G₀), θ.val (c.val⁻¹*x) = (ω c : ℂ) * θ.val x}

private def moved (c : K) (φ : D) : D := by
  refine ⟨fun x ↦ φ.val (c.val*x), (mem_bruhatSmoothSubmodule_iff _).mpr (fun p ↦ ?_), ?_⟩
  · let m : G₀ →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm F
    have hm : IsModulation (G := G₀) m := by
      change IsProperMap (ideleClassNorm F) ∧ ∃ g, ideleClassNorm F g ≠ 1
      exact ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    have hs : Surjective m := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
    have hf := bruhatCompactSupport_le_modulatedExponentialDecay (G := G₀) m ({0} : Set ℝ) hm hs φ.property
    rw [modulatedExponentialDecaySubmodule_singleton_zero] at hf
    let w := schwartzBruhatTranslate (c.val⁻¹) (⟨φ.val, hf⟩ : SchwartzBruhat G₀)
    have he : (fun x ↦ w x) = (fun x ↦ φ.val (c.val*x)) := by
      funext x
      exact congrArg (fun y : G₀ ↦ φ.val (y*x)) (inv_inv c.val)
    exact he ▸ schwartzBruhat_isBruhatSmooth w p
  · exact φ.property.2.comp_homeomorph (Homeomorph.mulLeft c.val)

variable {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
private abbrev Char (A : Type*) [CommGroup A] := AddChar (Additive A) ℂ
private abbrev value (ψ : Char A) (a : A) := ψ (Additive.ofMul a)
private def lifted (π : K →ₜ* A) (ψ : Char A) : PontryaginDual K :=
  { toFun := fun c ↦ ⟨value ψ (π c), mem_sphere_zero_iff_norm.mpr (ψ.norm_apply _)⟩
    map_one' := Circle.ext (by change value ψ (π 1) = 1; rw [map_one]; exact ψ.map_zero_eq_one)
    map_mul' := fun c d ↦ Circle.ext (by change value ψ (π (c*d)) = value ψ (π c) * value ψ (π d); rw [map_mul]; exact ψ.map_add_eq_mul _ _)
    continuous_toFun := (continuous_of_discreteTopology (f := fun a : A ↦ (⟨value ψ a, mem_sphere_zero_iff_norm.mpr (ψ.norm_apply _)⟩ : Circle))).comp π.continuous }

private def evaluate (x : G₀) : D →+ ℂ where
  toFun φ := φ.val x
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

private theorem finite_quotient (φ : D) (π : K →ₜ* A) (hπ : Surjective π)
    (hinv : ∀ c : K, π c = 1 → ∀ x : G₀, φ.val (c.val*x) = φ.val x) : φ ∈ homogeneousSums (F := F) := by
  classical
  choose s hs using hπ
  let : Fintype (Char A) := Fintype.ofFinite _
  let N : ℂ := Fintype.card A
  let f (ψ : Char A) : D := N⁻¹ • ∑ a : A, value ψ a • moved (s a) φ
  have hval (ψ : Char A) (x : G₀) : (f ψ).val x = N⁻¹* ∑ a : A, value ψ a * φ.val ((s a).val*x) := by
    change N⁻¹ * ((∑ a : A, value ψ a • moved (s a) φ : D).val x) = _
    congr 1
    exact map_sum (evaluate x) _ _
  have hsx (r q : K) (h : π r = π q) (x : G₀) : φ.val (r.val*x) = φ.val (q.val*x) := by
    have he := hinv (r/q) (by rw [map_div, h, div_self']) (q.val*x)
    simpa [div_eq_mul_inv, mul_assoc] using he
  have hmem (ψ : Char A) : f ψ ∈ homogeneousSums (F := F) := by
    apply AddSubmonoid.subset_closure
    refine ⟨lifted π ψ, ?_⟩
    intro c x
    rw [hval, hval]
    change N⁻¹ * _ = value ψ (π c) * (N⁻¹ * _)
    rw [mul_left_comm (value ψ (π c)) N⁻¹]
    congr 1
    rw [Finset.mul_sum]
    let e := Equiv.mulRight (π c)
    symm
    apply Fintype.sum_equiv e
    intro a
    change value ψ (π c) * (value ψ a * φ.val ((s a).val * x)) =
      value ψ (a * π c) * φ.val ((s (a*π c)).val * (c.val⁻¹*x))
    have he := hsx (s (a*π c) / c) (s a) (by simp [hs]) x
    rw [show (s (a*π c)).val * (c.val⁻¹*x) = (s (a*π c)/c).val*x by change _ = ((s (a * π c)).val / c.val) * x; rw [div_eq_mul_inv]; exact (mul_assoc (s (a * π c)).val c.val⁻¹ x).symm, he]
    unfold value; rw [ofMul_mul, AddChar.map_add_eq_mul]; ring
  have hsum : (∑ ψ : Char A, f ψ) = φ := by
    apply Subtype.ext; funext x
    have ev := map_sum (evaluate x) f Finset.univ
    change evaluate x (∑ ψ : Char A, f ψ) = φ.val x
    rw [ev]; change (∑ ψ : Char A, (f ψ).val x) = φ.val x
    simp only [hval, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have orth (a : A) : (∑ ψ : Char A, value ψ a) = if a = 1 then N else 0 := by
      simpa [value, N, ofMul_eq_zero] using AddChar.sum_apply_eq_ite (Additive.ofMul a)
    simp_rw [orth]
    simp [N, hsx (s 1) 1 (by simp [hs])]
  rw [← hsum]
  exact AddSubmonoid.sum_mem _ (fun i _ ↦ hmem i)

private theorem open_period [TotallyDisconnectedSpace K] (φ : D) :
    ∃ H : OpenSubgroup K, ∀ c ∈ H, ∀ x : G₀, φ.val (c.val * x) = φ.val x := by
  let : IsMulCommutative G₀ := .of_comm (fun a b ↦ mul_comm a b)
  let : IsMulCommutative K := .of_comm (fun a b ↦ Subtype.ext (mul_comm a.val b.val))
  let : CompactSpace K := (ideleClassGroup_finiteness F).2.1
  obtain ⟨U, hU, hperiod, _⟩ := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 0
  let : IsClosed (U : Set G₀) := hU.1
  let q : K →ₜ* G₀ ⧸ U := ⟨(QuotientGroup.mk' U).comp (ideleClassNorm F).ker.subtype,
      (QuotientGroup.continuous_mk).comp continuous_subtype_val⟩
  letI : T1Space (G₀ ⧸ U) := QuotientGroup.t1Space_iff.mpr hU.1
  obtain ⟨e, _⟩ := lcaQuotientDual_equiv_annihilator U hU.1
  have hloc := isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (isCompactlyGeneratedGroup_of_continuousMulEquiv e.symm hU.2.2)
  obtain ⟨W, hW, hpow⟩ := exists_nhds_one_of_isLocallyEuclidean hloc
  have hq : q ⁻¹' W ∈ 𝓝 (1:K) := q.continuous.continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨C, hC, h1C, hCW⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hq
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hC h1C
  refine ⟨H, fun c hc ↦ ?_⟩
  have hqc : q c = 1 := hpow (q c) (fun n ↦ by rw [← map_pow]; exact hCW (hH (H.pow_mem hc n)))
  exact hperiod ⟨c.val,(QuotientGroup.eq_one_iff _).mp hqc⟩

private theorem factor_totally_disconnected [TotallyDisconnectedSpace K] (φ : D) : φ ∈ homogeneousSums (F := F) := by
  classical
  let : IsMulCommutative G₀ := .of_comm (fun a b ↦ mul_comm a b)
  let : IsMulCommutative K := .of_comm (fun a b ↦ Subtype.ext (mul_comm a.val b.val))
  let : CompactSpace K := (ideleClassGroup_finiteness F).2.1
  obtain ⟨H, hH⟩ := open_period φ
  let : CommGroup K := { (inferInstance : Group K) with mul_comm := fun a b ↦ Subtype.ext (mul_comm a.val b.val) }
  let U : Subgroup K := H.toSubgroup
  let hdis : DiscreteTopology (K ⧸ U) := discreteTopology_iff_isOpen_singleton_one.mpr (by
    rw [← (QuotientGroup.isQuotientMap_mk U).isOpen_preimage]; convert H.isOpen using 1; ext a; exact QuotientGroup.eq_one_iff _)
  let : Fintype (K ⧸ U) := @Fintype.ofFinite _ (finite_of_compact_of_discrete (X := K ⧸ U))
  let π : K →ₜ* K ⧸ U := ⟨QuotientGroup.mk' U, QuotientGroup.continuous_mk⟩
  have hs : Function.Surjective π := @QuotientGroup.mk_surjective K _ U
  apply finite_quotient (F := F) (A := K ⧸ U) φ π hs
  intro c hc
  exact hH c ((QuotientGroup.eq_one_iff _).mp hc)

local notation "VQ" => HeightOneSpectrum (𝓞 ℚ)
local notation "UQ" => (v:VQ) → (v.adicCompletionIntegers ℚ)ˣ
local notation "CQ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "KQ" => (ideleClassNorm ℚ).ker
private theorem rat_normOne_totally_disconnected : TotallyDisconnectedSpace KQ := by
  let : CompactSpace KQ := (ideleClassGroup_finiteness ℚ).2.1
  obtain ⟨e, _⟩ := ratIdeleClassGroup_decomposition
  let r : CQ →ₜ* ℝ≥0ˣ := ⟨(MonoidHom.fst ℝ≥0ˣ UQ).comp e.symm.toMonoidHom, continuous_fst.comp e.symm.continuous⟩
  let : CommGroup KQ := { (inferInstance : Group KQ) with mul_comm := fun a b ↦ Subtype.ext (mul_comm a.val b.val) }
  let rc : KQ →ₜ* ℝ≥0ˣ := ⟨r.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype, r.continuous.comp continuous_subtype_val⟩
  have hr (c : KQ) : r c.val = 1 := compactSubgroup_le_modulation_ker rc ⊤ (by simpa using (isCompact_univ : IsCompact (univ:Set KQ))) (Subgroup.mem_top c)
  let ι : KQ → UQ := fun c ↦ (e.symm c.val).2
  have hc : Continuous ι := (continuous_snd.comp e.symm.continuous).comp continuous_subtype_val
  have hi : Injective ι := by
    intro c d he
    apply Subtype.ext; apply e.symm.injective; apply Prod.ext _ he
    exact (hr c).trans (hr d).symm
  let (v : VQ) : TotallyDisconnectedSpace (v.adicCompletionIntegers ℚ)ˣ :=
    ⟨isTotallyDisconnected_of_image ((continuous_subtype_val.comp Units.continuous_val).continuousOn) (Subtype.val_injective.comp Units.val_injective)
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  exact ⟨isTotallyDisconnected_of_image hc.continuousOn hi (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- On a totally disconnected norm-one idele class group, finite Fourier decomposition
and the existing single-character theorem yield compactly supported convolution factors. -/
public theorem factorization_of_normOne_totallyDisconnected [TotallyDisconnectedSpace K] (φ : D) :
    φ ∈ AddSubmonoid.closure {θ : D | ∃ u v : D, θ.val = lcaConvolution μ u.val v.val} := by
  apply AddSubmonoid.closure_le.mpr _ (factor_totally_disconnected φ)
  rintro θ ⟨ω, hθ⟩
  apply AddSubmonoid.closure_mono _ (spectralHomogeneousTest_convolution_factorization ω θ hθ)
  rintro ψ ⟨u, v, _, _, huv⟩
  exact ⟨u, v, huv⟩

/-- Every rational idele-class test is a finite sum of compact test convolutions. -/
public theorem rational_convolution_factorization (φ : BruhatCompactSupport CQ) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport CQ | ∃ u v : BruhatCompactSupport CQ,
      θ.val = lcaConvolution (ideleClassTamagawaMeasure ℚ) u.val v.val} := by
  let := rat_normOne_totally_disconnected
  exact factorization_of_normOne_totallyDisconnected φ

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
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; direct admissions: {directSorry}; kernel axioms {axioms}"


run_cmd auditRoot ``finite_quotient
run_cmd auditRoot ``open_period
run_cmd auditRoot ``factor_totally_disconnected
run_cmd auditRoot ``rat_normOne_totally_disconnected
run_cmd auditRoot ``factorization_of_normOne_totallyDisconnected
run_cmd auditRoot ``rational_convolution_factorization
end RiemannMasullo.Isolated.Factorization
