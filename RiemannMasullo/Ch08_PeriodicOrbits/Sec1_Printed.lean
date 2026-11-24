module

public import RiemannMasullo.Ch08_PeriodicOrbits.Sec1
import Mathlib.Algebra.Field.ULift
import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b_PolarFreeExamples
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Printed claims from §8.1 that fail -/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set
open scoped BigOperators NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 1000000

universe u

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "PicTrivial(" F ", " S ")" => Subsingleton (CommRing.Pic ((S : Set V(F)).integer F))
local notation "fullFibre(" S ", " p ")" => (∀ v ∉ S, HeightOneSpectrum.under (𝓞 ℚ) v ≠ p)
local notation "zeroExtension(" g ")" => Function.extend Units.val g (fun _ ↦ 0)

local notation "C(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "res(" F ", " χ ")" => (χ : PontryaginDual C(F)).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C(F))

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
The projective tensor product identifies by pointwise multiplication with a closed
subspace of the additive tests. The predicate specifies what is claimed of that subspace.
The tensor factors are grouped in the order archimedean, punctured, additive, using the
canonical permutation in (8.1.0.4). -/
def Printed.orbitalSupportTensorImage {F : Type u} [Field F] [NumberField F]
    (S T : Finset V(F)) (claim : Submodule ℂ ℬ(SAdeleRing F S) → Prop) : Prop :=
  let A := ↥(sLocalOrbitalArchimedeanFlatTests F)
  let H := FiniteProjectiveTensor (fun v : {v : S // v.val ∉ T} ↦
    SchwartzBruhat (v.val.val.adicCompletion F)ˣ)
  let G := FiniteProjectiveTensor (fun v : {v : S // v.val ∈ T} ↦ ℬ(v.val.val.adicCompletion F))
  ∃ U : Submodule ℂ ℬ(SAdeleRing F S), IsClosed (U : Set ℬ(SAdeleRing F S)) ∧
    (∃ e : ProjectiveTensor (ProjectiveTensor A H) G ≃L[ℂ] U,
      ∀ (a : A) (h : ∀ v : {v : S // v.val ∉ T}, SchwartzBruhat (v.val.val.adicCompletion F)ˣ)
        (g : ∀ v : {v : S // v.val ∈ T}, ℬ(v.val.val.adicCompletion F)) (x : SAdeleRing F S),
        (e ((show ProjectiveTensor A H from a ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, h v)) ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v))).val
            (Multiplicative.ofAdd x) = a.val (Multiplicative.ofAdd x.1) *
          (∏ v : {v : S // v.val ∉ T}, zeroExtension(h v) (x.2 v.val)) *
          (∏ v : {v : S // v.val ∈ T}, g v (Multiplicative.ofAdd (x.2 v.val)))) ∧ claim U

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The inclusion of the displayed tensor subspace induces an equivalence modulo principal
value on homogeneous theta classes. Its action on representatives specifies the map.
Deviation: Both source denominators use the source numerator, as in the intersection on
p. 384. Literally (8.1.0.1) has a global denominator and (8.1.0.3) has a free index p. -/
def Printed.orbitalSupportQuotientEquiv {F : Type u} [Field F] [NumberField F]
    {S T : Finset V(F)} (hT : T ⊆ S) (η : PontryaginDual J₁(F, S))
    (U : Submodule ℂ ℬ(SAdeleRing F S)) : Prop :=
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S η
  let P := sAdelePrincipalValue F hT
  let D := (sLocalHomogeneousThetaPrincipalValue hT η).range
  ∃ h : ∀ f : U, P f.val ∈ U,
    let P' := LinearMap.codRestrict U (P.domRestrict U) h
    let R := (θ.domRestrict U).ker ⊔ P'.range
    ∃ e : (↥U ⧸ R) ≃L[ℂ] (SLocalHomogeneousThetaSpace F S η ⧸ D),
      ∀ f : U, e (R.mkQ f) = D.mkQ (θ.ker.mkQ f.val)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
The printed tensor product with full multiplicative factors off the primary fibre
embeds as a closed subspace of the additive tests with its projective tensor topology. -/
def Printed.sLocalPrimaryOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)), NormOneCharacterUnramifiedOutside (res(F, χ)) S →
      Printed.orbitalSupportTensorImage S (sLocalPrimaryPlaces S p) (fun _ ↦ True)

/-- Nontrivial circle powers cannot all have real part greater than one half. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_circle (u : Circle)
    (hu : ∀ n : ℕ, 1 / 2 < ((u : ℂ) ^ n).re) : u = 1 := by
  by_contra h
  have hne : (u : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h' ↦ h (Subtype.ext h')
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / ‖(u : ℂ) - 1‖)
  have hs : (n : ℝ) / 2 ≤ (∑ k ∈ Finset.range n, (u : ℂ) ^ k).re := by
    rw [Complex.re_sum]
    simpa [div_eq_mul_inv] using Finset.sum_le_sum (s := Finset.range n) (fun i _ ↦ (hu i).le)
  have hb : ‖(u : ℂ) ^ n - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖(u : ℂ) ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [norm_pow, Circle.norm_coe, one_pow, norm_one]; norm_num
  rw [← geom_sum_mul _ n, norm_mul] at hb
  have hmul := mul_le_mul_of_nonneg_right
    (hs.trans (Complex.re_le_norm _)) (norm_nonneg ((u : ℂ) - 1))
  have hp := (div_lt_iff₀ (norm_pos_iff.mpr hne)).mp hn
  nlinarith

open Filter Topology in
/-- An elementary group has an identity neighborhood containing no nontrivial cyclic group. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_elementary
    {m n r : ℕ} {F : Type*}
    [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F] :
    ∃ U ∈ 𝓝 (0 : ElementaryLieGroup m n r F),
      ∀ x : ElementaryLieGroup m n r F, (∀ k : ℕ, k • x ∈ U) → x = 0 := by
  let U : Set (ElementaryLieGroup m n r F) := {x | ‖x.1‖ < 1 ∧
    (∀ i : Fin n, 1 / 2 < ((AddCircle.toCircle (x.2.1 i) : Circle) : ℂ).re) ∧
    x.2.2 = 0}
  have htorus : ∀ i : Fin n, ∀ᶠ x : ElementaryLieGroup m n r F in 𝓝 0,
      1 / 2 < ((AddCircle.toCircle (x.2.1 i) : Circle) : ℂ).re := by
    intro i
    have hc : Continuous fun x : ElementaryLieGroup m n r F ↦
        ((AddCircle.toCircle (x.2.1 i) : Circle) : ℂ).re :=
      Complex.continuous_re.comp (continuous_subtype_val.comp
        (AddCircle.continuous_toCircle.comp ((continuous_apply i).comp continuous_snd.fst)))
    exact (continuousAt_const.eventually_lt hc.continuousAt (by simp; norm_num))
  have hreal : ∀ᶠ x : ElementaryLieGroup m n r F in 𝓝 0, ‖x.1‖ < 1 :=
    continuous_fst.norm.continuousAt.eventually_lt continuousAt_const (by simp)
  have hdisc : ∀ᶠ x : ElementaryLieGroup m n r F in 𝓝 0, x.2.2 = 0 := by
    have h : ContinuousAt (fun x : ElementaryLieGroup m n r F ↦ x.2.2) 0 :=
      (continuous_snd.snd :
      Continuous (fun x : ElementaryLieGroup m n r F ↦ x.2.2)).continuousAt
    have hz : ({0} : Set ((Fin r → ℤ) × F)) ∈ 𝓝 0 :=
      (isOpen_discrete ({0} : Set ((Fin r → ℤ) × F))).mem_nhds (by simp)
    exact h.eventually hz
  refine ⟨U, hreal.and ((eventually_all.mpr htorus).and hdisc), fun x hx ↦ ?_⟩
  have hr : x.1 = 0 := by
    by_contra h
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ‖x.1‖)
    have hlt := (hx k).1
    change ‖k • x.1‖ < 1 at hlt
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hlt
    exact (not_lt_of_ge ((div_lt_iff₀ (norm_pos_iff.mpr h)).mp hk).le) hlt
  have ht : x.2.1 = 0 := by
    funext i
    apply AddCircle.injective_toCircle (one_ne_zero : (1 : ℝ) ≠ 0)
    rw [Pi.zero_apply, AddCircle.toCircle_zero]
    apply Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_circle
    intro k
    have hki := (hx k).2.1 i
    change 1 / 2 < ((AddCircle.toCircle (k • x.2.1 i) : Circle) : ℂ).re at hki
    simpa only [AddCircle.toCircle_nsmul, Circle.coe_pow] using hki
  exact Prod.ext hr (Prod.ext ht (by simpa using (hx 1).2.2))

open Filter Topology in
/-- Powers staying in a small identity neighborhood force membership in the stage kernel. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_stageNhd
    {G : Type*} [CommGroup G]
    [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    ∃ U ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ U) → x ∈ OrderDual.ofDual a.val.2 := by
  let q : a.val.1 →* a.quotient := QuotientGroup.mk' _
  let f := e.equiv.toMulEquiv.toMonoidHom.comp q
  obtain ⟨W, hW, hsmall⟩ := Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_elementary
    (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  have hf : Continuous f := e.equiv.continuous_toFun.comp QuotientGroup.continuous_mk
  have hpre : f ⁻¹' W ∈ 𝓝 (1 : a.val.1) := by
    apply hf.continuousAt.preimage_mem_nhds
    rwa [map_one f]
  refine ⟨Subtype.val '' (f ⁻¹' W),
    a.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hpre, fun x hx ↦ ?_⟩
  obtain ⟨y, _, rfl⟩ := (pow_one x ▸ hx 1 : x ∈ Subtype.val '' (f ⁻¹' W))
  apply (a.quotient_mk_eq_one y).mp
  apply e.equiv.injective
  rw [map_one e.equiv]
  apply hsmall (f y)
  intro k
  change (f y) ^ k ∈ W
  rw [← map_pow]
  obtain ⟨z, hz, hzy⟩ := hx k
  exact (Subtype.ext hzy : z = y ^ k) ▸ hz

/-- A stage realization is invariant under translation by its kernel. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_stagePeriod
    {G : Type*} [CommGroup G]
    [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e)
    {g : G} (hg : g ∈ OrderDual.ofDual a.val.2) (x : G) :
    schwartzBruhatStageRealization a e s (g * x) = schwartzBruhatStageRealization a e s x := by
  classical
  have hh := a.property.2.2.2 hg
  simp only [schwartzBruhatStageRealization_apply, a.val.1.mul_mem_cancel_left hh]
  split_ifs with hx
  · let u : a.val.1 := ⟨g, hh⟩
    let v : a.val.1 := ⟨x, hx⟩
    have hu := (a.quotient_mk_eq_one u).mpr hg
    have huv : (QuotientGroup.mk (u * v) : a.quotient) = QuotientGroup.mk v := by
      rw [QuotientGroup.mk_mul, hu, one_mul]
    exact congrArg (fun q : a.quotient ↦ s (e.equiv q).toAdd) huv
  · rfl

open Filter Topology in
/-- A structural stage gives a common additive period in each nonarchimedean direction. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_periodic
    {G H : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [AddGroup H] [TopologicalSpace H]
    [NonarchimedeanAddGroup H] (j : Multiplicative H →* G)
    (hj : Continuous j) (f : SchwartzBruhat G) :
    ∀ᶠ y : H in 𝓝 0, ∀ x, f (j (Multiplicative.ofAdd y) * x) = f x := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff (f : G → ℂ)).mp
    ((SchwartzBruhat.toSubmodule G f).property)
  obtain ⟨U, hU, hker⟩ := Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_stageNhd a e
  have hJ : (j ∘ Multiplicative.ofAdd) ⁻¹' U ∈ 𝓝 (0 : H) :=
    (hj.comp continuous_ofAdd).continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hJ
  filter_upwards [V.isOpen.mem_nhds V.zero_mem] with y hy x
  rw [← hs]
  apply Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_stagePeriod a e s _ x
  apply hker
  intro k
  have h := hV (V.nsmul_mem hy k)
  change j (Multiplicative.ofAdd (k • y)) ∈ U at h
  simpa only [ofAdd_nsmul, map_pow] using h


open scoped ContDiff in
/-- The geometric sequence on the nonnegative integers is a Schwartz function on ℤ. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_geomStage
    (q : ℝ) (hq : 1 < q) :
    (fun y : ElementaryLieGroup 0 0 1 PUnit ↦
      if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0) ∈
      elementarySchwartzSubmodule 0 0 1 PUnit := by
  let f : ElementaryLieGroup 0 0 1 PUnit → ℂ := fun y ↦
    if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0
  have hconst (z : Fin 1 → ℤ) (b : PUnit)
      (x : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) :
      f (elementaryCover x z b) = f (0, 0, z, b) := rfl
  refine ⟨fun z b ↦ ?_, fun ⟨α, β, γ, δ⟩ ↦ ?_⟩
  · change ContDiff ℝ (∞ : ℕ∞ω) (fun x ↦ f (elementaryCover x z b))
    simp only [hconst]
    exact contDiff_const
  obtain rfl : β = 0 := Subsingleton.elim _ _
  obtain rfl : γ = 0 := Subsingleton.elim _ _
  have hdecay := tendsto_pow_const_div_const_pow_of_one_lt (δ 0) hq
  obtain ⟨C, hC⟩ := hdecay.bddAbove_range
  change elementarySchwartzBound f (α, 0, 0, δ) < ⊤
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := max 0 C))
  simp only [elementarySchwartzBound, elementaryPartial_zero, Finset.univ_eq_empty,
    Finset.prod_empty, one_mul, hconst]
  refine iSup_le fun x ↦ iSup_le fun z ↦ iSup_le fun b ↦ ?_
  simp only [f, Fin.prod_univ_one]
  split_ifs with h
  · have hcast (a : ℂ) : (‖a‖₊ : ENNReal) = ENNReal.ofReal ‖a‖ := (ofReal_norm a).symm
    rw [hcast]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (le_of_lt (zero_lt_one.trans hq)), Complex.norm_intCast,
      abs_of_nonneg (Int.cast_nonneg h), inv_pow, ← div_eq_mul_inv]
    have hz : (↑(z 0).toNat : ℝ) = (z 0 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h
    rw [← hz]
    exact (hC (Set.mem_range_self (z 0).toNat)).trans (le_max_right _ _)
  · simp

open Filter Topology in
/-- A discrete valuation with compact open kernel carries a Schwartz–Bruhat test with
geometric values on the powers of a uniformizing element. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_geomValuation
    {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (d : G →* Multiplicative ℤ) (π : G) (hπ : d π = Multiplicative.ofAdd 1)
    (ho : IsOpen (d.ker : Set G)) (hc : IsCompact (d.ker : Set G))
    (q : ℝ) (hq : 1 < q) :
    ∃ k : SchwartzBruhat G, ∀ n : ℕ, k (π ^ n) = (q : ℂ)⁻¹ ^ n := by
  classical
  have hgen : IsCompactlyGeneratedGroup G := by
    refine ⟨insert π (d.ker : Set G), mem_of_superset (ho.mem_nhds d.ker.one_mem)
      (Set.subset_insert _ _), hc.insert π, top_unique fun x _ ↦ ?_⟩
    let H := Subgroup.closure (insert π (d.ker : Set G))
    have hpH : π ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have hx : x * π ^ (-(d x).toAdd) ∈ d.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hπ]
      change Multiplicative.ofAdd ((d x).toAdd + (-(d x).toAdd) * 1) = 1
      simp
    have hxH : x * π ^ (-(d x).toAdd) ∈ H :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
    simpa [mul_assoc, ← zpow_add] using H.mul_mem hxH (H.zpow_mem hpH (d x).toAdd)
  let A : BruhatStructuralPair G := ⟨(⊤, OrderDual.toDual d.ker), by simp,
    isCompactlyGeneratedGroup_of_continuousMulEquiv
      (⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩ :
        G ≃ₜ* (⊤ : Subgroup G))
      hgen,
    ⟨hc.isClosed, isOpen_lcaAnnihilator _ hc, by
      let : CompactSpace (lcaAnnihilator d.ker) :=
        isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator _ ho)
      exact (isCompactlyGeneratedGroup_of_compact (G := lcaAnnihilator d.ker))⟩, le_top⟩
  let dTop : (⊤ : Subgroup G) →* Multiplicative ℤ := d.comp (⊤ : Subgroup G).subtype
  have hd : Function.Surjective dTop := by
    intro n
    refine ⟨⟨π ^ n.toAdd, trivial⟩, ?_⟩
    change d (π ^ n.toAdd) = n
    rw [map_zpow, hπ]
    change Multiplicative.ofAdd (n.toAdd * 1) = n
    simp
  let E : A.quotient ≃* Multiplicative ℤ := QuotientGroup.quotientKerEquivOfSurjective dTop hd
  let : DiscreteTopology A.quotient := QuotientGroup.discreteTopology
    (ho.preimage continuous_subtype_val)
  let L : ℤ ≃+ ElementaryLieGroup 0 0 1 PUnit :=
    { toFun := fun n ↦ (0, 0, fun _ ↦ n, PUnit.unit)
      invFun := fun y ↦ y.2.2.1 0
      left_inv := fun _ ↦ rfl
      right_inv := fun y ↦ Prod.ext (Subsingleton.elim _ _) (Prod.ext
        (Subsingleton.elim _ _) (Prod.ext (funext fun i ↦ congrArg y.2.2.1 (Subsingleton.elim 0 i))
          (Subsingleton.elim _ _)))
      map_add' := fun _ _ ↦ Prod.ext (Subsingleton.elim _ _)
        (Prod.ext (Subsingleton.elim _ _) rfl) }
  let e : ElementaryLCAPresentation A.quotient :=
    ⟨0, 0, 1, PUnit, ⟨E.trans L.toMultiplicative,
      continuous_of_discreteTopology, continuous_of_discreteTopology⟩⟩
  let s : SchwartzBruhatStage e :=
    ⟨_, Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_geomStage q hq⟩
  refine ⟨schwartzBruhatStageInclusion A e s, fun n ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show π ^ n ∈ A.val.1 from trivial)]
  have hn : (d (π ^ n)).toAdd = (n : ℤ) := by simp [map_pow, hπ]
  change (if 0 ≤ (d (π ^ n)).toAdd then (q : ℂ)⁻¹ ^ (d (π ^ n)).toAdd.toNat else 0) = _
  rw [hn, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

/-- A finite-place multiplicative Schwartz test with geometric values on the powers of a
uniformizing element, over any number field. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_shellTest
    {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (π : (v.adicCompletion F)ˣ) (k : SchwartzBruhat (v.adicCompletion F)ˣ),
      ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ ∧
        ∀ n : ℕ, k (π ^ n) = (v.asIdeal.absNorm : ℂ)⁻¹ ^ n := by
  let K := v.adicCompletion F
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨p, hp⟩ := V.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (p : K) hp.ne_zero
  have hπ : V.IsUniformizer π.val := hp
  have hvπ : V π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective F)))
  let d : Kˣ →* Multiplicative ℤ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (-(WithZero.log (V x.val)))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), neg_add]
        rfl }
  have hdπ : d π = Multiplicative.ofAdd 1 := by
    change Multiplicative.ofAdd (-(WithZero.log (V π.val))) = _
    simp [hvπ]
  have hk : (d.ker : Set Kˣ) = (v.adicCompletionIntegers F).units := by
    ext x
    change x ∈ d.ker ↔ x ∈ (v.adicCompletionIntegers F).units
    rw [MonoidHom.mem_ker, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change Multiplicative.ofAdd (-(WithZero.log (V x.val))) = Multiplicative.ofAdd 0 ↔
      V x.val = 1
    rw [Equiv.apply_eq_iff_eq, neg_eq_zero]
    exact ⟨fun h ↦ by simpa [h] using (WithZero.exp_log ((map_ne_zero V).2 x.ne_zero)).symm,
      fun h ↦ by simp [h]⟩
  have ho : IsOpen (d.ker : Set Kˣ) := hk ▸
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  have hc : IsCompact (d.ker : Set Kˣ) := hk ▸
    Submonoid.units_isCompact
      (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let : LocallyCompactSpace K := locallyCompactSpace_adicCompletion v
  let : LocallyCompactSpace Kˣ := Units.isOpenEmbedding_val.locallyCompactSpace
  obtain ⟨k, hkn⟩ :=
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_geomValuation d π hdπ ho hc _ hq
  exact ⟨π, k, norm_uniformizer_adicCompletion v _ hπ, by simpa using hkn⟩

/-- A flat archimedean test that does not vanish identically. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_arch
    (F : Type u) [Field F] [NumberField F] :
    ∃ (a : sLocalOrbitalArchimedeanFlatTests F) (x : InfiniteAdeleRing F),
      a.val (Multiplicative.ofAdd x) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_archimedeanFlatSchwartz_one {w : InfinitePlace F // w.IsReal}
    {w : InfinitePlace F // w.IsComplex}
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  refine ⟨⟨J φ.val, ?_⟩, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (1, 1), ?_⟩
  · unfold sLocalOrbitalArchimedeanFlatTests
    dsimp only
    refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨φ.val, φ.property, funext fun x ↦ ?_⟩)
    refine Eq.symm ((hJ φ.val _).trans (congrArg φ.val ?_))
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
    · have hw : w.1.IsReal := w.2
      simp only [hw, ↓reduceDIte]
      exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply _
    · have hw : ¬ w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
      simp only [hw, ↓reduceDIte]
      exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex _).apply_symm_apply _
  · have h1 := hJ φ.val ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (1, 1))
    rw [RingEquiv.apply_symm_apply, hφ] at h1
    exact fun h0 ↦ one_ne_zero (h1.symm.trans h0)

open Filter Topology in
/-- An S-adelic test is invariant under all small translations of a finite coordinate. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_slice
    {F : Type u} [Field F] [NumberField F] (S : Finset V(F)) (w : S)
    (f : ℬ(SAdeleRing F S)) :
    ∀ᶠ t : w.val.adicCompletion F in 𝓝 0, ∀ x : SAdeleRing F S,
      f (Multiplicative.ofAdd (((0, Pi.single w t) : SAdeleRing F S) + x)) =
        f (Multiplicative.ofAdd x) := by
  let addSingle := AddMonoidHom.single (fun u : S ↦ u.val.adicCompletion F) w
  let j : Multiplicative (w.val.adicCompletion F) →* Multiplicative (SAdeleRing F S) :=
    ((AddMonoidHom.inr (InfiniteAdeleRing F) _).comp addSingle).toMultiplicative
  have hj : Continuous j := by
    change Continuous (fun y : Multiplicative (w.val.adicCompletion F) ↦
      Multiplicative.ofAdd ((0, Pi.single w y.toAdd) : SAdeleRing F S))
    exact continuous_ofAdd.comp
      ((continuous_const.prodMk (continuous_single w)).comp continuous_toAdd)
  let (u : S) : ProperSpace (u.val.adicCompletion F) := properSpace_adicCompletion u.val
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) :=
    inferInstanceAs (LocallyCompactSpace
      (((a : InfinitePlace F) → a.Completion) × ((u : S) → u.val.adicCompletion F)))
  let : T2Space (Multiplicative (SAdeleRing F S)) :=
    inferInstanceAs (T2Space
      (((a : InfinitePlace F) → a.Completion) × ((u : S) → u.val.adicCompletion F)))
  have hper := Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_periodic j hj f
  filter_upwards [hper] with t ht x
  exact ht (Multiplicative.ofAdd x)

open Filter Topology in
/-- An S-adelic test cannot be a product whose factor at one finite place vanishes at the
origin and is nonzero along a sequence tending to the origin, when the other factors are
nonzero at a common point: it is invariant under small translations of that coordinate. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_product
    {F : Type u} [Field F] [NumberField F] (S T : Finset V(F)) (w : V(F)) (hwS : w ∈ S)
    (hwT : w ∉ T) (f : ℬ(SAdeleRing F S)) (c : InfiniteAdeleRing F → ℂ)
    (ψ : ∀ v : {v : S // v.val ∉ T}, v.val.val.adicCompletion F → ℂ)
    (γ : ∀ v : {v : S // v.val ∈ T}, v.val.val.adicCompletion F → ℂ)
    (hf : ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
      c x.1 * (∏ v : {v : S // v.val ∉ T}, ψ v (x.2 v.val)) *
        ∏ v : {v : S // v.val ∈ T}, γ v (x.2 v.val))
    (x₀ : InfiniteAdeleRing F) (hc : c x₀ ≠ 0) (ϖ : w.adicCompletion F) (hϖ : ‖ϖ‖ < 1)
    (hψ0 : ψ ⟨⟨w, hwS⟩, hwT⟩ 0 = 0) (hψϖ : ∀ n : ℕ, ψ ⟨⟨w, hwS⟩, hwT⟩ (ϖ ^ n) ≠ 0)
    (hψ1 : ∀ v : {v : S // v.val ∉ T}, v.val ≠ ⟨w, hwS⟩ → ψ v 1 ≠ 0)
    (hγ : ∀ v : {v : S // v.val ∈ T}, γ v 0 ≠ 0) : False := by
  let y (t : w.adicCompletion F) : ∀ v : S, v.val.adicCompletion F :=
    Function.update (fun v : S ↦ if v.val ∈ T then 0 else 1) ⟨w, hwS⟩ t
  have hyw (t : w.adicCompletion F) : y t ⟨w, hwS⟩ = t := Function.update_self ..
  have hyT (t : w.adicCompletion F) (v : {v : S // v.val ∈ T}) : y t v.val = 0 := by
    have hne : v.val ≠ ⟨w, hwS⟩ := fun h ↦ hwT (by
      have h2 := v.property
      rw [h] at h2
      exact h2)
    simp only [y, Function.update_of_ne hne, ite_eq_left v.property]
  have hyN (t : w.adicCompletion F) (v : {v : S // v.val ∉ T}) (hne : v.val ≠ ⟨w, hwS⟩) :
      y t v.val = 1 := by
    simp only [y, Function.update_of_ne hne, ite_eq_right v.property]
  have hzero : f (Multiplicative.ofAdd ((x₀, y 0) : SAdeleRing F S)) = 0 := by
    rw [hf]
    refine mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero
      (Finset.mem_univ (⟨⟨w, hwS⟩, hwT⟩ : {v : S // v.val ∉ T})) ?_)) _
    change ψ ⟨⟨w, hwS⟩, hwT⟩ (y 0 ⟨w, hwS⟩) = 0
    rw [hyw]
    exact hψ0
  have hnonzero (n : ℕ) : f (Multiplicative.ofAdd ((x₀, y (ϖ ^ n)) : SAdeleRing F S)) ≠ 0 := by
    rw [hf]
    refine mul_ne_zero (mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_))
      (Finset.prod_ne_zero_iff.mpr fun v _ ↦ ?_)
    · by_cases hv : v.val = ⟨w, hwS⟩
      · obtain ⟨v, hvT⟩ := v
        subst hv
        change ψ ⟨⟨w, hwS⟩, hwT⟩ (y (ϖ ^ n) ⟨w, hwS⟩) ≠ 0
        rw [hyw]
        exact hψϖ n
      · change ψ v (y (ϖ ^ n) v.val) ≠ 0
        rw [hyN _ v hv]
        exact hψ1 v hv
    · change γ v (y (ϖ ^ n) v.val) ≠ 0
      rw [hyT]
      exact hγ v
  have hper := Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_slice S ⟨w, hwS⟩ f
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ).eventually hper).exists
  have hsum : (((0, Pi.single ⟨w, hwS⟩ (ϖ ^ n)) : SAdeleRing F S) + (x₀, y 0)) =
      (x₀, y (ϖ ^ n)) := by
    refine Prod.ext (zero_add _) (funext fun v ↦ ?_)
    by_cases hv : v = ⟨w, hwS⟩
    · subst hv
      change (Pi.single ⟨w, hwS⟩ (ϖ ^ n) : ∀ u : S, u.val.adicCompletion F) ⟨w, hwS⟩ +
        y 0 ⟨w, hwS⟩ = y (ϖ ^ n) ⟨w, hwS⟩
      rw [Pi.single_eq_same, hyw, hyw, add_zero]
    · change (Pi.single ⟨w, hwS⟩ (ϖ ^ n) : ∀ u : S, u.val.adicCompletion F) v + y 0 v =
        y (ϖ ^ n) v
      simp only [y, Pi.single_eq_of_ne hv, Function.update_of_ne hv, zero_add]
  have hpow := hn ((x₀, y 0) : SAdeleRing F S)
  rw [hsum, hzero] at hpow
  exact hnonzero n hpow

/-- The displayed tensor inclusion fails as soon as one selected finite place carries a full
multiplicative factor: a geometric shell test there has a zero extension that is not locally
constant at the origin, while every S-adelic test is. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_core
    {F : Type u} [Field F] [NumberField F] (S T : Finset V(F)) (w : V(F)) (hwS : w ∈ S)
    (hwT : w ∉ T) (claim : Submodule ℂ ℬ(SAdeleRing F S) → Prop) :
    ¬ Printed.orbitalSupportTensorImage S T claim := by
  rintro ⟨U, -, ⟨e, he⟩, -⟩
  obtain ⟨a, x₀, hax⟩ := Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_arch F
  choose π k hπ hk using fun v : V(F) ↦
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_shellTest v
  have hg0 (v : V(F)) : finiteStandardGaussian v 1 (Multiplicative.ofAdd 0) = 1 := by
    change finiteStandardGaussianValue v 1 0 = 1
    unfold finiteStandardGaussianValue
    split_ifs with h
    · exact Set.indicator_of_mem (zero_mem (v.adicCompletionIntegers F)) _
    · exact absurd (fun u _ ↦ rfl) h
  have hk1 (v : V(F)) : k v 1 = 1 := by simpa using hk v 0
  have hext (v : V(F)) (u : (v.adicCompletion F)ˣ) :
      zeroExtension(k v) u.val = k v u := Units.val_injective.extend_apply _ _ u
  have hext0 (v : V(F)) : zeroExtension(k v) (0 : v.adicCompletion F) = 0 :=
    Function.extend_apply' _ _ _ fun ⟨u, hu⟩ ↦ u.ne_zero hu
  have hq : (w.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm w)).ne'
  have hπsmall : ‖(π w).val‖ < 1 := by
    rw [hπ]
    exact inv_lt_one_of_one_lt₀ (by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w)
  have hf := he a (fun v ↦ k v.val.val) (fun v ↦ finiteStandardGaussian v.val.val 1)
  refine Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_product S T w hwS hwT _
    (fun x ↦ a.val (Multiplicative.ofAdd x)) (fun v t ↦ zeroExtension(k v.val.val) t)
    (fun v t ↦ finiteStandardGaussian v.val.val 1 (Multiplicative.ofAdd t)) hf x₀ hax
    (π w).val hπsmall (hext0 w) (fun n ↦ ?_) (fun v _ ↦ ?_) (fun v ↦ ?_)
  · change zeroExtension(k w) ((π w).val ^ n) ≠ 0
    rw [← Units.val_pow_eq_pow_val, hext, hk]
    exact pow_ne_zero n (inv_ne_zero hq)
  · change zeroExtension(k v.val.val) (1 : v.val.val.adicCompletion F) ≠ 0
    rw [← Units.val_one, hext, hk1]
    exact one_ne_zero
  · rw [hg0]
    exact one_ne_zero

/-- Over any number field there are a finite set of finite places with trivial Picard group,
a rational prime whose whole fibre it contains, and two of its members only one of which lies
over that prime. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_data
    (F : Type u) [Field F] [NumberField F] :
    ∃ (S : Finset V(F)) (p : Vℚ) (v w : V(F)), v ∈ S ∧ w ∈ S ∧ w ≠ v ∧
      w.under (𝓞 ℚ) ≠ p ∧ fullFibre(S, p) ∧ PicTrivial(F, S) := by
  have hi : Infinite Vℚ := Rat.HeightOneSpectrum.primesEquiv.infinite_iff.mpr inferInstance
  obtain ⟨p⟩ := (inferInstance : Nonempty Vℚ)
  obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset ({p} : Finset Vℚ)
  have hqp : q ≠ p := fun h ↦ hq (Finset.mem_singleton.mpr h)
  have hover (r : Vℚ) : ∃ u : V(F), u.under (𝓞 ℚ) = r := by
    have := r.isPrime
    obtain ⟨⟨Q, hQ⟩⟩ := r.asIdeal.nonempty_primesOver (S := 𝓞 F)
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver r.ne_bot hQ⟩,
      HeightOneSpectrum.ext hQ.2.over.symm⟩
  obtain ⟨v, hv⟩ := hover p
  obtain ⟨w, hw⟩ := hover q
  have hfin : {u : V(F) | u.under (𝓞 ℚ) = p}.Finite := by
    apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
      (hi := HeightOneSpectrum.asIdeal_injective.injOn)
    apply (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)).subset
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u.isPrime,
      ⟨congrArg HeightOneSpectrum.asIdeal (show u.under (𝓞 ℚ) = p from hu).symm⟩⟩
  obtain ⟨S, hS, hPic⟩ := (picard_uniformization F (insert w hfin.toFinset)).1
  refine ⟨S, p, v, w, hS (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hv)),
    hS (Finset.mem_insert_self _ _), fun h ↦ hqp ?_, fun h ↦ hqp (hw.symm.trans h),
    fun u hu h ↦ hu (hS (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr h))), hPic⟩
  rw [← hw, h, hv]

/-- The trivial idele class character is unramified outside every finite set of places. -/
private theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_unramified
    (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) :
    NormOneCharacterUnramifiedOutside (res(F, 1)) S :=
  ⟨⟨1, (mem_unramifiedOutside_iff F S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.2), p. 382.
Use ℚ with S = {∞, 2, 3}, p = 2 and the trivial character. Use a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the multiplicative 3-adic
test h(3ᵏu) = exp(−k²) for k ∈ ℤ and u ∈ ℤ₃ˣ. At a point where the real test is
nonzero and the 2-adic coordinate is 1, the zero extension of the product fails
local constancy at the 3-adic origin. See ERRATA R11. -/
theorem Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportTests_inclusion.{u} := by
  intro H
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨S, p, v, w, -, hw, -, hwp, hfull, hPic⟩ :=
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_data (ULift.{u} ℚ)
  exact Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_core S (sLocalPrimaryPlaces S p)
    w hw (fun h ↦ hwp ((mem_sLocalPrimaryPlaces p w).mp h).2) _
    (H (ULift.{u} ℚ) S p hfull hPic 1
      (Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_unramified (ULift.{u} ℚ) S))

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
The printed tensor product with full multiplicative factors away from v embeds
as a closed subspace of the additive tests with its projective tensor topology. -/
def Printed.sLocalPlaceOrbitalSupportTests_inclusion : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)), NormOneCharacterUnramifiedOutside (res(F, χ)) S →
      Printed.orbitalSupportTensorImage S {v.val} (fun _ ↦ True)

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.4), p. 382.
Use ℚ with S = {∞, 2, 3}, v = 2 and the trivial character. Take a nonzero smooth
real test supported in (1, 2), the indicator of ℤ₂, and the unit-invariant
3-adic test with profile k ↦ exp(−k²). The 3-adic slice is nonzero on 3ᵏ for
every k, but zero at the origin, so it fails local constancy there. -/
theorem Printed.sLocalPlaceOrbitalSupportTests_inclusion_false :
    ¬ Printed.sLocalPlaceOrbitalSupportTests_inclusion.{u} := by
  intro H
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨S, p, v, w, hv, hw, hwv, -, -, hPic⟩ :=
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_data (ULift.{u} ℚ)
  exact Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_core S {v}
    w hw (fun h ↦ hwv (Finset.mem_singleton.mp h)) _
    (H (ULift.{u} ℚ) S ⟨v, hv⟩ hPic 1
      (Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_unramified (ULift.{u} ℚ) S))

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
The printed tensor product is a closed subspace and its canonical primary
comparison is a continuous linear equivalence.
Deviation: The source denominator uses the same restricted numerator, as on p. 384. -/
def Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (p : Vℚ),
    fullFibre(S, p) → PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)) (hω : NormOneCharacterUnramifiedOutside (res(F, χ)) S),
      let T := sLocalPrimaryPlaces S p
      let hT := sLocalPrimaryPlaces_subset S p
      let η := sLocalNormOneCharacter S (res(F, χ)) hω
      Printed.orbitalSupportTensorImage S T (Printed.orbitalSupportQuotientEquiv hT η)

/-- Paper: Theorem 8.1.0.1(1), Equation (8.1.0.1), p. 382.
For ℚ with S = {∞, 2}, p = 2 and the trivial character, the zeta transform
of the real Gaussian times 1_{ℤ₂} has a double pole at zero. Restricted tests
have at most a simple pole there, and PV₂ lowers the pole order by one.
Thus this Gaussian class lies outside the comparison's range. -/
theorem Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPrimaryOrbitalSupportComparison_isomorphism.{u} := by
  intro H
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨S, p, v, w, -, hw, -, hwp, hfull, hPic⟩ :=
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_data (ULift.{u} ℚ)
  exact Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_core S (sLocalPrimaryPlaces S p)
    w hw (fun h ↦ hwp ((mem_sLocalPrimaryPlaces p w).mp h).2) _
    (H (ULift.{u} ℚ) S p hfull hPic 1
      (Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_unramified (ULift.{u} ℚ) S))

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
The printed tensor product is a closed subspace and its canonical single-place
comparison is a continuous linear equivalence.
Deviation: The source denominator uses the same restricted numerator, as on p. 384. -/
def Printed.sLocalPlaceOrbitalSupportComparison_isomorphism : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset V(F)) (v : S),
    PicTrivial(F, S) →
    ∀ (χ : PontryaginDual C(F)) (hω : NormOneCharacterUnramifiedOutside (res(F, χ)) S),
      let T : Finset V(F) := {v.val}
      let hT : T ⊆ S := Finset.singleton_subset_iff.mpr v.property
      let η := sLocalNormOneCharacter S (res(F, χ)) hω
      Printed.orbitalSupportTensorImage S T (Printed.orbitalSupportQuotientEquiv hT η)

/-- Paper: Theorem 8.1.0.1(2), Equation (8.1.0.3), p. 382.
For ℚ with S = {∞, 2}, v = 2 and the trivial character, the real Gaussian
times 1_{ℤ₂} gives the same double-pole obstruction as in part (1). -/
theorem Printed.sLocalPlaceOrbitalSupportComparison_isomorphism_false :
    ¬ Printed.sLocalPlaceOrbitalSupportComparison_isomorphism.{u} := by
  intro H
  have : CharZero (ULift.{u} ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift.{u} ℚ) := ⟨⟩
  obtain ⟨S, p, v, w, hv, hw, hwv, -, -, hPic⟩ :=
    Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_data (ULift.{u} ℚ)
  exact Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_core S {v}
    w hw (fun h ↦ hwv (Finset.mem_singleton.mp h)) _
    (H (ULift.{u} ℚ) S ⟨v, hv⟩ hPic 1
      (Printed.sLocalPrimaryOrbitalSupportTests_inclusion_false_unramified (ULift.{u} ℚ) S))

open MeasureTheory in
/-- The local principal value of a test vanishes at zero. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_localPV
    {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : SchwartzBruhat (Multiplicative (v.adicCompletion F))) :
    finitePlacePrincipalValue v g (Multiplicative.ofAdd 0) = 0 := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π' := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  rw [finitePlacePrincipalValue_spec v π' hπ g]
  have hm := (finitePlacePrincipalValue_integrable v π' g (Multiplicative.ofAdd 0)).1
  unfold finitePlacePrincipalValueFun
  simp only [toAdd_ofAdd, mul_zero]
  rw [setIntegral_const, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), one_mul, sub_self]

/-- The S-local principal value vanishes at every point whose coordinate at a selected
place is zero. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_sPV
    {F : Type*} [Field F] [NumberField F]
    {S S₀ : Finset (HeightOneSpectrum (𝓞 F))} (h₀ : S₀ ⊆ S) {p : HeightOneSpectrum (𝓞 F)}
    (hp : p ∈ S₀) (x : SAdeleRing F S) (hx : x.2 ⟨p, h₀ hp⟩ = 0)
    (h : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
    sAdelePrincipalValue F h₀ h (Multiplicative.ofAdd x) = 0 := by
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have he := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec
  let A := SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
  let P := ⨂[ℂ] w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))
  let evL : SchwartzBruhat (Multiplicative (SAdeleRing F S)) →ₗ[ℂ] ℂ :=
    { toFun := fun k ↦ k (Multiplicative.ofAdd x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let Φ : A ⊗[ℂ] FinestLocallyConvex P →ₗ[ℂ] ℂ :=
    (evL.comp (sAdelePrincipalValue F h₀)).comp e.toLinearMap
  have hpure (a : A) (g : ∀ w : S, SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
      Φ (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) = 0 := by
    change sAdelePrincipalValue F h₀ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) (Multiplicative.ofAdd x) = 0
    rw [sAdelePrincipalValue_tmul h₀ a g, he]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨p, h₀ hp⟩) ?_)
    simp only [hp, ite_true, hx]
    exact sLocalOrbitalSupportComparison_rat_two_fails_localPV p (g ⟨p, h₀ hp⟩)
  have hΦ (t : A ⊗[ℂ] FinestLocallyConvex P) : Φ t = 0 := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul a w =>
      let Ψ : P →ₗ[ℂ] ℂ := Φ.comp (TensorProduct.mk ℂ A (FinestLocallyConvex P) a)
      change Ψ w = 0
      induction w using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        rw [map_smul, smul_eq_mul]
        exact mul_eq_zero_of_right _ (hpure a g)
      | add x y hx hy => rw [map_add, hx, hy, add_zero]
  have := hΦ (e.symm h)
  change sAdelePrincipalValue F h₀ (e (e.symm h)) (Multiplicative.ofAdd x) = 0 at this
  rwa [e.apply_symm_apply] at this

open MeasureTheory Filter Topology in
open scoped NNReal in
/-- A test in the kernel of global homogeneous theta for the trivial character vanishes at
zero: after the polar term the homogeneous theta function is small at small norm. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_globalHom
    {F : Type*} [Field F] [NumberField F]
    (f : SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F)))
    (hf : homogeneousAdelicTheta (1 : PontryaginDual (ideleClassNorm F).ker) f = 0) :
    f (Multiplicative.ofAdd 0) = 0 := by
  let : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
  let : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  obtain ⟨C, T, hC, hT, hsmall⟩ :=
    homogeneousAdelicTheta_decay_small (1 : PontryaginDual (ideleClassNorm F).ker) f 1
  set V := (normOneIdeleClassTamagawaMeasure F univ).toReal
  have hV : 0 < V := ENNReal.toReal_pos (isOpen_univ.measure_ne_zero _ univ_nonempty)
    isCompact_univ.measure_lt_top.ne
  set a := adeleSchwartzFourier f (Multiplicative.ofAdd 0)
  set b := f (Multiplicative.ofAdd 0)
  -- Every positive real below `T` is the norm of an idele class.
  have key (t : ℝ) (ht : 0 < t) (htT : t < T) : ‖V • (t⁻¹ • a - b)‖ ≤ C * t := by
    let u : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ fun h0 ↦ ht.ne' (congrArg Subtype.val h0)
    let g : IdeleClassGroup (𝓞 F) F := QuotientGroup.mk (canonicalIdeleNormSection F u)
    have hg : ((ideleClassNorm F g : ℝ≥0) : ℝ) = t := by
      change ((ideleNorm F (canonicalIdeleNormSection F u) : ℝ≥0) : ℝ) = t
      rw [canonicalIdeleNormSection_rightInverse F u]
      rfl
    have h := hsmall g (by beta_reduce; rw [hg]; exact htT)
    beta_reduce at h
    simp only [homogeneousAdelicTheta_polarTerm, ite_true] at h
    rw [hf, hg, pow_one] at h
    rw [norm_smul, Real.norm_of_nonneg hV.le]
    simpa [V, a, b] using h
  have hlim0 : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Multiplying by `t` shows that the Fourier value vanishes.
  have ha : a = 0 := by
    have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖a‖ ≤ t * ‖b‖ + C * t ^ 2 / V := by
      filter_upwards [Ioo_mem_nhdsGT hT] with t ht
      have h := key t ht.1 ht.2
      have he : a = (t / V) • (V • (t⁻¹ • a - b)) + t • b := by
        rw [smul_smul, div_mul_cancel₀ _ hV.ne', smul_sub, smul_smul,
          mul_inv_cancel₀ ht.1.ne', one_smul, sub_add_cancel]
      rw [he]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul (t / V), norm_smul t, Real.norm_of_nonneg (div_nonneg ht.1.le hV.le),
        Real.norm_of_nonneg ht.1.le]
      have h2 : t / V * ‖V • (t⁻¹ • a - b)‖ ≤ t / V * (C * t) :=
        mul_le_mul_of_nonneg_left h (div_nonneg ht.1.le hV.le)
      have h3 : t / V * (C * t) = C * t ^ 2 / V := by ring
      linarith
    have hl : Tendsto (fun t : ℝ ↦ t * ‖b‖ + C * t ^ 2 / V) (𝓝[>] 0) (𝓝 0) := by
      have := ((hlim0.mul_const ‖b‖).add ((hlim0.pow 2).const_mul C |>.div_const V))
      simpa using this
    exact norm_le_zero_iff.mp (ge_of_tendsto hl hb)
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖b‖ ≤ C * t / V := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    have h := key t ht.1 ht.2
    rw [ha, smul_zero, zero_sub, smul_neg, norm_neg, norm_smul, Real.norm_of_nonneg hV.le] at h
    rw [le_div_iff₀ hV]
    linarith
  have hl : Tendsto (fun t : ℝ ↦ C * t / V) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hlim0.const_mul C).div_const V
  exact norm_le_zero_iff.mp (ge_of_tendsto hl hb)

/-- Evaluation at zero descends to the homogeneous theta space at a stage `T` for an
unramified norm-one character, through the insertion into the global homogeneous space. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_evalZero
    {F : Type*} [Field F] [NumberField F]
    {T : Finset (V(F))} (hω : NormOneCharacterUnramifiedOutside
      (1 : PontryaginDual (ideleClassNorm F).ker) T)
    (f : ℬ(SAdeleRing F T))
    (hf : f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T
      (sLocalNormOneCharacter T 1 hω))) :
    f (Multiplicative.ofAdd 0) = 0 := by
  have hg := sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (S := T) hω hf
  rw [Submodule.mem_comap, LinearMap.mem_ker] at hg
  have h0 := sLocalOrbitalSupportComparison_rat_two_fails_globalHom _ hg
  rw [sAdeleSchwartzToGlobal_apply, ite_eq_left (fun w _ ↦ (w.adicCompletionIntegers F).zero_mem),
    map_zero] at h0
  exact h0

/-- Over ℚ the S-local norm-one character of the trivial character is trivial. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_oneLocal (S : Finset Vℚ)
    (hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S) :
    sLocalNormOneCharacter S 1 hu = 1 := by
  ext y
  have h := sLocalNormOneCharacter_eq_sIdeleRestriction (F := ℚ) (S := S) 1
    ⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩ (fun _ ↦ rfl) y
  rw [h]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
  rw [← hg, sIdeleRestriction_mk]
  rfl

/-- Every restricted test vanishes at the origin, because its archimedean factor is flat. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_testsZero
    {F : Type u} [Field F] [NumberField F] (S T : Finset V(F))
    (g : ℬ(SAdeleRing F S)) (hg : g ∈ sLocalOrbitalSupportTests S T) :
    g (Multiplicative.ofAdd 0) = 0 := by
  unfold sLocalOrbitalSupportTests at hg
  dsimp only at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, -, rfl⟩ := hg
    rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec]
    exact mul_eq_zero_of_left (sLocalOrbitalArchimedeanFlatTests_zero a) _
  | zero => rfl
  | add f g _ _ hf hg => rw [SchwartzBruhat.coe_add, Pi.add_apply, hf, hg, add_zero]
  | smul c f _ hf => rw [SchwartzBruhat.coe_smul, Pi.smul_apply, hf, smul_zero]

open Filter Topology in
/-- An S-adelic test with value one at the origin. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_valueOne
    {F : Type u} [Field F] [NumberField F] (S : Finset V(F)) :
    ∃ f : ℬ(SAdeleRing F S), f (Multiplicative.ofAdd 0) = 1 := by
  obtain ⟨b, -, hbc, hbd, -, hb⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (show (Set.univ : Set (mixedEmbedding.mixedSpace F)) ∈ 𝓝 0 from univ_mem)
  let b₀ : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ :=
    (hbc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hbd)
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := F)
  have hG (v : V(F)) : finiteStandardGaussian v 1 (Multiplicative.ofAdd 0) = 1 := by
    change finiteStandardGaussianValue v 1 0 = 1
    unfold finiteStandardGaussianValue
    split_ifs with h
    · exact Set.indicator_of_mem (zero_mem (v.adicCompletionIntegers F)) _
    · exact absurd (fun u _ ↦ rfl) h
  have hprod : (∏ w : S, finiteStandardGaussian w.val 1
      (Multiplicative.ofAdd ((0 : SAdeleRing F S).2 w))) = 1 :=
    Finset.prod_eq_one fun w _ ↦ hG w.val
  have hJ0 : J b₀ (Multiplicative.ofAdd (0 : SAdeleRing F S).1) = 1 := by
    refine (hJ b₀ 0).trans ?_
    rw [map_zero]
    change (b 0 : ℂ) = 1
    exact_mod_cast hb
  refine ⟨(sAdeleSchwartz_inductiveTensor_equiv F S).choose
    (J b₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, finiteStandardGaussian w.val 1)), ?_⟩
  rw [(sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec, hprod, hJ0, mul_one]

/-- The repaired comparison over ℚ with a nonempty set of selected primes, all of them
taken for the principal value, is not surjective. Evaluation at the origin vanishes on the
theta kernel of the trivial character, on the restricted tests and on principal values, so
the class of a test that is nonzero at the origin is missed. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_not_surjective
    (S : Finset Vℚ) (p : Vℚ) (hp : p ∈ S) :
    ¬ Function.Surjective
      (sLocalOrbitalSupportComparison (F := ℚ) (Finset.Subset.refl S) 1) := by
  intro hsurj
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have h1 := sLocalOrbitalSupportComparison_rat_two_fails_oneLocal S hu
  have hker (f : ℬ(SAdeleRing ℚ S))
      (hf : f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)) :
      f (Multiplicative.ofAdd 0) = 0 :=
    sLocalOrbitalSupportComparison_rat_two_fails_evalZero hu f (h1 ▸ hf)
  obtain ⟨f₀, hf₀⟩ := sLocalOrbitalSupportComparison_rat_two_fails_valueOne S
  obtain ⟨y, hy⟩ := hsurj (Submodule.Quotient.mk (Submodule.Quotient.mk f₀))
  obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp hy
  obtain ⟨h, rfl⟩ := Submodule.mkQ_surjective _ z
  have hmem := (Submodule.Quotient.eq _).mp hz
  have hP : sAdelePrincipalValue ℚ (Finset.Subset.refl S) h (Multiplicative.ofAdd 0) = 0 :=
    sLocalOrbitalSupportComparison_rat_two_fails_sPV (Finset.Subset.refl S) hp 0 rfl h
  have hg0 : g.val (Multiplicative.ofAdd 0) = 0 :=
    sLocalOrbitalSupportComparison_rat_two_fails_testsZero S S g.val g.property
  have h0 : sAdelePrincipalValue ℚ (Finset.Subset.refl S) h (Multiplicative.ofAdd 0) -
      (g.val (Multiplicative.ofAdd 0) - f₀ (Multiplicative.ofAdd 0)) = 0 := hker _ hmem
  rw [hP, hg0, hf₀] at h0
  norm_num at h0

/-- On the trivial norm-one component every quasi-character is a bare norm power. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_onNormChart
    {S : Finset Vℚ} (c : QuasiCharacter (SIdeleQuotient ℚ S))
    (hc : ∀ k : J₁(ℚ, S), c k.val = 1) :
    ∃ z, (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
      (isProperMap_sIdeleQuotientNorm ℚ S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient ℚ S))) z) = c := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ S
  obtain ⟨z, hz⟩ := (existsUnique_complexPower (c.comp τ)).exists
  refine ⟨z, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have h := hc ⟨g / τ (sIdeleQuotientNorm ℚ S g),
    MonoidHom.mem_ker.mpr (by rw [map_div, hτ, div_self'])⟩
  change c (g / τ (sIdeleQuotientNorm ℚ S g)) = 1 at h
  rw [map_div, div_eq_one_iff_eq ((Group.isUnit _).map c).ne_zero] at h
  exact (one_mul _).trans ((hz _).symm.trans h.symm)

/-- On a bare norm chart the singleton Euler factor is the reciprocal of the
translation-difference multiplier. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_singleEuler
    {S : Finset Vℚ} (v : S) (z : ℂ) (hz : 0 < z.re) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v
      ((quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
        (isProperMap_sIdeleQuotientNorm ℚ S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient ℚ S))) z))) =
      (1 - (v.val.asIdeal.absNorm : ℂ) ^ (-z))⁻¹ := by
  refine Eq.trans ?_ (finiteLocalEulerFactor_norm v.val hz)
  congr 1
  ext u
  obtain ⟨y, hy⟩ : ∃ y : SIdeleQuotient ℚ S, ∀ c, sLocalFiniteRestriction v c u = c y :=
    ⟨_, fun _ ↦ rfl⟩
  have h := sLocalFiniteRestriction_norm v u
  rw [hy] at h ⊢
  change (1 : ℂ) * _ ^ (1 : ℂ) = _ at h
  rw [one_mul, Complex.cpow_one] at h
  change (1 : ℂ) * _ ^ z = (1 : ℂ) * _ ^ z
  rw [h]

open Filter Topology in
/-- The Euler multiplier identifies PV on the trivial singleton-stage quotient
with the identity minus translation by any idele of norm 1/N(p). -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_singlePV
    {p : Vℚ} {T : Finset Vℚ} (hT : T = {p}) (u : (SAdeleRing ℚ T)ˣ)
    (hu : ((sIdeleNorm ℚ T u).val : ℝ) = (p.asIdeal.absNorm : ℝ)⁻¹)
    (f : ℬ(SAdeleRing ℚ T)) :
    (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ T 1)).mkQ
        (sAdelePrincipalValue ℚ (Finset.Subset.refl T) f) =
      (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ T 1)).mkQ
        (f - schwartzBruhatUnitTranslate u f) := by
  let P := sAdelePrincipalValue ℚ (Finset.Subset.refl T)
  let k := P f - (f - schwartzBruhatUnitTranslate u f)
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (1 : PontryaginDual J₁(ℚ, T)) k).mpr
  intro c hc
  obtain ⟨s, hs⟩ := sLocalOrbitalSupportComparison_rat_two_fails_onNormChart c.val (fun h ↦ hc h)
  change sLocalIdelicZFunction k c.val = 0
  rw [← hs]
  let Z := fun z : ℂ ↦ sLocalIdelicZFunction k
    ((quasiCharacterNormTwist (sIdeleQuotientNorm ℚ T)
      (isProperMap_sIdeleQuotientNorm ℚ T).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient ℚ T))) z))
  have heq : Z = 0 := by
    apply eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic k 1)
      (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0
    intro z hz
    have hn : ∀ᶠ w : ℂ in 𝓝[≠] z, 0 < w.re := nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hzero : Z =ᶠ[𝓝[≠] z] 0 := by
      filter_upwards [hn, nhdsNE_le_codiscrete z (sLocalIdelicZFunction_principalValue T
        (Finset.Subset.refl T) f 1)] with w hw hP
      let c₀ := (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ T)
        (isProperMap_sIdeleQuotientNorm ℚ T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient ℚ T))) w)
      let d := (⟨c₀, sLocalOrderBound_positive (F := ℚ) (S := T) 1 hw⟩ :
        {c : QuasiCharacter (SIdeleQuotient ℚ T) // 0 ≤ sLocalIdelicOrderBound c})
      let A := sLocalIdelicMellin (F := ℚ) (S := T)
      have htr := sLocalIdelicMellin_unitTranslate u f d
      have hev : c₀ (QuotientGroup.mk u) = (p.asIdeal.absNorm : ℂ) ^ (-w) := by
        change (1 : ℂ) * (((sIdeleNorm ℚ T u).val : ℝ) : ℂ) ^ w = _
        rw [one_mul, hu, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm),
          ← Complex.cpow_neg, Complex.ofReal_natCast]
      have hprod : (∏ v : T, if v.val ∈ T then
          finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c₀)
          else 1) = (1 - (p.asIdeal.absNorm : ℂ) ^ (-w))⁻¹ := by
        have : Subsingleton T := hT ▸ inferInstanceAs (Subsingleton (↥({p} : Finset Vℚ)))
        let v : T := ⟨p, hT ▸ Finset.mem_singleton_self _⟩
        rw [Finset.prod_eq_single v (fun b _ hb ↦ (hb (Subsingleton.elim _ _)).elim)
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left v.property]
        exact sLocalOrbitalSupportComparison_rat_two_fails_singleEuler v w hw
      change (A (P f)).val d = (A f).val d / _ at hP
      rw [hprod, div_inv_eq_mul] at hP
      change (A (schwartzBruhatUnitTranslate u f)).val d =
        c₀ (QuotientGroup.mk u) * (A f).val d at htr
      rw [hev] at htr
      change (A (P f - (f - schwartzBruhatUnitTranslate u f))).val d = 0
      rw [map_sub, map_sub]
      change (A (P f)).val d - ((A f).val d - (A (schwartzBruhatUnitTranslate u f)).val d) = 0
      rw [hP, htr]
      ring
    exact (((sLocalIdelicZFunction_meromorphic k 1
      (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        analyticAt_const.meromorphicNFAt).mp hzero).eq_of_nhds
  exact congrFun heq s

/-- A test on the archimedean factor whose mixed-coordinate form is flat along the coordinate
hyperplanes is a flat archimedean test. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_flatMem
    {F : Type u} [Field F] [NumberField F] (a : ℬ(InfiniteAdeleRing F))
    (ψ : SchwartzMap (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ψ ∈ archimedeanFlatSchwartz (ι := {w : InfinitePlace F // w.IsReal})
      (κ := {w : InfinitePlace F // w.IsComplex}))
    (key : ∀ y : InfiniteAdeleRing F,
      a (Multiplicative.ofAdd y) = ψ (InfiniteAdeleRing.ringEquiv_mixedSpace F y)) :
    a ∈ sLocalOrbitalArchimedeanFlatTests F := by
  unfold sLocalOrbitalArchimedeanFlatTests
  dsimp only
  refine Submodule.mem_comap.mpr (Submodule.mem_map.mpr ⟨ψ, hψ, funext fun x ↦ ?_⟩)
  refine Eq.symm ((key _).trans (congrArg ψ ?_))
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
  · have hw : w.1.IsReal := w.2
    simp only [hw, ↓reduceDIte]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply _
  · have hw : ¬ w.1.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr w.2
    simp only [hw, ↓reduceDIte]
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex _).apply_symm_apply _

open Filter Topology in
/-- Over ℚ the difference of a bump that is one near the origin and any of its dilates is a
flat archimedean test: it vanishes near the origin, the only point of the coordinate
hyperplanes. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_bumpDiff
    (J : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ ≃L[ℂ] ℬ(InfiniteAdeleRing ℚ))
    (hJ : ∀ (f : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ) (x : InfiniteAdeleRing ℚ),
      J f (Multiplicative.ofAdd x) = f (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x))
    (b₀ : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ)
    (hb₀ : ∀ᶠ z in 𝓝 (0 : mixedEmbedding.mixedSpace ℚ), b₀ z = 1)
    (r : (InfiniteAdeleRing ℚ)ˣ) :
    J b₀ - schwartzBruhatUnitTranslate r (J b₀) ∈ sLocalOrbitalArchimedeanFlatTests ℚ := by
  have hc (v : {v : InfinitePlace ℚ // v.IsComplex}) : False :=
    InfinitePlace.not_isComplex_iff_isReal.mpr
      ((Subsingleton.elim v.val Rat.infinitePlace) ▸ Rat.isReal_infinitePlace) v.property
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace ℚ
  let d : ℬ(InfiniteAdeleRing ℚ) := J b₀ - schwartzBruhatUnitTranslate r (J b₀)
  let ψ : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ := J.symm d
  have key (y : InfiniteAdeleRing ℚ) : d (Multiplicative.ofAdd y) = ψ (E y) :=
    (congrArg (fun f : ℬ(InfiniteAdeleRing ℚ) ↦ f (Multiplicative.ofAdd y))
      (J.apply_symm_apply d)).symm.trans (hJ ψ y)
  have hsub (y : InfiniteAdeleRing ℚ) : d (Multiplicative.ofAdd y) =
      J b₀ (Multiplicative.ofAdd y) -
        J b₀ (Multiplicative.ofAdd ((↑r⁻¹ : InfiniteAdeleRing ℚ) * y)) := rfl
  let c : mixedEmbedding.mixedSpace ℚ := E (↑r⁻¹ : InfiniteAdeleRing ℚ)
  have hψ (z : mixedEmbedding.mixedSpace ℚ) : ψ z = b₀ z - b₀ (c * z) := by
    have hz : E (E.symm z) = z := E.apply_symm_apply z
    have h1 : ψ z = d (Multiplicative.ofAdd (E.symm z)) :=
      ((key (E.symm z)).trans (congrArg ψ hz)).symm
    have hA : J b₀ (Multiplicative.ofAdd (E.symm z)) = b₀ z :=
      (hJ b₀ (E.symm z)).trans (congrArg b₀ hz)
    have hB : J b₀ (Multiplicative.ofAdd ((↑r⁻¹ : InfiniteAdeleRing ℚ) * E.symm z)) =
        b₀ (c * z) :=
      (hJ b₀ _).trans (congrArg b₀ ((map_mul E _ _).trans (congrArg (fun y ↦ c * y) hz)))
    exact h1.trans ((hsub _).trans (congrArg₂ (fun s t : ℂ ↦ s - t) hA hB))
  refine sLocalOrbitalSupportComparison_rat_two_fails_flatMem d ψ ?_ key
  apply mem_archimedeanFlatSchwartz_of_tsupport
  rw [Set.disjoint_left]
  intro z hz hw
  have hz0 : z = 0 := by
    rcases hw with ⟨i, hi⟩ | ⟨j, -⟩
    · refine Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ (hc k).elim)
      have hk : k = i := Subtype.ext (Subsingleton.elim _ _)
      rw [hk]
      exact hi
    · exact (hc j).elim
  subst hz0
  refine notMem_tsupport_iff_eventuallyEq.mpr ?_ hz
  have hcont : Tendsto (fun z : mixedEmbedding.mixedSpace ℚ ↦ c * z) (𝓝 0) (𝓝 0) := by
    have hm : Continuous fun z : mixedEmbedding.mixedSpace ℚ ↦ c * z :=
      continuous_const.mul continuous_id
    have h := hm.tendsto 0
    rwa [mul_zero] at h
  filter_upwards [hb₀, hcont.eventually hb₀] with z hz1 hz2
  rw [hψ, hz1, hz2, sub_self]
  rfl

/-- Translating a product test by an S-idele with trivial finite coordinates only translates
its archimedean factor, so the difference with the translate is again a product test. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_translateDiff
    (S : Finset Vℚ) (u : (SAdeleRing ℚ S)ˣ) (hu : ∀ v : S, (u⁻¹).val.2 v = 1)
    (a a₂ d : ℬ(InfiniteAdeleRing ℚ)) (G : ∀ w : S, ℬ(w.val.adicCompletion ℚ))
    (H D : ℬ(SAdeleRing ℚ S))
    (ha₂ : ∀ x : SAdeleRing ℚ S, a₂ (Multiplicative.ofAdd x.1) =
      a (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing ℚ S) * x).1))
    (hd : ∀ y : InfiniteAdeleRing ℚ, d (Multiplicative.ofAdd y) =
      a (Multiplicative.ofAdd y) - a₂ (Multiplicative.ofAdd y))
    (hH : ∀ x : SAdeleRing ℚ S, H (Multiplicative.ofAdd x) =
      a (Multiplicative.ofAdd x.1) * ∏ w : S, G w (Multiplicative.ofAdd (x.2 w)))
    (hD : ∀ x : SAdeleRing ℚ S, D (Multiplicative.ofAdd x) =
      d (Multiplicative.ofAdd x.1) * ∏ w : S, G w (Multiplicative.ofAdd (x.2 w))) :
    H - schwartzBruhatUnitTranslate u H = D := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  have hfin (w : S) : ((↑u⁻¹ : SAdeleRing ℚ S) * x.toAdd).2 w = x.toAdd.2 w :=
    (congrArg (fun y ↦ y * x.toAdd.2 w) (hu w)).trans (one_mul _)
  have hprod : (∏ w : S, G w (Multiplicative.ofAdd
      (((↑u⁻¹ : SAdeleRing ℚ S) * x.toAdd).2 w))) =
      ∏ w : S, G w (Multiplicative.ofAdd (x.toAdd.2 w)) :=
    Finset.prod_congr rfl fun w _ ↦ congrArg (fun y ↦ G w (Multiplicative.ofAdd y)) (hfin w)
  have h2 : H (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing ℚ S) * x.toAdd)) =
      a₂ (Multiplicative.ofAdd x.toAdd.1) *
        ∏ w : S, G w (Multiplicative.ofAdd (x.toAdd.2 w)) :=
    (hH _).trans (congrArg₂ (fun s t : ℂ ↦ s * t) (ha₂ x.toAdd).symm hprod)
  have h3 : D (Multiplicative.ofAdd x.toAdd) =
      (a (Multiplicative.ofAdd x.toAdd.1) - a₂ (Multiplicative.ofAdd x.toAdd.1)) *
        ∏ w : S, G w (Multiplicative.ofAdd (x.toAdd.2 w)) :=
    (hD _).trans (congrArg (fun s : ℂ ↦ s * _) (hd _))
  change H (Multiplicative.ofAdd x.toAdd) -
    H (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing ℚ S) * x.toAdd)) =
      D (Multiplicative.ofAdd x.toAdd)
  exact (congrArg₂ (fun s t : ℂ ↦ s - t) (hH _) h2).trans ((sub_mul _ _ _).symm.trans h3.symm)

/-- A pure tensor with flat archimedean factor is a restricted test when every finite place is
selected. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_tensorMem
    {F : Type u} [Field F] [NumberField F] (S : Finset V(F))
    (a : ℬ(InfiniteAdeleRing F)) (ha : a ∈ sLocalOrbitalArchimedeanFlatTests F)
    (G : ∀ w : S, ℬ(w.val.adicCompletion F)) :
    (sAdeleSchwartz_inductiveTensor_equiv F S).choose (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, G w)) ∈
      sLocalOrbitalSupportTests S S := by
  unfold sLocalOrbitalSupportTests
  exact Submodule.subset_span ⟨⟨a, ha⟩, G, fun w hw ↦ absurd w.property hw, rfl⟩

open Filter Topology in
/-- A test with value one at the origin whose difference with its translate by an S-idele with
trivial finite coordinates is a restricted test: the archimedean factor is constant near the
origin, so the difference of the two archimedean factors vanishes there. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_witness
    (S : Finset Vℚ) (u : (SAdeleRing ℚ S)ˣ) (hu : ∀ v : S, (u⁻¹).val.2 v = 1) :
    ∃ H : ℬ(SAdeleRing ℚ S), H (Multiplicative.ofAdd 0) = 1 ∧
      H - schwartzBruhatUnitTranslate u H ∈ sLocalOrbitalSupportTests S S := by
  let b : ContDiffBump (0 : mixedEmbedding.mixedSpace ℚ) := ⟨1, 2, one_pos, one_lt_two⟩
  let b₀ : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hb₀ (z : mixedEmbedding.mixedSpace ℚ) : b₀ z = ((b z : ℝ) : ℂ) := rfl
  have hb₁ : ∀ᶠ z in 𝓝 (0 : mixedEmbedding.mixedSpace ℚ), b₀ z = 1 := by
    filter_upwards [b.eventuallyEq_one] with z hz
    rw [hb₀, hz]
    rfl
  obtain ⟨J, hJ⟩ := archimedeanSchwartzBruhat_equiv (F := ℚ)
  have he := (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose_spec
  let G (w : S) : ℬ(w.val.adicCompletion ℚ) := finiteStandardGaussian w.val 1
  have hG (w : S) : G w (Multiplicative.ofAdd 0) = 1 := by
    change finiteStandardGaussianValue w.val 1 0 = 1
    unfold finiteStandardGaussianValue
    split_ifs with h
    · exact Set.indicator_of_mem (zero_mem (w.val.adicCompletionIntegers ℚ)) _
    · exact absurd (fun u _ ↦ rfl) h
  let r : (InfiniteAdeleRing ℚ)ˣ := Units.map (RingHom.fst _ _).toMonoidHom u
  have hflat := sLocalOrbitalSupportComparison_rat_two_fails_bumpDiff J hJ b₀ hb₁ r
  have hmem := sLocalOrbitalSupportComparison_rat_two_fails_tensorMem S _ hflat G
  have hH0 : (sAdeleSchwartz_inductiveTensor_equiv ℚ S).choose
      (J b₀ ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, G w)) (Multiplicative.ofAdd 0) = 1 := by
    refine (he (J b₀) G 0).trans ?_
    have h1 : J b₀ (Multiplicative.ofAdd (0 : SAdeleRing ℚ S).1) = 1 := by
      refine (hJ b₀ 0).trans ?_
      rw [map_zero]
      exact hb₁.self_of_nhds
    rw [h1, one_mul]
    exact Finset.prod_eq_one fun w _ ↦ hG w
  have hD := sLocalOrbitalSupportComparison_rat_two_fails_translateDiff S u hu (J b₀)
    (schwartzBruhatUnitTranslate r (J b₀)) (J b₀ - schwartzBruhatUnitTranslate r (J b₀)) G _ _
    (fun x ↦ rfl) (fun y ↦ rfl) (he (J b₀) G) (he _ G)
  exact ⟨_, hH0, (congrArg (fun k ↦ k ∈ sLocalOrbitalSupportTests S S) hD).mpr hmem⟩

open Filter Topology in
/-- On the trivial singleton-stage quotient the principal value is injective on theta classes:
its Euler multiplier does not vanish on the right half-plane. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_pvKer
    {p : Vℚ} {T : Finset Vℚ} (hT : T = {p}) (f : ℬ(SAdeleRing ℚ T))
    (hf : sAdelePrincipalValue ℚ (Finset.Subset.refl T) f ∈
      LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ T 1)) :
    f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ T 1) := by
  let P := sAdelePrincipalValue ℚ (Finset.Subset.refl T)
  have hP0 := (mem_sLocalHomogeneousAdelicTheta_ker_iff (1 : PontryaginDual J₁(ℚ, T)) (P f)).mp hf
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (1 : PontryaginDual J₁(ℚ, T)) f).mpr
  intro c hc
  obtain ⟨s, hs⟩ := sLocalOrbitalSupportComparison_rat_two_fails_onNormChart c.val (fun h ↦ hc h)
  change sLocalIdelicZFunction f c.val = 0
  rw [← hs]
  let Z := fun z : ℂ ↦ sLocalIdelicZFunction f
    ((quasiCharacterNormTwist (sIdeleQuotientNorm ℚ T)
      (isProperMap_sIdeleQuotientNorm ℚ T).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient ℚ T))) z))
  have heq : Z = 0 := by
    apply eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f 1)
      (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0
    intro z hz
    have hn : ∀ᶠ w : ℂ in 𝓝[≠] z, 0 < w.re := nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hzero : Z =ᶠ[𝓝[≠] z] 0 := by
      filter_upwards [hn, nhdsNE_le_codiscrete z (sLocalIdelicZFunction_principalValue T
        (Finset.Subset.refl T) f 1)] with w hw hP
      let c₀ := (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ T)
        (isProperMap_sIdeleQuotientNorm ℚ T).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient ℚ T))) w)
      let d := (⟨c₀, sLocalOrderBound_positive (F := ℚ) (S := T) 1 hw⟩ :
        {c : QuasiCharacter (SIdeleQuotient ℚ T) // 0 ≤ sLocalIdelicOrderBound c})
      let A := sLocalIdelicMellin (F := ℚ) (S := T)
      have hprod : (∏ v : T, if v.val ∈ T then
          finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c₀)
          else 1) = (1 - (p.asIdeal.absNorm : ℂ) ^ (-w))⁻¹ := by
        have : Subsingleton T := hT ▸ inferInstanceAs (Subsingleton (↥({p} : Finset Vℚ)))
        let v : T := ⟨p, hT ▸ Finset.mem_singleton_self _⟩
        rw [Finset.prod_eq_single v (fun b _ hb ↦ (hb (Subsingleton.elim _ _)).elim)
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left v.property]
        exact sLocalOrbitalSupportComparison_rat_two_fails_singleEuler v w hw
      have hone (h : J₁(ℚ, T)) : c₀ h.val = 1 := by
        change (1 : ℂ) * (((sIdeleQuotientNorm ℚ T h.val).val : ℝ) : ℂ) ^ w = 1
        rw [MonoidHom.mem_ker.mp h.property]
        simp
      have hPz : (A (P f)).val d = 0 := hP0 d (fun h ↦ hone h)
      change (A (P f)).val d = (A f).val d / _ at hP
      rw [hprod, div_inv_eq_mul, hPz] at hP
      have hne : (1 : ℂ) - (p.asIdeal.absNorm : ℂ) ^ (-w) ≠ 0 := by
        intro h0
        have hN : 1 < p.asIdeal.absNorm := by
          exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
        have hnorm := Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans hN) (-w)
        rw [← sub_eq_zero.mp h0, norm_one] at hnorm
        have hlt : ((p.asIdeal.absNorm : ℕ) : ℝ) ^ (-w).re < 1 :=
          Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) (by simpa using hw)
        exact hlt.ne hnorm.symm
      change (A f).val d = 0
      exact (mul_eq_zero.mp hP.symm).resolve_right hne
    exact (((sLocalIdelicZFunction_meromorphic f 1
      (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
        analyticAt_const.meromorphicNFAt).mp hzero).eq_of_nhds
  exact congrFun heq s

open scoped NNReal in
/-- The repaired comparison over ℚ with one selected prime is not injective. For a test `H`
with value one at the origin, the difference of `H` and its radial translate of norm `1/N(p)`
is a restricted test whose theta class is the principal value of the class of `H`, so it maps
to zero. Were its class zero, it would be the principal value of the class of a restricted
test `g`; the principal value is injective on theta classes, so `H - g` would lie in the theta
kernel, and evaluation at the origin would give `1 = 0`. -/
private theorem sLocalOrbitalSupportComparison_rat_two_fails_not_injective
    (S : Finset Vℚ) (p : Vℚ) (hS : S = {p}) :
    ¬ Function.Injective
      (sLocalOrbitalSupportComparison (F := ℚ) (Finset.Subset.refl S) 1) := by
  intro hinj
  have hu1 : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ _ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have h1 := sLocalOrbitalSupportComparison_rat_two_fails_oneLocal S hu1
  have hker (f : ℬ(SAdeleRing ℚ S))
      (hf : f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)) :
      f (Multiplicative.ofAdd 0) = 0 :=
    sLocalOrbitalSupportComparison_rat_two_fails_evalZero hu1 f (h1 ▸ hf)
  have hN : (0 : ℝ) < (p.asIdeal.absNorm : ℝ) := by
    exact_mod_cast zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p)
  let t : ℝ≥0ˣ := Units.mk0 ⟨(p.asIdeal.absNorm : ℝ)⁻¹, inv_nonneg.mpr hN.le⟩
    (fun h ↦ (inv_ne_zero hN.ne') (congrArg Subtype.val h))
  let u : (SAdeleRing ℚ S)ˣ :=
    Units.map (adeleProjection ℚ S).toMonoidHom (canonicalIdeleNormSection ℚ t)
  have hnorm : ((sIdeleNorm ℚ S u).val : ℝ) = (p.asIdeal.absNorm : ℝ)⁻¹ :=
    congrArg (fun z : ℝ≥0ˣ ↦ (z.val : ℝ)) (sIdeleNorm_project_canonicalSection ℚ S t)
  have hfin (v : S) : (u⁻¹).val.2 v = 1 := by
    change (canonicalIdeleNormSection ℚ t)⁻¹.val.2 v.val = 1
    rw [← map_inv]
    exact congrArg (fun b ↦ b v.val) (canonicalIdeleNormSection_finite ℚ t⁻¹)
  obtain ⟨H, hH0, hHU⟩ := sLocalOrbitalSupportComparison_rat_two_fails_witness S u hfin
  have hq := sLocalOrbitalSupportComparison_rat_two_fails_singlePV hS u hnorm H
  have hA : sLocalOrbitalSupportComparison (F := ℚ) (Finset.Subset.refl S) 1
      (Submodule.Quotient.mk ⟨H - schwartzBruhatUnitTranslate u H, hHU⟩) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨Submodule.Quotient.mk H, ?_⟩
    exact hq
  have hfR := (Submodule.Quotient.mk_eq_zero _).mp (hinj (hA.trans (map_zero _).symm))
  obtain ⟨g, hg⟩ := (mem_sLocalOrbitalSupportRelations_iff (Finset.Subset.refl S)
    1 ⟨H - schwartzBruhatUnitTranslate u H, hHU⟩).mp hfR
  have hPg : (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)).mkQ
        (sAdelePrincipalValue ℚ (Finset.Subset.refl S) H) =
      (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1)).mkQ
        (sAdelePrincipalValue ℚ (Finset.Subset.refl S) g.val) := hq.trans hg
  have hmem : sAdelePrincipalValue ℚ (Finset.Subset.refl S) (H - g.val) ∈
      LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ S 1) := by
    rw [map_sub]
    exact (Submodule.Quotient.eq _).mp hPg
  have h0 : H (Multiplicative.ofAdd 0) - g.val (Multiplicative.ofAdd 0) = 0 :=
    hker _ (sLocalOrbitalSupportComparison_rat_two_fails_pvKer hS (H - g.val) hmem)
  rw [hH0, sLocalOrbitalSupportComparison_rat_two_fails_testsZero S S g.val g.property] at h0
  norm_num at h0

/-- Paper: Theorem 8.1.0.1(1)–(2), p. 382, and the intersection on p. 384.
Even for the repaired comparison, both properties fail over ℚ with one selected prime.
For injectivity take (h(x) − h(2x)) times the 2-adic integer indicator, with h even,
smooth, compactly supported and one near zero. Diagonal translation by 2 identifies
its theta class with the principal value of the unrestricted tensor with real factor h.
Its Mellin transform has a simple pole at zero, whereas a restricted principal value
has holomorphic transform there. The Gaussian double pole witnesses nonsurjectivity. -/
theorem sLocalOrbitalSupportComparison_rat_two_fails :
    let v : Vℚ := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
    let S : Finset Vℚ := {v}
    let A := sLocalOrbitalSupportComparison (F := ℚ) (Finset.Subset.refl S) 1
    ¬ Function.Injective A ∧ ¬ Function.Surjective A := by
  intro v S A
  exact ⟨sLocalOrbitalSupportComparison_rat_two_fails_not_injective S v rfl,
    sLocalOrbitalSupportComparison_rat_two_fails_not_surjective S v (Finset.mem_singleton_self v)⟩

end RiemannMasullo
