module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Test functions for the polar-free counterexamples

The geometric valuation test and the flat archimedean bump were extracted from the proof of
the quasi-character multiplication counterexample in `Sec3b_QuasiCharacter_Printed.lean`.
They also supply the witnesses in ERRATA F56.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped BigOperators

namespace RiemannMasullo

open scoped ContDiff in
private theorem polarFreeTensor_geometric_stage (q : ℝ) (hq : 1 < q) :
    (fun y : ElementaryLieGroup 0 0 1 PUnit ↦
      if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0) ∈
      elementarySchwartzSubmodule 0 0 1 PUnit := by
  let f : ElementaryLieGroup 0 0 1 PUnit → ℂ := fun y ↦
    if 0 ≤ y.2.2.1 0 then (q : ℂ)⁻¹ ^ (y.2.2.1 0).toNat else 0
  have hconst (z : Fin 1 → ℤ) (b : PUnit)
      (x : EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) :
      f (elementaryCover x z b) = f (0, 0, z, b) := rfl
  refine ⟨fun z b ↦ ?_, fun ⟨α, β, γ, δ⟩ ↦ ?_⟩
  · change ContDiff ℝ ∞ (fun x ↦ f (elementaryCover x z b))
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

open scoped Topology in
open Filter in
private theorem polarFreeTensor_geometric_valuation {G : Type} [CommGroup G]
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
  let s : SchwartzBruhatStage e := ⟨_, polarFreeTensor_geometric_stage q hq⟩
  refine ⟨schwartzBruhatStageInclusion A e s, fun n ↦ ?_⟩
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (show π ^ n ∈ A.val.1 from trivial)]
  have hn : (d (π ^ n)).toAdd = (n : ℤ) := by simp [map_pow, hπ]
  change (if 0 ≤ (d (π ^ n)).toAdd then (q : ℂ)⁻¹ ^ (d (π ^ n)).toAdd.toNat else 0) = _
  rw [hn, ite_eq_left (Int.natCast_nonneg n), Int.toNat_natCast]

/-- A finite-place multiplicative Schwartz test with geometric values on uniformizer powers. -/
theorem exists_polarFree_geometric_shell_test (v : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (π : (v.adicCompletion ℚ)ˣ) (k : SchwartzBruhat (v.adicCompletion ℚ)ˣ),
      ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹ ∧
        ∀ n : ℕ, k (π ^ n) = (v.asIdeal.absNorm : ℂ)⁻¹ ^ n := by
  let K := v.adicCompletion ℚ
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨p, hp⟩ := V.exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : Kˣ := Units.mk0 (p : K) hp.ne_zero
  have hπ : V.IsUniformizer π.val := hp
  have hvπ : V π.val = WithZero.exp (-1 : ℤ) := hπ.trans
    (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective ℚ)))
  let d : Kˣ →* Multiplicative ℤ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (-(WithZero.log (V x.val)))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), neg_add]
        rfl }
  have hdπ : d π = Multiplicative.ofAdd 1 := by
    change Multiplicative.ofAdd (-(WithZero.log (V π.val))) = _
    simp [hvπ]
  have hk : (d.ker : Set Kˣ) = (v.adicCompletionIntegers ℚ).units := by
    ext x
    change x ∈ d.ker ↔ x ∈ (v.adicCompletionIntegers ℚ).units
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
  obtain ⟨k, hkn⟩ := polarFreeTensor_geometric_valuation d π hdπ ho hc _ hq
  exact ⟨π, k, norm_uniformizer_adicCompletion v _ hπ, by simpa using hkn⟩

open Function Set in
open scoped Topology in
/-- An archimedean flat Schwartz function can take the value one at the identity. -/
theorem exists_archimedeanFlatSchwartz_one (ι κ : Type*) [Fintype ι] [Fintype κ] :
    ∃ h : archimedeanFlatSchwartz (ι := ι) (κ := κ), h.val (1, 1) = 1 := by
  let U : Set ((ι → ℝ) × (κ → ℂ)) :=
    {x | (∀ i, x.1 i ≠ 0) ∧ (∀ j, x.2 j ≠ 0)}
  have hU : IsOpen U := by
    rw [show U = (⋂ i, {x : (ι → ℝ) × (κ → ℂ) | x.1 i ≠ 0}) ∩
      ⋂ j, {x : (ι → ℝ) × (κ → ℂ) | x.2 j ≠ 0} from by ext x; simp [U]]
    exact (isOpen_iInter_of_finite fun i ↦
      isOpen_ne_fun ((continuous_apply i).comp continuous_fst) continuous_const).inter
      (isOpen_iInter_of_finite fun j ↦
        isOpen_ne_fun ((continuous_apply j).comp continuous_snd) continuous_const)
  have h1 : ((1, 1) : (ι → ℝ) × (κ → ℂ)) ∈ U := by simp [U]
  obtain ⟨u, hsupport, hcompact, hsmooth, -, hvalue⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hU.mem_nhds h1)
  let g := Complex.ofRealCLM ∘ u
  have hgSupport : tsupport g ⊆ U := (tsupport_comp_subset rfl _).trans hsupport
  have hgCompact : HasCompactSupport g := hcompact.comp_left rfl
  let f := hgCompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hsmooth)
  have hf : f ∈ archimedeanFlatSchwartz := by
    refine mem_archimedeanFlatSchwartz_of_tsupport f (Set.disjoint_left.mpr ?_)
    intro x hx hw
    have hxU := hgSupport hx
    rcases hw with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hxU.1 i hi
    · exact hxU.2 j hj
  refine ⟨⟨f, hf⟩, ?_⟩
  change (u (1, 1) : ℂ) = 1
  simp [hvalue]

end RiemannMasullo
