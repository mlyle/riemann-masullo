module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # False printed PW-level claims in §7.3.2–7.3.3 -/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 600000

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "m(" F ", " T ")" => sIdeleQuotientNorm F T
local notation "J₁(" F ", " T ")" => (m(F, T)).ker
local notation "Θ(" F ", " T ", " χ ")" => SLocalHomogeneousThetaSpace F T χ
local notation "q(" F ", " T ", " χ ")" =>
  (LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T χ)).mkQ
local notation "size(" P ")" => (∏ v ∈ P, (v.asIdeal.absNorm : ℝ))
local notation "count(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S)
local notation "unitTests(" F ", " S ", " T ", " h ", " K ")" =>
  (sLocalPWTests h K).map (sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T))
local notation "unitLevel(" F ", " S ", " T ", " h ", " K ", " D ", " χ ")" =>
  ((unitTests(F, S, T, h, K) ⊓ D).map (q(F, T, χ))).topologicalClosure
local notation "zeroMoments(" F ", " T ")" => sAdelePolarSubspace F T

local notation "B(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "unitPV(" F ", " S ", " T ")" =>
  sAdelePrincipalValue F (Finset.sdiff_subset : T \ S ⊆ T)

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
On a test at either level the cited transition is asserted to insert unit indicators. -/
def Printed.sLocalPWTransition_eq_units : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        ∀ f : B(F, S), HasCompactSupport (sAdeleSchwartzFourier f).val →
          tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K →
          sAdeleSchwartzTransition F hST f = unitPV(F, S, T) (sAdeleSchwartzTransition F hST f)

open MeasureTheory in
/-- The local principal value of a test vanishes at zero. -/
private theorem sec3bP_localPV_zero {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
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
private theorem sec3bP_sPV_zero {F : Type*} [Field F] [NumberField F]
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
    simp only [hp, if_true, hx]
    exact sec3bP_localPV_zero p (g ⟨p, h₀ hp⟩)
  have hΦ (t : A ⊗[ℂ] FinestLocallyConvex P) : Φ t = 0 := by
    induction t using TensorProduct.induction_on with
    | zero => exact map_zero Φ
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

/-- Over the rationals with no finite places the S-integers have trivial Picard group. -/
private theorem sec3bP_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset Vℚ) : Set Vℚ).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- Over the rationals a single finite place is a saturated set. -/
private theorem sec3bP_saturated (p : Vℚ) : IsSaturatedPlaceSet (F := ℚ) {p} := by
  intro v w hv hw
  rw [Finset.mem_singleton] at hv ⊢
  subst hv
  apply HeightOneSpectrum.ext
  have h := congrArg HeightOneSpectrum.asIdeal hw
  change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) w.asIdeal =
    Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) v.asIdeal at h
  rwa [Algebra.algebraMap_self, Ideal.comap_id, Ideal.comap_id] at h

/-- Paper: Equations (7.3.2.2) and (7.3.2.13), pp. 351, 355.
Over the rationals add one prime and choose an inverse Fourier bump with positive
integral. At the zero tuple integer insertion gives its nonzero value at zero,
while unit insertion gives zero. -/
theorem Printed.sLocalPWTransition_eq_units_false : ¬ Printed.sLocalPWTransition_eq_units := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  let A := SAdeleRing ℚ S
  let G := Multiplicative A
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  -- A bump equal to one near zero, supported where every archimedean coordinate is small.
  let U : Set G := {x | ∀ w : InfinitePlace ℚ, ‖x.toAdd.1 w‖ < 1 / 2}
  have hU : IsOpen U := by
    simp only [U, setOf_forall]
    exact isOpen_iInter_of_finite fun w ↦ isOpen_lt
      ((continuous_apply w).comp (continuous_fst.comp continuous_toAdd)).norm continuous_const
  have h1U : (1 : G) ∈ U := fun w ↦ by
    change ‖(0 : A).1 w‖ < 1 / 2
    rw [show (0 : A).1 w = 0 from rfl, norm_zero]
    norm_num
  obtain ⟨g, hgc, hgs, hg1⟩ := schwartzBruhat_exists_local_unit hU h1U
  let f := sAdeleSchwartzFourier g
  have hFf (y : G) : sAdeleSchwartzFourier f y = g y⁻¹ := by
    have := sLocal_fourier_inversion g y.toAdd
    simpa [f] using this
  have hFf' : (sAdeleSchwartzFourier f).val = g.val ∘ (Homeomorph.inv G) := funext hFf
  have hcs : HasCompactSupport (sAdeleSchwartzFourier f).val := by
    rw [hFf']
    exact hgc.comp_homeomorph _
  have hts : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' sLocalPWBox S 1 := by
    rw [hFf', tsupport_comp_eq_preimage]
    intro y hy
    refine ⟨fun w ↦ ?_, fun v ↦ absurd v.property (Finset.notMem_empty v.val)⟩
    have hw : ‖(Multiplicative.toAdd y⁻¹).1 w‖ < 1 / 2 := hgs hy w
    rw [show (Multiplicative.toAdd y⁻¹).1 w = -((Multiplicative.toAdd y).1 w) from rfl,
      norm_neg] at hw
    exact pow_le_one₀ (norm_nonneg _) (by linarith)
  -- The test is not identically zero, since its Fourier transform is one at the origin.
  obtain ⟨y, hy⟩ : ∃ y : A, f (Multiplicative.ofAdd y) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : sAdeleSchwartzFourier f 1 = 0 := by
      let : MeasurableSpace A := instMeasurableSpaceSAdeleRing ℚ S
      change tamagawaFourier _ _ (fun x ↦ f (Multiplicative.ofAdd x)) _ = 0
      simp [hall, tamagawaFourier]
    rw [hFf, inv_one, hg1.eq_of_nhds] at h0
    exact one_ne_zero h0
  -- Apply the printed identity at the point with the same archimedean part and zero at p.
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  have hEq := h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p)
    sec3bP_pic hsub 1 one_pos (sLocalPWBox S 1) (by simp) f hcs hts
  let z : SAdeleRing ℚ T := (y.1, 0)
  have hval := congrArg (fun k : B(ℚ, T) ↦ k (Multiplicative.ofAdd z)) hEq
  simp only at hval
  rw [sec3bP_sPV_zero Finset.sdiff_subset hpT z rfl] at hval
  rw [sAdeleSchwartzTransition_apply, if_pos (fun w _ ↦ (w.val.adicCompletionIntegers ℚ).zero_mem)]
    at hval
  apply hy
  have hyz : (z.1, fun w : S ↦ z.2 ⟨w.val, hsub w.property⟩) = y :=
    Prod.ext rfl (funext fun w ↦ absurd w.property (Finset.notMem_empty w.val))
  rwa [hyz] at hval

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
Inside each printed test level the common kernel of the two evaluations has codimension two. -/
def Printed.sLocalPWTests_twoMoments : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (hST : S ⊆ T) (X : ℝ), 0 < X →
      ∀ K ∈ ({sLocalPWBox S X, sLocalPWProductRegion S X} : Set (Set (SAdeleRing F S))),
        let E := unitTests(F, S, T, hST, K)
        Module.finrank ℂ (E ⧸ (zeroMoments(F, T)).comap E.subtype) = 2

/-- Paper: Definitions 7.3.2.1(1) and 7.3.2.3(1), pp. 351, 355.
For one added rational prime every inserted test vanishes at zero, so at most
one independent moment remains on the test space. -/
theorem Printed.sLocalPWTests_twoMoments_false : ¬ Printed.sLocalPWTests_twoMoments := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  let E := unitTests(ℚ, S, T, hsub, sLocalPWBox S 1)
  let Q := (zeroMoments(ℚ, T)).comap E.subtype
  have h2 : Module.finrank ℂ (E ⧸ Q) = 2 :=
    h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p)
      sec3bP_pic hsub 1 one_pos (sLocalPWBox S 1) (by simp)
  -- The Fourier transform at zero, restricted to the inserted tests.
  let M := (sAdelePolarValues_isLinear (F := ℚ) (S := T)).mk' _
  let L : E →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp (M.comp E.subtype)
  -- Every inserted test is a unit principal value, so it vanishes at zero, and the
  -- zero-moment condition reduces to the kernel of the Fourier moment.
  have hker : LinearMap.ker L ≤ Q := by
    intro e he
    rw [Submodule.mem_comap, mem_sAdelePolarSubspace]
    refine ⟨?_, LinearMap.mem_ker.mp he⟩
    obtain ⟨t, -, hte⟩ := Submodule.mem_map.mp e.property
    rw [Submodule.subtype_apply, ← hte]
    exact sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t
  have hle : Module.finrank ℂ (E ⧸ LinearMap.ker L) ≤ 1 := by
    rw [L.quotKerEquivRange.finrank_eq]
    exact (Submodule.finrank_le _).trans (by simp)
  have : FiniteDimensional ℂ (E ⧸ LinearMap.ker L) :=
    L.quotKerEquivRange.symm.finiteDimensional
  let φ := Submodule.mapQ (LinearMap.ker L) Q LinearMap.id hker
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨e, rfl⟩ := Submodule.mkQ_surjective Q q
    exact ⟨Submodule.mkQ _ e, rfl⟩
  have hrange : Module.finrank ℂ (E ⧸ Q) ≤ Module.finrank ℂ (E ⧸ LinearMap.ker L) := by
    rw [← finrank_top ℂ (E ⧸ Q), ← LinearMap.range_eq_top.mpr hφ]
    exact LinearMap.finrank_range_le φ
  omega

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
The absolute levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalAbsolutePW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

open MeasureTheory in
/-- A test in the kernel of global homogeneous theta for the trivial character vanishes at
zero: after the polar term the homogeneous theta function is small at small norm. -/
private theorem sec3bP_globalHom_zero {F : Type*} [Field F] [NumberField F]
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
private theorem sec3bP_evalZero_ker {F : Type*} [Field F] [NumberField F]
    {T : Finset (V(F))} (hω : NormOneCharacterUnramifiedOutside
      (1 : PontryaginDual (ideleClassNorm F).ker) T)
    (f : B(F, T))
    (hf : f ∈ LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F T
      (sLocalNormOneCharacter T 1 hω))) :
    f (Multiplicative.ofAdd 0) = 0 := by
  have hg := sLocalHomogeneousThetaToGlobal_preserves_kernel (F := F) (S := T) hω hf
  rw [Submodule.mem_comap, LinearMap.mem_ker] at hg
  have h0 := sec3bP_globalHom_zero _ hg
  rw [sAdeleSchwartzToGlobal_apply, if_pos (fun w _ ↦ (w.adicCompletionIntegers F).zero_mem),
    map_zero] at h0
  exact h0

/-- Over the rationals with S = ∅ and one added prime, the unit levels for every family of
cutoff regions miss a class: evaluation at zero is continuous on the theta space, vanishes on
every inserted unit test, and is nonzero on some class. -/
private theorem sec3bP_seqDense_false (p : Vℚ) (hsub : (∅ : Finset Vℚ) ⊆ {p})
    (hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅)
    (K : ℝ → Set (SAdeleRing ℚ ∅)) :
    ¬ ∀ x : Θ(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub)),
      x ∈ (⊤ : Submodule ℂ (B(ℚ, {p}))).map (q(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub))) →
        ∃ u : ℕ → Θ(ℚ, {p}, sLocalNormOneCharacter {p} 1 (hu.mono hsub)),
          (∀ n, ∃ X > 0, u n ∈ unitLevel(ℚ, (∅ : Finset Vℚ), {p}, hsub, K X, ⊤,
            sLocalNormOneCharacter {p} 1 (hu.mono hsub))) ∧
          Tendsto u atTop (𝓝 x) := by
  intro h
  set χ := sLocalNormOneCharacter {p} 1 (hu.mono hsub) with hχ
  set Kθ := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap ℚ ({p} : Finset Vℚ) χ) with hKθ
  have hpT : p ∈ ({p} : Finset Vℚ) \ (∅ : Finset Vℚ) := by simp
  -- Evaluation at zero as a continuous functional on tests and on the theta space.
  let ℓ : B(ℚ, ({p} : Finset Vℚ)) →L[ℂ] ℂ :=
    ⟨(LinearMap.fst ℂ ℂ ℂ).comp ((adelePolarValues (F := ℚ)).comp (sAdeleSchwartzToGlobal ℚ ({p} : Finset Vℚ))),
      continuous_fst.comp ((adelePolarValues_continuous (F := ℚ)).comp
        (sAdeleSchwartzToGlobal_isEmbedding ℚ ({p} : Finset Vℚ)).continuous)⟩
  have hℓ (f : B(ℚ, ({p} : Finset Vℚ))) : ℓ f = f (Multiplicative.ofAdd 0) := by
    change sAdeleSchwartzToGlobal ℚ ({p} : Finset Vℚ) f (Multiplicative.ofAdd 0) = _
    rw [sAdeleSchwartzToGlobal_apply, if_pos (fun w _ ↦ (w.adicCompletionIntegers ℚ).zero_mem),
      map_zero]
  have hker : Kθ ≤ LinearMap.ker (ℓ : B(ℚ, ({p} : Finset Vℚ)) →ₗ[ℂ] ℂ) := fun f hf ↦ by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓ]
    exact sec3bP_evalZero_ker (hu.mono hsub) f hf
  let L : Θ(ℚ, ({p} : Finset Vℚ), χ) →L[ℂ] ℂ := Kθ.liftQL ℓ hker
  have hL (f : B(ℚ, ({p} : Finset Vℚ))) : L (Kθ.mkQ f) = f (Multiplicative.ofAdd 0) := hℓ f
  -- The insertion of a test that is one near zero.
  let G := Multiplicative (SAdeleRing ℚ ∅)
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset Vℚ)) → v.val.adicCompletion ℚ)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset Vℚ)) → v.val.adicCompletion ℚ)))
  obtain ⟨g, -, -, hg⟩ := schwartzBruhat_exists_local_unit (G := G) isOpen_univ (mem_univ 1)
  let f₀ := sAdeleSchwartzTransition ℚ hsub g
  have hf₀0 : f₀ (Multiplicative.ofAdd 0) = 1 := by
    rw [sAdeleSchwartzTransition_apply,
      if_pos (fun w _ ↦ (w.val.adicCompletionIntegers ℚ).zero_mem)]
    have h0 : ((0 : SAdeleRing ℚ ({p} : Finset Vℚ)).1, fun w : (∅ : Finset Vℚ) ↦
        (0 : SAdeleRing ℚ ({p} : Finset Vℚ)).2 ⟨w.val, hsub w.property⟩) = (0 : SAdeleRing ℚ ∅) :=
      Prod.ext rfl (funext fun w ↦ absurd w.property (Finset.notMem_empty w.val))
    rw [h0]
    exact hg.eq_of_nhds
  obtain ⟨u, hun, hlim⟩ := h _ (Submodule.mem_map_of_mem (p := ⊤) (Submodule.mem_top (x := f₀)))
  have hE (t : B(ℚ, ({p} : Finset Vℚ))) :
      L (Kθ.mkQ (sAdelePrincipalValue ℚ (Finset.sdiff_subset : ({p} : Finset Vℚ) \ (∅ : Finset Vℚ) ⊆ ({p} : Finset Vℚ)) t)) = 0 :=
    (hL _).trans (sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t)
  have hzero (n : ℕ) : L (u n) = 0 := by
    obtain ⟨X, -, hX⟩ := hun n
    have hX' := (Submodule.topologicalClosure_coe _).subst (motive := fun A ↦ u n ∈ A) hX
    refine closure_minimal (t := {x | L x = 0}) ?_ (isClosed_eq L.continuous continuous_const) hX'
    intro y hy
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.mp he.1
    exact hE t
  have hx : L (Kθ.mkQ f₀) = 0 :=
    tendsto_nhds_unique ((L.continuous.tendsto _).comp hlim)
      (by rw [show (⇑L ∘ u) = fun _ ↦ 0 from funext hzero]; exact tendsto_const_nhds)
  rw [hL, hf₀0] at hx
  exact one_ne_zero hx

/-- Paper: Proposition 7.3.2.2(1), p. 352, with Definition 7.3.2.1, p. 351.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalAbsolutePW_seqDense_false : ¬ Printed.sLocalAbsolutePW_seqDense := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hsub : (∅ : Finset Vℚ) ⊆ {p} := Finset.empty_subset _
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  exact sec3bP_seqDense_false p hsub hu (sLocalPWBox ∅)
    (h ℚ ∅ {p} {p} (by simp) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub _ rfl ⊤ (Or.inl rfl))

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
The invariant levels formed with the printed unit factors exhaust the homogeneous
theta space sequentially, both for unrestricted and for zero-moment tests. Applying
principal value to the inserted integer indicators realizes the printed unit factors. -/
def Printed.sLocalInvariantPW_seqDense : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S),
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ (D : Submodule ℂ (SchwartzBruhat (Multiplicative (SAdeleRing F T)))),
        (D = ⊤ ∨ D = zeroMoments(F, T)) →
        ∀ x : Θ(F, T, χ), x ∈ D.map (q(F, T, χ)) →
          ∃ u : ℕ → Θ(F, T, χ),
            (∀ n, ∃ X > 0, u n ∈ unitLevel(F, S, T, hST, sLocalPWProductRegion S X, D, χ)) ∧
            Tendsto u atTop (𝓝 x)

/-- Paper: Proposition 7.3.2.4(1), pp. 355–356, with Definition 7.3.2.3, p. 355.
Take F = ℚ, S = {∞}, S₀ = {p}, and the trivial character. All inserted tests
vanish near 0 at p, so their Mellin transforms have no pole at 2πi/log p.
The residue there is continuous and is nonzero on the Gaussian tensored with
the integer-ring indicator, whose Mellin transform contains (1 − p^(-s))⁻¹. -/
theorem Printed.sLocalInvariantPW_seqDense_false : ¬ Printed.sLocalInvariantPW_seqDense := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hsub : (∅ : Finset Vℚ) ⊆ {p} := Finset.empty_subset _
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  exact sec3bP_seqDense_false p hsub hu (sLocalPWProductRegion ∅)
    (h ℚ ∅ {p} {p} (by simp) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub _ rfl ⊤ (Or.inl rfl))

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
The closed zero-moment absolute level is said to have codimension two in the full level. -/
def Printed.sLocalAbsolutePW_zeroMoment_codim : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ X > (0 : ℝ),
        let K := sLocalPWBox S X
        let W := unitLevel(F, S, T, hST, K, ⊤, χ)
        let W₀ := unitLevel(F, S, T, hST, K, zeroMoments(F, T), χ)
        Module.finrank ℂ (W ⧸ W₀.comap W.subtype) = 2

/-- Paper: Discussion after Proposition 7.3.2.2(4), p. 354.
Take the quadratic character modulo five over the rationals at the stage with infinity and
five, with no added places. Translation by the local unit two preserves the test band and
the moments and acts by minus one on the theta quotient. Half the difference from the
translate represents the same class and has both moments zero. The two levels coincide. -/
theorem Printed.sLocalAbsolutePW_zeroMoment_codim_false :
    ¬ Printed.sLocalAbsolutePW_zeroMoment_codim := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  let χ := sLocalNormOneCharacter (F := ℚ) T 1 (hu.mono hsub)
  let K := sLocalPWBox S 1
  let E := unitTests(ℚ, S, T, hsub, K)
  let q := q(ℚ, T, χ)
  let W := unitLevel(ℚ, S, T, hsub, K, ⊤, χ)
  let W₀ := unitLevel(ℚ, S, T, hsub, K, zeroMoments(ℚ, T), χ)
  have h2 : Module.finrank ℂ (W ⧸ W₀.comap W.subtype) = 2 :=
    h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _) (sec3bP_saturated p) sec3bP_pic
      1 hu hsub χ rfl 1 one_pos
  -- Every inserted test vanishes at zero, so only the Fourier moment separates the levels.
  let M := (sAdelePolarValues_isLinear (F := ℚ) (S := T)).mk' _
  let L : B(ℚ, T) →ₗ[ℂ] ℂ := (LinearMap.snd ℂ ℂ ℂ).comp M
  have hE0 (e : B(ℚ, T)) (he : e ∈ E) : e (Multiplicative.ofAdd 0) = 0 := by
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.mp he
    exact sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t
  have hpol (e : B(ℚ, T)) (he : e ∈ E) (hL : L e = 0) : e ∈ zeroMoments(ℚ, T) :=
    (mem_sAdelePolarSubspace _).mpr ⟨hE0 e he, hL⟩
  obtain ⟨R, hRE, hR1, hRfd, hsplit⟩ : ∃ R : Submodule ℂ (B(ℚ, T)), R ≤ E ∧
      Module.finrank ℂ R ≤ 1 ∧ FiniteDimensional ℂ R ∧ E ≤ (E ⊓ zeroMoments(ℚ, T)) ⊔ R := by
    by_cases hex : ∃ e₀ ∈ E, L e₀ ≠ 0
    · obtain ⟨e₀, he₀, hL₀⟩ := hex
      refine ⟨ℂ ∙ e₀, (Submodule.span_singleton_le_iff_mem _ _).mpr he₀,
        (finrank_span_le_card ({e₀} : Set (B(ℚ, T)))).trans (by simp), inferInstance,
        fun e he ↦ ?_⟩
      have hm : e - (L e / L e₀) • e₀ ∈ E := E.sub_mem he (E.smul_mem _ he₀)
      have hd : e - (L e / L e₀) • e₀ ∈ E ⊓ zeroMoments(ℚ, T) := by
        refine ⟨hm, hpol _ hm ?_⟩
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hL₀, sub_self]
      have he' : e = (e - (L e / L e₀) • e₀) + (L e / L e₀) • e₀ := by abel
      rw [he']
      exact Submodule.add_mem_sup hd (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e₀))
    · push Not at hex
      exact ⟨⊥, bot_le, by simp, inferInstance,
        fun e he ↦ Submodule.mem_sup_left ⟨he, hpol e he (hex e he)⟩⟩
  -- The closure of the inserted tests lies in the closed zero-moment level plus one line.
  let Rq := R.map q
  have : FiniteDimensional ℂ Rq := inferInstance
  have hcl : IsClosed ((W₀ ⊔ Rq : Submodule ℂ (Θ(ℚ, T, χ))) : Set (Θ(ℚ, T, χ))) :=
    Submodule.isClosed_sup_finiteDimensional W₀ Rq (Submodule.isClosed_topologicalClosure _)
  have hWle : W ≤ W₀ ⊔ Rq := by
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    intro x hx
    obtain ⟨e, ⟨he, -⟩, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp (hsplit he)
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ha))
      (Submodule.mem_map_of_mem hr)
  have hRW : Rq ≤ W := (Submodule.map_mono (le_inf hRE le_top)).trans
    (Submodule.le_topologicalClosure _)
  -- Hence that line maps onto the quotient, which has dimension at most one.
  let ψ : Rq →ₗ[ℂ] W ⧸ W₀.comap W.subtype :=
    (W₀.comap W.subtype).mkQ ∘ₗ Submodule.inclusion hRW
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, ha, r, hr, hw⟩ := Submodule.mem_sup.mp (hWle w.property)
    refine ⟨⟨r, hr⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    have hrw : (r : _) - w = -a := by rw [← hw]; abel
    change (r : _) - (w : _) ∈ W₀
    rw [hrw]
    exact W₀.neg_mem ha
  have hle : Module.finrank ℂ (W ⧸ W₀.comap W.subtype) ≤ Module.finrank ℂ Rq :=
    LinearMap.finrank_le_finrank_of_surjective hψ
  have hRq : Module.finrank ℂ Rq ≤ Module.finrank ℂ R := Submodule.finrank_map_le q R
  omega

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
The diagram of inclusions and restrictions of the continuous ambient PV operator
commutes at the printed cutoffs and is equivariant for the large-norm semigroup.
The containments define the restrictions, so both paths have the same ambient value. -/
def Printed.sLocalPW_principalValue_diagram : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T R : Finset (V(F))),
    T = S ∪ S₀ →
    Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ → R ⊆ S₀ → IsSaturatedPlaceSet (F := F) R →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y → X ^ count(F, S) ≤ Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      ∀ hRT : R ⊆ T,
        let D := zeroMoments(F, T)
        let H₀ := D.map (q(F, T, χ))
        let a := unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)
        let b := unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)
        let a' := unitLevel(F, S, T, hST, sLocalPWBox S (size(R) * X), D, χ)
        let b' := unitLevel(F, S, T, hST, sLocalPWProductRegion S (size(R) * Y), D, χ)
        let P := sLocalHomogeneousThetaPrincipalValue (F := F) hRT χ
        let A := (existsUnique_sLocalHomogeneousThetaAction (F := F) (S := T) χ).exists.choose
        a ≤ b ∧ b ≤ H₀ ∧ a' ≤ b' ∧ b' ≤ H₀ ∧
        a.map P ≤ a' ∧ b.map P ≤ b' ∧ H₀.map P ≤ H₀ ∧
        ∀ g : SIdeleQuotient F T, 1 ≤ ((m(F, T) g).val : ℝ) →
          (∀ E ∈ ({a, b, a', b', H₀} : Set (Submodule ℂ (Θ(F, T, χ)))),
            ∀ x ∈ E, A g x ∈ E) ∧ ∀ x ∈ H₀, P (A g x) = A g (P x)

/-- Fourier theta evaluation on the trivial component, read from the second Čech coordinate. -/
private theorem sec3bP_fourierEval (S : Finset Vℚ) (g : SIdeleQuotient ℚ S) :
    ∃ L : Θ(ℚ, S, 1) →L[ℂ] ℂ, ∀ f : B(ℚ, S),
      L (q(ℚ, S, 1) f) = sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier f) g := by
  let := isClosed_sProjectedDiagonal (F := ℚ) (S := S)
  let : T2Space (SIdeleQuotient ℚ S) := inferInstanceAs (T2Space (_ ⧸ _))
  let : LocallyCompactSpace (SAdeleRing ℚ S)ˣ := (sIdeleGroup_description ℚ S).2.2.1
  let (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing ℚ S) := inferInstanceAs
    (SecondCountableTopology (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology (SAdeleRing ℚ S)ˣ := (sIdeleGroup_description ℚ S).1.secondCountableTopology
  have hpair := (existsUnique_sLocalCechThetaPair (F := ℚ) (S := S) 1).exists
  simp only [inv_one] at hpair
  obtain ⟨U, hU⟩ := hpair
  let m : SIdeleQuotient ℚ S →ₜ* ℝ≥0ˣ := ⟨m(ℚ, S), (isProperMap_sIdeleQuotientNorm ℚ S).continuous⟩
  let E := ModulatedExponentialDecay m (Ioi (0 : ℝ))
  let ev : E →L[ℂ] ℂ :=
    ⟨(LinearMap.proj g).comp (modulatedExponentialDecaySubmodule m _).subtype,
      continuous_modulatedExponentialDecay_eval m _ ⟨1, one_pos⟩ g⟩
  exact ⟨ev.comp ((Submodule.subtypeL _).comp ((ContinuousLinearMap.snd ℂ _ _).comp U)),
    fun f ↦ congrFun (hU f).2 g⟩

/-- Every term in the homogeneous theta integral at g has the same idelic norm as g. -/
private theorem sec3bP_theta_zero (S : Finset Vℚ) (g : SIdeleQuotient ℚ S) (f : B(ℚ, S))
    (hz : ∀ u : (SAdeleRing ℚ S)ˣ, sIdeleNorm ℚ S u = m(ℚ, S) g →
      f (Multiplicative.ofAdd u.val) = 0) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 f g = 0 := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  apply (MeasureTheory.integral_congr_ae (Eventually.of_forall fun k ↦ ?_)).trans (MeasureTheory.integral_zero _ _)
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (g * k.val)
  simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one, ← ha,
    sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  refine (tsum_congr fun ξ ↦ hz (sUnitEmbedding ℚ S ξ * a) ?_).trans tsum_zero
  have hξ : sIdeleNorm ℚ S (sUnitEmbedding ℚ S ξ) = 1 := MonoidHom.mem_ker.mp ((sIdeleNorm_spec ℚ S).2 ⟨ξ, rfl⟩)
  rw [map_mul, hξ, one_mul,
    ← sIdeleQuotientNorm_mk, ha, map_mul, MonoidHom.mem_ker.mp k.property, mul_one]

open MeasureTheory in
/-- A nonnegative test which is positive at an idele has positive homogeneous theta there. -/
private theorem sec3bP_theta_ne (S : Finset Vℚ) (a : (SAdeleRing ℚ S)ˣ) (f : B(ℚ, S))
    (hf : ∀ x, 0 ≤ (f x).re) (ha : 0 < (f (Multiplicative.ofAdd a.val)).re) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 f (QuotientGroup.mk a) ≠ 0 := by
  let : MeasurableSpace J₁(ℚ, S) := borel _
  let : BorelSpace J₁(ℚ, S) := ⟨rfl⟩
  let μ : MeasureTheory.Measure J₁(ℚ, S) := sLocalNormOneQuotientMeasure ℚ S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := S)).1
  let : CompactSpace J₁(ℚ, S) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ S).isCompact_preimage isCompact_singleton)
  let θ := sLocalAdelicThetaOnClasses ℚ S f
  have hle (b : (SAdeleRing ℚ S)ˣ) : (f (Multiplicative.ofAdd b.val)).re ≤ (θ (QuotientGroup.mk b)).re := by
    change _ ≤ (sLocalAdelicThetaOnClasses ℚ S f (QuotientGroup.mk b)).re
    have hs := ((sLocalAdelicTheta_hasSumUniformlyOn ℚ S f {b} isCompact_singleton).hasSum rfl).summable
    rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply, Complex.re_tsum hs]
    simpa only [Function.comp_apply, Complex.reCLM_apply, map_one, one_mul] using
      (hs.mapL Complex.reCLM).le_tsum 1 (fun ξ _ ↦ hf _)
  let v (k : J₁(ℚ, S)) := θ (QuotientGroup.mk a * k.val)
  have hc : Continuous v := θ.continuous.comp (continuous_const.mul (continuous_subtype_val (p := (· ∈ J₁(ℚ, S)))))
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := μ)
  have hp : 0 < ∫ k, (v k).re ∂μ := by
    apply MeasureTheory.integral_pos_of_integrable_nonneg_ne_zero (Complex.continuous_re.comp hc)
      ((Complex.continuous_re.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (x := 1)
    · intro k
      obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (QuotientGroup.mk a * k.val)
      exact (hf _).trans (hb ▸ hle b)
    · simpa only [Function.comp_apply, v, OneMemClass.coe_one, mul_one] using (ha.trans_le (hle a)).ne'
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one]
  intro h
  change ∫ k, v k ∂μ = 0 at h
  have hr := Complex.reCLM.integral_comp_comm (μ := μ) hi
  change (∫ k, (v k).re ∂μ) = (∫ k, v k ∂μ).re at hr
  rw [hr, h, Complex.zero_re] at hp
  exact lt_irrefl _ hp

local notation "prodNorm(" S ", " x ")" =>
  ((∏ w : InfinitePlace ℚ, ‖(x : SAdeleRing ℚ S).1 w‖ ^ w.mult) * ∏ v : S, ‖x.2 v‖)

private theorem sec3bP_prodNorm_unit {S : Finset Vℚ} (u : (SAdeleRing ℚ S)ˣ) :
    prodNorm(S, u.val) = ((sIdeleNorm ℚ S u).val : ℝ) := by simp [sIdeleNorm]

/-- A compact Fourier bump on an open shell can be chosen with nonzero homogeneous
Fourier theta at any prescribed idele on that shell. -/
private theorem sec3bP_shell_bump (S : Finset Vℚ) (a : (SAdeleRing ℚ S)ˣ) (l r : ℝ)
    (ha : ((sIdeleNorm ℚ S a).val : ℝ) ∈ Ioo l r) :
    ∃ f : B(ℚ, S), HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      (∀ x ∈ tsupport (sAdeleSchwartzFourier f).val, prodNorm(S, x.toAdd) ∈ Ioo l r) ∧
      sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier f) (QuotientGroup.mk a) ≠ 0 := by
  let (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let G := Multiplicative (SAdeleRing ℚ S)
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let U : Set G := {x | prodNorm(S, x.toAdd) ∈ Ioo l r}
  have hU : IsOpen U := by
    refine isOpen_Ioo.preimage (Continuous.mul ?_ ?_)
    · exact continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp
        (continuous_fst.comp continuous_toAdd)).norm.pow w.mult)
    · exact continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp
        (continuous_snd.comp continuous_toAdd)).norm
  have ham : Multiplicative.ofAdd a.val ∈ U := by
    change prodNorm(S, a.val) ∈ Ioo l r
    rwa [sec3bP_prodNorm_unit]
  obtain ⟨b, hc, hs, hb⟩ := schwartzBruhat_exists_local_unit hU ham
  -- As in the compact shape construction in Ch05 Sec3b, take the squared modulus.
  have hn : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ ↦ Complex.normSq z) :=
    (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  obtain ⟨k, hk⟩ := compact_schwartzBruhat_comp hc
    (φ := fun z ↦ (Complex.normSq z : ℂ)) (Complex.ofRealCLM.contDiff.comp hn) (by simp)
  let F := sAdeleSchwartzFourier (F := ℚ) (S := S)
  have h4 : F (F (F (F k))) = k := by
    apply Subtype.ext
    funext x
    exact (sLocal_fourier_inversion (F (F k)) x.toAdd).trans
      ((sLocal_fourier_inversion k (-x.toAdd)).trans (by rw [neg_neg]; rfl))
  refine ⟨F (F (F k)), ?_⟩
  change HasCompactSupport (F (F (F (F k)))).val ∧ _
  rw [show sAdeleSchwartzFourier (F (F (F k))) = k from h4, h4]
  refine ⟨by rw [hk]; exact hc.comp_left (by simp), ?_, sec3bP_theta_ne S a k ?_ ?_⟩
  · intro x hx
    apply hs
    refine closure_mono (s := Function.support k.val) (t := Function.support b.val) ?_ hx
    intro y hy hyb
    apply hy
    change b y = 0 at hyb
    simp [hk, hyb]
  · intro x
    simp [hk, Complex.normSq_nonneg]
  · simp [hk, hb.eq_of_nhds]

/-- A compact set of frequencies fits in a single box. From the compact-box argument in Sec3b. -/
private theorem sec3bP_compact_box {S : Finset Vℚ} {K : Set (Multiplicative (SAdeleRing ℚ S))}
    (hK : IsCompact K) : ∃ X > 0, K ⊆ Multiplicative.toAdd ⁻¹' sLocalPWBox S X := by
  let N (x : SAdeleRing ℚ S) := (∑ w : InfinitePlace ℚ, ‖x.1 w‖ ^ w.mult) + ∑ v : S, ‖x.2 v‖
  have hN : Continuous N := (continuous_finsetSum _ fun w _ ↦
    ((continuous_apply w).comp continuous_fst).norm.pow w.mult).add
      (continuous_finsetSum _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  obtain ⟨R, hR⟩ := (hK.image (hN.comp continuous_toAdd)).bddAbove
  refine ⟨max R 1, zero_lt_one.trans_le (le_max_right _ _), fun x hx ↦ ?_⟩
  have hxR : N x.toAdd ≤ max R 1 := (hR (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
  · exact (Finset.single_le_sum (fun i _ ↦ pow_nonneg (norm_nonneg _) _) (Finset.mem_univ w)).trans
      ((le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hxR)
  · exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg _) (Finset.mem_univ v)).trans
      ((le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ pow_nonneg (norm_nonneg _) _)).trans hxR)

/-- Two disjoint Fourier shells give a nonzero Fourier theta even after imposing one
additional scalar moment. Their common box bound is independent of that moment. -/
private theorem sec3bP_shell_test (S : Finset Vℚ) :
    ∃ B₀ > (0 : ℝ), ∀ M : B(ℚ, S) →ₗ[ℂ] ℂ, ∃ f : B(ℚ, S),
      M f = 0 ∧ HasCompactSupport (sAdeleSchwartzFourier f).val ∧
      tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWBox S B₀ ∧
      (∀ x ∈ tsupport (sAdeleSchwartzFourier f).val, prodNorm(S, x.toAdd) ∈ Ioo (1/2) 3) ∧
      ∃ g : SIdeleQuotient ℚ S, ((m(ℚ, S) g).val : ℝ) ∈ Icc 1 2 ∧
        sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier f) g ≠ 0 := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ S
  let t : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (τ t)
  have hb2 : ((sIdeleNorm ℚ S b).val : ℝ) = 2 := by
    rw [← sIdeleQuotientNorm_mk, hb, hτ]
    rfl
  obtain ⟨u, hu, hSu, hθu⟩ := sec3bP_shell_bump S 1 (1/2) (3/2) (by simp; norm_num)
  obtain ⟨v, hv, hSv, hθv⟩ := sec3bP_shell_bump S b (3/2) 3 (by rw [hb2]; constructor <;> norm_num)
  obtain ⟨B₀, hB, hbox⟩ := sec3bP_compact_box (hu.union hv)
  refine ⟨B₀, hB, fun M ↦ ?_⟩
  let K := tsupport (sAdeleSchwartzFourier u).val ∪ tsupport (sAdeleSchwartzFourier v).val
  have hK (x) (hx : x ∈ K) : prodNorm(S, x.toAdd) ∈ Ioo (1/2) 3 := by
    rcases hx with hx | hx
    · exact ⟨(hSu x hx).1, (hSu x hx).2.trans (by norm_num)⟩
    · exact ⟨lt_trans (by norm_num) (hSv x hx).1, (hSv x hx).2⟩
  by_cases hM : M u = 0
  · exact ⟨u, hM, hu, subset_union_left.trans hbox, fun x hx ↦ hK x (Or.inl hx),
      QuotientGroup.mk (1 : (SAdeleRing ℚ S)ˣ), by simp, hθu⟩
  let c := M v / M u
  let w := v - c • u
  obtain ⟨A, hA⟩ := sLocal_fourier_continuousLinear (F := ℚ) (S := S)
  have hw : sAdeleSchwartzFourier w = sAdeleSchwartzFourier v - c • sAdeleSchwartzFourier u := by
    rw [← hA, map_sub, map_smul, hA, hA]
  have hs : tsupport (sAdeleSchwartzFourier w).val ⊆ K := by
    rw [hw]
    exact (tsupport_sub _ _).trans (union_subset subset_union_right
      ((tsupport_smul_subset_right (fun _ ↦ c) _).trans subset_union_left))
  have hz : sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier u) (QuotientGroup.mk b) = 0 := by
    apply sec3bP_theta_zero
    intro a ha
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hlt := (hSu _ hx).2
    change prodNorm(S, a.val) < 3/2 at hlt
    rw [sec3bP_prodNorm_unit, ha, sIdeleQuotientNorm_mk, hb2] at hlt
    norm_num at hlt
  refine ⟨w, ?_, (hu.union hv).of_isClosed_subset isClosed_closure hs, hs.trans hbox,
    fun x hx ↦ hK x (hs hx), QuotientGroup.mk b, ?_, ?_⟩
  · simp [w, c, div_mul_cancel₀ _ hM]
  · rw [sIdeleQuotientNorm_mk, hb2]; constructor <;> norm_num
  · rw [hw, map_sub, map_smul]
    simpa only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, hz, smul_zero, sub_zero] using hθv

private theorem sec3bP_one_unramified (S : Finset Vℚ) :
    NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩

private theorem sec3bP_one_local (S : Finset Vℚ)
    (hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S) :
    sLocalNormOneCharacter S 1 hu = 1 := by
  ext y
  have h := sLocalNormOneCharacter_eq_sIdeleRestriction (F := ℚ) (S := S) 1
    ⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩ (fun _ ↦ rfl) y
  rw [h]
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
  rw [← hg, sIdeleRestriction_mk]
  rfl

/-- Composing ordinary stage insertion with principal value at the added places gives
a closed embedding on the trivial theta component. -/
private theorem sec3bP_unit_embedding {S T : Finset Vℚ} (hST : S ⊆ T) :
    ∃ E : Θ(ℚ, S, 1) →ₗ[ℂ] Θ(ℚ, T, 1), IsClosedEmbedding E ∧
      ∀ f, E (q(ℚ, S, 1) f) = q(ℚ, T, 1) (unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f)) := by
  have hu := sec3bP_one_unramified S
  let χ := sLocalNormOneCharacter T 1 (hu.mono hST)
  let η := sLocalNormOneCharacter S 1 hu
  let i := sLocalHomogeneousThetaTransition hu hST
  let P := sLocalHomogeneousThetaPrincipalValue (Finset.sdiff_subset : T \ S ⊆ T) χ
  have hex : ∃ E : Θ(ℚ, S, η) →ₗ[ℂ] Θ(ℚ, T, χ), IsClosedEmbedding E ∧
      ∀ f, E (q(ℚ, S, η) f) = q(ℚ, T, χ) (unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f)) :=
    ⟨P.comp i, (sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding _ χ).comp
      (sLocalHomogeneousThetaTransition_isClosedEmbedding hu hST), fun f ↦
        congrArg P (LinearMap.congr_fun (sLocalHomogeneousThetaTransition_spec hu hST).1 f)⟩
  rwa [show η = 1 from sec3bP_one_local S hu, show χ = 1 from sec3bP_one_local T _] at hex

/-- Beyond the product cutoff, the old-stage Fourier theta evaluation vanishes on every
representative in the closed unit level, after cancellation of its insertion. -/
private theorem sec3bP_unitLevel_bound {S T : Finset Vℚ} (hST : S ⊆ T)
    (E : Θ(ℚ, S, 1) →ₗ[ℂ] Θ(ℚ, T, 1)) (hc : IsClosedEmbedding E)
    (he : ∀ f, E (q(ℚ, S, 1) f) = q(ℚ, T, 1) (unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f)))
    {Y : ℝ} (f : B(ℚ, S))
    (hf : E (q(ℚ, S, 1) f) ∈ unitLevel(ℚ, S, T, hST, sLocalPWProductRegion S Y, zeroMoments(ℚ, T), 1))
    (g : SIdeleQuotient ℚ S) (hg : Y < ((m(ℚ, S) g).val : ℝ)) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier f) g = 0 := by
  obtain ⟨L, hL⟩ := sec3bP_fourierEval S g
  have hclosed : IsClosed (L.ker.map E : Set (Θ(ℚ, T, 1))) := hc.isClosedMap _ L.isClosed_ker
  obtain ⟨x, hx, hxf⟩ := Submodule.topologicalClosure_minimal _ (t := L.ker.map E) (by
    rintro _ ⟨b, ⟨⟨t, ht, rfl⟩, -⟩, rfl⟩
    obtain ⟨v, rfl, -, hband⟩ := (mem_sLocalPWTests hST _ _).mp ht
    refine ⟨q(ℚ, S, 1) v, ?_, he v⟩
    change L (q(ℚ, S, 1) v) = 0
    rw [hL]
    apply sec3bP_theta_zero
    intro u hu
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hn := (mem_sLocalPWProductRegion_units (F := ℚ) Y u).mp (hband (by exact h))
    exact hg.not_ge (hu ▸ hn)) hclosed hf
  rw [← hL, ← hc.injective hxf]
  exact hx

/-- The value at zero already vanishes after unit insertion. The remaining moment is
one linear constraint on the small-stage test. -/
private theorem sec3bP_unit_moment {S T : Finset Vℚ} (hST : S ⊆ T) (hne : (T \ S).Nonempty) :
    ∃ M : B(ℚ, S) →ₗ[ℂ] ℂ, ∀ f, M f = 0 →
      unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f) ∈ zeroMoments(ℚ, T) := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨((LinearMap.snd ℂ ℂ ℂ).comp ((sAdelePolarValues_isLinear (F := ℚ) (S := T)).mk' _)).comp
    ((unitPV(ℚ, S, T)).comp (sAdeleSchwartzTransition ℚ hST)), fun f hf ↦ ?_⟩
  exact (mem_sAdelePolarSubspace _).mpr ⟨sec3bP_sPV_zero Finset.sdiff_subset hp 0 rfl _, hf⟩

private theorem sec3bP_unitLevel_mem {S T : Finset Vℚ} (hST : S ⊆ T) (K : Set (SAdeleRing ℚ S))
    (f : B(ℚ, S)) (hc : HasCompactSupport (sAdeleSchwartzFourier f).val)
    (hs : tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' K)
    (hm : unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f) ∈ zeroMoments(ℚ, T)) :
    q(ℚ, T, 1) (unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f)) ∈
      unitLevel(ℚ, S, T, hST, K, zeroMoments(ℚ, T), 1) :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem ⟨Submodule.mem_map_of_mem
    ((mem_sLocalPWTests hST _ _).mpr ⟨f, rfl, hc, hs⟩), hm⟩)

/-- Rational prime ideals have unbounded residue sizes, even after removing finitely many. -/
private theorem sec3bP_large_prime (S : Finset Vℚ) (b : ℝ) :
    ∃ p : Vℚ, p ∉ S ∧ b < (p.asIdeal.absNorm : ℝ) := by
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt b
  have hi : Infinite Vℚ := Rat.HeightOneSpectrum.primesEquiv.infinite_iff.mpr inferInstance
  have hf := (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 ℚ) n).preimage
    (f := fun p : Vℚ ↦ p.asIdeal) (fun _ _ _ _ h ↦ HeightOneSpectrum.ext h)
  obtain ⟨p, hp⟩ := (S.finite_toSet.union hf).exists_notMem
  have hpn : n < p.asIdeal.absNorm := lt_of_not_ge fun h ↦ hp (Or.inr h)
  exact ⟨p, fun h ↦ hp (Or.inl h), hn.trans (by exact_mod_cast hpn)⟩

/-- Paper: Proposition 7.3.3.2, pp. 357–358.
Over ℚ take one old finite place and add a prime of residue size N. Choose a test
with Fourier support in a box of size B and nonzero Fourier theta at a norm in [1, 2].
With X = B/N and Y = X², the bottom box has size B and the bottom product cutoff
is B²/N. Choosing N > B² puts this cutoff below 1. The Fourier theta evaluation
separates the two closed levels after cancelling the common unit insertion. -/
theorem Printed.sLocalPW_principalValue_diagram_false :
    ¬ Printed.sLocalPW_principalValue_diagram := by
  intro h
  obtain ⟨r, -, -⟩ := sec3bP_large_prime ∅ 1
  let S : Finset Vℚ := {r}
  have hPic : Subsingleton (CommRing.Pic ((S : Set Vℚ).integer ℚ)) := by
    let := sec3bP_pic
    obtain ⟨_, _, _, hsurj, _⟩ := picard_localization_exact ℚ ∅ S (Finset.empty_subset _)
    exact hsurj.subsingleton
  obtain ⟨B₀, hB, htest⟩ := sec3bP_shell_test S
  obtain ⟨p, hp, hlarge⟩ := sec3bP_large_prime S (B₀ ^ 2)
  let T := S ∪ {p}
  have hST : S ⊆ T := Finset.subset_union_left
  have hpT : p ∈ T \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), hp⟩
  let N : ℝ := p.asIdeal.absNorm
  have hN : 0 < N := (sq_nonneg _).trans_lt hlarge
  let X := B₀ / N
  have hX : 0 < X := div_pos hB hN
  have hsize : size(({p} : Finset Vℚ)) = N := by simp [N]
  have hcard : count(ℚ, S) = 2 := by
    simp [S, Fintype.card_unique]
  have hbot := (h ℚ S {p} T {p} rfl (Finset.disjoint_singleton_right.mpr hp) (sec3bP_saturated p)
    (by rfl) (sec3bP_saturated p) hPic 1 (sec3bP_one_unramified S) X (X ^ 2) hX (sq_pos_of_pos hX)
    (by rw [hcard]) hST 1 (sec3bP_one_local T _).symm (Finset.subset_union_right)).2.2.1
  have hNX : N * X = B₀ := by dsimp [X]; field_simp
  rw [hsize, hNX] at hbot
  obtain ⟨E, hE, he⟩ := sec3bP_unit_embedding hST
  obtain ⟨M, hM⟩ := sec3bP_unit_moment hST ⟨p, hpT⟩
  obtain ⟨f, hm, hc, hbox, -, g, hg, hne⟩ := htest M
  have hf := hbot (sec3bP_unitLevel_mem hST _ f hc hbox (hM f hm))
  rw [← he] at hf
  apply hne (sec3bP_unitLevel_bound hST E hE he f hf g ?_)
  apply lt_of_lt_of_le _ hg.1
  have hlevel : N * X ^ 2 = B₀ ^ 2 / N := by dsimp [X]; field_simp
  rw [hlevel, div_lt_one hN]
  exact hlarge

local notation "primary(" F ", " T ", " p ")" => sLocalPrimaryPlaces (F := F) T p

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Both printed quotients require the primary principal-value image of the given
zero-moment level to lie inside the level divided by the product of residue sizes. -/
def Printed.sLocalPWOrbitalQuotients_defined : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ →
    IsSaturatedPlaceSet (F := F) S → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S) (X Y : ℝ),
      0 < X → 0 < Y →
      ∀ (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
        χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
        let PV := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
        let D := zeroMoments(F, T)
        (unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
        (unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ)).map PV ≤
          unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ)

local notation "normChart(" S ", " z ")" =>
  quasiCharacterNormTwist (m(ℚ, S)) (isProperMap_sIdeleQuotientNorm ℚ S).continuous
    ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual (SIdeleQuotient ℚ S))) z

/-- On the trivial norm-one component every quasi-character is a bare norm power. -/
private theorem sec3bP_on_norm_chart {S : Finset Vℚ} (c : QuasiCharacter (SIdeleQuotient ℚ S))
    (hc : ∀ k : J₁(ℚ, S), c k.val = 1) : ∃ z, normChart(S, z) = c := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ S
  obtain ⟨z, hz⟩ := (existsUnique_complexPower (c.comp τ)).exists
  refine ⟨z, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have h := hc ⟨g / τ (m(ℚ, S) g), MonoidHom.mem_ker.mpr (by rw [map_div, hτ, div_self'])⟩
  change c (g / τ (m(ℚ, S) g)) = 1 at h
  rw [map_div, div_eq_one_iff_eq ((Group.isUnit _).map c).ne_zero] at h
  exact (one_mul _).trans ((hz _).symm.trans h.symm)

/-- On a bare norm chart the singleton Euler factor is the reciprocal of the
translation-difference multiplier. -/
private theorem sec3bP_single_euler {S : Finset Vℚ} (v : S) (z : ℂ) (hz : 0 < z.re) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (normChart(S, z))) =
      (1 - (v.val.asIdeal.absNorm : ℂ) ^ (-z))⁻¹ := by
  refine Eq.trans ?_ (finiteLocalEulerFactor_norm v.val hz)
  congr 1
  ext u
  obtain ⟨y, hy⟩ : ∃ y : SIdeleQuotient ℚ S, ∀ c, sLocalFiniteRestriction v c u = c y := ⟨_, fun _ ↦ rfl⟩
  have h := sLocalFiniteRestriction_norm v u
  rw [hy] at h ⊢
  change (1 : ℂ) * _ ^ (1 : ℂ) = _ at h
  rw [one_mul, Complex.cpow_one] at h
  change (1 : ℂ) * _ ^ z = (1 : ℂ) * _ ^ z
  rw [h]

/-- The Euler multiplier identifies PV on the trivial singleton-stage quotient
with the identity minus translation by any idele of norm 1/N(p). -/
private theorem sec3bP_single_pv {p : Vℚ} {T : Finset Vℚ} (hT : T = {p}) (u : (SAdeleRing ℚ T)ˣ)
    (hu : ((sIdeleNorm ℚ T u).val : ℝ) = (p.asIdeal.absNorm : ℝ)⁻¹)
    (f : B(ℚ, T)) :
    q(ℚ, T, 1) (sAdelePrincipalValue ℚ (Finset.Subset.refl T) f) =
      q(ℚ, T, 1) (f - schwartzBruhatUnitTranslate u f) := by
  let P := sAdelePrincipalValue ℚ (Finset.Subset.refl T)
  let k := P f - (f - schwartzBruhatUnitTranslate u f)
  apply (Submodule.Quotient.eq _).mpr
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (1 : PontryaginDual J₁(ℚ, T)) k).mpr
  intro c hc
  obtain ⟨s, hs⟩ := sec3bP_on_norm_chart c.val (fun h ↦ hc h)
  change sLocalIdelicZFunction k c.val = 0
  rw [← hs]
  let Z := fun z : ℂ ↦ sLocalIdelicZFunction k (normChart(T, z))
  have heq : Z = 0 := by
    apply eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic k 1) (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0
    intro z hz
    have hn : ∀ᶠ w : ℂ in 𝓝[≠] z, 0 < w.re := nhdsWithin_le_nhds
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
    have hzero : Z =ᶠ[𝓝[≠] z] 0 := by
      filter_upwards [hn, nhdsNE_le_codiscrete z (sLocalIdelicZFunction_principalValue T
        (Finset.Subset.refl T) f 1)] with w hw hP
      let c₀ := normChart(T, w)
      let d := (⟨c₀, sLocalOrderBound_positive (F := ℚ) (S := T) 1 hw⟩ :
        {c : QuasiCharacter (SIdeleQuotient ℚ T) // 0 ≤ sLocalIdelicOrderBound c})
      let A := sLocalIdelicMellin (F := ℚ) (S := T)
      have htr := sLocalIdelicMellin_unitTranslate u f d
      have hev : c₀ (QuotientGroup.mk u) = (p.asIdeal.absNorm : ℂ) ^ (-w) := by
        change (1 : ℂ) * (((sIdeleNorm ℚ T u).val : ℝ) : ℂ) ^ w = _
        rw [one_mul, hu, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_ne_zero.symm),
          ← Complex.cpow_neg, Complex.ofReal_natCast]
      have hprod : (∏ v : T, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c₀)
          else 1) = (1 - (p.asIdeal.absNorm : ℂ) ^ (-w))⁻¹ := by
        have : Subsingleton T := hT ▸ inferInstanceAs (Subsingleton (↥({p} : Finset Vℚ)))
        let v : T := ⟨p, hT ▸ Finset.mem_singleton_self _⟩
        rw [Finset.prod_eq_single v (fun b _ hb ↦ (hb (Subsingleton.elim _ _)).elim)
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left v.property]
        exact sec3bP_single_euler v w hw
      change (A (P f)).val d = (A f).val d / _ at hP
      rw [hprod, div_inv_eq_mul] at hP
      change (A (schwartzBruhatUnitTranslate u f)).val d = c₀ (QuotientGroup.mk u) * (A f).val d at htr
      rw [hev] at htr
      change (A (P f - (f - schwartzBruhatUnitTranslate u f))).val d = 0
      rw [map_sub, map_sub]
      change (A (P f)).val d - ((A f).val d - (A (schwartzBruhatUnitTranslate u f)).val d) = 0
      rw [hP, htr]
      ring
    exact (((sLocalIdelicZFunction_meromorphic k 1 (mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      analyticAt_const.meromorphicNFAt).mp hzero).eq_of_nhds
  exact congrFun heq s

open MeasureTheory in
/-- The Fourier transform of a translated test is zero wherever its dilated transform
is zero. This is the change of Haar measure in the Fourier dilation argument of Sec3b. -/
private theorem sec3bP_translate_fourier_zero {S : Finset Vℚ} (u : (SAdeleRing ℚ S)ˣ)
    (f : B(ℚ, S)) (y : SAdeleRing ℚ S)
    (hy : sAdeleSchwartzFourier f (Multiplicative.ofAdd (u.val * y)) = 0) :
    sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f) (Multiplicative.ofAdd y) = 0 := by
  let A := SAdeleRing ℚ S
  let : MeasurableSpace A := instMeasurableSpaceSAdeleRing ℚ S
  let : BorelSpace A := sAdeleRing_borelSpace
  let (v : S) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let : LocallyCompactSpace A := inferInstanceAs (LocallyCompactSpace (SAdeleRing ℚ S))
  let : T2Space A := inferInstanceAs (T2Space
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
  let (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ) := borel _
  let (w : InfinitePlace ℚ) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion ℚ) := ⟨rfl⟩
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace ℚ) : (infiniteLocalAdditiveTamagawaMeasure ℚ w).IsAddHaarMeasure := by
    have hw : w.IsReal := (Subsingleton.elim w Rat.infinitePlace) ▸ Rat.isReal_infinitePlace
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toAddEquiv.isAddHaarMeasure_map
      volume (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).continuous
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure ℚ v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar ℚ v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure ℚ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure ℚ v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let μ : Measure A := sAdditiveTamagawaMeasure ℚ S
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let : SecondCountableTopology A := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : S) → v.val.adicCompletion ℚ)))
  let k (x : A) := f (Multiplicative.ofAdd x) * star (sAdeleStandardCharacter ℚ S (x * (u.val * y)) : ℂ)
  change ∫ x, k x ∂μ = 0 at hy
  have h : ∫ x : A, k (u⁻¹ • x) ∂μ = 0 := by
    refine (integral_domSMul (μ := μ) (DomMulAct.mk u) k).symm.trans ?_
    rw [Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk u • μ) μ,
      integral_smul_nnreal_measure, hy, smul_zero]
  refine Eq.trans ?_ h
  change (∫ x : A, f (Multiplicative.ofAdd (u⁻¹.val * x)) *
    star (sAdeleStandardCharacter ℚ S (x * y) : ℂ) ∂μ) = _
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  change _ * star (sAdeleStandardCharacter ℚ S (x * y) : ℂ) =
    _ * star (sAdeleStandardCharacter ℚ S ((u⁻¹.val * x) * (u.val * y)) : ℂ)
  rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  rfl

local notation "radialAt(" S ", " t ")" =>
  Units.map (adeleProjection ℚ S).toMonoidHom (canonicalIdeleNormSection ℚ t)

/-- Dilation along the archimedean norm section commutes with integer insertion. -/
private theorem sec3bP_radial_insert {S T : Finset Vℚ} (hST : S ⊆ T) (t : ℝ≥0ˣ) (f : B(ℚ, S)) :
    schwartzBruhatUnitTranslate (radialAt(T, t)) (sAdeleSchwartzTransition ℚ hST f) =
      sAdeleSchwartzTransition ℚ hST (schwartzBruhatUnitTranslate (radialAt(S, t)) f) := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate _ _ (Multiplicative.ofAdd x.toAdd) =
    sAdeleSchwartzTransition ℚ hST _ (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply, sAdeleSchwartzTransition_apply,
    sAdeleSchwartzTransition_apply]
  have hfin (v : T) : (radialAt(T, t))⁻¹.val.2 v = 1 := by
    change (canonicalIdeleNormSection ℚ t)⁻¹.val.2 v.val = 1
    rw [← map_inv]
    exact congrArg (fun b ↦ b v.val) (canonicalIdeleNormSection_finite ℚ t⁻¹)
  have he (v : T) : ((radialAt(T, t))⁻¹.val * x.toAdd).2 v = x.toAdd.2 v := by
    change (radialAt(T, t))⁻¹.val.2 v * _ = _
    rw [hfin, one_mul]
  have hc : (∀ w : T, w.val ∉ S → ((radialAt(T, t))⁻¹.val * x.toAdd).2 w ∈ w.val.adicCompletionIntegers ℚ) ↔
      ∀ w : T, w.val ∉ S → x.toAdd.2 w ∈ w.val.adicCompletionIntegers ℚ := by simp only [he]
  rw [if_congr hc rfl rfl]
  split_ifs
  · rw [schwartzBruhatUnitTranslate_apply]
    rfl
  · rfl

/-- On the embedded old stage the singleton principal value is the difference
with the radial translate. The radial section has trivial finite coordinates. -/
private theorem sec3bP_insert_pv_diff {S T : Finset Vℚ} (hST : S ⊆ T) (p : Vℚ)
    (hT : T = {p}) (hR : T \ S = T) (t : ℝ≥0ˣ)
    (ht : ((sIdeleNorm ℚ T (radialAt(T, t))).val : ℝ) = (p.asIdeal.absNorm : ℝ)⁻¹)
    (E : Θ(ℚ, S, 1) →ₗ[ℂ] Θ(ℚ, T, 1))
    (he : ∀ f : B(ℚ, S), E (q(ℚ, S, 1) f) = q(ℚ, T, 1)
      (unitPV(ℚ, S, T) (sAdeleSchwartzTransition ℚ hST f)))
    (f : B(ℚ, S)) :
    sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl T) (1 : PontryaginDual J₁(ℚ, T))
      (E (q(ℚ, S, 1) f)) = E (q(ℚ, S, 1) (f - schwartzBruhatUnitTranslate (radialAt(S, t)) f)) := by
  let P := sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl T) (1 : PontryaginDual J₁(ℚ, T))
  let ins := sAdeleSchwartzTransition ℚ hST
  have he' (k : B(ℚ, S)) : E (q(ℚ, S, 1) k) = P (q(ℚ, T, 1) (ins k)) := by
    change E (q(ℚ, S, 1) k) = q(ℚ, T, 1) (sAdelePrincipalValue ℚ (Finset.Subset.refl T) (ins k))
    simpa only [hR] using he k
  let f' := schwartzBruhatUnitTranslate (radialAt(S, t)) f
  have hdiff : P (q(ℚ, T, 1) (ins f)) = q(ℚ, T, 1) (ins (f - f')) := by
    refine (sec3bP_single_pv hT (radialAt(T, t)) ht (ins f)).trans ?_
    apply congrArg (q(ℚ, T, 1))
    exact (congrArg (fun k ↦ ins f - k) (sec3bP_radial_insert hST t f)).trans (map_sub ins f f').symm
  exact (congrArg P (he' f)).trans ((congrArg P hdiff).trans (he' (f - f')).symm)

/-- The translated Fourier theta vanishes if the entire dilated norm fibre misses the support. -/
private theorem sec3bP_dilated_theta_zero {S : Finset Vℚ} (u : (SAdeleRing ℚ S)ˣ)
    (f : B(ℚ, S)) (g : SIdeleQuotient ℚ S)
    (hshell : ∀ x ∈ tsupport (sAdeleSchwartzFourier f).val, 1/2 < prodNorm(S, x.toAdd))
    (hsmall : ((sIdeleNorm ℚ S u).val : ℝ) * ((m(ℚ, S) g).val : ℝ) ≤ 1/2) :
    sLocalHomogeneousAdelicThetaLinearMap ℚ S 1
      (sAdeleSchwartzFourier (schwartzBruhatUnitTranslate u f)) g = 0 := by
  apply sec3bP_theta_zero
  intro a ha
  apply sec3bP_translate_fourier_zero u f a.val
  apply image_eq_zero_of_notMem_tsupport
  intro hsup
  have hlo := hshell _ hsup
  change 1/2 < prodNorm(S, (u * a).val) at hlo
  rw [sec3bP_prodNorm_unit, map_mul, Units.val_mul, NNReal.coe_mul, ha] at hlo
  exact hsmall.not_gt hlo

/-- Paper: Definition 7.3.3.3(1)–(2), p. 359.
Over ℚ start with no finite places and add one prime of residue size N > 4.
Take the product cutoff Y = 3. On the trivial component, principal value acts
as the identity minus translation by an idele of norm 1/N. The translated
Fourier theta vanishes on [1, 2], where the original test has a nonzero Fourier
theta value. The printed target cutoff 3/N is below 1. -/
theorem Printed.sLocalPWOrbitalQuotients_defined_false :
    ¬ Printed.sLocalPWOrbitalQuotients_defined := by
  intro h
  let S : Finset Vℚ := ∅
  obtain ⟨p, -, hp⟩ := sec3bP_large_prime S 4
  let T : Finset Vℚ := {p}
  let N : ℝ := p.asIdeal.absNorm
  have hN : 0 < N := lt_trans (by norm_num : (0 : ℝ) < 4) hp
  have hST : S ⊆ T := Finset.empty_subset _
  have hPT : sLocalPrimaryPlaces (F := ℚ) T p = T := by
    ext v
    rw [mem_sLocalPrimaryPlaces]
    refine and_iff_left_of_imp (fun hv ↦ ?_)
    rw [Finset.mem_singleton.mp hv]
    apply HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) p.asIdeal = p.asIdeal
    rw [Algebra.algebraMap_self, Ideal.comap_id]
  have hn : (sLocalPrimaryPlaces (F := ℚ) T p).Nonempty := by
    rw [hPT]
    exact Finset.singleton_nonempty _
  have hsat : IsSaturatedPlaceSet (F := ℚ) S := fun _ _ hv ↦ (Finset.notMem_empty _ hv).elim
  have hcont := (h ℚ S T T (by simp [S]) hsat (Finset.disjoint_empty_left _) (sec3bP_saturated p)
    sec3bP_pic p 1 (sec3bP_one_unramified S) 1 3 one_pos (by norm_num) hST 1
    (sec3bP_one_local T _).symm hn (sLocalPrimaryPlaces_subset T p)).2
  let P := sLocalHomogeneousThetaPrincipalValue (F := ℚ) (Finset.Subset.refl T) (1 : PontryaginDual J₁(ℚ, T))
  have hsize : size(sLocalPrimaryPlaces (F := ℚ) T p) = N := by rw [hPT]; simp [T, N]
  have hPV : sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := ℚ) T p)
      (1 : PontryaginDual J₁(ℚ, T)) = P := by
    unfold P
    congr 1
  rw [hPV, hsize] at hcont
  obtain ⟨E, hE, he⟩ := sec3bP_unit_embedding hST
  obtain ⟨_, _, htest⟩ := sec3bP_shell_test S
  obtain ⟨M, hM⟩ := sec3bP_unit_moment hST ⟨p, by simp [T, S]⟩
  obtain ⟨f, hm, hc, -, hshell, g, hg, hne⟩ := htest M
  have hband : tsupport (sAdeleSchwartzFourier f).val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S 3 :=
    fun x hx ↦ (hshell x hx).2.le
  have hsrc := sec3bP_unitLevel_mem hST _ f hc hband (hM f hm)
  rw [← he] at hsrc
  have himage := hcont (Submodule.mem_map_of_mem (f := P) hsrc)
  -- The second principal value acts, before the common embedding, as a dilation difference.
  let t : ℝ≥0ˣ := Units.mk0 ⟨N⁻¹, inv_nonneg.mpr hN.le⟩
    (fun h ↦ (inv_ne_zero hN.ne') (congrArg Subtype.val h))
  have ht (U : Finset Vℚ) : ((sIdeleNorm ℚ U (radialAt(U, t))).val : ℝ) = N⁻¹ :=
    congrArg (fun z : ℝ≥0ˣ ↦ (z.val : ℝ)) (sIdeleNorm_project_canonicalSection ℚ U t)
  let f' := schwartzBruhatUnitTranslate (radialAt(S, t)) f
  have heq : P (E (q(ℚ, S, 1) f)) = E (q(ℚ, S, 1) (f - f')) :=
    sec3bP_insert_pv_diff hST p rfl Finset.sdiff_empty t (ht T) E he f
  rw [heq] at himage
  have hz := sec3bP_unitLevel_bound hST E hE he (f - f') himage g
    (lt_of_lt_of_le ((div_lt_one hN).mpr (by change (3 : ℝ) < p.asIdeal.absNorm; linarith only [hp])) hg.1)
  have hshift : sLocalHomogeneousAdelicThetaLinearMap ℚ S 1 (sAdeleSchwartzFourier f') g = 0 := by
    apply sec3bP_dilated_theta_zero _ f g (fun x hx ↦ (hshell x hx).1)
    rw [ht]
    apply (mul_le_mul_of_nonneg_left hg.2 (inv_nonneg.mpr hN.le)).trans
    rw [← div_eq_inv_mul, div_le_iff₀ hN]
    dsimp only [N]
    linarith only [hp]
  obtain ⟨L, hL⟩ := sec3bP_fourierEval S g
  rw [← hL (f - f'), map_sub, map_sub, hL, hL, hshift, sub_zero] at hz
  exact hne hz

local notation "Rₚ(" F ", " T ", " p ", " χ ")" =>
  sLocalPrimaryOrbitalSubmodule (F := F) (S := T) p χ
local notation "Iₚ(" F ", " T ", " p ", " χ ")" =>
  SLocalOrbitalIndex (F := F) (S := T) (primary(F, T, p)) χ

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
The restricted dual basis and the lifts of its ambient biorthogonals share this enumeration. -/
def Printed.HasPWOrbitalBases {H : Type*} [AddCommGroup H] [Module ℂ H]
    [TopologicalSpace H] [IsTopologicalAddGroup H] [ContinuousSMul ℂ H]
    (R W : Submodule ℂ H) (K : Submodule ℂ W)
    (L : ℕ → StrongDual ℂ H) : Prop :=
  ∃ (e : ℕ → (H ⧸ R)) (d : ℕ → StrongDual ℂ (H ⧸ R))
    (eW : ℕ → (W ⧸ K)) (dW : ℕ → StrongDual ℂ (W ⧸ K))
    (ev : ℕ → StrongDual ℂ (StrongDual ℂ (W ⧸ K))),
    (∀ n (x : H), d n (R.mkQ x) = L n x) ∧ IsSchauderBasis e d ∧
    (∀ n (x : W), dW n (K.mkQ x) = L n x.val) ∧
    (∀ n, ∃ x : W, K.mkQ x = eW n ∧ R.mkQ x.val = e n) ∧
    (∀ n ℓ, ev n ℓ = ℓ (eW n)) ∧
    IsSchauderBasis dW ev ∧ SchauderBasis.IsUnconditional dW ev ∧
    IsSchauderBasis eW dW ∧ SchauderBasis.IsAbsolute eW dW

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
For both printed quotient levels every enumeration of either restricted family gives an
unconditional strong-dual basis, and the ambient biorthogonals lift to an absolute basis.
The containment expresses existence of the quotients in (7.3.3.5)–(6). In (7.3.3.7)
the small-stage multiplicity counts contributing places in S, and the Laurent subscript
is the signed exponent of Definition 7.1.2.1. -/
def Printed.sLocalPWOrbital_bases : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S S₀ T : Finset (V(F))),
    T = S ∪ S₀ → Disjoint S S₀ → IsSaturatedPlaceSet (F := F) S₀ →
    Subsingleton (CommRing.Pic ((S : Set (V(F))).integer F)) →
    ∀ (p : Vℚ) (ω : PontryaginDual (ideleClassNorm F).ker)
      (hu : NormOneCharacterUnramifiedOutside ω S)
      (hST : S ⊆ T) (χ : PontryaginDual J₁(F, T)),
      χ = sLocalNormOneCharacter (F := F) T ω (hu.mono hST) →
      let P := primary(F, T, p)
      P.Nonempty → P ⊆ S₀ →
      let pv := sLocalHomogeneousThetaPrincipalValue (sLocalPrimaryPlaces_subset (F := F) T p) χ
      let D := zeroMoments(F, T)
      let H := Θ(F, T, χ)
      let R := Rₚ(F, T, p, χ)
      ∃ B > (0 : ℝ), ∀ (X Y : ℝ), B ≤ X → B ≤ Y → X ^ count(F, S) ≤ Y →
        ∀ (W U : Submodule ℂ H),
          ((W = unitLevel(F, S, T, hST, sLocalPWBox S (X / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWBox S X, D, χ)) ∨
           (W = unitLevel(F, S, T, hST, sLocalPWProductRegion S (Y / size(P)), D, χ) ∧
            U = unitLevel(F, S, T, hST, sLocalPWProductRegion S Y, D, χ))) →
          U.map pv ≤ W ∧
          let K := (U.map pv).comap W.subtype
          let mS := fun c ↦ (sLocalArchPolePlaces (F := F) (S := T) c).card +
            sLocalFinitePoleMultiplicity (F := F) (S := T) S c
          ∀ fourier : Bool, ∃ L : Iₚ(F, T, p, χ) → StrongDual ℂ H,
            (∀ (j : Iₚ(F, T, p, χ)) (f : B(F, T)), L j (q(F, T, χ) f) =
              if fourier then sLocalOrbitalFourierJet (F := F) (S := T) j (q(F, T, χ) f)
              else sLocalZLaurentCoeff (F := F) (S := T) f j.val.1
                ((mS j.val.1 : ℤ) - (j.val.2 : ℤ))) ∧
            ∀ σ : ℕ ≃ Iₚ(F, T, p, χ), Printed.HasPWOrbitalBases R W K (L ∘ σ)

section OrbitalBases

-- The measure comparison below is copied from `Ch12_TraceGeometric/Sec4.lean`
-- (`sLocalTrace_measure_density`, `sLocalTrace_integral_units`, `sLocalTrace_nonunits_null`),
-- and the archimedean Haar lemma from `AppA_AlgebraicNT/Sec3.lean`.

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "cS" => (∏ v ∈ S, (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1))

attribute [local instance] instMeasurableSpaceSAdeleRing

local instance sec3bP_msCompletion (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance sec3bP_msAdic (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel _

/-- The archimedean additive Tamagawa factors are additive Haar measures. -/
private theorem sec3bP_infAddHaar (v : InfinitePlace F) :
    (infiniteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by
  let : BorelSpace v.Completion := ⟨rfl⟩
  by_cases h : v.IsReal
  · rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left h]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map
      volume (InfinitePlace.Completion.isometryEquivRealOfIsReal h).symm.continuous
      (InfinitePlace.Completion.isometryEquivRealOfIsReal h).continuous
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_right h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).continuous

/-- The lower integral of a product of coordinate functions over a product measure on
`n` coordinates is the product of the lower integrals. -/
private theorem sec3bP_lintegral_fin {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succAbove _ 0]
      have hfun : (fun p ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm p i)) =
          fun p ↦ f 0 p.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (p.2 j) := by
        funext p
        rw [Fin.prod_univ_succAbove _ 0]
        exact congrArg₂ (· * ·) (congrArg (f 0) (Fin.insertNth_apply_same 0 p.1 p.2))
          (Finset.prod_congr rfl fun j _ ↦ congrArg _ (Fin.insertNth_apply_succAbove 0 p.1 p.2 j))
      rw [hfun, lintegral_prod_mul (f := f 0) (g := fun x : (j : Fin n) → E (Fin.succAbove 0 j) ↦
          ∏ j : Fin n, f (Fin.succAbove 0 j) (x j))
        (hf 0).aemeasurable (Finset.measurable_prod _ fun j _ ↦
          (hf (Fin.succAbove 0 j)).comp (measurable_pi_apply j)).aemeasurable,
        n_ih (fun j ↦ f (Fin.succAbove 0 j)) (fun j ↦ hf _)]

/-- The lower integral of a product of coordinate functions over a finite product measure
is the product of the lower integrals. -/
private theorem sec3bP_lintegral_pi {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact sec3bP_lintegral_fin (fun i ↦ f (e i)) (fun i ↦ hf (e i))

/-- A finite product of measures with densities is the product measure with the
product density. -/
private theorem sec3bP_pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    sec3bP_lintegral_pi f hf]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply _ (hs i)).symm

/-- The pushforward of multiplicative Tamagawa measure to the invertible locus has density
c_S divided by the product norm against additive measure restricted to that locus. -/
private theorem sec3bP_measure_density :
    (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((νₛ).restrict (range (Units.val : Iₛ → Aₛ))).withDensity
        (fun z ↦ ENNReal.ofReal (cS / modS(z))) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    sec3bP_infAddHaar w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let ρI (w : InfinitePlace F) (x : w.Completion) : ℝ≥0∞ := (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹
  let c (v : S) : ℝ≥0∞ := ↑v.val.asIdeal.absNorm / (↑v.val.asIdeal.absNorm - 1)
  let ρS (v : S) (x : v.val.adicCompletion F) : ℝ≥0∞ := c v * (↑‖x‖₊ : ℝ≥0∞)⁻¹
  have hq (v : S) : 1 < v.val.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v.val
  have hc (v : S) : c v ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt (by exact_mod_cast hq v)).ne'
  have hρI (w : InfinitePlace F) : Measurable (ρI w) :=
    ((measurable_nnNorm.pow_const _).coe_nnreal_ennreal).inv
  have hρS (v : S) : Measurable (ρS v) :=
    measurable_const.mul measurable_nnNorm.coe_nnreal_ennreal.inv
  have hRI (w : InfinitePlace F) : MeasurableSet (range (Units.val : w.Completionˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).isOpen_range.measurableSet
  have hRS (v : S) : MeasurableSet (range (Units.val : (v.val.adicCompletion F)ˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).isOpen_range.measurableSet
  have hlocI (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val =
      ((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity (ρI w) := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding.map_comap,
      restrict_withDensity (hRI w)]
  have hlocS (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val =
      ((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, Measure.map_smul,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).measurableEmbedding.map_comap,
      restrict_withDensity (hRS v), ← withDensity_smul' _ _ (hc v)]
    · rfl
    · exact Units.continuous_val.measurable.aemeasurable
  have hsfI (w : InfinitePlace F) : SigmaFinite
      (((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity
        (ρI w)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRI w)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 (pow_ne_zero _
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have hsfS (v : S) : SigmaFinite
      (((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRS v)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.mul_ne_top (hc v) (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have (w : InfinitePlace F) :
      SigmaFinite ((infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val) := by
    rw [hlocI w]; exact hsfI w
  have (v : S) :
      SigmaFinite ((finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val) := by
    rw [hlocS v]; exact hsfS v
  have hAI : Measurable (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      (f w).val) :=
    measurable_pi_iff.2 fun w ↦ Units.continuous_val.measurable.comp (measurable_pi_apply w)
  have hAS : Measurable (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) :=
    measurable_pi_iff.2 fun v ↦ Units.continuous_val.measurable.comp (measurable_pi_apply v)
  have hmapL : (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
        (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val)).prod
      ((Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
        (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val)) := by
    rw [Measure.map_prod_map _ _ hAI hAS]
    unfold sMultiplicativeTamagawaMeasure
    rw [Measure.map_map]
    · rfl
    · exact fun s hs ↦ ⟨s, hs, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hAI.prodMap hAS) ht
  have hrange : range (Units.val : Iₛ → Aₛ) =
      (univ.pi fun w : InfinitePlace F ↦ range (Units.val : w.Completionˣ → w.Completion)) ×ˢ
        (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F)) := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ_pi]
    change IsUnit z ↔ (∀ w, IsUnit (z.1 w)) ∧ ∀ v, IsUnit (z.2 v)
    rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  have hbox : MeasurableSet ((univ.pi fun w : InfinitePlace F ↦
      range (Units.val : w.Completionˣ → w.Completion)) ×ˢ (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F))) :=
    (MeasurableSet.univ_pi hRI).prod (MeasurableSet.univ_pi hRS)
  have hpiI : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
      (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val) =
      Measure.pi fun w ↦ (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val :=
    Measure.pi_map_pi fun w ↦ Units.continuous_val.measurable.aemeasurable
  have hpiS : (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
      (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) =
      Measure.pi fun v : S ↦ (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val :=
    Measure.pi_map_pi fun v ↦ Units.continuous_val.measurable.aemeasurable
  rw [hmapL, hpiI, hpiS]
  simp_rw [hlocI, hlocS]
  rw [sec3bP_pi_withDensity _ ρI hρI,
    sec3bP_pi_withDensity _ ρS hρS,
    prod_withDensity (f := fun x : (w : InfinitePlace F) → w.Completion ↦ ∏ w, ρI w (x w))
      (g := fun x : (v : S) → v.val.adicCompletion F ↦ ∏ v, ρS v (x v))
      (Finset.measurable_prod _ fun w _ ↦ (hρI w).comp (measurable_pi_apply w))
      (Finset.measurable_prod _ fun v _ ↦ (hρS v).comp (measurable_pi_apply v)),
    ← Measure.restrict_pi_pi, ← Measure.restrict_pi_pi, Measure.prod_restrict, hrange]
  refine withDensity_congr_ae ((ae_restrict_iff' hbox).2 (ae_of_all _ fun z hz ↦ ?_))
  have hz1 (w : InfinitePlace F) : 0 < ‖z.1 w‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.1) w
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hz2 (v : S) : 0 < ‖z.2 v‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.2) v
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hq' (v : S) : (1 : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast hq v
  have e1 (w : InfinitePlace F) :
      ρI w (z.1 w) = ENNReal.ofReal ((‖z.1 w‖ ^ w.mult)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (hz1 w) _),
      show ‖z.1 w‖ ^ w.mult = ((‖z.1 w‖₊ ^ w.mult : ℝ≥0) : ℝ) by simp,
      ENNReal.ofReal_coe_nnreal]
  have e2 (v : S) : ρS v (z.2 v) =
      ENNReal.ofReal ((v.val.asIdeal.absNorm : ℝ) / ((v.val.asIdeal.absNorm : ℝ) - 1)) *
        ENNReal.ofReal ‖z.2 v‖⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (hz2 v), ENNReal.ofReal_div_of_pos (sub_pos.2 (hq' v)),
      ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]
  simp only [e1, e2]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' _)).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ ↦ mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' v)).le) (inv_nonneg.2 (hz2 v).le)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  congr 1
  rw [← Finset.prod_coe_sort S, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- A normed field with a nonzero element of norm less than one has no isolated zero. -/
private theorem sec3bP_neBot_of_norm_lt_one {K : Type*} [NormedField K] (a : K)
    (ha0 : a ≠ 0) (ha : ‖a‖ < 1) : (𝓝[≠] (0 : K)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_of_tendsto
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha) (Eventually.of_forall fun n ↦ pow_ne_zero n ha0))

/-- Zero is not isolated in a finite completion: the powers of a uniformizer tend to it. -/
private theorem sec3bP_finite_neBot (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact sec3bP_neBot_of_norm_lt_one (π : v.adicCompletion F) hπ.ne_zero
    (Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one)

/-- Zero is not isolated in an infinite completion: the powers of one half tend to it. -/
private theorem sec3bP_infinite_neBot (w : InfinitePlace F) :
    (𝓝[≠] (0 : w.Completion)).NeBot := by
  let a : w.Completion := ((WithAbs.equiv w.1).symm (2⁻¹ : F) : WithAbs w.1)
  have h2 : w (2 : F) = 2 := by simpa using w.map_natCast 2
  have hval : ‖a‖ = 2⁻¹ := by
    rw [InfinitePlace.Completion.norm_coe, RingEquiv.apply_symm_apply, map_inv₀, h2]
  refine sec3bP_neBot_of_norm_lt_one a (fun h ↦ ?_) (by rw [hval]; norm_num)
  rw [h, norm_zero] at hval
  norm_num at hval

/-- The S-adeles with a zero coordinate form a null set for additive Tamagawa measure. -/
private theorem sec3bP_nonunits_null :
    νₛ (range (Units.val : Iₛ → Aₛ))ᶜ = 0 := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    sec3bP_infAddHaar w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let (w : InfinitePlace F) : (𝓝[≠] (0 : w.Completion)).NeBot := sec3bP_infinite_neBot w
  let (v : S) : (𝓝[≠] (0 : v.val.adicCompletion F)).NeBot := sec3bP_finite_neBot v.val
  have hw (w : InfinitePlace F) : infiniteLocalAdditiveTamagawaMeasure F w {0} = 0 :=
    measure_singleton 0
  have hv (v : S) : finiteLocalAdditiveTamagawaMeasure F v.val {0} = 0 :=
    measure_singleton 0
  have hsub : (range (Units.val : Iₛ → Aₛ))ᶜ ⊆
      (⋃ w : InfinitePlace F, Prod.fst ⁻¹' (Function.eval w ⁻¹' {0})) ∪
        ⋃ v : S, Prod.snd ⁻¹' (Function.eval v ⁻¹' {0}) := by
    intro a ha
    by_contra h
    simp only [mem_union, mem_iUnion, not_or, not_exists, mem_preimage, Function.eval,
      mem_singleton_iff] at h
    have hu : IsUnit a := Prod.isUnit_iff.mpr
      ⟨Pi.isUnit_iff.mpr fun w ↦ isUnit_iff_ne_zero.mpr (h.1 w),
        Pi.isUnit_iff.mpr fun v ↦ isUnit_iff_ne_zero.mpr (h.2 v)⟩
    exact ha ⟨hu.unit, rfl⟩
  refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun w ↦ ?_)
    (measure_iUnion_null fun v ↦ ?_))
  · rw [← prod_univ]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null _ (hw w), zero_mul]
  · rw [← univ_prod]
    change ((Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))) (_ ×ˢ _) = 0
    rw [Measure.prod_prod, Measure.pi_eval_preimage_null
      (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val) (i := v) (hv v), mul_zero]

/-- The multiplicative integral of the norm times a function is c_S times its additive integral. -/
private theorem sec3bP_integral_units (a : Aₛ → ℂ) :
    (∫ t : Iₛ, (normS(t) : ℂ) * a t.val ∂μₛ) = (cS : ℂ) * ∫ t, a t ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  have hfull : ∀ᵐ u ∂νₛ, u ∈ range (Units.val : Iₛ → Aₛ) :=
    measure_eq_zero_iff_ae_notMem.mp sec3bP_nonunits_null |>.mono fun _ h ↦ not_not.mp h
  have hres : (νₛ).restrict (range (Units.val : Iₛ → Aₛ)) = νₛ :=
    Measure.restrict_eq_self_of_ae_mem hfull
  let n (t : Aₛ) := modS(t)
  have hn (t : Iₛ) : normS(t) = n t.val := by simp [n, sIdeleNorm, Units.coe_prod]
  have hm : Continuous n := by
    unfold n
    exact (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let c := cS
  have hc : 0 ≤ c := by
    apply Finset.prod_nonneg
    intro v _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hv.le)
  let d (t : Aₛ) := ENNReal.ofReal (c / n t)
  have hd : Measurable d := (measurable_const.div hm.measurable).ennreal_ofReal
  simp_rw [hn]
  rw [← ho.measurableEmbedding.integral_map (μ := μₛ) (fun t ↦ (n t : ℂ) * a t),
    sec3bP_measure_density]
  change (∫ t, (n t : ℂ) * a t ∂((νₛ).restrict _).withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  conv_rhs => rw [← hres]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply (ae_restrict_iff' ho.isOpen_range.measurableSet).2
  apply ae_of_all
  rintro _ ⟨t, rfl⟩
  have hpos : 0 < n t.val := (hn t) ▸ NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S t))
  simp only [d, ENNReal.toReal_ofReal (div_nonneg hc hpos.le), Complex.real_smul,
    Complex.ofReal_div]
  have hn0 : ((n t.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  push_cast [c]
  field_simp

local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

/-- The continued zeta function at the norm character is c_S times the additive integral. -/
private theorem sec3bP_zeta_norm (g : SchwartzBruhat (Multiplicative Aₛ)) :
    sLocalIdelicZFunction g (dualₛ (twistₛ 1 0)) =
      (cS : ℂ) * ∫ x, g (Multiplicative.ofAdd x) ∂νₛ := by
  have hval (x : Jₛ) : dualₛ (twistₛ 1 0) x = (((mₛ x : ℝ≥0) : ℝ) : ℂ) := by
    simp [dualQuasiCharacter, quasiCharacterNormTwist]
    change _ * (1 : ℂ)⁻¹ = _
    rw [inv_one, mul_one]
    rfl
  have hc : dualₛ (twistₛ 1 0) = twistₛ ((circleToComplex).comp 1) 1 := by
    ext x
    rw [hval]
    simp [quasiCharacterNormTwist]
    rfl
  rw [sLocalIdelicZFunction_eq_integral g ⟨1, 1, by simp, hc⟩, sLocalIdelicZetaIntegral,
    ← sec3bP_integral_units]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  change g _ * dualₛ (twistₛ 1 0) (QuotientGroup.mk t) = _
  rw [hval, sIdeleQuotientNorm_mk, mul_comm]


/-- Every subring of the rationals is a principal ideal ring. -/
private theorem sec3bP_subring_pid (R : Subring ℚ) : IsPrincipalIdealRing R := by
  refine ⟨fun I ↦ ?_⟩
  let J : Ideal ℤ := I.comap (Int.castRingHom R)
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal J).principal
  refine ⟨⟨(g : R), ?_⟩⟩
  have hgJ : g ∈ J := hg ▸ Submodule.mem_span_singleton_self g
  apply le_antisymm
  · intro x hx
    let q : ℚ := x
    have hcop : Int.gcd q.num q.den = 1 := q.reduced
    have hb := Int.gcd_eq_gcd_ab q.num q.den
    rw [hcop] at hb
    -- the inverse denominator lies in the subring
    have hinv : (q.den : ℚ)⁻¹ ∈ R := by
      have : (q.den : ℚ)⁻¹ = q * (Int.gcdA q.num q.den : ℚ) + (Int.gcdB q.num q.den : ℚ) := by
        have hd : (q.den : ℚ) ≠ 0 := by positivity
        have h1 : ((1 : ℤ) : ℚ) = (q.num : ℚ) * Int.gcdA q.num q.den + (q.den : ℚ) * Int.gcdB q.num q.den := by
          exact_mod_cast hb
        push_cast at h1
        generalize Int.gcdA q.num q.den = A at h1 ⊢
        generalize Int.gcdB q.num q.den = B at h1 ⊢
        conv_rhs => rw [← Rat.num_div_den q]
        field_simp
        linear_combination h1
      rw [this]
      exact R.add_mem (R.mul_mem x.property (intCast_mem R _)) (intCast_mem R _)
    have hnum : (q.num : R) ∈ I := by
      have : (q.num : R) = (q.den : R) * x := by
        apply Subtype.ext
        push_cast
        exact (Rat.mul_den_eq_num q).symm.trans (mul_comm _ _)
      rw [this]
      exact I.mul_mem_left _ hx
    have hnumJ : q.num ∈ J := hnum
    rw [hg, Ideal.mem_span_singleton'] at hnumJ
    obtain ⟨k, hk⟩ := hnumJ
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
    refine ⟨(k : R) * ⟨_, hinv⟩, Subtype.ext ?_⟩
    push_cast
    change (k : ℚ) * (q.den : ℚ)⁻¹ * g = q
    rw [mul_right_comm, ← Int.cast_mul, hk, ← div_eq_mul_inv]
    exact Rat.num_div_den q
  · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact hgJ

end OrbitalBases

/-- Paper: Theorem 7.3.3.4(1)–(2), pp. 360–361.
Over the rationals with one added prime and trivial character, the index contains the
order-zero jet at the trivial center. It evaluates the Fourier zeta integral at norm
power one, a nonzero multiple of evaluation at zero by Fourier inversion. Its restriction
vanishes on each zero-moment level, contradicting the unit biorthogonal pairing.
The same obstruction persists with the proof's intersection denominator. -/
theorem Printed.sLocalPWOrbital_bases_false : ¬ Printed.sLocalPWOrbital_bases := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let p : Vℚ := ⟨m, hm.isPrime, NeZero.ne m⟩
  let S : Finset Vℚ := ∅
  let T : Finset Vℚ := {p}
  have hsub : S ⊆ T := Finset.empty_subset _
  have hpT : p ∈ T \ S := by simp [S, T]
  have hu : NormOneCharacterUnramifiedOutside (1 : PontryaginDual (ideleClassNorm ℚ).ker) S :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have hχ : (1 : PontryaginDual J₁(ℚ, T)) =
      sLocalNormOneCharacter (F := ℚ) T 1 (hu.mono hsub) := by
    ext y
    have := sLocalNormOneCharacter_eq_sIdeleRestriction (F := ℚ) (S := T) 1
      ⟨1, (mem_unramifiedOutside_iff ℚ T 1).mpr (fun _ _ _ ↦ rfl)⟩ (fun _ ↦ rfl) y
    rw [this]
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.val
    rw [← hg, sIdeleRestriction_mk]
    rfl
  have hunder : p.under (𝓞 ℚ) = p := by
    apply HeightOneSpectrum.ext
    change Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) p.asIdeal = p.asIdeal
    rw [Algebra.algebraMap_self, Ideal.comap_id]
  have hP : sLocalPrimaryPlaces (F := ℚ) T p = T := by
    ext v
    rw [mem_sLocalPrimaryPlaces]
    constructor
    · exact fun hv ↦ hv.1
    · intro hv
      refine ⟨hv, ?_⟩
      rw [Finset.mem_singleton.mp hv]
      exact hunder
  have hPne : (sLocalPrimaryPlaces (F := ℚ) T p).Nonempty := by
    rw [hP]; exact Finset.singleton_nonempty p
  have hPsub : sLocalPrimaryPlaces (F := ℚ) T p ⊆ T := sLocalPrimaryPlaces_subset T p
  obtain ⟨B, -, hall⟩ := h ℚ S T T (by simp [S, T]) (Finset.disjoint_empty_left _)
    (sec3bP_saturated p) sec3bP_pic p 1 hu hsub 1 hχ hPne hPsub
  have hn : Fintype.card (InfinitePlace ℚ) + Finset.card S ≠ 0 := by
    have : Nonempty (InfinitePlace ℚ) := ⟨Rat.infinitePlace⟩
    have := Fintype.card_pos (α := InfinitePlace ℚ)
    omega
  let X := max B 1
  have hBX : B ≤ X := le_max_left _ _
  have hBY : B ≤ X ^ (Fintype.card (InfinitePlace ℚ) + Finset.card S) :=
    hBX.trans (le_self_pow₀ (le_max_right _ _) hn)
  obtain ⟨-, hrest⟩ := hall X _ hBX hBY le_rfl _ _ (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨L, hL, hbases⟩ := hrest true
  obtain ⟨j₀, hj₀⟩ := (sLocalOrbitalIndex_one_iff (F := ℚ) (S := T) hPsub 0).mpr
    (by rw [hP]; simp [T])
  have hPic : Subsingleton (CommRing.Pic (((T : Set Vℚ)).integer ℚ)) := by
    let A := (((T : Set Vℚ)).integer ℚ)
    let := sec3bP_subring_pid A.toSubring
    let i : A.toSubring ≃+* A := RingEquiv.refl _
    let := IsPrincipalIdealRing.of_surjective i.toRingHom i.surjective
    infer_instance
  obtain ⟨σ⟩ := (sLocalOrbitalIndex_enumerable_or_empty (F := ℚ) (S := T) p 1
    (sec3bP_saturated p) hPne hPic).resolve_right (fun h ↦ h.1.false j₀)
  obtain ⟨e, d, eW, dW, ev, -, -, hdW, hlift, -, -, -, hbas, -⟩ := hbases σ
  let k := σ.symm j₀
  obtain ⟨x, hxK, -⟩ := hlift k
  have h1 : dW k (eW k) = 1 := (hbas.1 k k).trans (if_pos rfl)
  have h2 : dW k (eW k) = L j₀ x.val := (congrArg (dW k) hxK).symm.trans
    ((hdW k x).trans (congrArg (fun j ↦ L j x.val) (σ.apply_symm_apply j₀)))
  have hx0 : x.val ∈ LinearMap.ker (L j₀).toLinearMap := by
    refine Submodule.topologicalClosure_minimal _ ?_ (L j₀).isClosed_ker x.property
    rintro _ ⟨f, ⟨hfE, -⟩, rfl⟩
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.mp hfE
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hL j₀, if_pos rfl]
    erw [sLocalOrbitalFourierJet_mk]
    rw [hj₀]
    simp only [iteratedDeriv_zero]
    rw [sec3bP_zeta_norm, ← sAdeleSchwartzFourier_apply_zero, sLocal_fourier_inversion, neg_zero,
      sec3bP_sPV_zero Finset.sdiff_subset hpT 0 rfl t, mul_zero]
  exact one_ne_zero (h1.symm.trans (h2.trans (LinearMap.mem_ker.mp hx0)))

local notation "lexLe(" e ", " a ", " b ")" =>
  ((∀ i, a (e i).val = b (e i).val) ∨
    ∃ i, a (e i).val < b (e i).val ∧ ∀ j < i, a (e j).val = b (e j).val)

section GammaAntitone

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Xg" => QuasiCharacter (SIdeleQuotient F S)
local notation "shiftg(" c ", " z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous c z
local notation "archg(" c ")" => sLocalArchPolePlaces (F := F) (S := S) c
local notation "Gg(" w ")" => (fun s : ℂ ↦ if (w : InfinitePlace F).IsReal then Complex.Gammaℝ s
  else Complex.Gammaℂ s / 2)

/-- A finite set of linearly independent functionals separates any one of them from the rest. -/
private theorem sec3bP_exists_dual_single {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Finite ι]
    (L : ι → E →ₗ[ℂ] ℂ) (hL : LinearIndependent ℂ L) (i₀ : ι) :
    ∃ x : E, L i₀ x ≠ 0 ∧ ∀ i, i ≠ i₀ → L i x = 0 := by
  by_contra h
  push Not at h
  have hle : (⨅ i : {i // i ≠ i₀}, LinearMap.ker (L i.val)) ≤ LinearMap.ker (L i₀) := by
    intro x hx
    rw [Submodule.mem_iInf] at hx
    by_contra hne
    obtain ⟨i, hi, hix⟩ := h x hne
    exact hix (hx ⟨i, hi⟩)
  have hmem := mem_span_of_iInf_ker_le_ker hle
  have hrange : Set.range (fun i : {i // i ≠ i₀} ↦ L i.val) = L '' {i | i ≠ i₀} := by
    ext φ
    simp
  rw [hrange] at hmem
  exact hL.notMem_span_image (s := {i | i ≠ i₀}) (by simp) hmem

private theorem sec3bP_twist_twist (c : Xg) (a z : ℂ) :
    shiftg(shiftg(c, a), z) = shiftg(c, z + a) := by
  ext1 g
  change c g * _ ^ a * _ ^ z = c g * _ ^ (z + a)
  rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr (sIdeleQuotientNorm F S g).ne_zero)), mul_assoc]

/-- Along the chart through the trivial character the archimedean Euler factors are
`Γℝ` at real places and `Γℂ / 2` at complex places. -/
private theorem sec3bP_archEuler (w : InfinitePlace F) (s : ℂ) :
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (shiftg((1 : Xg), s))) = Gg(w) s := by
  have hres (g : w.Completionˣ) :
      sLocalInfiniteRestriction w (shiftg((1 : Xg), s)) g =
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ s := by
    have h1 : shiftg((1 : Xg), s) = quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous
        ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
          (1 : PontryaginDual (SIdeleQuotient F S))) s := by
      ext1 x
      change (1 : ℂ) * _ = ((1 : Circle) : ℂ) * _
      rw [Circle.coe_one]
      rfl
    rw [h1]
    exact sLocalInfiniteRestriction_normTwist w s g
  by_cases hw : w.IsReal
  · let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
    have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (shiftg((1 : Xg), s))
        (Units.map e.toMonoidHom x) =
          (‖(x : ℝ)‖ : ℂ) ^ s * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (0 : Fin 2).val := by
      intro x
      have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero e) (x : ℝ)
      have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
          (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
        simp [InfinitePlace.mult, hw, hn]
      rw [hres, hm, Fin.val_zero, pow_zero, mul_one]
    have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
      (shiftg((1 : Xg), s)))).unique (realLocalEulerParameters w hw
        (sLocalInfiniteRestriction w (shiftg((1 : Xg), s)))).exists.choose_spec
      (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, ite_true, Fin.val_zero,
      Nat.cast_zero, add_zero]
  · have hwc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hwc).symm
    have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (shiftg((1 : Xg), s))
        (Units.map e.toMonoidHom x) =
          ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (0 : ℤ) := by
      intro x
      have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          hwc).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
      have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
          (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
        simp [InfinitePlace.mult, hw, hn]
      rw [hres, hm, zpow_zero, mul_one]
    have hq := (complexLocalEulerParameters w hwc (sLocalInfiniteRestriction w
      (shiftg((1 : Xg), s)))).unique (complexLocalEulerParameters w hwc
        (sLocalInfiniteRestriction w (shiftg((1 : Xg), s)))).exists.choose_spec
      (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, ite_false, Int.natAbs_zero,
      Nat.cast_zero, zero_div, add_zero]

private theorem sec3bP_mem_arch (a : ℂ) (w : InfinitePlace F) :
    w ∈ archg(shiftg((1 : Xg), a)) ↔ meromorphicOrderAt (fun z ↦ Gg(w) (z + a)) 0 < 0 := by
  simp only [sLocalArchPolePlaces, Finset.mem_filter, Finset.mem_univ, true_and]
  refine iff_of_eq (congrArg (· < 0) (congrArg (meromorphicOrderAt · 0) ?_))
  funext z
  rw [sec3bP_twist_twist, sec3bP_archEuler]

omit [NumberField F] in
private theorem sec3bP_G_inv (w : InfinitePlace F) : Differentiable ℂ (fun s ↦ (Gg(w) s)⁻¹) := by
  by_cases hw : w.IsReal
  · simpa only [hw, ite_true] using Complex.differentiable_Gammaℝ_inv
  · simp only [hw, ite_false, inv_div]
    exact Complex.differentiable_Gammaℂ_inv.const_mul 2

omit [NumberField F] in
private theorem sec3bP_G_one (w : InfinitePlace F) : Gg(w) 1 ≠ 0 := by
  by_cases hw : w.IsReal
  · simpa only [hw, ite_true] using Complex.Gammaℝ_ne_zero_of_re_pos (by simp)
  · simp only [hw, ite_false, Complex.Gammaℂ_def]
    refine div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_) two_ne_zero
    · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simp)).mpr
        (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · exact Complex.Gamma_ne_zero_of_re_pos (by simp)

omit [NumberField F] in
private theorem sec3bP_G_even (w : InfinitePlace F) (n : ℕ) : Gg(w) (-(2 * (n : ℂ))) = 0 := by
  by_cases hw : w.IsReal
  · simpa only [hw, ite_true] using Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, rfl⟩
  · simp only [hw, ite_false, Complex.Gammaℂ_def]
    have : Complex.Gamma (-(2 * (n : ℂ))) = 0 := by
      simpa using Complex.Gamma_neg_nat_eq_zero (2 * n)
    rw [this, mul_zero, zero_div]

/-- A zero of the entire reciprocal is a pole. -/
private theorem sec3bP_pole_of_zero {G : ℂ → ℂ} (hinv : Differentiable ℂ (fun s ↦ (G s)⁻¹))
    (a : ℂ) (ha : G a = 0) (h1 : G 1 ≠ 0) :
    meromorphicOrderAt (fun z ↦ G (z + a)) 0 < 0 := by
  let g : ℂ → ℂ := fun z ↦ (G (z + a))⁻¹
  have hg : AnalyticOnNhd ℂ g Set.univ := fun z _ ↦
    ((hinv.comp (differentiable_id.add_const a)).analyticAt z)
  have h1' : analyticOrderAt g (1 - a) ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (by simpa [g] using h1))]
    exact ENat.zero_ne_top
  have hnt : analyticOrderAt g 0 ≠ ⊤ :=
    hg.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _) h1'
  have hn0 : analyticOrderAt g 0 ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hg 0 (Set.mem_univ _), by simp [g, ha]⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnt
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [← hn, h]; rfl) hn0
    · exact h
  have hord : meromorphicOrderAt g 0 = (n : ℤ) := by
    rw [(hg 0 (Set.mem_univ _)).meromorphicOrderAt_eq, ← hn]
    rfl
  have hinvg : (fun z ↦ G (z + a)) = g⁻¹ := by
    funext z
    simp [g]
  rw [hinvg, meromorphicOrderAt_inv, hord]
  exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- A nonzero value of the entire reciprocal is a regular point. -/
private theorem sec3bP_reg_of_ne {G : ℂ → ℂ} (hinv : Differentiable ℂ (fun s ↦ (G s)⁻¹))
    (a : ℂ) (ha : G a ≠ 0) :
    ¬ meromorphicOrderAt (fun z ↦ G (z + a)) 0 < 0 := by
  have han : AnalyticAt ℂ (fun z ↦ ((G (z + a))⁻¹)⁻¹) 0 :=
    ((hinv.analyticAt _).comp (f := fun z : ℂ ↦ z + a) (by fun_prop)).inv
      (by simpa using ha)
  simp only [inv_inv] at han
  exact not_lt.mpr han.meromorphicOrderAt_nonneg

local notation "J₁g" => (sIdeleQuotientNorm F S).ker
local notation "cutg(" N ")" => sLocalGammaPoleCutoff (F := F) (S := S) (1 : PontryaginDual J₁g) N

/-- Every even nonpositive integer shift of the trivial character is a pole at every place. -/
private theorem sec3bP_even_pole (w : InfinitePlace F) (n : ℕ) :
    w ∈ archg(shiftg((1 : Xg), -(2 * (n : ℂ)))) := by
  rw [sec3bP_mem_arch]
  exact sec3bP_pole_of_zero (sec3bP_G_inv w) _ (sec3bP_G_even w n) (sec3bP_G_one w)

/-- At a real place, the poles along the trivial chart are at even nonpositive integers. -/
private theorem sec3bP_real_pole (w : InfinitePlace F) (hw : w.IsReal) (a : ℂ)
    (h : w ∈ archg(shiftg((1 : Xg), a))) : ∃ n : ℕ, a = -(2 * (n : ℂ)) := by
  rw [sec3bP_mem_arch] at h
  by_contra hn
  refine sec3bP_reg_of_ne (sec3bP_G_inv w) a ?_ h
  simpa only [hw, ite_true, Ne, Complex.Gammaℝ_eq_zero_iff] using hn

private theorem sec3bP_onComponent_shift (s : ℂ) :
    normOneRestriction (sIdeleQuotientNorm F S) (shiftg((1 : Xg), s)) =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual J₁g) := by
  ext x
  have hx : sIdeleQuotientNorm F S x.val = 1 := x.property
  change (1 : Xg) x.val * ((((sIdeleQuotientNorm F S x.val : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s =
    ((1 : Circle) : ℂ)
  rw [hx]
  simp

private theorem sec3bP_cut_mono {N N' : InfinitePlace F → ℕ} (hN : ∀ w, N w ≤ N' w) {c : Xg}
    (hc : c ∈ cutg(N)) : c ∈ cutg(N') := by
  obtain ⟨hc, w, hw, hcard⟩ := hc
  exact ⟨hc, w, hw, hcard.trans (by exact_mod_cast hN w)⟩

private theorem sec3bP_shift4 (t : ℝ) :
    shiftg(shiftg((1 : Xg), (-4 : ℂ)), (t : ℂ)) = shiftg((1 : Xg), (t : ℂ) + -4) :=
  sec3bP_twist_twist _ _ _

private theorem sec3bP_pair_sub (w : InfinitePlace F) :
    ({2, 4} : Set ℝ) ⊆ {t : ℝ | 0 < t ∧ w ∈ archg(shiftg(shiftg((1 : Xg), (-4 : ℂ)), (t : ℂ)))} := by
  rintro t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl
  · refine ⟨by norm_num, ?_⟩
    rw [sec3bP_shift4, show ((2 : ℝ) : ℂ) + -4 = -(2 * ((1 : ℕ) : ℂ)) by push_cast; ring]
    exact sec3bP_even_pole w 1
  · refine ⟨by norm_num, ?_⟩
    rw [sec3bP_shift4,
      show ((4 : ℝ) : ℂ) + -4 = -(2 * ((0 : ℕ) : ℂ)) by push_cast; ring]
    exact sec3bP_even_pole w 0

private theorem sec3bP_sub_pair (w : InfinitePlace F) (hw : w.IsReal) :
    {t : ℝ | 0 < t ∧ w ∈ archg(shiftg(shiftg((1 : Xg), (-4 : ℂ)), (t : ℂ)))} ⊆ ({2, 4} : Set ℝ) := by
  rintro t ⟨ht, hmem⟩
  rw [sec3bP_shift4] at hmem
  obtain ⟨n, hn⟩ := sec3bP_real_pole w hw _ hmem
  have hr : t + -4 = -(2 * (n : ℝ)) := by
    have := congrArg Complex.re hn
    simpa using this
  have hn2 : n < 2 := by
    by_contra h
    have : (2 : ℝ) ≤ n := by exact_mod_cast not_lt.mp h
    linarith
  interval_cases n
  · right; simp only [Set.mem_singleton_iff]; push_cast at hr; linarith
  · left; push_cast at hr; linarith

local notation "fullPVg" => (sLocalHomogeneousThetaPrincipalValue (F := F)
  (Finset.Subset.refl S) (1 : PontryaginDual J₁g)).range

private theorem sec3bP_mem_filt (N : InfinitePlace F → ℕ) (x : fullPVg) :
    x ∈ sLocalGammaFiltration (F := F) (S := S) (1 : PontryaginDual J₁g) N ↔
      ∀ j : {j : Xg × ℕ // normOneRestriction (sIdeleQuotientNorm F S) j.1 =
          (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (1 : PontryaginDual J₁g) ∧
          j.1 ∈ cutg(N) ∧ 0 < j.2 ∧ j.2 ≤ (archg(j.1)).card},
        sLocalThetaPrincipalPartCoeff (F := F) (S := S) (1 : PontryaginDual J₁g) j.val.1
          j.property.1 j.val.2 x.val = 0 :=
  Submodule.mem_iInf _

private theorem sec3bP_gamma_not_le (u₁ u₂ : InfinitePlace F) (h2 : u₂.IsReal) :
    ¬ sLocalGammaFiltration (F := F) (S := S) (1 : PontryaginDual J₁g)
        (fun w ↦ if w = u₁ then 1 else 0) ≤
      sLocalGammaFiltration (F := F) (S := S) (1 : PontryaginDual J₁g)
        (fun w ↦ if w = u₂ then 2 else 0) := by
  intro hle
  let a : InfinitePlace F → ℕ := fun w ↦ if w = u₂ then 2 else 0
  let b : InfinitePlace F → ℕ := fun w ↦ if w = u₁ then 1 else 0
  let N' : InfinitePlace F → ℕ := fun w ↦ max (a w) (b w)
  let c4 : Xg := shiftg((1 : Xg), (-4 : ℂ))
  have hcomp := sec3bP_onComponent_shift (F := F) (S := S) (-4 : ℂ)
  have hpair : ({2, 4} : Set ℝ).encard = 2 := Set.encard_pair (by norm_num)
  have hc4b : c4 ∉ cutg(b) := by
    rintro ⟨-, w, -, hcard⟩
    have h1 := (Set.encard_le_encard (sec3bP_pair_sub (S := S) w)).trans hcard
    rw [hpair] at h1
    have h3 : b w ≤ 1 := by simp only [b]; split_ifs <;> omega
    have h4 : ((b w : ℕ) : ℕ∞) ≤ 1 := by exact_mod_cast h3
    exact absurd (h1.trans h4) (by decide)
  have hc4a : c4 ∈ cutg(a) := by
    refine ⟨hcomp, u₂, ?_, ?_⟩
    · have := sec3bP_even_pole (S := S) u₂ 2
      rwa [show -(2 * ((2 : ℕ) : ℂ)) = (-4 : ℂ) by push_cast; ring] at this
    · refine (Set.encard_le_encard (sec3bP_sub_pair (S := S) u₂ h2)).trans ?_
      rw [hpair]
      simp [a]
  obtain ⟨hfin, hind⟩ := sLocalGammaFiltration_coeff_independent (F := F) (S := S)
    (1 : PontryaginDual J₁g) N'
  have hmono_a := fun c (hc : c ∈ cutg(a)) ↦ sec3bP_cut_mono (N' := N') (fun w ↦ le_max_left _ _) hc
  have hmono_b := fun c (hc : c ∈ cutg(b)) ↦ sec3bP_cut_mono (N' := N') (fun w ↦ le_max_right _ _) hc
  have hcard : 1 ≤ (archg(c4)).card :=
    Finset.card_pos.mpr ⟨u₂, by
      have := sec3bP_even_pole (S := S) u₂ 2
      rwa [show -(2 * ((2 : ℕ) : ℂ)) = (-4 : ℂ) by push_cast; ring] at this⟩
  obtain ⟨x, hx0, hxo⟩ := sec3bP_exists_dual_single _
    (hind.map' (ContinuousLinearMap.coeLM ℂ)
      (LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective))
    ⟨(c4, 1), hcomp, hmono_a c4 hc4a, one_pos, hcard⟩
  have hxb : x ∈ sLocalGammaFiltration (F := F) (S := S) (1 : PontryaginDual J₁g) b := by
    refine (sec3bP_mem_filt b x).mpr fun j ↦ ?_
    refine hxo ⟨j.val, j.property.1, hmono_b _ j.property.2.1, j.property.2.2⟩ ?_
    intro h
    apply hc4b
    have := congrArg (fun k ↦ k.val.1) h
    simp only at this
    rw [← this]
    exact j.property.2.1
  exact hx0 ((sec3bP_mem_filt a x).mp (hle hxb) ⟨(c4, 1), hcomp, hc4a, one_pos, hcard⟩)

end GammaAntitone

section QSqrtTwo

open Polynomial

/-- Two is not the square of a rational number. -/
private theorem sec3bP_sq_ne_two (b : ℚ) : b ^ 2 ≠ 2 := by
  intro hb
  have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
  have h1 : (b.num : ℚ) ^ 2 = 2 * (b.den : ℚ) ^ 2 := by
    have := Rat.num_div_den b
    rw [← this, div_pow, div_eq_iff (pow_ne_zero 2 hd)] at hb
    exact hb
  have h2 : b.num ^ 2 = 2 * (b.den : ℤ) ^ 2 := by exact_mod_cast h1
  have hn : Even b.num := (Int.even_pow.mp ⟨b.den ^ 2, by rw [h2]; ring⟩).1
  obtain ⟨k, hk⟩ := hn
  have h3 : (b.den : ℤ) ^ 2 = 2 * k ^ 2 := by
    rw [hk] at h2
    nlinarith [h2]
  have hdn : Even (b.den : ℤ) := (Int.even_pow.mp ⟨k ^ 2, by rw [h3]; ring⟩).1
  have h4 : 2 ∣ b.num.natAbs := Int.ofNat_dvd_left.mp ⟨k, by rw [hk]; ring⟩
  have h5 : 2 ∣ b.den := by
    obtain ⟨m, hm⟩ := hdn
    exact Int.natCast_dvd_natCast.mp ⟨m, by rw [hm]; push_cast; ring⟩
  have h6 := Nat.dvd_gcd h4 h5
  rw [b.reduced.gcd_eq_one] at h6
  norm_num at h6

private theorem sec3bP_irred_sqrt_two : Irreducible (X ^ 2 - C 2 : ℚ[X]) :=
  irreducible_X_pow_sub_C_of_prime Nat.prime_two sec3bP_sq_ne_two

/-- A real embedding as a real infinite place. -/
private theorem sec3bP_mk_real {K : Type*} [Field K] (φ : K →+* ℝ) :
    (InfinitePlace.mk (Complex.ofRealHom.comp φ)).IsReal := by
  rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

/-- Two real embeddings with different absolute values give two real places. -/
private theorem sec3bP_two_real {K : Type*} [Field K] (φ ψ : K →+* ℝ) (x : K)
    (hx : |φ x| ≠ |ψ x|) :
    ∃ w₁ w₂ : InfinitePlace K, w₁ ≠ w₂ ∧ w₁.IsReal ∧ w₂.IsReal := by
  refine ⟨_, _, fun h ↦ hx ?_, sec3bP_mk_real φ, sec3bP_mk_real ψ⟩
  have := congrArg (fun w : InfinitePlace K ↦ w x) h
  simpa [InfinitePlace.apply] using this

private theorem sec3bP_qsqrt2_two_real :
    letI : Fact (Irreducible (X ^ 2 - C 2 : ℚ[X])) := ⟨sec3bP_irred_sqrt_two⟩
    ∃ w₁ w₂ : InfinitePlace (AdjoinRoot (X ^ 2 - C 2 : ℚ[X])),
      w₁ ≠ w₂ ∧ w₁.IsReal ∧ w₂.IsReal := by
  have : Fact (Irreducible (X ^ 2 - C 2 : ℚ[X])) := ⟨sec3bP_irred_sqrt_two⟩
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (X ^ 2 - C 2 : ℚ[X]).eval₂ (algebraMap ℚ ℝ) (Real.sqrt 2) = 0 := by
    simp [hs]
  have h2 : (X ^ 2 - C 2 : ℚ[X]).eval₂ (algebraMap ℚ ℝ) (-Real.sqrt 2) = 0 := by
    simp [hs]
  refine sec3bP_two_real (AdjoinRoot.lift _ _ h1) (AdjoinRoot.lift _ _ h2)
    (AdjoinRoot.root _ + 1) ?_
  simp only [map_add, map_one, AdjoinRoot.lift_root]
  have hgt : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [abs_of_pos (by linarith), abs_of_neg (by linarith)]
  intro h
  linarith

end QSqrtTwo

/-- Paper: Notation 7.3.4.1, p. 364.
The printed lexicographic orders on the real and complex cutoff tuples make
the no-pole spaces a decreasing filtration. -/
def Printed.sLocalGammaFiltration_antitone : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (χ : PontryaginDual J₁(F, S)) (r₁ r₂ : ℕ)
    (realPlaces : Fin r₁ ≃ {w : InfinitePlace F // w.IsReal})
    (complexPlaces : Fin r₂ ≃ {w : InfinitePlace F // w.IsComplex})
    (a b : InfinitePlace F → ℕ),
    lexLe(realPlaces, a, b) → lexLe(complexPlaces, a, b) →
      sLocalGammaFiltration χ b ≤ sLocalGammaFiltration χ a

/-- Paper: Notation 7.3.4.1, p. 364.
For F = ℚ(√2) and the trivial character on the archimedean stage, (0,2) is
lexicographically below (1,0). Both real places have the poles of Γℝ. Apply
the Euler differential polynomial s²(s+2)² in the Mellin variable to the
product Gaussian. Its double pole at −4 remains, while the poles at 0 and
−2 are canceled. Its class is in the stage (1,0) and outside (0,2). -/
theorem Printed.sLocalGammaFiltration_antitone_false :
    ¬ Printed.sLocalGammaFiltration_antitone := by
  intro h
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ)) :=
    ⟨sec3bP_irred_sqrt_two⟩
  let K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ)
  let : NumberField K :=
    { to_charZero := inferInstance
      to_finiteDimensional :=
        (AdjoinRoot.powerBasis (Fact.out : Irreducible
          (Polynomial.X ^ 2 - Polynomial.C 2 : Polynomial ℚ)).ne_zero).finite }
  obtain ⟨w₁, w₂, hne, hr₁, hr₂⟩ := sec3bP_qsqrt2_two_real
  let e := (Fintype.equivFin {w : InfinitePlace K // w.IsReal}).symm
  let e' := (Fintype.equivFin {w : InfinitePlace K // w.IsComplex}).symm
  have hcard : 1 < Fintype.card {w : InfinitePlace K // w.IsReal} :=
    Fintype.one_lt_card_iff.mpr ⟨⟨w₁, hr₁⟩, ⟨w₂, hr₂⟩, fun h' ↦ hne (congrArg Subtype.val h')⟩
  let u₁ : InfinitePlace K := (e ⟨0, by omega⟩).val
  let u₂ : InfinitePlace K := (e ⟨1, hcard⟩).val
  have hu : u₁ ≠ u₂ := by
    intro h'
    have := e.injective (Subtype.ext h')
    simp [Fin.ext_iff] at this
  have hreal (u : InfinitePlace K) (hu : u.IsReal) (v : {w : InfinitePlace K // w.IsComplex}) :
      v.val ≠ u := by
    intro h'
    exact InfinitePlace.not_isReal_iff_isComplex.mpr v.property (h' ▸ hu)
  have hle := h K ∅ 1 _ _ e e' (fun w ↦ if w = u₂ then 2 else 0) (fun w ↦ if w = u₁ then 1 else 0)
    (Or.inr ⟨⟨0, by omega⟩, show (if u₁ = u₂ then 2 else 0) < (if u₁ = u₁ then 1 else 0) by
      simp [hu], fun j hj ↦ absurd hj (by simp [Fin.lt_def])⟩)
    (Or.inl fun i ↦ by simp [hreal u₁ (e _).property (e' i), hreal u₂ (e _).property (e' i)])
  exact sec3bP_gamma_not_le (S := ∅) u₁ u₂ (e _).property hle

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
On the signed Laurent convention of Definition 7.1.2.1, the displayed positive-index
coefficients (7.3.4.4) form a finite independent spanning family for the annihilator.
On representatives after finite PV this says the finite array is onto and its common
kernel is the no-pole stage, characterized by vanishing of the negative coefficients. -/
def Printed.sLocalGammaFiltration_dual_span : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (V(F)))
    (ω : PontryaginDual J₁(F, S)) (N : InfinitePlace F → ℕ),
    let C := sLocalGammaPoleCutoff (F := F) (S := S) ω N
    let J := {j : QuasiCharacter (SIdeleQuotient F S) × ℕ // j.1 ∈ C ∧
      0 < j.2 ∧ j.2 ≤ (sLocalArchPolePlaces (F := F) (S := S) j.1).card}
    let coeff := fun (f : B(F, S)) (j : J) (k : ℤ) ↦
      sLocalZLaurentCoeff (F := F) (S := S)
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) j.val.1 k
    Finite J ∧ (∀ z : J → ℂ, ∃ f : B(F, S), ∀ j : J, coeff f j j.val.2 = z j) ∧
      (∀ f : B(F, S), (∀ j : J, coeff f j j.val.2 = 0) ↔
        ∀ j : J, coeff f j (-(j.val.2 : ℤ)) = 0)

section DualSpan

open MeasureTheory

local notation "Jq" => SIdeleQuotient ℚ ∅
local notation "Iq" => (SAdeleRing ℚ ∅)ˣ
local notation "Bq" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))
local notation "mq" => sIdeleQuotientNorm ℚ ∅
local notation "hmq" => (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous
local notation "circleℂ" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartq(" χ ")" => quasiCharacterNormTwist mq hmq ((circleℂ).comp χ)
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ ∅
local notation "re∞" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
local notation "rq(" g ")" => (((mq (QuotientGroup.mk g) : ℝ≥0ˣ) : ℝ≥0) : ℝ)

/-- Conjugating the identity on a tensor factor by an equivalence gives the identity. -/
private theorem sec3bP_pv_aux {A B W : Type*} [AddCommGroup A] [Module ℂ A] [TopologicalSpace A]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [AddCommGroup B] [Module ℂ B] [TopologicalSpace B]
    (e : InductiveTensor A W ≃L[ℂ] B) (P : W →ₗ[ℂ] W) (hP : P = LinearMap.id) (f : B) :
    (e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : A →ₗ[ℂ] A) P).comp
      e.symm.toLinearMap)) f = f := by
  subst hP
  exact (congrArg e (LinearMap.congr_fun TensorProduct.map_id (e.symm f))).trans
    (e.apply_symm_apply f)

/-- With no finite places the full principal value is the identity. -/
private theorem sec3bP_PV_empty (f : Bq) :
    sAdelePrincipalValue ℚ (Finset.Subset.refl (∅ : Finset Vℚ)) f = f := by
  unfold sAdelePrincipalValue
  refine sec3bP_pv_aux _ _ ?_ f
  refine LinearMap.ext fun x ↦ ?_
  have hfun : (fun w : (∅ : Finset Vℚ) ↦ if w.val ∈ (∅ : Finset Vℚ) then
      (finitePlacePrincipalValue w.val).toLinearMap else
      (LinearMap.id : SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)) →ₗ[ℂ] _)) =
      fun _ ↦ LinearMap.id := funext fun w ↦ absurd w.2 (Finset.notMem_empty _)
  exact (LinearMap.congr_fun (congrArg PiTensorProduct.map hfun) x).trans
    (LinearMap.congr_fun PiTensorProduct.map_id x)

/-- The residue of `g z / z ^ 2` at zero is the derivative of `g` there. -/
private theorem sec3bP_residue_sq {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    complexResidue (fun z ↦ g z / z ^ ((1 : ℤ) + 1)) 0 = deriv g 0 := by
  let h := dslope g 0
  have hh : Differentiable ℂ h := fun z ↦ ((hg.analyticAt z).dslope 0).differentiableAt
  have hgz (z : ℂ) : g z = g 0 + z * h z := by
    have := sub_smul_dslope g 0 z
    rw [sub_zero, smul_eq_mul] at this
    linear_combination -this
  unfold complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hne (z : ℂ) (hz : z ∈ Metric.sphere (0 : ℂ) r) : z ≠ 0 := by
    rintro rfl
    rw [mem_sphere_iff_norm, sub_zero, norm_zero] at hz
    exact hr.ne hz
  have heq : EqOn (fun z ↦ g z / z ^ ((1 : ℤ) + 1))
      (fun z ↦ g 0 * (z - 0) ^ (-2 : ℤ) + (z - 0)⁻¹ • h z) (Metric.sphere 0 r) := by
    intro z hz
    have h0 := hne z hz
    simp only [sub_zero, smul_eq_mul]
    rw [hgz z, show ((1 : ℤ) + 1) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast,
      show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    field_simp
  have hc1 : CircleIntegrable (fun z ↦ g 0 * (z - 0) ^ (-2 : ℤ)) 0 r :=
    (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun z hz ↦ Or.inl (by simpa using hne z hz))).circleIntegrable hr.le
  have hc2 : CircleIntegrable (fun z ↦ (z - 0)⁻¹ • h z) 0 r :=
    (((continuousOn_id.sub continuousOn_const).inv₀ fun z hz ↦ by simpa using hne z hz).smul
      hh.continuous.continuousOn).circleIntegrable hr.le
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [circleIntegral.integral_congr hr.le heq, circleIntegral.integral_add hc1 hc2,
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_zpow_of_ne (by norm_num),
    mul_zero, zero_add,
    Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty
      (Metric.mem_ball_self hr) hh.continuous.continuousOn (fun z _ ↦ hh z),
    smul_eq_mul, mul_div_cancel_left₀ _ h2pi]
  exact (dslope_same g 0).symm

/-- The residue of `g z / z ^ (1 - n)` at zero vanishes for entire `g` and `1 ≤ n`. -/
private theorem sec3bP_residue_neg {g : ℂ → ℂ} (hg : Differentiable ℂ g) (n : ℕ) (hn : 0 < n) :
    complexResidue (fun z ↦ g z / z ^ (-(n : ℤ) + 1)) 0 = 0 := by
  unfold complexResidue
  have he : (fun z ↦ g z / z ^ (-(n : ℤ) + 1)) = fun z ↦ g z * z ^ (n - 1) := by
    funext z
    rw [show -(n : ℤ) + 1 = -((n - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, div_inv_eq_mul]
  rw [he]
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hd : Differentiable ℂ (fun z ↦ g z * z ^ (n - 1)) := hg.mul (differentiable_id.pow _)
  rw [Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    hd.continuous.continuousOn (fun z _ ↦ hd z), zero_div]

/-- A compactly supported smooth profile of the real coordinate is a test at the rational
archimedean stage. -/
private theorem sec3bP_test (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ f : Bq, ∀ x : SAdeleRing ℚ ∅,
      f (Multiplicative.ofAdd x) = (φ (re∞ (x.1 Rat.infinitePlace)) : ℂ) := by
  have hreal (w : InfinitePlace ℚ) : w.IsReal :=
    (Subsingleton.elim Rat.infinitePlace w) ▸ Rat.isReal_infinitePlace
  let i0 : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  have : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) (hreal w.1)⟩
  let G : mixedEmbedding.mixedSpace ℚ → ℂ := fun y ↦ (φ (y.1 i0) : ℂ)
  have hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G :=
    Complex.ofRealCLM.contDiff.comp (hφ.comp
      ((ContinuousLinearMap.proj i0 : ({w : InfinitePlace ℚ // w.IsReal} → ℝ) →L[ℝ] ℝ).contDiff.comp
        contDiff_fst))
  have hK : IsCompact ((fun t : ℝ ↦ ((fun _ ↦ t, 0) : mixedEmbedding.mixedSpace ℚ)) ''
      tsupport φ) :=
    hc.isCompact.image (by fun_prop)
  have hGc : HasCompactSupport G := by
    refine HasCompactSupport.intro hK fun y hy ↦ ?_
    by_contra hne
    apply hy
    refine ⟨y.1 i0, subset_tsupport φ (fun h0 ↦ hne (by simp [G, h0])), ?_⟩
    exact Prod.ext (funext fun j ↦ congrArg y.1 (Subsingleton.elim i0 j)) (Subsingleton.elim _ _)
  let Gs : SchwartzMap (mixedEmbedding.mixedSpace ℚ) ℂ := hGc.toSchwartzMap hG
  have hmem := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ (φ (re∞ (x Rat.infinitePlace)) : ℂ))).mpr ⟨Gs, fun x ↦ rfl⟩
  let a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)) := ⟨_, hmem⟩
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv ℚ (∅ : Finset Vℚ)
  let g : ∀ w : (∅ : Finset Vℚ), SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)) :=
    fun w ↦ absurd w.2 (Finset.notMem_empty _)
  refine ⟨e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)), fun x ↦ ?_⟩
  rw [he, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rfl

/-- At the rational archimedean stage the real coordinate of an idele has the idelic norm
as its absolute value. -/
private theorem sec3bP_norm (g : Iq) : (re∞ (g.val.1 Rat.infinitePlace)) ^ 2 = rq(g) ^ 2 := by
  have hn : rq(g) = ‖g.val.1 Rat.infinitePlace‖ := by
    change ((sIdeleNorm ℚ ∅ g : ℝ≥0) : ℝ) = _
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset Vℚ)), Finset.prod_empty, mul_one,
      Fintype.prod_subsingleton _ Rat.infinitePlace, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  rw [hn, ← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _), Real.norm_eq_abs, sq_abs]

/-- A smooth bump supported in `(4, 9)`. -/
private theorem sec3bP_bump : ∃ ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ t, 0 ≤ ψ t) ∧
    (∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) ∧ ψ (25 / 4) ≠ 0 := by
  let b : ContDiffBump (25 / 4 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b, b.contDiff, fun t ↦ b.nonneg, fun t ht ↦ ?_, ?_⟩
  · have h1 : t ∈ Metric.ball (25 / 4 : ℝ) (1 / 4) := by
      have := Function.mem_support.mpr ht
      rwa [b.support_eq] at this
    rw [Real.ball_eq_Ioo] at h1
    obtain ⟨h1, h2⟩ := h1
    constructor <;> linarith
  · rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]
    norm_num

/-- The profiles `ψ(t²) t⁻²ⁿ` are smooth and compactly supported. -/
private theorem sec3bP_profile (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hs : ∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) ∧
      HasCompactSupport (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) := by
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t = 0
    · subst ht
      have hev : (fun t : ℝ ↦ ψ (t ^ 2) * ((t ^ 2) ^ n)⁻¹) =ᶠ[𝓝 0] fun _ ↦ 0 := by
        have h4 : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 < 4 :=
          (continuousAt_id.pow 2).eventually_lt continuousAt_const (by norm_num)
        filter_upwards [h4] with t ht
        have : ψ (t ^ 2) = 0 := by
          by_contra h
          linarith [(hs _ h).1]
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · exact (hψ.contDiffAt.comp t (contDiffAt_id.pow 2)).mul
        (((contDiffAt_id.pow 2).pow n).inv (pow_ne_zero _ (pow_ne_zero _ ht)))
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 3) fun t ht ↦ ?_
    have : ψ (t ^ 2) = 0 := by
      by_contra h
      have h9 := (hs _ h).2
      apply ht
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
      exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
    simp [this]

/-- Two functions in meromorphic normal form on the plane that agree on the right
half-plane agree everywhere. -/
private theorem sec3bP_eq_of_meromorphicNFOn {G H : ℂ → ℂ}
    (hG : MeromorphicNFOn G univ) (hH : MeromorphicNFOn H univ)
    (h : ∀ z : ℂ, 0 < z.re → G z = H z) (s : ℂ) : G s = H s := by
  have hAt : meromorphicOrderAt (G - H) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hn : ∀ᶠ z : ℂ in 𝓝 (1 : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono fun z hz ↦ sub_eq_zero.mpr (h z hz)
  have hOrd := (hG.meromorphicOn.sub hH.meromorphicOn).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (1 : ℂ)) (mem_univ s) hAt
  have hNear : G =ᶠ[𝓝[≠] s] H :=
    (meromorphicOrderAt_eq_top_iff.mp hOrd).mono fun _ h ↦ sub_eq_zero.mp h
  exact (((hG (mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hH (mem_univ s))).mp
    hNear).eq_of_nhds

/-- Every quasi-character of the rational archimedean stage lies on a unitary chart. -/
private theorem sec3bP_chart (c : QuasiCharacter Jq) :
    ∃ (χ : PontryaginDual Jq) (s : ℂ), ∀ z : ℂ,
      quasiCharacterNormTwist mq hmq c z = chartq(χ) (s + z) := by
  let : LocallyCompactSpace Iq := (sIdeleGroup_description ℚ ∅).2.2.1
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  have hp := isProperMap_sIdeleQuotientNorm ℚ ∅
  have hne : ∃ g, mq g ≠ 1 := by
    obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    exact ⟨τ t, (hτ t).trans_ne ht⟩
  let a := quasiCharacterAbscissa mq hp hne c
  let d := quasiCharacterNormTwist mq hmq c (-(a : ℂ))
  have hrad (g : Jq) : (((mq g : ℝ≥0) : ℝ) : ℂ) ^ (a : ℂ) = (‖c g‖ : ℂ) := by
    rw [← Complex.ofReal_cpow (NNReal.coe_nonneg _) a,
      norm_quasiCharacter_eq_rpow_abscissa mq hp hne]
  have hd (g : Jq) : d g = c g / (‖c g‖ : ℂ) := by
    change c g * _ ^ (-(a : ℂ)) = _
    rw [Complex.cpow_neg, hrad, div_eq_mul_inv]
  have hn (g : Jq) : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  let χ : PontryaginDual Jq :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (by
        rw [hd, norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (hn g)])⟩
      map_one' := Subtype.ext d.map_one
      map_mul' x y := Subtype.ext (d.map_mul x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  refine ⟨χ, (a : ℂ), fun z ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  have hN : (((mq g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mq g).ne_zero)
  change c g * (((mq g : ℝ≥0) : ℝ) : ℂ) ^ z =
    d g * (((mq g : ℝ≥0) : ℝ) : ℂ) ^ ((a : ℂ) + z)
  rw [hd, Complex.cpow_add _ _ hN, hrad, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (hn g))]

/-- Dividing a test by an even power of the norm shifts its zeta integral. -/
private theorem sec3bP_shift (F0 G : Bq) (n : ℕ)
    (hF : ∀ g : Iq, G (Multiplicative.ofAdd g.val) =
      F0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹)
    (χ : PontryaginDual Jq) (v : ℂ) :
    sLocalIdelicZetaIntegral G (chartq(χ) (v + 2 * n)) =
      sLocalIdelicZetaIntegral F0 (chartq(χ) v) := by
  unfold sLocalIdelicZetaIntegral
  congr 1
  funext g
  change G _ * ((χ (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ (v + 2 * n)) =
    F0 _ * ((χ (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ v)
  have h0 : ((rq(g) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have h1 := pow_ne_zero (2 * n) h0
  rw [hF, Complex.cpow_add _ _ h0, show (2 * (n : ℂ)) = ((2 * n : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast]
  field_simp

/-- A test whose quotients by even powers of the norm are again tests has an entire
Z-function on every unitary chart. -/
private theorem sec3bP_entire (F0 : Bq) (Fn : ℕ → Bq)
    (hF : ∀ (n : ℕ) (g : Iq), Fn n (Multiplicative.ofAdd g.val) =
      F0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹)
    (χ : PontryaginDual Jq) :
    Differentiable ℂ (fun s ↦ sLocalIdelicZFunction F0 (chartq(χ) s)) := by
  have hint (n : ℕ) (v : ℂ) := sec3bP_shift F0 (Fn n) n (hF n) χ v
  have hmer (n : ℕ) : MeromorphicNFOn
      (fun v ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) (v + 2 * n))) univ := fun z _ ↦
    (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt
      (f := fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) s))).mpr
      (sLocalIdelicZFunction_meromorphic (Fn n) χ (mem_univ _))
  have heq (n : ℕ) (v : ℂ) : sLocalIdelicZFunction F0 (chartq(χ) v) =
      sLocalIdelicZFunction (Fn n) (chartq(χ) (v + 2 * n)) := by
    refine sec3bP_eq_of_meromorphicNFOn (G := fun v ↦ sLocalIdelicZFunction F0 (chartq(χ) v))
      (sLocalIdelicZFunction_meromorphic F0 χ) (hmer n) (fun z hz ↦ ?_) v
    have hz' : 0 < (z + 2 * (n : ℂ)).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      norm_num
      positivity
    rw [sLocalIdelicZFunction_eq_integral F0 ⟨χ, z, hz, rfl⟩,
      sLocalIdelicZFunction_eq_integral (Fn n) ⟨χ, z + 2 * n, hz', rfl⟩, hint]
  have han (n : ℕ) (w : ℂ) (hw : 0 < w.re) :
      AnalyticAt ℂ (fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) s)) w := by
    have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    refine ((sLocalIdelicZetaIntegral_analyticOn (Fn n) χ) w hw).congr ?_
    filter_upwards [hopen.mem_nhds hw] with s hs
    exact (sLocalIdelicZFunction_eq_integral (Fn n) ⟨χ, s, hs, rfl⟩).symm
  intro v
  obtain ⟨n, hn⟩ := exists_nat_gt (-v.re)
  have hfun : (fun s ↦ sLocalIdelicZFunction F0 (chartq(χ) s)) =
      fun s ↦ sLocalIdelicZFunction (Fn n) (chartq(χ) (s + 2 * n)) := funext (heq n)
  rw [hfun]
  have hpos : 0 < (v + 2 * (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith
  exact differentiableAt_comp_add_const.mpr (han n (v + 2 * n) hpos).differentiableAt

/-- A real function with a holomorphic extension, growing at least geometrically to the
right and bounded below near zero, has positive derivative at zero. -/
private theorem sec3bP_slope {g : ℂ → ℂ} (hg : Differentiable ℂ g) (G : ℝ → ℝ)
    (hgG : ∀ t : ℝ, 0 < t → g t = G t)
    (hmono : ∀ s t : ℝ, 0 < s → s < t → (2 : ℝ) ^ (t - s) * G s ≤ G t)
    (hlow : ∀ s : ℝ, 0 < s → s < 1 → (3 : ℝ) ^ (s - 1) * G 1 ≤ G s) (h1 : 0 < G 1) :
    0 < (deriv g 0).re := by
  let h : ℝ → ℝ := fun t ↦ (g t).re
  have hd : HasDerivAt h (deriv g 0).re 0 :=
    HasDerivAt.real_of_complex (z := 0) (by simpa using (hg 0).hasDerivAt)
  have hhG (t : ℝ) (ht : 0 < t) : h t = G t := by simp [h, hgG t ht]
  have hcont : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  set c := (3 : ℝ)⁻¹ * G 1 with hcdef
  have hc : 0 < c := by positivity
  have h0 : c ≤ h 0 := by
    refine ge_of_tendsto hcont ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    rw [hhG s hs.1]
    refine le_trans ?_ (hlow s hs.1 hs.2)
    apply mul_le_mul_of_nonneg_right _ h1.le
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hs.1])
  have hup (t : ℝ) (ht : 0 < t) : (2 : ℝ) ^ t * h 0 ≤ G t := by
    have hc2 : Continuous (fun s : ℝ ↦ (2 : ℝ) ^ (t - s)) := by
      simp_rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      fun_prop
    have hlim : Tendsto (fun s ↦ (2 : ℝ) ^ (t - s) * h s) (𝓝[>] 0)
        (𝓝 ((2 : ℝ) ^ (t - 0) * h 0)) :=
      ((hc2.tendsto 0).mono_left nhdsWithin_le_nhds).mul hcont
    rw [sub_zero] at hlim
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    rw [hhG s hs.1]
    exact hmono s t hs.1 hs.2
  have hslope : Tendsto (slope h 0) (𝓝[>] 0) (𝓝 (deriv g 0).re) :=
    (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun x (hx : 0 < x) ↦ hx.ne')
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbound : Real.log 2 * c ≤ (deriv g 0).re := by
    refine ge_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [slope_def_field, hhG t ht, sub_zero, le_div_iff₀ ht]
    have h2 : 1 + t * Real.log 2 ≤ (2 : ℝ) ^ t := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      linarith [Real.add_one_le_exp (Real.log 2 * t)]
    have hA := mul_le_mul_of_nonneg_right h2 (hc.le.trans h0)
    have hB := mul_nonneg (mul_nonneg ht.le hlog.le) (sub_nonneg.mpr h0)
    nlinarith [hup t ht]
  exact lt_of_lt_of_le (mul_pos hlog hc) hbound

/-- On the trivial chart the Z-function of a nonnegative bump in norm between two and
three has positive derivative at zero. -/
private theorem sec3bP_deriv_pos (F0 : Bq) (ψ : ℝ → ℝ) (hψc : Continuous ψ)
    (hψ0 : ∀ t, 0 ≤ ψ t) (hs : ∀ t, ψ t ≠ 0 → 4 < t ∧ t < 9) (hψ1 : ψ (25 / 4) ≠ 0)
    (hF : ∀ g : Iq, F0 (Multiplicative.ofAdd g.val) = (ψ (rq(g) ^ 2) : ℂ))
    (hd : Differentiable ℂ (fun s ↦ sLocalIdelicZFunction F0 (chartq(1) s))) :
    0 < (deriv (fun s ↦ sLocalIdelicZFunction F0 (chartq(1) s)) 0).re := by
  let F (t : ℝ) (g : Iq) : ℝ := ψ (rq(g) ^ 2) * rq(g) ^ t
  have hpt (t : ℝ) (g : Iq) : F0 (Multiplicative.ofAdd g.val) * chartq(1) t (QuotientGroup.mk g) =
      ((F t g : ℝ) : ℂ) := by
    change F0 _ * (((1 : PontryaginDual Jq) (QuotientGroup.mk g) : ℂ) * ((rq(g) : ℂ)) ^ (t : ℂ)) = _
    rw [hF, PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.ofReal_mul,
      Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  have hpos (t : ℝ) (ht : 0 < t) : chartq(1) t ∈ {c : QuasiCharacter Jq |
      ∃ (χ : PontryaginDual Jq) (s : ℂ), s ∈ Complex.re ⁻¹' Ioi (0 : ℝ) ∧ c = chartq(χ) s} :=
    ⟨1, t, by simpa using ht, rfl⟩
  have hval (t : ℝ) (ht : 0 < t) :
      sLocalIdelicZFunction F0 (chartq(1) t) = ((∫ g, F t g ∂μq : ℝ) : ℂ) := by
    let : MeasurableSpace (SAdeleRing ℚ ∅) := instMeasurableSpaceSAdeleRing ℚ ∅
    rw [sLocalIdelicZFunction_eq_integral F0 (hpos t ht), ← integral_complex_ofReal]
    unfold sLocalIdelicZetaIntegral
    congr 1
    funext g
    exact hpt t g
  have hint (t : ℝ) (ht : 0 < t) : Integrable (F t) μq := by
    have h := sLocalIdelicZetaIntegral_integrable F0 (chartq(1) t) (hpos t ht)
    simp_rw [hpt] at h
    simpa using ContinuousLinearMap.integrable_comp Complex.reCLM h
  -- Pointwise facts about the norm on the support of the bump.
  have hr0 (g : Iq) : 0 < rq(g) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hsupp (g : Iq) (hg : ψ (rq(g) ^ 2) ≠ 0) : 2 < rq(g) ∧ rq(g) < 3 := by
    obtain ⟨h4, h9⟩ := hs _ hg
    have := hr0 g
    constructor <;> nlinarith
  have hmono (s t : ℝ) (hs0 : 0 < s) (hst : s < t) :
      (2 : ℝ) ^ (t - s) * (∫ g, F s g ∂μq) ≤ ∫ g, F t g ∂μq := by
    rw [← integral_const_mul]
    refine integral_mono ((hint s hs0).const_mul _) (hint t (hs0.trans hst)) fun g ↦ ?_
    by_cases hg : ψ (rq(g) ^ 2) = 0
    · change (2 : ℝ) ^ (t - s) * (ψ (rq(g) ^ 2) * rq(g) ^ s) ≤ ψ (rq(g) ^ 2) * rq(g) ^ t
      rw [hg]
      simp
    obtain ⟨h2, -⟩ := hsupp g hg
    change (2 : ℝ) ^ (t - s) * (ψ (rq(g) ^ 2) * rq(g) ^ s) ≤ ψ (rq(g) ^ 2) * rq(g) ^ t
    have hx := hr0 g
    have hpow : (2 : ℝ) ^ (t - s) ≤ rq(g) ^ (t - s) :=
      Real.rpow_le_rpow (by norm_num) h2.le (by linarith)
    have hsplit : rq(g) ^ t = rq(g) ^ (t - s) * rq(g) ^ s := by
      rw [← Real.rpow_add hx, sub_add_cancel]
    rw [hsplit]
    have := hψ0 (rq(g) ^ 2)
    have := Real.rpow_nonneg hx.le s
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (hψ0 (rq(g) ^ 2)) this)]
  have hlow (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
      (3 : ℝ) ^ (s - 1) * (∫ g, F 1 g ∂μq) ≤ ∫ g, F s g ∂μq := by
    rw [← integral_const_mul]
    refine integral_mono ((hint 1 one_pos).const_mul _) (hint s hs0) fun g ↦ ?_
    by_cases hg : ψ (rq(g) ^ 2) = 0
    · change (3 : ℝ) ^ (s - 1) * (ψ (rq(g) ^ 2) * rq(g) ^ (1 : ℝ)) ≤ ψ (rq(g) ^ 2) * rq(g) ^ s
      rw [hg]
      simp
    obtain ⟨-, h3⟩ := hsupp g hg
    change (3 : ℝ) ^ (s - 1) * (ψ (rq(g) ^ 2) * rq(g) ^ (1 : ℝ)) ≤ ψ (rq(g) ^ 2) * rq(g) ^ s
    have hx := hr0 g
    have hpow : (3 : ℝ) ^ (s - 1) ≤ rq(g) ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos hx h3.le (by linarith)
    have hsplit : rq(g) ^ s = rq(g) ^ (s - 1) * rq(g) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hx, sub_add_cancel]
    rw [hsplit]
    have := hψ0 (rq(g) ^ 2)
    have := Real.rpow_nonneg hx.le (1 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (hψ0 (rq(g) ^ 2)) this)]
  have h1 : 0 < ∫ g, F 1 g ∂μq := by
    have := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) (S := ∅)
    have hrc : Continuous (fun g : Iq ↦ rq(g)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp ((isProperMap_sIdeleQuotientNorm ℚ ∅).continuous.comp QuotientGroup.continuous_mk))
    have hU : IsOpen {g : Iq | ψ (rq(g) ^ 2) ≠ 0} :=
      isOpen_ne_fun (hψc.comp (hrc.pow 2)) continuous_const
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    let u : ℝ≥0ˣ := Units.mk0 (5 / 2) (by norm_num)
    obtain ⟨g, hg⟩ := (QuotientGroup.mk_surjective :
      Function.Surjective (QuotientGroup.mk : Iq → Jq)) (σ u)
    have hgr : rq(g) = 5 / 2 := by
      rw [hg, hσ u]
      simp [u]
    have hne : ({g : Iq | ψ (rq(g) ^ 2) ≠ 0}).Nonempty :=
      ⟨g, by
        change ψ (rq(g) ^ 2) ≠ 0
        rw [hgr]
        norm_num
        exact hψ1⟩
    rw [integral_pos_iff_support_of_nonneg (fun g ↦ mul_nonneg (hψ0 _)
      (Real.rpow_nonneg (hr0 g).le _)) (hint 1 one_pos)]
    refine lt_of_lt_of_le (hU.measure_pos μq hne) (measure_mono fun g hg ↦ ?_)
    exact mul_ne_zero hg (Real.rpow_pos_of_pos (hr0 g) _).ne'
  exact sec3bP_slope hd (fun t ↦ ∫ g, F t g ∂μq) hval hmono hlow h1

/-- Paper: Theorem 7.3.4.1(2), pp. 364–365.
For the rational archimedean stage and trivial character take a nonnegative nonzero even
bump in the annulus two to three. Its Mellin transform is entire, and its derivative
at zero integrates the bump against a strictly positive logarithm. The coefficient
of exponent one therefore fails to annihilate the zero-cutoff stage. -/
theorem Printed.sLocalGammaFiltration_dual_span_false : ¬ Printed.sLocalGammaFiltration_dual_span := by
  intro h
  have h3 := (h ℚ ∅ 1 (fun _ ↦ 0)).2.2
  obtain ⟨ψ, hψ, hψ0, hs, hψ1⟩ := sec3bP_bump
  choose Fn hFn using fun n : ℕ ↦ sec3bP_test _ (sec3bP_profile ψ hψ hs n).1
    (sec3bP_profile ψ hψ hs n).2
  have hval (n : ℕ) (g : Iq) : Fn n (Multiplicative.ofAdd g.val) =
      ((ψ (rq(g) ^ 2) * ((rq(g) ^ 2) ^ n)⁻¹ : ℝ) : ℂ) := by
    rw [hFn, sec3bP_norm]
  have hF : ∀ (n : ℕ) (g : Iq), Fn n (Multiplicative.ofAdd g.val) =
      Fn 0 (Multiplicative.ofAdd g.val) * (((rq(g) : ℂ)) ^ (2 * n))⁻¹ := by
    intro n g
    rw [hval, hval]
    push_cast
    rw [pow_mul]
    simp
  have hF0 (g : Iq) : Fn 0 (Multiplicative.ofAdd g.val) = (ψ (rq(g) ^ 2) : ℂ) := by
    rw [hval]
    simp
  -- Every centered Z-germ of the test is entire.
  have hent (c : QuasiCharacter Jq) :
      Differentiable ℂ (fun z ↦ sLocalIdelicZFunction (Fn 0) (quasiCharacterNormTwist mq hmq c z)) := by
    obtain ⟨χ, s, hχ⟩ := sec3bP_chart c
    simp only [hχ]
    exact (sec3bP_entire (Fn 0) Fn hF χ).comp (differentiable_const _ |>.add differentiable_id)
  have hneg := (h3 (Fn 0)).mpr (fun j ↦ by
    beta_reduce
    rw [sec3bP_PV_empty]
    exact sec3bP_residue_neg (hent _) _ j.2.2.1)
  have hC := (sLocalGammaPoleCutoff_zero (F := ℚ) ∅).1
  obtain ⟨-, w, hw, -⟩ := id hC
  have hj := hneg ⟨(1, 1), hC, Nat.one_pos, Finset.card_pos.mpr ⟨w, hw⟩⟩
  beta_reduce at hj
  rw [sec3bP_PV_empty] at hj
  change complexResidue (fun z ↦ sLocalIdelicZFunction (Fn 0)
    (quasiCharacterNormTwist mq hmq 1 z) / z ^ ((1 : ℤ) + 1)) 0 = 0 at hj
  rw [sec3bP_residue_sq (hent 1)] at hj
  have h1 : (1 : QuasiCharacter Jq) = (circleℂ).comp (1 : PontryaginDual Jq) :=
    ContinuousMonoidHom.ext fun g ↦ by
      change (1 : ℂ) = (((1 : PontryaginDual Jq) g : Circle) : ℂ)
      rw [PontryaginDual.one_apply, Circle.coe_one]
  rw [h1] at hj
  have hpos := sec3bP_deriv_pos (Fn 0) ψ hψ.continuous hψ0 hs hψ1 hF0
    (sec3bP_entire (Fn 0) Fn hF 1)
  have hzero : (deriv (fun s ↦ sLocalIdelicZFunction (Fn 0) (chartq(1) s)) 0).re = 0 := by
    rw [show deriv (fun s ↦ sLocalIdelicZFunction (Fn 0) (chartq(1) s)) 0 = 0 from hj]
    rfl
  linarith

end DualSpan

end RiemannMasullo
