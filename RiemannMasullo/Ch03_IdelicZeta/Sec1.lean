module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.NumberTheory.NumberField.HeckeLFunction
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.PontryaginDual

import RiemannMasullo.ForMathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import RiemannMasullo.AppA_AlgebraicNT.Sec2

import RiemannMasullo.ForMathlib.Analysis.Complex.CoveringMap
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.CharacterExtension
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.CompactOpen
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Cyclic

/-!
# Riemann surfaces of continuous quasi-characters

Section 3.1 of Masullo. We use the compact-open topology on continuous monoid homomorphisms.
On a group, such a map into ℂ takes values in ℂˣ. This convention makes the global space
definitionally Mathlib's space of Hecke characters. The complex coordinates below use the
normalized module, including its exponent two at a complex place.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open scoped NNReal Manifold ContDiff

/-- Paper: §3.1.1, p. 118. The space of quasi-characters has the compact-open topology.
Deviation: We use complex-valued continuous homomorphisms on a group, whose values are units. -/
abbrev QuasiCharacter (G : Type*) [Group G] [TopologicalSpace G] := G →ₜ* ℂ

section Generalities

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)

local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

/-- Paper: Equation (3.1.1.1), p. 119. Restricting a quasi-character to the kernel of the
module gives the projection indexing the components. We view its values as complex numbers. -/
def normOneRestriction : C(QuasiCharacter G, QuasiCharacter m.ker) :=
  let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
  ⟨fun c => c.comp i, i.continuous_comp_left⟩

/-- The positive real units have the order topology and compact closed intervals. -/
private theorem nonnegRealUnits_orderTopology_and_compactIccSpace :
    OrderTopology ℝ≥0ˣ ∧ CompactIccSpace ℝ≥0ˣ := by
  let e := Nonneg.unitsHomeomorphPos ℝ
  let f : ℝ≥0ˣ ↪o ℝ := OrderEmbedding.ofStrictMono (Subtype.val ∘ e) (fun _ _ h => h)
  have hi : IsInducing f := (IsInducing.subtypeVal (t := Set.Ioi (0 : ℝ))).comp e.isInducing
  have hr : Set.range f = Set.Ioi 0 := by
    change Set.range ((Subtype.val : Set.Ioi (0 : ℝ) → ℝ) ∘ e) = _
    rw [Set.range_comp, e.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have ho : Set.OrdConnected (Set.range f) := hr.symm ▸ Set.ordConnected_Ioi
  refine ⟨⟨hi.eq_induced.trans (f.strictMono.induced_topology_eq_preorder ho)⟩, ⟨?_⟩⟩
  intro a b
  apply hi.isCompact_iff.mpr
  rw [f.image_Icc ho]
  exact isCompact_Icc

/-- Paper: Equation (3.1.1.1), p. 119. Every quasi-character of a closed nontrivial subgroup
of the positive reals can be joined to the trivial character by a continuous family. -/
private theorem exists_quasiCharacter_deformation (H : Subgroup ℝ≥0ˣ)
    (hH : IsClosed (H : Set ℝ≥0ˣ)) [Nontrivial H] (χ : QuasiCharacter H) :
    ∃ f : ℝ → QuasiCharacter H, Continuous f ∧ f 0 = 1 ∧ f 1 = χ := by
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.1
  rcases H.dense_or_isCyclic with hd | hc
  · have htop : H = ⊤ :=
      Subgroup.coe_eq_univ.mp (hH.closure_eq ▸ hd.closure_eq)
    subst H
    -- Real powers interpolate between the trivial homomorphism and the identity.
    let power (t : ℝ) (u : ↥(⊤ : Subgroup ℝ≥0ˣ)) : ↥(⊤ : Subgroup ℝ≥0ˣ) :=
      ⟨Units.mk0 ((u.val : ℝ≥0) ^ t)
        (ne_of_gt (NNReal.rpow_pos (pos_iff_ne_zero.mpr u.val.ne_zero))), trivial⟩
    have hpower : Continuous (uncurry power) := by
      apply IsInducing.subtypeVal.continuous_iff.mpr
      apply Units.isEmbedding_val₀.continuous_iff.mpr
      apply NNReal.isEmbedding_coe.continuous_iff.mpr
      exact (NNReal.continuous_coe.comp
        (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd))).rpow
          continuous_fst (fun p => Or.inl (NNReal.coe_ne_zero.mpr p.2.val.ne_zero))
    let f (t : ℝ) : QuasiCharacter ↥(⊤ : Subgroup ℝ≥0ˣ) :=
      χ.comp
        { toFun := power t
          map_one' := by
            apply Subtype.ext
            apply Units.ext
            simp [power]
          map_mul' := by
            intro x y
            apply Subtype.ext
            apply Units.ext
            simp [power, NNReal.mul_rpow]
          continuous_toFun := hpower.comp (continuous_const.prodMk continuous_id) }
    refine ⟨f, ContinuousMonoidHom.continuous_of_continuous_uncurry f
      (χ.continuous.comp hpower), ?_, ?_⟩
    · ext1 x
      change χ (power 0 x) = 1
      have h : power 0 x = 1 := by
        apply Subtype.ext
        apply Units.ext
        simp [power]
      rw [h, map_one]
    · ext1 x
      change χ (power 1 x) = χ x
      congr 1
      apply Subtype.ext
      apply Units.ext
      simp [power]
  · let : DiscreteTopology H := Subgroup.isCyclic_iff_discreteTopology.mp hc
    obtain ⟨orderIso⟩ := LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int.mp hc
    let e := orderIso.toMulEquiv
    -- Exponentiating a multiple of the logarithm interpolates the value on a generator.
    let z := Complex.log (χ (e.symm (Multiplicative.ofAdd 1)))
    let f (t : ℝ) : QuasiCharacter H := {
      toFun x := Complex.exp (((e x).toAdd : ℂ) * ((t : ℂ) * z))
      map_one' := by simp [show (1 : Multiplicative ℤ).toAdd = 0 from rfl]
      map_mul' x y := by
        rw [map_mul]
        change Complex.exp (↑((e x).toAdd + (e y).toAdd) * _) = _
        rw [Int.cast_add, add_mul, Complex.exp_add]
      continuous_toFun := continuous_of_discreteTopology }
    refine ⟨f, ContinuousMonoidHom.continuous_of_continuous_uncurry f ?_, ?_, ?_⟩
    · apply continuous_prod_of_discrete_right.mpr
      intro x
      change Continuous fun t : ℝ => Complex.exp (((e x).toAdd : ℂ) * ((t : ℂ) * z))
      exact Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.mul continuous_const))
    · ext1 x
      change Complex.exp (((e x).toAdd : ℂ) * ((0 : ℝ) * z)) = 1
      simp
    · ext1 x
      change Complex.exp (((e x).toAdd : ℂ) * (Complex.ofReal 1 * z)) = χ x
      have hx : e.symm (Multiplicative.ofAdd 1) ^ (e x).toAdd = x := by
        apply e.injective
        rw [map_zpow, e.apply_symm_apply]
        change Multiplicative.ofAdd ((e x).toAdd • (1 : ℤ)) = e x
        simp
      rw [Complex.ofReal_one, one_mul, Complex.exp_int_mul, Complex.exp_log, ← map_zpow, hx]
      exact ((Group.isUnit _).map χ).ne_zero

/-- Paper: Equation (3.1.1.1), p. 119. Two quasi-characters are in the same connected
component exactly when their restrictions to the norm-one subgroup agree. -/
theorem mem_connectedComponent_iff_normOneRestriction [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c d : QuasiCharacter G) :
    d ∈ connectedComponent c ↔ normOneRestriction m d = normOneRestriction m c := by
  let inv := c.comp (ContinuousMonoidHom.inv G)
  have hc (x : G) : c x ≠ 0 := ((Group.isUnit x).map c).ne_zero
  have hdiv (e : QuasiCharacter G) (x : G) : (e * inv) x = e x / c x := by
    change e x * c x⁻¹ = e x / c x
    rw [map_inv, div_eq_mul_inv]
  have htranslate (q : QuasiCharacter G) : Continuous (fun e : QuasiCharacter G => e * q) := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval.comp (continuous_fst.prodMk continuous_snd)).mul
      (q.continuous.comp continuous_snd)
  have hrestrict (e : QuasiCharacter G) :
      normOneRestriction m (e * inv) = 1 ↔ normOneRestriction m e = normOneRestriction m c := by
    rw [DFunLike.ext_iff, DFunLike.ext_iff]
    refine forall_congr' fun x => ?_
    change (e * inv) x = 1 ↔ e x = c x
    rw [hdiv, div_eq_one_iff_eq (hc x)]
  constructor
  · intro hd
    let : CompactSpace m.ker :=
      isCompact_iff_compactSpace.mp (hm.isCompact_preimage (isCompact_singleton (x := 1)))
    have hopen : IsOpen {e | normOneRestriction m e = normOneRestriction m c} := by
      have ho := isOpen_singleton_one_complex.preimage
        ((normOneRestriction m).continuous.comp (htranslate inv))
      convert ho using 1
      ext e
      exact (hrestrict e).symm
    exact IsClopen.connectedComponent_subset
      ⟨isClosed_eq (normOneRestriction m).continuous continuous_const, hopen⟩ rfl hd
  · intro hd
    -- The ratio is trivial on the kernel and descends to the closed norm image.
    let q := d * inv
    have hq (x : m.ker) : q x = 1 := DFunLike.congr_fun ((hrestrict d).mpr hd) x
    let r : G →ₜ* m.range :=
      ⟨m.rangeRestrict, hm.continuous.subtype_mk fun x => ⟨x, rfl⟩⟩
    have hr : IsQuotientMap r :=
      (hm.isClosedMap.codRestrict (s := (m.range : Set ℝ≥0ˣ)) fun x => ⟨x, rfl⟩).isQuotientMap
        r.continuous m.rangeRestrict_surjective
    have hqKer : m.ker ≤ q.toMonoidHom.ker := fun x hx => hq ⟨x, hx⟩
    let qLift := (QuotientGroup.lift m.ker q.toMonoidHom hqKer).comp
      (QuotientGroup.quotientKerEquivRange m).symm.toMonoidHom
    have hqLift (x : G) : qLift (r x) = q x := by
      change
        QuotientGroup.lift m.ker q.toMonoidHom hqKer ((QuotientGroup.quotientKerEquivRange m).symm
          ((QuotientGroup.quotientKerEquivRange m) (QuotientGroup.mk x))) = q.toMonoidHom x
      rw [MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]
    have hqCont : Continuous qLift := hr.continuous_iff.mpr (by
      rw [show (qLift : m.range → ℂ) ∘ r = q from funext hqLift]
      exact q.continuous)
    have : Nontrivial m.range := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨r x, 1, fun he => hx (congrArg Subtype.val he)⟩⟩
    obtain ⟨f, hf, hf0, hf1⟩ :=
      exists_quasiCharacter_deformation m.range hm.isClosed_range ⟨qLift, hqCont⟩
    let p (t : ℝ) : QuasiCharacter G := (f t).comp r * c
    have hp : Continuous p := (htranslate c).comp (r.continuous_comp_left.comp hf)
    have hp0 : p 0 = c := by
      ext1 x
      simp [p, hf0, ContinuousMonoidHom.mul_apply]
    have hp1 : p 1 = d := by
      ext1 x
      change f 1 (r x) * c x = d x
      rw [hf1]
      change qLift (r x) * c x = d x
      rw [hqLift, hdiv, div_mul_cancel₀ _ (hc x)]
    exact (isPreconnected_range hp).subset_connectedComponent
      ⟨0, hp0⟩ ⟨1, hp1⟩

/-- Paper: Equation (3.1.1.1), p. 119. The restrictions to the norm-one subgroup are
exactly its unitary characters. In particular every such character lifts. -/
theorem range_normOneRestriction [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Set.range (normOneRestriction m) = Set.range (fun χ : PontryaginDual m.ker =>
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) := by
  let : CompactSpace m.ker :=
    isCompact_iff_compactSpace.mp (hm.isCompact_preimage (isCompact_singleton (x := 1)))
  apply Set.Subset.antisymm
  · rintro _ ⟨c, rfl⟩
    let q := normOneRestriction m c
    obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty (α := m.ker))
      q.continuous.norm.continuousOn
    have hmax (y : m.ker) : ‖q y‖ ≤ ‖q x‖ := isMaxOn_univ_iff.mp hx y
    have hpos : 0 < ‖q x‖ := zero_lt_one.trans_le (by simpa using hmax 1)
    have hsq := hmax (x * x)
    rw [map_mul, norm_mul] at hsq
    have hle (y : m.ker) : ‖q y‖ ≤ 1 :=
      (hmax y).trans ((mul_le_iff_le_one_right hpos).mp hsq)
    have hnorm (y : m.ker) : ‖q y‖ = 1 := by
      have h := hle y⁻¹
      rw [map_inv, norm_inv] at h
      exact (hle y).antisymm ((inv_le_one₀ (norm_pos_iff.mpr
        ((Group.isUnit y).map q).ne_zero)).mp h)
    let χ : PontryaginDual m.ker :=
      { toFun := fun y => ⟨q y, mem_sphere_zero_iff_norm.mpr (hnorm y)⟩
        map_one' := Circle.ext (map_one q)
        map_mul' := fun y z => Circle.ext (map_mul q y z)
        continuous_toFun := q.continuous.subtype_mk _ }
    exact ⟨χ, ContinuousMonoidHom.ext fun _ => rfl⟩
  · rintro _ ⟨χ, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g, 1 < m g := by
      obtain ⟨g, hg⟩ := hne
      rcases lt_or_gt_of_ne hg with h | h
      · exact ⟨g⁻¹, by simpa only [map_inv, one_lt_inv'] using h⟩
      · exact ⟨g, h⟩
    have := nonnegRealUnits_orderTopology_and_compactIccSpace.1
    have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
    let Z := Subgroup.zpowers g
    -- The module embeds this cyclic subgroup into a discrete subgroup of the positive reals.
    have hmZ : Set.InjOn m (Z : Set G) := by
      intro x hx y hy h
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact congrArg (g ^ ·) ((zpow_right_strictMono hg).injective (by simpa only [map_zpow] using h))
    let : DiscreteTopology (Z.map m) := by
      change DiscreteTopology ((Subgroup.zpowers g).map m)
      rw [MonoidHom.map_zpowers]
      exact Subgroup.isCyclic_iff_discreteTopology.mp inferInstance
    let : DiscreteTopology Z := .of_continuous_injective
      (f := m.subgroupMap Z) ((hm.continuous.comp continuous_subtype_val).subtype_mk _)
      (fun x y h => Subtype.ext (hmZ x.property y.property (congrArg Subtype.val h)))
    let : IsClosed (Z : Set G) := Subgroup.isClosed_of_discreteTopology
    let p : G →ₜ* G ⧸ Z := ⟨QuotientGroup.mk' Z, QuotientGroup.continuous_mk⟩
    -- Each quotient class has a representative with module between one and `m g`.
    have huniv : p '' (m ⁻¹' Set.Icc 1 (m g)) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' hg (m y)
      refine ⟨y / g ^ n, ?_, ?_⟩
      · change m (y / g ^ n) ∈ Set.Icc 1 (m g)
        simpa only [map_div, map_zpow, Set.mem_Icc] using ⟨hn.1, hn.2.le⟩
      · have hpow : p (g ^ n) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers g n)
        rw [map_div, hpow, div_one]
        rfl
    let : CompactSpace (G ⧸ Z) := isCompact_univ_iff.mp
      (huniv ▸ (hm.isCompact_preimage isCompact_Icc).image p.continuous)
    let i : m.ker →ₜ* G := ⟨m.ker.subtype, continuous_subtype_val⟩
    have hi : Injective (p.comp i) := by
      apply (MonoidHom.ker_eq_bot_iff (p.comp i).toMonoidHom).mp
      apply le_antisymm ?_ bot_le
      intro x hx
      have hxZ : (x : G) ∈ Z := (QuotientGroup.eq_one_iff _).mp hx
      exact Subgroup.mem_bot.mpr (Subtype.ext (hmZ hxZ Z.one_mem (x.property.trans (map_one m).symm)))
    obtain ⟨ψ, hψ⟩ := exists_pontryaginDual_extension_of_compact (p.comp i) hi χ
    let coeCircle : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    exact ⟨(coeCircle.comp ψ).comp p,
      ContinuousMonoidHom.ext fun x => congrArg (fun z : Circle => (z : ℂ)) (hψ x)⟩

/-- Paper: §3.1.1, p. 119. Near each quasi-character the complex exponent is a coordinate
centered at zero. Its inverse sends z to the character twisted by the z-th power of the module. -/
def HasNormTwistCharts : Prop :=
  ∀ c : QuasiCharacter G, ∃ e : OpenPartialHomeomorph (QuasiCharacter G) ℂ,
    c ∈ e.source ∧ e c = 0 ∧
      ∀ z ∈ e.target, ∀ g, e.symm z g = c g * (modℝ g : ℂ) ^ z

/-- A quasi-character trivial at an element of module greater than one is trivial
if its values stay in the open unit ball about one on the corresponding norm interval. -/
private theorem quasiCharacter_eq_one_of_normInterval {g : G}
    (hK : IsCompact (m ⁻¹' Set.Icc 1 (m g)))
    (hg : 1 < m g) (q : QuasiCharacter G) (hqg : q g = 1)
    (hq : Set.MapsTo q (m ⁻¹' Set.Icc 1 (m g)) (Metric.ball 1 1)) : q = 1 := by
  let K := m ⁻¹' Set.Icc 1 (m g)
  -- Multiplying by powers of g moves any element into K without changing its value.
  have himage : Set.range (q : G → ℂ) = q '' K := by
    refine Set.Subset.antisymm (Set.range_subset_iff.mpr fun y => ?_) (Set.image_subset_range _ _)
    obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' hg (m y)
    refine ⟨y / g ^ n, ?_, by rw [map_div, map_zpow, hqg, one_zpow, div_one]⟩
    simpa only [K, Set.mem_preimage, map_div, map_zpow, Set.mem_Icc] using ⟨hn.1, hn.2.le⟩
  have heq := monoidHom_eq_one_of_compact_range_subset_ball q.toMonoidHom
    (himage ▸ hK.image q.continuous) (himage ▸ hq.image_subset)
  exact ContinuousMonoidHom.ext fun x => DFunLike.congr_fun heq x

/-- Paper: §3.1.1, p. 119. Every modulated group admits local norm-twist coordinates,
including when the complex exponent is defined globally only modulo a period. -/
theorem hasNormTwistCharts_of_proper [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) : HasNormTwistCharts m := by
  intro c
  obtain ⟨g, hg⟩ : ∃ g, 1 < m g := by
    obtain ⟨g, hg⟩ := hne
    rcases lt_or_gt_of_ne hg with h | h
    · exact ⟨g⁻¹, by simpa only [map_inv, one_lt_inv'] using h⟩
    · exact ⟨g, h⟩
  have hpos (x : G) : 0 < modℝ x :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)
  let L (x : G) : ℂ := Real.log (modℝ x)
  have hLg : L g ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.log_ne_zero_of_pos_of_ne_one (hpos g) fun h =>
      hg.ne (Units.val_inj.mp (NNReal.coe_inj.mp h)).symm)
  have hL : Continuous L := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)).log
      fun x => (hpos x).ne')
  let twist (z : ℂ) : QuasiCharacter G :=
    c * { toFun := fun x => Complex.exp (L x * z)
          map_one' := by simp [L]
          map_mul' := by
            intro x y
            simp only [L, map_mul, Units.val_mul, NNReal.coe_mul,
              Real.log_mul (hpos x).ne' (hpos y).ne', Complex.ofReal_add, add_mul, Complex.exp_add]
          continuous_toFun := (hL.mul continuous_const).cexp }
  have htwist (z : ℂ) (x : G) : twist z x = c x * Complex.exp (L x * z) := rfl
  have htwist_cont : Continuous twist := by
    apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (c.continuous.comp continuous_snd).mul
      (((hL.comp continuous_snd).mul continuous_fst).cexp)
  have hneval (d : QuasiCharacter G) (x : G) : d x ≠ 0 := ((Group.isUnit x).map d).ne_zero
  -- Evaluation at g recovers the exponent using the principal logarithm.
  let ratio (d : QuasiCharacter G) : ℂ := d g / c g
  let expChart := Complex.expOpenPartialHomeomorph
  let coord (d : QuasiCharacter G) : ℂ := expChart.symm (ratio d) / L g
  let U := ratio ⁻¹' expChart.target
  let T := (L g * ·) ⁻¹' expChart.source
  have hratio : Continuous ratio := (continuous_eval_const g).div_const (c g)
  have hU : IsOpen U := expChart.open_target.preimage hratio
  have hcoord : ContinuousOn coord U :=
    (expChart.continuousOn_invFun.comp hratio.continuousOn (fun _ h => h)).div_const _
  have hscale (d : QuasiCharacter G) : L g * coord d = expChart.symm (ratio d) := by
    change L g * (expChart.symm (ratio d) / L g) = _
    rw [mul_comm, div_mul_cancel₀ _ hLg]
  let residual (d : QuasiCharacter G) :=
    d * (twist (coord d)).comp (ContinuousMonoidHom.inv G)
  have hresidual (d : QuasiCharacter G) (x : G) : residual d x = d x / twist (coord d) x := by
    change d x * twist (coord d) x⁻¹ = _
    rw [map_inv, div_eq_mul_inv]
  have hresidual_cont : ContinuousOn (fun d => (residual d).toContinuousMap) U := by
    have hforget : Continuous (ContinuousMonoidHom.toContinuousMap : QuasiCharacter G → C(G, ℂ)) :=
      (ContinuousMonoidHom.isInducing_toContinuousMap _ _).continuous
    have hinv := (ContinuousMonoidHom.inv G).continuous_comp_left (C := ℂ)
    exact hforget.continuousOn.mul
      ((hforget.comp hinv).comp_continuousOn' (htwist_cont.comp_continuousOn' hcoord))
  -- On the chart source the residual stays close to one on a compact norm interval.
  let K := m ⁻¹' Set.Icc 1 (m g)
  let V : Set C(G, ℂ) := {f | Set.MapsTo f K (Metric.ball 1 1)}
  let S := U ∩ (fun d => (residual d).toContinuousMap) ⁻¹' V
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
  have hK : IsCompact K := hm.isCompact_preimage isCompact_Icc
  have hS : IsOpen S := hresidual_cont.isOpen_inter_preimage hU
    (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball)
  have hratio_twist (z : ℂ) : ratio (twist z) = expChart (L g * z) := by
    change twist z g / c g = Complex.exp (L g * z)
    rw [htwist, mul_div_cancel_left₀ _ (hneval c g)]
  have hright (z : ℂ) (hz : z ∈ T) : coord (twist z) = z := by
    change expChart.symm (ratio (twist z)) / L g = z
    rw [hratio_twist, expChart.left_inv hz, mul_div_cancel_left₀ _ hLg]
  have hleft (d : QuasiCharacter G) (hd : d ∈ S) : twist (coord d) = d := by
    have hrg : residual d g = 1 := by
      have hval : twist (coord d) g = d g := by
        rw [htwist, hscale]
        change c g * expChart (expChart.symm (ratio d)) = d g
        rw [expChart.right_inv hd.1, mul_comm]
        exact div_mul_cancel₀ _ (hneval c g)
      rw [hresidual, hval, div_self (hneval d g)]
    have h := quasiCharacter_eq_one_of_normInterval m hK hg (residual d) hrg hd.2
    ext1 x
    have hx : residual d x = 1 := DFunLike.congr_fun h x
    exact ((div_eq_one_iff_eq (hneval _ x)).mp (hresidual d x ▸ hx)).symm
  let e : OpenPartialHomeomorph (QuasiCharacter G) ℂ := {
    toFun := coord
    invFun := twist
    source := S
    target := T
    map_source' d hd := by
      change L g * coord d ∈ expChart.source
      rw [hscale]
      exact expChart.map_target hd.1
    map_target' z hz := by
      refine ⟨?_, ?_⟩
      · change ratio (twist z) ∈ expChart.target
        rw [hratio_twist]
        exact expChart.map_source hz
      · intro x _
        change residual (twist z) x ∈ Metric.ball 1 1
        rw [hresidual, hright z hz, div_self (hneval _ x)]
        exact Metric.mem_ball_self zero_lt_one
    left_inv' := hleft
    right_inv' := hright
    open_source := hS
    open_target := expChart.open_source.preimage (continuous_const.mul continuous_id)
    continuousOn_toFun := hcoord.mono Set.inter_subset_left
    continuousOn_invFun := htwist_cont.continuousOn }
  have hzero : (0 : ℂ) ∈ T := by
    change L g * 0 ∈ expChart.source
    simp [expChart, Complex.expOpenPartialHomeomorph, Real.pi_pos]
  have htwist_zero : twist 0 = c := by
    ext1 x
    simp [htwist]
  refine ⟨e, htwist_zero ▸ e.map_target hzero, ?_, fun z _ x => ?_⟩
  · change coord c = 0
    rw [← htwist_zero, hright 0 hzero]
  · change twist z x = _
    rw [htwist, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos x).ne'),
      ← Complex.ofReal_log (hpos x).le]

/-- Paper: §3.1.1, p. 119. Choose one norm-twist chart around each point. These charts form
an atlas on the existing compact-open space. -/
@[instance_reducible] def quasiCharacterChartedSpace (h : HasNormTwistCharts m) :
    ChartedSpace ℂ (QuasiCharacter G) where
  atlas := Set.range fun c => (h c).choose
  chartAt c := (h c).choose
  mem_chart_source c := (h c).choose_spec.1
  chart_mem_atlas c := ⟨c, rfl⟩

/-- Paper: §3.1.1, p. 119. The atlas of complex norm-twist coordinates is analytic. -/
theorem quasiCharacter_isManifold (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    IsManifold 𝓘(ℂ) ω (QuasiCharacter G) := by
  let := quasiCharacterChartedSpace m h
  apply isManifold_of_contDiffOn
  intro e e' he he'
  change e ∈ Set.range (fun c => (h c).choose) at he
  change e' ∈ Set.range (fun c => (h c).choose) at he'
  obtain ⟨c, rfl⟩ := he
  obtain ⟨d, rfl⟩ := he'
  let e := (h c).choose
  let e' := (h d).choose
  have hc := (h c).choose_spec.2.2
  have hd := (h d).choose_spec.2.2
  change ContDiffOn ℂ ω (e.symm.trans e') ((e.symm.trans e').source ∩ Set.range id)
  rw [Set.range_id, Set.inter_univ]
  intro z hz
  have hz' : z ∈ e.target ∧ e.symm z ∈ e'.source := by
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] using hz
  let w := e' (e.symm z)
  have hw : w ∈ e'.target := e'.map_source hz'.2
  have hbase (g : G) : c g * (modℝ g : ℂ) ^ z = d g * (modℝ g : ℂ) ^ w := by
    rw [← hc z hz'.1 g, ← hd w hw g]
    exact congrArg (fun q : QuasiCharacter G => q g) (e'.left_inv hz'.2).symm
  -- Adding the same increment to both coordinates twists both characters by the same power.
  let translate (y : ℂ) := w + (y - z)
  have hsmooth : ContDiff ℂ ω translate := contDiff_const.add (contDiff_id.sub contDiff_const)
  have hnear : translate ⁻¹' e'.target ∈ 𝓝 z :=
    (e'.open_target.preimage hsmooth.continuous).mem_nhds (by simpa [translate] using hw)
  refine hsmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ hz
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hnear]
    with y hy htranslate
  have hy' : y ∈ e.target := by
    rw [OpenPartialHomeomorph.trans_source] at hy
    exact hy.1
  have heq : e.symm y = e'.symm (translate y) := by
    ext1 g
    have hmod : (modℝ g : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
    rw [hc y hy' g, hd (translate y) htranslate g]
    change c g * (modℝ g : ℂ) ^ y = d g * (modℝ g : ℂ) ^ (w + (y - z))
    rw [Complex.cpow_add _ _ hmod, ← mul_assoc, ← hbase g, mul_assoc,
      ← Complex.cpow_add _ _ hmod, show z + (y - z) = y by abel]
  change e' (e.symm y) = translate y
  rw [heq, e'.right_inv htranslate]

/-- Pullback along a modulus-preserving homomorphism is a local analytic isomorphism
in the norm-twist atlases. In coordinates at a character and its pullback it is the identity. -/
theorem quasiCharacter_comp_isLocalDiffeomorph {H : Type*} [CommGroup H] [TopologicalSpace H]
    (n : H →* ℝ≥0ˣ) (i : H →ₜ* G) (hi : ∀ x, m (i x) = n x)
    (hG : HasNormTwistCharts m) (hH : HasNormTwistCharts n) :
    letI := quasiCharacterChartedSpace m hG
    letI := quasiCharacterChartedSpace n hH
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (fun c : QuasiCharacter G ↦ c.comp i) := by
  let := quasiCharacterChartedSpace m hG
  let := quasiCharacterChartedSpace n hH
  let := quasiCharacter_isManifold m hG
  let := quasiCharacter_isManifold n hH
  apply isLocalDiffeomorph_of_chartAt 𝓘(ℂ) ω
  · intro c
    let d := c.comp i
    let a := (hG c).choose
    let b := (hH d).choose
    change a c ∈ b.target
    rw [show a c = b d from (hG c).choose_spec.2.1.trans (hH d).choose_spec.2.1.symm]
    exact b.map_source (hH d).choose_spec.1
  · intro c y hy hz
    let d := c.comp i
    let a := (hG c).choose
    let b := (hH d).choose
    ext1 x
    change y (i x) = b.symm (a y) x
    rw [(hH d).choose_spec.2.2 (a y) hz x]
    change y (i x) = c (i x) * (((n x : ℝ≥0) : ℝ) : ℂ) ^ (a y)
    rw [← hi x]
    exact (congrArg (fun q : QuasiCharacter G ↦ q (i x)) (a.left_inv hy)).symm.trans
      ((hG c).choose_spec.2.2 _ (a.map_source hy) (i x))

/-- Paper: Definition 3.1.1.1, p. 119. The abscissa is the real exponent in the modulus of
a quasi-character. We evaluate the ratio of logarithms at a point where the module differs from one.
Deviation: This formula computes (3.1.1.2) without choosing a unitary base-point. -/
def quasiCharacterAbscissa (_hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) : ℝ :=
  Real.log ‖c hne.choose‖ / Real.log (modℝ hne.choose)

/-- Paper: Equation (3.1.1.2), p. 119. Twisting any unitary character by the s-th power
of the module gives a quasi-character of abscissa Re(s). -/
theorem quasiCharacterAbscissa_of_unitary_twist (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (χ : PontryaginDual G) (s : ℂ)
    (hc : ∀ g, c g = (χ g : ℂ) * (modℝ g : ℂ) ^ s) :
    quasiCharacterAbscissa m hm hne c = s.re := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  change Real.log ‖c g‖ / Real.log (modℝ g) = s.re
  rw [hc g, norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hmod,
    Real.log_rpow hmod, mul_div_cancel_right₀ _ hlog]

/-- Paper: Equation (3.1.1.2), p. 119. At every element of a modulated group, the modulus
of a quasi-character equals the module raised to its abscissa. -/
theorem norm_quasiCharacter_eq_rpow_abscissa [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (g : G) :
    ‖c g‖ = (modℝ g) ^ quasiCharacterAbscissa m hm hne c := by
  let s := quasiCharacterAbscissa m hm hne c
  have hmod (x : G) : 0 < modℝ x :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)
  have hnorm (x : G) : 0 < ‖c x‖ := norm_pos_iff.mpr ((Group.isUnit x).map c).ne_zero
  let q : G →ₜ* ℝ :=
    { toFun := fun x => ‖c x‖ / (modℝ x) ^ s
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, norm_mul, Units.val_mul, NNReal.coe_mul,
          Real.mul_rpow (hmod x).le (hmod y).le, mul_div_mul_comm]
      continuous_toFun := c.continuous.norm.div
        ((NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)).rpow
          continuous_const (fun x => Or.inl (hmod x).ne'))
        (fun x => (Real.rpow_pos_of_pos (hmod x) s).ne') }
  have hqpos (x : G) : 0 < q x := div_pos (hnorm x) (Real.rpow_pos_of_pos (hmod x) s)
  have hqbase : q hne.choose = 1 := by
    have hlog := Real.log_ne_zero_of_pos_of_ne_one (hmod hne.choose) fun h =>
      hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
    change ‖c hne.choose‖ / (modℝ hne.choose) ^ s = 1
    have hs := Real.rpow_pos_of_pos (hmod hne.choose) s
    apply (div_eq_one_iff_eq hs.ne').mpr
    apply Real.log_injOn_pos (hnorm hne.choose) hs
    rw [Real.log_rpow (hmod hne.choose)]
    exact (div_mul_cancel₀ _ hlog).symm
  obtain ⟨a, ha, hqa⟩ : ∃ a, 1 < m a ∧ q a = 1 := by
    rcases lt_or_gt_of_ne hne.choose_spec with h | h
    · exact ⟨hne.choose⁻¹, by simpa only [map_inv, one_lt_inv'] using h,
        by rw [map_inv, hqbase, inv_one]⟩
    · exact ⟨hne.choose, h, hqbase⟩
  have := nonnegRealUnits_orderTopology_and_compactIccSpace.2
  let K := m ⁻¹' Set.Icc 1 (m a)
  have hK : IsCompact K := hm.isCompact_preimage isCompact_Icc
  have hKone : (1 : G) ∈ K := by simp [K, ha.le]
  obtain ⟨x, -, hx⟩ := hK.exists_isMaxOn ⟨1, hKone⟩ q.continuous.continuousOn
  -- Multiplying by powers of a moves every point into K and preserves its q-value.
  have hmax (y : G) : q y ≤ q x := by
    obtain ⟨n, hn, -⟩ := existsUnique_zpow_near_of_one_lt' ha (m y)
    have hy : y / a ^ n ∈ K := by
      simpa only [K, Set.mem_preimage, Set.mem_Icc, map_div, map_zpow] using ⟨hn.1, hn.2.le⟩
    have h := hx hy
    change q (y / a ^ n) ≤ q x at h
    simpa only [map_div, map_zpow, hqa, one_zpow, div_one] using h
  have hsq := hmax (x * x)
  rw [map_mul] at hsq
  have hle (y : G) : q y ≤ 1 := (hmax y).trans ((mul_le_iff_le_one_right (hqpos x)).mp hsq)
  have hinv := hle g⁻¹
  rw [map_inv] at hinv
  have hqg : q g = 1 := (hle g).antisymm ((inv_le_one₀ (hqpos g)).mp hinv)
  exact (div_eq_one_iff_eq (Real.rpow_pos_of_pos (hmod g) s).ne').mp hqg

/-- Paper: Equation (3.1.1.2), p. 119. The abscissa is continuous in the compact-open topology. -/
theorem continuous_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Continuous (quasiCharacterAbscissa m hm hne) := by
  have hev : Continuous (fun c : QuasiCharacter G => c hne.choose) := continuous_eval_const _
  have hneval (c : QuasiCharacter G) : c hne.choose ≠ 0 :=
    ((Group.isUnit hne.choose).map c).ne_zero
  exact (hev.norm.log fun c => norm_ne_zero_iff.mpr (hneval c)).div_const _

/-- Paper: Equation (3.1.1.2), p. 119. Every real number occurs as an abscissa. -/
theorem surjective_quasiCharacterAbscissa (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) :
    Surjective (quasiCharacterAbscissa m hm hne) := by
  intro r
  let n := (Units.coeHom ℝ≥0).comp m
  let f := Complex.ofRealHom.toMonoidHom.comp
    (NNReal.toRealHom.toMonoidHom.comp ((NNReal.rpowMonoidHom r).comp n))
  have hc : Continuous f := Complex.continuous_ofReal.comp
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp hm.continuous)).rpow continuous_const
      (fun g ↦ Or.inl (NNReal.coe_ne_zero.mpr (m g).ne_zero)))
  let c : QuasiCharacter G := ⟨f, hc⟩
  refine ⟨c, quasiCharacterAbscissa_of_unitary_twist m hm hne c 1 (r : ℂ) ?_⟩
  intro g
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul]
  exact Complex.ofReal_cpow (NNReal.coe_nonneg _) r

/-- Paper: Definition 3.1.1.2(1), p. 119. The relative vertical strip over an interval is
the inverse image under the abscissa, with the topology inherited on its subtype.
Deviation: The same inverse image is defined for every real set. -/
def relativeVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    Set (QuasiCharacter G) :=
  quasiCharacterAbscissa m hm hne ⁻¹' I

/-- Paper: Definition 3.1.1.2(2), p. 119. The relative right half-plane has abscissa
strictly larger than its boundary. -/
def relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    TopologicalSpace.Opens (QuasiCharacter G) :=
  ⟨relativeVerticalStrip m hm hne (Set.Ioi a),
    isOpen_Ioi.preimage (continuous_quasiCharacterAbscissa m hm hne)⟩

/-- Paper: Definition 3.1.1.2(3), p. 119. The strip in the component indexed by ω also
requires the restriction of the quasi-character to the norm-one subgroup to equal ω. -/
def componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (χ : PontryaginDual m.ker) (I : Set ℝ) : Set (QuasiCharacter G) :=
  relativeVerticalStrip m hm hne I ∩ {c | ∀ g : m.ker, normOneRestriction m c g = (χ g : ℂ)}

/-- Paper: Definition 3.1.1.2(2), p. 119. The trivial character lies in the relative
right half-plane precisely when its boundary is strictly negative. -/
theorem one_mem_relativeRightHalfPlane (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (a : ℝ) :
    1 ∈ relativeRightHalfPlane m hm hne a ↔ a < 0 := by
  change a < quasiCharacterAbscissa m hm hne 1 ↔ a < 0
  simp [quasiCharacterAbscissa]

/-- Paper: Definition 3.1.1.2, p. 119. The trivial character belongs to the strip in
the trivial component exactly when the interval contains zero. -/
theorem one_mem_componentVerticalStrip (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1) (I : Set ℝ) :
    1 ∈ componentVerticalStrip m hm hne 1 I ↔ 0 ∈ I := by
  simp [componentVerticalStrip, relativeVerticalStrip, quasiCharacterAbscissa, normOneRestriction]

/-- Paper: Equation (3.1.1.4), p. 119. The dual quasi-character is the module times
the inverse character, evaluated by composing the original character with inversion. -/
def dualQuasiCharacter [IsTopologicalGroup G] (hm : Continuous m) (c : QuasiCharacter G) :
    QuasiCharacter G :=
  let n : QuasiCharacter G :=
    ⟨Complex.ofRealHom.toMonoidHom.comp (NNReal.toRealHom.toMonoidHom.comp
      ((Units.coeHom ℝ≥0).comp m)),
      Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hm))⟩
  n * c.comp (ContinuousMonoidHom.inv G)

/-- Paper: Equation (3.1.1.4), p. 119. Duality reflects the abscissa in the line σ = 1/2. -/
theorem quasiCharacterAbscissa_dual [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (c : QuasiCharacter G) :
    quasiCharacterAbscissa m hm hne (dualQuasiCharacter m hm.continuous c) =
      1 - quasiCharacterAbscissa m hm hne c := by
  let g := hne.choose
  have hmod : 0 < modℝ g := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hmod_one : modℝ g ≠ 1 := fun h =>
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hmod hmod_one
  have hnorm : ‖c g‖ ≠ 0 := norm_ne_zero_iff.mpr ((Group.isUnit g).map c).ne_zero
  change Real.log ‖(modℝ g : ℂ) * c (g⁻¹)‖ / Real.log (modℝ g) =
    1 - Real.log ‖c g‖ / Real.log (modℝ g)
  rw [map_inv, ← div_eq_mul_inv, norm_div, Complex.norm_of_nonneg hmod.le,
    Real.log_div hmod.ne' hnorm, sub_div, div_self hlog]

/-- Applying the module-times-inverse duality twice recovers the original quasi-character. -/
theorem dualQuasiCharacter_involutive [IsTopologicalGroup G] (hm : Continuous m) :
    Function.Involutive (dualQuasiCharacter m hm) := by
  intro c
  ext1 g
  change (modℝ g : ℂ) * dualQuasiCharacter m hm c g⁻¹ = c g
  rw [map_inv]
  change (modℝ g : ℂ) * ((modℝ g : ℂ) * c g⁻¹)⁻¹ = c g
  rw [map_inv]
  have hn := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (m g).ne_zero)
  field_simp [hn, ((Group.isUnit g).map c).ne_zero]

open Filter in
/-- Paper: Equation (3.1.1.4), p. 119. The duality map is an analytic automorphism and
serves as its own inverse. -/
theorem dualQuasiCharacter_analyticEquiv [IsTopologicalGroup G] (hm : Continuous m)
    (h : HasNormTwistCharts m) :
    letI := quasiCharacterChartedSpace m h
    ∃ e : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (QuasiCharacter G) (QuasiCharacter G) ω,
      (∀ c, e c = dualQuasiCharacter m hm c) ∧ ∀ c, e.symm c = dualQuasiCharacter m hm c := by
  let := quasiCharacterChartedSpace m h
  let D := dualQuasiCharacter m hm
  have hD (c : QuasiCharacter G) (g : G) : D c g = (modℝ g : ℂ) / c g := by
    change (modℝ g : ℂ) * c g⁻¹ = _
    rw [map_inv, div_eq_mul_inv]
  have hinv : Function.Involutive D := dualQuasiCharacter_involutive m hm
  have hsmooth : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω D := by
    intro c
    let a := (h c).choose
    let b := (h (D c)).choose
    obtain ⟨ha, ha0, htwist⟩ := (h c).choose_spec
    obtain ⟨hb, hb0, hdual⟩ := (h (D c)).choose_spec
    have ht : -(a c) ∈ b.target := by
      change -((h c).choose c) ∈ b.target
      rw [ha0, neg_zero, ← hb0]
      exact b.map_source hb
    have hnear : ∀ᶠ z in 𝓝 (a c), z ∈ a.target ∧ -z ∈ b.target := by
      filter_upwards [a.open_target.mem_nhds (a.map_source ha),
        continuous_neg.continuousAt.preimage_mem_nhds (b.open_target.mem_nhds ht)] with z hz hz'
      exact ⟨hz, hz'⟩
    -- Duality sends a twist by z to a twist by -z in the chart at the dual character.
    have hchart : D ∘ a.symm =ᶠ[𝓝 (a c)] b.symm ∘ Neg.neg := by
      filter_upwards [hnear] with z hz
      ext1 g
      change D (a.symm z) g = b.symm (-z) g
      rw [hD, htwist z hz.1 g, hdual (-z) hz.2 g, hD, Complex.cpow_neg]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    apply contMDiffAt_iff.mpr
    constructor
    · apply (a.symm.continuousAt_iff_continuousAt_comp_right ha).mpr
      exact ((b.continuousAt_symm ht).comp continuous_neg.continuousAt).congr_of_eventuallyEq hchart
    · change ContDiffWithinAt ℂ ω (b ∘ D ∘ a.symm) (Set.range id) (a c)
      apply ContDiffAt.contDiffWithinAt
      apply (contDiff_neg.contDiffAt : ContDiffAt ℂ ω Neg.neg (a c)).congr_of_eventuallyEq
      filter_upwards [hchart, hnear] with z he hz
      exact (congrArg b he).trans (b.right_inv hz.2)
  exact ⟨{
    toFun := D
    invFun := D
    left_inv := hinv
    right_inv := hinv
    contMDiff_toFun := hsmooth
    contMDiff_invFun := hsmooth }, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Paper: Following Equation (3.1.1.4), p. 119. Duality exchanges the components
indexed by a norm-one character and its complex conjugate. -/
theorem dualQuasiCharacter_image_component [IsTopologicalGroup G] (hm : IsProperMap m)
    (hne : ∃ g, m g ≠ 1) (χ : PontryaginDual m.ker) :
    dualQuasiCharacter m hm.continuous '' componentVerticalStrip m hm hne χ Set.univ =
      componentVerticalStrip m hm hne χ⁻¹ Set.univ := by
  let D := dualQuasiCharacter m hm.continuous
  have hmap (ψ : PontryaginDual m.ker) {c : QuasiCharacter G}
      (hc : c ∈ componentVerticalStrip m hm hne ψ Set.univ) :
      D c ∈ componentVerticalStrip m hm hne ψ⁻¹ Set.univ := by
    refine ⟨Set.mem_univ _, fun g ↦ ?_⟩
    have hg : m (g : G) = 1 := g.property
    change (↑((m (g : G) : ℝ≥0) : ℝ) : ℂ) * c ((g : G)⁻¹) = ((ψ⁻¹ g : Circle) : ℂ)
    have hcg : c (g : G) = (ψ g : ℂ) := hc.2 g
    rw [hg, map_inv, hcg]
    change (1 : ℂ) * (ψ g : ℂ)⁻¹ = (((ψ g)⁻¹ : Circle) : ℂ)
    simp
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact hmap χ hd
  · intro hc
    exact ⟨D c, by simpa using hmap χ⁻¹ hc, dualQuasiCharacter_involutive m hm.continuous c⟩

end Generalities

section SplitCharacters

local notation "valℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)

/-- The exponent of a positive-real character varies continuously in the compact-open topology. -/
private theorem continuous_complexPowerExponent :
    Continuous fun c : ℝ≥0ˣ →ₜ* ℂ ↦ (existsUnique_complexPower c).choose := by
  let m := MonoidHom.id ℝ≥0ˣ
  have hm : IsProperMap m := isProperMap_id
  have hne : ∃ t, m t ≠ 1 := ⟨Units.mk0 2 (by norm_num), fun he ↦ by
    have h := congrArg (fun u : ℝ≥0ˣ ↦ ((u : ℝ≥0) : ℝ)) he
    norm_num [m] at h⟩
  apply continuous_iff_continuousAt.mpr
  intro c
  obtain ⟨e, hc, -, he⟩ := hasNormTwistCharts_of_proper m hm hne c
  apply (continuousAt_const.add (e.continuousAt hc) :
    ContinuousAt (fun d ↦ (existsUnique_complexPower c).choose + e d) c).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hc] with d hd
  symm
  change _ + e d = _
  apply (existsUnique_complexPower d).choose_spec.2
  intro t
  have hv := he (e d) (e.map_source hd) t
  rw [e.left_inv hd] at hv
  rw [hv, (existsUnique_complexPower c).choose_spec.1 t,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr t.ne_zero))]
  rfl

/-- A continuous splitting determines both coordinates of a character, by restriction to
the positive real section and to the compact norm-one subgroup. -/
theorem quasiCharacterParametrization_of_split {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] (m : G →* ℝ≥0ˣ) (hm : Continuous m)
    [CompactSpace m.ker] (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m) :
    ∃ e : QuasiCharacter G ≃ₜ (ℂ × PontryaginDual m.ker), ∀ c,
      (∀ t, c (σ t) = (valℝ t : ℂ) ^ (e c).1) ∧
        ∀ u : m.ker, ((e c).2 u : ℂ) = c u.val := by
  have hrker (g : G) : g / σ (m g) ∈ m.ker := by
    simp [MonoidHom.mem_ker, hσ (m g)]
  let r : G →ₜ* m.ker :=
    { toFun := fun g ↦ ⟨g / σ (m g), hrker g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (σ.continuous.comp hm)).subtype_mk hrker }
  have hrσ (t : ℝ≥0ˣ) : r (σ t) = 1 := by
    apply Subtype.ext
    change σ t / σ (m (σ t)) = 1
    simp [hσ t]
  have hru (u : m.ker) : r u = u := by
    apply Subtype.ext
    change _ / σ (m u) = _
    rw [u.prop, map_one, div_one]
  let exponent (c : QuasiCharacter G) := (existsUnique_complexPower (c.comp σ)).choose
  have hrad (c : QuasiCharacter G) (t : ℝ≥0ˣ) : c (σ t) = (valℝ t : ℂ) ^ exponent c :=
    (existsUnique_complexPower (c.comp σ)).choose_spec.1 t
  have hnorm (c : QuasiCharacter G) (u : m.ker) : ‖c (u : G)‖ = 1 := by
    obtain ⟨B, hB⟩ := (isCompact_range (c.continuous.norm.comp
      (continuous_subtype_val (p := fun g ↦ g ∈ m.ker)))).bddAbove
    have hle (v : m.ker) : ‖c (v : G)‖ ≤ 1 := by
      by_contra! h
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B h
      have hb := hB (Set.mem_range_self (v ^ k))
      change ‖c ((v : G) ^ k)‖ ≤ B at hb
      rw [map_pow, norm_pow] at hb
      exact hk.not_ge hb
    refine (hle u).antisymm ?_
    have h := hle u⁻¹
    rw [Subgroup.coe_inv, map_inv, norm_inv] at h
    exact (inv_le_one₀ (norm_pos_iff.mpr ((Group.isUnit _).map c).ne_zero)).mp h
  have hcircle (c : QuasiCharacter G) (u : m.ker) : c u ∈ Submonoid.unitSphere ℂ :=
    mem_sphere_zero_iff_norm.mpr (hnorm c u)
  let unitary (c : QuasiCharacter G) : PontryaginDual m.ker :=
    { toFun := fun u ↦ ⟨c u, hcircle c u⟩
      map_one' := Circle.ext (map_one c)
      map_mul' := fun u v ↦ Circle.ext (map_mul c _ _)
      continuous_toFun := (c.continuous.comp continuous_subtype_val).subtype_mk (hcircle c) }
  have hpos (g : G) : 0 < valℝ (m g) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)
  have hbase : Continuous (fun g ↦ (valℝ (m g) : ℂ)) :=
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (Units.continuous_val.comp hm))
  -- Reconstruct each character from its values on the two factors.
  let assemble (p : ℂ × PontryaginDual m.ker) : QuasiCharacter G :=
    { toFun := fun g ↦ (p.2 (r g) : ℂ) * (valℝ (m g) : ℂ) ^ p.1
      map_one' := by simp
      map_mul' := fun g h ↦ by
        simp only [map_mul, Circle.coe_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg (hpos g).le (hpos h).le]
        ring
      continuous_toFun := (continuous_subtype_val.comp (p.2.continuous.comp r.continuous)).mul
        (hbase.cpow continuous_const fun g ↦ Or.inl (hpos g)) }
  have hσval (p : ℂ × PontryaginDual m.ker) (t : ℝ≥0ˣ) :
      assemble p (σ t) = (valℝ t : ℂ) ^ p.1 := by
    change (p.2 (r (σ t)) : ℂ) * (valℝ (m (σ t)) : ℂ) ^ p.1 = _
    rw [hrσ, hσ, map_one, Circle.coe_one, one_mul]
  have huval (p : ℂ × PontryaginDual m.ker) (u : m.ker) :
      assemble p u = (p.2 u : ℂ) := by
    change (p.2 (r u) : ℂ) * (valℝ (m u) : ℂ) ^ p.1 = _
    rw [hru, u.prop]
    simp
  refine ⟨{
    toFun := fun c ↦ (exponent c, unitary c)
    invFun := assemble
    left_inv := fun c ↦ by
      ext1 g
      change c (g / σ (m g)) * (valℝ (m g) : ℂ) ^ exponent c = c g
      rw [← hrad, ← map_mul, div_mul_cancel]
    right_inv := fun p ↦ Prod.ext
      ((existsUnique_complexPower ((assemble p).comp σ)).choose_spec.2 _ (hσval p)).symm (by
        ext1 u
        exact Circle.ext (huval p u))
    continuous_toFun := (continuous_complexPowerExponent.comp σ.continuous_comp_left).prodMk ?_
    continuous_invFun := ContinuousMonoidHom.continuous_of_continuous_uncurry assemble ?_ },
    fun c ↦ ⟨hrad c, fun _ ↦ rfl⟩⟩
  · apply ContinuousMonoidHom.continuous_of_continuous_uncurry
    exact (continuous_eval.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
        (fun p ↦ hcircle p.1 p.2)
  · have : ContinuousEval (PontryaginDual m.ker) m.ker Circle :=
      inferInstanceAs (ContinuousEval (m.ker →ₜ* Circle) m.ker Circle)
    exact (continuous_subtype_val.comp (continuous_eval.comp
      ((continuous_snd.comp continuous_fst).prodMk (r.continuous.comp continuous_snd)))).mul
      ((hbase.comp continuous_snd).cpow (continuous_fst.comp continuous_fst) fun p ↦
        Or.inl (hpos p.2))

end SplitCharacters

section Ideles

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

variable (S : Finset (Primes(F)))

/-- The image of the diagonal S-units in the S-ideles, by which `SIdeleQuotient` is taken.
Naming it keeps every elaborated term over the quotient and its instances small: spelled out,
the subgroup is copied into each instance argument, and goals grow to hundreds of millions of
nodes when unfolded, which `kabstract` (`rw`, `obtain`, `cases`, `generalize`) walks in full. -/
abbrev sProjectedDiagonal : Subgroup (SAdeleRing F S)ˣ :=
  Subgroup.map (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (MonoidHom.range (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))))

/-- The diagonal embedding of the S-units into the S-ideles, whose range is
`sProjectedDiagonal`. Named for the same reason: Chapters 2, 5 and 7 wrote it out through
`unitAtS` notations, so every instance argument over it carried a copy. -/
abbrev sUnitEmbedding : ((S : Set (Primes(F))).integer F)ˣ →* (SAdeleRing F S)ˣ :=
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection F S)
    (Subring.subtype (integralAdelesOutside F S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S)))

local notation "projectedDiagonal" => sProjectedDiagonal F S

/-- Paper: Equation (3.1.2.1), p. 120. The group J_{F,S} is the quotient of the S-ideles
by the projected diagonal S-units. As in §A.1, S specifies the finite places only. -/
abbrev SIdeleQuotient := (SAdeleRing F S)ˣ ⧸ projectedDiagonal

/-- Paper: Equation (3.1.2.1), p. 120. An S-idele represents the identity of J_{F,S}
precisely when it is the projection of a diagonal S-unit. -/
theorem sIdeleQuotient_mk_eq_one (g : (SAdeleRing F S)ˣ) :
    (QuotientGroup.mk g : SIdeleQuotient F S) = 1 ↔
      ∃ u : ((S : Set (Primes(F))).integer F)ˣ, g = Units.map
        ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom
        (Units.map (integralAdeleDiagonal F S).toMonoidHom u) := by
  rw [QuotientGroup.eq_one_iff, sProjectedDiagonal, MonoidHom.map_range, MonoidHom.mem_range]
  exact exists_congr fun _ ↦ eq_comm

/-- Paper: Equation (3.1.2.1), p. 120. The product of normalized absolute values in S
descends to J_{F,S} by the S-unit product formula. -/
def sIdeleQuotientNorm : SIdeleQuotient F S →* ℝ≥0ˣ :=
  QuotientGroup.lift _ (sIdeleNorm F S)
    (Subgroup.map_le_iff_le_comap.mpr (sIdeleNorm_spec F S).2)

/-- Paper: Equation (3.1.2.1), p. 120. The norm on J_{F,S} takes the S-idelic norm of
any representative. -/
theorem sIdeleQuotientNorm_mk (g : (SAdeleRing F S)ˣ) :
    sIdeleQuotientNorm F S (QuotientGroup.mk g) = sIdeleNorm F S g := by
  rfl

/-- Paper: §3.1.2.3, p. 121. The S-idelic norm admits a continuous homomorphic section,
as used to parametrize the components in (3.1.2.5). -/
theorem sIdeleQuotientNorm_exists_section :
    ∃ σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S, RightInverse σ (sIdeleQuotientNorm F S) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let q := QuotientGroup.mk' projectedDiagonal
  refine ⟨⟨q.comp (p.comp s), QuotientGroup.continuous_mk.comp
    (hp.comp (singlePlaceIdeleNormSection_continuous F w))⟩, fun t ↦ ?_⟩
  -- The chosen section has every finite coordinate equal to one.
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units :=
    ⟨hmem t, by
      change ((s t)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem t⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)

/-- Paper: §3.1.2, p. 120. The global idele class norm is a proper module. -/
theorem isProperMap_ideleClassNorm : IsProperMap (ideleClassNorm F) := by
  let n := ideleClassNorm F
  let : CompactSpace n.ker := (ideleClassGroup_finiteness F).2.1
  obtain ⟨_, _, _, _, _, _, _, _, hn, _, ⟨s, hs, hsn⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  let f (p : n.ker × ℝ≥0ˣ) := p.1.val * s p.2
  have hf : Continuous f := (continuous_subtype_val.comp continuous_fst).mul (hs.comp continuous_snd)
  have hcomp : n ∘ f = Prod.snd := by
    funext p
    change n (p.1.val * s p.2) = p.2
    rw [map_mul, MonoidHom.mem_ker.mp p.1.property, hsn, one_mul]
  apply isProperMap_of_comp_of_surj hf hn (hcomp ▸ isProperMap_snd_of_compactSpace)
  intro g
  refine ⟨(⟨g / s (n g), ?_⟩, n g), div_mul_cancel _ _⟩
  exact MonoidHom.mem_ker.mpr (by rw [map_div, hsn, div_self'])

/-- Forgetting the unit coordinates outside S induces an open quotient map on S-idele
classes, and this projection preserves the norm. -/
theorem sIdeleClassGroup_projection :
    ∃ π : SIdeleClassGroup F S →* SIdeleQuotient F S, IsOpenQuotientMap π ∧
      ∀ c, sIdeleQuotientNorm F S (π c) = sIdeleClassNorm F S c := by
  let A := integralAdelesOutside F S
  let p := Units.map ((adeleProjection F S).comp A.subtype).toMonoidHom
  let d := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  let π := QuotientGroup.map d (d.map p) p (Subgroup.le_comap_map _ _)
  have hp : IsOpenQuotientMap p := by
    let B := (v : {v : Primes(F) // v ∉ S}) → v.val.adicCompletionIntegers F
    obtain ⟨e, he, he', hcoords⟩ := integralAdelesOutside_factors F S
    let E : A ≃ₜ* (SAdeleRing F S × B) :=
      { e.toMulEquiv with continuous_toFun := he, continuous_invFun := he' }
    let U := (Units.mapContinuousMulEquiv E).trans (ContinuousMulEquiv.prodUnits _ _)
    have heq : (p : Aˣ → (SAdeleRing F S)ˣ) = Prod.fst ∘ U := by
      funext g
      exact Units.ext (hcoords g.val).1.symm
    rw [heq]
    exact isOpenQuotientMap_fst.comp U.toHomeomorph.isOpenQuotientMap
  let q := QuotientGroup.mk' d
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨π, hq.of_comp_iff.mp ?_, ?_⟩
  · exact (QuotientGroup.isOpenQuotientMap_mk (N := d.map p)).comp hp
  · intro c
    induction c using QuotientGroup.induction_on with
    | H g => rfl

/-- Paper: §3.1.2, p. 120. The norm on J_{F,S} is proper. In particular its fiber over
one is compact. -/
theorem isProperMap_sIdeleQuotientNorm : IsProperMap (sIdeleQuotientNorm F S) := by
  obtain ⟨π, hπ, hnorm⟩ := sIdeleClassGroup_projection F S
  have hcomp : IsProperMap ((sIdeleQuotientNorm F S) ∘ π) := by
    simpa only [Function.comp_def, hnorm] using
      isProperMap_sIdeleClassNorm_of_global F S (isProperMap_ideleClassNorm F)
  exact isProperMap_of_comp_of_surj hπ.continuous
    (hπ.continuous_comp_iff.mp hcomp.continuous) hcomp hπ.surjective

/-- Paper: §3.1.2, p. 120. The global idelic module supplies complex exponent charts on
the space of Hecke characters. -/
theorem ideleClass_hasNormTwistCharts : HasNormTwistCharts (ideleClassNorm F) := by
  obtain ⟨_, _, _, _, _, hT, hLC, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  obtain ⟨g, rfl⟩ := hsurj t
  exact hasNormTwistCharts_of_proper _ (isProperMap_ideleClassNorm F) ⟨g, ht⟩

/-- Paper: Equation (3.1.2.4), p. 121. Inserting the multiplicative group of a finite completion and
passing to idele classes is continuous. -/
theorem continuous_ideleClass_ofAdicCompletion (v : Primes(F)) :
    Continuous (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v) := by
  classical
  apply QuotientGroup.continuous_mk.comp
  apply Continuous.units_map
  apply continuous_const.prodMk
  apply continuous_restrictedProduct_of_uniform
  · intro w
    exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : Primes(F) ↦
      u.adicCompletion F) v)
  · filter_upwards [Filter.eventually_cofinite_ne v] with w hw x
    change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
    rw [Pi.mulSingle_eq_of_ne hw]
    exact (w.adicCompletionIntegers F).one_mem

/-- Paper: Equation (3.1.2.4), p. 121. Inserting an infinite local multiplicative group
into the idele class group is continuous. -/
theorem continuous_ideleClass_ofCompletion (w : InfinitePlace F) :
    Continuous (IdeleClassGroup.ofCompletion (𝓞 F) F w) := by
  classical
  apply QuotientGroup.continuous_mk.comp
  apply Continuous.units_map
  exact (continuous_mulSingle (A := InfinitePlace.Completion) w).prodMk continuous_const

/-- Paper: §3.1.2, p. 120. The idele class norm on one finite completion is its normalized
local norm. -/
theorem ideleClassNorm_ofAdicCompletion (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x) =
      Units.map nnNormHom.toMonoidHom x := by
  classical
  let g := IdeleGroup.ofAdicCompletion (𝓞 F) F v x
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm F g : ℝ≥0) : ℝ) = ‖x.val‖
  rw [((ideleNorm_spec F).1 g).2]
  change (∏ w : InfinitePlace F, ‖(1 : w.Completion)‖ ^ w.mult) *
    ∏ᶠ w, ‖RestrictedProduct.mulSingle (fun w : Primes(F) ↦ w.adicCompletionIntegers F) v x.val w‖ = _
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v]
  · rw [RestrictedProduct.mulSingle_eq_same]
  · intro w hw
    rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hw, norm_one]

/-- Inserting a unit at an infinite place gives its normalized local norm in the idele class group. -/
theorem ideleClassNorm_ofCompletion (w : InfinitePlace F) (x : w.Completionˣ) :
    ideleClassNorm F (IdeleClassGroup.ofCompletion (𝓞 F) F w x) =
      (Units.map nnNormHom.toMonoidHom x) ^ w.mult := by
  classical
  let g := IdeleGroup.ofCompletion (𝓞 F) F w x
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm F g : ℝ≥0) : ℝ) = ‖x.val‖ ^ w.mult
  rw [((ideleNorm_spec F).1 g).2]
  change (∏ v : InfinitePlace F, ‖Pi.mulSingle (M := fun t : InfinitePlace F ↦ t.Completion)
    w x.val v‖ ^ v.mult) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : v.adicCompletion F)‖ = _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single w]
  · rw [Pi.mulSingle_eq_same]
  · intro v _ hv
    rw [Pi.mulSingle_eq_of_ne hv, norm_one, one_pow]
  · simp

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at a finite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def finitePlaceRestriction (v : Primes(F)) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter (v.adicCompletion F)ˣ :=
  c.comp ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩

/-- Paper: Equation (3.1.2.4), p. 121. Restriction at an infinite place is precomposition
with insertion in that coordinate followed by passage to idele classes. -/
def infinitePlaceRestriction (w : InfinitePlace F) (c : HeckeCharacter (𝓞 F) F) :
    QuasiCharacter w.Completionˣ :=
  c.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩

open Classical in
/-- Paper: §3.1.2, p. 120. A quasi-character of J_{F,S} is the product of its local
restrictions at the infinite places and the finite places in S. Each restriction
evaluates the character on the S-idele with the given coordinate and ones elsewhere. -/
theorem sIdeleQuotientCharacter_eq_prod_restrictions (c : QuasiCharacter (SIdeleQuotient F S)) :
    let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
      ((v : S) → v.val.adicCompletion F)
    let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
    let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
    ∃ (a : (w : InfinitePlace F) → QuasiCharacter w.Completionˣ)
        (b : (v : S) → QuasiCharacter (v.val.adicCompletion F)ˣ),
      (∀ w u, a w u = c (QuotientGroup.mk (e.symm (eArch.symm (Pi.mulSingle w u), 1)))) ∧
      (∀ v u, b v u = c (QuotientGroup.mk (e.symm (1, eS.symm (Pi.mulSingle v u))))) ∧
      ∀ g : (SAdeleRing F S)ˣ, c (QuotientGroup.mk g) =
        (∏ w, a w (eArch (e g).1 w)) * ∏ v, b v (eS (e g).2 v) := by
  classical
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let q : (SAdeleRing F S)ˣ →ₜ* SIdeleQuotient F S :=
    ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let f := (c.comp q).comp ⟨e.symm.toMonoidHom, e.symm.continuous⟩
  let a := f.toMonoidHom.comp ((MonoidHom.inl _ _).comp eArch.symm.toMonoidHom)
  let b := f.toMonoidHom.comp ((MonoidHom.inr _ _).comp eS.symm.toMonoidHom)
  have ha : Continuous a := f.continuous.comp (eArch.symm.continuous.prodMk continuous_const)
  have hb : Continuous b := f.continuous.comp (continuous_const.prodMk eS.symm.continuous)
  let A (w : InfinitePlace F) := w.Completionˣ
  let B (v : S) := (v.val.adicCompletion F)ˣ
  refine ⟨fun w ↦ ⟨a.comp (MonoidHom.mulSingle A w), ha.comp (continuous_mulSingle (A := A) w)⟩,
    fun v ↦ ⟨b.comp (MonoidHom.mulSingle B v), hb.comp (continuous_mulSingle (A := B) v)⟩,
    fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun g ↦ ?_⟩
  change c (q g) =
    (∏ w, a (Pi.mulSingle w (eArch (e g).1 w))) * ∏ v, b (Pi.mulSingle v (eS (e g).2 v))
  rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle, Finset.univ_prod_mulSingle]
  change c (q g) = f (eArch.symm (eArch (e g).1), 1) * f (1, eS.symm (eS (e g).2))
  rw [eArch.symm_apply_apply, eS.symm_apply_apply, ← map_mul]
  change c (q g) = c (q (e.symm (((e g).1, 1) * (1, (e g).2))))
  simp

local notation "finiteNorm" => Units.map nnNormHom.toMonoidHom
local notation "infiniteNorm(" w ")" => (Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w

-- TODO(paper-gap): At a finite place the section in (3.1.2.2) must be taken over the
-- value group q^ℤ. The absolute value has no right inverse on all positive reals.

/-- Paper: Equation (3.1.2.2), p. 120. The finite-place surface is a cylinder for each
character of the local integer units. In exponent coordinates a uniformizer contributes q⁻ˢ.
Deviation: The auxiliary character of the discrete value group is specified by its value b
at the module of the chosen uniformizer. The coordinate equations specify the biholomorphism. -/
theorem finitePlace_quasiCharacterParametrization (v : Primes(F)) (π : (v.adicCompletion F)ˣ)
    (hπ : ‖π.val‖ = (v.asIdeal.absNorm : ℝ)⁻¹) (b : ℂˣ) :
    let q : ℝ := v.asIdeal.absNorm
    let periods := AddSubgroup.zmultiples (2 * (Real.pi : ℂ) * Complex.I / (Real.log q : ℂ))
    ∃ e : QuasiCharacter (v.adicCompletion F)ˣ ≃ₜ
        ((ℂ ⧸ periods) × PontryaginDual (v.adicCompletionIntegers F)ˣ),
      ∀ c, (∀ s : ℂ, (e c).1 = QuotientAddGroup.mk s ↔ c π = (b : ℂ) * (q : ℂ) ^ (-s)) ∧
        ∀ u, ((e c).2 u : ℂ) = c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) := by
  let O := v.adicCompletionIntegers F
  have : CompactSpace O := compactSpace_adicCompletionIntegers v
  have : CompactSpace Oˣ := compactSpace_units_of_compactSpace O
  obtain ⟨split, hπ', hO⟩ := finitePlace_unitDecomposition v π hπ
  let f : (v.adicCompletion F)ˣ →ₜ* (Multiplicative ℤ × Oˣ) := ⟨split, split.continuous⟩
  let g : (Multiplicative ℤ × Oˣ) →ₜ* (v.adicCompletion F)ˣ := ⟨split.symm, split.symm.continuous⟩
  let transport : QuasiCharacter (v.adicCompletion F)ˣ ≃ₜ QuasiCharacter (Multiplicative ℤ × Oˣ) :=
    { toFun := fun c ↦ c.comp g
      invFun := fun c ↦ c.comp f
      left_inv := fun c ↦ ContinuousMonoidHom.ext fun x ↦ congrArg c (split.symm_apply_apply x)
      right_inv := fun c ↦ ContinuousMonoidHom.ext fun x ↦ congrArg c (split.apply_symm_apply x)
      continuous_toFun := g.continuous_comp_left
      continuous_invFun := f.continuous_comp_left }
  obtain ⟨chars, hchars⟩ := exists_cyclicProductCharacterHomeomorph (U := Oˣ)
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨cylinder, hcyl⟩ := exists_complexPowerCylinder _ hq b
  let e := (transport.trans chars).trans (cylinder.symm.prodCongr (Homeomorph.refl _))
  refine ⟨e, fun c ↦ ⟨fun s ↦ ?_, fun u ↦ ?_⟩⟩
  · have hval := (hchars (transport c)).1
    change _ = c (split.symm (Multiplicative.ofAdd 1, 1)) at hval
    rw [← hπ', split.symm_apply_apply] at hval
    change cylinder.symm (chars (transport c)).1 = _ ↔ _
    rw [cylinder.symm_apply_eq, ← Units.val_inj, hval, hcyl]
  · have hval := (hchars (transport c)).2 u
    change _ = c (split.symm (1, u)) at hval
    rw [← hO u, split.symm_apply_apply] at hval
    exact hval

/-- Paper: Equation (3.1.2.2), p. 120. At a finite place the locally defined complex
exponent is a chart for the normalized absolute value. -/
theorem finitePlace_hasNormTwistCharts (v : Primes(F)) :
    HasNormTwistCharts (finiteNorm : (v.adicCompletion F)ˣ →* ℝ≥0ˣ) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let n : (v.adicCompletion F)ˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom
  have hp : IsProperMap (fun x ↦ (n x) ^ (1 : ℕ)) := isProperMap_units_nnNorm_pow 1 one_ne_zero
  simp only [pow_one] at hp
  apply hasNormTwistCharts_of_proper n hp
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  refine ⟨u, fun he ↦ hπ.val_lt_one.ne ?_⟩
  apply Valued.toNormedField.norm_eq_one_iff.mp
  exact congrArg (fun t : ℝ≥0ˣ ↦ ((t : ℝ≥0) : ℝ)) he

/-- Paper: Equation (3.1.2.3), p. 121. A continuous splitting of the normalized absolute
value identifies the surface with a complex plane for each character of the norm-one group.
Deviation: We use the norm-one kernel specified below (3.1.2.3) for its archimedean unit
group. We state the homeomorphism with the coordinate formulas that determine its analytic maps. -/
theorem infinitePlace_quasiCharacterParametrization (w : InfinitePlace F)
    (σ : ℝ≥0ˣ →ₜ* w.Completionˣ) (hσ : RightInverse σ (infiniteNorm(w))) :
    let n : w.Completionˣ →* ℝ≥0ˣ := infiniteNorm(w)
    ∃ e : QuasiCharacter w.Completionˣ ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  let n : w.Completionˣ →* ℝ≥0ˣ := infiniteNorm(w)
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  have hker (u : w.Completionˣ) : u ∈ n.ker ↔ ‖(u : w.Completion)‖ = 1 := by
    rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
    exact pow_eq_one_iff_of_nonneg (norm_nonneg _) w.mult_ne_zero
  let : CompactSpace n.ker := by
    apply isCompact_iff_compactSpace.mp
    apply Units.isEmbedding_val₀.isInducing.isCompact_iff.mpr
    have himage : Units.val '' (n.ker : Set w.Completionˣ) = Metric.sphere 0 1 := by
      ext x
      rw [mem_sphere_zero_iff_norm]
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (hker u).mp hu
      · intro hx
        have hne : x ≠ 0 := norm_ne_zero_iff.mp (hx.trans_ne one_ne_zero)
        exact ⟨Units.mk0 x hne, (hker _).mpr hx, rfl⟩
    rw [himage]
    exact isCompact_sphere _ _
  exact quasiCharacterParametrization_of_split n
    ((continuous_nnNorm.units_map nnNormHom.toMonoidHom).pow w.mult) σ hσ

/-- Paper: Equation (3.1.2.3), p. 121. At an infinite place the normalized absolute value
gives complex exponent charts. Its multiplicity is one at real places and two at complex places. -/
theorem infinitePlace_hasNormTwistCharts (w : InfinitePlace F) :
    HasNormTwistCharts (infiniteNorm(w) : w.Completionˣ →* ℝ≥0ˣ) := by
  have htwo : 1 < ‖(2 : w.Completion)‖ := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num
  let : NontriviallyNormedField w.Completion := ⟨⟨2, htwo⟩⟩
  let : ProperSpace w.Completion :=
    .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
  apply hasNormTwistCharts_of_proper _ (isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero)
  let u := Units.mk0 (2 : w.Completion) (by rintro h; rw [h, norm_zero] at htwo; linarith)
  refine ⟨u, fun he ↦ ?_⟩
  have hv := congrArg (fun y : ℝ≥0ˣ ↦ ((y : ℝ≥0) : ℝ)) he
  change ‖(2 : w.Completion)‖ ^ w.mult = 1 at hv
  exact (one_lt_pow₀ htwo w.mult_ne_zero).ne' hv

/-- Paper: §3.1.2, p. 120. Equip the Hecke characters with the norm-twist atlas. -/
scoped instance heckeCharacterChartedSpace : ChartedSpace ℂ (HeckeCharacter (𝓞 F) F) :=
  quasiCharacterChartedSpace _ (ideleClass_hasNormTwistCharts F)

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to a finite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem finitePlaceRestriction_isLocalDiffeomorph (v : Primes(F)) :
    letI := quasiCharacterChartedSpace _ (finitePlace_hasNormTwistCharts F v)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (finitePlaceRestriction F v) := by
  let i : (v.adicCompletion F)ˣ →ₜ* IdeleClassGroup (𝓞 F) F :=
    ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩
  exact quasiCharacter_comp_isLocalDiffeomorph (G := IdeleClassGroup (𝓞 F) F)
    (H := (v.adicCompletion F)ˣ) (ideleClassNorm F) finiteNorm i
    (fun x ↦ ideleClassNorm_ofAdicCompletion F v x) (ideleClass_hasNormTwistCharts F)
    (finitePlace_hasNormTwistCharts F v)

/-- Paper: Lemma 3.1.2.1, p. 121. Restriction to an infinite completion is a local
complex analytic isomorphism in the norm-twist atlases. -/
theorem infinitePlaceRestriction_isLocalDiffeomorph (w : InfinitePlace F) :
    letI := quasiCharacterChartedSpace _ (infinitePlace_hasNormTwistCharts F w)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (infinitePlaceRestriction F w) := by
  let i : w.Completionˣ →ₜ* IdeleClassGroup (𝓞 F) F :=
    ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩
  exact quasiCharacter_comp_isLocalDiffeomorph (G := IdeleClassGroup (𝓞 F) F)
    (H := w.Completionˣ) (ideleClassNorm F) (infiniteNorm(w)) i
    (fun x ↦ ideleClassNorm_ofCompletion F w x) (ideleClass_hasNormTwistCharts F)
    (infinitePlace_hasNormTwistCharts F w)

/-- Paper: Equation (3.1.2.5), p. 121. A continuous splitting of the S-idelic norm
identifies the surface with a complex plane for each character of its norm-one subgroup.
Deviation: We give the homeomorphism with its analytic coordinates fixed by evaluation along
the splitting and restriction to the kernel. -/
theorem sIdeleQuotient_quasiCharacterParametrization (σ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (hσ : RightInverse σ (sIdeleQuotientNorm F S)) :
    let n := sIdeleQuotientNorm F S
    ∃ e : QuasiCharacter (SIdeleQuotient F S) ≃ₜ (ℂ × PontryaginDual n.ker), ∀ c,
      (∀ t : ℝ≥0ˣ, c (σ t) = (((t : ℝ≥0) : ℝ) : ℂ) ^ (e c).1) ∧
        ∀ u : n.ker, ((e c).2 u : ℂ) = c u.val := by
  let n := sIdeleQuotientNorm F S
  have : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have hp : IsProperMap n := isProperMap_sIdeleQuotientNorm F S
  have : CompactSpace n.ker :=
    isCompact_iff_compactSpace.mp (hp.isCompact_preimage (isCompact_singleton (x := 1)))
  exact quasiCharacterParametrization_of_split (G := SIdeleQuotient F S) n hp.continuous σ hσ

/-- Paper: Equation (3.1.2.5), p. 121. The S-idelic module gives complex exponent
charts on the space of quasi-characters of J_{F,S}. -/
theorem sIdeleQuotient_hasNormTwistCharts : HasNormTwistCharts (sIdeleQuotientNorm F S) := by
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  let d := p.comp (integralAdeleDiagonal F S)
  obtain ⟨hd, hc, _⟩ := sAdele_additive_quotient F S
  have : IsClosed (projectedDiagonal : Set (SAdeleRing F S)ˣ) := by
    rw [sProjectedDiagonal, MonoidHom.map_range]
    exact isClosed_range_unitsMap d.toMonoidHom hd hc
  have : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  exact hasNormTwistCharts_of_proper _ (isProperMap_sIdeleQuotientNorm F S)
    ⟨σ t, (hσ t).trans_ne ht⟩

local notation "LocalIntegers(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "LocalUnits(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v)ˣ

open scoped NumberField.AdeleRing in
/-- Send a family of local integer units to its idele class, with all infinite
coordinates equal to one. -/
private def finiteIntegerUnitInsertion : (∀ v : Primes(F), LocalUnits(v)) →ₜ* IdeleClassGroup (𝓞 F) F :=
  let f : (∀ v : Primes(F), LocalIntegers(v)) →* AdeleRing (𝓞 F) F :=
    (1 : _ →* InfiniteAdeleRing F).prod
      { toFun := RestrictedProduct.structureMap (fun v : Primes(F) => v.adicCompletion F)
          (fun v => (LocalIntegers(v) : Set (v.adicCompletion F))) Filter.cofinite
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  ⟨(QuotientGroup.mk' _).comp ((Units.map f).comp
    (ContinuousMulEquiv.piUnits.symm : (∀ v : Primes(F), LocalUnits(v)) ≃ₜ* _).toMonoidHom),
    QuotientGroup.continuous_mk.comp
      ((continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous).units_map f
        |>.comp (ContinuousMulEquiv.piUnits.symm : (∀ v : Primes(F), LocalUnits(v)) ≃ₜ* _).continuous)⟩

/-- On a family supported at one finite place, the product insertion agrees with
Mathlib's insertion at that place. -/
private theorem finiteIntegerUnitInsertion_mulSingle (v : Primes(F)) (u : LocalUnits(v)) :
    letI := Classical.decEq (Primes(F))
    finiteIntegerUnitInsertion F (Pi.mulSingle v u) =
      IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
        (Units.map (LocalIntegers(v)).subtype.toMonoidHom u) := by
  let _ := Classical.decEq (Primes(F))
  apply congrArg (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F)
  apply Units.ext
  refine Prod.ext rfl ?_
  apply RestrictedProduct.ext
  intro w
  change (((Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) w).val : w.adicCompletion F) =
    RestrictedProduct.mulSingle (fun w : Primes(F) => LocalIntegers(w)) v
      (u.val : v.adicCompletion F) w
  rcases eq_or_ne w v with rfl | hw
  · rw [Pi.mulSingle_eq_same]
    exact (RestrictedProduct.mulSingle_eq_same _ _ _).symm
  · rw [Pi.mulSingle_eq_of_ne hw]
    exact (RestrictedProduct.mulSingle_eq_of_ne _ _ hw).symm

/-- Paper: Equation (3.1.2.6), p. 121. The global quasi-characters trivial on the
local integer units at every finite place outside S form an open set. -/
theorem isOpen_unramifiedOutside :
    IsOpen {c : HeckeCharacter (𝓞 F) F | ∀ v ∉ S, c.IsUnramifiedAt v} := by
  classical
  have (v : Primes(F)) : CompactSpace (LocalUnits(v)) := by
    have := compactSpace_adicCompletionIntegers (K := F) v
    exact compactSpace_units_of_compactSpace _
  let cut : (∀ v : Primes(F), LocalUnits(v)) →ₜ* (∀ v : Primes(F), LocalUnits(v)) :=
    ⟨{ toFun := fun u v => if v ∈ S then 1 else u v
       map_one' := by
         funext v
         simp
       map_mul' := fun u w => by
         funext v
         by_cases hv : v ∈ S <;> simp [hv] },
      continuous_pi fun v => by
        by_cases hv : v ∈ S
        · simpa only [hv, ite_true] using continuous_const
        · simpa only [hv, ite_false] using continuous_apply v⟩
  let i := (finiteIntegerUnitInsertion F).comp cut
  have hl (c : HeckeCharacter (𝓞 F) F) (v : Primes(F)) :
      c.IsUnramifiedAt v ↔
        ∀ u : LocalUnits(v), c (finiteIntegerUnitInsertion F (Pi.mulSingle v u)) = 1 := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, finiteIntegerUnitInsertion_mulSingle]
    refine forall_congr' fun u => ?_
    change c.restrict v ↑(Units.map (LocalIntegers(v)).subtype.toMonoidHom u) = 1 ↔ _
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hsingle (v : Primes(F)) (u : LocalUnits(v)) :
      cut (Pi.mulSingle v u) = if v ∈ S then 1 else (Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) := by
    funext w
    change (if w ∈ S then 1 else (Pi.mulSingle v u : ∀ w : Primes(F), LocalUnits(w)) w) = _
    rcases eq_or_ne w v with rfl | h
    · by_cases hv : w ∈ S <;> simp [hv]
    · by_cases hv : v ∈ S <;> simp [hv, Pi.mulSingle_eq_of_ne h]
  have hset : {c : HeckeCharacter (𝓞 F) F | ∀ v ∉ S, c.IsUnramifiedAt v} =
      (fun c => c.comp i) ⁻¹' {1} := by
    ext c
    change (∀ v ∉ S, c.IsUnramifiedAt v) ↔ c.comp i = 1
    simp only [hl]
    constructor
    · intro hc
      ext1 u
      change c (i u) = 1
      -- Finite products of the single-coordinate families converge to the full family.
      have hp : HasProd (fun v => Pi.mulSingle v (u v)) u := by
        refine Pi.hasProd.mpr fun w => ?_
        convert hasProd_ite_eq w (u w) using 1
        funext v
        rcases eq_or_ne v w with rfl | hv
        · simp
        · simp [hv]
      have hmap := hp.map (c.comp i) (c.comp i).continuous
      refine hmap.unique (hasProd_one.congr_fun fun v => ?_)
      change c (finiteIntegerUnitInsertion F (cut (Pi.mulSingle v (u v)))) = 1
      rw [hsingle]
      by_cases hv : v ∈ S
      · simp [hv]
      · simpa [hv] using hc v hv (u v)
    · intro hc v hv u
      have h := DFunLike.congr_fun hc (Pi.mulSingle v u)
      change c (finiteIntegerUnitInsertion F (cut (Pi.mulSingle v u))) = 1 at h
      simpa [hsingle, hv] using h
  rw [hset]
  exact isOpen_singleton_one_complex.preimage i.continuous_comp_left

/-- Paper: Equation (3.1.2.6), p. 121. The open subspace Ω_S(C_F) consists of the
Hecke characters unramified at every finite place outside S. -/
def unramifiedOutside : TopologicalSpace.Opens (HeckeCharacter (𝓞 F) F) :=
  ⟨{c | ∀ v ∉ S, c.IsUnramifiedAt v}, isOpen_unramifiedOutside F S⟩

/-- Paper: Equation (3.1.2.6), p. 121. Membership in Ω_S is equivalent to triviality
of the continuous local restrictions on all integer units outside S. -/
theorem mem_unramifiedOutside_iff (c : HeckeCharacter (𝓞 F) F) :
    c ∈ unramifiedOutside F S ↔ ∀ v ∉ S, ∀ u : (v.adicCompletionIntegers F)ˣ,
      finitePlaceRestriction F v c (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
  change (∀ v ∉ S, c.IsUnramifiedAt v) ↔ _
  simp only [HeckeCharacter.isUnramifiedAt_iff]
  refine forall_congr' fun v => imp_congr_right fun _ => forall_congr' fun u => ?_
  change c.restrict v ↑(Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 ↔ _
  rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
  rfl

/-- Paper: Equations (3.1.2.7)–(3.1.2.8), p. 121. Insert an S-idele into the full idele
group by multiplying its single-coordinate insertions over S, including all infinite places. -/
def sIdeleInsertion : (SAdeleRing F S)ˣ →* IdeleGroup (𝓞 F) F :=
  (∏ w : InfinitePlace F, (IdeleGroup.ofCompletion (𝓞 F) F w).comp
    (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom)) *
  ∏ v : S, (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val).comp
    (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom)

/-- Paper: Equation (3.1.2.8), p. 121. The inserted idele has the given components in S
and component one at every finite place outside S. -/
theorem sIdeleInsertion_apply (g : (SAdeleRing F S)ˣ) :
    (sIdeleInsertion F S g).val.1 = g.val.1 ∧
    (∀ v : S, (sIdeleInsertion F S g).val.2 v.val = g.val.2 v) ∧
    ∀ v ∉ S, (sIdeleInsertion F S g).val.2 v = 1 := by
  classical
  have hfinite (v : Primes(F)) :
      (sIdeleInsertion F S g).val.2 v =
        ∏ u : S, (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u)) v := by
    let eval : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F :=
      RestrictedProduct.evalRingHom _ v
    change eval (sIdeleInsertion F S g).val.2 =
      ∏ u : S, eval (FiniteAdeleRing.ofAdicCompletion F u.val (g.val.2 u))
    rw [← map_prod]
    apply congrArg eval
    simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.snd_prod]
  refine ⟨?_, ?_, ?_⟩
  · simp [sIdeleInsertion, MonoidHom.finsetProd_apply, AdeleRing, Prod.fst_prod,
      InfiniteAdeleRing.ofCompletion]
    exact Finset.univ_prod_mulSingle g.val.1
  · intro v
    rw [hfinite, Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · exact RestrictedProduct.mulSingle_eq_same _ _ _
    · intro u _ huv
      have h : v.val ≠ u.val := fun h => huv (Subtype.ext h.symm)
      exact RestrictedProduct.mulSingle_eq_of_ne _ _ h
  · intro v hv
    rw [hfinite]
    apply Finset.prod_eq_one
    intro u _
    have h : v ≠ u.val := fun h => hv (h ▸ u.property)
    exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

/-- The global norm of the idele extended by one equals the product of the norms in S. -/
theorem ideleNorm_sIdeleInsertion (g : (SAdeleRing F S)ˣ) :
    ideleNorm F (sIdeleInsertion F S g) = sIdeleNorm F S g := by
  classical
  let a := sIdeleInsertion F S g
  obtain ⟨harch, hin, hout⟩ := sIdeleInsertion_apply F S g
  have hS : (fun v : Primes(F) ↦ ‖a.val.2 v‖).mulSupport ⊆ (S : Set (Primes(F))) := by
    intro v hv
    by_contra h
    exact hv ((congrArg norm (hout v h)).trans norm_one)
  let ev : ((SAdeleRing F S)ˣ →* ℝ≥0ˣ) →* ℝ := NNReal.toRealHom.toMonoidHom.comp
    ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm F a : ℝ≥0) : ℝ) = ev (sIdeleNorm F S)
  rw [((ideleNorm_spec F).1 a).2, finprod_eq_prod_of_mulSupport_subset _ hS,
    ← Finset.prod_coe_sort S (fun v ↦ ‖a.val.2 v‖)]
  change (∏ w : InfinitePlace F, ‖(sIdeleInsertion F S g).val.1 w‖ ^ w.mult) *
    (∏ v : S, ‖(sIdeleInsertion F S g).val.2 v.val‖) = _
  simp_rw [harch, hin]
  simp only [sIdeleNorm, map_mul, map_prod]
  rfl

/-- Paper: Equation (3.1.2.7), p. 121. Extension by one is a closed topological embedding. -/
theorem isClosedEmbedding_sIdeleInsertion : IsClosedEmbedding (sIdeleInsertion F S) := by
  let : T2Space (IdeleGroup (𝓞 F) F) := (ideleGroup_topology F).1
  let j := sIdeleInsertion F S
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := by
    apply Continuous.units_map
    exact continuous_fst.prodMk (continuous_pi fun v ↦
      (RestrictedProduct.continuous_eval v.val).comp continuous_snd)
  have hleft : LeftInverse p j := by
    intro g
    apply Units.ext
    exact Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  have hval : Continuous (fun g ↦ (j g).val) := by
    apply Continuous.prodMk
    · exact (continuous_fst.comp Units.continuous_val).congr fun g ↦
        (sIdeleInsertion_apply F S g).1.symm
    · apply continuous_restrictedProduct_of_uniform
      · intro v
        by_cases hv : v ∈ S
        · exact ((continuous_apply (⟨v, hv⟩ : S)).comp
            (continuous_snd.comp Units.continuous_val)).congr fun g ↦
              ((sIdeleInsertion_apply F S g).2.1 ⟨v, hv⟩).symm
        · exact continuous_const.congr fun g ↦ ((sIdeleInsertion_apply F S g).2.2 v hv).symm
      · filter_upwards [S.eventually_cofinite_notMem] with v hv g
        change (sIdeleInsertion F S g).val.2 v ∈ v.adicCompletionIntegers F
        rw [(sIdeleInsertion_apply F S g).2.2 v hv]
        exact (v.adicCompletionIntegers F).one_mem
  apply hleft.isClosedEmbedding hp
  refine Units.continuous_iff.mpr ⟨hval, (hval.comp continuous_inv).congr fun g ↦ ?_⟩
  exact congrArg Units.val (map_inv j g)

local notation "pullbackS(" c ")" => MonoidHom.comp (ContinuousMonoidHom.toMonoidHom c)
  (MonoidHom.comp (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)) (sIdeleInsertion F S))

/-- Paper: Equation (3.1.2.9), p. 121. For a character unramified outside S, pullback
along insertion kills the projected diagonal S-units. -/
theorem sIdeleRestriction_descent (c : unramifiedOutside F S) :
    projectedDiagonal ≤ (pullbackS(c.val)).ker := by
  classical
  rw [sProjectedDiagonal, MonoidHom.map_range]
  rintro _ ⟨u, rfl⟩
  let g := Units.map (integralAdeleDiagonal F S).toMonoidHom u
  let i := (integralAdelesOutside F S).subtype
  let a := Units.map i.toMonoidHom g
  let s := Units.map ((adeleProjection F S).comp i).toMonoidHom g
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let localEval (v : Primes(F)) (hv : v ∉ S) : integralAdelesOutside F S →+* LocalIntegers(v) :=
    (((RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)).comp i).codRestrict _
      (fun x => by
        have hx := x.property
        simp only [integralAdelesOutside, Subring.mem_iInf] at hx
        exact hx v hv)
  let outsideUnits (v : Primes(F)) : LocalUnits(v) :=
    if hv : v ∈ S then 1 else Units.map (localEval v hv).toMonoidHom g
  -- Continuity extends triviality on the single-coordinate factors to the whole family.
  have hb : c.val (finiteIntegerUnitInsertion F outsideUnits) = 1 := by
    let χ := c.val.comp (finiteIntegerUnitInsertion F)
    have hp : HasProd (fun v => Pi.mulSingle v (outsideUnits v)) outsideUnits := by
      refine Pi.hasProd.mpr fun w => ?_
      convert hasProd_pi_single w (outsideUnits w) using 1
      funext v
      rcases eq_or_ne v w with rfl | hv
      · simp
      · simp [hv, hv.symm]
    refine (hp.map χ χ.continuous).unique (hasProd_one.congr_fun fun v => ?_)
    change c.val (finiteIntegerUnitInsertion F (Pi.mulSingle v (outsideUnits v))) = 1
    by_cases hv : v ∈ S
    · simp [outsideUnits, hv]
    · rw [finiteIntegerUnitInsertion_mulSingle]
      have hc : ∀ v ∉ S, c.val.IsUnramifiedAt v := c.property
      have h := (hc v hv).restrict_apply_unit_eq_one (outsideUnits v)
      change c.val.restrict v ↑(Units.map (LocalIntegers(v)).subtype.toMonoidHom (outsideUnits v)) = 1 at h
      rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe] at h
      exact h
  have hfactor : q a = q (sIdeleInsertion F S s) * finiteIntegerUnitInsertion F outsideUnits := by
    change q a = q (sIdeleInsertion F S s) * q _
    rw [← map_mul]
    apply congrArg q
    apply Units.ext
    obtain ⟨hinf, hin, hout⟩ := sIdeleInsertion_apply F S s
    refine Prod.ext ?_ ?_
    · change a.val.1 = (sIdeleInsertion F S s).val.1 * 1
      rw [mul_one, hinf]
      rfl
    · apply RestrictedProduct.ext
      intro v
      change a.val.2 v =
        (sIdeleInsertion F S s).val.2 v * ((outsideUnits v).val : v.adicCompletion F)
      by_cases hv : v ∈ S
      · rw [hin ⟨v, hv⟩]
        change a.val.2 v = a.val.2 v * ((outsideUnits v).val : v.adicCompletion F)
        simp [outsideUnits, hv]
      · rw [hout v hv, one_mul]
        dsimp [outsideUnits]
        rw [dite_eq_right hv]
        rfl
  have ha : q a = 1 := (QuotientGroup.eq_one_iff a).mpr
    ⟨Units.map ((S : Set (Primes(F))).integer F).val.toRingHom.toMonoidHom u, Units.ext rfl⟩
  change c.val (q (sIdeleInsertion F S s)) = 1
  have h := congrArg c.val hfactor
  rw [map_mul, hb, mul_one, ha, map_one] at h
  exact h.symm

/-- Paper: Equation (3.1.2.9), p. 121. The S-local restriction is the quotient lift of
the pullback from idele classes. Its domain carries the open subspace topology. -/
def sIdeleRestriction (c : unramifiedOutside F S) : QuasiCharacter (SIdeleQuotient F S) :=
  ⟨QuotientGroup.lift _ (pullbackS(c.val)) (sIdeleRestriction_descent F S c),
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
      (c.val.continuous.comp (QuotientGroup.continuous_mk.comp
        (isClosedEmbedding_sIdeleInsertion F S).continuous))⟩

/-- Paper: Equation (3.1.2.9), p. 121. On an S-idele representative, the restriction
evaluates the original character on the class of the inserted idele. -/
theorem sIdeleRestriction_mk (c : unramifiedOutside F S) (g : (SAdeleRing F S)ˣ) :
    sIdeleRestriction F S c (QuotientGroup.mk g) = c.val (QuotientGroup.mk (sIdeleInsertion F S g)) :=
  rfl

/-- Paper: Lemma 3.1.2.2, p. 121. Every quasi-character of J_{F,S} extends to an
idele class character unramified outside S. -/
theorem sIdeleRestriction_surjective : Surjective (sIdeleRestriction F S) := by
  classical
  intro χ
  let A := integralAdelesOutside F S
  let p := Units.map ((adeleProjection F S).comp A.subtype).toMonoidHom
  let D := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  let π := QuotientGroup.map D (D.map p) p (Subgroup.le_comap_map _ _)
  have hp : Continuous p := ((continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).comp continuous_subtype_val).units_map _
  have hπ : Continuous π := (QuotientGroup.isQuotientMap_mk D).continuous_iff.mpr
    (QuotientGroup.continuous_mk.comp hp)
  obtain ⟨j, hj, _, hjmk⟩ := sIdeleClassGroup_openEmbedding F S
  let πc : SIdeleClassGroup F S →ₜ* SIdeleQuotient F S := ⟨π, hπ⟩
  let ψ : QuasiCharacter (SIdeleClassGroup F S) := χ.comp πc
  obtain ⟨C, hC⟩ := exists_complexCharacter_extension_of_isOpenEmbedding
    (G := SIdeleClassGroup F S) (H := IdeleClassGroup (𝓞 F) F) j hj ψ
  have hvalue (u : Aˣ) :
      C (QuotientGroup.mk (Units.map A.subtype.toMonoidHom u)) = χ (QuotientGroup.mk (p u)) := by
    rw [← hjmk]
    exact hC (QuotientGroup.mk u)
  -- Lift any family of ideles whose coordinates are integral off S, including its inverses.
  have hlift {B : Type _} [Group B] (f : B →* IdeleGroup (𝓞 F) F)
      (hf : ∀ b v, v ∉ S → (f b).val.2 v ∈ v.adicCompletionIntegers F) (b : B) :
      ∃ u : Aˣ, Units.map A.subtype.toMonoidHom u = f b := by
    let φ : B →* A := ((Units.coeHom _).comp f).codRestrict A.toSubmonoid (by
      intro b
      change (f b).val ∈ integralAdelesOutside F S
      simp only [integralAdelesOutside, Subring.mem_iInf]
      intro v hv
      exact hf b v hv)
    exact ⟨φ.toHomUnits b, Units.ext rfl⟩
  have hunram : C ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S C).mpr
    intro v hv x
    let f := (IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
      (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)
    have hfin (b) (w : Primes(F)) (hw : w ≠ v) : (f b).val.2 w = 1 :=
      RestrictedProduct.mulSingle_eq_of_ne _ _ hw
    obtain ⟨u, hu⟩ := hlift f (fun b w _ ↦ by
      by_cases hw : w = v
      · subst w
        change RestrictedProduct.mulSingle _ v (b.val : v.adicCompletion F) v ∈ _
        rw [RestrictedProduct.mulSingle_eq_same]
        exact b.val.property
      · rw [hfin _ w hw]
        exact one_mem _) x
    have hpu : p u = 1 := by
      change Units.map (adeleProjection F S).toMonoidHom (Units.map A.subtype.toMonoidHom u) = 1
      rw [hu]
      apply Units.ext
      exact Prod.ext rfl (funext fun w ↦ hfin x w.val (fun h ↦ hv (h ▸ w.property)))
    change C (QuotientGroup.mk (f x)) = 1
    rw [← hu, hvalue, hpu, QuotientGroup.mk_one, map_one]
  refine ⟨⟨C, hunram⟩, ?_⟩
  ext1 y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [sIdeleRestriction_mk]
  obtain ⟨u, hu⟩ := hlift (sIdeleInsertion F S) (fun b v hv ↦ by
    rw [(sIdeleInsertion_apply F S b).2.2 v hv]
    exact one_mem _) g
  have hpu : p u = g := by
    change Units.map (adeleProjection F S).toMonoidHom (Units.map A.subtype.toMonoidHom u) = g
    rw [hu]
    apply Units.ext
    exact Prod.ext (sIdeleInsertion_apply F S g).1 (funext (sIdeleInsertion_apply F S g).2.1)
  change C (QuotientGroup.mk (sIdeleInsertion F S g)) = _
  rw [← hu, hvalue, hpu]

/-- Paper: Lemma 3.1.2.2, p. 121. Restriction from the open unramified locus to the
S-idelic character surface is a local complex analytic isomorphism. -/
theorem sIdeleRestriction_isLocalDiffeomorph :
    letI := quasiCharacterChartedSpace _ (sIdeleQuotient_hasNormTwistCharts F S)
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (sIdeleRestriction F S) := by
  let m := ideleClassNorm F
  let n := sIdeleQuotientNorm F S
  let hG := ideleClass_hasNormTwistCharts F
  let hH := sIdeleQuotient_hasNormTwistCharts F S
  let := quasiCharacterChartedSpace (G := SIdeleQuotient F S) n hH
  let : IsManifold 𝓘(ℂ) ω (HeckeCharacter (𝓞 F) F) :=
    quasiCharacter_isManifold (G := IdeleClassGroup (𝓞 F) F) m hG
  let := quasiCharacter_isManifold (G := SIdeleQuotient F S) n hH
  apply isLocalDiffeomorph_of_chartAt 𝓘(ℂ) ω
  · intro c
    let d := sIdeleRestriction F S c
    have h₀ := (hG c.val).choose_spec.2.1
    have hd₀ := (hH d).choose_spec.2.1
    change (hG c.val).choose c.val ∈ (hH d).choose.target
    rw [h₀.trans hd₀.symm]
    exact (hH d).choose.map_source (hH d).choose_spec.1
  · intro c y hy hz
    let d := sIdeleRestriction F S c
    let a := (hG c.val).choose
    let b := (hH d).choose
    have hy' : y.val ∈ a.source := hy.2
    change a y.val ∈ b.target at hz
    change sIdeleRestriction F S y = b.symm (a y.val)
    ext1 x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [sIdeleRestriction_mk, (hH d).choose_spec.2.2 _ hz]
    change y.val (QuotientGroup.mk (sIdeleInsertion F S g)) =
      c.val (QuotientGroup.mk (sIdeleInsertion F S g)) * (((sIdeleNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ (a y.val)
    rw [← ideleNorm_sIdeleInsertion]
    let t : IdeleClassGroup (𝓞 F) F := QuotientGroup.mk (sIdeleInsertion F S g)
    exact (congrArg (fun q : HeckeCharacter (𝓞 F) F ↦ q t) (a.left_inv hy')).symm.trans
      ((hG c.val).choose_spec.2.2 _ (a.map_source hy') t)

/-- Paper: §3.1.2.3, p. 122. As S varies, the open loci of characters unramified
outside S cover the entire space of Hecke characters. -/
theorem iUnion_unramifiedOutside :
    (⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set (HeckeCharacter (𝓞 F) F))) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro c
  have (v : Primes(F)) : CompactSpace (LocalUnits(v)) := by
    have := compactSpace_adicCompletionIntegers (K := F) v
    exact compactSpace_units_of_compactSpace _
  obtain ⟨T, hT⟩ := exists_finset_complexCharacter_eq_one (c.comp (finiteIntegerUnitInsertion F))
  refine Set.mem_iUnion.mpr ⟨T, (mem_unramifiedOutside_iff F T c).mpr ?_⟩
  intro v hv u
  change c (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
    (Units.map (LocalIntegers(v)).subtype.toMonoidHom u)) = 1
  rw [← finiteIntegerUnitInsertion_mulSingle]
  apply hT (Pi.mulSingle v u)
  intro w hw
  have hwv : w ≠ v := fun he ↦ hv (he ▸ hw)
  exact Pi.mulSingle_eq_of_ne hwv _

open scoped RestrictedProduct in
/-- Paper: §3.1.2, p. 120. The value of a global character is the product of its local
values on an idele. Only finitely many finite-place factors differ from one. -/
theorem heckeCharacter_eq_prod_restrictions (c : HeckeCharacter (𝓞 F) F)
    (g : IdeleGroup (𝓞 F) F) :
    let a := fun w : InfinitePlace F => infinitePlaceRestriction F w c
      (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom g)
    let b := fun v : Primes(F) => finitePlaceRestriction F v c
      (Units.map ((RestrictedProduct.evalRingHom (fun w : Primes(F) => w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g)
    b.HasFiniteMulSupport ∧ c (QuotientGroup.mk g) = (∏ w, a w) * ∏ᶠ v, b v := by
  classical
  let A (v : Primes(F)) := (v.adicCompletionIntegers F).units
  let X := (w : InfinitePlace F) → w.Completionˣ
  let Y := Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, A v]
  obtain ⟨e, he⟩ := (ideleGroup_topology F).2.2.2.1
  let q : IdeleGroup (𝓞 F) F →ₜ* IdeleClassGroup (𝓞 F) F :=
    ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let d := (c.comp q).comp (e.symm : (X × Y) →ₜ* IdeleGroup (𝓞 F) F)
  let d₁ := d.comp (ContinuousMonoidHom.inl X Y)
  let d₂ := d.comp (ContinuousMonoidHom.inr X Y)
  let a (w : InfinitePlace F) := infinitePlaceRestriction F w c ((e g).1 w)
  let b (v : Primes(F)) := finitePlaceRestriction F v c ((e g).2 v)
  have harch (w : InfinitePlace F) (u : w.Completionˣ) :
      e (IdeleGroup.ofCompletion (𝓞 F) F w u) = (Pi.mulSingle w u, 1) := by
    refine Prod.ext (funext fun j ↦ Units.ext ?_) ?_
    · rw [(he _).1 j]
      change Pi.mulSingle (M := fun t : InfinitePlace F ↦ t.Completion) w u.val j =
        (Pi.mulSingle (M := fun t : InfinitePlace F ↦ t.Completionˣ) w u j).val
      by_cases hj : j = w
      · subst j
        simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    · apply RestrictedProduct.ext
      exact fun j ↦ Units.ext ((he _).2 j)
  have hfin (v : Primes(F)) (u : (v.adicCompletion F)ˣ) :
      e (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) = (1, RestrictedProduct.mulSingle A v u) := by
    refine Prod.ext (funext fun j ↦ Units.ext ((he _).1 j)) ?_
    apply RestrictedProduct.ext
    intro j
    apply Units.ext
    rw [(he _).2 j]
    change Pi.mulSingle (M := fun t : Primes(F) ↦ t.adicCompletion F) v u.val j =
      (Pi.mulSingle (M := fun t : Primes(F) ↦ (t.adicCompletion F)ˣ) v u j).val
    by_cases hj : j = v
    · subst j
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  have h₁ (w : InfinitePlace F) : d₁ (Pi.mulSingle w ((e g).1 w)) = a w := by
    change c (q (e.symm (Pi.mulSingle w ((e g).1 w), 1))) = _
    rw [← harch, e.symm_apply_apply]
    rfl
  have h₂ (v : Primes(F)) : d₂ (RestrictedProduct.mulSingle A v ((e g).2 v)) = b v := by
    change c (q (e.symm (1, RestrictedProduct.mulSingle A v ((e g).2 v)))) = _
    rw [← hfin, e.symm_apply_apply]
    rfl
  -- An idele is integral almost everywhere, and the character is unramified outside a finite set.
  have hc : c ∈ ⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set _) := by
    rw [iUnion_unramifiedOutside F]
    trivial
  obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hc
  have hsupport : b.HasFiniteMulSupport := by
    apply Filter.eventually_cofinite.mp
    filter_upwards [T.eventually_cofinite_notMem, (e g).2.property] with v hv hu
    let u := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨(e g).2 v, hu⟩
    exact (mem_unramifiedOutside_iff F T c).mp hT v hv u
  have hp := (hasProd_restrictedProduct_mulSingle A (e g).2).map d₂ d₂.continuous
  have hprod : HasProd b (d₂ (e g).2) := hp.congr_fun fun v ↦ (h₂ v).symm
  have hA (w : InfinitePlace F) : (e g).1 w =
      Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom g := Units.ext ((he g).1 w)
  have hB (v : Primes(F)) : (e g).2 v =
      Units.map ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g := Units.ext ((he g).2 v)
  dsimp only
  simp_rw [← hA, ← hB]
  refine ⟨hsupport, ?_⟩
  change c (q g) = (∏ w, a w) * ∏ᶠ v, b v
  have ht : (∏' v, b v) = ∏ᶠ v, b v := tprod_eq_finprod hsupport
  rw [← ht, hprod.tprod_eq]
  have hinf : d₁ (e g).1 = ∏ w, a w := by
    conv_lhs => rw [← Finset.univ_prod_mulSingle (e g).1, map_prod]
    exact Finset.prod_congr rfl fun w _ ↦ h₁ w
  rw [← hinf]
  change c (q g) = d ((e g).1, 1) * d (1, (e g).2)
  rw [← map_mul]
  change c (q g) = c (q (e.symm ((e g).1 * 1, 1 * (e g).2)))
  rw [mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply]

end Ideles

end RiemannMasullo
