module

import Lean
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.PontryaginDual
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.MeasureTheory.Group.Integral
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3b
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Rational finite-stage Meyer criterion

Pinned base: mccorvie/riemann-masullo, 25a6833189618215573ba704bde262a030484ad6,
Lean 4.36.0. Replay from the repository root:

    lake build RiemannMasullo.Ch06_LocalGlobal.Sec2
    lake lean research/MeyerRationalFiniteStages.lean

The file audits both proof terms and checks the exact rational specialization
of the library statement. The criterion
uses a bounded set of test representatives, allows an arbitrary sequence of
tests and any norm section, and includes both ordinary and Fourier-side weighted
Mellin estimates. Former private facts are used across chapters in this
downstream certificate. Chapter 6 depends on Chapter 5.
-/

section
open Function Set
namespace RiemannMasullo
/-- Resolving an orbit that factors through one finite abelian group gives a
fixed list of character families whose sum is the original sequence. Each
character family is a finite linear combination of translates. -/
private theorem meyer_finite_orbit_resolution {A E : Type*} [AddCommGroup A] [Fintype A]
    [AddCommGroup E] [Module ℂ E] (f : A → ℕ → E)
    (L : A → E →ₗ[ℂ] E) (hL : ∀ a b n, L a (f b n) = f (a+b) n) :
    let p (χ : AddChar A ℂ) (n : ℕ) := (Fintype.card A : ℂ)⁻¹ •
      ∑ a : A, χ (-a) • f a n
    (∀ n, ∑ χ : AddChar A ℂ, p χ n = f 0 n) ∧
      ∀ (χ : AddChar A ℂ) (n : ℕ) (a : A), L a (p χ n) = χ a • p χ n := by
  classical
  intro p
  have hcard : (Fintype.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · intro n
    change (∑ χ : AddChar A ℂ, (Fintype.card A : ℂ)⁻¹ • ∑ a : A, χ (-a) • f a n) = _
    rw [← Finset.smul_sum,Finset.sum_comm]
    simp_rw [← Finset.sum_smul,AddChar.sum_apply_eq_ite]
    simp [ite_smul,inv_smul_smul₀ hcard]
  · intro χ n a
    change L a ((Fintype.card A : ℂ)⁻¹ • ∑ b : A, χ (-b) • f b n) = _
    rw [map_smul,map_sum]
    simp_rw [map_smul,hL]
    change _ = χ a • ((Fintype.card A : ℂ)⁻¹ • _)
    rw [smul_comm (χ a) (Fintype.card A : ℂ)⁻¹]
    apply congrArg ((Fintype.card A : ℂ)⁻¹ • ·)
    rw [Finset.smul_sum]
    apply Fintype.sum_equiv (Equiv.addLeft a)
    intro b
    change χ (-b) • f (a+b) n = χ a • (χ (-(a+b)) • f (a+b) n)
    rw [smul_smul,← AddChar.map_add_eq_mul,show a + -(a+b) = -b by abel]

/-- An open subgroup fixing every member of a family in a representation of a
compact abelian group gives finitely many common continuous character sectors.
Their resolving maps are finite sums of the original continuous translations. -/
private theorem meyer_open_orbit_resolution {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℂ E]
    (R : G →* (E →L[ℂ] E)) (v : ℕ → E) (D : Subgroup G)
    (hD : IsOpen (D : Set G)) (hfix : ∀ d ∈ D, ∀ n, R d (v n) = v n) :
    ∃ (m : ℕ) (ω : Fin m → PontryaginDual G) (P : Fin m → (E →L[ℂ] E)),
      (∀ i, (Set.range (ω i)).Finite) ∧
      (∀ i, P i ∈ Submodule.span ℂ (Set.range R)) ∧
      (∀ n, ∑ i, P i (v n) = v n) ∧
      ∀ i n g, R g (P i (v n)) = (ω i g : ℂ) • P i (v n) := by
  classical
  let Z := G ⧸ D
  let q : G →* Z := QuotientGroup.mk' D
  let : Finite Z := Subgroup.quotient_finite_of_isOpen D hD
  let : DiscreteTopology Z := QuotientGroup.discreteTopology hD
  let : Fintype (Additive Z) := Fintype.ofFinite _
  let A := Additive Z
  let rep (a : A) := (Additive.toMul a).out
  have hrep (a : A) : q (rep a) = Additive.toMul a := Quotient.out_eq _
  let act (a : G) := R a
  have same {g h : G} (he : q g = q h) (n : ℕ) : act g (v n) = act h (v n) := by
    have hd : h⁻¹*g ∈ D := (QuotientGroup.eq_one_iff _).mp (show q (h⁻¹*g) = 1 by simp [he])
    have H : act (h*(h⁻¹*g)) (v n) = act h (v n) := by
      change R (h*(h⁻¹*g)) (v n) = _
      rw [map_mul,mul_apply_eq_comp,hfix _ hd]
    simpa using H
  let L (a : A) := (act (rep a)).toLinearMap
  let f (a : A) (n : ℕ) := act (rep a) (v n)
  have hf (a b : A) (n : ℕ) : L a (f b n) = f (a+b) n := by
    change ((R (rep a) * R (rep b)) (v n)) = _
    rw [← map_mul]
    apply same
    rw [map_mul,hrep,hrep,hrep]
    rfl
  let e := Fintype.equivFin (AddChar A ℂ)
  let P (χ : AddChar A ℂ) : E →L[ℂ] E :=
    (Fintype.card A : ℂ)⁻¹ • ∑ a : A, χ (-a) • act (rep a)
  let ω (χ : AddChar A ℂ) : PontryaginDual G :=
    let c := AddChar.circleEquivComplex.symm χ
    { toMonoidHom := c.toMonoidHom.comp q
      continuous_toFun := (continuous_of_discreteTopology : Continuous c.toMonoidHom).comp
        QuotientGroup.continuous_mk }
  have hω (χ : AddChar A ℂ) (g : G) : (ω χ g : ℂ) = χ (Additive.ofMul (q g)) := rfl
  let p (χ : AddChar A ℂ) (n : ℕ) := (Fintype.card A : ℂ)⁻¹ • ∑ a : A, χ (-a) • f a n
  have hp (χ : AddChar A ℂ) (n : ℕ) : P χ (v n) = p χ n := by
    simp only [P,smul_apply,sum_apply,p,f]
  obtain ⟨hs,he⟩ := meyer_finite_orbit_resolution f L hf
  refine ⟨Fintype.card (AddChar A ℂ),fun j ↦ ω (e.symm j),fun j ↦ P (e.symm j),?_,?_,?_,?_⟩
  · intro i
    apply (Set.finite_range (fun b : A ↦ (AddChar.circleEquivComplex.symm (e.symm i)) b)).subset
    rintro _ ⟨g,rfl⟩
    exact ⟨Additive.ofMul (q g),rfl⟩
  · intro i
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro b _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rep b,rfl⟩)
  · intro n
    have hz : f 0 n = v n := (same (hrep 0) n).trans (by simp [act])
    calc
      _ = ∑ χ : AddChar A ℂ, p χ n := Fintype.sum_equiv e.symm _ _ fun i ↦ hp _ n
      _ = v n := (hs n).trans hz
  · intro i n g
    rw [hp,hω]
    let a := Additive.ofMul (q g)
    have identical : act g (p (e.symm i) n) = L a (p (e.symm i) n) := by
      dsimp only [p]
      rw [map_smul,map_smul,map_sum,map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [map_smul,map_smul]
      apply congrArg (_ • ·)
      change (R g * R (rep b)) (v n) = (R (rep a) * R (rep b)) (v n)
      rw [← map_mul,← map_mul]
      apply same
      rw [map_mul,map_mul,hrep a]
      rfl
    exact identical.trans (he (e.symm i) n a)

variable {F : Type*} [Field F] [NumberField F]
open Function Set IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing
/-- For every degree-one field, the Mellin bounds on the tests alone resolve
a sequence of actual theta classes into a common finite collection of
continuous character sectors for the full norm-one quotient. -/
private theorem meyer_degree_one_orbit (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hF : Module.finrank ℚ F = 1) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing F T)))
    (h : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    let x (n : ℕ) := (sLocalAdelicTheta F T).ker.mkQ (v n)
    let A := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    ∃ (m : ℕ) (ω : Fin m → PontryaginDual (sIdeleQuotientNorm F T).ker)
      (P : Fin m → (SLocalAdelicThetaSpace F T →L[ℂ] SLocalAdelicThetaSpace F T)),
      (∀ j, (range (ω j)).Finite) ∧
      (∀ j, P j ∈ Submodule.span ℂ (range fun g : (sIdeleQuotientNorm F T).ker ↦ A g.val)) ∧
      (∀ n, ∑ j, P j (x n) = x n) ∧
      ∀ j n (g : (sIdeleQuotientNorm F T).ker), A g.val (P j (x n)) = (ω j g : ℂ) • P j (x n) := by
  intro x A
  obtain ⟨k,hk⟩ := sLocalMellinSchwartzBounds_meyer_mellin_bounds_level T τ hτ v h
  obtain ⟨D,hD,hd⟩ := sLocalMellinSchwartzBounds_meyer_degree_one_open_quotient T hF k
  let N := (sIdeleQuotientNorm F T).ker
  let : CompactSpace N := isCompact_iff_compactSpace.mp
    (show IsCompact ((sIdeleQuotientNorm F T) ⁻¹' ({1} : Set ℝ≥0ˣ)) from
      (isProperMap_sIdeleQuotientNorm F T).isCompact_preimage isCompact_singleton)
  apply meyer_open_orbit_resolution (A.comp N.subtype) x D hD
  intro g hg n
  obtain ⟨u,hu,ha,hu'⟩ := hd g hg
  change A g.val (x n) = x n
  rw [← hu]
  exact ((existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 u (v n)).trans (hk u ha hu' n)

set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "B(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
local notation "N(" T ")" => (sIdeleQuotientNorm F T).ker
local notation "Q(" T ")" => (sLocalAdelicTheta F T).ker.mkQ
local notation "c(" T "," χ "," z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F T)
  (isProperMap_sIdeleQuotientNorm F T).continuous ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) z

set_option maxHeartbeats 800000 in
/-- Finite linear combinations of norm-one translations preserve the complete
Mellin bounds, including every angular seminorm and every signed derivative.
On the normalized charts the added multiplier is a finite character polynomial. -/
private theorem meyer_sector_bounds (T : Finset V) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (v w : ℕ → B(T)) (hv : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral)
    (P : SLocalAdelicThetaSpace F T →L[ℂ] SLocalAdelicThetaSpace F T)
    (hP : P ∈ Submodule.span ℂ (range fun g : N(T) ↦
      (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose g.val))
    (hw : ∀ n, Q(T) (w n) = P (Q(T) (v n))) :
    sLocalMellinSchwartzBounds T τ w sLocalThetaMellinIntegral := by
  classical
  let A := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
  obtain ⟨b,hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP
  have hOp : P = ∑ g ∈ b.support, b g • A g.val := hb.symm
  let W (χ : PontryaginDual (SIdeleQuotient F T)) : ℂ := ∑ g ∈ b.support, b g * (χ g.val : ℂ)
  let C := ∑ g ∈ b.support, ‖b g‖
  have bounded (χ : PontryaginDual (SIdeleQuotient F T)) : ‖W χ‖ ≤ C := by
    exact (norm_sum_le ..).trans (by simp [C,Circle.norm_coe])
  have factor (χ : PontryaginDual (SIdeleQuotient F T)) (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
      sLocalThetaMellinIntegral (w n) c(T,χ,z) = W χ * sLocalThetaMellinIntegral (v n) c(T,χ,z) := by
    let c := c(T,χ,z)
    let E : SLocalAdelicThetaSpace F T →ₗ[ℂ] ℂ := (ContinuousMap.evalCLM ℂ
      ⟨c,sLocalOrderBound_positive χ hz⟩).toLinearMap.comp ((Submodule.subtype _).comp sLocalThetaMellin)
    have he (f : B(T)) : E (Q(T) f) = sLocalThetaMellinIntegral f c := by
      change sLocalIdelicZFunction f c = _
      rw [sLocalThetaMellinIntegral_eq_zeta f ⟨χ,z,hz,rfl⟩,sLocalIdelicZFunction_eq_integral f ⟨χ,z,hz,rfl⟩]
    have trans (g : N(T)) :
        E (A g.val (Q(T) (v n))) = (χ g.val : ℂ)*E (Q(T) (v n)) := by
      obtain ⟨u,hu⟩ := QuotientGroup.mk_surjective g.val
      have hA := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose_spec.2 u (v n)
      rw [← hu]
      change E (A (QuotientGroup.mk u) (Q(T) (v n))) = _
      rw [show A (QuotientGroup.mk u) (Q(T) (v n)) = Q(T) (schwartzBruhatUnitTranslate u (v n)) from hA]
      change (sLocalIdelicMellin (schwartzBruhatUnitTranslate u (v n))).val ⟨c,_⟩ = _
      rw [sLocalIdelicMellin_unitTranslate]
      apply congrArg (· * E (Q(T) (v n)))
      change (χ (QuotientGroup.mk u) : ℂ) * (((sIdeleQuotientNorm F T (QuotientGroup.mk u)).val : ℝ) : ℂ)^z = _
      rw [hu,g.property]
      simp
    rw [← he,← he,hw n,hOp]
    simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul,
      smul_eq_mul,trans,W,Finset.sum_mul,mul_assoc]
  apply (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ w).mpr
  intro a ha
  obtain ⟨H,hFG,hs,hbnd⟩ := (sLocalMellinSchwartzBounds_meyer_zeroth_iff T τ v).mp hv a ha
  refine ⟨H,hFG,?_,?_⟩
  · intro χ hχ n z hz
    rw [factor χ.val n z (hz.symm ▸ zero_lt_one.trans ha),hs _ hχ _ _ hz,mul_zero]
  · intro p k m
    obtain ⟨M,hM⟩ := hbnd p k m
    refine ⟨C*M,fun χ n z hz ↦ ?_⟩
    rw [factor χ.val.val n z (hz.symm ▸ zero_lt_one.trans ha),mul_left_comm (z^m),norm_mul,
      mul_left_comm ((1+p χ)^k)]
    exact mul_le_mul (bounded _) (hM χ n z hz) (by positivity) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)

/-- On a finite sum of actual norm-one isotypes, Fourier intertwines each action
with its inverse. This follows from the public Fourier-isotype theorem alone. -/
private theorem meyer_degree_one_fourier_intertwines (T : Finset V) (hF : Module.finrank ℚ F = 1)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v : ℕ → B(T)) (hv : sLocalMellinSchwartzBounds T τ v sLocalThetaMellinIntegral) :
    let A := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    let FT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
    ∀ (g : N(T)) n, FT (A g.val (Q(T) (v n))) = A g.val⁻¹ (FT (Q(T) (v n))) := by
  intro A FT
  obtain ⟨m,ω,P,_,_,hS,he⟩ := meyer_degree_one_orbit T hF τ hτ v hv
  intro g n
  let x (i : Fin m) := P i (Q(T) (v n))
  have sum_eq : ∑ i, x i = Q(T) (v n) := hS n
  have h (i : Fin m) : FT (A g.val (x i)) = A g.val⁻¹ (FT (x i)) := by
    have hi : x i ∈ actionIsotype (A.comp (N(T)).subtype) (ω i) :=
      (mem_actionIsotype _ _ _).mpr (he i n)
    have hf := (sLocalThetaFourier_mem_isotype (F := F) (S := T) (ω i) (x i)).mpr hi
    have H := (mem_actionIsotype _ _ _).mp hf g⁻¹
    have hg : ((ω i)⁻¹ g⁻¹ : ℂ) = (ω i g : ℂ) := by
      apply congrArg (fun t : Circle ↦ (t : ℂ))
      change (((ω i) g⁻¹)⁻¹ : Circle) = _
      rw [map_inv,inv_inv]
    change A g.val⁻¹ (FT (x i)) = _ at H
    rw [H,he i n g,map_smul,hg]
  rw [← sum_eq,map_sum,map_sum,map_sum,map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ h i

/-- Fourier transport sends the finite span of norm-one translations back into
itself. Conjugating exchanges the translating group elements with their inverses. -/
private theorem meyer_sector_fourier (T : Finset V)
    (P : SLocalAdelicThetaSpace F T →L[ℂ] SLocalAdelicThetaSpace F T)
    (hP : P ∈ Submodule.span ℂ (range fun g : N(T) ↦
      (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose g.val))
    (z : ℕ → SLocalAdelicThetaSpace F T)
    (hint : let A := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
      let FT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
      ∀ (g : N(T)) n, FT (A g.val (z n)) = A g.val⁻¹ (FT (z n))) :
    let FT := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
    let A := (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose
    ∃ P' ∈ Submodule.span ℂ (range fun g : N(T) ↦ A g.val),
      ∀ n, FT (P (z n)) = P' (FT (z n)) := by
  intro FT A
  classical
  obtain ⟨b,hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hP
  have hOp : P = ∑ g ∈ b.support, b g • A g.val := hb.symm
  let P' := ∑ g ∈ b.support, b g • A g.val⁻¹
  refine ⟨P',Submodule.sum_mem _ fun g _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨g⁻¹,rfl⟩),fun n ↦ ?_⟩
  rw [hOp]
  simp only [P',ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (b g • ·) (hint g n)

/-- The two full seminorm conditions pass to every finite norm-one translate
component of a family on the actual theta quotient. -/
private theorem meyer_sector_paired (T : Finset V) (hF : Module.finrank ℚ F = 1) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T) (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (v w : ℕ → B(T)) (P : SLocalAdelicThetaSpace F T →L[ℂ] SLocalAdelicThetaSpace F T)
    (hP : P ∈ Submodule.span ℂ (range fun g : N(T) ↦
      (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose g.val))
    (hw : ∀ n, Q(T) (w n) = P (Q(T) (v n)))
    (hv : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → B(T))),
      sLocalMellinSchwartzBounds T τ f sLocalThetaMellinIntegral) :
    ∀ f ∈ ({w,fun n ↦ sAdeleSchwartzFourier (w n)} : Set (ℕ → B(T))),
      sLocalMellinSchwartzBounds T τ f sLocalThetaMellinIntegral := by
  obtain ⟨P',hP',hp⟩ := meyer_sector_fourier T P hP (fun n ↦ Q(T) (v n))
    (meyer_degree_one_fourier_intertwines T hF τ hτ v (hv _ (by simp)))
  have hf := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose_spec.2
  intro f hf'
  rcases Set.mem_insert_iff.mp hf' with hzero | hrest
  · subst f
    exact meyer_sector_bounds T τ v w (hv _ (by simp)) P hP hw
  · rw [Set.mem_singleton_iff.mp hrest]
    apply meyer_sector_bounds T τ (fun n ↦ sAdeleSchwartzFourier (v n)) _ (hv _ (by simp)) P' hP'
    intro n
    rw [← hf,← hf,hw n,hp]

/-- In degree one it suffices to prove the inverse for families in one finite-order
norm-one character subspace. This uses the original paired Mellin estimates on
each summand and gives boundedness in the original quotient. -/
private theorem meyer_degree_one_reduce_to_isotypes (T : Finset V)
    (hF : Module.finrank ℚ F = 1) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F T)
    (hτ : RightInverse τ (sIdeleQuotientNorm F T))
    (hsingle : ∀ (ω : PontryaginDual N(T)), (range ω).Finite → ∀ u : ℕ → B(T),
      (∀ n (g : N(T)), (existsUnique_sLocalThetaAction (F := F) (S := T)).exists.choose g.val
        (Q(T) (u n)) = (ω g : ℂ) • Q(T) (u n)) →
      (∀ f ∈ ({u,fun n ↦ sAdeleSchwartzFourier (u n)} : Set (ℕ → B(T))),
        sLocalMellinSchwartzBounds T τ f sLocalThetaMellinIntegral) →
      Bornology.IsVonNBounded ℂ (range fun n ↦ Q(T) (u n)))
    (v : ℕ → B(T))
    (hv : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → B(T))),
      sLocalMellinSchwartzBounds T τ f sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ Q(T) (v n)) := by
  classical
  obtain ⟨m,ω,P,hfinite,hP,hs,he⟩ := meyer_degree_one_orbit T hF τ hτ v (hv v (by simp))
  let x (n : ℕ) := Q(T) (v n)
  have lift (i : Fin m) (n : ℕ) : ∃ u : B(T), Q(T) u = P i (x n) :=
    (sLocalAdelicTheta F T).ker.mkQ_surjective _
  choose u hu using lift
  have bounded (i : Fin m) : Bornology.IsVonNBounded ℂ (range fun n ↦ P i (x n)) := by
    have h := hsingle (ω i) (hfinite i) (u i) (fun n g ↦ by rw [hu]; exact he i n g)
      (meyer_sector_paired T hF τ hτ v (u i) (P i) (hP i) (hu i) hv)
    simpa only [hu] using h
  have sumBounded (s : Finset (Fin m)) :
      Bornology.IsVonNBounded ℂ (range fun n ↦ ∑ i ∈ s, P i (x n)) := by
    induction s using Finset.induction_on with
    | empty => simpa using Bornology.isVonNBounded_singleton (𝕜 := ℂ) (0 : SLocalAdelicThetaSpace F T)
    | insert a s ha ih =>
      apply ((bounded a).add ih).subset
      rintro _ ⟨n,rfl⟩
      change (∑ i ∈ insert a s, P i (x n)) ∈ _
      rw [Finset.sum_insert ha]
      exact ⟨_,⟨n,rfl⟩,_,⟨n,rfl⟩,rfl⟩
  simpa only [x,hs] using sumBounded Finset.univ

end RiemannMasullo
end

section
section
open Function Filter Set MeasureTheory NumberField IsDedekindDomain Topology InfinitePlace.Completion
open scoped NNReal ENNReal NumberField.AdeleRing Pointwise
namespace RiemannMasullo
section
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "K(" v ")" => HeightOneSpectrum.adicCompletion F v
local notation "U(" v ")" => (HeightOneSpectrum.adicCompletionIntegers F v).units
local notation "N(" v ")" => (Units.map nnNormHom.toMonoidHom : K(v)ˣ →* ℝ≥0ˣ)
local notation "μ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "c(" v "," ρ "," z ")" => quasiCharacterNormTwist (N(v)) (continuous_finiteLocalModule v)
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ) z
local notation "G(" v ")" => finiteStandardGaussian v 1
private theorem meyer_gaussian_unitary_lower (v : V) (ρ : PontryaginDual K(v)ˣ) (hρ : ∀ u ∈ U(v), ρ u = 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, 0 < z.re →
      B ≤ ‖@localIdelicZetaIntegral _ _ _ (borel _) (μ(v)) (fun x ↦ G(v) (Multiplicative.ofAdd x)) (c(v,ρ,z))‖ := by
  let : MeasurableSpace K(v)ˣ := borel _
  let : BorelSpace K(v)ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  have hUo : IsOpen (U(v) : Set K(v)ˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U(v) : Set K(v)ˣ) := by
    let : ProperSpace K(v) := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set K(v))
    convert isCompact_closedBall (0 : K(v)) 1 using 1
    ext x
    simp only [SetLike.mem_coe,Metric.mem_closedBall,dist_zero_right,Valued.toNormedField.norm_le_one_iff]
    exact HeightOneSpectrum.mem_adicCompletionIntegers _ _ _
  let mass : ℝ := (μ(v)).real U(v)
  have hm : 0 < mass := ENNReal.toReal_pos (hUo.measure_pos _ ⟨1,Subgroup.one_mem _⟩).ne' hUc.measure_lt_top.ne
  obtain ⟨π₀,hπ₀⟩ := (Valued.v : Valuation K(v) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : K(v)ˣ := Units.mk0 π₀ hπ₀.ne_zero
  have hπ : (Valued.v : Valuation K(v) (WithZero (Multiplicative ℤ))).IsUniformizer π.val := hπ₀
  refine ⟨mass/2,half_pos hm,fun z hz ↦ ?_⟩
  let c := c(v,ρ,z)
  let f := G(v)
  obtain ⟨D,hD,hEval⟩ := exists_finiteEigendistribution_eq_zetaIntegral v ρ z hz
  have heig : ∀ (u : K(v)ˣ) (f : SchwartzBruhat (Multiplicative K(v))),
      D (schwartzBruhatUnitTranslate u f) = c u * D f := hD
  have hlocal : D (finitePlaceDifference v π f) = (1-c π) * D f := by
    change D (f-schwartzBruhatUnitTranslate π f) = _
    rw [map_sub,heig]
    ring
  have hu (g : K(v)ˣ) (hg : g ∈ U(v)) : c g = 1 := by
    change (ρ g : ℂ) * (‖g.val‖ : ℂ)^z = 1
    rw [hρ g hg]
    rw [Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hg)]
    simp
  have hi : D (finitePlaceDifference v π f) = (mass : ℂ) := by
    rw [hEval]
    have hh : (fun x ↦ finitePlaceDifference v π f (Multiplicative.ofAdd x)) =
        (Units.val '' (U(v) : Set K(v)ˣ)).indicator (fun _ ↦ (1 : ℂ)) :=
      funext (finitePlaceDifference_integerIndicator v π hπ)
    rw [hh]
    exact localIdelicZetaIntegral_indicator (μ(v)) c _ hUo.measurableSet hUc.measure_lt_top.ne hu
  have huπ : ‖c π‖ ≤ 1 := by
    change ‖(ρ π : ℂ) * (‖π.val‖ : ℂ)^z‖ ≤ 1
    rw [norm_mul,Circle.norm_coe,one_mul,Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.mpr π.ne_zero)]
    apply Real.rpow_le_one (norm_nonneg _)
    · rw [norm_uniformizer_adicCompletion v _ hπ]
      exact (inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).le
    · exact hz.le
  have hk : ‖1-c π‖ ≤ 2 := (norm_sub_le _ _).trans (by simp; linarith)
  have hm' : mass ≤ 2 * ‖D f‖ := calc
    mass = ‖(mass:ℂ)‖ := by rw [Complex.norm_real,Real.norm_of_nonneg hm.le]
    _ = ‖1-c π‖*‖D f‖ := by rw [← norm_mul,← hlocal,hi]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (norm_nonneg _)
  rw [← hEval]
  linarith

end
section
variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
set_option quotPrecheck false
local notation "K" => v.adicCompletion F
local notation "O" => v.adicCompletionIntegers F
local notation "μv" => finiteLocalAdditiveTamagawaMeasure F v
local notation "νv" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ψ" => finiteLocalStandardCharacter F v
local notation "U" => (v.adicCompletionIntegers F).units
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "G(" ρ ")" => fun x : K ↦ finiteStandardGaussian v cc(ρ) (Multiplicative.ofAdd x)
noncomputable local instance : MeasurableSpace K := borel _
local instance : BorelSpace K := ⟨rfl⟩
noncomputable local instance : MeasurableSpace Kˣ := borel _
local instance : BorelSpace Kˣ := ⟨rfl⟩
private theorem meyer_shell_integral (ρ : PontryaginDual Kˣ) (f : K → ℂ) (y : Kˣ)
    (hout : ∀ u : Kˣ, ‖u.val‖ ≠ ‖y.val‖ → f u.val = 0)
    (hunit : ∀ u : Kˣ, ‖u.val‖ = 1 → f (y.val * u.val) = (ρ u : ℂ)⁻¹ * f y.val)
    (z : ℂ) :
    (∫ u : Kˣ, f u.val * ((ρ u : ℂ) * (‖u.val‖ : ℂ)^z) ∂νv) =
      ((νv).real U * f y.val * (ρ y : ℂ)) * (‖y.val‖ : ℂ)^z := by
  let : (νv).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  rw [← integral_mul_left_eq_self (μ := νv) _ y]
  let c := f y.val * (ρ y : ℂ) * (‖y.val‖ : ℂ)^z
  have hh (u : Kˣ) : f (y*u).val * ((ρ (y*u) : ℂ) * (‖(y*u).val‖ : ℂ)^z) =
      (U : Set Kˣ).indicator (fun _ ↦ c) u := by
    rw [Units.val_mul,norm_mul,map_mul,Circle.coe_mul]
    by_cases hu : u ∈ U
    · have hn := (finiteUnit_norm v u).mp hu
      rw [indicator_of_mem hu,hunit u hn,hn,mul_one]
      dsimp [c]
      field_simp
    · have hn := (finiteUnit_norm v u).not.mp hu
      rw [indicator_of_notMem hu,show f (y.val * u.val) = 0 from hout (y*u) (by
        rw [Units.val_mul,norm_mul]; simpa [norm_ne_zero_iff.mpr y.ne_zero] using hn),zero_mul]
  have hUo : IsOpen (U : Set Kˣ) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring K)
  rw [show (fun u : Kˣ ↦ _) = _ from funext hh]
  change (∫ u, (U : Set Kˣ).indicator (fun _ ↦ c) u ∂νv) = _
  rw [integral_indicator hUo.measurableSet,setIntegral_const]
  simp [c,Complex.real_smul,mul_assoc]

private theorem meyer_ramified_gaussian_eq (ρ : PontryaginDual Kˣ)
    (hr : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1) : G(ρ) = finiteUnitTest v ρ := by
  classical
  obtain ⟨u,hu,hn⟩ := hr
  have hram : ¬ ∀ w ∈ U, cc(ρ) w = 1 := by
    intro h
    apply hn
    apply Subtype.ext
    exact h u ((finiteUnit_norm v u).mpr hu)
  funext x
  by_cases hx : ‖x‖ = 1
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    let w := Units.mk0 x hx0
    exact (finiteStandardGaussian_integerUnit v cc(ρ) w ((finiteUnit_norm v w).mpr hx)).trans (by
      change (ρ w : ℂ)⁻¹ = finiteUnitTest v ρ w.val
      rw [finiteUnitTest_unit v ρ w,ite_eq_left (show ‖w.val‖ = 1 from hx)])
  · change finiteStandardGaussianValue v cc(ρ) x = _
    rw [finiteStandardGaussianValue,ite_eq_right hram,Set.indicator_of_notMem,finiteUnitTest,dite_eq_right hx]
    rintro ⟨w,hw,rfl⟩
    exact hx ((finiteUnit_norm v w).mp hw)

private theorem meyer_ramified_gaussian_pair (ρ : PontryaginDual Kˣ)
    (hr : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1) :
    ∃ b : ℂ, ∃ q : ℝ, b ≠ 0 ∧ 0 < q ∧ ∀ z : ℂ,
      (∫ u : Kˣ, tamagawaFourier μv ψ (G(ρ)) u.val *
        ((ρ⁻¹ u : ℂ)*(‖u.val‖ : ℂ)^z) ∂νv) = b * (q : ℂ)^z := by
  rw [meyer_ramified_gaussian_eq v ρ hr]
  let g := tamagawaFourier μv ψ (finiteUnitTest v ρ)
  obtain ⟨y,hy⟩ := finiteFourier_unit_ne_zero v ρ
  have hy0 : y ≠ 0 := by
    rintro rfl
    obtain ⟨u,hu,hne⟩ := hr
    exact hne (finiteFourier_implies_unit_trivial v ρ hy u hu (by simp))
  let t := Units.mk0 y hy0
  have hm : ((νv).real U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (unitMass_pos v).ne'
  refine ⟨(νv).real U * g y * (ρ⁻¹ t : ℂ), ‖y‖,
    mul_ne_zero (mul_ne_zero hm hy) (Circle.coe_ne_zero _),norm_pos_iff.mpr hy0,fun z ↦ ?_⟩
  apply meyer_shell_integral v ρ⁻¹ g t
  · intro u hne
    by_contra hn
    exact hne (le_antisymm (finiteFourier_common_radius v ρ hr hy hn)
      (finiteFourier_common_radius v ρ hr hn hy))
  · intro u hu
    rw [mul_comm,show (ρ⁻¹ u : ℂ) = (ρ u : ℂ)⁻¹ from rfl,inv_inv]
    exact finiteFourier_unit_covariant v ρ u hu y

/-- The ramified Fourier factor has a fixed positive modulus on each full vertical
line, without a restriction on the line or a choice of an imaginary shift. -/
private theorem meyer_ramified_gaussian_vertical (ρ : PontryaginDual Kˣ)
    (hr : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1) (a : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℂ, z.re = a →
      ‖∫ u : Kˣ, tamagawaFourier μv ψ (G(ρ)) u.val *
        ((ρ⁻¹ u : ℂ)*(‖u.val‖ : ℂ)^z) ∂νv‖ = A := by
  obtain ⟨b,q,hb,hq,hz⟩ := meyer_ramified_gaussian_pair v ρ hr
  refine ⟨‖b‖ * q^a,mul_pos (norm_pos_iff.mpr hb) (Real.rpow_pos_of_pos hq a),fun z h ↦ ?_⟩
  rw [hz z,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hq,h]

private theorem meyer_ramified_gaussian_original (ρ : PontryaginDual Kˣ)
    (hr : ∃ u : Kˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1) (z : ℂ) :
    (∫ u : Kˣ, (G(ρ)) u.val * ((ρ u : ℂ)*(‖u.val‖ : ℂ)^z) ∂νv) = (νv).real U := by
  rw [meyer_ramified_gaussian_eq v ρ hr]
  have h := meyer_shell_integral v ρ (finiteUnitTest v ρ) 1 (fun u hu ↦ by
    rw [finiteUnitTest_unit,ite_eq_right (by simpa using hu)]) (fun u hu ↦ by
    simp [hu,finiteUnitTest]) z
  simpa [finiteUnitTest] using h

/-- For every finite rational place the Fourier transform of its integer Gaussian
is the same test, with its actual additive Tamagawa normalization. -/
private theorem meyer_rational_disk_selfdual (w : HeightOneSpectrum (𝓞 ℚ)) :
    let h := ((w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)).indicator (fun _ ↦ (1:ℂ)))
    @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ w) (finiteLocalStandardCharacter ℚ w) h = h := by
  intro h
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top,← Ideal.absNorm_eq_one_iff,NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ),NumberField.discr_rat]
    rfl
  have hs : {x : w.adicCompletion ℚ | ‖x‖ ≤ 1} = (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) := by
    ext x
    change ‖x‖ ≤ 1 ↔ _
    rw [Valued.toNormedField.norm_le_one_iff]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  rw [show h = _ from rfl,finiteLocalTamagawaFourier_integers,hd,multiplicity_one_right]
  simp only [pow_zero,Real.sqrt_one,ENNReal.ofReal_one,inv_one,ENNReal.toReal_one,Complex.ofReal_one,one_smul,hs]
  rfl

/-- At every finite rational place, the actual standard test and its additive Fourier
transform both have positive lower Mellin bounds for the matched characters,
uniformly on every positive vertical line. -/
private theorem meyer_rational_finite_test_pair (w : HeightOneSpectrum (𝓞 ℚ))
    (ρ : PontryaginDual (w.adicCompletion ℚ)ˣ) (a : ℝ) (ha : 0 < a) :
    let G := fun x : w.adicCompletion ℚ ↦ finiteStandardGaussian w cc(ρ) (Multiplicative.ofAdd x)
    let FT := @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ w) (finiteLocalStandardCharacter ℚ w)
    let Z := fun (p : w.adicCompletion ℚ → ℂ) (χ : PontryaginDual (w.adicCompletion ℚ)ˣ) (z : ℂ) ↦
      ∫ u : (w.adicCompletion ℚ)ˣ, p u.val * ((χ u : ℂ) * (‖u.val‖ : ℂ)^z)
        ∂(finiteLocalMultiplicativeTamagawaMeasure ℚ w)
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, z.re = a → B ≤ ‖Z G ρ z‖ ∧ B ≤ ‖Z (FT G) ρ⁻¹ z‖ := by
  intro G FT Z
  classical
  by_cases hr : ∃ u : (w.adicCompletion ℚ)ˣ, ‖u.val‖ = 1 ∧ ρ u ≠ 1
  · obtain ⟨A,hA,hF⟩ := meyer_ramified_gaussian_vertical w ρ hr a
    let m := (finiteLocalMultiplicativeTamagawaMeasure ℚ w).real (w.adicCompletionIntegers ℚ).units
    have hm : 0 < m := unitMass_pos w
    refine ⟨min m A,lt_min hm hA,fun z hz ↦ ⟨?_,?_⟩⟩
    · change _ ≤ ‖∫ u : (w.adicCompletion ℚ)ˣ, _ ∂_‖
      rw [meyer_ramified_gaussian_original w ρ hr,Complex.norm_real,Real.norm_of_nonneg hm.le]
      exact min_le_left _ _
    · change _ ≤ ‖∫ u : (w.adicCompletion ℚ)ˣ, _ ∂_‖
      rw [hF z hz]
      exact min_le_right _ _
  · push_neg at hr
    let H := ((w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)).indicator (fun _ ↦ (1:ℂ)))
    have hu (u : (w.adicCompletion ℚ)ˣ) (h : u ∈ (w.adicCompletionIntegers ℚ).units) : ρ u = 1 :=
      hr u ((finiteUnit_norm w _).mp h)
    have hU : ∀ u ∈ (w.adicCompletionIntegers ℚ).units, cc(ρ) u = 1 := by
      intro u h
      change (ρ u : ℂ) = 1
      rw [hu u h,Circle.coe_one]
    have ht : G = H := by
      ext x
      change finiteStandardGaussianValue w cc(ρ) x = _
      rw [finiteStandardGaussianValue,ite_eq_left hU]
    have hT : (fun x : w.adicCompletion ℚ ↦ finiteStandardGaussian w 1 (Multiplicative.ofAdd x)) = H := by
      ext x
      change finiteStandardGaussianValue w 1 x = _
      rw [finiteStandardGaussianValue,ite_eq_left (by simp)]
    have hl (χ : PontryaginDual (w.adicCompletion ℚ)ˣ)
        (hχ : ∀ u ∈ (w.adicCompletionIntegers ℚ).units, χ u = 1) :
        ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = a → C ≤ ‖Z H χ z‖ := by
      obtain ⟨C,hC,HC⟩ := meyer_gaussian_unitary_lower w χ hχ
      refine ⟨C,hC,fun z hz ↦ ?_⟩
      rw [← hT]
      exact HC z (hz.symm ▸ ha)
    obtain ⟨A,hA,h₁⟩ := hl ρ hu
    obtain ⟨B,hB,h₂⟩ := hl ρ⁻¹ (fun u hh ↦ by change (ρ u)⁻¹ = 1; rw [hu u hh,inv_one])
    rw [ht]
    have hf : FT H = H := meyer_rational_disk_selfdual w
    rw [hf]
    exact ⟨min A B,lt_min hA hB,fun z hz ↦ ⟨(min_le_left _ _).trans (h₁ z hz),(min_le_right _ _).trans (h₂ z hz)⟩⟩

end
end RiemannMasullo

namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F]
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 F)
private theorem meyer_finite_standard_congr (v : V) (c d : QuasiCharacter (v.adicCompletion F)ˣ)
    (h : ∀ u ∈ (v.adicCompletionIntegers F).units, c u = d u) :
    finiteStandardGaussian v c = finiteStandardGaussian v d := by
  classical
  ext x
  change finiteStandardGaussianValue v c x.toAdd = finiteStandardGaussianValue v d x.toAdd
  have hu : (∀ u ∈ (v.adicCompletionIntegers F).units, c u = 1) ↔
      ∀ u ∈ (v.adicCompletionIntegers F).units, d u = 1 := by
    constructor
    · intro H u hu; rw [← h u hu]; exact H u hu
    · intro H u hu; rw [h u hu]; exact H u hu
  unfold finiteStandardGaussianValue
  rw [propext hu]
  split_ifs with hh
  · rfl
  · by_cases hx : x.toAdd ∈ Units.val '' (↑(v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ)
    · have hx₀ := hx
      obtain ⟨u,hu,hx'⟩ := hx₀
      rw [indicator_of_mem hx,indicator_of_mem hx,← hx']
      simp [u.ne_zero,h u hu]
    · rw [indicator_of_notMem hx,indicator_of_notMem hx]

private theorem meyer_standard_norm_one_congr (S : Finset V) (c d : QuasiCharacter (SIdeleQuotient F S))
    (h : ∀ g : (sIdeleQuotientNorm F S).ker, c g.val = d g.val) (v : S) :
    finiteStandardGaussian v.val (sLocalFiniteRestriction v c) =
      finiteStandardGaussian v.val (sLocalFiniteRestriction v d) := by
  let ep := ContinuousMulEquiv.prodUnits
    (InfiniteAdeleRing F) ((v : S) → HeightOneSpectrum.adicCompletion F (Subtype.val v))
  let ef := ContinuousMulEquiv.piUnits (M := fun v : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val v))
  let i (x : (v.val.adicCompletion F)ˣ) := (QuotientGroup.mk : (SAdeleRing F S)ˣ → SIdeleQuotient F S)
    (ep.symm (1,ef.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))
  apply meyer_finite_standard_congr
  intro u hu
  have hu' : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu)
  have hn := sLocalFiniteRestriction_norm v u
  let q : ℝ≥0 := ((sIdeleQuotientNorm F S) (i u)).val
  change (1 : ℂ) * ((q : ℝ) : ℂ)^(1:ℂ) = (‖u.val‖ : ℂ) at hn
  rw [one_mul,Complex.cpow_one,hu',Complex.ofReal_one] at hn
  have hi : i u ∈ (sIdeleQuotientNorm F S).ker := by
    apply Units.ext
    apply NNReal.eq
    change (q : ℝ) = 1
    exact_mod_cast hn
  exact h ⟨i u,hi⟩

end RiemannMasullo

namespace RiemannMasullo
open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K(" v ")" => HeightOneSpectrum.adicCompletion ℚ v
local notation "iμ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure ℚ v
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "chart(" S "," η "," z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
  (isProperMap_sIdeleQuotientNorm ℚ S).continuous cc(η) z
private theorem meyer_rational_global_finite_pair (S : Finset V) (η : PontryaginDual (SIdeleQuotient ℚ S))
    (c : QuasiCharacter (SIdeleQuotient ℚ S)) (hc : ∀ g : (sIdeleQuotientNorm ℚ S).ker, c g.val = (η g.val : ℂ))
    (a : ℝ) (ha : 0 < a) :
    let G := fun (v : S) (x : K(v.val)) ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c) (Multiplicative.ofAdd x)
    let FT := fun (v : S) ↦ @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ v.val)
      (finiteLocalStandardCharacter ℚ v.val)
    let Z := fun (p : (v : S) → K(v.val) → ℂ) (χ : PontryaginDual (SIdeleQuotient ℚ S)) (z : ℂ) ↦
      ∏ v : S, @localIdelicZetaIntegral _ _ _ (borel _) (iμ(v.val)) (p v) (sLocalFiniteRestriction v (chart(S,χ,z)))
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, z.re = a → B ≤ ‖Z G η z‖ ∧ B ≤ ‖Z (fun v ↦ FT v (G v)) η⁻¹ z‖ := by
  intro G FT Z
  classical
  let ep := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing ℚ) ((v : S) → K(v.val))
  let ef := ContinuousMulEquiv.piUnits (M := fun v : S ↦ K(v.val))
  let i (v : S) (x : K(v.val)ˣ) := (QuotientGroup.mk : (SAdeleRing ℚ S)ˣ → SIdeleQuotient ℚ S)
    (ep.symm (1,ef.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))
  let j (v : S) : K(v.val)ˣ →ₜ* SIdeleQuotient ℚ S :=
    ⟨{ toFun := i v, map_one' := (sLocalFiniteInsertion_properties v).1, map_mul' := (sLocalFiniteInsertion_properties v).2.1 },
      (sLocalFiniteInsertion_properties v).2.2⟩
  let g (v : S) (x : K(v.val)) := finiteStandardGaussian v.val cc(η.comp (j v)) (Multiplicative.ofAdd x)
  have HG (v : S) : G v = g v := by
    funext x
    exact congrArg (fun f : SchwartzBruhat (Multiplicative K(v.val)) ↦ f (Multiplicative.ofAdd x))
      (meyer_standard_norm_one_congr S c cc(η) hc v)
  let m := sIdeleQuotientNorm ℚ S
  have hn (v : S) (u : K(v.val)ˣ) :
      (((m (j v u) : ℝ≥0) : ℝ) : ℂ) = (‖u.val‖ : ℂ) := by
    have h := sLocalFiniteRestriction_norm v u
    change (1:ℂ) * (((m (j v u) : ℝ≥0) : ℝ) : ℂ)^(1:ℂ) = (‖u.val‖ : ℂ) at h
    rwa [one_mul,Complex.cpow_one] at h
  have hzeta (v : S) (p : K(v.val) → ℂ) (χ : PontryaginDual (SIdeleQuotient ℚ S)) (z : ℂ) :
      @localIdelicZetaIntegral _ _ _ (borel _) (iμ(v.val)) p (sLocalFiniteRestriction v (chart(S,χ,z))) =
        ∫ u : K(v.val)ˣ, p u.val * ((χ.comp (j v) u : ℂ) * (‖u.val‖ : ℂ)^z) ∂(iμ(v.val)) := by
    apply integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    change p u.val * ((χ (j v u) : ℂ) * (((m (j v u) : ℝ≥0) : ℝ) : ℂ)^z) =
      p u.val * ((χ (j v u) : ℂ) * (‖u.val‖ : ℂ)^z)
    rw [hn v u]
  have leaf (v : S) := meyer_rational_finite_test_pair v.val (η.comp (j v)) a ha
  choose b hb hboth using leaf
  refine ⟨∏ v : S, b v,Finset.prod_pos (fun v _ ↦ hb v),fun z hz ↦ ?_⟩
  rw [show G = g from funext HG]
  constructor
  · change _ ≤ ‖∏ v : S, _‖
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun v _ ↦ (hb v).le)
    intro v _
    rw [hzeta]
    exact (hboth v z hz).1
  · change _ ≤ ‖∏ v : S, _‖
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun v _ ↦ (hb v).le)
    intro v _
    rw [hzeta]
    exact (hboth v z hz).2

end RiemannMasullo
end

section
open Set Function
open scoped NNReal
namespace RiemannMasullo
private theorem meyer_finite_character_connected {G : Type*} [Monoid G] [TopologicalSpace G]
    [PreconnectedSpace G] (χ : G →ₜ* Circle) (h : (range χ).Finite) (g : G) : χ g = 1 := by
  let H := range χ
  let : Finite H := h.to_subtype
  let f : G → H := fun x ↦ ⟨χ x,mem_range_self _⟩
  have hf : Continuous f := χ.continuous.subtype_mk _
  have he := (isPreconnected_range hf).subsingleton (mem_range_self g) (mem_range_self 1)
  exact (congrArg Subtype.val he).trans (map_one χ)

private theorem meyer_finite_real_sign (χ : PontryaginDual ℝˣ) (h : (range χ).Finite) :
    (∀ u : ℝˣ, 0 < u.val → χ u = 1) ∧
    (∀ u : ℝˣ, u.val < 0 → χ u = χ (-1)) ∧ (χ (-1))^2 = 1 := by
  let : ConnectedSpace ℝ≥0ˣ := (Nonneg.unitsHomeomorphPos ℝ).connectedSpace_iff.mpr
    (isConnected_iff_connectedSpace.mp (isConnected_Ioi (a := (0:ℝ))))
  let i : ℝ≥0ˣ →ₜ* ℝˣ := ⟨Units.map NNReal.toRealHom.toMonoidHom,
    continuous_subtype_val.units_map _⟩
  have hf : (range (χ.comp i)).Finite := h.subset (by rintro _ ⟨x,rfl⟩; exact ⟨i x,rfl⟩)
  have pos (u : ℝˣ) (hu : 0 < u.val) : χ u = 1 := by
    let a : ℝ≥0 := ⟨u.val,hu.le⟩
    let w := Units.mk0 a (by intro ha; exact hu.ne' (congrArg NNReal.toReal ha))
    have eq : i w = u := Units.ext rfl
    exact eq ▸ meyer_finite_character_connected (χ.comp i) hf w
  refine ⟨pos,?_,?_⟩
  · intro u hu
    have hp := pos (-u) (neg_pos.mpr hu)
    have he : u = (-1 : ℝˣ) * (-u) := by simp
    rw [he,map_mul,hp,mul_one]
  · rw [← map_pow,neg_one_sq,map_one]

end RiemannMasullo

namespace RiemannMasullo
open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing FourierTransform
set_option quotPrecheck false
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "module∞(" w ")" => ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
  (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "chart(" w "," η "," z ")" => quasiCharacterNormTwist module∞(w) (continuous_infiniteLocalModule w) cc(η) z
noncomputable local instance {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private theorem meyer_real_finite_pair {F : Type*} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsReal) (χ : PontryaginDual w.Completionˣ) (hfin : (range χ).Finite) :
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let localZ := fun (p : w.Completion → ℂ) (θ : PontryaginDual w.Completionˣ) (z : ℂ) ↦
      localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w) p (chart(w,θ,z))
    ∃ a : Fin 2, (-1:ℂ)^a.val = (χ (-1) : ℂ) ∧ ∀ (f : SchwartzMap ℝ ℂ) (z : ℂ), 0 < z.re →
      localZ (fun t ↦ f (e t)) χ z = mellin (fun t : ℝ ↦ f t + (-1:ℂ)^a.val * f (-t)) z ∧
      localZ (fun t ↦ (𝓕 f) (e t)) χ⁻¹ z = mellin (fun t : ℝ ↦ (𝓕 f) t + (-1:ℂ)^a.val * (𝓕 f) (-t)) z := by
  intro e localZ
  let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.symm.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  let ξ := χ.comp i
  obtain ⟨hp,hn,hs⟩ := meyer_finite_real_sign ξ
    (hfin.subset (by rintro _ ⟨u,rfl⟩; exact ⟨i u,rfl⟩))
  have sig : ∃ a : Fin 2, (ξ (-1) : ℂ) = (-1:ℂ)^a.val := by
    have he : (ξ (-1) : ℂ)^2 = 1 := by
      have h := congrArg (fun x : Circle ↦ (x:ℂ)) hs
      simp only [Circle.coe_pow,Circle.coe_one] at h
      exact h
    rcases sq_eq_one_iff.mp he with H | H
    · exact ⟨0,by simpa using H⟩
    · exact ⟨1,by simpa using H⟩
  obtain ⟨a,ha⟩ := sig
  have hc (x : ℝˣ) : (χ (i x) : ℂ) =
      (‖(x:ℝ)‖:ℂ)^(0:ℂ)*(if 0 < x.val then (1:ℂ) else -1)^a.val := by
    rw [Complex.cpow_zero,one_mul]
    change (ξ x : ℂ) = _
    by_cases h : 0 < x.val
    · rw [if_pos h,one_pow]
      exact congrArg (fun y : Circle ↦ (y:ℂ)) (hp x h)
    · rw [if_neg h,← ha]
      exact congrArg (fun y : Circle ↦ (y:ℂ)) (hn x (lt_of_le_of_ne (le_of_not_gt h) x.ne_zero))
  have hd (x : ℝˣ) : ((χ⁻¹) (i x) : ℂ) =
      (‖(x:ℝ)‖:ℂ)^(0:ℂ)*(if 0 < x.val then (1:ℂ) else -1)^a.val := by
    change ((χ (i x) : ℂ)⁻¹) = _
    rw [hc,Complex.cpow_zero,one_mul]
    by_cases h : 0 < x.val <;> simp [h,←inv_pow]
  have him : i (-1) = -1 := Units.ext (by change e.symm (-1) = _; simp)
  have hi : ξ (-1) = χ (-1) := congrArg χ him
  refine ⟨a,ha.symm.trans (congrArg (fun t : Circle ↦ (t:ℂ)) hi),fun f z hz ↦ ⟨?_,?_⟩⟩
  · exact realIntegral_shape w hw f _ z a
      (by simpa only [add_zero] using realChart_shape w hw χ 0 a hc z) hz
  · exact realIntegral_shape w hw (𝓕 f) _ z a
      (by simpa only [add_zero] using realChart_shape w hw χ⁻¹ 0 a hd z) hz

end RiemannMasullo

open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing FourierTransform
namespace RiemannMasullo
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K(" v ")" => HeightOneSpectrum.adicCompletion ℚ v
local notation "realModel" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
private theorem meyer_rational_tensor_fourier (S : Finset V) (c : QuasiCharacter (SIdeleQuotient ℚ S))
    (φ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : InfiniteAdeleRing ℚ, φ (Multiplicative.ofAdd x) = f (realModel (x Rat.infinitePlace))) :
    let G := fun (v : S) (x : K(v.val)) ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c) (Multiplicative.ofAdd x)
    let FT := fun (v : S) ↦ @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ v.val)
      (finiteLocalStandardCharacter ℚ v.val)
    ∀ y : SAdeleRing ℚ S, sAdeleSchwartzFourier (sLocalStandardThetaTensor c φ) (Multiplicative.ofAdd y) =
      (𝓕 f) (realModel (y.1 Rat.infinitePlace)) * ∏ v : S, FT v (G v) (y.2 v) := by
  intro G FT y
  let : MeasurableSpace (SAdeleRing ℚ S) := instMeasurableSpaceSAdeleRing ℚ S
  obtain ⟨E,hE⟩ := sLocalMellinSchwartzBounds_meyer_rational_test_coordinates
  let H := E f
  have hH (x : SAdeleRing ℚ ∅) : H (Multiplicative.ofAdd x) = f (realModel (x.1 Rat.infinitePlace)) := hE f x
  have same : (fun z : SAdeleRing ℚ S ↦ sLocalStandardThetaTensor c φ (Multiplicative.ofAdd z)) =
      partialTensor ℚ S H G := by
    funext z
    rw [sLocalStandardThetaTensor_apply,hf]
    change _ = H (Multiplicative.ofAdd (z.1,0)) * _
    rw [hH]
  change tamagawaFourier _ _ _ y = _
  rw [same,partialTensor_fourier]
  exact congrArg (· * ∏ v : S, FT v (G v) (y.2 v))
    (sAdeleSchwartzFourier_ratEmpty_apply f H hH (y.1,0))

end RiemannMasullo

namespace RiemannMasullo
open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing FourierTransform
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K(" v ")" => HeightOneSpectrum.adicCompletion ℚ v
local notation "∞₀" => Rat.infinitePlace
local notation "realModel" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "chart(" S "," η "," z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
  (isProperMap_sIdeleQuotientNorm ℚ S).continuous cc(η) z
noncomputable local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
private theorem meyer_rational_standard_zeta (S : Finset V) (η : PontryaginDual (SIdeleQuotient ℚ S))
    (hfin : (range η).Finite) (c : QuasiCharacter (SIdeleQuotient ℚ S)) :
    let G := fun (v : S) (x : K(v.val)) ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c) (Multiplicative.ofAdd x)
    let FT := fun (v : S) ↦ @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ v.val)
      (finiteLocalStandardCharacter ℚ v.val)
    let Z := fun (p : (v : S) → K(v.val) → ℂ) (χ : PontryaginDual (SIdeleQuotient ℚ S)) (z : ℂ) ↦
      ∏ v : S, @localIdelicZetaIntegral _ _ _ (borel _) (finiteLocalMultiplicativeTamagawaMeasure ℚ v.val) (p v)
        (sLocalFiniteRestriction v (chart(S,χ,z)))
    ∃ a : Fin 2, (-1:ℂ)^a.val = sLocalInfiniteRestriction ∞₀ cc(η) (-1) ∧ ∀ (φ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))) (f : SchwartzMap ℝ ℂ),
      (∀ x : InfiniteAdeleRing ℚ, φ (Multiplicative.ofAdd x) = f (realModel (x ∞₀))) →
      ∀ z : ℂ, 0 < z.re →
        sLocalIdelicZetaIntegral (sLocalStandardThetaTensor c φ) (chart(S,η,z)) =
          mellin (fun t : ℝ ↦ f t + (-1:ℂ)^a.val*f (-t)) z * Z G η z ∧
        sLocalIdelicZetaIntegral (sAdeleSchwartzFourier (sLocalStandardThetaTensor c φ)) (chart(S,η⁻¹,z)) =
          mellin (fun t : ℝ ↦ (𝓕 f) t + (-1:ℂ)^a.val*(𝓕 f) (-t)) z * Z (fun v ↦ FT v (G v)) η⁻¹ z := by
  intro G FT Z
  classical
  let ep := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing ℚ) ((v : S) → K(v.val))
  let ea := ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := ℚ))
  let i (x : ∞₀.Completionˣ) := (QuotientGroup.mk : (SAdeleRing ℚ S)ˣ → SIdeleQuotient ℚ S)
    (ep.symm (ea.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) ∞₀ x),1))
  let j : ∞₀.Completionˣ →ₜ* SIdeleQuotient ℚ S :=
    ⟨{ toFun := i, map_one' := (sLocalInfiniteInsertion_properties (S := S) ∞₀).1,
       map_mul' := (sLocalInfiniteInsertion_properties (S := S) ∞₀).2.1 },(sLocalInfiniteInsertion_properties (S := S) ∞₀).2.2⟩
  let χ := η.comp j
  have hχ : (range χ).Finite := hfin.subset (by rintro _ ⟨g,rfl⟩; exact ⟨j g,rfl⟩)
  obtain ⟨a,hA,H⟩ := meyer_real_finite_pair ∞₀ Rat.isReal_infinitePlace χ hχ
  let archNorm := ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult ∞₀ : ∞₀.Completionˣ →* ℝ≥0ˣ)
  let localChart (ψ : PontryaginDual ∞₀.Completionˣ) (z : ℂ) := quasiCharacterNormTwist archNorm
    (continuous_infiniteLocalModule ∞₀) cc(ψ) z
  have rest (ψ : PontryaginDual (SIdeleQuotient ℚ S)) (z : ℂ) :
      sLocalInfiniteRestriction ∞₀ (chart(S,ψ,z)) = localChart (ψ.comp j) z := by
    ext u
    let m := sIdeleQuotientNorm ℚ S
    change (ψ (j u) : ℂ) * (((m (j u) : ℝ≥0) : ℝ) : ℂ)^z = (ψ (j u) : ℂ) * (((archNorm u : ℝ≥0) : ℝ) : ℂ)^z
    apply congrArg ((ψ (j u) : ℂ) * ·)
    have ht := sLocalInfiniteRestriction_normTwist (S := S) ∞₀ z u
    change (1:ℂ)*(((m (j u) : ℝ≥0) : ℝ) : ℂ)^z = _ at ht
    rwa [one_mul] at ht
  have eval (f : SchwartzMap ℝ ℂ) (ψ : PontryaginDual (SIdeleQuotient ℚ S)) (z : ℂ) (hz : 0 < z.re)
      (u : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) (p : (v : S) → K(v.val) → ℂ)
      (hu : ∀ x : SAdeleRing ℚ S, u (Multiplicative.ofAdd x) = f (realModel (x.1 ∞₀)) * ∏ v : S, p v (x.2 v)) :
      sLocalIdelicZetaIntegral u (chart(S,ψ,z)) =
        localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure ℚ ∞₀)
          (fun t ↦ f (realModel t)) (localChart (ψ.comp j) z) * Z p ψ z := by
    let pA (w : InfinitePlace ℚ) : w.Completion → ℂ := by
      obtain rfl := Subsingleton.elim w ∞₀
      exact fun t ↦ f (realModel t)
    have HA (x : SAdeleRing ℚ S) : f (realModel (x.1 ∞₀)) = ∏ w : InfinitePlace ℚ, pA w (x.1 w) := by
      rw [Fintype.prod_unique]
      rfl
    rw [sLocal_zeta_prod (chart(S,ψ,z)) ⟨ψ,z,hz,rfl⟩ u pA p (fun x ↦ (hu x).trans (congrArg (· * _) (HA x))),
      Fintype.prod_unique]
    change localIdelicZetaIntegral _ _ (sLocalInfiniteRestriction ∞₀ _) * _ = _
    rw [rest]
    rfl
  refine ⟨a,hA,fun φ f hφ z hz ↦ ⟨?_,?_⟩⟩
  · rw [eval f η z hz (sLocalStandardThetaTensor c φ) G (fun x ↦ by rw [sLocalStandardThetaTensor_apply,hφ])]
    exact congrArg (· * _) (H f z hz).1
  · exact (eval (𝓕 f) η⁻¹ z hz _ (fun v ↦ FT v (G v)) (meyer_rational_tensor_fourier S c φ f hφ)).trans
      (congrArg (· * _) (H f z hz).2)

end RiemannMasullo
end

section
open Function Set IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing
namespace RiemannMasullo
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "N(" S ")" => (sIdeleQuotientNorm ℚ S).ker
local notation "J(" S ")" => SIdeleQuotient ℚ S
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "Q(" S ")" => (sLocalAdelicTheta ℚ S).ker.mkQ
local notation "A(" S ")" => (existsUnique_sLocalThetaAction (F := ℚ) (S := S)).exists.choose
local notation "P(" S "," ω ")" => (existsUnique_sLocalThetaIsotypicAverage (F := ℚ) (S := S) ω).exists.choose

private theorem meyer_rat_stage_pic (S : Finset V) :
    Subsingleton (CommRing.Pic ((S : Set V).integer ℚ)) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have : Subsingleton (CommRing.Pic (((∅ : Finset V) : Set V).integer ℚ)) := by
    rw [Finset.coe_empty,integer_empty]
    let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
    let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    infer_instance
  obtain ⟨_,_,_,hsurj,_⟩ := picard_localization_exact ℚ ∅ S (Finset.empty_subset S)
  exact hsurj.subsingleton

private theorem meyer_rat_angular_extension (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (hτ : RightInverse τ (sIdeleQuotientNorm ℚ S)) (ω : PontryaginDual N(S)) (hfin : (range ω).Finite) :
    ∃ (η : PontryaginDual J(S)) (w : PontryaginDual (ideleClassNorm ℚ).ker)
      (hw : NormOneCharacterUnramifiedOutside w S),
      (∀ g : N(S), η g.val = ω g) ∧ (∀ t, η (τ t) = 1) ∧ (range η).Finite ∧ sLocalNormOneCharacter S w hw = ω := by
  let m := sIdeleQuotientNorm ℚ S
  have hker (g : J(S)) : g / τ (m g) ∈ (sIdeleQuotientNorm ℚ S).ker := by
    change m (g / τ (m g)) = 1
    rw [map_div,hτ,div_self']
  let b : J(S) →ₜ* N(S) :=
    { toFun := fun g ↦ ⟨g / τ (m g),hker g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by
        change a*b / τ (m (a*b)) = (a/τ (m a)) * (b/τ (m b))
        rw [map_mul,map_mul,div_mul_div_comm])
      continuous_toFun := (show Continuous (fun g : J(S) ↦ g / τ (m g)) by
        change Continuous ((fun g : J(S) ↦ g) / (fun g : J(S) ↦ τ (m g)))
        apply Continuous.div' continuous_id
        exact τ.continuous.comp (isProperMap_sIdeleQuotientNorm ℚ S).continuous).subtype_mk hker }
  have hb (u : N(S)) : b u.val = u := by apply Subtype.ext; change u.val / τ (m u.val) = u.val; rw [u.property,map_one,div_one]
  let η := ω.comp b
  have heta (g : N(S)) : η g.val = ω g := congrArg ω (hb g)
  let toC : Circle →ₜ* ℂ := ⟨Circle.coeHom,continuous_subtype_val⟩
  obtain ⟨W,hW⟩ := sIdeleRestriction_surjective ℚ S (toC.comp η)
  let C := IdeleClassGroup (𝓞 ℚ) ℚ
  let : T2Space C := (ideleGroup_quotient.{_,0} ℚ).2.2.2.2.2.1
  let : LocallyCompactSpace C := (ideleGroup_quotient.{_,0} ℚ).2.2.2.2.2.2.1
  have hn (x : (ideleClassNorm ℚ).ker) : ‖W.val x.val‖ = 1 := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm ℚ) (isProperMap_ideleClassNorm ℚ)
      (ideleClassNorm_ne_one (F := ℚ))]
    simp [MonoidHom.mem_ker.mp x.property]
  let w : PontryaginDual (ideleClassNorm ℚ).ker :=
    { toFun := fun x ↦ ⟨W.val x.val,mem_sphere_zero_iff_norm.mpr (hn x)⟩
      map_one' := Circle.ext (map_one W.val)
      map_mul' := fun x y ↦ Circle.ext (map_mul W.val x.val y.val)
      continuous_toFun := (W.val.continuous.comp continuous_subtype_val).subtype_mk (fun x ↦ mem_sphere_zero_iff_norm.mpr (hn x)) }
  let hw : NormOneCharacterUnramifiedOutside w S := ⟨W,fun _ ↦ rfl⟩
  have hwω : sLocalNormOneCharacter S w hw = ω := by
    apply ContinuousMonoidHom.ext
    intro g
    apply Circle.ext
    calc
      _ = sIdeleRestriction ℚ S W g.val := sLocalNormOneCharacter_eq_sIdeleRestriction w W (fun _ ↦ rfl) g
      _ = toC (η g.val) := DFunLike.congr_fun hW g.val
      _ = _ := congrArg toC (heta g)
  have hbase (t : ℝ≥0ˣ) : b (τ t) = 1 := by
    apply Subtype.ext
    change τ t / τ (m (τ t)) = 1
    rw [hτ,div_self']
  refine ⟨η,w,hw,heta,fun t ↦ (congrArg ω (hbase t)).trans (map_one ω),?_,hwω⟩
  apply hfin.subset
  rintro _ ⟨g,rfl⟩
  exact ⟨b g,rfl⟩

set_option maxHeartbeats 800000 in
/-- Every actual rational norm-one isotype at any finite stage is represented
by an average of an archimedean test tensor one fixed finite standard profile.
The global lifting and Picard hypotheses of Theorem 6.2.2.1 are discharged. -/
private theorem meyer_rat_isotype_standard (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (hτ : RightInverse τ (sIdeleQuotientNorm ℚ S)) (ω : PontryaginDual N(S)) (hfin : (range ω).Finite) :
    ∃ (η : PontryaginDual J(S)) (c : QuasiCharacter J(S)),
      (∀ g : N(S), η g.val = ω g) ∧ (∀ t, η (τ t) = 1) ∧ (range η).Finite ∧
      (∀ g : N(S), c g.val = (ω g : ℂ)) ∧
      ∀ x : SLocalAdelicThetaSpace ℚ S, (∀ g : N(S), A(S) g.val x = (ω g : ℂ) • x) →
        ∃ φ : B∞, P(S,ω) (Q(S) (sLocalStandardThetaTensor c φ)) = x := by
  obtain ⟨η,w,hw,heta,hbase,hfinη,hwω⟩ := meyer_rat_angular_extension S τ hτ ω hfin
  let c := sIdeleRestriction ℚ S hw.choose
  have hcy (g : N(S)) : c g.val = (ω g : ℂ) := by
    rw [← hwω]
    exact (sLocalNormOneCharacter_eq_sIdeleRestriction w hw.choose hw.choose_spec g).symm
  let χ := η.comp ⟨QuotientGroup.mk' _,QuotientGroup.continuous_mk⟩
  have hχ (g : (sIdeleNorm ℚ S).ker) (y : N(S)) (hy : y.val = QuotientGroup.mk g.val) :
      χ g.val = sLocalNormOneCharacter S w hw y := by
    rw [hwω,← heta y,hy]
    rfl
  obtain ⟨E,hE⟩ := sLocalStandardThetaTensor_quotient_equiv (meyer_rat_stage_pic S) hw χ hχ
  obtain ⟨J,hJ⟩ := (sLocalThetaIsotypicAverage_equiv (F := ℚ) (S := S) (sLocalNormOneCharacter S w hw)).2
  refine ⟨η,c,heta,hbase,hfinη,hcy,fun x hx ↦ ?_⟩
  have hx' : x ∈ actionIsotype ((A(S)).comp (N(S)).subtype) (sLocalNormOneCharacter S w hw) := by
    rw [hwω,mem_actionIsotype]
    exact hx
  obtain ⟨y,hy⟩ := J.surjective ⟨x,hx'⟩
  obtain ⟨p,hp⟩ := E.surjective y
  obtain ⟨φ,rfl⟩ := (infiniteStandardThetaMellinAverage χ).ker.mkQ_surjective p
  refine ⟨φ,?_⟩
  have ha := hJ (sLocalStandardThetaTensor c φ)
  have hb := hE φ
  have hh := congrArg (fun z ↦ (J z).val) ((hp.symm.trans hb).symm)
  have hr := ((ha.symm.trans hh).trans (congrArg Subtype.val hy))
  rw [← hwω]
  exact hr

end RiemannMasullo
end

section
open Function MeasureTheory Set IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing
namespace RiemannMasullo
/-- Fourier interchange with the unnormalized compact isotypic average has no
extra scalar. Inversion preserves the Haar measure and inverts the character. -/
private theorem meyer_fourier_character_average {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [MeasurableInv G] [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [SeparatingDual ℂ E] (μ : Measure G) [μ.IsInvInvariant] (A : G →* (E →L[ℂ] E))
    (ω : PontryaginDual G) (P Q L : E →L[ℂ] E)
    (hP : IsPettisIsotypicAverageOn μ univ A ω P)
    (hQ : IsPettisIsotypicAverageOn μ univ A ω⁻¹ Q) (x : E)
    (hint : ∀ g, L (A g x) = A g⁻¹ (L x)) :
    L (P x) = Q (L x) := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro φ
  have hp := LinearMap.congr_fun (hP x).2 (φ.comp L)
  have hq := LinearMap.congr_fun (hQ (L x)).2 φ
  change φ (L (P x)) = ∫ g, φ (L (star (ω g : ℂ) • A g x)) ∂(μ.restrict univ) at hp
  change φ (Q (L x)) = ∫ g, φ (star ((ω⁻¹) g : ℂ) • A g (L x)) ∂(μ.restrict univ) at hq
  rw [Measure.restrict_univ] at hp hq
  rw [hp,hq,← integral_inv_eq_self (fun g : G ↦ φ (star ((ω⁻¹) g : ℂ) • A g (L x))) μ]
  apply integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  rw [map_smul,hint]
  have hc : ((ω⁻¹) g⁻¹ : Circle) = ω g := by change (ω g⁻¹)⁻¹ = _; rw [map_inv,inv_inv]
  rw [hc]

private theorem meyer_actual_fourier_average {F : Type*} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hF : Module.finrank ℚ F = 1)
    (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S) (hτ : RightInverse τ (sIdeleQuotientNorm F S))
    (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) (x : SLocalAdelicThetaSpace F S) :
    let FT := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
    let P := fun χ' ↦ (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ').exists.choose
    FT (P χ x) = P χ⁻¹ (FT x) := by
  intro FT P
  let E := SLocalAdelicThetaSpace F S
  let G := (sIdeleQuotientNorm F S).ker
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  let : T2Space (SIdeleQuotient F S) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm F S).ker : Set (SIdeleQuotient F S)))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := F) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := F) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := F) (S := S)
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : μ.Regular := (sLocalNormOneQuotientMeasure_existsUnique (F := F) (S := S)).exists.choose_spec.2.1
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let A := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
  have hs := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose_spec
  have ht := (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ⁻¹).exists.choose_spec
  obtain ⟨f,rfl⟩ := (sLocalAdelicTheta F S).ker.mkQ_surjective x
  let v := fun _ : ℕ ↦ f
  have hb : Bornology.IsVonNBounded ℂ (range fun n ↦ (sLocalAdelicTheta F S).ker.mkQ (v n)) := by
    simpa [v] using Bornology.isVonNBounded_singleton (𝕜 := ℂ) ((sLocalAdelicTheta F S).ker.mkQ f)
  have hq := meyer_degree_one_fourier_intertwines S hF τ hτ v
    (sLocalMellinSchwartzBounds_meyer_general_forward S τ hτ v hb)
  exact meyer_fourier_character_average μ (A.comp G.subtype) χ (P χ) (P χ⁻¹) FT.toContinuousLinearMap
      hs ht _ (fun g ↦ hq g 0)

end RiemannMasullo
end

section
namespace RiemannMasullo
open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "J(" S ")" => SIdeleQuotient F S
local notation "N(" S ")" => (sIdeleQuotientNorm F S).ker
local notation "B(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Q(" S ")" => (sLocalAdelicTheta F S).ker.mkQ
local notation "P(" S "," χ ")" => (existsUnique_sLocalThetaIsotypicAverage (F := F) (S := S) χ).exists.choose
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "chart(" S "," η "," z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous cc(η) z

private theorem meyer_projected_heights (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (η : PontryaginDual J(S)) (hb : ∀ t, η (τ t) = 1) (χ : PontryaginDual N(S))
    (hχ : ∀ g : N(S), η g.val = χ g) (v f : ℕ → B(S))
    (he : ∀ n, Q(S) (v n) = P(S,χ) (Q(S) (f n)))
    (hM : sLocalMellinSchwartzBounds S τ v sLocalThetaMellinIntegral) :
    ∀ a : ℝ, 1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (z : ℂ), z.re = a →
      ‖z^m * sLocalIdelicZetaIntegral (f n) (chart(S,η,z))‖ ≤ B := by
  let angle : (PontryaginDual.map τ).ker := ⟨η,ContinuousMonoidHom.ext (fun t ↦ hb t)⟩
  let : MeasurableSpace N(S) := borel _
  let : BorelSpace N(S) := ⟨rfl⟩
  let : CompactSpace N(S) := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hpos : 0 < μ.real univ := ENNReal.toReal_pos (isOpen_univ.measure_pos μ univ_nonempty).ne' isCompact_univ.measure_lt_top.ne
  have coefficient (n : ℕ) (z : ℂ) (hz : 0 < z.re) :
      sLocalThetaMellinIntegral (v n) (chart(S,η,z)) = (μ.real univ : ℂ) * sLocalIdelicZetaIntegral (f n) (chart(S,η,z)) := by
    let c := chart(S,η,z)
    let r := (⟨c,sLocalOrderBound_positive η hz⟩ : {c : QuasiCharacter J(S) // 0 ≤ sLocalIdelicOrderBound c})
    have eq := congrArg (fun x : SLocalAdelicThetaSpace F S ↦ (sLocalThetaMellin x).val r) (he n)
    have hs := sLocalThetaMellin_isotypicAverage χ (Q(S) (f n)) r (fun g ↦ by
      change (η g.val : ℂ) * (((sIdeleQuotientNorm F S g.val : ℝ≥0) : ℝ) : ℂ)^z = _
      rw [MonoidHom.mem_ker.mp g.property]
      simp only [Units.val_one,NNReal.coe_one,Complex.ofReal_one,Complex.one_cpow,mul_one]
      exact congrArg (fun y : Circle ↦ (y:ℂ)) (hχ g))
    have h := eq.trans hs
    change sLocalIdelicZFunction (v n) c = (μ.real univ : ℂ) * sLocalIdelicZFunction (f n) c at h
    rw [sLocalThetaMellinIntegral_eq_zeta _ ⟨η,z,hz,rfl⟩,← sLocalIdelicZFunction_eq_integral _ ⟨η,z,hz,rfl⟩,
        ← sLocalIdelicZFunction_eq_integral _ ⟨η,z,hz,rfl⟩]
    exact h
  intro a ha m
  obtain ⟨H,_,hs,hw⟩ := (sLocalMellinSchwartzBounds_meyer_zeroth_iff S τ v).mp hM a ha
  obtain ⟨D,hD⟩ := hw 0 0 m
  refine ⟨max D 0 / μ.real univ,fun n z hz ↦ ?_⟩
  rw [le_div_iff₀ hpos]
  have h : ‖z^m*sLocalThetaMellinIntegral (v n) (chart(S,η,z))‖ ≤ max D 0 := by
    by_cases hA : angle ∈ H
    · exact (show ‖z^m*sLocalThetaMellinIntegral (v n) (chart(S,η,z))‖ ≤ D by
        simpa using hD ⟨angle,hA⟩ n z hz).trans (le_max_left _ _)
    · have hz' := hs angle hA n z hz
      change sLocalThetaMellinIntegral (v n) (chart(S,η,z)) = 0 at hz'
      rw [hz',mul_zero,norm_zero]
      exact le_max_right _ _
  rw [coefficient n z (hz.symm ▸ zero_lt_one.trans ha),mul_left_comm, norm_mul,Complex.norm_real,
    Real.norm_of_nonneg hpos.le,mul_comm] at h
  exact h

end RiemannMasullo
end

section
open Function IsDedekindDomain NumberField
open scoped NumberField.AdeleRing
namespace RiemannMasullo
set_option quotPrecheck false
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
private theorem meyer_arch_coordinates :
    ∃ E : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(InfiniteAdeleRing ℚ),
      ∀ (f : SchwartzMap ℝ ℂ) (x : InfiniteAdeleRing ℚ),
        E f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace (x Rat.infinitePlace)) := by
  let real : Rat.infinitePlace.Completion ≃ᵢ ℝ :=
    InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let coord : InfiniteAdeleRing ℚ ≃ₜ ℝ := (Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans real.toHomeomorph
  let e : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' coord fun x y ↦
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).map_add
        (x.toAdd Rat.infinitePlace) (y.toAdd Rat.infinitePlace)
  with_reducible refine realSchwartzBruhat_equiv.elim fun R hR ↦ ?_
  let : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  let : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  let : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨A,hA⟩ := exists_schwartzBruhat_comp_equivCLM e
  obtain ⟨B,hB⟩ := exists_schwartzBruhat_comp_equivCLM e.symm
  have hAB : Function.LeftInverse B A := by
    intro f
    apply Subtype.ext
    funext x
    rw [hB,hA,e.apply_symm_apply]
  have hBA : Function.RightInverse B A := by
    intro f
    apply Subtype.ext
    funext x
    rw [hA,hB,e.symm_apply_apply]
  refine ⟨R.trans (ContinuousLinearEquiv.equivOfInverse A B hAB hBA),fun f x ↦ ?_⟩
  exact (hA (R f) (Multiplicative.ofAdd x)).trans (hR f (coord x))

end RiemannMasullo
end

section
open Function Set IsDedekindDomain NumberField MeasureTheory
open scoped NNReal NumberField.AdeleRing FourierTransform
namespace RiemannMasullo
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "∞₀" => Rat.infinitePlace
local notation "realModel" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "N(" S ")" => (sIdeleQuotientNorm ℚ S).ker
local notation "Q(" S ")" => (sLocalAdelicTheta ℚ S).ker.mkQ
local notation "P(" S "," χ ")" => (existsUnique_sLocalThetaIsotypicAverage (F := ℚ) (S := S) χ).exists.choose
local notation "SB" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
set_option maxHeartbeats 800000 in
private theorem meyer_rational_reflect (S : Finset V) (η : PontryaginDual (SIdeleQuotient ℚ S))
    (χ : PontryaginDual N(S)) (hχ : ∀ t : N(S), η t.val = χ t)
    (c : QuasiCharacter (SIdeleQuotient ℚ S)) (R : SB → SB)
    (hR : ∀ (f : SB) x, R f (Multiplicative.ofAdd x) = f (Multiplicative.ofAdd (-x))) (φ : SB) :
    P(S,χ) (Q(S) (sLocalStandardThetaTensor c (R φ))) =
      sLocalInfiniteRestriction ∞₀ cc(η) (-1) • P(S,χ) (Q(S) (sLocalStandardThetaTensor c φ)) := by
  classical
  let E := SLocalAdelicThetaSpace ℚ S
  let G := N(S)
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := S)
  let : T2Space (SIdeleQuotient ℚ S) := inferInstanceAs (T2Space (_ ⧸ _))
  let : T2Space G := inferInstanceAs (T2Space ((sIdeleQuotientNorm ℚ S).ker : Set (SIdeleQuotient ℚ S)))
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let : T2Space E := sLocalAdelicThetaSpace_t2_of_isClosed (F := ℚ) (S := S)
    (sLocalAdelicTheta_ker_isClosed (F := ℚ) (S := S))
  let : PolynormableSpace ℂ E := sLocalAdelicThetaSpace_polynormable (F := ℚ) (S := S)
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  let μ := sLocalNormOneQuotientMeasure ℚ S
  let : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := S)).1
  let ep := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing ℚ) ((v : S) → v.val.adicCompletion ℚ)
  let ea := ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := ℚ))
  let u : (SAdeleRing ℚ S)ˣ := ep.symm (-1,1)
  let q : (SAdeleRing ℚ S)ˣ →* SIdeleQuotient ℚ S := QuotientGroup.mk' _
  have hsq : u^2 = 1 := by
    apply ep.injective
    rw [map_pow,map_one,show ep u = (-1,1) from ep.apply_symm_apply _]
    apply Prod.ext
    · change (-1 : (InfiniteAdeleRing ℚ)ˣ)^2 = 1
      exact neg_one_sq
    · change (1 : ((v : S) → v.val.adicCompletion ℚ)ˣ)^2 = 1
      simp
  have hn : q u ∈ N(S) := (pow_eq_one_iff_left (by decide : 2 ≠ 0)).mp (by
    change (sIdeleQuotientNorm ℚ S (q u))^2 = 1
    rw [← map_pow,←map_pow,hsq,map_one,map_one])
  let t : N(S) := ⟨q u,hn⟩
  have harch : ea.symm (@Pi.mulSingle (InfinitePlace ℚ) (fun w ↦ w.Completionˣ) _ (Classical.decEq _) ∞₀ (-1 : ∞₀.Completionˣ)) = -1 := by
    apply Units.ext
    funext w
    obtain rfl := Subsingleton.elim w ∞₀
    change ((@Pi.mulSingle (InfinitePlace ℚ) (fun w ↦ w.Completionˣ) _ (Classical.decEq _) ∞₀ (-1 : ∞₀.Completionˣ)) ∞₀).val = _
    exact congrArg (fun t : ∞₀.Completionˣ ↦ t.val)
      (@Pi.mulSingle_eq_same (InfinitePlace ℚ) (fun w ↦ w.Completionˣ) _ (Classical.decEq _) ∞₀ (-1))
  have hsign : sLocalInfiniteRestriction ∞₀ cc(η) (-1) = (χ t : ℂ) := by
    change (η (q (ep.symm (ea.symm _,1))) : ℂ) = _
    rw [harch]
    exact congrArg (fun y : Circle ↦ (y:ℂ)) (hχ t)
  let A := (existsUnique_sLocalThetaAction (F := ℚ) (S := S)).exists.choose
  have htrans : schwartzBruhatUnitTranslate u (sLocalStandardThetaTensor c φ) = sLocalStandardThetaTensor c (R φ) := by
    apply Subtype.ext
    funext x
    rw [show schwartzBruhatUnitTranslate u (sLocalStandardThetaTensor c φ) x =
      sLocalStandardThetaTensor c φ (Multiplicative.ofAdd (u⁻¹.val*x.toAdd)) from rfl]
    rw [sLocalStandardThetaTensor_apply]
    change _ = sLocalStandardThetaTensor c (R φ) (Multiplicative.ofAdd x.toAdd)
    rw [sLocalStandardThetaTensor_apply,hR]
    have hi : u⁻¹ = u := calc
      u⁻¹ = u⁻¹ * (u*u) := by rw [← pow_two,hsq,mul_one]
      _ = u := inv_mul_cancel_left _ _
    rw [hi]
    change φ (Multiplicative.ofAdd ((-1:InfiniteAdeleRing ℚ)*x.toAdd.1)) * _ = _
    rw [neg_one_mul]
    apply congrArg (_ * ·)
    apply Finset.prod_congr rfl
    intro v _
    change finiteStandardGaussian _ _ (Multiplicative.ofAdd ((1 : v.val.adicCompletion ℚ)*x.toAdd.2 v)) = _
    rw [one_mul]
  have hact := (existsUnique_sLocalThetaAction (F := ℚ) (S := S)).exists.choose_spec.2 u
    (sLocalStandardThetaTensor c φ)
  rw [htrans] at hact
  have he := compactActionAverage_apply_action μ (A.comp (N(S)).subtype) χ (P(S,χ))
    (existsUnique_sLocalThetaIsotypicAverage (F := ℚ) (S := S) χ).exists.choose_spec t (Q(S) (sLocalStandardThetaTensor c φ))
  exact (congrArg (P(S,χ)) hact.symm).trans (he.trans
    (congrArg (fun k : ℂ ↦ k • P(S,χ) (Q(S) (sLocalStandardThetaTensor c φ))) hsign.symm))

end RiemannMasullo
end

section
open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal NumberField.AdeleRing TensorProduct
namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
set_option quotPrecheck false
local notation "ℬ∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing F))
local notation "ℬₛ(" T ")" => SchwartzBruhat (Multiplicative (SAdeleRing F T))
private theorem meyer_standard_tensor_continuous (c : QuasiCharacter (SIdeleQuotient F S)) :
    Continuous (sLocalStandardThetaTensor c) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (Multiplicative (InfiniteAdeleRing F)) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : SecondCountableTopology (Multiplicative (SAdeleRing F S)) := inferInstanceAs
    (SecondCountableTopology (((w : InfinitePlace F) → w.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  let : T2Space (Multiplicative (SAdeleRing F S)) := inferInstanceAs
    (T2Space (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace ((w : InfinitePlace F) → w.Completion))
  let : LocallyCompactSpace (Multiplicative (SAdeleRing F S)) := inferInstanceAs
    (LocallyCompactSpace (((w : InfinitePlace F) → w.Completion) ×
      ((v : S) → v.val.adicCompletion F)))
  let : T2Space ℬ∞ := schwartzBruhat_t2
  let : T2Space ℬₛ(S) := schwartzBruhat_t2
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] v : S, SchwartzBruhat (Multiplicative (v.val.adicCompletion F)))
  let g : W := ⨂ₜ[ℂ] v : S, finiteStandardGaussian v.val (sLocalFiniteRestriction v c)
  let : PolynormableSpace ℂ W := (finestLocallyConvex_withSeminorms _).toPolynormableSpace
  let : T2Space W := finestLocallyConvex_t2 _
  have ht : Continuous fun f : ℬ∞ ↦ e (f ⊗ₜ[ℂ] g) :=
    ((continuous_inductiveTensor_iff (e : InductiveTensor ℬ∞ W →L[ℂ] ℬₛ(S)).toLinearMap).mp
      e.continuous).2 g
  exact ht

end RiemannMasullo
end

section
open Filter Function MeasureTheory Set Topology
open scoped SchwartzMap FourierTransform
namespace RiemannMasullo
/-- A real sign isotype has the same derivative magnitudes on both half-lines.
The formulation with a unimodular scalar also applies after changing an isotype
coordinate by an arbitrary unitary normalization. -/
private theorem meyer_unitary_parity (g : SchwartzMap ℝ ℂ) (e : ℂ) (he : ‖e‖ = 1)
    (h : ∀ x : ℝ, g (-x) = e * g x) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (g : ℝ → ℂ) (-x)‖ = ‖iteratedDeriv k (g : ℝ → ℂ) x‖ := by
  have heq : (fun t : ℝ ↦ g (-t)) = e • (g : ℝ → ℂ) := funext h
  have hz := congrArg norm (iteratedDeriv_comp_neg k (g : ℝ → ℂ) x)
  rw [heq,iteratedDeriv_const_smul ((g.smooth _).contDiffAt) e] at hz
  simpa [norm_smul,he] using hz.symm
/-- Reflection commutes with the real Fourier transform, so the Fourier profile
has exactly the same sign as the physical profile. -/
private theorem meyer_unitary_parity_fourier (g : SchwartzMap ℝ ℂ) (e : ℂ)
    (h : ∀ x : ℝ, g (-x) = e * g x) (x : ℝ) : 𝓕 g (-x) = e * 𝓕 g x := by
  let R := LinearIsometryEquiv.neg ℝ (E := ℝ)
  have hr : (g : ℝ → ℂ) ∘ R = fun t : ℝ ↦ e • g t := funext h
  have hh := Real.fourier_comp_linearIsometry R (g : ℝ → ℂ) x
  rw [hr] at hh
  apply hh.symm.trans
  change 𝓕 (e • g) x = _
  rw [FourierTransform.fourier_smul]
  rfl
private theorem meyer_inverse_signed_real_profiles
    (f : ℕ → SchwartzMap ℝ ℂ) (e : ℕ → ℂ) (he : ∀ n, ‖e n‖ = 1)
    (hf : ∀ n x, f n (-x) = e n * f n x)
    (hM : ∀ v ∈ ({f,fun n ↦ 𝓕 (f n)} : Set (ℕ → SchwartzMap ℝ ℂ)),
      ∀ a : ℝ, 1 < a → ∀ m : ℕ, ∃ B : ℝ, ∀ n (z : ℂ), z.re = a →
        ‖z^m*mellin (v n) z‖ ≤ B) :
    Bornology.IsVonNBounded ℂ (range f) := by
  have hbd (v : ℕ → SchwartzMap ℝ ℂ) (hv : v ∈ ({f,fun n ↦ 𝓕 (f n)} : Set _))
      (j : ℕ) (a : ℝ) (ha : (j:ℝ)+1 < a) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n (x : ℝ), 0 < x →
        x^a * ‖iteratedDeriv j (v n : ℝ → ℂ) x‖ ≤ B := by
    let D := SchwartzMap.derivCLM ℂ ℂ
    let w (n : ℕ) := D^[j] (v n)
    have hpoint (n i : ℕ) : ((D^[i] (v n) : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
        iteratedDeriv i (v n : ℝ → ℂ) := by
      induction i with
      | zero => rfl
      | succ i ih => rw [Function.iterate_succ_apply',iteratedDeriv_succ,← ih]; rfl
    obtain ⟨C,hC⟩ := sLocalMellinSchwartzBounds_meyer_real_mellin_bounds_all_derivatives v (hM v hv) j a ha 2
    have ha1 : 1 ≤ a := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hco (n) : Continuous (fun t : ℝ ↦ mellin (w n) ((a:ℂ)+(t:ℂ)*Complex.I)) := by
      apply continuous_iff_continuousAt.mpr
      intro x
      let z (t : ℝ) := (a:ℂ)+(t:ℂ)*Complex.I
      have hz : 0 < (z x).re := by simp [z]; linarith
      exact ContinuousAt.comp (f := z) (g := mellin (w n))
        (sLocalMellinSchwartzBounds_meyer_real_mellin_differentiableAt (w n) hz).continuousAt (by dsimp [z]; fun_prop)
    have H := sLocalMellinSchwartzBounds_meyer_real_inverse_ray a ha1 (fun n ↦ (w n : ℝ → ℂ)) (fun n ↦ (w n).continuous)
      (fun n ↦ sLocalMellinSchwartzBounds_meyer_real_mellin_convergent (w n) (by simp; linarith)) hco C
      (fun n t ↦ hC n _ (by simp))
    refine ⟨max (C/2) 0,le_max_right _ _,fun n x hx ↦ ?_⟩
    rw [← hpoint]
    exact (H n x hx).trans (le_max_left _ _)
  have hfF : (fun n ↦ 𝓕 (f n)) ∈ ({f,fun n ↦ 𝓕 (f n)} : Set _) := by simp
  have hpos := sLocalMellinSchwartzBounds_meyer_real_positive_moments (fun n ↦ 𝓕 (f n)) (by
    intro a ha; simpa only [Nat.cast_zero,zero_add,iteratedDeriv_zero] using hbd _ hfF 0 a (by simpa))
  apply sLocalMellinSchwartzBounds_meyer_real_bounds_suffice f
  · intro j hj
    obtain ⟨B,hB⟩ := hpos j hj
    refine ⟨(2*Real.pi)^j*(2*B),fun n x ↦ ?_⟩
    apply sLocalMellinSchwartzBounds_meyer_real_derivative_from_fourier_moment _ j _ _ x
    have hEven (y : ℝ) : ‖𝓕 (f n) |y|‖ = ‖𝓕 (f n) y‖ := by
      rcases le_total 0 y with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h,meyer_unitary_parity_fourier (f n) (e n) (hf n),norm_mul,he n,one_mul]
    have he := integral_comp_abs (f := fun y : ℝ ↦ y^j*‖𝓕 (f n) y‖)
    simp_rw [hEven] at he
    exact he.trans_le (by gcongr; exact hB n)
  · intro k j
    let a : ℝ := max (k:ℝ) ((j:ℝ)+1)+1
    have ha : (j:ℝ)+1 < a := (le_max_right _ _).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    obtain ⟨B,_,hB⟩ := hbd f (by simp) j a ha
    refine ⟨B,fun n x hx ↦ ?_⟩
    have hx0 : 0 < |x| := zero_lt_one.trans_le hx
    have hEven : ‖iteratedDeriv j (f n : ℝ → ℂ) |x|‖ = ‖iteratedDeriv j (f n : ℝ → ℂ) x‖ := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h]
        exact meyer_unitary_parity (f n) (e n) (he n) (hf n) j x
    have hp : |x|^k ≤ |x|^a := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hx
      exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
    rw [← hEven]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans (hB n _ hx0)

end RiemannMasullo
end
end

section
open Function Set MeasureTheory IsDedekindDomain NumberField
open scoped NNReal NumberField.AdeleRing FourierTransform
namespace RiemannMasullo
set_option quotPrecheck false
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "K(" v ")" => HeightOneSpectrum.adicCompletion ℚ v
local notation "∞₀" => Rat.infinitePlace
local notation "realModel" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "cc(" ρ ")" => ((⟨Circle.coeHom,continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ρ)
local notation "N(" S ")" => (sIdeleQuotientNorm ℚ S).ker
local notation "B(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))
local notation "Q(" S ")" => (sLocalAdelicTheta ℚ S).ker.mkQ
local notation "P(" S "," χ ")" => (existsUnique_sLocalThetaIsotypicAverage (F := ℚ) (S := S) χ).exists.choose
local notation "A(" S ")" => (existsUnique_sLocalThetaAction (F := ℚ) (S := S)).exists.choose
local notation "SB" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "J(" S ")" => SIdeleQuotient ℚ S
local notation "chart(" S "," η "," z ")" => quasiCharacterNormTwist (sIdeleQuotientNorm ℚ S)
  (isProperMap_sIdeleQuotientNorm ℚ S).continuous cc(η) z

private theorem meyer_peel_factors (M : ℕ → ℂ → ℂ) (D : ℂ → ℂ) (Z : ℕ → ℂ → ℂ)
    (b C a : ℝ) (hb : 0 < b) (m : ℕ) (hD : ∀ z : ℂ, z.re = a → b ≤ ‖D z‖)
    (hZ : ∀ n z, z.re = a → ‖z^m * Z n z‖ ≤ C) (h : ∀ n z, z.re = a → Z n z = M n z * D z) :
    ∃ K : ℝ, ∀ n z, z.re = a → ‖z^m * M n z‖ ≤ K := by
  refine ⟨C/b,fun n z hz ↦ (le_div_iff₀ hb).mpr ?_⟩
  calc
    _ ≤ ‖z^m * M n z‖ * ‖D z‖ := mul_le_mul_of_nonneg_left (hD z hz) (norm_nonneg _)
    _ = ‖z^m * Z n z‖ := by rw [←norm_mul,mul_assoc,h n z hz]
    _ ≤ C := hZ n z hz

set_option maxHeartbeats 850000 in
private theorem meyer_rat_sector_inverse (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (hτ : RightInverse τ (sIdeleQuotientNorm ℚ S)) (χ : PontryaginDual N(S)) (hfin : (range χ).Finite)
    (v : ℕ → B(S)) (heig : ∀ n (g : N(S)), A(S) g.val (Q(S) (v n)) = (χ g : ℂ) • Q(S) (v n))
    (hv : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → B(S))),
      sLocalMellinSchwartzBounds S τ f sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ Q(S) (v n)) := by
  classical
  obtain ⟨η,c,hη,hbase,hfη,hc,rep⟩ := meyer_rat_isotype_standard S τ hτ χ hfin
  choose φ hφ using fun n ↦ rep (Q(S) (v n)) (heig n)
  let t (n : ℕ) := sLocalStandardThetaTensor c (φ n)
  have hcη (g : N(S)) : c g.val = (η g.val : ℂ) := (hc g).trans (congrArg (fun y : Circle ↦ (y : ℂ)) (hη g).symm)
  let Fv := fun n ↦ sAdeleSchwartzFourier (v n)
  let Ft := fun n ↦ sAdeleSchwartzFourier (t n)
  let T := (existsUnique_sLocalThetaFourier (F := ℚ) (S := S)).exists.choose
  have hT := (existsUnique_sLocalThetaFourier (F := ℚ) (S := S)).exists.choose_spec.2
  have hft (n : ℕ) : Q(S) (Fv n) = P(S,χ⁻¹) (Q(S) (Ft n)) := calc
    Q(S) (Fv n) = T (Q(S) (v n)) := (hT (v n)).symm
    _ = T (P(S,χ) (Q(S) (t n))) := congrArg T (hφ n).symm
    _ = P(S,χ⁻¹) (T (Q(S) (t n))) := meyer_actual_fourier_average S (by simp) τ hτ χ _
    _ = _ := congrArg (P(S,χ⁻¹)) (hT (t n))
  have phys := meyer_projected_heights S τ η hbase χ hη v t (fun n ↦ (hφ n).symm) (hv v (by simp))
  have freq := meyer_projected_heights S τ η⁻¹ (fun t ↦ by change (η (τ t))⁻¹ = 1; rw [hbase,inv_one])
    χ⁻¹ (fun g ↦ congrArg Inv.inv (hη g)) Fv Ft hft (hv Fv (by simp [Fv]))
  obtain ⟨E,hE⟩ := meyer_arch_coordinates
  let f (n : ℕ) := E.symm (φ n)
  have coord (n : ℕ) (x : InfiniteAdeleRing ℚ) : φ n (Multiplicative.ofAdd x) = f n (realModel (x ∞₀)) := by
    have eq := hE (E.symm (φ n)) x
    rwa [E.apply_symm_apply] at eq
  obtain ⟨a,ha,hprod⟩ := meyer_rational_standard_zeta S η hfη c
  let ε := (-1:ℂ)^a.val
  let R : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
  let g (n : ℕ) := f n + ε • R (f n)
  have eps : ε*ε = 1 := by
    change (-1:ℂ)^a.val * (-1)^a.val = 1
    rw [←mul_pow,neg_one_mul,neg_neg,one_pow]
  have parity (n : ℕ) (x : ℝ) : g n (-x) = ε * g n x := by
    change f n (-x) + ε * f n (- -x) = ε*(f n x + ε*f n (-x))
    rw [neg_neg,mul_add,←mul_assoc,eps,one_mul,add_comm]
  have fg (n : ℕ) (x : ℝ) : (𝓕 (g n)) x = (𝓕 (f n)) x + ε * (𝓕 (f n)) (-x) := by
    change 𝓕 (f n + ε • R (f n)) x = _
    rw [FourierTransform.fourier_add,FourierTransform.fourier_smul]
    change (𝓕 (f n)) x + ε * 𝓕 ((f n : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ) x = _
    rw [Real.fourier_comp_linearIsometry]
    rfl
  let G := fun (v : S) (x : K(v.val)) ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c) (Multiplicative.ofAdd x)
  let FT := fun (v : S) ↦ @tamagawaFourier _ _ (borel _) (finiteLocalAdditiveTamagawaMeasure ℚ v.val)
    (finiteLocalStandardCharacter ℚ v.val)
  let Z := fun (p : (v : S) → K(v.val) → ℂ) (ψ : PontryaginDual J(S)) (z : ℂ) ↦
    ∏ v : S, @localIdelicZetaIntegral _ _ _ (borel _) (finiteLocalMultiplicativeTamagawaMeasure ℚ v.val) (p v)
      (sLocalFiniteRestriction v (chart(S,ψ,z)))
  have bounded : Bornology.IsVonNBounded ℂ (range g) := by
    apply meyer_inverse_signed_real_profiles g (fun _ ↦ ε) (fun _ ↦ by simp [ε]) parity
    intro k hk b hb m
    have hb' := zero_lt_one.trans hb
    obtain ⟨C,hC,lower⟩ := meyer_rational_global_finite_pair S η c hcη b hb'
    rcases hk with rfl | hk
    · obtain ⟨D,hD⟩ := phys b hb m
      exact meyer_peel_factors (fun n ↦ mellin (g n)) (Z G η) _ C D b hC m
        (fun z hz ↦ (lower z hz).1) hD (fun n z hz ↦ (hprod _ _ (coord n) z (hz.symm ▸ hb')).1)
    · rw [mem_singleton_iff] at hk
      subst k
      obtain ⟨D,hD⟩ := freq b hb m
      apply meyer_peel_factors (fun n ↦ mellin ((𝓕 (g n) : SchwartzMap ℝ ℂ) : ℝ → ℂ)) (Z (fun v ↦ FT v (G v)) η⁻¹) _ C D b hC m
        (fun z hz ↦ (lower z hz).2) hD
      intro n z hz
      rw [show ((𝓕 (g n) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = _ from funext (fg n)]
      exact (hprod _ _ (coord n) z (hz.symm ▸ hb')).2
  let Tst : SB →L[ℂ] B(S) := ⟨sLocalStandardThetaTensor c,meyer_standard_tensor_continuous c⟩
  let L := (P(S,χ)).comp ((sLocalAdelicTheta ℚ S).ker.mkQL.comp (Tst.comp E.toContinuousLinearMap))
  let r : SB → SB := fun ψ ↦ E (R (E.symm ψ))
  have hr (ψ : SB) (x : InfiniteAdeleRing ℚ) : r ψ (Multiplicative.ofAdd x) = ψ (Multiplicative.ofAdd (-x)) := by
    have hp := hE (E.symm ψ) (-x)
    rw [E.apply_symm_apply] at hp
    change E (R (E.symm ψ)) (Multiplicative.ofAdd x) = _
    rw [hE,hp]
    change E.symm ψ (-realModel (x ∞₀)) = E.symm ψ (realModel (-(x ∞₀)))
    exact congrArg (fun u : ℝ ↦ E.symm ψ u) (map_neg realModel (x ∞₀)).symm
  have reflect (n : ℕ) : L (R (f n)) = ε • L (f n) := by
    have h := meyer_rational_reflect S η χ hη c r hr (φ n)
    change P(S,χ) (Q(S) (sLocalStandardThetaTensor c (E (R (f n))))) =
      ε • P(S,χ) (Q(S) (sLocalStandardThetaTensor c (E (E.symm (φ n)))))
    change ε = _ at ha
    rw [E.apply_symm_apply,ha]
    exact h
  have lift (n : ℕ) : ((1/2:ℂ) • L) (g n) = Q(S) (v n) := by
    have hL : L (f n) = Q(S) (v n) := by
      change P(S,χ) (Q(S) (sLocalStandardThetaTensor c (E (E.symm (φ n))))) = _
      rw [E.apply_symm_apply]
      exact hφ n
    change (1/2:ℂ) • (L (f n + ε • R (f n))) = _
    rw [map_add,map_smul,reflect,smul_smul,eps,one_smul,←two_smul ℂ _,smul_smul]
    norm_num [hL]
  apply (bounded.image ((1/2:ℂ) • L)).subset
  rintro _ ⟨n,rfl⟩
  exact ⟨g n,⟨n,rfl⟩,lift n⟩

private theorem meyer_rational_all_finite_inverse (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (hτ : RightInverse τ (sIdeleQuotientNorm ℚ S)) (v : ℕ → B(S))
    (hv : ∀ f ∈ ({v,fun n ↦ sAdeleSchwartzFourier (v n)} : Set (ℕ → B(S))),
      sLocalMellinSchwartzBounds S τ f sLocalThetaMellinIntegral) :
    Bornology.IsVonNBounded ℂ (range fun n ↦ Q(S) (v n)) :=
  meyer_degree_one_reduce_to_isotypes S (by simp) τ hτ
    (meyer_rat_sector_inverse S τ hτ) v hv

/-- Meyer's exact bounded-lift criterion specialized to the rational field, with
arbitrary finite stage, norm section and sequence. The two directions use no
part of the all-field classical input. -/
private theorem meyer_rational_finite_stage_criterion (S : Finset V) (τ : ℝ≥0ˣ →ₜ* J(S))
    (hτ : RightInverse τ (sIdeleQuotientNorm ℚ S)) (v : ℕ → B(S)) :
    (∃ A : Set B(S), Bornology.IsVonNBounded ℂ A ∧
      (range fun n ↦ Q(S) (v n)) ⊆ (sLocalAdelicTheta ℚ S).ker.mkQL '' A) ↔
      sLocalMellinSchwartzBounds S τ v sLocalThetaMellinIntegral ∧
        sLocalMellinSchwartzBounds S τ (fun n ↦ sAdeleSchwartzFourier (v n)) sLocalThetaMellinIntegral := by
  rw [sLocalMellinSchwartzBounds_meyer_lift_iff_quotient_bounded S v]
  constructor
  · exact sLocalMellinSchwartzBounds_meyer_degree_one_forward S (by simp) τ hτ v
  · rintro ⟨h,hF⟩
    apply meyer_rational_all_finite_inverse S τ hτ v
    intro w hw
    rcases hw with rfl | hw
    · exact h
    · rw [mem_singleton_iff] at hw
      simpa only [hw] using hF
end RiemannMasullo
end

open NumberField
open scoped NNReal NumberField.AdeleRing
open RiemannMasullo
open Lean Elab Command

private def auditRoot (n : Name) (allowSorry : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "unknown audit root {n}"
  let axioms ← Lean.collectAxioms n
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ (if allowSorry then [``sorryAx] else [])
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
  if !allowSorry && !directSorry.isEmpty then throwError "{n} reaches admissions at {directSorry}"
  logInfo m!"{n}: {visited.size} reached declarations across {mods.size} modules; direct admissions: {directSorry}; kernel axioms {axioms}"

run_cmd auditRoot ``RiemannMasullo.meyer_rational_all_finite_inverse
run_cmd auditRoot ``RiemannMasullo.meyer_rational_finite_stage_criterion

-- Both sides elaborate at the exact rational specialization of the project's
-- classical criterion. This proof-irrelevance check does not enter either root.
example (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient ℚ S)
    (hτ : Function.RightInverse τ (sIdeleQuotientNorm ℚ S))
    (v : ℕ → SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    meyer_rational_finite_stage_criterion S τ hτ v = sLocalMellinSchwartzBounds_meyer S τ hτ v :=
  Subsingleton.elim _ _
